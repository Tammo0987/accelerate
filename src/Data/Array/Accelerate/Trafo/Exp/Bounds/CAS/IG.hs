{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.IG where
import qualified Data.Map as Map
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Type
import Data.Coerce (coerce)
import Control.Arrow (second)
import Control.Applicative (liftA3)
import qualified Data.Set as Set
import Control.Monad.State
import Data.List (intercalate)
import GHC.List (foldl1')
import Data.Maybe (catMaybes)
import Debug.Trace as Debug

type Node   = Int
type Weight = Int
type SumMap = Map.Map Int Int

data BoundKind = Upper | Lower
  deriving (Eq, Show)
boundKinds :: Bounds BoundKind
boundKinds = Bounds Lower Upper

data IG = IG BoundKind (Map.Map Node [(Node, Weight)]) PhiSet SumMap
type PhiSet = Set.Set Node

-- used to log the graph according to the theory
reverseGraph :: Map.Map Node [(Node, Weight)] -> Map.Map Node [(Node, Weight)]
reverseGraph =
  Map.foldrWithKey (\u outs acc ->
    foldr (\(v,w) -> Map.insertWith (++) v [(u,w)]) acc outs) Map.empty

instance {-# OVERLAPPING #-} Show (Bounds IG) where
    show (Bounds lowerG upperG) =
        let showIG varName (IG _ adj' phiSet _) =
                let adj = reverseGraph adj'
                    showEdges (n, ws) = show n ++ ": [" ++ intercalate ", " (map (\(t,w) -> "(" ++ show t ++ "," ++ show w ++ ")") ws) ++ "]"
                    adjStr = varName ++ " = {\n" ++ intercalate ",\n" (map showEdges (Map.toList adj)) ++ "\n}"
                    phiStr = varName ++ "_phi_nodes = " ++ show (Set.toList phiSet)
                in adjStr ++ "\n\n" ++ phiStr
        in showIG "lower_adj_graph" lowerG ++ "\n\n" ++ showIG "upper_adj_graph" upperG

instance Show IG where
    show (IG _ adj' phiSet _) =
        let adj = reverseGraph adj'
            showEdges (n, ws) = show n ++ ": [" ++ intercalate ", " (map (\(t,w) -> "(" ++ show t ++ "," ++ show w ++ ")") ws) ++ "]"
            adjStr = "adj_list = {\n" ++ intercalate ",\n" (map showEdges (Map.toList adj)) ++ "\n}"
            phiStr = "phi_nodes = " ++ show (Set.toList phiSet)
        in "\n" ++ adjStr ++ "\n" ++ phiStr ++ "\n"

emptyIGs :: Bounds IG
emptyIGs = Bounds (IG Lower Map.empty Set.empty Map.empty) (IG Upper Map.empty Set.empty Map.empty)

zeroNode :: Int
zeroNode = 0

-- Variant suited for Controlflow Constraints
insertC :: ControlMap t -> IG -> IG
insertC m p = foldr (\(ESSAIdx _ i, c) g -> insert i c g) p (Map.toList (coerce m))

insertMaybeConstraint :: (HMaybe ESSAIdx) t -> DiffExp ESSAIdx t -> IG -> IG
insertMaybeConstraint (HMaybe idx) df g = maybe g (\(ESSAIdx _ i) -> insert i df g) idx

insertD :: ESSAIdx t -> DiffExp ESSAIdx t -> IG -> IG
insertD (ESSAIdx _ i) = insert i

insert :: Node -> DiffExp ESSAIdx t -> IG -> IG

insert _ DiffUndef g = g

-- avoid edges where src == target. they appear as a consequence of using the same index
-- for arrays and their point-wise argument when mapping
insert i (Diff (BDiff (Just (ESSAIdx _ l)) _)) g | i == l = g

insert i (Diff (BDiff (Just l) w)) (IG label g ps sm) =
  let ix = essaInt l
      g' = Map.insertWith (++) i [(ix, w)] g
      in IG label g' ps sm

insert i (Diff (BDiff Nothing w)) (IG label g ps sm) =
  let g' = Map.insertWith (++) i [(zeroNode, w)] g
  in IG label g' ps sm

insert i (PhiDiff d DiffUndef) g = insert i d g
insert i (PhiDiff DiffUndef d) g = insert i d g

insert i (PhiDiff d1 d2) (IG label g ps sm) =
  let ls  = flattenPhiDiffs d1
      ls' = flattenPhiDiffs d2
      g' = foldr (\(ix, w) -> Map.insertWith (++) i [(ix, w)]) g (ls ++ ls')
      ps' = Set.insert i ps
  in IG label g' ps' sm

flattenPhiDiffs :: DiffExp ESSAIdx t -> [(Int, Int)]
flattenPhiDiffs (Diff (BDiff idx w)) =
  let i' = case idx of Nothing -> zeroNode; Just (ESSAIdx _ i) -> i
  in [(i', w)]
flattenPhiDiffs (PhiDiff DiffUndef d) = flattenPhiDiffs d
flattenPhiDiffs (PhiDiff d DiffUndef) = flattenPhiDiffs d
flattenPhiDiffs (PhiDiff a b)  =
  let ls  = flattenPhiDiffs a
      ls' = flattenPhiDiffs b
  in ls ++ ls'
flattenPhiDiffs DiffUndef = []

insertConstraints :: TupR (BCConstraint (HMaybe ESSAIdx)) t -> DataConstraints t -> Bounds IG -> Bounds IG
insertConstraints idxs dt ps =
    let flat = flattenTupR (hzipWith (hzipWith HPair) idxs dt)
        in foldr (\(Exists bcc) p ->
          let (i, d) = distribute (second runHMaybe . toPair <$> unwrapBCConstraint bcc)
            in liftA3 (\i' d' p' -> maybe p' (\d'' -> insertMaybeConstraint i' d'' p') d') i d p) ps flat

distance :: IG -> Node -> Node -> Weight -> Maybe Weight
distance (IG kind g phis _) src dst wght
  | src == dst = Just 0
  | otherwise  =
      let res = evalState (go dst) Map.empty
       in fmap (wght +) res
  where
    go :: Node -> State (Map.Map Node (Either () (Maybe Weight))) (Maybe Weight)
    go n
      | n == src  = pure (Just 0)
      | otherwise = do
          memo <- get
          case Map.lookup n memo of
            Just (Right ans) -> pure ans
            Just (Left ())   -> pure Nothing
            Nothing          -> do
              modify (Map.insert n (Left ()))
              let preds = Map.findWithDefault [] n g
              contribs <- mapM (step n) preds
              let res = combine n contribs
              modify (Map.insert n (Right res))
              pure res

    step :: Node -> (Node, Weight)
         -> State (Map.Map Node (Either () (Maybe Weight)))
                   (Maybe Weight)
    step _ (p, w) = fmap (fmap (+ w)) (go p)

    combine :: Node -> [Maybe Weight] -> Maybe Weight
    combine _ [] = Nothing
    combine n xs =
      let values = catMaybes xs
          isPhi  = n `Set.member` phis
          op | isPhi = phiOp | otherwise = andOp
       in if null values then Nothing else Just (foldl1' op values)

    andOp, phiOp :: Weight -> Weight -> Weight
    andOp = case kind of
      Upper -> min
      Lower -> max

    phiOp = case kind of
      Upper -> max
      Lower -> min


-- === IG Assisted Operations ===

boundCheck
  :: (Int -> Int -> Bool)
  -> (Int -> Bool)
  -> IG -> BasicDiff ESSAIdx t -> BasicDiff ESSAIdx t -> Bool
boundCheck cmpConsts _ _ (BDiff Nothing w1) (BDiff Nothing w2) = cmpConsts w1 w2
boundCheck _ cmpDist graph (BDiff a w1) (BDiff b w2) =
  let a' = maybe zeroNode essaInt a
      b' = maybe zeroNode essaInt b
      stride = w1 - w2
      dist = distance graph b' a' stride
   in maybe False cmpDist dist


isUpperBound, isStrictUpperBound, isLowerBound, isStrictLowerBound
  :: IG -> BasicDiff ESSAIdx t -> BasicDiff ESSAIdx t -> Bool
isUpperBound g@(IG Upper _ _ _) bd1 bd2 =
  let res = boundCheck (<=) (<= 0) g bd1 bd2
  in -- Debug.trace ("-> " ++ show bd2 ++ " >= " ++ show bd1 ++ " is " ++ show res ++ "\n") 
    res
isUpperBound _ _ _= error "opposite inequality graph encountered"

isStrictUpperBound g@(IG Upper _ _ _) bd1 bd2 =
  let res = boundCheck (<) (< 0) g bd1 bd2
  in -- Debug.trace ("-> " ++ show bd2 ++ " > " ++ show bd1 ++ " is " ++ show res ++ "\n") 
    res
isStrictUpperBound _ _ _= error "opposite inequality graph encountered"

isLowerBound g@(IG Lower _ _ _) bd1 bd2 =
  let res = boundCheck (>=) (>= 0) g bd1 bd2
  in -- Debug.trace ("-> " ++ show bd2 ++ " <= " ++ show bd1 ++ " is " ++ show res ++ "\n") 
    res
isLowerBound _ _ _ = error "opposite inequality graph encountered"

isStrictLowerBound g@(IG Lower _ _ _) bd1 bd2 =
  let res = boundCheck (>) (> 0) g bd1 bd2
  in -- Debug.trace ("-> " ++ show bd2 ++ " < " ++ show bd1 ++ " is " ++ show res ++ "\n") 
    res
isStrictLowerBound _ _ _ = error "opposite inequality graph encountered"

basicDiffToConst :: (HasIdx v) => IG -> BasicDiff v t -> Maybe Int
basicDiffToConst _     (BDiff Nothing  w) = Just w
basicDiffToConst graph (BDiff (Just v) w) = distance graph zeroNode (essaInt $ getIdx v) w