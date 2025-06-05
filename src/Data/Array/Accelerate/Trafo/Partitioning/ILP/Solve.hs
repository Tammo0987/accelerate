{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve where


import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph hiding (graph, constraints, bounds)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
    (Label, parent, Labels, LabelType (..) )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver hiding (finalize)

import Data.List (groupBy, sortOn)
import Prelude hiding (sum, pi, read )

import qualified Data.Map as M

-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S
import Data.Function ( on )
import Lens.Micro ((^.),  _1 )
import Lens.Micro.Extras ( view )
import Data.Maybe (fromJust,  mapMaybe )
import Control.Monad.State
import Data.Array.Accelerate.Trafo.Partitioning.ILP.NameGeneration (freshName)
import Data.Foldable

data FusionObjective
  = NumClusters         -- ^ Minimise the number of clusters.
  | ArrayReads          -- ^ Minimise the number of array reads.
  | ArrayReadsWrites    -- ^ Minimise the number of array reads and writes.
  | IntermediateArrays  -- ^ Minimise the number of intermediate arrays.
  | FusedEdges          -- ^ Minimise the number of unfused edges.
  | Everything          -- ^ Minimise the number of clusters and array reads/writes.
  deriving (Show, Bounded, Enum)

data IUpdatesObjective
  = NumInplaceUpdates       -- ^ Each in-place update counts as 1.
  | WeightedInplaceUpdates  -- ^ Use the weights and merge strategy defined by the backend.

-- TODO: _obj is now obsolete
-- Makes the ILP. Note that this function 'appears' to ignore the Label levels completely!
-- We could add some assertions, but if all the input is well-formed (no labels, constraints, etc
-- that reward putting non-siblings in the same cluster) this is fine: We will interpret 'cluster 3'
-- with parents `Nothing` as a different cluster than 'cluster 3' with parents `Just 5`.
makeILP :: forall op. MakesILP op => FusionObjective -> FusionILP op -> ILP op
makeILP _obj (FusionILP graph constraints bounds) =
  ILP minMax objFun (allConstraints <> constraints) (allBounds <> bounds) (Constants n m)
  where
    compN :: Labels Comp
    compN = graph^.computationNodes

    buffN :: Labels Buff
    buffN = graph^.bufferNodes

    readE :: S.Set ReadEdge
    readE = graph^.readEdges

    writeE :: S.Set WriteEdge
    writeE = graph^.writeEdges

    dataflowE :: S.Set DataflowEdge
    dataflowE = graph^.dataflowEdges

    strictE :: S.Set StrictEdge
    strictE = graph^.strictEdges

    fusibleE, infusibleE :: S.Set DataflowEdge
    (fusibleE, infusibleE) = graph^.fusionEdges

    fusibleE', infusibleE' :: S.Set (Label Comp, Label Comp)
    fusibleE'   = S.map (\(i,_,j) -> (i,j)) fusibleE
    infusibleE' = S.map (\(i,_,j) -> (i,j)) infusibleE

    inplaceP :: S.Set InplacePath
    inplaceP = graph^.inplacePaths

    n :: Int
    n = S.size compN

    m :: Int
    m = S.size buffN

    -- Combine the two objective functions.
    minMax = fusionMinMax
    objFun = (if fusionMinMax == iupdatesMinMax then (.+.) else (.-.))
      (defaultFusionWeight   @op .*. fusionObjFun)
      (defaultIUpdatesWeight @op .*. iupdatesObjFun)

    -- Since we want all clusters to have one 'iteration size', the final objFun should
    -- take care to never reward 'fusing' disjoint clusters, and then slightly penalise it.
    -- The alternative is O(n^2) edges, so this is worth the trouble!
    --
    -- In the future, maybe we want this to be backend-dependent (add to MakesILP).
    -- Also future: add @IVO's IPU reward here.
    fusionObjFun :: Expression op
    fusionMinMax :: OptDir
    (fusionMinMax, fusionObjFun) = case defaultFusionObjective @op of
      NumClusters        -> (Minimise, numberOfClusters)
      ArrayReads         -> (Minimise, numberOfReads)
      ArrayReadsWrites   -> (Minimise, numberOfArrayReadsWrites)
      IntermediateArrays -> (Minimise, numberOfManifestArrays)
      FusedEdges         -> (Minimise, numberOfUnfusedEdges)
      Everything         -> (Minimise, numberOfClusters .+. numberOfArrayReadsWrites) -- arrayreadswrites already indictly includes everything else

    -- objective function that maximises the number of edges we fuse, and minimises the number of array reads if you ignore horizontal fusion
    -- numberOfUnfusedEdges = M.foldMapWithKey (\e v -> const v `times` fused e)
    --                      $ foldl (flip \(i,_,j) -> M.insertWith (+) (i,j) 1) M.empty dataflowE
    numberOfUnfusedEdges = foldMap fused fusibleE'

    -- A cost function that doesn't ignore horizontal fusion.
    -- Idea: Each node $x$ with $n$ outgoing edges gets $n$ extra variables.
    -- Each edge (fused or not) $(x,y)$ will require that one of these variables is equal to $pi y$.
    -- The number of extra variables that are equal to 0 (the thing you maximise) is exactly equal to n - the number of clusters that read from $x$.
    -- Then, we also need n^2 intermediate variables just to make these disjunction of conjunctions
    -- note, it's only quadratic in the number of consumers of a specific array.
    -- We also check for the 'order': horizontal fusion only happens when the two fused accesses are in the same order.
    numberOfReads = nReads .+. numberOfUnfusedEdges
    (nReads, readC, readB)
      = foldl (<>) mempty
      . flip evalState ""
      . forM (S.toList compN) $ \computation -> do
      let consumers  = S.map (\(_,b,c) -> (b,c)) $ S.filter (\(c,_,_) -> c == computation) fusibleE
          nConsumers = S.size consumers
      readPis    <- replicateM nConsumers readPiVar
      readOrders <- replicateM nConsumers readOrderVar
      (subConstraint, subBounds) <- flip foldMapM consumers $ \(buff,cons) -> do
        useVars <- replicateM nConsumers useVar -- these are the n^2 variables: For each consumer, n variables which each check the equality of pi to readpi
        let constraint = foldMap
              (\(uv, rp, ro) -> isEqualRangeN (var rp) (pi cons)              (var uv)
                             <> isEqualRangeN (var ro) (readDir (buff, cons)) (var uv))
              (zip3 useVars readPis readOrders)
        return (constraint <> foldl (.+.) (int 0) (map var useVars) .<=. int (nConsumers-1), foldMap binary useVars)
      readPi0s <- replicateM nConsumers readPi0Var
      return ( foldl (.+.) (int 0) (map var readPi0s)
             , subConstraint <> fold (zipWith (\p p0 -> var p .<=. timesN (var p0)) readPis readPi0s)
             , subBounds <> foldMap (\v -> lowerUpper 0 v n) readPis <> foldMap binary readPi0s)

    readOrderVar = Other <$> freshName "ReadOrder"
    readPiVar    = Other <$> freshName "ReadPi"   -- non-zero signifies that at least one consumer reads this array from a certain pi
    readPi0Var   = Other <$> freshName "Read0Pi"  -- signifies whether the corresponding readPi variable is 0
    useVar       = Other <$> freshName "ReadUse"  -- signifies whether a consumer corresponds with a readPi variable; because its pi == readpi

    -- objective function that maximises the number of fused away arrays, and thus minimises the number of array writes
    -- using .-. instead of notB to factor the constants out of the cost function; if we use (1 - manifest l) as elsewhere Gurobi thinks the 1 is a variable name
    numberOfManifestArrays = foldl' (\e b -> e .-. manifest b) (int 0) buffN

    -- objective function that minimises the total number of array reads + writes
    numberOfArrayReadsWrites = numberOfReads .+. numberOfManifestArrays

    -- objective function that minimises the number of clusters only works if the constraint below it is used!
    -- NOTE: this does not work remotely as well as you'd hope, because the ILP outputs clusters that get split afterwards.
    -- This includes independent array operations, which might not be safe to fuse and get no real benefit from fusing,
    -- but also includes independent alloc, compute, etc nodes which we don't even want to count in the first place!
    -- It's possible to also give each array operation a 'exec-pi' variable, and change this to minimise the maximum of
    -- these exec-pi values, in which case we are only left with the independent array operations problem.
    -- To eliminate that one too, we'd need n^2 edges.
    numberOfClusters  = var (Other "maximumClusterNumber")
    -- removing this from myConstraints makes the ILP slightly smaller, but disables the use of this cost function
    numberOfClustersC = case defaultFusionObjective @op of
      NumClusters -> foldMap (\l -> pi l .<=. numberOfClusters) compN
      Everything  -> foldMap (\l -> pi l .<=. numberOfClusters) compN
      _ -> mempty

    fusionConstraints = fusibleAcyclicC <> strictAcyclicC <> infusibleC <> manifestC
      <> numberOfClustersC <> readC <> orderC <> finalize graph

    -- x_ij <= pi_j - pi_i <= n*x_ij for all fusible edges
    fusibleAcyclicC = foldMap (\e@(i,j) -> between (fused e) (pi j .-. pi i) (timesN $ fused e)) fusibleE'

    -- pi_i < pi_j for all strict edges  NEW!
    strictAcyclicC = foldMap (\(i,j) -> pi i .<. pi j) strictE

    -- x_ij == 1 for all infusible edges
    infusibleC = foldMap (\e -> fused e .==. int 1) infusibleE'

    -- if (i,b,j) is not fused, b has to be manifest
    -- TODO: final output is also manifest
    -- manifestC = foldMap (\(i,b,j) -> notB (fused i j) `impliesB` manifest b) dataflowE

    -- forall b, iff all (w,b,r) are fused, then b is not manifest.
    manifestC = M.foldMapWithKey (\b es -> allB (map fused es) (notB $ manifest b))
              $ foldl (flip \(i,b,j) -> M.insertWith (<>) b [(i,j)]) M.empty dataflowE

    -- if (w,b,r) is fused, then d_wb == d_br
    orderC = flip foldMap fusibleE $ \(w,b,r) ->
                  timesN (fused (w,r)) .>=. readDir (b,r) .-. writeDir (w,b)
      <> (-1) .*. timesN (fused (w,r)) .<=. readDir (b,r) .-. writeDir (w,b)

    fusionBounds :: Bounds op
    fusionBounds = piB <> fusedB <> manifestB <> readB

    --  0 <= pi_i <= n
    piB = foldMap (\i -> lowerUpper 0 (Pi i) n) compN

    -- 0 <= x_ij <= 1
    fusedB = foldMap (binary . uncurry Fused) $ S.map (\(i,_,j) -> (i,j)) dataflowE

    -- 0 <= m_i  <= 1
    manifestB = foldMap (binary . Manifest) buffN


    ----------------------------------------------------------------------------
    -- For in-place updates:
    ----------------------------------------------------------------------------

    iupdatesObjFun :: Expression op
    iupdatesMinMax :: OptDir
    (iupdatesMinMax, iupdatesObjFun) = case defaultIUpdatesObjective @op of
      NumInplaceUpdates       -> (Minimise, numberOfNonInplaceUpdates)
      WeightedInplaceUpdates  -> (Minimise, numberOfNonInplaceUpdates) -- TODO: use the weights and merge strategy defined by the backend

    numberOfNonInplaceUpdates = foldMap inplace inplaceP

    -- If inplace p, then c1 == c2
    acrossClusterC = flip foldMap inplaceP \case
      p@((_,c1),(c2,_))
        | c1 == c2  -> mempty
        | otherwise -> isEqualRangeN (pi c1) (pi c2) (inplace p)

    -- If inplace p, then manifest b1 and manifest b2
    onManifestC = foldMap (\p@((b1,_),(_,b2)) -> (inplace p `impliesB` manifest b1) <> (inplace p `impliesB` manifest b2)) inplaceP

    -- Forall b, at most one inplace p
    singleUpdateC = foldMap (packB 1) $ foldl (flip \p@((b,_),_) -> M.insertWith (<>) b [inplace p]) M.empty inplaceP

    -- If inplace p, then pimax b1 == pi c2
    inplaceClusterC = foldMap (\p@((b1,_),(c2,_)) -> between (int 0) (pimax b1 .-. pi c2) (timesN $ inplace p)) inplaceP

    -- Iff     inplace p, then pi c1     <= pimax b1
    -- Iff not inplace p, then pi c1 + 1 <= pimax b1
    finalClusterC = foldMap (\p@((b1,c1),_) -> pi c1 .+. inplace p .<=. pimax b1) inplaceP

    -- TODO: Maybe add a constraint that c2 is the first writer to b2?
    -- This would make sense because the graph doesn't acctually enforce there is only one writer per buffer.
    -- For most cases there shouldn't be more than 2 writers, one of which is a let-binding, so no issues arise without this constraint.
    -- However, a mutable computation would create a third writer, which would be a problem.

    inplaceConstraints = acrossClusterC <> onManifestC <> singleUpdateC <> inplaceClusterC <> finalClusterC


    -- 0 <= pimax_b
    pimaxB = foldMap (lower 0 . PiMax) buffN

    -- inplace b1 b2 \in {0, 1}
    inplaceB = foldMap (\((b1,c1),(c2,b2)) -> binary $ InPlace b1 c1 c2 b2) inplaceP

    inplaceBounds = pimaxB <> inplaceB


    allConstraints = fusionConstraints <> inplaceConstraints
    allBounds      = fusionBounds <> inplaceBounds








-- | Extract the read directions from the ILP solution.
interpretReadDirs :: forall op. Solution op -> M.Map ReadEdge Int
interpretReadDirs = M.fromList . mapMaybe (_1 fromReadDir) . M.toList
  where
    fromReadDir :: Var op -> Maybe ReadEdge
    fromReadDir (ReadDir b c) = Just (b, c)
    fromReadDir _             = Nothing

-- | Extract the write directions from the ILP solution.
interpretWriteDirs :: forall op. Solution op -> M.Map WriteEdge Int
interpretWriteDirs = M.fromList . mapMaybe (_1 fromWriteDir) . M.toList
  where
    fromWriteDir :: Var op -> Maybe WriteEdge
    fromWriteDir (WriteDir c b) = Just (c, b)
    fromWriteDir _              = Nothing

-- | Extract the top-level clusters and the sub-scoped clusters from the ILP
--   solution.
interpretClusters :: Solution op -> ([Labels Comp], M.Map (Label Comp) [Labels Comp])
interpretClusters sol = do
  let            piVars  = mapMaybe (_1 fromPi) (M.toList sol)               -- Take the Pi variables.
  let      scopedPiVars  = partition (^._1.parent) piVars                    -- Partition them by their parent (i.e. the scope they are in).
  let   clusteredPiVars  = map (partition snd) scopedPiVars                  -- Partition them again by their cluster (i.e. the value of the variable).
  let    scopedClusters  = map (map $ S.fromList . map fst) clusteredPiVars  -- Remove the cluster numbers and convert each cluster to a set.
  let       topClusters  = head scopedClusters  -- The first scope in the list is the top-level scope.
  let subScopedClusters  = tail scopedClusters  -- The rest of the scopes are arbitrarily nested sub-scopes.
  let subScopedClustersM = M.fromList $ map (\s -> (scopeLabel s, s)) subScopedClusters
  (topClusters, subScopedClustersM)
  where
    fromPi :: Var op -> Maybe (Label Comp)
    fromPi (Pi l) = Just l
    fromPi _      = Nothing

    scopeLabel :: [Labels Comp] -> Label Comp
    scopeLabel = fromJust . view parent . S.findMin . head

-- | `groupBy` except it's equivalent to SQL's `GROUP BY` clause.
partition :: Ord b => (a -> b) -> [a] -> [[a]]
partition f = groupBy ((==) `on` f) . sortOn f

interpretInplaceUpdates :: Solution op -> M.Map (Label Buff) (Label Buff)
interpretInplaceUpdates sol = M.map firstInChain inplaceM
  where
    -- Map from buffer to the buffer that will replace it.
    inplaceM = M.fromList $ mapMaybe fromInPlace $ M.toList sol

    fromInPlace :: (Var op, Int) -> Maybe (Label Buff, Label Buff)
    fromInPlace (InPlace b1 _ _ b2, v) | v == 0 = Just (b2, b1)
    fromInPlace _ = Nothing

    firstInChain :: Label Buff -> Label Buff
    firstInChain b = maybe b firstInChain (M.lookup b inplaceM)

-- | Cluster labels, distinguishing between execute and non-execute labels.
data ClusterLs = Execs (Labels Comp) | NonExec (Label Comp)
  deriving (Eq, Show)

-- I think that only `let`s can still be in the same cluster as `exec`s,
-- and their bodies should all be in earlier clusters already.
-- Simply make one cluster per let, before the cluster with execs.
-- TODO: split the cluster of Execs into connected components
splitExecs :: ([Labels Comp], M.Map (Label Comp) [Labels Comp]) -> Symbols op -> ([ClusterLs], M.Map (Label Comp) [ClusterLs])
splitExecs (xs, xM) symbolMap = (f xs, M.map f xM)
  where
    f :: [Labels Comp] -> [ClusterLs]
    f = concatMap (\ls -> filter (/= Execs mempty) $ map NonExec (S.toList $ S.filter isNonExec ls) ++ [Execs (S.filter isExec ls)])

    isExec :: Label Comp -> Bool
    isExec l = case symbolMap M.!? l of
      Just SExe {} -> True
      Just SExe'{} -> True
      _ -> False

    isNonExec :: Label Comp -> Bool
    isNonExec = not . isExec




-- Only needs Applicative
newtype MonadMonoid f m = MonadMonoid { getMonadMonoid :: f m }
instance (Monad f, Semigroup m) => Semigroup (MonadMonoid f m) where
  (MonadMonoid x) <> (MonadMonoid y) = MonadMonoid $ (<>) <$> x <*> y
instance (Monad f, Monoid m) => Monoid (MonadMonoid f m) where
  mempty = MonadMonoid (pure mempty)

foldMapM :: (Foldable t, Monad f, Monoid m) => (a -> f m) -> t a -> f m
foldMapM f = getMonadMonoid . foldMap (MonadMonoid . f)
