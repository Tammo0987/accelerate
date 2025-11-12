{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.Optimize.Exp where
import Data.Array.Accelerate.Trafo.Exp.Bounds.BCState
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.LoopStack
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Bounds.Optimize.Pi
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.IG
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAEnv
import Control.Monad.State
import Prelude hiding (init)
import Data.Kind
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx
import Lens.Micro
import qualified Data.Map as Map
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.RecChain
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.ConstraintArgs
import Data.Maybe (fromMaybe)
import Control.Applicative hiding (Const, empty)
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.AST.LeftHandSide (Exists(..), lhsToTupR)
import Data.Array.Accelerate.Analysis.Match (matchSingleType)
import Data.Type.Equality
import Data.Array.Accelerate.Representation.Shape (ShapeR (..))

-------------------------------------------------------------
-- Expression level bounds inference and assertion removal --
-------------------------------------------------------------

optimizeBoundsExp :: forall benv env t l ls .
    PreOpenExp (ArrayInstr benv) env t -> BCState ScalarType (ArrayInstr benv) (ls:l) '(benv, env) (PreOpenExp (ArrayInstr benv) env t, AnalysisResult t ())

-- Get the constraints of the guard. If it is lower bounded by 1,
-- the boolean expression is always true, which results in a safe removal of the assertion.
-- The variables that are constrianed by the assertion are redefined persistently, 
-- to assure dominant checks remove further weaker checks
optimizeBoundsExp (Assert g e) = do
    (g', arG) <- optimizeBoundsExp g
    redundant <- isAlwaysTrueData (getSingle $ arG ^. rCS . rData)
    if redundant then do
                    -- if the assertion is redundant pi-information does not introduce any useful information
                    (e', arE) <- optimizeBoundsExp e
                    return (e', arE)
                 else do
                    -- Turn assertion domination on and off
                    (e', arE) <- withPiPersist True optimizeBoundsExp e (arG ^. rCS.rControl) 
                    -- (e', arE) <- optimizeBoundsExp e
                    return (Assert g' e', arE)

-- Optimize the guard and non-persistently pi-constrain the variables. The lack of persistence
-- is meant to contain the unsafe effect of an assumtion within intended scope
optimizeBoundsExp (Assume g e) = do
    (_, arG) <- optimizeBoundsExp g
    (e', arE) <- withPi True optimizeBoundsExp e (arG ^. rCS.rControl)
    return (e', arE)

-- TODO: Implement SCEV/Hoisting?
optimizeBoundsExp instr@(While g it init)
  | BCBodyDict <- oneParamFunc it
  , BCBodyDict <- oneParamFunc g = do
    a <- get
    -- Optimize the init expression
    (init', rInit) <- optimizeBoundsExp init

    -- Optimize the guard with init values as arguments.
    let gArgs = diffArg1 (NewBindArg (rInit ^. rCS . rData) (bccsEmpty instr) (bccsEmpty instr))
    (g', urGuard) <- optimizeBoundsFun' gArgs g
    let rGuard = mkFunRes1 urGuard

    redundant <- valOfBool (getSingle $ rGuard ^. rCS . rData)
    case redundant of
      -- if the guard is always false when analyzed with init values, then the loop never iterates and we can safely
      -- restrict the constrants to init
      Just False -> do
        return (While g' it init', rInit)

      -- Otherwise, optimize the body. If hoisting is implemented, the (Just True) marks the trip count is > 0
      _ -> do
        let ((it', _), a') = runState (optimizeWhileBody (rGuard ^. rSCEV . rArgIdxs) (bccsEmpty init) (rGuard ^. rCS . rControl) it) (newLoopScope a)
        put $ popLoopScope a'
        -- Without SCEV, no data constraints are returned for a non-trivial loop 
        return $ identityResult $ While g' it' init'

-- The binded value is optimized and all its constraints are associated to the left hand side
optimizeBoundsExp (Let lhs bnd e) = do
    (bnd', arD) <- optimizeBoundsExp bnd
    a <- get
    let (a', _) = declBind lhs (arD ^. rCS.rData) (arD ^. rCS.rControl) (arD ^. rSCEV.rSCEVExp) a
    let ((e', arE), a'') = runState (optimizeBoundsExp e) a'
    put $ snd $ popBind lhs a''
    return (Let lhs bnd' e', arE)

optimizeBoundsExp (Case expr eqs def) = do
    (expr', _) <- optimizeBoundsExp expr

    -- gather a list of analysis results
    aEqs <- mapM (\(tag, e) -> do
                     (e', arE) <- optimizeBoundsExp e
                     return ((tag, e'), arE)
                 ) eqs

    let eqs' = fmap fst aEqs
        altArs = fmap snd aEqs

    -- analyize default
    tDef <- traverse optimizeBoundsExp def
    let (def', mDefAr) = case tDef of
            Just (d, arD) -> (Just d, Just arD)
            Nothing       -> (Nothing, Nothing)

        allArs = case mDefAr of
                   Just arD -> altArs ++ [arD]
                   Nothing  -> altArs

    case allArs of
      [] -> return $ identityResult $ Case expr' eqs' def'
      [ar] -> return (Case expr' eqs' def', ar)
      _ ->
        let
            -- phi-combine constraints
            d = foldl1 phi (map (^. rCS . rData) allArs)
            c = foldl1 (hzipWith (hzipWith $ zipControlMaps
                                      (Map.intersectionWith PhiDiff)
                                      (Map.intersectionWith PhiDiff)))
                        (map (^. rCS . rControl) allArs)
            s = foldl1 (hzipWith (hzipWith (hzipWith SCEVPhi)))
                        (map (^. rSCEV . rSCEVExp) allArs)
        in return (Case expr' eqs' def', analysisResult d c s)

optimizeBoundsExp (Cond g t e) = do
    (g', arG) <- optimizeBoundsExp g
    redundant  <- valOfBool -- $ Debug.trace (show $ getSingle $ arG ^. rCS . rData) 
        $ getSingle $ arG ^. rCS . rData

    case redundant of
      -- if the guard is always true, only "then" branch is optimized
      Just True -> do
        (t', arT) <- withPi True optimizeBoundsExp t (arG ^. rCS . rControl)
        return (Cond g t' e, arT)

      -- if the guard is always false, only "else" branch is optimized
      Just False -> do
        (e', arE) <- withPi False optimizeBoundsExp e (arG ^. rCS . rControl)
        return (Cond g t e', arE)

      Nothing -> do
        -- phi-combine constraints
        (t', arT) <- withPi True  optimizeBoundsExp t (arG ^. rCS . rControl)
        (e', arE) <- withPi False optimizeBoundsExp e (arG ^. rCS . rControl)
        let d = phi (arT ^. rCS . rData) (arE ^. rCS . rData)
        let c = hzipWith (hzipWith $ zipControlMaps (Map.intersectionWith PhiDiff)
                                                    (Map.intersectionWith PhiDiff))
                         (arT ^. rCS . rControl) (arE ^. rCS . rControl)
        let s = hzipWith (hzipWith (hzipWith SCEVPhi))
                         (arT ^. rSCEV . rSCEVExp) (arE ^. rSCEV . rSCEVExp)
        return (Cond g' t' e', analysisResult d c s)

optimizeBoundsExp (Pair expr1 expr2) = do
    (expr1', AnalysisResult (RCS d1 cD1) (RSCEV ch1 _)) <- optimizeBoundsExp expr1
    (expr2', AnalysisResult (RCS d2 cD2) (RSCEV ch2 _)) <- optimizeBoundsExp expr2
    return (Pair expr1' expr2', AnalysisResult (RCS (TupRpair d1 d2) (TupRpair cD1 cD2)) (RSCEV (TupRpair ch1 ch2) TupRunit))

optimizeBoundsExp (Evar v) = do
    a <- get
    let expEnv = a ^. essaEnvs.essaEnvExp
    let d = varToDataConstraint expEnv v
        c = varToControlConstraint expEnv v
        ch = fromMaybe (hfmap (hfmap SCEVInvar) (varToClosedForm expEnv v)) (indexLoopScopeStackExpVar v (a ^. stack))
    return (Evar v, analysisResult (t d) (t c) (t ch))
        where t = TupRsingle

optimizeBoundsExp instr@(Const tp val) | BCScalarDict <- reprBCScalar tp = do
    let (d, s) = case tp of
            (SingleScalarType (NumSingleType (IntegralNumType int))) | IntegralDict <- integralDict int ->
                let d' = TupRsingle . bccPut (cgTypeScalar tp) $ pure $ fromConst val
                    s' = TupRsingle . bccPut (cgTypeScalar tp) $ pure $ fromConst val
                    in (d', s')
            _ -> (bccsEmpty instr, bccsEmpty instr)
        in return (Const tp val, analysisResult d (bccsEmpty instr) s)

optimizeBoundsExp instr@(PrimConst tp) = do
    let (d, s) = case tp of
            (PrimMinBound (IntegralBoundedType TypeInt)) ->
                let d' = TupRsingle . bccPut (cgTypeScalar $ SingleScalarType $ NumSingleType $ IntegralNumType TypeInt) $ pure $ fromConst (minBound :: t)
                    s' = TupRsingle . bccPut (cgTypeScalar $ SingleScalarType $ NumSingleType $ IntegralNumType TypeInt) $ pure $ fromConst (minBound :: t)
                    in (d', s')
            (PrimMaxBound (IntegralBoundedType TypeInt)) ->
                let d' = TupRsingle . bccPut (cgTypeScalar $ SingleScalarType $ NumSingleType $ IntegralNumType TypeInt) $ pure $ fromConst (maxBound :: t)
                    s' = TupRsingle . bccPut (cgTypeScalar $ SingleScalarType $ NumSingleType $ IntegralNumType TypeInt) $ pure $ fromConst (maxBound :: t)
                    in (d', s')
            _ -> (bccsEmpty instr, bccsEmpty instr)
        in return (PrimConst tp, analysisResult d (bccsEmpty instr) s)

optimizeBoundsExp (ArrayInstr instr@(Parameter v) n) = do
    a <- get
    let env = a ^. essaEnvs.essaEnvArr
        st  = a ^. stack
        (dArr, _) = getArrayInstrCSConstraints instr env
    let c    = varToClosedForm env v
        ctrl = TupRsingle $ varToControlConstraint env v
        sArr = case st of
            -- if there is an expression level loop, then a parameter is invariant to it
            (ConsLoopScopeStack _ _) -> TupRsingle $ hfmap (hfmap SCEVInvar) c
            (EnterExpScope _ (ConsLoopScopeStack _ _)) -> TupRsingle $ fromMaybe (hfmap (hfmap SCEVInvar) (varToClosedForm env v)) $ indexLoopScopeStackParam v (a ^. stack)
            _ -> TupRsingle $ hfmap (const hnothing) c
    return (ArrayInstr instr n, analysisResult dArr ctrl sArr)

optimizeBoundsExp (ArrayInstr instr@(Index v@(Var tp _)) expr) =
    case tp of
        (GroundRbuffer tp') | BCScalarDict <- reprBCScalar tp' -> do
            a <- get
            let env = a ^. essaEnvs.essaEnvArr
                st  = a ^. stack
                (dArr, _) = getArrayInstrCSConstraints instr env

            -- allocate new ESSA for the indexed value to avoid encoding a[i] == a[j] in the graph
            bdIndex <- traverseTupR indexToBasic dArr
            let dIndex = hfmap (hfmap (hfmap Diff)) bdIndex
            (expr', _) <- optimizeBoundsExp expr

            let c    = bccToScalar $ varToClosedForm env v
                sIndex = case st of
                    (ConsLoopScopeStack _ _) -> TupRsingle $ hfmap (hfmap SCEVInvar) c
                    _ -> TupRsingle $ hfmap (const hnothing) c

            return (ArrayInstr instr expr', analysisResult dIndex (TupRsingle $ hfmap (const empty) c) sIndex)
        (GroundRscalar tp') -> case absurdScalarBuffer tp' of {}

optimizeBoundsExp instr@(ShapeSize shr expr) = do
    (expr', r) <- optimizeBoundsExp expr
    d <- bcShapeSize shr (r ^. rCS . rData)
    return (ShapeSize shr expr', analysisResult (TupRsingle d) (bccsEmpty instr) (bccsEmpty instr))

optimizeBoundsExp instr@(Undef tp) = return (instr, analysisResult (TupRsingle $ bccPut (toCGType (GroundRscalar tp)) $ pure $ hjust DiffUndef) (bccsEmpty instr) (bccsEmpty instr))

optimizeBoundsExp instr@(PrimApp pf expr) = do
    (expr', ar) <- optimizeBoundsExp expr
    ar' <- interpretPrimFun (groundsR instr) pf ar
    return (PrimApp pf expr', ar')

-----------------------
-- Nothing to infer: --
-----------------------

optimizeBoundsExp (Coerce tp1 tp2 expr) = do
    (expr', _) <- optimizeBoundsExp expr
    return $ identityResult $ Coerce tp1 tp2 expr'

optimizeBoundsExp (IndexSlice slix shExpr expr) = do
    (shExpr', _) <- optimizeBoundsExp shExpr
    (expr'  , _) <- optimizeBoundsExp expr
    return $ identityResult $ IndexSlice slix shExpr' expr'

optimizeBoundsExp (IndexFull slix shExpr expr) = do
    (shExpr', _) <- optimizeBoundsExp shExpr
    (expr'  , _) <- optimizeBoundsExp expr
    return $ identityResult $ IndexFull slix shExpr' expr'

optimizeBoundsExp (ToIndex shr shrExpr expr) = do
    (shrExpr', _) <- optimizeBoundsExp shrExpr
    (expr'   , _) <- optimizeBoundsExp expr
    return $ identityResult $ ToIndex shr shrExpr' expr'

optimizeBoundsExp (FromIndex shr shrExpr expr) = do
    (shrExpr', _) <- optimizeBoundsExp shrExpr
    (expr'   , _) <- optimizeBoundsExp expr
    return $ identityResult $ FromIndex shr shrExpr' expr'

optimizeBoundsExp (VecPack vr expr) = do
    (expr', _) <- optimizeBoundsExp expr
    return $ identityResult $ VecPack vr expr'

optimizeBoundsExp (VecUnpack vr expr) = do
    (expr', _) <- optimizeBoundsExp expr
    return $ identityResult $ VecUnpack vr expr'

optimizeBoundsExp Nil = return $ identityResult Nil

optimizeBoundsExp instr@(Foreign {}) = return $ identityResult instr


bcShapeSize :: ShapeR dim -> DataConstraints dim -> BCState s op prev env (DataConstraint Int)
bcShapeSize (ShapeRsnoc ShapeRz) (TupRpair TupRunit (TupRsingle d)) = return d
bcShapeSize (ShapeRsnoc sh) (TupRpair d1 (TupRsingle d2)) = do
    a <- get
    d1' <- bcShapeSize sh d1
    return $ interpretData (a ^. ig) interpretPrimMul d2 d1'
bcShapeSize _ _ = error "mismatched tuples"

---------------
-- Functions --
---------------

optimizeBoundsFun'
    :: forall benv env t loopEnv loops
    .  ConstraintsArgs (TypeToArgs t)
    -> PreOpenFun (ArrayInstr benv) env t
    -> BCState ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env)
       (PreOpenFun (ArrayInstr benv) env t, AnalysisResult (ReturnType t) (ArgsType t))
optimizeBoundsFun' (ConstraintsArgsCons (NewBindArg d cD ch) args) (Lam lhs f) = do
    a <- get
    let (a', idxs) = declBind lhs d cD ch a
    let ((f', ar), a'') = runState (optimizeBoundsFun' args f) a'
        ar' = ar & rSCEV . rArgIdxs %~ \x -> TupRpair x idxs
    put $ snd $ popBind lhs a''
    return (Lam lhs f', ar')
optimizeBoundsFun' (ConstraintsArgsCons (KeepBindArg i) args) (Lam lhs f) = do
    a <- get
    let a' = rebind lhs i (bccsEmptyG (hfmap GroundRscalar (lhsToTupR lhs))) (bccsEmptyG (hfmap GroundRscalar (lhsToTupR lhs))) a
        ((f', ar), a'') = runState (optimizeBoundsFun' args f) a'
        ar' = ar & rSCEV . rArgIdxs %~ \x -> TupRpair x i
    put $ snd $ popBind lhs a''
    return (Lam lhs f', ar')
optimizeBoundsFun' _ (Body body) | BCBodyDict <- isBody body = do
    (body', ar) <- optimizeBoundsExp body
    return (Body body', ar)

optimizeWhileBody
    :: TupR (BCConstraint (HMaybe ESSAIdx)) t
    -> DataConstraints t
    -> ControlConstraints PrimBool
    -> PreOpenFun (ArrayInstr benv) env (t -> t)
    -> BCState ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env)
       (PreOpenFun (ArrayInstr benv) env (t -> t), AnalysisResult (ReturnType t) (ArgsType t))
optimizeWhileBody idxs d ctrl (Lam lhs (Body body)) | BCBodyDict <- isBody body = do
    a <- get
    let a' = rebind lhs idxs d (bccsEmpty body) a
    let ((body', _), a'') = runState (withPi True optimizeBoundsExp body ctrl) a'
    -- The guard arugments and body arguments have the same ESSA-indices
    let (_, a''') = popBind lhs a''
    put a'''
    () <- putPiAssignment False (getSingle ctrl)
    return (Lam lhs (Body body'), analysisResult (bccsEmpty body) (bccsEmpty body) (bccsEmpty body))
optimizeWhileBody _ _ _ _ = error "malformed While encountered"

mkFunRes1 :: AnalysisResult t ((), ts) -> AnalysisResult t ts
mkFunRes1 (AnalysisResult cs (RSCEV ch a)) = AnalysisResult cs (RSCEV ch (mkArgRes1 a))

mkArgRes1 :: TupR a ((), ts) -> TupR a ts
mkArgRes1 (TupRpair TupRunit a) = a
mkArgRes1 _ = error "mismatched function arity"

mkFunRes2 :: AnalysisResult t (((), ts), ts') -> AnalysisResult t (ts, ts')
mkFunRes2 (AnalysisResult cs (RSCEV ch (TupRpair (TupRpair TupRunit a) b))) = AnalysisResult cs (RSCEV ch (TupRpair a b))
mkFunRes2 _ = error "mismatched function arity"

-- ======================
-- === Prim Operators ===
-- ======================

interpretPrimFun :: GroundsR t
                 -> PrimFun (a -> t)
                 -> AnalysisResult a ()
                 -> BCState ScalarType (ArrayInstr benv) (l:ls) '(benv, env) (AnalysisResult t ())
interpretPrimFun g pf (AnalysisResult (RCS d c) (RSCEV s _)) = do
        c'  <- primFunControl g pf d c
        d'  <- primFunData    g pf d
        let s' = primFunSCEV  g pf s
        return $ AnalysisResult (RCS d' c') (RSCEV s' TupRunit)

interpretBCC :: (HasIdx v)
              => Bounds IG
              -> (forall t' . IG -> b v t' -> b v t' -> Maybe (b v t'))
              -> BCConstraint (HMaybe (b v)) t
              -> BCConstraint (HMaybe (b v)) t
              -> BCConstraint (HMaybe (b v)) t
interpretBCC graphs f d1 d2 =
    let graphs' = bccPut (toCGType d1) $ Tag <$> graphs
        in hzipWith3
            (\(Tag g) m1 m2 -> hbind m1 $ \d1' -> hbind m2 $ \d2' -> HMaybe $ f g d1' d2')
            graphs' d1 d2

interpretDiffExp :: (HasIdx v)
              => (forall t' . BasicDiff v t' -> BasicDiff v t' -> Maybe (BasicDiff v t'))
              -> DiffExp v t
              -> DiffExp v t
              -> Maybe (DiffExp v t)
interpretDiffExp f (Diff bd1) (Diff bd2) = Diff <$> f bd1 bd2
interpretDiffExp _ _ DiffUndef = Nothing
interpretDiffExp _ DiffUndef _ = Nothing
interpretDiffExp f (PhiDiff DiffUndef d1) d2 = interpretDiffExp f d1 d2
interpretDiffExp f (PhiDiff d1 DiffUndef) d2 = interpretDiffExp f d1 d2
interpretDiffExp f d1 (PhiDiff d2 DiffUndef) = interpretDiffExp f d1 d2
interpretDiffExp f d1 (PhiDiff DiffUndef d2) = interpretDiffExp f d1 d2
interpretDiffExp f (PhiDiff d1 d2) d' =
    let left  = interpretDiffExp f d1 d'
        right = interpretDiffExp f d2 d'
    in liftA2 PhiDiff left right
interpretDiffExp f d' (PhiDiff d1 d2) =
    let left  = interpretDiffExp f d1 d'
        right = interpretDiffExp f d2 d'
    in liftA2 PhiDiff left right

-- === Data Constraints ===
interpretData :: Bounds IG -> (forall v t' . (HasIdx v) => IG -> BasicDiff v t' -> BasicDiff v t' -> Maybe (BasicDiff v t')) -> DataConstraint t -> DataConstraint t -> DataConstraint t
interpretData g f = interpretBCC g (\g' -> interpretDiffExp (f g'))

interpretSub :: DataConstraint t -> DataConstraint t -> BCState ScalarType (ArrayInstr benv) (l:ls) '(benv, env) (DataConstraint t)
interpretSub d1 d2 = do
    d1' <- dataToBasic d1
    d2' <- bccToConst d2
    let b = sequenceMBounds $ runHMaybe <$> unwrapBCConstraint d1'
        c = sequenceMBounds d2'
        r = HMaybe <$> boundsToMaybe (f <$> b <*> c)
    return $ bccPut (toCGType d1) (fmap (hfmap Diff) r)
        where
            f :: Bounds (BasicDiff ESSAIdx t) -> Bounds Int -> Bounds (BasicDiff ESSAIdx t)
            f (Bounds (BDiff i1 w1) (BDiff i2 w2)) (Bounds c1 c2) =
                Bounds (BDiff i1 (w1 - c2))
                    (BDiff i2 (w2 - c1))

boolData :: Maybe Bool -> DataConstraint PrimBool
boolData val = bccPut (cgTypeScalar scalarTypeWord8) $
    case val of
        (Just True)  -> Bounds (fromConst (1 :: Int)) (fromConst (1 :: Int))
        (Just False) -> Bounds (fromConst (0 :: Int)) (fromConst (0 :: Int))
        Nothing      -> Bounds (fromConst (0 :: Int)) (fromConst (1 :: Int))

isAlwaysTrue :: Bounds IG -> ClosedFormConstraint PrimBool -> Bool
isAlwaysTrue graphs c =
    let l = runHMaybe $ _lower $ unwrapBCConstraint c
        lgraph = _lower graphs
        f b = case basicDiffToConst lgraph b of
                Just 1 -> True
                _      -> False
        in maybe False f l

isAlwaysFalse :: Bounds IG -> ClosedFormConstraint PrimBool -> Bool
isAlwaysFalse graphs c =
    let u = runHMaybe $ _upper $ unwrapBCConstraint c
        ugraph = _upper graphs
        f b = case basicDiffToConst ugraph b of
                Just 0 -> True
                _      -> False
        in maybe False f u

valOfBool :: DataConstraint PrimBool -> BCState s op prev env (Maybe Bool)
valOfBool d = do
    t <- isAlwaysTrueData d
    f <- isAlwaysFalseData d
    if t then return $ Just True
        else if f then return $ Just False
            else return Nothing

isAlwaysTrueData :: DataConstraint PrimBool -> BCState s op prev env Bool
isAlwaysTrueData d = do
    a <- get
    let graphs = a ^. ig
    d' <- dataToBasic d
    return $ isAlwaysTrue graphs d'

isAlwaysFalseData :: DataConstraint PrimBool -> BCState s op prev env Bool
isAlwaysFalseData d = do
    a <- get
    let graphs = a ^. ig
    d' <- dataToBasic d
    return $ isAlwaysFalse graphs d'

primFunData :: GroundsR t
            -> PrimFun (a -> t)
            -> DataConstraints a
            -> BCState ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env) (DataConstraints t)
primFunData g pf (TupRpair dx@(TupRsingle x) dy@(TupRsingle y)) =
    do a <- get
       let graphs = a ^. ig
       case pf of
            (PrimAdd   _) -> return $ TupRsingle $ interpretData graphs interpretPrimAdd x y
            (PrimSub   _) -> do r <- interpretSub x y; return $ TupRsingle r
            (PrimMax   _) -> return $ phi dx dy
            (PrimMin   _) -> return $ phi dx dy
            PrimLAnd ->
                    TupRsingle . boolData <$> liftA2 (<|>) (fTrue x y) (fFalse x y)
                where
                    -- Logical AND semantics
                    isTrue  x' y' = isAlwaysTrue  graphs x' && isAlwaysTrue  graphs y'
                    isFalse x' y' = isAlwaysFalse graphs x' || isAlwaysFalse graphs y'

                    fTrue  x' y' = liftM2 (\m n ->
                            if isTrue m n
                            then Just True
                            else Nothing
                        ) (dataToBasic x') (dataToBasic y')

                    fFalse x' y' = liftM2 (\m n ->
                            if isFalse m n
                            then Just False
                            else Nothing
                        ) (dataToBasic x') (dataToBasic y')

            PrimLOr ->
                    TupRsingle . boolData <$> liftA2 (<|>) (fTrue x y) (fFalse x y)
                where
                    isTrue  x' y' = isAlwaysTrue  graphs x' || isAlwaysTrue  graphs y'
                    isFalse x' y' = isAlwaysFalse graphs x' && isAlwaysFalse graphs y'

                    fTrue  x' y' = liftM2 (\m n ->
                            if isTrue m n
                            then Just True
                            else Nothing
                        ) (dataToBasic x') (dataToBasic y')

                    fFalse x' y' = liftM2 (\m n ->
                            if isFalse m n
                            then Just False
                            else Nothing
                        ) (dataToBasic x') (dataToBasic y')
            (PrimLt    _) -> do
                always <- alwaysLT x y;
                never  <- neverLT x y;
                return $ TupRsingle $ boolData ((True <$ guard always) <|> (False <$ guard never))
            (PrimGt    _) -> do
                always <- alwaysGT x y;
                never  <- neverGT x y;
                return $ TupRsingle $ boolData ((True <$ guard always) <|> (False <$ guard never))
            (PrimLtEq  _) -> do
                always <- alwaysLTEQ x y;
                never  <- neverLTEQ x y;
                return $ TupRsingle $ boolData ((True <$ guard always) <|> (False <$ guard never))
            (PrimGtEq  _) -> do
                always <- alwaysGTEQ x y;
                never  <- neverGTEQ x y;
                return $ TupRsingle $ boolData ((True <$ guard always) <|> (False <$ guard never))
            (PrimEq   _) -> return $ TupRsingle (boolData Nothing)
            _            -> return $ bccsEmpty g
    -- temporary, will traverse and replace types of ESSA indices
primFunData _ (PrimFromIntegral tp a) (TupRsingle x) = return $ TupRsingle $ retypeData (NumSingleType $ IntegralNumType tp) (NumSingleType a) x
primFunData g _ _ = return $ bccsEmpty g

retypeData :: SingleType t -> SingleType t' -> DataConstraint t -> DataConstraint t'
retypeData tp tp' d | BCSingleDict <- reprBCSingle tp,  BCSingleDict <- reprBCSingle tp' =
    let
        d' = fmap (fmap (retypeDiff tp')) (runHMaybe <$> unwrapBCConstraint d)
        in bccPut (toCGType $ GroundRscalar (SingleScalarType tp')) (HMaybe <$> d')

retypeDiff :: SingleType t' -> DiffExp ESSAIdx t -> DiffExp ESSAIdx t'
retypeDiff _ DiffUndef = DiffUndef
retypeDiff tp (PhiDiff d1 d2) = PhiDiff (retypeDiff tp d1) (retypeDiff tp d2)
retypeDiff tp (Diff (BDiff essa w)) = Diff $ BDiff (fmap (\(ESSAIdx _ i) -> ESSAIdx tp i) essa) w


alwaysGT :: DataConstraint t -> DataConstraint t
         -> BCState ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env) Bool
alwaysGT d1 d2 = do
    res <- bindCS2 d1 d2                                 -- show that always d1 > d2
              (\g a b -> Tag $ isStrictLowerBound g a b) -- d1 > d2
              (\g a b -> Tag $ isStrictUpperBound g b a) -- d2 < d1
    let (Bounds (Tag l) (Tag u)) = unwrapBCConstraint res
    return $ l || u
neverGT :: DataConstraint t -> DataConstraint t -> BCState      ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env) Bool
neverGT = alwaysLTEQ

alwaysLT :: DataConstraint t -> DataConstraint t
         -> BCState ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env) Bool
alwaysLT d1 d2 = do
    res <- bindCS2 d1 d2                                 -- show that always d1 < d2
              (\g a b -> Tag $ isStrictLowerBound g b a) -- d2 > d1
              (\g a b -> Tag $ isStrictUpperBound g a b) -- d1 < d2
    let (Bounds (Tag l) (Tag u)) = unwrapBCConstraint res
    return $ l || u
neverLT :: DataConstraint t -> DataConstraint t -> BCState      ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env) Bool
neverLT = alwaysGTEQ

alwaysGTEQ :: DataConstraint t -> DataConstraint t
           -> BCState ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env) Bool
alwaysGTEQ d1 d2 = do
    res <- bindCS2 d1 d2                           -- show that always d1 >= d2
              (\g a b -> Tag $ isLowerBound g a b) -- d1 >= d2
              (\g a b -> Tag $ isUpperBound g b a) -- d2 <= d1
    let (Bounds (Tag l) (Tag u)) = unwrapBCConstraint res
    return $ l || u
neverGTEQ :: DataConstraint t -> DataConstraint t -> BCState      ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env) Bool
neverGTEQ = alwaysLT

alwaysLTEQ :: DataConstraint t -> DataConstraint t
           -> BCState ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env) Bool
alwaysLTEQ d1 d2 = do
    res <- bindCS2 d1 d2                           -- show that always d1 <= d2
              (\g a b -> Tag $ isLowerBound g b a) -- d2 >= d1
              (\g a b -> Tag $ isUpperBound g a b) -- d1 <= d2
    let (Bounds (Tag l) (Tag u)) = unwrapBCConstraint res
    return $ l || u
neverLTEQ :: DataConstraint t -> DataConstraint t -> BCState      ScalarType (ArrayInstr benv) (loopEnv : loops) '(benv, env) Bool
neverLTEQ = alwaysGT

interpretPrimAdd :: (HasIdx v) => IG -> BasicDiff v t -> BasicDiff v t -> Maybe (BasicDiff v t)
interpretPrimAdd _ (BDiff Nothing w1) (BDiff Nothing w2) =
    Just $ fromConst (w1 + w2)
interpretPrimAdd _ (BDiff (Just v) w1) (BDiff Nothing w2) = Just $ BDiff (Just v) (w1 + w2)
interpretPrimAdd _ (BDiff Nothing w1) (BDiff (Just v) w2) = Just $ BDiff (Just v) (w1 + w2)
interpretPrimAdd graph d1@(BDiff (Just _) _) d2@(BDiff (Just _) _) =
      (basicDiffToConst graph d1 >>= \c -> interpretPrimAdd graph (fromConst c) d2)
  <|> (basicDiffToConst graph d2 >>= \c -> interpretPrimAdd graph d1 (fromConst c))

interpretPrimMul :: (HasIdx v) => IG -> BasicDiff v t -> BasicDiff v t -> Maybe (BasicDiff v t)
interpretPrimMul _ (BDiff Nothing w1) (BDiff Nothing w2) =
    Just $ fromConst (w1 * w2)
interpretPrimMul graph bd1@(BDiff (Just _) _) bd2@(BDiff Nothing w2)
    | w2 == 1   = Just bd1
    | w2 == 0   = Just $ fromConst (0 :: Int)
    | otherwise = basicDiffToConst graph bd1 >>= \c -> interpretPrimMul graph (fromConst c) bd2
interpretPrimMul graph bd1@(BDiff Nothing w1) bd2@(BDiff (Just _) _)
    | w1 == 1   = Just bd2
    | w1 == 0   = Just $ fromConst (0 :: Int)
    | otherwise = basicDiffToConst graph bd2 >>= \c -> interpretPrimMul graph bd1 (fromConst c)
interpretPrimMul graph d1@(BDiff (Just _) _) d2@(BDiff (Just _) _) =
      (basicDiffToConst graph d1 >>= \c -> interpretPrimMul graph (fromConst c) d2)
  <|> (basicDiffToConst graph d2 >>= \c -> interpretPrimMul graph d1 (fromConst c))

interpretPrimPow :: (HasIdx v) => IG -> BasicDiff v t -> BasicDiff v t -> Maybe (BasicDiff v t)
interpretPrimPow _ (BDiff Nothing w1) (BDiff Nothing w2) =
    Just $ fromConst (w1 ^ w2)
interpretPrimPow graph bd1@(BDiff (Just v) w1) bd2@(BDiff Nothing w2)
    | w2 == 1   = Just $ BDiff (Just v) w1
    | w2 == 0   = Just $ fromConst (1 :: Int)
    | otherwise = basicDiffToConst graph bd1 >>= \c -> interpretPrimPow graph (fromConst c) bd2
interpretPrimPow graph bd1@(BDiff Nothing w1) bd2@(BDiff (Just _) _)
    | w1 == 1   = Just $ fromConst (1 :: Int)
    | w1 == 0   = Just $ fromConst (0 :: Int)
    | otherwise = basicDiffToConst graph bd2 >>= \c -> interpretPrimMul graph bd1 (fromConst c)
interpretPrimPow graph d1@(BDiff (Just _) _) d2@(BDiff (Just _) _) =
      (basicDiffToConst graph d1 >>= \c -> interpretPrimPow graph (fromConst c) d2)
  <|> (basicDiffToConst graph d2 >>= \c -> interpretPrimPow graph d1 (fromConst c))

-- === SCEV Constraints ===
interpretSCEV :: (forall t' . SCEVExp t' -> SCEVExp t' -> SCEVExp t') -> SCEVConstraint t -> SCEVConstraint t -> SCEVConstraint t
interpretSCEV f = hzipWith (\m1 m2 -> hbind m1 $ \d1' -> hbind m2 $ \d2' -> hreturn $ f d1' d2')

primFunSCEV :: GroundsR t
            -> PrimFun (a -> t)
            -> SCEVConstraints a
            -> SCEVConstraints t
primFunSCEV g pf (TupRpair (TupRsingle x) (TupRsingle y)) =
    case pf of
        (PrimAdd _) -> TupRsingle $ interpretSCEV (SCEVOp Add ) x y
        (PrimMul _) -> TupRsingle $ interpretSCEV (SCEVOp Mult) x y
        _           -> bccsEmpty g
primFunSCEV _ _ _ = error "misaligned TupR"

-- === Control Constraints ===
primFunControl :: GroundsR t
               -> PrimFun (a -> t)
               -> DataConstraints a
               -> ControlConstraints a
               -> BCState s op prev '(benv, env) (ControlConstraints t)
primFunControl g pf d (TupRpair (TupRsingle maps1) (TupRsingle maps2)) =
    case pf of
        (PrimLt   _) -> interpretControlComparisson pf d
        (PrimGt   _) -> interpretControlComparisson pf d
        (PrimLtEq _) -> interpretControlComparisson pf d
        (PrimGtEq _) -> interpretControlComparisson pf d
        (PrimEq   _) -> interpretControlComparisson pf d
        (PrimNEq  _) -> interpretControlComparisson pf d
        PrimLAnd     -> return $ TupRsingle maps
            where maps    = bccBind maps1 $ \(ControlMaps true1 false1) ->
                            bccBind maps2 $ \(ControlMaps true2 false2) ->
                                -- to avoid the need for multiple pi-assignments of the same variable caused by a single guard we Xor over controlMaps.
                                bccPut (toCGType maps) $ pure $ ControlMaps (mapXor true1 true2) (Map.intersectionWith PhiDiff false1 false2)
        PrimLOr      -> return $ TupRsingle maps
            where maps    = bccBind maps1 $ \(ControlMaps true1 false1) ->
                            bccBind maps2 $ \(ControlMaps true2 false2) ->
                                bccPut (toCGType maps) $ pure $ ControlMaps (Map.intersectionWith PhiDiff true1 true2) (mapXor false1 false2)
        _            -> return $ bccsEmpty g
primFunControl g pf _ (TupRsingle c) =
    case pf of
        PrimLNot     -> return (TupRsingle (hfmap (\(ControlMaps t f) -> ControlMaps f t) c))
        _            -> return $ bccsEmpty g
primFunControl g _ _ _ = return $ bccsEmpty g

ifI :: Maybe (ESSAIdx t) -> Maybe (ESSAIdx t) -> Int -> [(ESSAIdx t, DiffExp ESSAIdx t)]
ifI idx1 idx2 w = maybe [] (\ix1 -> [(ix1, Diff $ BDiff idx2 w)]) idx1

interpretControlComparisson
  :: PrimFun ((a, a) -> PrimBool)
  -> DataConstraints (a, a)
  -> BCState level op loops ssaEnv (ControlConstraints PrimBool)
interpretControlComparisson pf (TupRpair (TupRsingle bcd1) (TupRsingle bcd2)) = do
    let m ls1 ls2 = ControlMaps (Map.fromList ls1) (Map.fromList ls2)
    let upperF :: IG -> BasicDiff ESSAIdx t -> BasicDiff ESSAIdx t -> ControlMaps t
        upperF _ (BDiff i1 w1) (BDiff i2 w2) = case pf of
            -- i1 + w1 < i2 + w2
            -- True branch: i1 <= i2 + (w2 - w1 - 1)
            -- False branch: i2 <= i1 + (w1 - w2)
            PrimLt _   -> -- Debug.trace (show bd1 ++ "<" ++ show bd2 ++ "?") $
                m (ifI i1 i2 (w2 - w1 - 1)) (ifI i2 i1 (w1 - w2))

            -- i1 + w1 > i2 + w2
            -- True branch: i2 <= i1 + (w1 - w2 - 1)
            -- False branch: i1 <= i2 + (w2 - w1)
            PrimGt _   -> m (ifI i2 i1 (w1 - w2 - 1)) (ifI i1 i2 (w2 - w1))

            -- i1 + w1 <= i2 + w2
            -- True branch: i1 <= i2 + (w2 - w1)
            -- False branch: i2 <= i1 + (w1 - w2 - 1)
            PrimLtEq _ -> m (ifI i1 i2 (w2 - w1))     (ifI i2 i1 (w1 - w2 - 1))

            -- i1 + w1 >= i2 + w2
            -- True branch: i2 <= i1 + (w1 - w2)
            -- False branch: i1 <= i2 + (w2 - w1 - 1)
            PrimGtEq _ -> m (ifI i2 i1 (w1 - w2))     (ifI i1 i2 (w2 - w1 - 1))
            -- Treat EQ as a LTEQ
            PrimEq   _ -> m (ifI i1 i2 (w2 - w1))     (ifI i2 i1 (w1 - w2 - 1))
            _         -> m [] []

    let lowerF :: IG -> BasicDiff ESSAIdx t -> BasicDiff ESSAIdx t -> ControlMaps t
        lowerF _ (BDiff i1 w1) (BDiff i2 w2) = case pf of
            -- i1 + w1 < i2 + w2
            -- True  : i2 > i1 + (w1 - w2)  =>  i2 >= i1 + (w1 - w2 + 1)
            -- False : i1 >= i2 + (w2 - w1)
            PrimLt _  -> m (ifI i2 i1 (w1 - w2 + 1)) (ifI i1 i2 (w2 - w1))

            -- i1 + w1 > i2 + w2
            -- True  : i1 > i2 + (w2 - w1)  =>  i1 >= i2 + (w2 - w1 + 1)
            -- False : i2 >= i1 + (w1 - w2)
            PrimGt _  -> m (ifI i1 i2 (w2 - w1 + 1)) (ifI i2 i1 (w1 - w2))

            -- i1 + w1 <= i2 + w2
            -- True  : i2 >= i1 + (w1 - w2)
            -- False : i1 > i2 + (w2 - w1)  =>  i1 >= i2 + (w2 - w1 + 1)
            PrimLtEq _ -> m (ifI i2 i1 (w1 - w2)) (ifI i1 i2 (w2 - w1 + 1))

            -- i1 + w1 >= i2 + w2
            -- True  : i1 >= i2 + (w2 - w1)
            -- False : i2 > i1 + (w1 - w2)  =>  i2 >= i1 + (w1 - w2 + 1)
            PrimGtEq _ -> m (ifI i1 i2 (w2 - w1)) (ifI i2 i1 (w1 - w2 + 1))
            -- Treat EQ as a GTEQ
            PrimEq   _ -> m (ifI i1 i2 (w2 - w1)) (ifI i2 i1 (w1 - w2 + 1))
            _         -> m [] []

    res <- bindCS2 bcd1 bcd2 lowerF upperF
    return $ TupRsingle $ unsafeCoerce res
interpretControlComparisson _ _ = error "mismatched tuples"

-- === Helpers for BOT inferences ===
identityCS
    :: forall instr (op :: Type -> Type) env t
    .  (HasGroundsR (instr op env))
    => instr op env t -> RCS t
identityCS instr = RCS (bccsEmpty instr) (bccsEmpty instr)

identitySCEV
    :: forall instr (op :: Type -> Type) env t
    .  (HasGroundsR (instr op env))
    => instr op env t -> RSCEV t ()
identitySCEV instr = RSCEV (bccsEmpty instr) TupRunit

identityResult
    :: forall instr (op :: Type -> Type) env t
    .  (HasGroundsR (instr op env))
    => instr op env t -> (instr op env t, AnalysisResult t ())
identityResult instr = (instr, AnalysisResult (identityCS instr) (identitySCEV instr))

getArrayInstrCSConstraints
    :: ArrayInstr benv (a -> t)
    -> ESSAEnv benv
    -> (DataConstraints t, ControlConstraints t)
getArrayInstrCSConstraints (Index  v@(Var (GroundRbuffer tp) _)) env | BCScalarDict <- reprBCScalar tp =
    let (EnvElem idxs ec) = getESSAEnv (varIdx v) env
        sIdxs   = bccToScalar idxs
        tupD    = TupRsingle $ (HMaybe . Just . hpure) `hfmap` sIdxs
        tupc = TupRsingle $ bccToScalar ec
    in (tupD, tupc)
getArrayInstrCSConstraints (Index (Var (GroundRscalar tp) _)) _ = case absurdScalarBuffer tp of {}
getArrayInstrCSConstraints (Parameter v) env =
    let (EnvElem idxs ec) = getESSAEnv (varIdx v) env
        tupD    = TupRsingle $ (HMaybe . Just . hpure) `hfmap` idxs
        tupc = TupRsingle ec
    in (tupD, tupc)

computeClosedForm :: Bounds IG -> TripCount -> SCEVChainConstraint t -> DataConstraint t
computeClosedForm graphs tripCount chains =
  let ch = unwrapBCConstraint chains
    in
      if chainIsNonDecreasing graphs chains
        then
            bccPut (toCGType chains) $ (\graph (Exists (HMaybe x)) (HMaybe y) -> HMaybe $ do
            chain <- y
            diff  <- x
            computeClosedForm' (bccSingleType chains) graph diff chain)
        <$> graphs <*> tripCount <*> ch
        else hfmap (const empty) chains

computeClosedFormNoTripCount :: Bounds IG -> SCEVChainConstraint t -> DataConstraint t
computeClosedFormNoTripCount graphs chains =
     let (Bounds (HMaybe lch) _) = unwrapBCConstraint chains
    in
      if chainIsNonDecreasing graphs chains
        then 
            let lch' = HMaybe $ do
                    chain <- lch
                    computeClosedFormNoTripCount' chain
                in bccPut (toCGType chains) $ Bounds lch' hnothing
        else hfmap (const empty) chains

computeClosedFormNoTripCount' :: SCEVChain t -> Maybe (DiffExp ESSAIdx t)
computeClosedFormNoTripCount' (SCEVChain (BaseRecChain bd)) = Just $ Diff bd
computeClosedFormNoTripCount' (SCEVChain (ConsRecChain bd2 SDelay (BaseRecChain bd1))) = Just $ PhiDiff (Diff bd1) (Diff bd2)
computeClosedFormNoTripCount' (SCEVChain (ConsRecChain (BDiff Nothing _) SAdd (BaseRecChain bd1))) = Just $ Diff bd1
computeClosedFormNoTripCount' (SCEVChain (ConsRecChain (BDiff Nothing _) SMult (BaseRecChain bd1))) = Just $ Diff bd1
computeClosedFormNoTripCount' _ = Nothing

computeClosedForm' :: SingleType t -> IG -> BasicDiff ESSAIdx t' -> SCEVChain t -> Maybe (DiffExp ESSAIdx t)
computeClosedForm' _ _ _ (SCEVChain (BaseRecChain bd)) = Just $ Diff bd
computeClosedForm' _ _ _ (SCEVChain (ConsRecChain bd2 SDelay (BaseRecChain bd1))) = Just $ PhiDiff (Diff bd1) (Diff bd2)
computeClosedForm' tp graph tc (SCEVChain (ConsRecChain bd2 SAdd (BaseRecChain bd1))) =
    do
        tc' <- matchBasicDiff tc tp
        prod <- interpretPrimMul graph tc' bd2
        Diff <$> interpretPrimAdd graph prod bd1
computeClosedForm' tp graph tc (SCEVChain (ConsRecChain bd2 SMult (BaseRecChain bd1))) =
    do
        tc' <- matchBasicDiff tc tp
        pow <- interpretPrimPow graph bd2 tc'
        Diff <$> interpretPrimMul graph bd1 pow
computeClosedForm' _ _ _ _ = Nothing

matchBasicDiff :: BasicDiff ESSAIdx t' -> SingleType t -> Maybe (BasicDiff ESSAIdx t)
matchBasicDiff (BDiff Nothing a) _ = Just $ BDiff Nothing a
matchBasicDiff d@(BDiff (Just (ESSAIdx tp' _)) _) tp = case matchSingleType tp' tp of
    Just Refl -> Just d
    Nothing -> Nothing

diffIsPositive :: IG -> BasicDiff ESSAIdx t -> Bool
diffIsPositive g@(IG Lower _ _ _) bd = maybe False (>= (0 :: Int)) $ basicDiffToConst g bd
diffIsPositive _ _ = error "strict positivity should be checked via the Lower IG"

diffIsPositiveNonZero :: IG -> BasicDiff ESSAIdx t -> Bool
diffIsPositiveNonZero g@(IG Lower _ _ _) bd = maybe False (> (0 :: Int)) $ basicDiffToConst g bd
diffIsPositiveNonZero _ _ = error "strict positivity should be checked via the Lower IG"

chainIsNonDecreasing :: Bounds IG -> SCEVChainConstraint t -> Bool
chainIsNonDecreasing graphs s =
    let ch = runHMaybe $ _lower $ unwrapBCConstraint s
        g  = _lower graphs
        f ch' = case ch' of
            (SCEVChain (BaseRecChain _)) -> True
            (SCEVChain (ConsRecChain _ SDelay (BaseRecChain _)))  -> True
            (SCEVChain (ConsRecChain d  SAdd (BaseRecChain _)))  -> diffIsPositive g d
            (SCEVChain (ConsRecChain d2 SMult (BaseRecChain d1))) -> diffIsPositiveNonZero g d2 && diffIsPositive g d1
            _ -> False
        in maybe False f ch

newtype PolyBF = PolyBF
  { runPolyBF  :: forall t. IG -> BasicDiff ESSAIdx t -> BasicDiff ESSAIdx t -> Bool}
computeChains :: Bounds IG -> BCConstraint (HMaybe ESSAIdx) t -> SCEVConstraint t -> SCEVChainConstraint t
computeChains graphs bci bcs =
  let
    fs = bccPut (toCGType bci) $ hjust <$> (Tag <$> Bounds (PolyBF isLowerBound) (PolyBF isUpperBound))
    gs = bccPut (toCGType bci) $ hjust <$> (Tag <$> graphs)
  in hfmap (`hbind` f) (hzipWith4 (hzipWith4 HQuad) gs fs bci bcs)
  where
    f :: HQuad (Tag IG) (Tag PolyBF) ESSAIdx SCEVExp t -> HMaybe SCEVChain t
    f (HQuad g bf i (SCEVPhi (SCEVOp Add (SCEVVar idx) b) (SCEVOp Add (SCEVVar idx') b'))) | idx == idx' = f (HQuad g bf i (SCEVOp Add (SCEVVar idx) (SCEVPhi b b')))
    f (HQuad g bf i (SCEVPhi (SCEVOp Add (SCEVVar idx) b) (SCEVOp Add b' (SCEVVar idx')))) | idx == idx' = f (HQuad g bf i (SCEVOp Add (SCEVVar idx) (SCEVPhi b b')))
    f (HQuad g bf i (SCEVPhi (SCEVOp Add b (SCEVVar idx)) (SCEVOp Add (SCEVVar idx') b'))) | idx == idx' = f (HQuad g bf i (SCEVOp Add (SCEVVar idx) (SCEVPhi b b')))
    f (HQuad g bf i (SCEVPhi (SCEVOp Add b (SCEVVar idx)) (SCEVOp Add b' (SCEVVar idx')))) | idx == idx' = f (HQuad g bf i (SCEVOp Add (SCEVVar idx) (SCEVPhi b b')))

    f (HQuad g bf i (SCEVPhi (SCEVOp Mult (SCEVVar idx) b) (SCEVOp Mult (SCEVVar idx') b'))) | idx == idx' = f (HQuad g bf i (SCEVOp Mult (SCEVVar idx) (SCEVPhi b b')))
    f (HQuad g bf i (SCEVPhi (SCEVOp Mult (SCEVVar idx) b) (SCEVOp Mult b' (SCEVVar idx')))) | idx == idx' = f (HQuad g bf i (SCEVOp Mult (SCEVVar idx) (SCEVPhi b b')))
    f (HQuad g bf i (SCEVPhi (SCEVOp Mult b (SCEVVar idx)) (SCEVOp Mult (SCEVVar idx') b'))) | idx == idx' = f (HQuad g bf i (SCEVOp Mult (SCEVVar idx) (SCEVPhi b b')))
    f (HQuad g bf i (SCEVPhi (SCEVOp Mult b (SCEVVar idx)) (SCEVOp Mult b' (SCEVVar idx')))) | idx == idx' = f (HQuad g bf i (SCEVOp Mult (SCEVVar idx) (SCEVPhi b b')))

    f (HQuad g bf i (SCEVPhi (SCEVOp Add (SCEVVar idx) b) (SCEVVar idx'))) | idx == idx' = f (HQuad g bf i (SCEVOp Add (SCEVVar idx) (SCEVPhi b (fromConst (0 :: Int)))))
    f (HQuad g bf i (SCEVPhi (SCEVVar idx') (SCEVOp Add (SCEVVar idx) b))) | idx == idx' = f (HQuad g bf i (SCEVOp Add (SCEVVar idx) (SCEVPhi b (fromConst (0 :: Int)))))
    f (HQuad g bf i (SCEVPhi (SCEVOp Add b (SCEVVar idx)) (SCEVVar idx'))) | idx == idx' = f (HQuad g bf i (SCEVOp Add (SCEVVar idx) (SCEVPhi b (fromConst (0 :: Int)))))
    f (HQuad g bf i (SCEVPhi (SCEVVar idx') (SCEVOp Add b (SCEVVar idx)))) | idx == idx' = f (HQuad g bf i (SCEVOp Add (SCEVVar idx) (SCEVPhi b (fromConst (0 :: Int)))))

    f (HQuad g bf i (SCEVPhi (SCEVOp Mult (SCEVVar idx) b) (SCEVVar idx'))) | idx == idx' = f (HQuad g bf i (SCEVOp Mult (SCEVVar idx) (SCEVPhi b (fromConst (1 :: Int)))))
    f (HQuad g bf i (SCEVPhi (SCEVVar idx') (SCEVOp Mult (SCEVVar idx) b))) | idx == idx' = f (HQuad g bf i (SCEVOp Mult (SCEVVar idx) (SCEVPhi b (fromConst (1 :: Int)))))
    f (HQuad g bf i (SCEVPhi (SCEVOp Mult b (SCEVVar idx)) (SCEVVar idx'))) | idx == idx' = f (HQuad g bf i (SCEVOp Mult (SCEVVar idx) (SCEVPhi b (fromConst (1 :: Int)))))
    f (HQuad g bf i (SCEVPhi (SCEVVar idx') (SCEVOp Mult b (SCEVVar idx)))) | idx == idx' = f (HQuad g bf i (SCEVOp Mult (SCEVVar idx) (SCEVPhi b (fromConst (1 :: Int)))))

    f (HQuad (Tag graph) (Tag bf) idx (SCEVOp Add  (SCEVVar idx') invar))  | idx == idx' = HMaybe $ do
      invarD <- computeSCEVInvar graph (runPolyBF bf) invar
      return $ SCEVChain $ ConsRecChain invarD SAdd  $ BaseRecChain (fromESSA idx')
    f (HQuad (Tag graph) (Tag bf) idx (SCEVOp Add  invar (SCEVVar idx'))) | idx == idx' = HMaybe $ do
      invarD <- computeSCEVInvar graph (runPolyBF bf) invar
      return $ SCEVChain $ ConsRecChain invarD SAdd  $ BaseRecChain (fromESSA idx')
    f (HQuad (Tag graph) (Tag bf) idx (SCEVOp Mult (SCEVVar idx') invar))  | idx == idx' = HMaybe $ do
      invarD <- computeSCEVInvar graph (runPolyBF bf) invar
      return $ SCEVChain $ ConsRecChain invarD SMult $ BaseRecChain (fromESSA idx')
    f (HQuad (Tag graph) (Tag bf) idx (SCEVOp Mult invar (SCEVVar idx'))) | idx == idx' = HMaybe $ do
      invarD <- computeSCEVInvar graph (runPolyBF bf) invar
      return $ SCEVChain $ ConsRecChain invarD SMult $ BaseRecChain (fromESSA idx')

    f (HQuad _ _ idx (SCEVVar idx')) | idx == idx' =
      hjust $ SCEVChain $ BaseRecChain (fromESSA idx')
    f (HQuad (Tag graph) (Tag bf) idx' e) = HMaybe $ do
        invar <- computeSCEVInvar graph (runPolyBF bf) e
        return $ SCEVChain $ ConsRecChain invar SDelay (BaseRecChain (fromESSA idx'))

computeSCEVInvar :: IG -> (forall t' . IG -> BasicDiff ESSAIdx t' -> BasicDiff ESSAIdx t' -> Bool) -> SCEVExp t -> Maybe (BasicDiff ESSAIdx t)
computeSCEVInvar _ _ (SCEVInvar d) = Just d
computeSCEVInvar  graph f (SCEVPhi e1 e2) = do
  invar1 <- computeSCEVInvar graph f e1
  invar2 <- computeSCEVInvar graph f e2
  if f graph invar1 invar2 then return invar2
    else if f graph invar2 invar1 then return invar1
      else Nothing
computeSCEVInvar graph f (SCEVOp Add e1 e2) = do
  invar1 <- computeSCEVInvar graph f e1
  invar2 <- computeSCEVInvar graph f e2
  interpretPrimAdd graph  invar1 invar2
computeSCEVInvar graph f (SCEVOp Mult e1 e2) = do
  invar1 <- computeSCEVInvar graph f e1
  invar2 <- computeSCEVInvar graph f e2
  interpretPrimMul graph invar1 invar2
computeSCEVInvar _ _ _ = Nothing