{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.Optimize.Acc where
import Data.Array.Accelerate.Trafo.Exp.Bounds.ArrayInstr
import Data.Array.Accelerate.Trafo.Exp.Bounds.BCState
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Control.Monad.State
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAEnv
import Data.Array.Accelerate.Trafo.Exp.Bounds.Optimize.Exp
import Prelude hiding (init)
import Lens.Micro
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.ConstraintArgs
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.RecChain
import Data.Array.Accelerate.Representation.Type (TupR(..))
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.LoopStack
import Data.Array.Accelerate.Trafo.Exp.Bounds.Optimize.Pi (withPi, putPiAssignment, withPiPersist)
import qualified Data.Map as Map
import Data.Array.Accelerate.Array.Buffer (indexBuffer)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx

--------------------------------------------------------
-- Array level bounds inference and assertion removal --
--------------------------------------------------------

optimizeBounds'
    :: forall benv op t loops
    .  BCOperation op => PreOpenAcc op benv t
    -> BCState GroundR op loops '(benv, ()) (PreOpenAcc op benv t, AnalysisResult t ())
-- 
optimizeBounds' (Aassert g e) = do
    a <- get
    let ((g', arG), a') = runState (optimizeBoundsExp g) (enterExpScope a)
    put $ popLoopScope a'
    redundant <- isAlwaysTrueData (getSingle $ arG ^. rCS . rData)
    if redundant then do
        -- if the assertion is redundant pi-information does not introduce any useful information
            (e', arE) <- optimizeBounds' e
            return (e', arE)
        else do
            -- Turn assertion domination on and off
            (e', arE) <- withPiPersist True optimizeBounds' e (arG ^. rCS.rControl)
            -- (e', arE) <- optimizeBounds' e
            return (Aassert g' e', arE)

-- A bind inserts it's data constraints in the IG, and stores the control constraints in the environment, to be used on an eventual branch on the value
optimizeBounds' (Alet lhs un bnd e) = do
    (bnd', arBnd) <- optimizeBounds' bnd
    a <- get
    -- TODO: This current implementation assumes that 'bnd' runs before 'e', and that
    -- if something is asserted in 'bnd' we don't have to assert it again in 'e'.
    -- However, later passes may reorder the program and break this assumption.
    -- Hence we should not propagate information from 'bnd' when analyzing 'e' here.
    -- We might want to enable rotation on Aassert in alet' again so we can still
    -- analyze and optimize away many assertions here.
    let (a', _) = declBind lhs (arBnd ^. rCS.rData) (arBnd ^. rCS.rControl) (arBnd ^. rSCEV.rSCEVExp) a
    let ((e', arD'), a'') = runState (optimizeBounds' e) a'
    put $ snd $ popBind lhs a''
    return (Alet lhs un bnd' e', arD')

-- Delegate to expression level constraint analysis and trivially lift the same constraints to Array Level
optimizeBounds' (Compute expr) = do
    a <- get
    let ((expr', ar), a') = runState (optimizeBoundsExp expr) (enterExpScope a)
    put $ popLoopScope a'
    return (Compute expr', ar)

optimizeBounds' (Exec op args) = do
  let AbstInterpOperation absInt = bcOperation op
  (BCOptOperation op' args', idxs, varIdxs, ar, _) <- absInt args
  insertBCConstraintsInIGDOneDir (hfmap (hfmap hjust) idxs) (ar ^. rCS.rData)
  let ctrls = hzipWith EnvElem idxs (ar ^. rCS.rControl)
  modify (essaEnvs . essaEnvArr %~ applyEnvUpdate (hfmap varIdx varIdxs) ctrls)
  return $ identityResult (Exec op' args')

-- The control constraints of the guard variable are retrieved from the environment. 
optimizeBounds' (Acond g t e) = do
    a <- get
    let env = a ^. essaEnvs . essaEnvArr
        dGuard = varToDataConstraint env g
        b = TupRsingle $ varToControlConstraint env g
    redundant <- valOfBool dGuard

    case redundant of
      Just True ->
        withPi True  optimizeBounds' t b

      Just False -> do
        withPi False optimizeBounds' e b

      Nothing -> do
        (t', arT) <- withPi True  optimizeBounds' t b
        (e', arE) <- withPi False optimizeBounds' e b

        let d = phi (arT ^. rCS . rData) (arE ^. rCS . rData)
            c = hzipWith (hzipWith
                            (zipControlMaps (Map.intersectionWith PhiDiff)
                                            (Map.intersectionWith PhiDiff)))
                         (arT ^. rCS . rControl) (arE ^. rCS . rControl)
            s = hzipWith (hzipWith $ hzipWith SCEVPhi)
                          (arT ^. rSCEV . rSCEVExp) (arE ^. rSCEV . rSCEVExp)

        return (Acond g t' e', analysisResult d c s)

optimizeBounds' instr@(Awhile un g it init)
  | BCBodyDict <- oneParamAfunc it
  , BCBodyDict <- oneParamAfunc g = do
    a <- get
    let env = a ^. essaEnvs . essaEnvArr

    let dInit = hfmap (varToDataConstraint env) init

    let gArgsInit = diffArg1 (NewBindArg dInit (bccsEmpty instr) (bccsEmpty instr))
    -- Optimize guard for first iteration
    (_, urGuardInit) <- optimizeBoundsAFun' gArgsInit g
    let rGuardInit = mkFunRes1 urGuardInit

    redundant <- valOfBool (getSingle $ rGuardInit ^. rCS . rData)

    case redundant of
      Just False ->
        -- Condition is always False, so we won't do any iterations
        return (Return init, analysisResult dInit (bccsEmpty instr) (bccsEmpty instr))
      _ -> do
        -- Optimize guard for any iteration.
        -- For reasoning behind this, see 'While' in the Exp analysis.
        let gArgs = diffArg1 (NewBindArg (bccsEmpty instr)  (bccsEmpty instr) (bccsEmpty instr))
        (g', urGuard) <- optimizeBoundsAFun' gArgs g
        let rGuard = mkFunRes1 urGuard

        -- traverse once to get SCEV information
        (sAcc, iAcc) <- mkInductionVars dInit
        let ((_, arIt), _) = runState (optimizeAwhileBody (rGuard ^. rSCEV . rArgIdxs) (bccsEmpty init) sAcc (rGuard ^. rCS . rControl) it) (newLoopScope a)
            sIt = arIt ^. rSCEV . rSCEVExp
            chIt = hzipWith (computeChains (a ^. ig)) iAcc sIt
            dIt = hfmap (computeClosedFormNoTripCount (a ^. ig)) chIt

        -- traverse again with more context
        let ((it', _), a') = runState (optimizeAwhileBody (rGuard ^. rSCEV . rArgIdxs) dIt (bccsEmpty init) (rGuard ^. rCS . rControl) it) (newLoopScope a)
        put $ popLoopScope a'

        return $ identityResult $ Awhile un g' it' init

optimizeBounds' instr@(Unit v@(Var tp _)) =
    case tp of
        (SingleScalarType (NumSingleType (IntegralNumType TypeInt))) -> do
            a <- get
            let env = a ^. essaEnvs . essaEnvArr
                st  = a ^. stack
                d = bccsToBuffers (TupRsingle tp) $ TupRsingle $ varToDataConstraint env v
                c = bccsToBuffers (TupRsingle tp) $ TupRsingle $ varToControlConstraint env v
                s = TupRsingle $ varToSCEVConstraint st env v
            return (instr, analysisResult d c s)
        _ -> return $ identityResult instr

optimizeBounds' instr@(Use tp i bf) =
    case tp of
        (SingleScalarType (NumSingleType (IntegralNumType TypeInt))) ->
            if i > 0 then
                let (Bounds maxC minC) = foldr (\index (Bounds l u)-> let e = indexBuffer tp bf index in Bounds (min e l) (max e u)) (Bounds (maxBound :: Int) (minBound :: Int)) [0..i-1]
                    b = pure (hjust $ fromConst minC `PhiDiff` fromConst maxC)
                    d = BCConstraint $ BufferConstraint tp $ toCSType tp $ HBounds b
                    in return (instr, analysisResult (TupRsingle d) (bccsEmpty instr) (bccsEmpty instr))
            else return $ identityResult instr
        _ -> return $ identityResult instr

optimizeBounds' instr@(Alloc _sh _tp _vars) = return $ identityResult instr
optimizeBounds' instr@(Return e) = do
    a <- get
    let env = a ^. essaEnvs . essaEnvArr
        st  = a ^. stack
        d   = hfmap (varToDataConstraint  env) e
        c   = hfmap (varToControlConstraint env) e
        s   = hfmap (varToSCEVConstraint st env) e
    return (instr, analysisResult d c s)

optimizeBounds' instr@(Manifest e) = do
    a <- get
    let env = a ^. essaEnvs . essaEnvArr
        st  = a ^. stack
        d   = varToDataConstraint  env e
        c   = varToControlConstraint env e
        s   = varToSCEVConstraint st env e
    return (instr, analysisResult (TupRsingle d) (TupRsingle c) (TupRsingle s))


#if ACCELERATE_OPTIMIZE_ASSERTIONS
optimizeBoundsAFun :: BCOperation op => PreOpenAfun op () t -> PreOpenAfun op () t
optimizeBoundsAFun acc =
  let ((optimizedFun, _), _a) = runState (optimizeBoundsAFun' (emptyConstraintsArgs acc) acc) emptyAnalysis
    in optimizedFun
#else
optimizeBoundsAFun :: BCOperation op => PreOpenAfun op () t -> PreOpenAfun op () t
optimizeBoundsAFun acc = acc
#endif

optimizeBoundsAFun'
    :: (BCOperation op)
    => ConstraintsArgs (TypeToArgs t)
    -> PreOpenAfun op benv t
    -> BCState GroundR op loops '(benv, ())
        (PreOpenAfun op benv t, AnalysisResult (ReturnType t) (ArgsType t))
optimizeBoundsAFun' (ConstraintsArgsCons (NewBindArg d ctrl ch) args) (Alam lhs f) = do
    a <- get
    let (a', idxs) = declBind lhs d ctrl ch a
    let ((f', ar), a'') = runState (optimizeBoundsAFun' args f) a'
        ar' = ar & rSCEV . rArgIdxs %~ \x -> TupRpair x idxs
    put $ snd $ popBind lhs a''
    return (Alam lhs f', ar')
optimizeBoundsAFun' (ConstraintsArgsCons (KeepBindArg _) _) (Alam _ _) = error "unexpected bind-preserving function at array level"
optimizeBoundsAFun' _ (Abody body) | BCBodyDict <- isBody body = do
    (body', ar) <- optimizeBounds' body
    return (Abody body', ar)

optimizeAwhileBody
    :: (BCOperation op)
    => TupR (BCConstraint (HMaybe ESSAIdx)) t
    -> DataConstraints t
    -> SCEVConstraints t
    -> ControlConstraints PrimBool
    -> PreOpenAfun op benv (t -> t)
    -> BCState GroundR op prev '(benv, ())
       (PreOpenAfun op benv (t -> t), AnalysisResult (ReturnType t) (ArgsType t))
optimizeAwhileBody idxs d s ctrl (Alam lhs (Abody body)) | BCBodyDict <- isBody body = do
    a <- get
    let a' = rebind lhs idxs d s a
        ((body', ar), a'') = runState (withPi True optimizeBounds' body ctrl) a'
        (_, a''') = popBind lhs a''
    put a'''
    () <- putPiAssignment False (getSingle ctrl)
    return (Alam lhs (Abody body'), analysisResult (bccsEmpty body) (bccsEmpty body) (ar ^. rSCEV . rSCEVExp))
optimizeAwhileBody _ _ _ _ _ = error "malformed While encountered"
