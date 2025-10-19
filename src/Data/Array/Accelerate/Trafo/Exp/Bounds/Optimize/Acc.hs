{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
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
import Data.Maybe
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.LoopStack
import Data.Array.Accelerate.Trafo.Exp.Bounds.Optimize.Pi (withPi, putPiAssignment)
import qualified Data.Map as Map
import Data.Array.Accelerate.Array.Buffer (indexBuffer)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx
import qualified Debug.Trace as Debug

-- Top function to optimize Closed Acc code
optimizeBounds :: BCOperation op => PreOpenAcc op () t -> PreOpenAcc op () t
optimizeBounds acc =
    let ((optimizedFun, _), a) = runState (optimizeBounds' acc) emptyAnalysis
        in Debug.trace (show $ a ^. ig) optimizedFun

optimizeBounds'
    :: forall benv op t loops
    .  BCOperation op => PreOpenAcc op benv t
    -> BCState GroundR op loops '(benv, ()) (PreOpenAcc op benv t, AnalysisResult t ())

-- A bind inserts it's data constraints in the IG, and stores the control constraints in the environment, to be used on an eventual branch on the value
optimizeBounds' (Alet lhs un bnd e) = do
    (bnd', arBnd) <- optimizeBounds' bnd
    a <- get
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
      Just True -> do
        (t', arT) <- withPi True  optimizeBounds' t b
        return (t', arT)

      Just False -> do
        (e', arE) <- withPi False optimizeBounds' e b
        return (e', arE)

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

    let gArgs = diffArg1 dInit (bccsEmpty instr) (bccsEmpty instr)
    (g', urGuard) <- optimizeBoundsAFun' gArgs g
    let rGuard = mkFunRes1 urGuard

    redundant <- valOfBool (getSingle $ rGuard ^. rCS . rData)

    let ((it', _), a') = runState (optimizeAwhileBody (rGuard ^. rSCEV . rArgIdxs) (rGuard ^. rCS . rControl) it) (newLoopScope a)
    put $ popLoopScope a'

    case redundant of
      Just False ->
        return (Awhile un g' it' init, analysisResult dInit (bccsEmpty instr) (bccsEmpty instr))
      _ -> return $ identityResult $ Awhile un g' it' init


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
        d   = hfmap (varToDataConstraint  env) e
        c   = hfmap (varToControlConstraint env) e
        s   = hfmap (\v -> fromMaybe (hfmap (hfmap SCEVInvar) (varToClosedForm env v)) (indexLoopScopeStackGroundVar v (a ^. stack))) e
    return (instr, analysisResult d c s)

optimizeBoundsAFun :: BCOperation op => PreOpenAfun op () t -> PreOpenAfun op () t
optimizeBoundsAFun acc =
  let ((optimizedFun, _), _) = runState (optimizeBoundsAFun' (emptyConstraintsArgs acc) acc) emptyAnalysis
  in optimizedFun

optimizeBoundsAFun'
    :: (BCOperation op)
    => ConstraintsArgs (TypeToArgs t)
    -> PreOpenAfun op benv t
    -> BCState GroundR op loops '(benv, ())
        (PreOpenAfun op benv t, AnalysisResult (ReturnType t) (ArgsType t))
optimizeBoundsAFun' (ConstraintsArgsCons cnst br ch args) (Alam lhs f) = do
    a <- get
    let (a', idxs) = declBind lhs cnst br ch a
    let ((f', ar), a'') = runState (optimizeBoundsAFun' args f) a'
        ar' = ar & rSCEV . rArgIdxs %~ \x -> TupRpair x idxs
    put $ snd $ popBind lhs a''
    return (Alam lhs f', ar')
optimizeBoundsAFun' _ (Abody body) | BCBodyDict <- isBody body = do
    (body', ar) <- optimizeBounds' body
    return (Abody body', ar)

optimizeAwhileBody
    :: (BCOperation op)
    => TupR (BCConstraint (HMaybe ESSAIdx)) t
    -> ControlConstraints PrimBool
    -> PreOpenAfun op benv (t -> t)
    -> BCState GroundR op prev '(benv, ())
       (PreOpenAfun op benv (t -> t), AnalysisResult (ReturnType t) (ArgsType t))
optimizeAwhileBody idxs ctrl (Alam lhs (Abody body)) | BCBodyDict <- isBody body = do
    a <- get
    let a' = rebind lhs idxs (bccsEmpty body) a
    let ((body', _), a'') = runState (withPi True optimizeBounds' body ctrl) a'
    () <- putPiAssignment False (getSingle ctrl)
    let (argIdxs, a''') = popBind lhs a''
        d = hfmap (hfmap (hfmap fromESSA)) argIdxs
    put a'''
    return (Alam lhs (Abody body'), analysisResult d (bccsEmpty body) (bccsEmpty body))
optimizeAwhileBody _ _ _ = error "malformed While encountered"