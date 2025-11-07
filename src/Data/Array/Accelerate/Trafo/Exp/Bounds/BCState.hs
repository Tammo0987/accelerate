{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImpredicativeTypes #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.BCState where
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.IG
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.LoopStack
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAEnv
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Control.Monad.State
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints
import Data.Array.Accelerate.AST.LeftHandSide
import Lens.Micro.TH
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.RecChain
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx
import Data.Biapplicative
import Lens.Micro
import qualified Control.Arrow as Data.Bifunctor
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Idx (Idx)
import Data.Array.Accelerate.Array.Buffer
import Lens.Micro.Mtl
import GHC.Base (Applicative(liftA2))

data Analysis s op prev envs =
    Analysis
    {  _ig             :: Bounds IG
    ,  _stack          :: LoopScopeStackSCEV s op prev (GetByType s envs)
    ,  _essaEnvs       :: ESSAEnvs envs
    ,  _currentESSAIdx :: Bounds Int
    ,  _level          :: SType s }
makeLenses ''Analysis

emptyAnalysis :: Analysis GroundR op '[] '((), ())
emptyAnalysis = Analysis
  {  _ig             = emptyIGs
  ,  _stack          = EmptyLoopScopeStack
  ,  _essaEnvs       = ESSAEnvs { _essaEnvArr = HEmpty, _essaEnvExp = HEmpty }
  ,  _currentESSAIdx = Bounds 0 0
  ,  _level          = STypeGround
  }

data AnalysisResult t ts = AnalysisResult
  {  _rCS   :: RCS   t
  ,  _rSCEV :: RSCEV t ts
  }
makeLenses ''AnalysisResult

analysisResult :: DataConstraints t -> ControlConstraints t -> SCEVConstraints t -> AnalysisResult t ()
analysisResult d ctrlD ch = AnalysisResult (RCS d ctrlD) (RSCEV ch TupRunit)

type BCState s op prev envs = State (Analysis s op prev envs)

declBind
     :: LeftHandSide        s         bnd env env'
     -> DataConstraints               bnd
     -> ControlConstraints            bnd
     -> SCEVConstraints               bnd
     -> Analysis s op prev (PutByType s benv () env )
     -> (Analysis s op prev (PutByType s benv () env'), TupR (BCConstraint (HMaybe ESSAIdx)) bnd)
declBind lhs d br ch (Analysis g st (ESSAEnvs envArr envExp) i lvl) =
  let essaEnv = case lvl of
            STypeGround -> envArr
            STypeScalar -> envExp
      (idxs, newIdxs, essaEnv') = declESSAEnv lvl lhs br i essaEnv
      g' = insertConstraints idxs d g
  in case lvl of
            STypeGround -> (Analysis g' st' (ESSAEnvs essaEnv' envExp) newIdxs lvl, idxs)
              where st' = declStack lhs ch st
            STypeScalar -> (Analysis g' st' (ESSAEnvs envArr essaEnv') newIdxs lvl, idxs)
              where st' = declStack lhs ch st

rebind
  :: LeftHandSide s bnd env env'
  -> TupR (BCConstraint (HMaybe ESSAIdx)) bnd
  -> DataConstraints bnd
  -> SCEVConstraints bnd
  -> Analysis s op prev (PutByType s benv () env)
  -> Analysis s op prev (PutByType s benv () env')
rebind lhs idxs d ch (Analysis g st (ESSAEnvs envArr envExp) i lvl) =
  let essaEnv = case lvl of
                  STypeGround -> envArr
                  STypeScalar -> envExp
      essaEnv' = redeclESSAEnv lvl lhs idxs essaEnv
      g' = insertConstraints idxs d g
  in case lvl of
       STypeGround -> Analysis g' st' (ESSAEnvs essaEnv' envExp) i lvl
          where st'      = declStack lhs ch st
       STypeScalar -> Analysis g' st' (ESSAEnvs envArr essaEnv') i lvl
          where st'      = declStack lhs ch st

enterExpScope :: Analysis GroundR op prev '(benv, ()) -> Analysis ScalarType (ArrayInstr benv) (Enter op benv : prev) '(benv, ())
enterExpScope (Analysis g st envs i STypeGround) = Analysis g (EnterExpScope empty st) envs i STypeScalar

newLoopScope :: Analysis s op prev envs -> Analysis s op (ConsEnv (GetByType s envs) : prev) envs
newLoopScope (Analysis g st envs i STypeScalar) = Analysis g (ConsLoopScopeStack empty st) envs i STypeScalar
newLoopScope (Analysis g st envs i STypeGround) = Analysis g (ConsLoopScopeStack empty st) envs i STypeGround

popBind
    :: LeftHandSide s bnd env env'
    -> Analysis s op prev (PutByType s benv () env')
    -> (TupR (BCConstraint (HMaybe ESSAIdx)) bnd, Analysis s op prev (PutByType s benv () env ))
popBind lhs (Analysis g st (ESSAEnvs benv aenv) i STypeGround)
  = let (idxs, benv') = popESSAEnv STypeGround lhs benv
      in (idxs, Analysis g (popBindStack lhs st) (ESSAEnvs benv' aenv) i STypeGround)
popBind lhs (Analysis g st (ESSAEnvs benv aenv) i STypeScalar)
  = let (idxs, aenv') = popESSAEnv STypeScalar lhs aenv
      in (idxs, Analysis g (popBindStack lhs st) (ESSAEnvs benv aenv') i STypeScalar)

mkArrayFuncRes :: (TypeNotBuffer t) => TypeR t -> AnalysisResult t ts -> AnalysisResult (Buffers t) ()
mkArrayFuncRes tpr (AnalysisResult (RCS a b) (RSCEV c _))= AnalysisResult (RCS (bccsToBuffers tpr a) (bccsToBuffers tpr b)) (RSCEV (bccsToBuffers tpr c) TupRunit)

extendResWithEmpty :: (HasGroundsR a) => AnalysisResult t ts -> a t' -> AnalysisResult (t, t') ts
extendResWithEmpty (AnalysisResult (RCS a b) (RSCEV c argC)) g = AnalysisResult (RCS a' b') (RSCEV c' argC)
  where a' = TupRpair a (bccsEmpty g)
        b' = TupRpair b (bccsEmpty g)
        c' = TupRpair c (bccsEmpty g)

type family PopLoopScope level op prev envs where
  PopLoopScope GroundR    op (ConsEnv     _ : prev) envs = Analysis GroundR    op prev envs
  PopLoopScope ScalarType op (ConsEnv     _ : prev) envs = Analysis ScalarType op prev envs
  PopLoopScope ScalarType op (Enter arrOp _ : prev) envs = Analysis GroundR    arrOp prev envs

type family PutByTypeAndCons s c benv aenv env where
  PutByTypeAndCons GroundR    ConsEnv   benv aenv env = '(env, aenv)
  PutByTypeAndCons ScalarType ConsEnv   benv aenv env = '(benv, env)
  PutByTypeAndCons ScalarType (Enter _) benv aenv env = '(env, aenv)

popLoopScope
    :: Analysis     s op (c p:prev) (PutByTypeAndCons s c benv () p)
    -> PopLoopScope s op (c p:prev) (PutByTypeAndCons s c benv () p)
popLoopScope (Analysis g (ConsLoopScopeStack _ st) envs i STypeGround) = Analysis g st envs i STypeGround
popLoopScope (Analysis g (ConsLoopScopeStack _ st) envs i STypeScalar) = Analysis g st envs i STypeScalar
popLoopScope (Analysis g (EnterExpScope      _ st) envs i STypeScalar) = Analysis g st envs i STypeGround


dataToBasic :: DataConstraint t -> BCState s op prev env (BCConstraint (HMaybe (BasicDiff ESSAIdx)) t)
dataToBasic = flushToIG bindDiffExp

indexToBasic :: DataConstraint t -> BCState s op prev env (BCConstraint (HMaybe (BasicDiff ESSAIdx)) t)
indexToBasic = flushToIG newBindDiffExp

dataToESSA :: DataConstraint t -> BCState s op prev env (BCConstraint (HMaybe ESSAIdx) t)
dataToESSA = flushToIG bindDiffExp'

flushToIG :: (forall t' . SingleType t' -> ESSADiffExp t' -> State (Int, IG) (Maybe (r t'))) -> DataConstraint t -> BCState s op prev env (BCConstraint (HMaybe r) t)
flushToIG f bcd = do
  a <- get
  let (res, (newIdxB, newIgB)) = second distribute $ distribute $ fmap unTag $ unwrapBCConstraint $
          bccBind bcd $ \md -> bccPut (toCGType bcd) $ fmap retag $ do
            graph <- a ^. ig
            index <- a ^. currentESSAIdx
            let ret = hbind md $ \d -> hreturn $ Tag $ first HMaybe $ runState (f (bccSingleType bcd) d) (index, graph)
            return $ hmaybe (Tag (empty, (index, graph))) id ret
  modify (currentESSAIdx .~ newIdxB)
  modify (ig             .~ newIgB)
  return $ bccPut (toCGType bcd) res

bindCS :: (Empty res)
       => DataConstraint t
       -> DataConstraint t
       -> (forall a . IG -> BasicDiff ESSAIdx a -> BasicDiff ESSAIdx a -> res a)
       -> BCState s op prev envs (BCConstraint res t)
bindCS bcd1 bcd2 f = do
  a  <- get
  c1 <- dataToBasic bcd1
  c2 <- dataToBasic bcd2
  return $ hzipWith3 (\(Tag graph) mc1 mc2 -> let m = hbind mc1 $ \c1' -> hbind mc2 $ \c2' -> hreturn $ f graph c1' c2' in hmaybe empty id m)
   (bccPut (toCGType bcd1) $ Tag <$> _ig a) c1 c2

bindCS2 :: (Empty res)
       => DataConstraint t
       -> DataConstraint t
       -> (forall a . IG -> BasicDiff ESSAIdx a -> BasicDiff ESSAIdx a -> res a)
       -> (forall a . IG -> BasicDiff ESSAIdx a -> BasicDiff ESSAIdx a -> res a)
       -> BCState s op prev envs (BCConstraint res t)
bindCS2 bcd1 bcd2 lf uf = do
  a  <- get
  c1 <- dataToBasic bcd1
  c2 <- dataToBasic bcd2
  return $ hbizipWith3 (\(Tag graph) mc1 mc2 -> let m = hbind mc1 $ \c1' -> hbind mc2 $ \c2' -> hreturn $ lf graph c1' c2' in hmaybe empty id m)
                       (\(Tag graph) mc1 mc2 -> let m = hbind mc1 $ \c1' -> hbind mc2 $ \c2' -> hreturn $ uf graph c1' c2' in hmaybe empty id m)
   (bccPut (toCGType bcd1) $ Tag <$> _ig a) c1 c2

newBindDiffExp ::
  SingleType t -> ESSADiffExp t
  -> State (Int, IG) (Maybe (BasicDiff ESSAIdx t))
newBindDiffExp _  DiffUndef = return Nothing
newBindDiffExp tp d = do
  modify (Data.Bifunctor.first (+1))
  (newIdx, graph) <- get
  let newESSA = ESSAIdx tp newIdx
      newGraph = insertD newESSA d graph
  put (newIdx, newGraph)
  return $ Just $ hpure newESSA

bindDiffExp ::
  SingleType t -> ESSADiffExp t
  -> State (Int, IG) (Maybe (BasicDiff ESSAIdx t))
bindDiffExp _ (Diff bd) = return $ Just bd
bindDiffExp tp (PhiDiff DiffUndef d) = bindDiffExp tp d
bindDiffExp tp (PhiDiff d DiffUndef) = bindDiffExp tp d
bindDiffExp tp c@(PhiDiff _ _) = do
  modify (Data.Bifunctor.first (+1))
  (newIdx, graph) <- get
  let newESSA = ESSAIdx tp newIdx
      newGraph = insertD newESSA c graph
  put (newIdx, newGraph)
  return $ Just $ hpure newESSA
bindDiffExp _ DiffUndef = return Nothing

bindDiffExp' ::
  SingleType t -> ESSADiffExp t
  -> State (Int, IG) (Maybe (ESSAIdx t))
bindDiffExp' _  (Diff (BDiff (Just i) 0)) = return $ Just i
bindDiffExp' tp (Diff bd) = do
  modify (Data.Bifunctor.first (+1))
  (newIdx, graph) <- get
  let newESSA  = ESSAIdx tp newIdx
      newGraph = insertD newESSA (Diff bd) graph
  put (newIdx, newGraph)
  return $ Just newESSA
bindDiffExp' tp (PhiDiff DiffUndef d) = bindDiffExp' tp d
bindDiffExp' tp (PhiDiff d DiffUndef) = bindDiffExp' tp d
bindDiffExp' tp c@(PhiDiff _ _) = do
  modify (Data.Bifunctor.first (+1))
  (newIdx, graph) <- get
  let newESSA  = ESSAIdx tp newIdx
      newGraph = insertD newESSA c graph
  put (newIdx, newGraph)
  return $ Just newESSA
bindDiffExp' _ DiffUndef = return Nothing

insertBCConstraintsInIGD :: TupR (BCConstraint (HMaybe ESSAIdx)) t -> DataConstraints t -> BCState s op prev env ()
insertBCConstraintsInIGD i d = do
  a <- get
  let graph = insertConstraints i d (a ^. ig)
  put $ a & ig .~ graph
  return ()

insertBCConstraintsInIGDOneDir :: TupR (BCConstraint (HMaybe ESSAIdx)) t -> DataConstraints t -> BCState s op prev env ()
insertBCConstraintsInIGDOneDir i d = do
  a <- get
  let graph = insertConstraints i d (a ^. ig)
  put $ a & ig .~ graph
  return ()

newtype PairF env a = PairF (Idx env a, EnvElem a)
updateEnvFromFlat
  :: TupR (Idx env) t
  -> TupR EnvElem t
  -> State (ESSAEnv env) ()
updateEnvFromFlat idxs elems =
  void . traverseTupR (\(PairF (i, e@(EnvElem _ _))) ->
           modify (modifyESSAEnv (const e) i) >> pure (PairF (i,e))
         ) $ hzipWith (curry PairF) idxs elems

applyEnvUpdate :: TupR (Idx env) t -> TupR EnvElem t -> ESSAEnv env -> ESSAEnv env
applyEnvUpdate idxs elems = execState (updateEnvFromFlat idxs elems)

mkInductionVars :: DataConstraints t -> BCState s op prev env (SCEVConstraints t, TupR (BCConstraint (HMaybe ESSAIdx)) t)
mkInductionVars d = do
  x <- traverseTupR dataToESSA d
  return (hfmap (hfmap (hfmap SCEVVar)) x, x)

mkInvarVars :: DataConstraints t -> BCState s op prev env (SCEVConstraints t)
mkInvarVars d = do
  x <- traverseTupR dataToBasic d
  return (hfmap (hfmap (hfmap SCEVInvar)) x)

bccReallocateMut :: BCConstraint ESSAIdx t -> BCState s op prev env (BCConstraint ESSAIdx t)
bccReallocateMut ixs = do
  modify $ currentESSAIdx %~ fmap (+1)
  i <- use currentESSAIdx
  let b = unwrapBCConstraint ixs
      ixs' = (\(ESSAIdx tp _) e -> ESSAIdx tp e) <$> b <*> i
  return $ bccPut (toCGType ixs) ixs'

bccToConst :: DataConstraint t -> BCState s op prev env (Bounds (Maybe Int))
bccToConst d = do
  b <- dataToBasic d
  g <- use ig
  let b' = runHMaybe <$> unwrapBCConstraint b
      r  = liftA2 (\g' mbd -> mbd >>= basicDiffToConst g') g b'
  return r