{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.LoopStack where
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.ChainEnv
import Data.Kind
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.Type (ScalarType)
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.RecChain (SCEVExp (SCEVVar), SCEVConstraint)
import Data.Maybe (fromMaybe)
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAEnv (ESSAEnv, varToESSA)
--- === Stack of nested loops ===

class Frame f where
  declareF    :: LeftHandSide s v env env' 
              -> TupR (BCConstraint (HMaybe e)) v
              -> f e env
              -> f e env'
  popF        :: LeftHandSide s v env env' 
              -> f e env'
              -> f e env
  getSCEVEnv  :: f e t -> SCEVEnv e t

instance Frame SCEVEnv where
    declareF = declSCEVEnv
    popF = popSCEVEnv
    getSCEVEnv = id

type LoopScopeStackSCEV s op prev env = LoopScopeStack SCEVEnv SCEVExp s op prev env
data LoopScopeStack f (e :: Type -> Type) (s :: Type -> Type) op prev env where
    EmptyLoopScopeStack
        :: LoopScopeStack f e GroundR op '[] env
    EnterExpScope
        :: f e aenv
        -> LoopScopeStack f e GroundR op prev benv
        -> LoopScopeStack f e ScalarType (ArrayInstr benv) (Enter op benv : prev) aenv
    ConsLoopScopeStack
        :: f e env'
        -> LoopScopeStack f e s op prev env
        -> LoopScopeStack f e s op (ConsEnv env : prev) env'

data EnvKind = ConsEnv Type | Enter (Type -> Type) Type

declStack
    :: Frame f
    => LeftHandSide    s v  env env'
    -> TupR (BCConstraint (HMaybe e)) v
    -> LoopScopeStack f e s op prev env
    -> LoopScopeStack f e s op prev env'
declStack _ _ EmptyLoopScopeStack = EmptyLoopScopeStack
declStack lhs e (ConsLoopScopeStack frame st) = ConsLoopScopeStack (declareF lhs e frame) st
declStack lhs e (EnterExpScope frame st)      = EnterExpScope (declareF lhs e frame) st

popBindStack :: (Frame f)
    => LeftHandSide s v env env'
    -> LoopScopeStack f e s op prev env'
    -> LoopScopeStack f e s op prev env
popBindStack _ EmptyLoopScopeStack = EmptyLoopScopeStack
popBindStack lhs (ConsLoopScopeStack frame st) = ConsLoopScopeStack (popF lhs frame) st
popBindStack lhs (EnterExpScope      frame st) = EnterExpScope (popF lhs frame) st

indexLoopScopeStackExpVar :: (s ~ ScalarType, Frame f)
                          => ExpVar env t
                          -> LoopScopeStack f e s op prev env
                          -> Maybe (BCConstraint (HMaybe e) t)
indexLoopScopeStackExpVar v st = case st of
    (EnterExpScope      frame _) -> indexPrefixHList (varIdx v) (runSCEVEnv $ getSCEVEnv frame)
    (ConsLoopScopeStack frame _) -> indexPrefixHList (varIdx v) (runSCEVEnv $ getSCEVEnv frame)

indexLoopScopeStackParam :: (s ~ ScalarType, Frame f)
                          => ExpVar benv t
                          -> LoopScopeStack f e s op (Enter arrOp benv:ps) env
                          -> Maybe (BCConstraint (HMaybe e) t)
indexLoopScopeStackParam v st = case st of
    (EnterExpScope _ (ConsLoopScopeStack frame _)) -> indexPrefixHList (varIdx v) (runSCEVEnv $ getSCEVEnv frame)
    _ -> Nothing

indexLoopScopeStackUse :: (s ~ GroundR, Frame f)
                          => ExpVar benv t
                          -> LoopScopeStack f e s op prev benv
                          -> Maybe (BCConstraint (HMaybe e) (Buffer t))
indexLoopScopeStackUse v@(Var tp _) st | BCScalarDict <- reprBCScalar tp = case st of
    (ConsLoopScopeStack frame _) -> bccToBuffer <$> indexPrefixHList (varIdx v) (runSCEVEnv $ getSCEVEnv frame)
    _ -> Nothing

indexLoopScopeStackIndex :: forall t s f benv e ps op env arrOp
                          . (s ~ ScalarType, Frame f, TypeNotBuffer t)
                          => GroundVar benv (Buffer t)
                          -> LoopScopeStack f e s op (Enter arrOp benv:ps) env
                          -> Maybe (BCConstraint (HMaybe e) t)
indexLoopScopeStackIndex v@(Var (GroundRbuffer _) _) st = case st of
    (EnterExpScope _ (ConsLoopScopeStack frame _)) -> bccToScalar <$> indexPrefixHList (varIdx v) (runSCEVEnv $ getSCEVEnv frame)
    _ -> Nothing
indexLoopScopeStackIndex (Var (GroundRscalar tp) _) _ = case absurdScalarBuffer tp of {}

indexLoopScopeStackGroundVar :: (s ~ GroundR, Frame f)
                             => GroundVar env t
                             -> LoopScopeStack f e s op prev env
                             -> Maybe (BCConstraint (HMaybe e) t)
indexLoopScopeStackGroundVar v st = case st of
    EmptyLoopScopeStack          -> Nothing
    (ConsLoopScopeStack frame _) -> indexPrefixHList (varIdx v) (runSCEVEnv $ getSCEVEnv frame)

class VarToSCEVConstraint s varS t res where
    varToSCEVConstraint ::  LoopScopeStackSCEV s op prev env -> ESSAEnv env -> Var varS env t -> SCEVConstraint res

instance VarToSCEVConstraint ScalarType ScalarType t t where
    varToSCEVConstraint stack env v = fromMaybe (hfmap (hjust . SCEVVar) $ varToESSA env v) (indexLoopScopeStackExpVar v stack)

instance VarToSCEVConstraint GroundR GroundR t t where
    varToSCEVConstraint stack env v = fromMaybe (hfmap (hjust . SCEVVar) $ varToESSA env v) (indexLoopScopeStackGroundVar v stack)

instance VarToSCEVConstraint GroundR ScalarType t (Buffer t) where
    varToSCEVConstraint stack env v@(Var tp _) | BCScalarDict <- reprBCScalar tp = fromMaybe (bccToBuffer $ hfmap (hjust . SCEVVar) $ varToESSA env v) (indexLoopScopeStackUse v stack)