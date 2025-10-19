{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.ChainEnv where
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.RecChain
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints

data SCEVEnv e env where
    SCEVEnv :: { runSCEVEnv :: PrefixHList (BCConstraint (HMaybe e)) env } -> SCEVEnv e env
type SCEVEnvExps env = SCEVEnv SCEVExp env 

instance Empty (SCEVEnv e) where
    empty = SCEVEnv empty

declSCEVEnv 
    :: LeftHandSide  s v  env env' -> TupR (BCConstraint (HMaybe e)) v -> SCEVEnv e env -> SCEVEnv e env'
declSCEVEnv (LeftHandSideSingle _) (TupRsingle e) (SCEVEnv env) = SCEVEnv $ PCons e env
declSCEVEnv (LeftHandSidePair lhs1 lhs2) (TupRpair e1 e2) env = declSCEVEnv lhs2 e2 $ declSCEVEnv lhs1 e1 env
declSCEVEnv LeftHandSideUnit _ env = env
declSCEVEnv (LeftHandSideWildcard _) _ env = env
declSCEVEnv _ _ _ = error "mismatched tuples"

popSCEVEnv
    :: LeftHandSide s v env env'
    -> SCEVEnv e env'
    -> SCEVEnv e env
popSCEVEnv LeftHandSideUnit  ch = ch
popSCEVEnv (LeftHandSideWildcard _) ch = ch
popSCEVEnv (LeftHandSideSingle   _)  (SCEVEnv (PCons _ cs)) = SCEVEnv cs
popSCEVEnv (LeftHandSidePair lhs1 lhs2) ch =
        let ch' = popSCEVEnv lhs2 ch
            in popSCEVEnv lhs1 ch'
popSCEVEnv _ _ = error "mismatched tuples"

popSCEVEnv'
    :: (ToCGType s)
    => LeftHandSide s v env env'
    ->  SCEVEnv e env'
    -> (SCEVEnv e env, TupR (BCConstraint (HMaybe e)) v)
popSCEVEnv' LeftHandSideUnit  ch = (ch, TupRunit)
popSCEVEnv' (LeftHandSideWildcard t)    ch = (ch, mapTupR (\tp -> BCConstraint $ toCGType tp $ HBounds $ pure $ HMaybe Nothing) t)
popSCEVEnv' (LeftHandSideSingle   _)  (SCEVEnv (PCons c cs)) = (SCEVEnv cs, TupRsingle c)
popSCEVEnv' (LeftHandSidePair lhs1 lhs2) ch =
        let (ch', cs'  ) = popSCEVEnv' lhs2 ch
            (ch'', cs'') = popSCEVEnv' lhs1 ch'
            in (ch'', TupRpair cs'' cs')
popSCEVEnv' _ _ = error "mismatched tuples"
