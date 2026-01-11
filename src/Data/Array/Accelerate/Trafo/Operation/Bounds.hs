{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.Bounds
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.Bounds (
  boundsOptimizeAfun
) where

import Data.Array.Accelerate.AST.Environment
import qualified Data.Array.Accelerate.AST.Graph as Graph
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.WeakenedEnvironment
import Data.Array.Accelerate.Trafo.SkipEnvironment
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error

import Data.Array.Accelerate.Trafo.Operation.Bounds.Algebra
import Data.Array.Accelerate.Trafo.Operation.Bounds.Environment

boundsOptimizeAfun
  :: forall op f.
     OperationAfun op () f
  -> OperationAfun op () f
boundsOptimizeAfun = snd . boundsOptimizeOpenAfun emptyEnv

boundsOptimizeOpenAfun
  :: forall benv op f.
     BoundsEnv benv ()
  -> OperationAfun op benv f
  -> (IdxSet benv, OperationAfun op benv f)
boundsOptimizeOpenAfun env@(BoundsEnv _ _ zero _) = \case
  Alam lhs f
    | env1 <- env `pushBuffers` (lhs, bottomsGround zero $ lhsToTupR lhs)
    , (modified, f') <- boundsOptimizeOpenAfun env1 f ->
      (IdxSet.drop' lhs modified, Alam lhs f')
  Abody acc
    | (modified, _, _, acc') <- boundsOptimizeAcc env acc ->
      (modified, Abody acc')

boundsOptimizeAcc
  :: forall benv op t.
     BoundsEnv benv ()
  -> OperationAcc op benv t
  -- Returns the set of arrays that have been modified,
  -- A new BoundsEnv (extended with new information from this term),
  -- the bounds of the return value and a transformed term.
  -> (IdxSet benv, BoundsEnv benv (), TermBounds (UniformEnv benv ()) t, OperationAcc op benv t)
boundsOptimizeAcc env@(BoundsEnv _ _ zero _) acc = case acc of
  Exec op args -> undefined

  Return vars ->
    ( IdxSet.empty
    , env
    , mapTupR (boundVar zero . accIdx env . varIdx) vars
    , Return vars )

  Manifest var
    | ix <- accIdx env $ varIdx var
    -> (IdxSet.empty, env, TupRsingle $ boundVar zero ix, Manifest var)

  Compute expr
    | (bounds, expr') <- boundsOptimizeExp env expr
    -> (IdxSet.empty, env, bounds, Compute expr')

  Unit var
    | bound <- boundVar zero $ accIdx env $ varIdx var
    -> (IdxSet.empty, env, TupRsingle $ castTermBound bound, Unit var)

  Alet lhs uniquenesses bnd body
    | (modified1, env1, bndBounds, bnd') <- boundsOptimizeAcc env bnd
    , env2 <- env1 `pushBuffers` (lhs, bndBounds)
    -- If this binds a single expression, an assertion or an assumption,
    -- mark this binding in the environment
    , env3 <- case lhs of
      LeftHandSideSingle _
        | Compute expr <- bnd -> env2{ boundsBindings = boundsBindings env1 `WPushB` weaken (weakenSucc weakenId) (BindExp expr) }
        | Aassert expr <- bnd -> env2{ boundsBindings = boundsBindings env1 `WPushB` weaken (weakenSucc weakenId) (BindAssertAssume expr) }
        | Aassume expr <- bnd -> env2{ boundsBindings = boundsBindings env1 `WPushB` weaken (weakenSucc weakenId) (BindAssertAssume expr) }
      _ -> env2
    , (modified2, env4, bodyBounds, body') <- boundsOptimizeAcc env3 body
    , (graph, bodyBounds') <- strengthenBoundsWithBufferLHS (boundsGraph env4) lhs bodyBounds ->
      ( modified1 `IdxSet.union` IdxSet.drop' lhs modified2
      , env{ boundsGraph = graph }
      , bodyBounds'
      , Alet lhs uniquenesses bnd' body'
      )

  Acond cond true false -> undefined
  Awhile uniquenesses cond step initial -> undefined

  Fence set body -> undefined

  -- Default
  Alloc{} -> defaultBottom
  Use{} -> defaultBottom
  Aassert{} -> defaultBottom
  Aassume{} -> defaultBottom
  where
    -- Default, for expressions that don't mutate buffers,
    -- have no subexpressions and whose bound should be bottom.
    defaultBottom :: (IdxSet benv, BoundsEnv benv (), TermBounds (UniformEnv benv ()) t, OperationAcc op benv t)
    defaultBottom = (IdxSet.empty, env, bottomsGround zero $ groundsR acc, acc)

boundsOptimizeFun
  :: BoundsEnv benv env
  -> OpenFun env benv f
  -> OpenFun env benv f
boundsOptimizeFun env@(BoundsEnv _ _ zero _) = \case
  Lam lhs f
    | env' <- env `pushScalars` (lhs, bottoms zero $ lhsToTupR lhs) ->
      Lam lhs $ boundsOptimizeFun env' f
  Body expr -> Body $ snd $ boundsOptimizeExp env expr

boundsOptimizeExp
  :: forall benv env t.
     BoundsEnv benv env
  -> OpenExp env benv t
  -> (TermBounds (UniformEnv benv env) t, OpenExp env benv t)
boundsOptimizeExp env@(BoundsEnv _ _ zero _) expr = detectConst env $ case expr of
  Const (SingleScalarType (NumSingleType (IntegralNumType tp))) val
    | IntegralDict <- integralDict tp ->
      ( TupRsingle $ boundConst zero $ fromIntegral val
      , expr )
  
  Const tp _ ->
    ( TupRsingle $ bottom zero tp
    , expr )

  Undef tp ->
    ( TupRsingle $ undefBound zero tp
    , expr )

  Let lhs bnd body
    | (bndBounds, bnd') <- boundsOptimizeExp env bnd
    , env' <- env `pushScalars` (lhs, bndBounds)
    , (bodyBounds, body') <- boundsOptimizeExp env' body ->
      ( snd $ strengthenBoundsWithScalarLHS @benv (boundsGraph env') lhs bodyBounds
      , Let lhs bnd' body' )

  Evar (Var _ ix)
    | ix' <- expIdx env ix ->
      -- Mark this value as equal to the variable
      ( TupRsingle $ boundVar zero ix', expr )
  ArrayInstr arr arg -> case arr of
    Parameter (Var _ ix)
      | ix' <- accIdx env ix ->
        -- Mark this value as equal to the variable
        ( TupRsingle $ boundVar zero ix', expr )

    Index (Var (GroundRscalar tp) _) -> bufferImpossible tp
    Index v@(Var (GroundRbuffer _) ix)
      | ix' <- accIdx env ix ->
        -- This value has the same bounds as the buffer.
        ( TupRsingle $ TermBound
            (mapPartialEnv (\(Graph.InEdge (Edge d)) -> Graph.InEdge $ Edge d) $ Graph.inn (boundsGraph env) ix')
            (mapPartialEnv (\(Edge d) -> Edge d) $ Graph.out (boundsGraph env) ix')
        , ArrayInstr (Index v) $ travE arg
        )

  Foreign tp asm f x -> (bottoms zero tp, Foreign tp asm f $ travE x) -- TODO: Optimize the fallback of Foreign
  Pair a b
    | (aBounds, a') <- boundsOptimizeExp env a
    , (bBounds, b') <- boundsOptimizeExp env b ->
      (TupRpair aBounds bBounds, Pair a' b')
  Nil -> (TupRunit, Nil)

  -- Analysis doesn't (yet) track SIMD vectors
  VecPack   vecR e -> bottomExpr $ VecPack   vecR $ travE e
  VecUnpack vecR e -> bottomExpr $ VecUnpack vecR $ travE e

  ToIndex shr sh ix -> bottomExpr $ ToIndex shr (travE sh) (travE ix)
  FromIndex shr sh ix
    | (shBounds, sh') <- boundsOptimizeExp env sh
    , (TupRsingle ixBound, ix') <- boundsOptimizeExp env ix ->
      (fromIndex zero shr shBounds ixBound, FromIndex shr sh' ix')
  
  ShapeSize shr sh -> bottomExpr $ ShapeSize shr (travE sh)

  Case _ [] (Just def) -> boundsOptimizeExp env def
  Case _ [] Nothing -> internalError "Illegal empty case"
  Case tag alts def
    | (bounds, alts', def') <- caseAlts alts def ->
      (bounds, Case (travE tag) alts' def')
  
  Cond c true false -> case travE c of
    -- Check if the condition is already known based on the bounds analysis
    Const _ 1 -> boundsOptimizeExp env true
    Const _ 0 -> boundsOptimizeExp env false

    c'
      | (trueBounds, true') <- boundsOptimizeExp (assumeTrue env c') true
      , (falseBounds, false') <- boundsOptimizeExp (assumeFalse env c') false ->
        ( unions (makeTransitives env trueBounds) (makeTransitives env falseBounds)
        , Cond c' true' false' )

  Assert c body -> case travE c of
    Const _ 1 -> boundsOptimizeExp env body
    c'@(Const _ 0) -> Assert c' <$> boundsOptimizeExp env (undefs $ expType body)
    c'
      | (_, body') <- boundsOptimizeExp (assumeTrue env c') body ->
        -- Don't propagate the bounds of the body,
        -- as acting on them could cause this expression to not be used any more,
        -- and that could cause that the assertion is not ran at all.
        bottomExpr $ Assert c' body'

  Assume c body -> case travE c of
    Const _ 1 -> boundsOptimizeExp env body
    Const _ 0 -> boundsOptimizeExp env (undefs $ expType body)
    c'
      | (bodyBounds, body') <- boundsOptimizeExp (assumeTrue env c') body ->
        (bodyBounds, Assume c' body')

  -- TODO: Add 'assumeTrue' on cond to step.
  -- Difficulty: cond and step are functions that may build different environments,
  -- as their left hand sides may be differehte
  While cond step initial -> bottomExpr $ While (travF cond) (travF step) initial

  PrimApp f arg
    | (argBounds, arg') <- boundsOptimizeExp env arg ->
      app zero f arg' argBounds (makeTransitives env argBounds)

  -- TODO: If 'a' is in range of 't2' (based on the bounds in the graph or the size of their types), keep the information of 'a'
  Coerce t1 t2 a -> bottomExpr $ Coerce t1 t2 $ travE a

  where
    travE :: OpenExp env benv s -> OpenExp env benv s
    travE = snd . boundsOptimizeExp env

    travF :: OpenFun env benv f -> OpenFun env benv f
    travF = boundsOptimizeFun env

    bottomExpr :: OpenExp env benv t -> (TermBounds (UniformEnv benv env) t, OpenExp env benv t)
    bottomExpr e = (bottoms zero $ expType e, e)

    caseAlts :: [(TAG, OpenExp env benv b)] -> Maybe (OpenExp env benv b) -> (TermBounds (UniformEnv benv env) b, [(TAG, OpenExp env benv b)], Maybe (OpenExp env benv b))
    caseAlts alts (Just def)
      | (altsBounds, alts', _) <- caseAlts alts Nothing
      , (defBounds, def') <- boundsOptimizeExp env def
      = (unions altsBounds $ makeTransitives env defBounds, alts', Just def')
    caseAlts alts Nothing
      | (altsBoundss, alts') <- unzip $ map (\(t, e) -> let (b, e') = boundsOptimizeExp env e in (b, (t, e'))) alts
      = (foldl1 unions $ map (makeTransitives env) altsBoundss, alts', Nothing)

detectConst :: BoundsEnv benv env -> (TermBounds (UniformEnv benv env) t, OpenExp env benv t) -> (TermBounds (UniformEnv benv env) t, OpenExp env benv t)
detectConst env (bound, expr)
  | TupRsingle b <- bound
  , Just a <- upperConst env b
  , Just a == lowerConst env b
  , TupRsingle tp <- expType expr
  , SingleScalarType (NumSingleType (IntegralNumType t)) <- tp
  , IntegralDict <- integralDict t
  = (bound, Const tp $ fromIntegral a)
  | otherwise
  = (bound, expr)
