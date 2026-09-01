{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

-- A domain-specific language for the fusion ILP's constraints.
module Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage where

import Control.Monad (replicateM)
import Control.Monad.State (State, evalState)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (InplacePath, ReadEdge, Var (Other), WriteEdge, fused, inplace, manifest, maxCluster, pi, pimax, readDir, writeDir)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Comp, GVal, Node)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.NameGeneration (freshName)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver (Bounds, Constants (nComps), Expression, LinearConstraint, allB, between, binary, impliesB, int, isEqualRangeN, lowerUpper, notB, packB, timesN, var, (.+.), (.-.), (.<.), (.<=.), (.==.))
import Data.Foldable (fold)
import Data.Kind (Type)
import Prelude hiding (pi)

-- | A property of the fusion problem, to be lowered into linear constraints.
data Constraint (op :: Type -> Type)
  = ClusterBefore (Node Comp) (Node Comp)
  | DifferentCluster (Node Comp) (Node Comp)
  | NotManifestIfAllFused (Node GVal) [(Node Comp, Node Comp)]
  | FusibleOrder (Node Comp) (Node Comp)
  | FusionDirection (Node Comp) (Node GVal) (Node Comp)
  | WithinClusterCount (Node Comp)
  | OnManifestIfInPlace InplacePath
  | InPlaceDirection InplacePath
  | InPlaceCluster InplacePath
  | AcrossClusterSame InplacePath
  | AtMostOneReader (Node GVal) [InplacePath]
  | AtMostOneWriter (Node GVal) [InplacePath]
  | ReadAliveThroughWriters ReadEdge [WriteEdge]
  | HorizontalReadCost (Node Comp) [(Node GVal, Node Comp)]

-- | An environment for lowering, containing the constants for the problem.
data LowerEnv (op :: Type -> Type) where
  LowerEnv :: {lowerEnvConstants :: Constants} -> LowerEnv op

-- | The result of lowering. Contains the generated constraints and the bounds of the variables.
--   State monad is used to generate fresh variable names.
type Lower op = State String (LinearConstraint op, Bounds op, Expression op)

readOrderVar, readPiVar, readPi0Var, useVar :: State String (Var op)
readOrderVar = Other <$> freshName "ReadOrder"
readPiVar = Other <$> freshName "ReadPi"
readPi0Var = Other <$> freshName "Read0Pi"
useVar = Other <$> freshName "ReadUse"

newtype MonadMonoid f m = MonadMonoid {getMonadMonoid :: f m}

instance (Monad f, Semigroup m) => Semigroup (MonadMonoid f m) where
  (MonadMonoid x) <> (MonadMonoid y) = MonadMonoid $ (<>) <$> x <*> y

instance (Monad f, Monoid m) => Monoid (MonadMonoid f m) where
  mempty = MonadMonoid $ pure mempty

foldMapM :: (Foldable t, Monad f, Monoid m) => (a -> f m) -> t a -> f m
foldMapM f = getMonadMonoid . foldMap (MonadMonoid . f)

lowerHorizontalReadCost :: LowerEnv op -> Node Comp -> [(Node GVal, Node Comp)] -> Lower op
lowerHorizontalReadCost env _ consumers = do
  let nConsumers = length consumers
      n = nComps (lowerEnvConstants env)
  readPis <- replicateM nConsumers readPiVar
  readOrders <- replicateM nConsumers readOrderVar
  (subConstraint, subBounds) <- flip foldMapM consumers $ \(buff, cons) -> do
    useVars <- replicateM nConsumers useVar
    let c =
          foldMap
            ( \(uv, rp, ro) ->
                isEqualRangeN (var rp) (pi cons) (var uv)
                  <> isEqualRangeN (var ro) (readDir (buff, cons)) (var uv)
            )
            (zip3 useVars readPis readOrders)
    pure (c <> foldl (.+.) (int 0) (map var useVars) .<=. int (nConsumers - 1), foldMap binary useVars)
  readPi0s <- replicateM nConsumers readPi0Var
  let cost = foldl (.+.) (int 0) (map var readPi0s)
      constraint' = subConstraint <> fold (zipWith (\p p0 -> var p .<=. timesN (var p0)) readPis readPi0s)
      bounds = subBounds <> foldMap (\v -> lowerUpper 0 v n) readPis <> foldMap binary readPi0s
  pure (constraint', bounds, cost)

-- | Lower a single 'Constraint'.
lower :: LowerEnv op -> Constraint op -> Lower op
lower env constraint = case constraint of
  ClusterBefore i j -> pure (pi i .<. pi j, mempty, mempty)
  DifferentCluster i j -> pure (fused (i, j) .==. int 1, mempty, mempty)
  NotManifestIfAllFused b pairs -> pure (allB (map fused pairs) (notB $ manifest b), mempty, mempty)
  FusibleOrder i j -> pure (between (fused (i, j)) (pi j .-. pi i) (timesN $ fused (i, j)), mempty, mempty)
  FusionDirection w b r -> pure (isEqualRangeN (writeDir (w, b)) (readDir (b, r)) (fused (w, r)), mempty, mempty)
  WithinClusterCount l -> pure (pi l .<=. maxCluster, mempty, mempty)
  OnManifestIfInPlace p@((b1, _), (_, b2)) -> pure ((inplace p `impliesB` manifest b1) <> (inplace p `impliesB` manifest b2), mempty, mempty)
  InPlaceDirection p@(r, w) -> pure (isEqualRangeN (readDir r) (writeDir w) (inplace p), mempty, mempty)
  InPlaceCluster p@((b1, _), (c2, _)) -> pure ((pimax b1 .-. pi c2) .<=. timesN (inplace p), mempty, mempty)
  AcrossClusterSame p@((_, c1), (c2, _))
    | c1 == c2 -> pure (mempty, mempty, mempty)
    | otherwise -> pure (isEqualRangeN (pi c1) (pi c2) (inplace p), mempty, mempty)
  AtMostOneReader _ ps -> pure (packB 1 (map inplace ps), mempty, mempty)
  AtMostOneWriter _ ps -> pure (packB 1 (map inplace ps), mempty, mempty)
  ReadAliveThroughWriters r@(b1, c1) ws ->
    pure (pi c1 .+. int 1 .-. foldMap (\w -> int 1 .-. inplace (r, w)) ws .<=. pimax b1, mempty, mempty)
  HorizontalReadCost c pairs -> lowerHorizontalReadCost env c pairs

-- | Lower a batch of 'Constraint's under one shared name supply.
lowerAll :: LowerEnv op -> [Constraint op] -> (LinearConstraint op, Bounds op, Expression op)
lowerAll env constraints = evalState (mconcat <$> mapM (lower env) constraints) ""
