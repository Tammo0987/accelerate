-- A domain-specific language for the fusion ILP's constraints.
module Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage where

import Control.Monad.State (State, evalState)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (InplacePath, ReadEdge, Var, WriteEdge, fused, inplace, manifest, pi, pimax, readDir, writeDir)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Comp, GVal, Node)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver (Bounds, Constants, LinearConstraint, allB, between, impliesB, int, isEqualRangeN, notB, packB, timesN, var, (.+.), (.-.), (.<.), (.<=.), (.==.))
import Data.Map (Map)
import Prelude hiding (pi)

-- | A property of the fusion problem, to be lowered into linear constraints.
data Constraint op
  = Linear (LinearConstraint op)
  | ClusterBefore (Node Comp) (Node Comp)
  | DifferentCluster (Node Comp) (Node Comp)
  | NotManifestIfAllFused (Node GVal) [(Node Comp, Node Comp)]
  | FusibleOrder (Node Comp) (Node Comp)
  | FusionDirection (Node Comp) (Node GVal) (Node Comp)
  | WithinClusterCount (Node Comp) (Var op)
  | OnManifestIfInPlace InplacePath
  | InPlaceDirection InplacePath
  | InPlaceCluster InplacePath
  | AcrossClusterSame InplacePath
  | AtMostOneReader (Node GVal) [InplacePath]
  | AtMostOneWriter (Node GVal) [InplacePath]
  | ReadAliveThroughWriters ReadEdge [WriteEdge]

-- | An environment for lowering, containing the bounds of the variables and the
-- constants for the problem.
data LowerEnv op = LowerEnv
  { lowerEnvBounds :: Map (Var op) (Int, Int),
    lowerEnvConstants :: Constants
  }

-- | The result of lowering. Contains the generated constraints and the bounds of the variables.
--   State monad is used to generate fresh variable names.
type Lower op = State String (LinearConstraint op, Bounds op)

-- | Lower a single 'Constraint'.
lower :: LowerEnv op -> Constraint op -> Lower op
lower _ constraint = case constraint of
  Linear c -> pure (c, mempty)
  ClusterBefore i j -> pure (pi i .<. pi j, mempty)
  DifferentCluster i j -> pure (fused (i, j) .==. int 1, mempty)
  NotManifestIfAllFused b pairs -> pure (allB (map fused pairs) (notB $ manifest b), mempty)
  FusibleOrder i j -> pure (between (fused (i, j)) (pi j .-. pi i) (timesN $ fused (i, j)), mempty)
  FusionDirection w b r -> pure (isEqualRangeN (writeDir (w, b)) (readDir (b, r)) (fused (w, r)), mempty)
  WithinClusterCount l v -> pure (pi l .<=. var v, mempty)
  OnManifestIfInPlace p@((b1, _), (_, b2)) -> pure ((inplace p `impliesB` manifest b1) <> (inplace p `impliesB` manifest b2), mempty)
  InPlaceDirection p@(r, w) -> pure (isEqualRangeN (readDir r) (writeDir w) (inplace p), mempty)
  InPlaceCluster p@((b1, _), (c2, _)) -> pure ((pimax b1 .-. pi c2) .<=. timesN (inplace p), mempty)
  AcrossClusterSame p@((_, c1), (c2, _))
    | c1 == c2 -> pure (mempty, mempty)
    | otherwise -> pure (isEqualRangeN (pi c1) (pi c2) (inplace p), mempty)
  AtMostOneReader _ ps -> pure (packB 1 (map inplace ps), mempty)
  AtMostOneWriter _ ps -> pure (packB 1 (map inplace ps), mempty)
  ReadAliveThroughWriters r@(b1, c1) ws ->
    pure (pi c1 .+. int 1 .-. foldMap (\w -> int 1 .-. inplace (r, w)) ws .<=. pimax b1, mempty)

-- | Lower a batch of 'Constraint's under one shared name supply.
lowerAll :: LowerEnv op -> [Constraint op] -> (LinearConstraint op, Bounds op)
lowerAll env constraints = evalState (mconcat <$> mapM (lower env) constraints) ""
