{-# LANGUAGE KindSignatures #-}

-- A domain-specific language for the fusion ILP's constraints.
module Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage where

import Control.Monad.State (State, evalState)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (Var, fused, pi)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Comp, Node)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver (Bounds, Constants, LinearConstraint, int, (.<.), (.==.), (.>=.))
import Data.Kind (Type)
import Data.Map (Map)
import Prelude hiding (pi)

data Atom (op :: Type -> Type)
  = ClusterBefore (Node Comp) (Node Comp)
  | SameCluster (Node Comp) (Node Comp)

-- | A property of the fusion problem, to be lowered into linear constraints.
data Constraint op
  = Linear (LinearConstraint op)
  | Holds (Atom op)
  | Not (Atom op)

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
  Holds (ClusterBefore i j) -> pure (pi i .<. pi j, mempty)
  Holds (SameCluster i j) -> pure (fused (i, j) .==. int 0, mempty)
  Not (ClusterBefore i j) -> pure (pi i .>=. pi j, mempty)
  Not (SameCluster i j) -> pure (fused (i, j) .==. int 1, mempty)

-- | Lower a batch of 'Constraint's under one shared name supply.
lowerAll :: LowerEnv op -> [Constraint op] -> (LinearConstraint op, Bounds op)
lowerAll env constraints = evalState (mconcat <$> mapM (lower env) constraints) ""
