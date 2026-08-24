-- A domain-specific language for the fusion ILP's constraints.
module Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage where

import Control.Monad.State (State, evalState)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (Var)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver (Bounds, Constants, LinearConstraint)
import Data.Map (Map)

-- | A property of the fusion problem, to be lowered into linear constraints.
data Constraint op
  = -- | An already-linear constraint, passed through unchanged.
    Linear (LinearConstraint op)

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

-- | Lower a batch of 'Constraint's under one shared name supply.
lowerAll :: LowerEnv op -> [Constraint op] -> (LinearConstraint op, Bounds op)
lowerAll env constraints = evalState (mconcat <$> mapM (lower env) constraints) ""
