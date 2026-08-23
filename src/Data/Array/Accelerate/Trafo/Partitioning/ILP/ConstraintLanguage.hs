-- A domain-specific language for the fusion ILP's constraints.
module Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage where

import Control.Monad.State (State, evalState)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (Var)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver (Bounds, Constants, Constraint)
import Data.Map (Map)

-- | A property of the fusion problem, to be lowered into linear constraints.
data Prop op
  = -- | An already-linear constraint, passed through unchanged.
    Linear (Constraint op)

-- | An environment for lowering, containing the bounds of the variables and the
-- constants for the problem.
data LowerEnv op = LowerEnv
  { lowerEnvBounds :: Map (Var op) (Int, Int),
    lowerEnvConstants :: Constants
  }

-- | The result of lowering. Contains the generated constraints and the bounds of the variables.
--   State monad is used to generate fresh variable names.
type Lower op = State String (Constraint op, Bounds op)

-- | Lower a single 'Prop'.
lower :: LowerEnv op -> Prop op -> Lower op
lower _ prop = case prop of
  Linear c -> pure (c, mempty)

-- | Lower a batch of 'Prop's under one shared name supply.
lowerAll :: LowerEnv op -> [Prop op] -> (Constraint op, Bounds op)
lowerAll env props = evalState (mconcat <$> mapM (lower env) props) ""
