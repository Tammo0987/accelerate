module Data.Array.Accelerate.Trafo.Partitioning.ILP.Presolve (presolve, Problem (..), substitutionConstraints, emptySubstitution) where

import Control.Monad (foldM)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage (Constraint (..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint (LinearConstraint, int, var, (.==.))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var (..))
import qualified Data.Map as M
import Data.Maybe (mapMaybe)

data Value = Const Int | Alias Var deriving (Eq, Show)

type Assignment = (Var, Value)

data Problem = Problem
  { constraints :: [Constraint],
    substitution :: Substitution
  }

data Infeasible = Conflict Var Value Value | Violated Constraint

newtype Substitution = Substitution (M.Map Var Value) deriving (Show)

emptySubstitution :: Substitution
emptySubstitution = Substitution M.empty

-- | Follow aliases to a constant or the representative variable.
lookupVar :: Var -> Substitution -> Value
lookupVar v s@(Substitution m) = case M.lookup v m of
  Nothing -> Alias v
  Just (Alias v') -> lookupVar v' s
  Just c -> c

-- | Record an assignment to the substitution. Fails if it contradicts an existing assignment.
assign :: Assignment -> Substitution -> Either Infeasible Substitution
assign (v, val) s@(Substitution m) = case (lookupVar v s, resolve val) of
  (Const a, Const b)
    | a == b -> Right s
    | otherwise -> Left (Conflict v (Const a) (Const b))
  (Alias r, Const b) -> Right $ Substitution (M.insert r (Const b) m)
  (Const a, Alias r) -> Right $ Substitution (M.insert r (Const a) m)
  (Alias r1, Alias r2)
    | r1 == r2 -> Right s
    | otherwise -> Right $ Substitution (M.insert (max r1 r2) (Alias (min r1 r2)) m)
  where
    resolve (Const c) = Const c
    resolve (Alias v') = lookupVar v' s

instantiate :: Substitution -> Constraint -> Either Infeasible (Maybe Constraint, [Assignment])
instantiate s c = case c of
  Unfused i j -> drop' [(Fused i j, Const 1)]
  ClusterBefore i j -> case (resolve (Pi i), resolve (Pi j)) of
    (Alias a, Alias b) | a == b -> Left (Violated c)
    (Const a, Const b)
      | a < b -> drop' []
      | otherwise -> Left (Violated c)
    _ -> keep
  ClusterBeforeUnlessFused i j -> case resolve (Fused i j) of
    Const 0 -> drop' [(Pi i, Alias (Pi j))]
    Const 1 -> instantiate s (ClusterBefore i j)
    Const _ -> Left (Violated c)
    Alias _ -> case (resolve (Pi i), resolve (Pi j)) of
      (a, b) | a == b -> drop' [(Fused i j, Const 0)]
      (Const a, Const b)
        | a < b -> drop' [(Fused i j, Const 1)]
        | otherwise -> Left (Violated c)
      _ -> keep
  _ -> keep
  where
    keep = Right (Just c, [])
    drop' as = Right (Nothing, as)
    resolve v = lookupVar v s

-- | Applying constraints and assignments as long as there is progress.
apply :: [Assignment] -> Problem -> Either Infeasible Problem
apply assignments p = assignAll (substitution p) assignments >>= go (constraints p)
  where
    go cs s = do
      results <- traverse (instantiate s) cs
      let cs' = mapMaybe fst results
      s' <- assignAll s (concatMap snd results)
      if size s' == size s
        then Right (Problem cs' s')
        else go cs' s'

assignAll :: Substitution -> [Assignment] -> Either Infeasible Substitution
assignAll = foldM $ flip assign

size :: Substitution -> Int
size (Substitution m) = M.size m

-- | Presolve a set of constraints, returning either an infeasibility or a simplified problem.
presolve :: [Constraint] -> Either Infeasible Problem
presolve cs = apply [] (Problem cs emptySubstitution)

-- | Convert a substitution to a set of linear constraints.
-- This could be optimized later by actually removing variables from the constraints instead of just adding equality constraints.
substitutionConstraints :: Substitution -> LinearConstraint
substitutionConstraints (Substitution m) = foldMap row $ M.toList m
  where
    row (v, Const c) = var v .==. int c
    row (v, Alias v') = var v .==. var v'
