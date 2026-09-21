{-# LANGUAGE MultiWayIf #-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.Presolve (presolve, Problem (..), substitutionConstraints, emptySubstitution) where

import Control.Monad (foldM)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage (Constraint (..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (InplacePath, ReadEdge, WriteEdge, nodeId)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint (LinearConstraint, int, var, (.==.))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var (..))
import Data.Graph.Inductive.Graph qualified as Graph
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.DFS qualified as DFS
import Data.Map qualified as M
import Data.Maybe (mapMaybe)
import Data.Set qualified as S
import Lens.Micro ((^.))

data Value = Const Int | Alias Var deriving (Eq, Show)

type Assignment = (Var, Value)

data Problem = Problem
  { constraints :: [Constraint],
    substitution :: Substitution
  }

data Infeasible = Conflict Var Value Value | Violated Constraint | CyclicClusterOrder [Var]

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
  Manifest b -> drop' [(IsManifest b, Const 0)]
  NewFoldSize co -> drop' [(OutFoldSize co, Const (co ^. nodeId))]
  SameFoldSize co -> drop' [(InFoldSize co, Alias (OutFoldSize co))]
  SameDirection rs ws -> drop' $ aliasAll $ dirVars rs ws
  PinnedDirection co rs ws -> drop' [(v, Const (co ^. nodeId)) | v <- dirVars rs ws]
  SameFoldSizeIfFused w co -> Fused w co .=>. (InFoldSize co, OutFoldSize w)
  FusionDirection w b r -> Fused w r .=>. (WriteDir w b, ReadDir b r)
  InPlaceDirection p@(r, w) -> inPlaceVar p .=>. (uncurry ReadDir r, uncurry WriteDir w)
  AcrossClusterSame p@((_, c1), (c2, _)) -> inPlaceVar p .=>. (Pi c1, Pi c2)
  NotManifestIfAllFused b pairs ->
    let xs = map (uncurry Fused) pairs
        vals = map resolve xs
        open = [x | (x, Alias _) <- zip xs vals]
     in if
          | null pairs -> drop' []
          | Const 1 `elem` vals -> drop' [(IsManifest b, Const 0)]
          | all (== Const 0) vals -> drop' [(IsManifest b, Const 1)]
          | otherwise -> case resolve (IsManifest b) of
              Const 1 -> drop' [(x, Const 0) | x <- open]
              Const 0 | [x] <- open -> drop' [(x, Const 1)]
              Const 0 -> keep
              Const _ -> Left (Violated c)
              Alias _ -> keep
  OnManifestIfInPlace p@((b1, _), (_, b2)) ->
    case (resolve (inPlaceVar p), resolve (IsManifest b1), resolve (IsManifest b2)) of
      (Const 1, _, _) -> drop' []
      (Const 0, _, _) -> drop' [(IsManifest b1, Const 0), (IsManifest b2, Const 0)]
      (_, Const 1, _) -> drop' [(inPlaceVar p, Const 1)]
      (_, _, Const 1) -> drop' [(inPlaceVar p, Const 1)]
      (_, Const 0, Const 0) -> drop' []
      _ -> keep
  AtMostOneReader ps -> atMostOne ps
  AtMostOneWriter ps -> atMostOne ps
  NegativeDirIfManifest (w, b) -> case (resolve (IsManifest b), resolve (WriteDir w b)) of
    (_, Const d) | d < 0 -> drop' []
    (_, Const _) -> Right (Just c, [(IsManifest b, Const 1)])
    _ -> keep
  InPlaceCluster p -> case resolve (inPlaceVar p) of
    Const 1 -> drop' []
    _ -> keep
  _ -> keep
  where
    keep = Right (Just c, [])
    drop' as = Right (Nothing, as)
    resolve v = lookupVar v s
    -- \| @x@ => @a == b@. x beeing 0 means true here exceptionally.
    x .=>. (a, b) = case resolve x of
      Const 1 -> drop' []
      Const 0 -> drop' [(a, Alias b)]
      Const _ -> Left (Violated c)
      Alias _ -> case (resolve a, resolve b) of
        (va, vb) | va == vb -> drop' []
        (Const _, Const _) -> drop' [(x, Const 1)]
        _ -> keep
    -- \| At most one of the paths is used in place.
    atMostOne ps =
      let xs = map inPlaceVar ps
          vals = map resolve xs
          chosen = [x | (x, Const 0) <- zip xs vals]
          open = [x | (x, Alias _) <- zip xs vals]
       in if
            | length ps <= 1 -> drop' []
            | [x] <- chosen -> drop' [(y, Const 1) | y <- xs, y /= x]
            | not (null chosen) -> Left (Violated c)
            | length open <= 1 -> drop' []
            | otherwise -> keep

dirVars :: [ReadEdge] -> [WriteEdge] -> [Var]
dirVars rs ws = map (uncurry ReadDir) rs <> map (uncurry WriteDir) ws

aliasAll :: [Var] -> [Assignment]
aliasAll [] = []
aliasAll (v : vs) = [(w, Alias v) | w <- vs]

inPlaceVar :: InplacePath -> Var
inPlaceVar ((b1, c1), (c2, b2)) = InPlace b1 c1 c2 b2

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
presolve cs = do
  initial <- apply [] (Problem cs emptySubstitution)
  runPasses defaultPasses initial

runPasses :: [Pass] -> Pass
runPasses passes problem = foldM (flip ($)) problem passes

defaultPasses :: [Pass]
defaultPasses = [orderReachability]

type Pass = Problem -> Either Infeasible Problem

type VertexMap = M.Map Var Graph.Node

data OrderGraph = OrderGraph
  { orderGraph :: Gr Var (),
    orderVertices :: VertexMap
  }

strictOrderEdges :: Problem -> [(Var, Var, Constraint)]
strictOrderEdges Problem {constraints = cs, substitution = s} =
  mapMaybe edge cs
  where
    edge c@(ClusterBefore i j) =
      case (lookupVar (Pi i) s, lookupVar (Pi j) s) of
        (Alias from, Alias to) -> Just (from, to, c)
        _ -> Nothing
    edge _ = Nothing

buildOrderGraph :: [(Var, Var, Constraint)] -> OrderGraph
buildOrderGraph edges =
  OrderGraph
    { orderGraph = Graph.mkGraph labeledNodes labeledEdges,
      orderVertices = vertexMap
    }
  where
    variables = S.toList $ S.fromList [v | (from, to, _) <- edges, v <- [from, to]]

    vertexMap = M.fromList $ zip variables [0 ..]

    labeledNodes = [(vertex, variable) | (variable, vertex) <- M.toList vertexMap]

    labeledEdges = [(vertexMap M.! from, vertexMap M.! to, ()) | (from, to, _) <- edges]

canReach :: OrderGraph -> Var -> Var -> Bool
canReach (OrderGraph g vMap) from to =
  case (M.lookup from vMap, M.lookup to vMap) of
    (Just fromVertex, Just toVertex) -> toVertex `elem` DFS.reachable fromVertex g
    _ -> False

orderReachability :: Pass
orderReachability p@Problem {constraints = cs, substitution = s} = do
  checkAcyclic graph
  (remaining, assignments) <- foldM inspect ([], []) cs
  apply assignments $ p {constraints = reverse remaining}
  where
    graph = buildOrderGraph $ strictOrderEdges p

    inspect (remaining, assignments) c@(ClusterBeforeUnlessFused i j) =
      case (lookupVar (Pi i) s, lookupVar (Pi j) s) of
        (Alias from, Alias to)
          -- A strict path from i to j exists, they can't be fused.
          | canReach graph from to -> Right (remaining, (Fused i j, Const 1) : assignments)
          -- The graph proves pi_j < pi_i, which constradicts the constraint (pi_i <= pi_j).
          | canReach graph to from -> Left (Violated c)
        _ -> Right (c : remaining, assignments)
    inspect (remaining, assignments) c = Right (c : remaining, assignments)

checkAcyclic :: OrderGraph -> Either Infeasible ()
checkAcyclic OrderGraph {orderGraph = g} =
  case filter ((> 1) . length) (DFS.scc g) of
    [] -> Right ()
    component : _ -> Left $ CyclicClusterOrder $ mapMaybe (Graph.lab g) component

-- | Convert a substitution to a set of linear constraints.
-- This could be optimized later by actually removing variables from the constraints instead of just adding equality constraints.
substitutionConstraints :: Substitution -> LinearConstraint
substitutionConstraints (Substitution m) = foldMap row $ M.toList m
  where
    row (v, Const c) = var v .==. int c
    row (v, Alias v') = var v .==. var v'
