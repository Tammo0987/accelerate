{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE BlockArguments           #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE KindSignatures           #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilyDependencies   #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE ViewPatterns             #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# OPTIONS_GHC -Wno-orphans          #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph where

import Prelude hiding ( init, reads )

-- Accelerate imports
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation hiding (Var)
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Data.Array.Accelerate.Type

-- Data structures
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as S
import qualified Data.Map as M

import Lens.Micro
import Lens.Micro.Mtl

import Control.Monad.State.Strict (State, runState)
import Data.Coerce (coerce)
import Data.Foldable (Foldable (fold, foldr'), traverse_)
import Data.Kind (Type)
import Debug.Trace
import Unsafe.Coerce (unsafeCoerce)



--------------------------------------------------------------------------------
-- Fusion Graph
--------------------------------------------------------------------------------

type ReadEdge      = (Label Buff, Label Comp)
type WriteEdge     = (Label Comp, Label Buff)
type StrictEdge    = (Label Comp, Label Comp)
type DataflowEdge  = (Label Comp, Label Buff, Label Comp)
type FusibleEdge   = DataflowEdge
type InfusibleEdge = DataflowEdge
type InplacePath   = (ReadEdge, WriteEdge)

-- | Program graph.
--
-- The graph consists of read/write edges, strict ordering edges and fusible
-- edges.
--
-- The read/write edges represent a read or write relation between a buffer and
-- a computation. In the ILP, these edges get a variable indicating in which
-- order a computation reads or writes an array in the buffer. Some of these
-- edges are duplicated, so we use a smart constructor to make sure they get the
-- same ILP variable.
--
-- The strict ordering edges enforce a strict ordering between two computations.
-- This ordering can be due to any number of reasons, but in most cases it is to
-- prevent race conditions between two computations.
--
-- The data-flow edges represent a flow of data between two computations over a
-- buffer. These edges are used to determine which computations can be fused.
-- Data-flow edges that are also strict edges are infusible.
-- Data-flow edges that are not strict edges are fusible.
--
-- From the sets of data-flow and strict ordering edges we can derive:
-- 1. The set of write edges. @S.map (\(w,b,_) -> (w,b)) _dataflowEdges@
-- 2. The set of read edges. @S.map (\(_,b,r) -> (w,b)) _dataflowEdges@
-- 3. The set of fusible edges. @S.filter (\(w,_,r) -> S.notMember (w,r) _strictEdges) _dataflowEdges@
-- 4. The set of infusible edges. @S.filter (\(w,_,r) -> S.member (w,r) _strictEdges) _dataflowEdges@
--
-- The latter two computations may be combined as such:
--
-- @
-- (fusible, infusible) = S.partition (\(w,_,r) -> S.notMember (w,r) _strictEdges) _dataflowEdges
-- @
--
data FusionGraph = FusionGraph   -- TODO: Use hashmaps and hashsets in production.
  {      _bufferNodes :: Labels Buff       -- ^ Buffers in the graph.
  , _computationNodes :: Labels Comp       -- ^ Computations in the graph.
  ,        _readEdges :: Set ReadEdge      -- ^ Edges that represent reads.
  ,       _writeEdges :: Set WriteEdge     -- ^ Edges that represent writes.
  ,      _strictEdges :: Set StrictEdge    -- ^ Edges that enforce strict ordering.
  ,    _dataflowEdges :: Set DataflowEdge  -- ^ Edges that represent data-flow.
  ,     _inplacePaths :: Set InplacePath   -- ^ Summary paths between buffers for in-place updates.
  }

instance Semigroup FusionGraph where
  (<>) :: FusionGraph -> FusionGraph -> FusionGraph
  (<>) (FusionGraph b1 c1 r1 w1 s1 d1 i1) (FusionGraph b2 c2 r2 w2 s2 d2 i2)
    = FusionGraph (b1 <> b2) (c1 <> c2) (r1 <> r2) (w1 <> w2) (s1 <> s2) (d1 <> d2) (i1 <> i2)

instance Monoid FusionGraph where
  mempty :: FusionGraph
  mempty = FusionGraph mempty mempty mempty mempty mempty mempty mempty

-- | Class for types that contain a fusion graph.
--
-- This is a manually written version of what microlens-th would generate when
-- using @makeClassy@.
class HasFusionGraph g where
  fusionGraph :: Lens' g FusionGraph

  bufferNodes :: Lens' g (Labels Buff)
  bufferNodes = fusionGraph.bufferNodes

  computationNodes :: Lens' g (Labels Comp)
  computationNodes = fusionGraph.computationNodes

  strictEdges :: Lens' g (Set StrictEdge)
  strictEdges = fusionGraph.strictEdges

  dataflowEdges :: Lens' g (Set DataflowEdge)
  dataflowEdges = fusionGraph.dataflowEdges

  readEdges :: Lens' g (Set ReadEdge)
  readEdges = fusionGraph.readEdges

  writeEdges :: Lens' g (Set WriteEdge)
  writeEdges = fusionGraph.writeEdges

  inplacePaths :: Lens' g (Set InplacePath)
  inplacePaths = fusionGraph.inplacePaths

-- | Base instance of 'HasFusionGraph' for 'FusionGraph'.
--
-- This instance cannot make use of lenses defined in 'HasFusionGraph' because
-- it is the base instance and would otherwise cause a loop.
instance HasFusionGraph FusionGraph where
  fusionGraph :: Lens' FusionGraph FusionGraph
  fusionGraph = id

  bufferNodes :: Lens' FusionGraph (Set (Label Buff))
  bufferNodes f s = f (_bufferNodes s) <&> \bs -> s{_bufferNodes = bs}

  computationNodes :: Lens' FusionGraph (Set (Label Comp))
  computationNodes f s = f (_computationNodes s) <&> \cs -> s{_computationNodes = cs}

  strictEdges :: Lens' FusionGraph (Set StrictEdge)
  strictEdges f s = f (_strictEdges s) <&> \es -> s{_strictEdges = es}

  dataflowEdges :: Lens' FusionGraph (Set DataflowEdge)
  dataflowEdges f s = f (_dataflowEdges s) <&> \es -> s{_dataflowEdges = es}

  readEdges :: Lens' FusionGraph (Set ReadEdge)
  readEdges f s = f (_readEdges s) <&> \es -> s{_readEdges = es}

  writeEdges :: Lens' FusionGraph (Set WriteEdge)
  writeEdges f s = f (_writeEdges s) <&> \es -> s{_writeEdges = es}

  inplacePaths :: Lens' FusionGraph (Set InplacePath)
  inplacePaths f s = f (_inplacePaths s) <&> \ps -> s{_inplacePaths = ps}

-- | Insert a buffer node into the graph.
insertBuffer :: HasFusionGraph g => Label Buff -> g -> g
insertBuffer b = bufferNodes %~ S.insert b

-- | Insert a write edge from a computation to a buffer.
insertComputation :: HasFusionGraph g => Label Comp -> g -> g
insertComputation c = computationNodes %~ S.insert c

-- | Insert a read edge from a buffer to a computation.
insertRead :: HasFusionGraph g => ReadEdge -> g -> g
insertRead (b, c) = readEdges %~ S.insert (b, c)

-- | Insert a write edge from a computation to a buffer.
insertWrite :: HasFusionGraph g => WriteEdge -> g -> g
insertWrite (c, b) = writeEdges %~ S.insert (c, b)

-- | Insert a strict relation between two computations.
insertStrict :: (HasCallStack, HasFusionGraph g) => StrictEdge -> g -> g
insertStrict (c1, c2) g
  | c1 == c2                           = internalError "insertStrict: Reflexive edge"
  | c1^.parent /= c2^.parent           = internalError "insertStrict: Different scopes"
  | S.member (c2, c1) (g^.strictEdges) = internalError "insertStrict: Cyclic edge"
  | otherwise = g & strictEdges %~ S.insert (c1, c2)

-- | Insert a fusible data-flow edge between two computations.
insertFusible :: (HasCallStack, HasFusionGraph g) => DataflowEdge -> g -> g
insertFusible (c1, b, c2) g
  | c1 == c2                            = internalError "insertFusible: Reflexive edge"
  | c1^.parent /= c2^.parent            = internalError "insertFusible: Different scopes"
  | S.member (c2, c1) (g^.strictEdges)  = internalError "insertFusible: Cyclic edge"
  | S.notMember (c1, b) (g^.writeEdges) = internalError "insertFusible: Missing write"
  | S.notMember (b, c2) (g^.readEdges)  = internalError "insertFusible: Missing read"
  | otherwise = g & dataflowEdges %~ S.insert (c1, b, c2)

-- | Insert an infusible data-flow edge between two computations.
insertInfusible :: (HasCallStack, HasFusionGraph g) => DataflowEdge -> g -> g
insertInfusible (c1, b, c2) g
  | c1 == c2                            = internalError "insertInfusible: Reflexive edge"
  | S.member (c2, c1) (g^.strictEdges)  = internalError "insertInfusible: Cyclic edge"
  | S.notMember (c1, b) (g^.writeEdges) = internalError "insertInfusible: Missing write"
  | S.notMember (b, c2) (g^.readEdges)  = internalError "insertInfusible: Missing read"
  | otherwise = g & dataflowEdges %~ S.insert (c1, b, c2)
                  & strictEdges   %~ S.insert (c1,    c2)

-- | Gets the set of fusible edges.
fusibleEdges :: HasFusionGraph g => SimpleGetter g (Set FusibleEdge)
fusibleEdges = to (\g -> S.filter (\(w, _, r) -> S.notMember (w, r) (g^.strictEdges)) (g^.dataflowEdges))

-- | Gets the set of infusible edges.
infusibleEdges :: HasFusionGraph g => SimpleGetter g (Set InfusibleEdge)
infusibleEdges = to (\g -> S.filter (\(w, _, r) -> S.member (w, r) (g^.strictEdges)) (g^.dataflowEdges))

-- | Gets the set of fusible and infusible edges.
fusionEdges :: HasFusionGraph g => SimpleGetter g (Set FusibleEdge, Set InfusibleEdge)
fusionEdges = to (\g -> S.partition (\(w, _, r) -> S.notMember (w, r) (g^.strictEdges)) (g^.dataflowEdges))

-- | Gets the set of strict edges that are not data-flow edges.
orderEdges :: HasFusionGraph g => SimpleGetter g (Set StrictEdge)
orderEdges = to (\g -> let dataflowEdges' = S.map (\(w,_,r) -> (w,r)) (g^.dataflowEdges)
                        in S.filter (\(w, r) -> S.notMember (w, r) dataflowEdges') (g^.strictEdges))

-- | Gets the input edges of a computations.
inputEdgesOf :: HasFusionGraph g => Label Comp -> SimpleGetter g (Set ReadEdge)
inputEdgesOf c = to (\g -> S.filter (\(_, r) -> r == c) (g^.readEdges))

-- | Gets the output edges of a computations.
outputEdgesOf :: HasFusionGraph g => Label Comp -> SimpleGetter g (Set WriteEdge)
outputEdgesOf c = to (\g -> S.filter (\(w, _) -> w == c) (g^.writeEdges))

-- | Gets the read edges of a buffer.
readEdgesOf :: HasFusionGraph g => Label Buff -> SimpleGetter g (Set ReadEdge)
readEdgesOf b = to (\g -> S.filter (\(b', _) -> b' == b) (g^.readEdges))

-- | Gets the write edges of a buffer.
writeEdgesOf :: HasFusionGraph g => Label Buff -> SimpleGetter g (Set WriteEdge)
writeEdgesOf b = to (\g -> S.filter (\(_, b') -> b' == b) (g^.writeEdges))



--------------------------------------------------------------------------------
-- The Fusion ILP.
--------------------------------------------------------------------------------

-- | A single block of the ILP.
--
-- 'FusionILP' stores an fusion ILP for a single block of code. This is
-- possible because there can be no fusion between different blocks of code.
-- Separating the ILP into blocks then allows us to pass much smaller ILPs to
-- the solver, which should make the whole process faster.
-- If not, we can always merge the blocks together later.
data FusionILP op = FusionILP
  { _graph       :: FusionGraph
  , _constraints :: Constraint op
  , _bounds      :: Bounds op
  }

instance Semigroup (FusionILP op) where
  (<>) :: FusionILP op -> FusionILP op -> FusionILP op
  (<>) (FusionILP g1 c1 b1) (FusionILP g2 c2 b2) =
    FusionILP (g1 <> g2) (c1 <> c2) (b1 <> b2)

instance Monoid (FusionILP op) where
  mempty :: FusionILP op
  mempty = FusionILP mempty mempty mempty

-- | Class for accessing the fusion ILP field of a data structure.
--
-- We make this because there are at least two data structures that contain a
-- fusion ILP: 'FusionGraphState' and the result of graph construction. This is
-- similar to what microlens-th would generate when using @makeFields@.
class HasFusionILP s op | s -> op where
  fusionILP :: Lens' s (FusionILP op)

graph :: Lens' (FusionILP op) FusionGraph
graph f s = f (_graph s) <&> \g -> s{_graph = g}

constraints :: Lens' (FusionILP op) (Constraint op)
constraints f s = f (_constraints s) <&> \c -> s{_constraints = c}

bounds :: Lens' (FusionILP op) (Bounds op)
bounds f s = f (_bounds s) <&> \b -> s{_bounds = b}

instance HasFusionGraph (FusionILP op) where
  fusionGraph :: Lens' (FusionILP op) FusionGraph
  fusionGraph = graph

-- | Safely insert a read edge into the graph.
--
-- We don't add edges between higher scoped computations because we would lose
-- some required information on those edges.
reads :: Label Comp -> Label Buff -> FusionILP op -> FusionILP op
reads c b = fusionGraph %~ insertRead (b, c)

-- | Safely insert a write edge into the graph.
--
-- We don't add edges between higher scoped computations because we would lose
-- some required information on those edges.
writes :: Label Comp -> Label Buff -> FusionILP op -> FusionILP op
writes c b = fusionGraph %~ insertWrite (c, b)

-- | Safely insert read edges between multiple computations and a buffer.
read :: Labels Comp -> Label Buff -> FusionILP op -> FusionILP op
read cs b = flip (foldr' (`reads` b)) cs

-- | Safely insert write edges between multiple computations and a buffer.
write :: Labels Comp -> Label Buff -> FusionILP op -> FusionILP op
write cs b = flip (foldr' (`writes` b)) cs

-- | Safely add a strict relation between two computations.
--
-- Strict edges can only occur between computations in the same scope, so we
-- traverse the scopes of the computations until we find two computations within
-- the same scope. If the computations we find are the same, we do nothing
-- because reflexive edges are not allowed but our algorithm may try to create
-- them in certain scenarios (e.g. when returning out of a body).
before :: HasCallStack => Label Comp -> Label Comp -> FusionILP op -> FusionILP op
before c1 c2
  | c1         == c2         = id
  | c1^.parent == c2^.parent = fusionGraph %~ insertStrict (c1, c2)
  | otherwise                = case compare (level c1) (level c2) of
      LT -> before  c1           (c2^.parent')
      GT -> before (c1^.parent')  c2
      EQ -> before (c1^.parent') (c2^.parent')

-- | Safely add a fusible edge between two computations.
--
-- If the computations share the same parent, add a fusible edge, otherwise add
-- an infusible edge.
fusible :: HasCallStack => Label Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
fusible prod buff cons = if prod^.parent == cons^.parent
  then fusionGraph %~ insertFusible (prod, buff, cons)
  else infusible prod buff cons

-- | Safely add an infusible edge between two computations.
--
-- We add an infusible edge between the producer and consumer. We also add a
-- strict edge between them using the rules described in 'before'.
infusible :: HasCallStack => Label Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
infusible prod buff cons = before prod cons . (fusionGraph %~ insertInfusible (prod, buff, cons))

-- | Safely add strict ordering between multiple computations and another computation.
allBefore :: HasCallStack => Labels Comp -> Label Comp -> FusionILP op -> FusionILP op
allBefore cs1 c2 ilp = foldr' (`before` c2) ilp cs1

-- | Safely add fusible edges from all producers to the consumer.
allFusible :: HasCallStack => Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
allFusible prods buff cons ilp = foldr' (\prod -> fusible prod buff cons) ilp prods

-- | Safely add infusible edges from all producers to the consumer.
allInfusible :: HasCallStack => Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
allInfusible prods buff cons ilp = foldr' (\prod -> infusible prod buff cons) ilp prods

-- | Infix synonym for 'before'.
(==|-|=>) :: HasCallStack => Label Comp -> Label Comp -> FusionILP op -> FusionILP op
(==|-|=>) = before

-- | Infix synonym for 'fusible'.
(--|) :: HasCallStack => Label Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
(--|) = fusible

-- | Infix synonym for 'infusible'.
(==|) :: HasCallStack => Label Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
(==|) = infusible

-- | Infix synonym for 'allBefore'.
(>=|-|=>) :: HasCallStack => Labels Comp -> Label Comp -> FusionILP op -> FusionILP op
(>=|-|=>) = allBefore

-- | Infix synonym for 'allFusible'.
(>-|) :: HasCallStack => Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
(>-|) = allFusible

-- | Infix synonym for 'allInfusible'.
(>=|) :: HasCallStack => Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
(>=|) = allInfusible

-- | Arrow heads to complete '(--|)', '(>-|)', '(==|)' and '(>=|)'.
(|->), (|=>) :: (a -> b) -> a -> b
(|->) = ($)
(|=>) = ($)

--------------------------------------------------------------------------------
-- Backend specific definitions
--------------------------------------------------------------------------------

-- | The backend has access to a small state so it doesn't accidentally break
--   the state used by the frontend construction algorithm.
data BackendGraphState op env = BackendGraphState
  { _backendFusionILP  :: FusionILP op    -- ^ The entire ILP.
  , _backendBuffersEnv :: BuffersEnv env  -- ^ The buffers environment (read only).
  , _backendReadersEnv :: ReadersEnv      -- ^ The readers environment (read only).
  , _backendWritersEnv :: WritersEnv      -- ^ The writers environment (read only).
  }

instance HasFusionILP (BackendGraphState op env) op where
  fusionILP :: Lens' (BackendGraphState op env) (FusionILP op)
  fusionILP f s = f (_backendFusionILP s) <&> \ilp -> s{_backendFusionILP = ilp}

instance HasBuffersEnv (BackendGraphState op env) (BackendGraphState op env') env env' where
  buffersEnv :: Lens (BackendGraphState op env) (BackendGraphState op env') (BuffersEnv env) (BuffersEnv env')
  buffersEnv f s = f (_backendBuffersEnv s) <&> \env -> s{_backendBuffersEnv = env}

instance HasReadersEnv (BackendGraphState op env) where
  readersEnv :: Lens' (BackendGraphState op env) ReadersEnv
  readersEnv f s = f (_backendReadersEnv s) <&> \env -> s{_backendReadersEnv = env}

instance HasWritersEnv (BackendGraphState op env) where
  writersEnv :: Lens' (BackendGraphState op env) WritersEnv
  writersEnv f s = f (_backendWritersEnv s) <&> \env -> s{_backendWritersEnv = env}

type BackendCluster op = PreArgs (BackendClusterArg op)

class ( ShrinkArg (BackendClusterArg op), Eq (BackendVar op)
      , Ord (BackendVar op), Eq (BackendArg op), Show (BackendArg op)
      , Ord (BackendArg op), Show (BackendVar op)
      ) => MakesILP op where

  -- | ILP variables for backend-specific fusion rules.
  type BackendVar op

  -- | Information that the backend attaches to arguments for use in
  --   interpreting/code generation.
  type BackendArg op
  defaultBA :: BackendArg op

  -- | Information that the backend attaches to the cluster for use in
  --   interpreting/code generation.
  data BackendClusterArg op arg
  combineBackendClusterArg
    :: BackendClusterArg op (Out sh e)
    -> BackendClusterArg op (In sh e)
    -> BackendClusterArg op (Var' sh)
  encodeBackendClusterArg  :: BackendClusterArg op arg -> Builder


  -- | Given an ILP solution, attach the backend-specific information to an
  --   argument.
  labelLabelledArg :: Solution op -> Label Comp -> LabelledArg env a -> LabelledArgOp op env a

  -- | Convert a labelled argument to a cluster argument.
  getClusterArg :: LabelledArgOp op env a -> BackendClusterArg op a

  -- | This function defines per-operation backend-specific fusion rules.
  --
  -- When this function gets called, the majority of edges have already been
  -- added to the graph. That is, we have already added read-, write-, fusible-
  -- and infusible-edges such that no race conditions exist.
  -- The backend is responsible for adding (or removing) edges to (or from) the
  -- graph to enforce any additional constraints the implementation may have.
  --
  mkGraph
    :: Label Comp             -- ^ The label of the operation.
    -> op args                -- ^ The operation.
    -> LabelledArgs env args  -- ^ The arguments to the operation.
    -> State (BackendGraphState op env) ()

  -- | This function lets the backend define additional constraints on the ILP.
  finalize :: FusionGraph -> Constraint op

labelLabelledArgs :: MakesILP op => Solution op -> Label Comp -> LabelledArgs env args -> LabelledArgsOp op env args
labelLabelledArgs sol l (arg :>: args) = labelLabelledArg sol l arg :>: labelLabelledArgs sol l args
labelLabelledArgs _ _ ArgsNil = ArgsNil

--------------------------------------------------------------------------------
-- ILP Variables
--------------------------------------------------------------------------------

data instance Var (op :: Type -> Type)
  -- Variables used by fusion:
  = Pi (Label Comp)
    -- ^ Used for acyclic ordering of clusters.
    -- Pi (Label x y) = z means that computation number x (possibly a subcomputation of y, see Label) is fused into cluster z (y ~ Just i -> z is a subcluster of the cluster of i)
  | Fused (Label Comp) (Label Comp)
    -- ^ 0 is fused (same cluster), 1 is unfused. We do *not* have one of these for all pairs, only the ones we need for constraints and/or costs!
    -- Invariant: Like edges, both labels have to have the same parent: Either on top (Label _ Nothing) or as sub-computation of the same label (Label _ (Just x)).
    -- In fact, this is the Var-equivalent to Edge: an infusible edge has a constraint (== 1).
  | Manifest (Label Buff)
    -- ^ 0 means manifest, 1 is like a `delayed array`.
    -- Binary variable; will we write the output to a manifest array, or is it fused away (i.e. all uses are in its cluster)?
  | ReadDir (Label Buff) (Label Comp)
    -- ^ \-3 can't fuse with anything, -2 for 'left to right', -1 for 'right to left', n for 'unknown', see computation n (currently only backpermute).
  | WriteDir (Label Comp) (Label Buff)
    -- ^ See 'ReadDir'.
  | InDir (Label Comp)  -- Legacy
    -- ^ For backwards compatibility, see 'ReadDir''. For this variable to have any meaning the backend has to call 'useInDir' (or 'useInOutDir').
  | OutDir (Label Comp)  -- Legacy
    -- ^ For backwards compatibility, see 'WriteDir''. For this variable to have any meaning the backend has to call 'useOutDir' (or 'useInOutDir').
  | InFoldSize (Label Comp)  -- Legacy? Probably needs per-edge equivalent
    -- ^ Keeps track of the fold that's one dimension larger than this operation, and is fused in the same cluster.
    -- This prevents something like @zipWith f (fold g xs) (fold g ys)@ from illegally fusing
  | OutFoldSize (Label Comp)  -- Legacy? Probably needs per-edge equivalent
    -- ^ Keeps track of the fold that's one dimension larger than this operation, and is fused in the same cluster.
    -- This prevents something like @zipWith f (fold g xs) (fold g ys)@ from illegally fusing
  | Other String
    -- ^ For one-shot variables that don't deserve a constructor. These are also integer variables, and the responsibility is on the user to pick a unique name!
    -- It is possible to add a variation for continuous variables too, see `allIntegers` in MIP.hs.
    -- We currently use this in Solve.hs for cost functions.
  | BackendSpecific (BackendVar op)
    -- ^ Vars needed to express backend-specific fusion rules.
    -- This is what allows backends to specify how each of the operations can fuse.

  -- Variables introduced for in-place updates:
  | InPlace (Label Buff) (Label Comp) (Label Buff)
    -- ^ 0 means in-place, 1 means not in-place. The first label is an input of a cluster, the second label is an output of a cluster.
    -- All 'InPlace' variables need to be unique, so we can't omit the first computation (the reader of the input buffer), but we can safely omit the second (writer of the output) because there should in theory only be one writer per buffer in the cases we care about.
    -- If the above assumption is not correct, you'll find that the ILP solver will throw an error @must have >=1 lines@, which is caused by an invalid ILP (in this case because we get duplicate variables in a single constraint).
  | PiMax (Label Buff)
    -- ^ The cluster number of the largest reader of the buffer, since in-place updates are only allowed on the final consumer of an array/buffer.
  -- | WriteDirPiMax (Label Buff)
  --   -- ^ The write direction of the largest reader of the buffer. This is used to check that all reads of the buffer are in the same direction as the write.

deriving instance Eq   (BackendVar op) => Eq   (Var op)
deriving instance Ord  (BackendVar op) => Ord  (Var op)
deriving instance Show (BackendVar op) => Show (Var op)

-- | Sets all 'ReadDir' that contain the computation @c@ to be equal to the
--   'InDir' variable of @c@. If you don't use this fuction, using 'InDir' will
--   have no effect.
--
-- This function makes it so we can write ILP's in the old style, i.e. where
-- a computation reads/writes in only one direction.
useInDir :: HasFusionILP g op => Label Comp -> State g ()
useInDir c = do
  readDirs <- map (var . uncurry ReadDir) . S.toList <$> use (fusionILP.inputEdgesOf c)
  fusionILP.constraints %= (<> equals (var (InDir c) : readDirs))

-- | Sets all 'WriteDir' that contain the computation @c@ to be equal to the
--   'OutDir' variable of @c@. If you don't use this fuction, using 'OutDir'
--   will have no effect.
--
-- This function makes it so we can write ILP's in the old style, i.e. where
-- a computation reads/writes in only one direction.
useOutDir :: HasFusionILP g op => Label Comp -> State g ()
useOutDir c = do
  writeDirs <- map (var . uncurry WriteDir) . S.toList <$> use (fusionILP.outputEdgesOf c)
  fusionILP.constraints %= (<> equals (var (OutDir c) : writeDirs))

-- | See 'useInDir' and 'useOutDir'.
useInOutDir :: HasFusionILP g op => Label Comp -> State g ()
useInOutDir c = useInDir c >> useOutDir c


-- | Constructor for 'Pi' variables.
pi :: Label Comp -> Expression op
pi = var . Pi

-- | No clue what this is for.
delayed :: Label Buff -> Expression op
delayed = notB . manifest

-- | Constructor for 'Manifest' variables.
manifest :: Label Buff -> Expression op
manifest = var . Manifest

-- | Safe constructor for 'Fused' variables.
fused :: DataflowEdge -> Expression op
fused (w, _, r)= var $ Fused w r

-- | Safe constructor for 'ReadDir' variables.
readDir :: ReadEdge -> Expression op
readDir = var . uncurry ReadDir

-- | Safe constructor for 'WriteDir' variables.
writeDir :: WriteEdge -> Expression op
writeDir = var . uncurry WriteDir

-- | Safe constructor for 'InPlace' variables.
inplace :: InplacePath -> Expression op
inplace ((b1,c1),(_,b2)) = var $ InPlace b1 c1 b2

-- | Safe constructor for 'PiMax' variables.
pimax :: Label Buff -> Expression op
pimax = var . PiMax



--------------------------------------------------------------------------------
-- Symbol table
--------------------------------------------------------------------------------

data Symbol (op :: Type -> Type) where
  SExe  :: BuffersEnv env -> LabelledArgs      env args -> op args                              -> Symbol op
  SExe' :: BuffersEnv env -> LabelledArgsOp op env args -> op args                              -> Symbol op
  SUse  ::                   ScalarType e -> Int -> Buffer e                                    -> Symbol op
  SITE  :: BuffersEnv env -> ExpVar env PrimBool -> Label Comp -> Label Comp                    -> Symbol op
  SWhl  :: BuffersEnv env -> Label Comp -> Label Comp -> GroundVars env bnd -> Uniquenesses bnd -> Symbol op
  SLet  ::                   BoundGLHS bnd env env' -> Label Comp           -> Uniquenesses bnd -> Symbol op
  SFun  ::                   BoundGLHS bnd env env' -> Label Comp                               -> Symbol op
  SBod  ::                   BuffersTup a                                                       -> Symbol op
  SBlk  ::                                                                                         Symbol op
  SRet  :: BuffersEnv env -> GroundVars env a                                                   -> Symbol op
  SCmp  :: BuffersEnv env -> Exp env a                                                          -> Symbol op
  SAlc  :: BuffersEnv env -> ShapeR sh -> ScalarType e -> ExpVars env sh                        -> Symbol op
  SUnt  :: BuffersEnv env -> ExpVar env e                                                       -> Symbol op

instance Show (Symbol op) where
  show :: Symbol op -> String
  show (SExe {}) = "Exe"
  show (SExe'{}) = "Exe'"
  show (SUse {}) = "Use"
  show (SITE {}) = "ITE"
  show (SWhl {}) = "Whl"
  show (SLet {}) = "Let"
  show (SFun {}) = "Fun"
  show (SBod {}) = "Bod"
  show (SBlk {}) = "Blk"
  show (SRet {}) = "Ret"
  show (SCmp {}) = "Cmp"
  show (SAlc {}) = "Alc"
  show (SUnt {}) = "Unt"

-- | Mapping from labels to symbols.
type Symbols op = Map (Label Comp) (Symbol op)

data LabelledArgOp  op env a = LOp (Arg env a) (ArgLabel a) (BackendArg op)
type LabelledArgsOp op env   = PreArgs (LabelledArgOp op env)

instance Show (LabelledArgOp op env a) where
  show :: LabelledArgOp op env a -> String
  show (LOp _ bs _) = show bs

unlabelop :: LabelledArgsOp op env a -> Args env a
unlabelop ArgsNil = ArgsNil
unlabelop ((LOp arg _ _) :>: args) = arg :>: unlabelop args

reindexLabelledArgOp :: Applicative f => ReindexPartial f env env' -> LabelledArgOp op env t -> f (LabelledArgOp op env' t)
reindexLabelledArgOp k (LOp (ArgVar vars               ) l o) = (\x -> LOp x l o)  .   ArgVar          <$> reindexVars k vars
reindexLabelledArgOp k (LOp (ArgExp e                  ) l o) = (\x -> LOp x l o)  .   ArgExp          <$> reindexExp k e
reindexLabelledArgOp k (LOp (ArgFun f                  ) l o) = (\x -> LOp x l o)  .   ArgFun          <$> reindexExp k f
reindexLabelledArgOp k (LOp (ArgArray m repr sh buffers) l o) = (\x -> LOp x l o) <$> (ArgArray m repr <$> reindexVars k sh <*> reindexVars k buffers)

reindexLabelledArgsOp :: Applicative f => ReindexPartial f env env' -> LabelledArgsOp op env t -> f (LabelledArgsOp op env' t)
reindexLabelledArgsOp = reindexPreArgs reindexLabelledArgOp

attachBackendLabels :: MakesILP op => Solution op -> Symbols op -> Symbols op
attachBackendLabels sol = M.mapWithKey \cases
  l (SExe lenv largs op) -> SExe' lenv (labelLabelledArgs sol l largs) op
  _  SExe'{} -> internalError "already converted???"
  _  con -> con



--------------------------------------------------------------------------------
-- FusionGraph construction
--------------------------------------------------------------------------------

-- | State for the full graph construction.
--
-- The graph is constructed inside the state monad by inserting edges into it.
-- The state also contains the symbols needed for reconstruction of the AST and
-- the current computation label.
--
-- Computations labels and buffer labels should always be unique, so we only use
-- one counter for the computation labels and provide lenses for interpreting
-- them as buffer labels.
-- Since all labels are unique, we can use a single symbol map for all labels
-- instead of separate maps for computation and buffer labels.
--
-- The result of the full graph construction is reserved for the return values
-- of nodes in the program, which are generally buffer labels.
-- This method makes defining the control flow easier since we do not need to
-- worry about merging the graphs in the return values as in the old approach.
--
-- The environment is not passed as an argument to 'mkFusionGraph' since it may
-- be modified by certain computations. Specifically, when a buffer is marked as
-- mutable, a copy of the buffer is created and the original buffer is replaced
-- by the copy in the environment.
--
-- We keep track of which computation last wrote to a buffer, i.e. the producer
-- of the buffer. Under normal circumstances a buffer has one and only one
-- producer, but when we enter an if-then-else it could be that some buffer
-- is written to by both branches. In this case the buffer is mutated by both,
-- which is safe because during execution only one branch is taken.
--
-- The environment and return values contain sets of buffer for a similar
-- reason. An if-then-else could return different buffers of the same type
-- depending on which branch is taken.
--
data FusionGraphState op env = FusionGraphState
  { _fusionILP  :: FusionILP op    -- ^ The ILP information.
  , _buffersEnv :: BuffersEnv env  -- ^ The label environment.
  , _readersEnv :: ReadersEnv      -- ^ Mapping from buffers to consumers.
  , _writersEnv :: WritersEnv      -- ^ Mapping from buffers to producers.
  , _symbols    :: Symbols op      -- ^ The symbols for the ILP.
  , _currComp   :: Label Comp      -- ^ The current computation label.
  , _currEnvL   :: EnvLabel        -- ^ The current environment label.
  }

type ReadersEnv = Map (Label Buff) (Labels Comp)
type WritersEnv = Map (Label Buff) (Labels Comp)

initialFusionGraphState :: FusionGraphState op ()
initialFusionGraphState = FusionGraphState mempty EnvNil mempty mempty mempty (Label 0 Nothing) 0

instance Show (FusionGraphState op env) where
  show :: FusionGraphState op env -> String
  show s = "FusionGraphState { readersEnv=" ++ show (s^.readersEnv) ++
            ", writersEnv=" ++ show (s^.writersEnv) ++
            " }"

instance HasFusionILP (FusionGraphState op env) op where
  fusionILP :: Lens' (FusionGraphState op env) (FusionILP op)
  fusionILP f s = f (_fusionILP s) <&> \ilp -> s{_fusionILP = ilp}

class HasBuffersEnv s t env env' | s -> env, t -> env' where
  buffersEnv :: Lens s t (BuffersEnv env) (BuffersEnv env')

instance HasBuffersEnv (FusionGraphState op env) (FusionGraphState op env') env env' where
  buffersEnv :: Lens (FusionGraphState op env) (FusionGraphState op env') (BuffersEnv env) (BuffersEnv env')
  buffersEnv f s = f (_buffersEnv s) <&> \env -> s{_buffersEnv = env}

class HasReadersEnv s where
  readersEnv :: Lens' s ReadersEnv

instance HasReadersEnv (FusionGraphState op env) where
  readersEnv :: Lens' (FusionGraphState op env) ReadersEnv
  readersEnv f s = f (_readersEnv s) <&> \env -> s{_readersEnv = env}

class HasWritersEnv s where
  writersEnv :: Lens' s WritersEnv

instance HasWritersEnv (FusionGraphState op env) where
  writersEnv :: Lens' (FusionGraphState op env) WritersEnv
  writersEnv f s = f (_writersEnv s) <&> \env -> s{_writersEnv = env}

class HasSymbols s op | s -> op where
  symbols :: Lens' s (Symbols op)

instance HasSymbols (FusionGraphState op env) op where
  symbols :: Lens' (FusionGraphState op env) (Symbols op)
  symbols f s = f (_symbols s) <&> \sym -> s{_symbols = sym}

currComp :: Lens' (FusionGraphState op env) (Label Comp)
currComp f s = f (_currComp s) <&> \c -> s{_currComp = c}

currEnvL :: Lens' (FusionGraphState op env) EnvLabel
currEnvL f s = f (_currEnvL s) <&> \l -> s{_currEnvL = l}

-- | Lens for creating the backend graph state.
--
-- This lens sets new values for the readers and writers environments because
-- the backend needs to work with the environment from before the computation
-- was added. We don't need to do the same for the buffers environment, because
-- it only changes when a new variable is introduced.
--
-- The fusion ILP is the only value that the backend may modify, so its the only
-- value that is retrieved from the backend graph state afterwards.
backendGraphState :: ReadersEnv -> WritersEnv -> Lens' (FusionGraphState op env) (BackendGraphState op env)
backendGraphState renv wenv f s = f (BackendGraphState (s^.fusionILP) (s^.buffersEnv) renv wenv)
  <&> \b -> s & fusionILP .~ b^.fusionILP

-- | Lens for getting and setting the writers of a buffer.
--
-- The default value for the producer of a buffer is the buffer itself casted to
-- a computation label. This actually has some meaning, in that a buffer which
-- has yet to be written to is "produced" by its allocator (which has the same
-- label).
writers :: HasWritersEnv s => Label Buff -> Lens' s (Labels Comp)
writers b f s = f (M.findWithDefault (S.singleton (coerce b)) b (s^.writersEnv)) <&> \cs -> s & writersEnv %~ M.insert b cs

-- | Lens for getting all writers of buffers.
allWriters :: (Foldable f, HasWritersEnv s) => f (Label Buff) -> SimpleGetter s (Labels Comp)
allWriters bs = to (\s -> foldMap (\b -> s^.writers b) bs)
-- allWriters bs = to (\s -> traverse (\b -> s^.writers b) bs)

-- | Lens for getting and setting the readers of a buffer.
--
-- By default a buffer isn't read by any computations.
readers :: HasReadersEnv s => Label Buff -> Lens' s (Labels Comp)
readers b f s = f (M.findWithDefault mempty b (s^.readersEnv)) <&> \cs -> s & readersEnv %~ M.insert b cs

-- | Lens for getting all readers of buffers.
allReaders :: (Foldable f, HasReadersEnv s) => f (Label Buff) -> SimpleGetter s (Labels Comp)
allReaders bs = to (\s -> foldMap (\b -> s^.readers b) bs)

-- | Lens for getting and setting symbol of a computation.
symbol :: HasSymbols s op => Label Comp -> Lens' s (Maybe (Symbol op))
symbol c = symbols.(`M.alterF` c)

-- | Lens for getting and setting the allocator of a buffer. 'symbol' but for
--   buffers.
allocator :: HasSymbols s op => Label Buff -> Lens' s (Maybe (Symbol op))
allocator = symbol . coerce

-- | Lens for working under the scope of a computation.
--
-- It first sets the parent of the current label to the supplied computation
-- label. Then it applies the function to the 'FusionGraphState' with the now
-- parented label. Finally, it sets the parent of the current label back to the
-- original parent.
scope :: Label Comp -> Lens' (FusionGraphState op env) (FusionGraphState op env)
scope c = with (currComp.parent) (Just c)

local :: BuffersEnv env' -> Lens' (FusionGraphState op env) (FusionGraphState op env')
local env' f s = (buffersEnv .~ s^.buffersEnv) <$> f (s & buffersEnv .~ env')

-- | Fresh computation label.
freshComp :: State (FusionGraphState op env) (Label Comp)
freshComp = do
  comp <- zoom currComp freshL'
  fusionILP %= insertComputation comp
  return comp

-- | Fresh buffer and the corresponding computation label.
--
-- The implementation of 'writers' makes it so by default the buffer is produced
-- by the computation that allocates it. This is possible because they have the
-- same label just, just different types. We still need to add the read edge to
-- the graph though.
freshBuff :: State (FusionGraphState op env) (Label Buff, Label Comp)
freshBuff = do
  c <- freshComp
  let b = coerce c
  fusionILP %= insertBuffer b
  fusionILP %= insertWrite (c, b)
  return (b, c)

-- | Read from a buffer.
readsBuffers :: HasCallStack => Label Comp -> Labels Buff -> State (FusionGraphState op env) ()
readsBuffers c = traverse_ \b -> do
  ws <- use $ writers b
  fusionILP %= c `reads` b
  fusionILP %= ws >-|b|-> c
  readers b %= S.insert c

-- | Require a buffer (i.e. to index into it or pass it to a function).
requiresBuffers :: HasCallStack => Label Comp -> Labels Buff -> State (FusionGraphState op env) ()
requiresBuffers c = traverse_ \b -> do
  ws <- use $ writers b
  fusionILP %= c `reads` b
  fusionILP %= ws >=|b|=> c
  readers b %= S.insert c


-- | Write to a buffer.
--
-- For a write to be safe we need to enforce the following:
-- 1. All readers run before the computation.
-- 2. All writers run before the computation.
-- 3. We become the sole writer of the buffer.
-- 4. We clear the readers of the buffer.
writesBuffers :: HasCallStack => Label Comp -> Labels Buff -> State (FusionGraphState op env) ()
writesBuffers c = traverse_ \b -> do
  rs <- use $ readers b
  ws <- use $ writers b
  fusionILP %= c `writes` b
  fusionILP %= rs >=|-|=> c
  fusionILP %= ws >=|-|=> c
  writers b .= S.singleton c
  readers b .= S.empty

-- | Mutate a buffer.
--
-- For a mutation to be safe we need to enforce the following:
-- 1. All readers run before this computation.
-- 2. All writers are infusible with this computation.
-- 3. We become the sole writer of the buffer.
-- 4. We clear the readers of the buffer.
mutatesBuffers :: HasCallStack => Label Comp -> Labels Buff -> State (FusionGraphState op env) ()
mutatesBuffers c = traverse_ \b -> do
  rs <- use $ readers b
  ws <- use $ writers b
  fusionILP %= c `reads` b
  fusionILP %= c `writes` b
  fusionILP %= rs >=|-|=> c
  fusionILP %= ws >=|b|=> c
  writers b .= S.singleton c
  readers b .= S.empty

-- | Return a buffer.
--
-- This can be interpreted as mutation with the identity function (i.e. no-op).
-- Since we don't actually change the contents of the buffer, we don't need to
-- enforce 1 and 4.
returnsBuffers :: HasCallStack => Label Comp -> Labels Buff -> State (FusionGraphState op env) ()
returnsBuffers c = traverse_ \b -> do
  ws <- use $ writers b
  fusionILP %= c `reads` b
  fusionILP %= c `writes` b
  fusionILP %= ws >=|b|=> c
  writers b .= S.singleton c

-- | Bind a buffer to a let.
--
-- This can be interpreted as mutation with the identity function (i.e. no-op).
-- Since we don't actually change the contents of the buffer, we don't need to
-- enforce 1 and 4. We also don't enforce 2, because doing so would prevent all
-- buffers from being non-manifest. (All buffers are bound to a let and
-- infusible edges force manifestation, so all buffers would be manifest.)
bindsBuffers :: HasCallStack => Label Comp -> Labels Buff -> State (FusionGraphState op env) ()
bindsBuffers c = traverse_ \b -> do
  ws <- use $ writers b
  fusionILP %= c `reads` b
  fusionILP %= c `writes` b
  fusionILP %= ws >-|b|-> c
  writers b .= S.singleton c

-- | A let-binding or function produces a buffer.
--
-- This just ensures that functions and let-bindings actually have a body.
-- In most cases this is not required, but if body doesn't use the bound buffer
-- it would try to generate a let-binding without a body.
-- TODO: This is ugly and should be removed, but for that the reconstruction
--       algorithm needs to be changed. It should be able to handle this case.
producesBuffers :: HasCallStack => Label Comp -> Labels Buff -> State (FusionGraphState op env) ()
producesBuffers c = traverse_ \b -> do
  ws <- use $ writers b
  fusionILP %= c `writes` b
  fusionILP %= flip (foldr' (c==|-|=>)) ws
  writers b .= S.singleton c



--------------------------------------------------------------------------------
-- Full Graph construction
--------------------------------------------------------------------------------

type FullGraph op = (FusionILP op, Symbols op)

-- The 2 instances below can be used to clean up the code in ILP.hs a bit.
instance HasFusionILP (FullGraph op) op where
  fusionILP :: Lens'  (FullGraph op) (FusionILP op)
  fusionILP f (ilp, sym) = f ilp <&> (,sym)

instance HasSymbols (FullGraph op) op where
  symbols :: Lens' (FullGraph op) (Symbols op)
  symbols f (ilp, sym) = f sym <&> (ilp,)

-- | Construct the full fusion graph for a program.
mkFullGraph :: MakesILP op => PreOpenAcc op () t -> FullGraph op
mkFullGraph acc = finalizeInplacePaths $ manifestBuffers (fold res) (s^.fusionILP, s^.symbols)
  where (res, s) = runState (mkFusionGraph acc) initialFusionGraphState

-- | Construct the full fusion graph for a function.
mkFullGraphF :: MakesILP op => PreOpenAfun op () a -> FullGraph op
mkFullGraphF acc = finalizeInplacePaths (s^.fusionILP, s^.symbols)
  where (_, s) = runState (mkFusionGraphF acc) initialFusionGraphState

-- | Make the supplied buffers manifest.
manifestBuffers :: HasFusionILP g op => Set (Label Buff) -> g -> g
manifestBuffers bs = fusionILP.constraints <>~ foldMap (\b -> manifest b .==. int 0) bs


--------------------------------------------------------------------------------
-- FusionGraph construction
--------------------------------------------------------------------------------

-- | Construct the fusion graph of a program.
mkFusionGraph :: forall op env t. MakesILP op
              => FusionGraphMaker PreOpenAcc op env t (BuffersTup t)
mkFusionGraph (Exec op args) = do
  lenv <- use buffersEnv
  renv <- use readersEnv
  wenv <- use writersEnv
  c    <- freshComp
  let labelledArgs = labelArgs args lenv
  let inpArrs      = inputArrays labelledArgs
  let outArrs      = outputArrays labelledArgs
  let notArrs      = notArrays labelledArgs
  c `readsBuffers`   (inpArrs `S.difference`   outArrs)
  c `writesBuffers`  (outArrs `S.difference`   inpArrs)
  c `mutatesBuffers` (inpArrs `S.intersection` outArrs)
  c `requiresBuffers` notArrs
  zoom (backendGraphState renv wenv) (mkGraph c op labelledArgs)
  symbol c ?= SExe lenv labelledArgs op
  return TupFunit

mkFusionGraph (Alet LeftHandSideUnit _ bnd body)
  = mkFusionGraph bnd >> mkFusionGraph body

-- In this definition I assume that whatever the right-hand side returns is
-- produced by a single computation, which is currently true because all
-- instructions attach themselves to the buffer.
mkFusionGraph (Alet lhs u bnd body) = do
  c       <- freshComp  -- TODO: If there is an issue with reconstruction, maybe move this behind "bndRes <- mkFusionGraph bnd". The order in which labels are generate affects the order in which the clusters are interpreted. Previously let-bindings where always in a separate cluster from the bound computation, but now they are usually in the same cluster to prevent all buffers from being manifest. That said, topsort should already be taking care of this ordering issue.
  lenv    <- use buffersEnv
  bndRes  <- mkFusionGraph bnd
  bndResW <- traverse (use . allWriters) bndRes
  c `bindsBuffers` fold bndRes
  lenv'   <- zoom currEnvL (weakenEnv lhs bndRes u lenv)
  symbol c ?= SLet (bindLHS lhs lenv') (fromSingletonSet $ fold bndResW) u
  bodyRes <- zoom (local lenv') (mkFusionGraph body)
  c `producesBuffers` fold bodyRes
  return bodyRes

mkFusionGraph (Return vars) = do
  lenv <- use buffersEnv
  c    <- freshComp
  let (_, bs, _) = getVarsFromEnv vars lenv
  c `returnsBuffers` fold bs
  symbol c ?= SRet lenv vars
  return bs

mkFusionGraph (Compute expr) = do
  lenv   <- use buffersEnv
  (b, c) <- freshBuff
  c `requiresBuffers` getExpDeps expr lenv
  symbol c ?= SCmp lenv expr
  return $ tupFlike (expType expr) (S.singleton b)

mkFusionGraph (Alloc shr e sh) = do
  lenv   <- use buffersEnv
  (b, c) <- freshBuff
  c `requiresBuffers` getVarsDeps sh lenv
  symbol c ?= SAlc lenv shr e sh
  return $ TupFsingle (S.singleton b)

mkFusionGraph (Unit v) = do
  lenv   <- use buffersEnv
  (b, c) <- freshBuff
  c `requiresBuffers` getVarDeps v lenv
  symbol c ?= SUnt lenv v
  return $ TupFsingle (S.singleton b)

mkFusionGraph (Use sctype n buff) = do
  (b, c) <- freshBuff
  symbol c ?= SUse sctype n buff
  return $ TupFsingle (S.singleton b)

mkFusionGraph (Acond cond tacc facc) = do
  lenv    <- use buffersEnv
  c_cond  <- freshComp
  zoom (scope c_cond) do
    c_true  <- freshComp
    c_false <- freshComp
    c_cond `requiresBuffers` getVarDeps cond lenv
    symbol c_cond ?= SITE lenv cond c_true c_false
    (t_res, t_renv, t_wenv) <- block c_true  mkFusionGraph tacc
    (f_res, f_renv, f_wenv) <- block c_false mkFusionGraph facc
    readersEnv .= M.unionWith S.union t_renv f_renv
    writersEnv .= M.unionWith S.union t_wenv f_wenv
    let res = t_res <> f_res
    c_cond `returnsBuffers` fold res
    return res

mkFusionGraph (Awhile u cond body init) = do
  lenv    <- use buffersEnv
  c_while <- freshComp
  zoom (scope c_while) do
    c_cond  <- freshComp
    c_body  <- freshComp
    let (_, init_res, _) = getVarsFromEnv init lenv
    c_while `requiresBuffers` fold init_res
    symbol c_while ?= SWhl lenv c_cond c_body init u
    (_       , cond_renv, cond_wenv) <- block c_cond (mkFusionGraphW u) cond
    (body_res, body_renv, body_wenv) <- block c_body (mkFusionGraphW u) body
    readersEnv .= M.unionWith S.union cond_renv body_renv
    writersEnv .= M.unionWith S.union cond_wenv body_wenv
    let res = init_res <> body_res
    c_while `returnsBuffers` fold res
    return res



-- | Construct the fusion graph of a single-argument function.
mkFusionGraphW :: forall op env s t. MakesILP op
               => Uniquenesses s -> FusionGraphMaker PreOpenAfun op env (s -> t) (BuffersTup t)
mkFusionGraphW _ (Abody _) = internalError "mkFusionGraphW: expected Alam"
mkFusionGraphW u (Alam lhs f) = do
  lenv <- use buffersEnv
  (S.singleton -> b, c) <- freshBuff
  let lhs' = lhsToTupR lhs
  lenv'<- zoom currEnvL (weakenEnv lhs (tupFlike lhs' b) u lenv)
  res  <- zoom (local lenv') (unresult <$> mkFusionGraphF f)
  resW <- traverse (use . allWriters) res
  symbol c ?= SFun (bindLHS lhs lenv') (fromSingletonSet $ fold resW)
  c `producesBuffers` fold res
  return res



-- | Construct the fusion graph of a function.
mkFusionGraphF :: forall op env t. MakesILP op
               => FusionGraphMaker PreOpenAfun op env t (BuffersTup (Result t))
mkFusionGraphF (Abody acc) = do
  c <- freshComp
  zoom (scope c) do
    res <- mkFusionGraph acc
    c `returnsBuffers` fold res
    symbol c ?= SBod res
    fusionILP.constraints %= (<> foldMap ((.==. int 0) . manifest) (fold res))
    return $ result res

mkFusionGraphF (Alam lhs f) = do
  lenv <- use buffersEnv
  (S.singleton -> b, c) <- freshBuff
  let lhs' = lhsToTupR lhs
  let u    = mapTupR (const Shared) lhs'  -- For now we assume variables to a function are shared. (safe)
  lenv'<- zoom currEnvL (weakenEnv lhs (tupFlike lhs' b) u lenv)
  res  <- zoom (local lenv') (mkFusionGraphF f)
  resW <- traverse (use . allWriters) res
  symbol c ?= SFun (bindLHS lhs lenv') (fromSingletonSet $ fold resW)
  c `producesBuffers` fold res
  return res



-- | Helper for if-then-else and while loop blocks.
block :: HasCallStack => Label Comp -> FusionGraphMaker f op env t (BuffersTup r)
      -> FusionGraphMaker f op env t (BuffersTup r, ReadersEnv, WritersEnv)
block c f x = zoom (scope c . protected writersEnv . protected readersEnv) do
  res <- f x
  symbol c ?= SBlk
  renv <- use readersEnv
  wenv <- use writersEnv
  return (res, renv, wenv)



-- | Type of functions that take an AST and produce a graph.
type FusionGraphMaker f op env t r = f op env t -> State (FusionGraphState op env) r

-- | Type-level function to get the result type of a function.
--
-- Note that to make this work I needed 'unsafeCoerce', because the constructors
-- of data types we encounter use either @t@ or @s -> t@. Unfortunately GHC
-- can't distinguish between these two cases since both are of kind 'Type'.
-- The current types used in Accelerate are simply too permissive to allow for
-- rigorous proofs.
type Result :: Type -> Type
type family Result t where
  Result (_ -> t) = Result t
  Result t        = t

result :: BuffersTup t -> BuffersTup (Result t)
result = unsafeCoerce
{-# INLINE result #-}

unresult :: BuffersTup (Result t) -> BuffersTup t
unresult = unsafeCoerce
{-# INLINE unresult #-}

{-
I probably want to not duplicate a buffer that is used as both input
and output. Doing so is extremely tricky because doing so requires that the
environment is updated to point to the new buffer. Because of this we can't
simply put the old environment back after a let binding.

Doing this isn't the worst, we just need to weaken the environment instead. What
is a problem is how to handle the backend. The backend needs to know which
buffers are its inputs and outputs and it needs to be able to query the graph.
Problem is, it needs to do these queries on the old graph which doesn't contain
the new buffer yet.

So avoinding duplicating buffers is probably best. In this case it's not
necessary to keep the environment in the state, but I'll do so regardless
because in most cases the environment isn't touched. I could in this case
move the graph out of the state since it might cause confusion as to whether I
am working on the full graph or some temporary subgraph that will be merged
later.

Bonus, this approach still allows for the duplication of input and ouput buffers
in a separate pass before fusion. Doing it like that won't have any of the
aforementioned problems since the buffer will be a proper part of the graph
and the environment before some operation is executed.
-}



--------------------------------------------------------------------------------
-- In-place update path extension
--------------------------------------------------------------------------------

-- | Creates unit-sized in-place update paths. Should be used by the backend to
--   create in-place update paths where applicable. We do not need to check the
--   type of the elements here, since these will be checked later. This ensures
--   we can still create paths that would alter the type of the elements to an
--   incompatible type and then back to a compatible type.
mkUnitInplacePaths :: HasCallStack => Label Comp -> ArgLabel (In sh s) -> ArgLabel (Out sh t) -> Set InplacePath
mkUnitInplacePaths c l1 l2
  | getLabelShape l1 == getLabelShape l2  -- This condition should always hold if used correctly, but we check it anyway.
  , bs1 <- getLabelUniqueArrDeps l1
  , bs2 <- getLabelUniqueArrDeps l2
  = foldMap (\b1 -> foldMap (\b2 -> S.singleton ((b1, c), (c, b2))) bs2) bs1
mkUnitInplacePaths _ _ _ = S.empty

-- | Combines the in-place update paths of length 1 (i.e. across computations)
--   to in-place update paths of arbitrary length.
combineInplacePaths :: FullGraph op -> FullGraph op
combineInplacePaths g = g&fusionILP.inplacePaths %~ stepsPaths 50
  where
    -- Keep extending the path until no more extensions are possible or the
    -- iteration limit reaches 0.
    -- The iteration limit is only there to prevent infinite loops, although I
    -- don't think this can happen.
    -- We could make this iteration limit an argument to the function and a
    -- global setting for the compiler later on.
    stepsPaths :: Int -> Set InplacePath -> Set InplacePath
    stepsPaths 0 ps = internalWarning "combineInplacePaths: iteration limit reached" False ps
    stepsPaths n ps | S.null ps = ps
                    | otherwise = ps <> stepsPaths (n-1) (foldMap stepPath ps)

    -- Extend the path by 1 step.
    -- This is done by looking at which computations can fuse with the end of
    -- the path, then finding any paths that start with the newly constructed
    -- read.
    stepPath :: InplacePath -> Set InplacePath
    stepPath (r, w@(_, b)) = case M.lookup w nextComps of
      Nothing -> S.empty
      Just cs -> flip foldMap cs \c -> case M.lookup (b, c) nextPaths of
        Nothing -> S.empty
        Just ws -> S.map (r,) ws

    -- For efficient lookup of extensions for paths.
    -- This maps read edges to the write edges that can be updated in-place with
    -- the read edge.
    nextPaths :: Map ReadEdge (Set WriteEdge)
    nextPaths = M.fromListWith S.union $ map (_2 %~ S.singleton) $ S.toList $ g^.fusionILP.inplacePaths

    -- For efficient lookup of which computation the data flows into.
    -- We only consider computations that can fuse with the previous computation
    -- because we can only perform an in-place update if the computations fuse.
    nextComps :: Map WriteEdge (Labels Comp)
    nextComps = M.fromListWith S.union $ map (tripleToLeftRec . (_3 %~ S.singleton)) $ S.toList $ g^.fusionILP.fusibleEdges

-- | Filters the in-place update paths to only include those that are valid.
filterInplacePaths :: forall op. FullGraph op -> FullGraph op
filterInplacePaths g = g & fusionILP.inplacePaths %~ S.filter sameElementType
  where
    -- Checks if two in-place updates have the same element type.
    sameElementType :: InplacePath -> Bool
    sameElementType ((b1, _), (_, b2))
      | Exists tp1 <- getElt b1
      , Exists tp2 <- getElt b2
      , Just Refl  <- matchTypeR tp1 tp2 = True
      | otherwise                        = False

    -- Gets the element size of a buffer.
    getElt :: Label Buff -> Exists TypeR
    getElt b = case g^.allocator b of
      Just (SAlc _ _ e _) -> Exists $ TupRsingle e
      Just (SUnt _ v)     -> Exists $ TupRsingle $ varType v
      Just (SUse e _ _)   -> Exists $ TupRsingle e
      Just (SFun lhs _)   -> groundsRtoTypeR $ lhsToTupR $ unbindLHS lhs
      Just _  -> internalError "getElementSize: not an array allocator"
      Nothing -> internalError "getElementSize: no allocator found"

    -- Use exists because we don't know the exact type.
    groundsRtoTypeR :: GroundsR s -> Exists TypeR
    groundsRtoTypeR TupRunit = Exists TupRunit
    groundsRtoTypeR (TupRsingle (GroundRscalar tp)) = Exists $ TupRsingle tp
    groundsRtoTypeR (TupRsingle (GroundRbuffer tp)) = Exists $ TupRsingle tp
    groundsRtoTypeR (TupRpair e1 e2)
      | Exists tp1 <- groundsRtoTypeR e1
      , Exists tp2 <- groundsRtoTypeR e2
      = Exists $ TupRpair tp1 tp2

-- | Finalizes the in-place update paths by combining them and filtering them.
finalizeInplacePaths :: FullGraph op -> FullGraph op
finalizeInplacePaths = filterInplacePaths . combineInplacePaths



-- | Naive approach: find in-place updates from scratch.
mkInplacePaths :: forall op. MakesILP op => FullGraph op -> FullGraph op
mkInplacePaths g = g&fusionILP.inplacePaths .~ validPaths
  where
    -- All valid in-place update paths in the graph.
    validPaths :: Set InplacePath
    validPaths = S.filter validInplaceUpdate $ foldMap go initialPaths

    -- Recursively extends the in-place path by looking at the next computation
    -- and its outputs.
    go :: InplacePath -> Set InplacePath
    go (r, w) = extendedPaths <> foldMap go extendedPaths
      where
        -- All paths that can be formed by extending the current path.
        extendedPaths :: Set InplacePath
        extendedPaths = case M.lookup w nextMap of
          Nothing -> S.empty
          Just cs -> flip foldMap cs \c -> case M.lookup c outputMap of
              Nothing -> S.empty
              Just bs -> S.map ((r,).(c,)) bs

    -- | Checks if the in-place update path is a valid one.
    --
    -- An in-place update path is valid if:
    -- 1. We have sole ownership of both buffers. (Alloc, Unit)
    -- 2. The buffers are of the same shape.
    -- 3. The elements in the buffers are of the same size.
    validInplaceUpdate :: InplacePath -> Bool
    validInplaceUpdate ((b1, _), (_, b2)) = case (getAlloc b1, getAlloc b2) of
        (SAlc env1 shr1 e1 sh1, SAlc env2 shr2 e2 sh2)
          | Just Refl <- matchShapeR shr1 shr2
          , (_, shVars1, _) <- getVarsFromEnv sh1 env1
          , (_, shVars2, _) <- getVarsFromEnv sh2 env2
          -> shVars1 == shVars2 && bytes e1 == bytes e2
        (SUnt _ v1, SUnt _ v2)
          -> bytes (varType v1) == bytes (varType v2)
        _ -> False
      where
        getAlloc :: Label Buff -> Symbol op
        getAlloc b = case g^.allocator b of
          Just x@SAlc{} -> x
          Just x@SUnt{} -> x
          Just x@SUse{} -> x
          Just x@SFun{} -> x
          Just _  -> internalError "getAlloc: not an array allocator"
          Nothing -> internalError "getAlloc: no allocator found"

        bytes :: ScalarType e -> Int
        bytes = bytesElt . TupRsingle

    -- The initial, length-1 paths that are formed from computations and all
    -- their inputs and outputs.
    initialPaths :: Set InplacePath
    initialPaths = flip foldMap (g^.fusionILP.readEdges) \r@(_,c) -> case M.lookup c outputMap of
        Nothing -> S.empty
        Just bs -> S.map ((r,).(c,)) bs

    -- For efficient lookup of outputs of computations.
    outputMap :: Map (Label Comp) (Labels Buff)
    outputMap = M.fromListWith S.union $ map (_2 %~ S.singleton) $ S.toList $ g^.fusionILP.writeEdges

    -- For efficient lookup of which computation the data flows into.
    -- We only consider computations that can fuse with the previous computation
    -- because we can only perform an in-place update if the computations fuse.
    nextMap :: Map WriteEdge (Labels Comp)
    nextMap = M.fromListWith S.union $ map (tripleToLeftRec . (_3 %~ S.singleton)) $ S.toList $ g^.fusionILP.fusibleEdges



--------------------------------------------------------------------------------
-- Reconstruction
--------------------------------------------------------------------------------

-- | Makes a ReindexPartial, which allows us to transform indices in @env@ into indices in @env'@.
-- We cannot guarantee the index is present in env', so we use the partiality of ReindexPartial by
-- returning a Maybe. Uses unsafeCoerce to re-introduce type information implied by the EnvLabels.
mkReindexPartial :: BuffersEnv env -> BuffersEnv env' -> ReindexPartial Maybe env env'
mkReindexPartial env env' idx = go env'
  where
    -- The EnvLabel in the original environment
    (e,_,_) = lookupIdxInEnv idx env
    go :: forall e a. BuffersEnv e -> Maybe (Idx e a)
    go ((e',_,_) :>>: rest) -- e' is the ELabel in the new environment
      -- Here we have to convince GHC that the top element in the environment
      -- really does have the same type as the one we were searching for.
      -- Some literature does this stuff too: 'effect handlers in haskell, evidently'
      -- and 'a monadic framework for delimited continuations' come to mind.
      -- Basically: standard procedure if you're using Ints as a unique identifier
      -- and want to re-introduce type information. :)
      -- Type applications allow us to restrict unsafeCoerce to the return type.
      | e == e' = Just $ unsafeCoerce @(Idx e _) @(Idx e a) ZeroIdx
      -- Recurse if we did not find e' yet.
      | otherwise = SuccIdx <$> go rest
    -- If we hit the end, the Elabel was not present in the environment.
    -- That probably means we'll error out at a later point, but maybe there is
    -- a case where we try multiple options? No need to worry about it here.
    go EnvNil = Nothing


--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Lens that protects a given value from being modified.
protected :: Lens' s a -> Lens' s s
protected l f s = (l .~ s^.l) <$> f s

-- | Lens that protects all but the given value from being modified.
unprotected :: Lens' s a -> Lens' s s
unprotected l f s = (\s' -> s & l .~ s'^.l) <$> f s

-- | Lens that temporarily uses the supplied value in place of the current
--   value, then restores the original value.
with :: Lens' s a -> a -> Lens' s s
with l a f s = (l .~ s^.l) <$> f (s & l .~ a)

-- | Converts a singleton set into a value.
--
-- This function is partial and will throw an error if the set is not singleton.
fromSingletonSet :: HasCallStack => Set a -> a
fromSingletonSet (S.toList -> [x]) = x
fromSingletonSet _ = internalError "fromSingletonSet: Set is not singleton."

-- | Print out information about the given buffer.
traceBuff :: Label Buff -> State (FusionGraphState op env) ()
traceBuff b = do
  c_alloc   <- use $ allocator b
  c_readers <- use $ readers b
  c_writers <- use $ writers b
  traceM $ "  Buffer " ++ show b ++ ":"
  traceM $ "    Allocated by: " ++ show c_alloc
  traceM $ "    Readers:      " ++ show c_readers
  traceM $ "    Writers:      " ++ show c_writers

-- | Print out information about the given computation.
traceComp :: Label Comp -> State (FusionGraphState op env) ()
traceComp c = do
  c_symb   <- use $ symbol c
  traceM $ "  Computation " ++ show c ++ ":"
  traceM $ "    Symbol:       " ++ show c_symb

-- | Print out information about the current environment.
traceEnv' :: BuffersEnv env' -> State (FusionGraphState op env) ()
traceEnv' env = do
  traceM "  Environment: "
  forLEnv_ env \bs -> traceM $ "    " ++ show bs

traceEnv :: State (FusionGraphState op env) ()
traceEnv = use buffersEnv >>= traceEnv'

-- | Converts a triple (a, b, c) into ((a, b), c)
tripleToLeftRec :: (a, b, c) -> ((a, b), c)
tripleToLeftRec (x, y, z) = ((x, y), z)



--------------------------------------------------------------------------------
-- Converting Graphs to DOT
--------------------------------------------------------------------------------

-- | Converts a graph to a DOT representation.
toDOT :: FusionGraph -> Symbols op -> String
toDOT g syms = "strict digraph {\n" ++
  concatMap (\c -> "  <" ++ show c ++ "> [shape=box, label=\"" ++ show (syms M.! c) ++ tail (show c) ++ "\"];\n") (g^.computationNodes) ++
  concatMap (\b -> "  <" ++ show b ++ "> [shape=circle, label=\"" ++ show b ++ "\"];\n") (g^.bufferNodes) ++
  concatMap (\(b,c) -> "  <" ++ show b ++ "> -> <" ++ show c ++ "> [];\n") (g^.readEdges) ++
  concatMap (\(c,b) -> "  <" ++ show c ++ "> -> <" ++ show b ++ "> [];\n") (g^.writeEdges) ++
  concatMap (\((b1, _), (_, b2)) -> "  <" ++ show b1 ++ "> -> <" ++ show b2 ++ "> [color=gray, style=dotted];\n") (g^.inplacePaths) ++
  concatMap (\(c1,_,c2) -> "  <" ++ show c1 ++ "> -> <" ++ show c2 ++ "> [color=green];\n") (g^.fusibleEdges) ++
  concatMap (\(c1,_,c2) -> "  <" ++ show c1 ++ "> -> <" ++ show c2 ++ "> [color=red];\n") (g^.infusibleEdges) ++
  concatMap (\(c1,c2) -> "  <" ++ show c1 ++ "> -> <" ++ show c2 ++ "> [style=dashed, color=red];\n") (g^.orderEdges) ++
  "}\n"
