module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve where

data FusionObjective
  = NumClusters         -- ^ Minimise the number of clusters.
  | ArrayReads          -- ^ Minimise the number of array reads.
  | ArrayReadsWrites    -- ^ Minimise the number of array reads and writes.
  | IntermediateArrays  -- ^ Minimise the number of intermediate arrays.
  | FusedEdges          -- ^ Minimise the number of unfused edges.
  | Everything          -- ^ Minimise the number of clusters and array reads/writes.

data IUpdatesObjective
  = NoInplaceUpdates        -- ^ Do not use in-place updates.
  | NumInplaceUpdates       -- ^ Each in-place update counts as 1.
  | WeightedInplaceUpdates  -- ^ Use the weights and merge strategy defined by the backend.
