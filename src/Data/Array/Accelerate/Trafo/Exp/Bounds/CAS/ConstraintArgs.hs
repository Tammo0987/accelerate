{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.ConstraintArgs where
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.RecChain
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Representation.Type

-- === Arg Wrapper ===
-- Wrapper used when passing the properties of the call values of a funciton

data ConstraintsArgs t where
    ConstraintsArgsCons 
      :: DataConstraints t 
      -> ControlConstraints t 
      -> SCEVConstraints t 
      -> ConstraintsArgs t' 
      -> ConstraintsArgs (t -> t')
    ConstraintsArgsNil  :: ConstraintsArgs ()

emptyConstraintsArgs :: PreOpenAfun op env t -> ConstraintsArgs (TypeToArgs t)
emptyConstraintsArgs (Alam x rest) = ConstraintsArgsCons (mapTupR bccEmpty tp) (mapTupR bccEmpty tp) (mapTupR bccEmpty tp) (emptyConstraintsArgs rest)
    where tp = lhsToTupR x
emptyConstraintsArgs (Abody body) | BCBodyDict <- isBody body = ConstraintsArgsNil

diffArg1 
  :: DataConstraints    t 
  -> ControlConstraints t 
  -> SCEVConstraints t 
  -> ConstraintsArgs (t -> ())
diffArg1 d b c = ConstraintsArgsCons d b c ConstraintsArgsNil

diffArg2 
  :: DataConstraints    t 
  -> ControlConstraints t 
  -> SCEVConstraints    t 
  -> DataConstraints    t' 
  -> ControlConstraints t' 
  -> SCEVConstraints    t' 
  -> ConstraintsArgs (t -> t' -> ())
diffArg2 d1 b1 c1 d2 b2 c2 = ConstraintsArgsCons d1 b1 c1 $ ConstraintsArgsCons d2 b2 c2 ConstraintsArgsNil