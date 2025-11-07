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
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx (ESSAIdx)

-- === Arg Wrapper ===
-- Wrapper used when passing the properties of the call values of a funciton

data ConstraintArgsElem t where
  NewBindArg  :: DataConstraints t -> ControlConstraints t -> SCEVConstraints t -> ConstraintArgsElem t
  KeepBindArg :: TupR (BCConstraint (HMaybe ESSAIdx)) t -> ConstraintArgsElem t

emptyDiffArg :: TupR GroundR t -> ConstraintArgsElem t
emptyDiffArg tp = NewBindArg (mapTupR bccEmpty tp) (mapTupR bccEmpty tp) (mapTupR bccEmpty tp)

data ConstraintsArgs t where
    ConstraintsArgsCons 
      :: ConstraintArgsElem t
      -> ConstraintsArgs t' 
      -> ConstraintsArgs (t -> t')
    ConstraintsArgsNil  :: ConstraintsArgs ()

emptyConstraintsArgs :: PreOpenAfun op env t -> ConstraintsArgs (TypeToArgs t)
emptyConstraintsArgs (Alam x rest) = ConstraintsArgsCons (emptyDiffArg tp) (emptyConstraintsArgs rest)
    where tp = lhsToTupR x
emptyConstraintsArgs (Abody body) | BCBodyDict <- isBody body = ConstraintsArgsNil

diffArg1 
  :: ConstraintArgsElem t
  -> ConstraintsArgs (t -> ())
diffArg1 e = ConstraintsArgsCons e ConstraintsArgsNil

diffArg2 
  :: ConstraintArgsElem t
  -> ConstraintArgsElem t'
  -> ConstraintsArgs (t -> t' -> ())
diffArg2 e1 e2 = ConstraintsArgsCons e1 $ ConstraintsArgsCons e2 ConstraintsArgsNil