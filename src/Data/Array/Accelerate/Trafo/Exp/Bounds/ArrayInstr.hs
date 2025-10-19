{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.ArrayInstr where
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Exp.Bounds.BCState
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints (BCConstraint)
import Data.Array.Accelerate.Representation.Type (TupR)
import Data.Array.Accelerate.Array.Buffer

-- === Interface for backend-specific array operation optimization ===
class BCOperation op where
    bcOperation :: op f -> AbstInterpOperation op f

type Bidirectional = Bool

newtype AbstInterpOperation op f =
    AbstInterpOperation (
        forall benv prev . Args benv f
        -> BCState GroundR op prev '(benv, ())
        (  BCOptOperation  op benv
        ,  TupR (BCConstraint ESSAIdx) (Buffers (ArrayInstrReturnType f))
        ,  GroundVars             benv (Buffers (ArrayInstrReturnType f))
        ,  AnalysisResult              (Buffers (ArrayInstrReturnType f)) ()
        ,  Bidirectional
        ))

data BCOptOperation op env where
    BCOptOperation
        :: op f
        -> Args env f
        -> BCOptOperation op env

type family ArrayInstrReturnType f where
    ArrayInstrReturnType (Mut sh e -> b) = Prepend e (ArrayInstrReturnType b)
    ArrayInstrReturnType (Out sh e -> b) = Prepend e (ArrayInstrReturnType b)
    ArrayInstrReturnType (a        -> b) = ArrayInstrReturnType b
    ArrayInstrReturnType ()              = End
