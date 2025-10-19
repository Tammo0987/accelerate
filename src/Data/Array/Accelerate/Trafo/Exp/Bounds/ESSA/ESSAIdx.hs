{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx where
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Array.Buffer (Buffer)
import Data.Array.Accelerate.Representation.Type
import Data.Void (Void)
import Data.Primitive.Vec

-- Indices used to uniquely identify dataflow and controlflow independent states of the program variables
data ESSAIdx t = ESSAIdx {essaType :: SingleType t, essaInt :: Int}

instance Show (ESSAIdx t) where
  show = ("n"++) . show . essaInt

instance Eq (ESSAIdx t) where
  (==) i1 i2 = essaInt i1 == essaInt i2

instance Ord (ESSAIdx t) where
  compare :: ESSAIdx t -> ESSAIdx t -> Ordering
  compare i1 i2 = compare (essaInt i1) (essaInt i2)

data BCSingleDict t where 
  BCSingleDict :: (IsSingle t, SingleTypeOf t ~ t, BufferAgnostic t ~ t, VectorAgnostic t ~ t) => BCSingleDict t

class BCIsSingle a where
    reprBCSingle :: a t -> BCSingleDict t

instance BCIsSingle SingleType where
  reprBCSingle (NumSingleType tp) | BCSingleDict <- reprBCSingle tp = BCSingleDict

instance BCIsSingle NumType where
  reprBCSingle (IntegralNumType int  ) = reprBCSingle int
  reprBCSingle (FloatingNumType float) = reprBCSingle float

instance BCIsSingle IntegralType where
    reprBCSingle TypeInt     = BCSingleDict
    reprBCSingle TypeInt8    = BCSingleDict
    reprBCSingle TypeInt16   = BCSingleDict
    reprBCSingle TypeInt32   = BCSingleDict
    reprBCSingle TypeInt64   = BCSingleDict
    reprBCSingle TypeWord    = BCSingleDict
    reprBCSingle TypeWord8   = BCSingleDict
    reprBCSingle TypeWord16  = BCSingleDict
    reprBCSingle TypeWord32  = BCSingleDict
    reprBCSingle TypeWord64  = BCSingleDict

instance BCIsSingle FloatingType where
    reprBCSingle TypeHalf   = BCSingleDict
    reprBCSingle TypeFloat  = BCSingleDict
    reprBCSingle TypeDouble = BCSingleDict

instance BCIsSingle PrimConst where
    reprBCSingle (PrimMinBound (IntegralBoundedType int)) = reprBCSingle int
    reprBCSingle (PrimMaxBound (IntegralBoundedType int)) = reprBCSingle int
    reprBCSingle (PrimPi float)                           = reprBCSingle float

absurdScalarBuffer :: ScalarType (Buffer t) -> Void
absurdScalarBuffer (SingleScalarType (NumSingleType (IntegralNumType int  ))) = case int   of {}
absurdScalarBuffer (SingleScalarType (NumSingleType (FloatingNumType float))) = case float of {}

absurdSingleVector :: SingleType (Vec n t) -> Void
absurdSingleVector (NumSingleType (IntegralNumType int  )) = case int   of {}
absurdSingleVector (NumSingleType (FloatingNumType float)) = case float of {}

class HasIdx a where
  getIdx :: a t -> ESSAIdx t

instance HasIdx ESSAIdx where
  getIdx (ESSAIdx tp i) = ESSAIdx tp i

data BCScalarDict t where
  BCScalarDict :: (BufferAgnostic t ~ t) => BCScalarDict t

class BCIsScalar a where
  reprBCScalar :: a t -> BCScalarDict t

instance BCIsScalar TypeR where
  reprBCScalar TupRunit = BCScalarDict
  reprBCScalar (TupRsingle tp) = reprBCScalar tp
  reprBCScalar (TupRpair t1 t2) = case (reprBCScalar t1, reprBCScalar t2) of
    (BCScalarDict, BCScalarDict) -> BCScalarDict

instance BCIsScalar (PreOpenExp (ArrayInstr benv) env) where
  reprBCScalar e = reprBCScalar $ expType e

instance BCIsScalar ScalarType where
  reprBCScalar (SingleScalarType tp) | BCSingleDict <- reprBCSingle tp = BCScalarDict
  reprBCScalar (VectorScalarType (_ :: VectorType (Vec n a))) = BCScalarDict