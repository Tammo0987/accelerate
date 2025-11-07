{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints where
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.AST.Operation
import Lens.Micro.TH
import qualified Data.Map as Map
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Type
import Control.Monad (join)
import Data.Primitive.Vec

-- === Basic Diff Constraint ===
newtype BCConstraint c t = BCConstraint ((ConstraintGround (HBounds c)) t)
instance HFunctor BCConstraint where
  hfmap f (BCConstraint c) = BCConstraint (hfmap (hfmap f) c)
instance HZip BCConstraint where
  hzipWith f (BCConstraint c1) (BCConstraint c2) = BCConstraint (hzipWith (hzipWith f) c1 c2)
instance HBizip BCConstraint where
  hbizipWith lf uf c1 c2 =
    let c1' = HBounds $ unwrapBCConstraint c1
        c2' = HBounds $ unwrapBCConstraint c2
        in bccPut (toCGType c1) $ runHBounds $ hbizipWith lf uf c1' c2'

instance Show (c (VectorAgnostic (BufferAgnostic t))) => Show (BCConstraint c t) where
  show c = show $ unwrapBCConstraint c

class ToCGType a where
  toCGType :: a t -> CGType t

instance ToCGType (BCConstraint c) where
  toCGType (BCConstraint (ScalarConstraint tp _)) = toCGType (GroundRscalar tp)
  toCGType (BCConstraint (BufferConstraint tp _)) = toCGType (GroundRbuffer tp)

bccSingleType :: BCConstraint c t -> SingleType (SingleTypeOf t)
bccSingleType (BCConstraint (ScalarConstraint (SingleScalarType tp) (SingleConstraint _))) = tp
bccSingleType (BCConstraint (BufferConstraint (SingleScalarType tp) (SingleConstraint _))) = tp
bccSingleType (BCConstraint (ScalarConstraint (VectorScalarType (VectorType _ tp)) (VectorConstraint _))) = tp
bccSingleType (BCConstraint (BufferConstraint (VectorScalarType (VectorType _ tp)) (VectorConstraint _))) = tp
bccSingleType (BCConstraint (ScalarConstraint (SingleScalarType tp) (VectorConstraint _))) = case absurdSingleVector tp of {}
bccSingleType (BCConstraint (BufferConstraint (SingleScalarType tp) (VectorConstraint _))) = case absurdSingleVector tp of {}

bccBind :: BCConstraint a t -> (a (SingleTypeOf t) -> BCConstraint b t) -> BCConstraint b t
bccBind bcc f = let x = f <$> unwrapBCConstraint bcc
                    y = unwrapBCConstraint <$> x
                    z = join y
                    in bccPut (toCGType bcc) z

unwrapBCConstraint :: BCConstraint c t -> Bounds (c (SingleTypeOf t))
unwrapBCConstraint (BCConstraint a) = runHBounds $ unwrapS $ unwrapG a

bccToScalar :: (TypeNotBuffer t) => BCConstraint c (Buffer t) -> BCConstraint c t
bccToScalar bcc@(BCConstraint (BufferConstraint tp cs)) = bccPut (ScalarConstraint tp . toCSType cs) $ unwrapBCConstraint bcc

bccToBuffer :: (TypeNotBuffer t) => BCConstraint c t -> BCConstraint c (Buffer t)
bccToBuffer bcc@(BCConstraint (ScalarConstraint tp cs)) = bccPut (BufferConstraint tp . toCSType cs) $ unwrapBCConstraint bcc

bccsToScalar :: forall t c .
  (BufferAgnostic t ~ t) => TypeR t -> TupR (BCConstraint c) (Buffers t) -> TupR (BCConstraint c) t
bccsToScalar tpr (TupRsingle bcc@(BCConstraint (BufferConstraint tp cs)))
  | Refl <- bufferAgnostic tpr
  = TupRsingle $ bccPut (ScalarConstraint tp . toCSType cs) $ unwrapBCConstraint bcc
bccsToScalar (TupRpair tpr1 tpr2) (TupRpair a b) = TupRpair (bccsToScalar tpr1 a) (bccsToScalar tpr2 b)
bccsToScalar tpr TupRunit       | Refl <- bufferAgnostic tpr = TupRunit
bccsToScalar _ _ = error "mismatched tuple"

bccsToBuffers :: forall t c .
  (BufferAgnostic t ~ t) => TypeR t -> TupR (BCConstraint c) t -> TupR (BCConstraint c) (Buffers t)
bccsToBuffers tpr (TupRsingle bcc@(BCConstraint (ScalarConstraint tp cs)))
  | Refl <- bufferAgnostic tpr, Refl <- reprIsSingle @ScalarType @t @Buffer tp
  = TupRsingle $ bccPut (BufferConstraint tp . toCSType cs) $ unwrapBCConstraint bcc
bccsToBuffers (TupRpair tpr1 tpr2) (TupRpair a b) = TupRpair (bccsToBuffers tpr1 a) (bccsToBuffers tpr2 b)
bccsToBuffers _ TupRunit       = TupRunit
bccsToBuffers _ _              = error "mismatched tuple"

bccPut :: ((t' ~ SingleTypeOf t)) => CGType t -> Bounds (c t') -> BCConstraint c t
bccPut ctype b = BCConstraint $ ctype $ HBounds b

-- === Wrapper to lift Scalar Constraints to Buffer level ===

data ConstraintScalar c t where
    SingleConstraint :: (IsSingle t, BufferAgnostic t ~ t, VectorAgnostic t ~ t) => c t -> ConstraintScalar c t
    VectorConstraint :: (IsSingle t, BufferAgnostic t ~ t, VectorAgnostic t ~ t) => c t -> ConstraintScalar c (Vec n t)

unwrapS :: ConstraintScalar c t -> c (VectorAgnostic t)
unwrapS (SingleConstraint a) = a
unwrapS (VectorConstraint a) = a

instance HFunctor ConstraintScalar where
  hfmap f (SingleConstraint x) = SingleConstraint (f x)
  hfmap f (VectorConstraint x) = VectorConstraint (f x)

instance HZip ConstraintScalar where
  hzipWith f (SingleConstraint x) (SingleConstraint y) = SingleConstraint (f x y)
  hzipWith f (VectorConstraint x) (VectorConstraint y) = VectorConstraint (f x y)

instance ToCSType (ConstraintScalar c) where
  toCSType :: ConstraintScalar c t -> CSType t
  toCSType (SingleConstraint _) = SingleConstraint
  toCSType (VectorConstraint _) = VectorConstraint

data ConstraintGround c t where
    ScalarConstraint :: (BufferAgnostic t ~ t) => ScalarType t -> ConstraintScalar c t -> ConstraintGround c t
    BufferConstraint :: (BufferAgnostic t ~ t) => ScalarType t -> ConstraintScalar c t -> ConstraintGround c (Buffer t)

cgTypeScalar :: ScalarType t -> CGType t
cgTypeScalar tp = toCGType (GroundRscalar tp)

unwrapG :: ConstraintGround c t -> ConstraintScalar c (BufferAgnostic t)
unwrapG (ScalarConstraint _ a) = a
unwrapG (BufferConstraint _ a) = a

instance HFunctor ConstraintGround where
  hfmap f (ScalarConstraint tp x) = ScalarConstraint tp (hfmap f x)
  hfmap f (BufferConstraint tp x) = BufferConstraint tp (hfmap f x)

instance HZip ConstraintGround where
  hzipWith f (ScalarConstraint tp x) (ScalarConstraint _ y) = ScalarConstraint tp (hzipWith f x y)
  hzipWith f (BufferConstraint tp x) (BufferConstraint _ y) = BufferConstraint tp (hzipWith f x y)

data BasicDiff v t = BDiff {var :: Maybe (v t), weight :: Int}
instance HPure BasicDiff where
  hpure v = BDiff (Just v) 0
instance FromConst (BasicDiff v) where
  fromConst = BDiff Nothing . fromIntegral

instance FromESSA (BasicDiff ESSAIdx) where
  fromESSA i = BDiff (Just i) 0

instance Show (v t) => Show (BasicDiff v t) where
  show :: Show (v t) => BasicDiff v t -> String
  show (BDiff v w) = "("++ maybe "" ((++ " + ") . show) v ++ show w ++ ")"

instance Distributes (BCConstraint v) where
  reprIsSingle :: BCConstraint v t -> Distribute f t :~: f t
  reprIsSingle (BCConstraint (ScalarConstraint tp _)) = reprIsSingle tp
  reprIsSingle (BCConstraint (BufferConstraint tp _)) = reprIsSingle (GroundRbuffer tp)
  pairImpossible :: BCConstraint v1 (t, v2) -> a
  pairImpossible (BCConstraint (ScalarConstraint tp _)) = pairImpossible tp
  unitImpossible :: BCConstraint v () -> a
  unitImpossible (BCConstraint (ScalarConstraint tp _)) = unitImpossible tp

data DiffExp v t where
    Diff     :: BasicDiff v t -> DiffExp v t
    PhiDiff  :: DiffExp   v t -> DiffExp v t -> DiffExp v t
    DiffUndef    :: DiffExp v t
    deriving Show

instance HPure DiffExp where
  hpure a = Diff $ BDiff (Just a) 0
instance FromConst (DiffExp v) where
  fromConst i = Diff $ fromConst (fromIntegral i :: Int)
instance FromESSA (DiffExp ESSAIdx) where
  fromESSA = Diff . fromESSA

class Empty c where
    empty :: c t
class FromConst c where
    fromConst :: (Integral a) => a -> c t
class FromESSA h where
  fromESSA :: ESSAIdx t -> h t

instance Empty (Tag Bool) where
  empty = Tag False

instance Empty (PrefixHList e) where
  empty = PEmpty

type CSType t = (forall v . v (VectorAgnostic t) -> ConstraintScalar v t)
type CGType t = (forall v . v (SingleTypeOf t) -> ConstraintGround v t)

class ToCSType s where
  toCSType ::  s t -> CSType t

instance ToCSType SingleType where
  toCSType tp | BCSingleDict <- reprBCSingle tp  = SingleConstraint
instance ToCSType ScalarType where
  toCSType (SingleScalarType tp) | BCSingleDict <- reprBCSingle tp = SingleConstraint
  toCSType (VectorScalarType (VectorType _ tp)) | BCSingleDict <- reprBCSingle tp = VectorConstraint

instance ToCGType GroundR where
  toCGType :: GroundR t -> CGType t
  toCGType (GroundRscalar tp) | BCScalarDict <- reprBCScalar tp = ScalarConstraint tp . toCSType tp
  toCGType (GroundRbuffer tp) | BCScalarDict <- reprBCScalar tp = BufferConstraint tp . toCSType tp

bccConst :: (FromConst c) => CGType t -> Bounds Int -> BCConstraint c t
bccConst ct a = bccPut ct $ fromConst <$> a

bccEmpty :: (Empty c) => GroundR t -> BCConstraint c t
bccEmpty gr = bccPut (toCGType gr) $ pure empty

bccsEmpty :: (HasGroundsR a, Empty c) => a t -> TupR (BCConstraint c) t
bccsEmpty a = bccsEmptyG $ groundsR a

bccsEmptyG :: (Empty c) => GroundsR t -> TupR (BCConstraint c) t
bccsEmptyG = mapTupR bccEmpty

instance HasGroundsR GroundsR where
  groundsR = id

-- === Dataflow ===
type ESSADiffExp t = DiffExp ESSAIdx t
type DataConstraint t = BCConstraint (HMaybe (DiffExp ESSAIdx)) t
type DataConstraints t = TupR (BCConstraint (HMaybe (DiffExp ESSAIdx))) t

instance Empty (HMaybe v) where
    empty = hnothing
instance (FromConst v) => FromConst (HMaybe v) where
  fromConst = hjust . fromConst

-- === Controlflow ===
-- The lists of properties that take effect on Pi assignment, after branching
type ControlMap  t = Map.Map (ESSAIdx t) (DiffExp ESSAIdx t)

data ControlMaps t =
  ControlMaps
    { cTrue  :: ControlMap t
    , cFalse :: ControlMap t }
    deriving Show
type ControlConstraint t =  BCConstraint ControlMaps t
type ControlConstraints t = TupR (BCConstraint ControlMaps) t

instance Empty ControlMaps where
  empty :: ControlMaps t
  empty = ControlMaps Map.empty Map.empty

zipControlMaps :: (ControlMap t -> ControlMap t -> ControlMap t) -> (ControlMap t -> ControlMap t -> ControlMap t) -> ControlMaps t -> ControlMaps t -> ControlMaps t
zipControlMaps ft ff (ControlMaps t1 f1) (ControlMaps t2 f2) = ControlMaps (ft t1 t2) (ff f1 f2)

-- === CS Analysis Result Format ===
data RCS t = RCS
  {  _rData    :: DataConstraints    t
  ,  _rControl :: ControlConstraints t
  }
makeLenses ''RCS

-- === Helpers ===
phi :: DataConstraints t -> DataConstraints t -> DataConstraints t
phi = hzipWith (hzipWith (hzipWith PhiDiff))