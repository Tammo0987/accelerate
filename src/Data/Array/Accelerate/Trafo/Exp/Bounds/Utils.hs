{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.Utils where
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Analysis.Match
import Data.Kind (Type)
import Lens.Micro.TH
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.AST.LeftHandSide (LeftHandSide)
import Data.Array.Accelerate.AST.Idx
import Data.Primitive.Vec
import qualified Data.Map as Map

type family Prepend e r where
    Prepend e End = e
    Prepend e r  = (e, r)
data End;

type family Fst (pair :: (t1, t2)) where
  Fst '(a, b) = a
type family Snd (pair :: (t1, t2)) where
  Snd '(a, b) = b

type family TypeToArgs t where
    TypeToArgs (t -> t') = t -> TypeToArgs t'
    TypeToArgs  t        = ()

type family ReturnType t where
    ReturnType (t -> t') = ReturnType t'
    ReturnType  t        = t

type family ArgsType   t where
    ArgsType  (t -> t') = (ArgsType t', t)
    ArgsType   t        = ()

data BCBodyDict t where
  BCBodyDict :: (TypeToArgs t ~ (), ArgsType t ~ (), ReturnType t ~ t, (t, t) ~ Prepend t t) => BCBodyDict t

isBody
    :: forall t (expr :: (Type -> Type) -> Type -> Type -> Type) (op :: Type -> Type) env
    .  (HasGroundsR (expr op env))
    => expr op env t
    -> BCBodyDict t
isBody e = case groundsR e of
    TupRunit -> BCBodyDict
    TupRpair{} -> BCBodyDict
    (TupRsingle (GroundRbuffer _)) -> BCBodyDict
    (TupRsingle (GroundRscalar (VectorScalarType _))) -> BCBodyDict
    (TupRsingle (GroundRscalar (SingleScalarType (NumSingleType t)))) -> case t of
        IntegralNumType TypeInt    -> BCBodyDict
        IntegralNumType TypeInt8   -> BCBodyDict
        IntegralNumType TypeInt16  -> BCBodyDict
        IntegralNumType TypeInt32  -> BCBodyDict
        IntegralNumType TypeInt64  -> BCBodyDict
        IntegralNumType TypeWord   -> BCBodyDict
        IntegralNumType TypeWord8  -> BCBodyDict
        IntegralNumType TypeWord16 -> BCBodyDict
        IntegralNumType TypeWord32 -> BCBodyDict
        IntegralNumType TypeWord64 -> BCBodyDict
        FloatingNumType TypeHalf   -> BCBodyDict
        FloatingNumType TypeFloat  -> BCBodyDict
        FloatingNumType TypeDouble -> BCBodyDict

getSingle :: TupR a t -> a t
getSingle (TupRsingle a) = a
getSingle _ = error "expected TupRsingle"

-- Bounds checking analysis is agnostic to the level it operates on. We use a singleton to make this abstraction
data SType s where
    STypeGround :: SType GroundR
    STypeScalar :: SType ScalarType

-- Type family used to route the abstract environment on the concrete, distinct environments
type family PutByType s benv aenv env :: (a, a) where
    PutByType GroundR     benv aenv env = '(env, aenv)
    PutByType ScalarType benv aenv env = '(benv, env)

type family ChooseByType s t1 t2 where
    ChooseByType GroundR    t1 t2 = t1
    ChooseByType ScalarType t1 t2 = t2

type family GetByType s ssaEnv where
    GetByType GroundR    '(benv, env) = benv
    GetByType ScalarType '(benv, env) = env

type family BenvFromOp t where
  BenvFromOp (ArrayInstr benv) = benv

type SingleTypeOf t = VectorAgnostic (BufferAgnostic t)

type family BufferAgnostic t where
  BufferAgnostic ()          = ()
  BufferAgnostic (a, b)      = (BufferAgnostic a, BufferAgnostic b)
  BufferAgnostic (Buffer  t) = BufferAgnostic t
  BufferAgnostic  t          = t

type family VectorAgnostic t where
  VectorAgnostic ()          = ()
  VectorAgnostic (a, b)      = (VectorAgnostic a, VectorAgnostic b)
  VectorAgnostic (Vec n   t)   = t
  VectorAgnostic  t          = t

bufferAgnostic :: forall t a . (TypeNotBuffer t, Distributes a) => TupR a t -> t :~: BufferAgnostic (Buffers t)
bufferAgnostic (TupRsingle a) | Refl <- reprIsSingle @a @t @Buffer a = Refl
bufferAgnostic (TupRpair a b) = case (bufferAgnostic a, bufferAgnostic b) of
  (Refl, Refl) -> Refl
bufferAgnostic TupRunit = Refl

applySingleTypeOf :: (t :~: SingleTypeOf (Buffers t)) -> TupR a (SingleTypeOf (Buffers t)) -> TupR a t
applySingleTypeOf Refl x = x

type TypeNotBuffer t = BufferAgnostic t ~ t

class HFunctor (h :: (Type -> Type) -> Type -> Type) where
  hfmap :: (forall a. f a -> g a) -> h f t -> h g t

infixl 4 <$$>
(<$$>) :: HFunctor h => (forall a. f a -> g a) -> h f t -> h g t
(<$$>) = hfmap

newtype FuncWrapper a b t = FuncWrapper (a t -> b t)
class HFunctor h => HZip h where
  hzipWith :: (forall a. f a -> g a -> r a) -> h f t -> h g t -> h r t
class HZip h => HBizip h where
  hbizipWith :: (forall a. f a -> g a -> r a) -> (forall a. f a -> g a -> r a) -> h f t -> h g t -> h r t

hzipWith3
  :: HZip h
  => (forall a. e a -> f a -> g a -> r a)
  -> h e t -> h f t -> h g t -> h r t
hzipWith3 f a b c =
  let f' = hzipWith (\ea fa -> FuncWrapper (f ea fa)) a b
  in  hzipWith (\(FuncWrapper f'') ca -> f'' ca) f' c

hzipWith4
  :: HZip h
  => (forall a. e a -> f a -> g a -> k a -> r a)
  -> h e t -> h f t -> h g t -> h k t -> h r t
hzipWith4 f a b c d =
  let f'  = hzipWith (\ea fa -> FuncWrapper (FuncWrapper . f ea fa)) a b
      f'' = hzipWith (\(FuncWrapper g2) ga -> g2 ga) f' c
  in  hzipWith (\(FuncWrapper k2) ka -> k2 ka) f'' d


hbizipWith3
  :: HBizip h
  => (forall a. e a -> f a -> g a -> r a)
  -> (forall a. e a -> f a -> g a -> r a)
  -> h e t -> h f t -> h g t -> h r t
hbizipWith3 lf uf a b c =
  let f' = hbizipWith (\a' b' -> FuncWrapper (lf a' b')) (\a' b' -> FuncWrapper (uf a' b')) a b
    in hzipWith (\(FuncWrapper f'') ca -> f'' ca) f' c

class HFunctor h => HBind h where
  hbind :: h a t -> (a t -> h b t) -> h b t
class HBind h => HMonad h where
  hreturn :: a t -> h a t
class HPure h where
  hpure :: v t -> h v t
class HFold h where
  hfoldr :: (forall t' . f t' -> r -> r) -> r -> h f t -> r

data Bounds t = Bounds
  {  _lower :: t
  ,  _upper :: t
  }
  deriving Show
makeLenses ''Bounds

newtype Selector = Selector { runSelector :: forall a. Bounds a -> a }
selectU :: Selector
selectU = Selector _upper
selectL :: Selector
selectL = Selector _lower

instance Functor Bounds where
  fmap f (Bounds a b) = Bounds (f a) (f b)
instance Applicative Bounds where
  pure a = Bounds a a
  (<*>) (Bounds f1 f2) (Bounds a b) = Bounds (f1 a) (f2 b)
instance Monad Bounds where
  (>>=) (Bounds a b) f = Bounds (_lower $ f a) (_upper $ f b)

sequenceMBounds :: Bounds (Maybe a) -> Maybe (Bounds a)
sequenceMBounds (Bounds ma mb) = case (ma, mb) of
  (Just a, Just b) -> Just (Bounds a b)
  _                -> Nothing

boundsToMaybe :: Maybe (Bounds a) -> Bounds (Maybe a)
boundsToMaybe Nothing          = Bounds Nothing Nothing
boundsToMaybe (Just (Bounds a b)) = Bounds (Just a) (Just b)


newtype HBounds c t = HBounds {runHBounds ::  Bounds (c t)}
  deriving (Functor, Show)
boundWrap :: c t -> c t -> HBounds c t
boundWrap a b = HBounds $ Bounds a b

instance HFunctor HBounds where
  hfmap f (HBounds (Bounds a b)) = HBounds (Bounds (f a) (f b))
instance HZip HBounds where
  hzipWith f (HBounds b1) (HBounds b2) = HBounds $ f <$> b1 <*> b2
instance HBizip HBounds where
  hbizipWith lf uf (HBounds (Bounds lb1 ub1)) (HBounds (Bounds lb2 ub2)) = HBounds $ Bounds (lf lb1 lb2) (uf ub1 ub2)

distribute :: Functor f => f (a, b) -> (f a, f b)
distribute fab = (fmap fst fab, fmap snd fab)

undistribute :: Applicative f => (f a, f b) -> f (a, b)
undistribute (fa, fb) = (,) <$> fa <*> fb

data HPair a b t = HPair { fstw :: a t, sndw :: b t }
toPair :: HPair a b t -> (a t, b t)
toPair (HPair a b) = (a, b)

data HQuad a b c d t = HQuad (a t) (b t) (c t) (d t)

newtype Tag a t = Tag { unTag :: a }
  deriving (Functor, Show)

class HRetag a where
  hretag :: a t -> a t'

retag :: Tag a t -> Tag a t'
retag (Tag x) = Tag x

instance HFunctor TupR where
  hfmap = mapTupR
instance HFunctor TupR => HZip TupR where
  hzipWith f (TupRsingle a) (TupRsingle b) = TupRsingle (f a b)
  hzipWith f (TupRpair a b) (TupRpair x y) = TupRpair (hzipWith f a x) (hzipWith f b y)
  hzipWith _ TupRunit TupRunit = TupRunit
  hzipWith _ _ _ = error "attempted to zip unmatching tuples"

instance HFold TupR where
  hfoldr _ z TupRunit          = z
  hfoldr f z (TupRsingle x)    = f x z
  hfoldr f z (TupRpair l r)    =
    hfoldr f (hfoldr f z r) l

data HList v t where
    HEmpty :: HList v ()
    HCons  :: v t -> HList v ts -> HList v (ts, t)

data PrefixHList v t where
    PEmpty :: PrefixHList v ts
    PCons  :: v t -> PrefixHList v ts -> PrefixHList v (ts, t)
instance HFunctor PrefixHList where
    hfmap _ PEmpty = PEmpty
    hfmap f (PCons x xs) = PCons (f x) (hfmap f xs)

indexPrefixHList :: Idx env t -> PrefixHList v env -> Maybe (v t)
indexPrefixHList ZeroIdx       (PCons c _)  = Just c
indexPrefixHList (SuccIdx idx) (PCons _ cs) = indexPrefixHList idx cs
indexPrefixHList _              PEmpty      = Nothing

class StrengthenL a where
  strengthenL  :: LeftHandSide s v env env' -> a env' t -> HMaybe (a env) t

newtype HMaybe a t = HMaybe { runHMaybe :: Maybe (a t) }
  deriving Show
instance HFunctor HMaybe where
  hfmap f (HMaybe m) = HMaybe $ f <$> m
instance HZip HMaybe where
  hzipWith f (HMaybe m1) (HMaybe m2) = HMaybe $ f <$> m1 <*> m2
instance HPure HMaybe where
  hpure = HMaybe . pure

hjust :: a t -> HMaybe a t
hjust = HMaybe . Just

hnothing :: HMaybe a t
hnothing = HMaybe Nothing

hmaybe :: b t -> (a t -> b t) -> HMaybe a t -> b t
hmaybe def f (HMaybe m) = maybe def f m

instance HBind HMaybe where
  hbind (HMaybe a) f = case f <$> a of
    Nothing -> HMaybe Nothing
    (Just m) -> m
instance HMonad HMaybe where
  hreturn x = HMaybe $ Just x

oneParamFunc :: PreOpenFun (ArrayInstr benv) env (a -> b) -> BCBodyDict b
oneParamFunc (Lam _ (Body body)) | BCBodyDict <- isBody body = BCBodyDict
oneParamFunc _ = error "wrong number of parameters in function"

twoParamFunc :: PreOpenFun (ArrayInstr benv) env (a -> b -> c) -> BCBodyDict c
twoParamFunc (Lam _ (Lam _ (Body body))) |BCBodyDict <- isBody body = BCBodyDict
twoParamFunc _ = error "wrong number of parameters in function"

oneParamAfunc :: PreOpenAfun op benv (a -> b) -> BCBodyDict b
oneParamAfunc (Alam _ (Abody body)) | BCBodyDict <- isBody body = BCBodyDict
oneParamAfunc _ = error "wrong number of parameters in function"

twoParamAfunc :: PreOpenAfun op benv (a -> b -> c) -> BCBodyDict c
twoParamAfunc (Alam _ (Alam _ (Abody body))) | BCBodyDict<- isBody body = BCBodyDict
twoParamAfunc _ = error "wrong number of parameters in function"

mapXor :: Ord k => Map.Map k a -> Map.Map k a -> Map.Map k a
mapXor m1 m2 =
    let commonKeys = Map.intersection m1 m2
        onlyInM1   = Map.difference m1 commonKeys
        onlyInM2   = Map.difference m2 commonKeys
    in Map.union onlyInM1 onlyInM2