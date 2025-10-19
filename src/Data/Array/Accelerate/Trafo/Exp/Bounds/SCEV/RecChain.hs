{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use bimap" #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.RecChain where
import Data.Array.Accelerate.Representation.Type
import Lens.Micro.TH
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx
import Data.Kind
import Data.Array.Accelerate.AST.LeftHandSide

data ChainOp = Mult | Add | Delay
  deriving Eq

instance Show ChainOp where
  show Mult  = "*"
  show Add   = "+"
  show Delay = "#" 

instance Ord ChainOp where
  compare a b = compare (rank a) (rank b)
    where
      rank :: ChainOp -> Int
      rank Delay = 0
      rank Add   = 1
      rank Mult  = 2

instance Eq (ExistsOp SChainOp) where
  (ExistsOp SDelay) == (ExistsOp SDelay) = True
  (ExistsOp SAdd)   == (ExistsOp SAdd)   = True
  (ExistsOp SMult)  == (ExistsOp SMult)  = True
  _                 == _                 = False

instance Ord (ExistsOp SChainOp) where
  compare (ExistsOp a) (ExistsOp b) = compare (rank a) (rank b)
    where
      rank :: SChainOp op -> Int
      rank SDelay = 0
      rank SAdd   = 1
      rank SMult  = 2

data ExistsOp (f :: ChainOp -> Type) where
  ExistsOp :: f op -> ExistsOp f

data SChainOp (op :: ChainOp) where
    SMult  :: SChainOp 'Mult
    SAdd   :: SChainOp 'Add
    SDelay :: SChainOp 'Delay

data RecChain ops v t where
    BaseRecChain :: v t -> RecChain '[] v t
    ConsRecChain :: forall v t (op :: ChainOp) (ops :: [ChainOp])
                 . v t -> SChainOp op -> RecChain ops v t -> RecChain (op : ops) v t
data SCEVChain t where
  SCEVChain :: RecChain ops (BasicDiff ESSAIdx) t -> SCEVChain t

instance Show (SCEVChain t) where
  show (SCEVChain r) = show r

instance (Show (v t)) => Show (RecChain ops v t) where
  show (ConsRecChain v _ rest) = "{" ++ show v ++ ",o," ++ show rest
  show (BaseRecChain a) = show a ++ "}"

instance HFunctor (RecChain ops) where
  hfmap :: (forall a. f a -> g a) -> RecChain ops f t -> RecChain ops g t
  hfmap nat (BaseRecChain x) = BaseRecChain (nat x)
  hfmap nat (ConsRecChain x op xs) = ConsRecChain (nat x) op (hfmap nat xs)
instance HZip (RecChain ops) where
  hzipWith f (BaseRecChain c1) (BaseRecChain c2) = BaseRecChain (f c1 c2)
  hzipWith f (ConsRecChain c1 op1 cs1) (ConsRecChain c2 _ cs2) = ConsRecChain (f c1 c2) op1 (hzipWith f cs1 cs2)

type ClosedFormConstraint  t = BCConstraint (HMaybe (BasicDiff ESSAIdx)) t
type ClosedFormConstraints t = TupR (BCConstraint (HMaybe (BasicDiff ESSAIdx))) t

closedToData :: ClosedFormConstraint t -> DataConstraint t
closedToData = hfmap (hfmap Diff)

data SCEVExp t where
  SCEVVar   :: ESSAIdx t              -> SCEVExp t
  SCEVInvar :: BasicDiff    ESSAIdx t -> SCEVExp t
  SCEVOp    :: ChainOp  -> SCEVExp t -> SCEVExp t -> SCEVExp t
  SCEVPhi   :: SCEVExp t -> SCEVExp t -> SCEVExp t

instance Show (SCEVExp t) where
  show (SCEVVar e) = "V." ++ show e
  show (SCEVInvar b) = "I." ++ show b
  show (SCEVOp op a b) = show a ++ show op ++ show b
  show (SCEVPhi a b) = "phi" ++ "(" ++ show a ++ "," ++ show b ++ ")"

instance FromConst SCEVExp where
  fromConst = SCEVInvar . fromConst

instance Empty SCEVExp where
  empty = SCEVInvar $ fromConst (0 :: Int)

type TripCount = Bounds (Exists (HMaybe (BasicDiff ESSAIdx)))

type SCEVConstraint  t = BCConstraint (HMaybe SCEVExp) t
type SCEVConstraints t = TupR (BCConstraint (HMaybe SCEVExp)) t

type SCEVChainConstraint  t = BCConstraint (HMaybe SCEVChain) t
type SCEVChainConstraints t = TupR (BCConstraint (HMaybe SCEVChain)) t

-- === SCEV Analysis Result Format ===
data RSCEV t ts = RSCEV
  {  _rSCEVExp     :: SCEVConstraints t
  ,  _rArgIdxs    :: TupR (BCConstraint (HMaybe ESSAIdx)) ts
  }
makeLenses ''RSCEV

type family AlignResult ops1 ops2 where
  AlignResult (Mult :os1) (Mult :os2) = (Mult :AlignResult os1 os2)
  AlignResult (Add  :os1) (Add  :os2) = (Add  :AlignResult os1 os2)
  AlignResult (Delay:os1) (Delay:os2) = (Delay:AlignResult os1 os2)
  AlignResult (Mult :os1) (Add  :os2) =  Add  :AlignResult (Mult :os1) os2
  AlignResult (Add  :os1) (Mult :os2) =  Add  :AlignResult os1 (Mult :os2)
  AlignResult (Delay:os1) (op   :os2) =  Delay:AlignResult os1 (op :os2)
  AlignResult (op   :os1) (Delay:os2) =  Delay:AlignResult (op :os1) os2
  AlignResult '[] (op :os2) = op : AlignResult '[] os2
  AlignResult (op :os1) '[] = op : AlignResult os1 '[]
  AlignResult '[] '[] = '[]

alignCR :: (forall a . Int -> v a) -> RecChain ops v t -> RecChain ops' v t' -> (RecChain (AlignResult ops ops') v t, RecChain (AlignResult ops ops') v t')
alignCR f (ConsRecChain x SMult  cs1) (ConsRecChain y SMult  cs2) = let (rc1, rc2) = alignCR f cs1 cs2 in (ConsRecChain x SMult  rc1, ConsRecChain y SMult  rc2)
alignCR f (ConsRecChain x SAdd   cs1) (ConsRecChain y SAdd   cs2) = let (rc1, rc2) = alignCR f cs1 cs2 in (ConsRecChain x SAdd   rc1, ConsRecChain y SAdd   rc2)
alignCR f (ConsRecChain x SDelay cs1) (ConsRecChain y SDelay cs2) = let (rc1, rc2) = alignCR f cs1 cs2 in (ConsRecChain x SDelay rc1, ConsRecChain y SDelay rc2)

alignCR f (ConsRecChain x SAdd cs1) c2@(ConsRecChain _ SMult _)   = let (rc1, rc2) = alignCR f cs1 c2 in (ConsRecChain x SAdd rc1, ConsRecChain (f 0) SAdd rc2)
alignCR f c1@(ConsRecChain _ SMult _) (ConsRecChain y SAdd cs2)   = let (rc1, rc2) = alignCR f c1 cs2 in (ConsRecChain (f 0) SAdd rc1, ConsRecChain y SAdd rc2)

alignCR f (ConsRecChain x SDelay cs1) c2@(ConsRecChain y SAdd _)  = let (rc1, rc2) = alignCR f cs1 c2 in (ConsRecChain x SDelay rc1, ConsRecChain y SDelay rc2)
alignCR f (ConsRecChain x SDelay cs1) c2@(ConsRecChain y SMult _) = let (rc1, rc2) = alignCR f cs1 c2 in (ConsRecChain x SDelay rc1, ConsRecChain y SDelay rc2)
alignCR f c1@(ConsRecChain x SAdd _) (ConsRecChain y SDelay cs2)  = let (rc1, rc2) = alignCR f c1 cs2 in (ConsRecChain x SDelay rc1, ConsRecChain y SDelay rc2)
alignCR f c1@(ConsRecChain x SMult _) (ConsRecChain y SDelay cs2) = let (rc1, rc2) = alignCR f c1 cs2 in (ConsRecChain x SDelay rc1, ConsRecChain y SDelay rc2)

alignCR f c1@(BaseRecChain _) (ConsRecChain y SMult cs)  = let (rc1, rc2) = alignCR f c1 cs in (ConsRecChain (f 1) SMult rc1, ConsRecChain y SMult rc2)
alignCR f (ConsRecChain x SMult cs) c2@(BaseRecChain _)  = let (rc1, rc2) = alignCR f cs c2 in (ConsRecChain x SMult rc1, ConsRecChain (f 1) SMult rc2)

alignCR f c1@(BaseRecChain _) (ConsRecChain y SAdd cs)   = let (rc1, rc2) = alignCR f c1 cs in (ConsRecChain (f 0) SAdd rc1, ConsRecChain y SAdd rc2)
alignCR f (ConsRecChain x SAdd cs) c2@(BaseRecChain _)   = let (rc1, rc2) = alignCR f cs c2 in (ConsRecChain x SAdd rc1, ConsRecChain (f 0) SAdd rc2)

alignCR f c1@(BaseRecChain x) (ConsRecChain y SDelay cs) = let (rc1, rc2) = alignCR f c1 cs in (ConsRecChain x SDelay rc1, ConsRecChain y SDelay rc2)
alignCR f (ConsRecChain x SDelay cs) c2@(BaseRecChain y) = let (rc1, rc2) = alignCR f cs c2 in (ConsRecChain x SDelay rc1, ConsRecChain y SDelay rc2)

alignCR _ c1@(BaseRecChain _) c2@(BaseRecChain _) = (c1, c2)

