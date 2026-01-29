{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Analysis.Hash.Exp
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Analysis.Hash.Schedule.Uniform (
  hashUniformScheduleFun
) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.AST.Operation (encodeGroundR)
import Data.Array.Accelerate.Analysis.Hash.TH
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Analysis.Hash.Operation (encodePreArgs)
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Primitive.Vec

import Crypto.Hash.XKCP
import Data.ByteString.Builder
import Data.ByteString.Builder.Extra
import Data.ByteString.Short.Internal                               ( ShortByteString(..) )
import Data.Monoid

hashUniformScheduleFun :: IsKernel kernel => UniformScheduleFun kernel env f -> Hash
hashUniformScheduleFun = hashlazy . toLazyByteString . encodeUniformScheduleFun

encodeUniformScheduleFun :: IsKernel kernel => UniformScheduleFun kernel env f -> Builder
encodeUniformScheduleFun (Slam lhs f) = intHost $(hashQ "Slam") <> encodeBLeftHandSide lhs <> encodeUniformScheduleFun f
encodeUniformScheduleFun (Sbody body) = intHost $(hashQ "Sbody") <> encodeUniformSchedule body

encodeUniformSchedule :: IsKernel kernel => UniformSchedule kernel env -> Builder
encodeUniformSchedule Return = intHost $(hashQ "Return")
encodeUniformSchedule (Alet lhs bnd next)
  = intHost $(hashQ "Alet")
  <> encodeBLeftHandSide lhs
  <> encodeBinding bnd
  <> encodeUniformSchedule next
encodeUniformSchedule (Effect effect next)
  = intHost $(hashQ "Effect")
  <> encodeEffect effect
  <> encodeUniformSchedule next
encodeUniformSchedule (Acond (Var _ idx) true false next)
  = intHost $(hashQ "Acond")
  <> encodeIdx idx
  <> encodeUniformSchedule true
  <> encodeUniformSchedule false
  <> encodeUniformSchedule next
encodeUniformSchedule (Awhile io fn initial next)
  = intHost $(hashQ "Awhile")
  <> encodeIO io
  <> encodeUniformScheduleFun fn
  <> encodeTupR (\(Var _ idx) -> encodeIdx idx) initial
  <> encodeUniformSchedule next
encodeUniformSchedule (AwhileSeq io fn initial next)
  = intHost $(hashQ "AwhileSeq")
  <> encodeIO io
  <> encodeUniformScheduleFun fn
  <> encodeTupR (\(Var _ idx) -> encodeIdx idx) initial
  <> encodeUniformSchedule next
encodeUniformSchedule (Spawn a b)
  = intHost $(hashQ "Spawn")
  <> encodeUniformSchedule a
  <> encodeUniformSchedule b

encodeBLeftHandSide :: BLeftHandSide t env env' -> Builder
encodeBLeftHandSide = encodeLeftHandSide encodeBaseR

encodeBaseR :: BaseR t -> Builder
encodeBaseR (BaseRground tp)    = intHost $(hashQ "Ground") <> encodeGroundR tp
encodeBaseR BaseRsignal         = intHost $(hashQ "Signal")
encodeBaseR BaseRsignalResolver = intHost $(hashQ "SignalResolver")
encodeBaseR (BaseRref tp)       = intHost $(hashQ "Ref") <> encodeGroundR tp
encodeBaseR (BaseRrefWrite tp)  = intHost $(hashQ "RefWrite") <> encodeGroundR tp

encodeBasesR :: BasesR t -> Builder
encodeBasesR = encodeTupR encodeBaseR

encodeBinding :: Binding env t -> Builder
encodeBinding = \case
  Compute expr -> intHost $(hashQ "Compute") <> encodeOpenExp expr
  NewSignal _ -> intHost $(hashQ "NewSignal")
  NewRef tp -> intHost $(hashQ "NewRef") <> encodeGroundR tp
  Alloc shr tp sh ->
    intHost $(hashQ "Alloc")
    <> encodeShapeR shr
    <> encodeScalarType tp
    <> encodeTupR (\(Var _ idx) -> encodeIdx idx) sh
  -- Buffer is passed indirectly, via %imports_t in accelerate-llvm-native,
  -- so the buffer/pointer does not need to included in the hashing.
  Use tp _ _ -> intHost $(hashQ "Use") <> encodeScalarType tp
  Unit (Var tp idx) -> intHost $(hashQ "Unit") <> encodeScalarType tp <> encodeIdx idx
  RefRead (Var _ idx) -> intHost $(hashQ "RefRead") <> encodeIdx idx

encodeEffect :: IsKernel kernel => Effect kernel env -> Builder
encodeEffect = \case
  Exec _ kernel args -> encodeKernelFun kernel <> encodePreArgs encodeSArg args
  SignalAwait indices ->
    intHost $(hashQ "SignalAwait")
    <> intHost (length indices)
    <> mconcat (map encodeIdx indices)
  SignalResolve indices ->
    intHost $(hashQ "SignalResolve")
    <> intHost (length indices)
    <> mconcat (map encodeIdx indices)
  RefWrite (Var _ ref) (Var _ var) ->
    intHost $(hashQ "RefWrite")
    <> encodeIdx ref
    <> encodeIdx var
  Aassert cond ->
    intHost $(hashQ "Aassert")
    <> encodeOpenExp cond

encodeIO :: InputOutputR input output -> Builder
encodeIO = \case
  InputOutputRsignal   -> intHost $(hashQ "signal")
  InputOutputRref tp   -> intHost $(hashQ "ref") <> encodeGroundR tp
  InputOutputRpair a b -> intHost $(hashQ "pair") <> encodeIO a <> encodeIO b
  InputOutputRunit     -> intHost $(hashQ "unit")

encodeSArg :: SArg env t -> Builder
encodeSArg (SArgScalar (Var tp idx)) =
  intHost $(hashQ "SArgScalar")
  <> encodeScalarType tp
  <> encodeIdx idx
encodeSArg (SArgBuffer m (Var tp idx)) =
  intHost $(hashQ "SArgBuffer")
  <> m'
  <> encodeGroundR tp
  <> encodeIdx idx
  where
    m' = case m of
      In  -> intHost $(hashQ "In")
      Out -> intHost $(hashQ "Out")
      Mut -> intHost $(hashQ "Mut")

encodeKernelFun :: IsKernel kernel => OpenKernelFun kernel env t -> Builder
-- Argument types are encoded via encodeSArg
encodeKernelFun (KernelFunLam _ f) = encodeKernelFun f
encodeKernelFun (KernelFunBody kernel) = case encodeKernel kernel of
  Left (SHA3_256 ba#) -> shortByteString (SBS ba#)
  Right builder -> builder
