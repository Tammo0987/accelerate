{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.Optimize.Pi where
import Data.Array.Accelerate.Trafo.Exp.Bounds.BCState
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Representation.Type
import Control.Monad.State
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.IG
import qualified Data.Map as Map
import Data.Array.Accelerate.Trafo.LiveVars (expectJust)
import Prelude hiding (pi)
import Lens.Micro
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAEnv
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx

-- === Pi Assignment Wrapper ===
type Persistent = Bool

putPiAssignment :: Bool -> ControlConstraint PrimBool -> BCState s op prev (PutByType s benv () env) ()
putPiAssignment branch ctrl = do
  a <- get
  case a ^. level of
    STypeGround -> do
      let env = a ^. essaEnvs . essaEnvArr
          controlMaps   = unwrapBCConstraint ctrl
          controlBranch = if branch then cTrue <$> controlMaps else cFalse <$> controlMaps
          assignResult  = assignNewIdxs <$> (a ^. currentESSAIdx) <*> controlBranch
          insertCResult = insertC <$> fmap reMap assignResult
                                                <*> a ^. ig
          env'          = remapEnv (fmap rePairs assignResult) env
          insertDResult = foldr
                            (\(old, new) g -> insertD new (fromESSA old) g)
                            <$> insertCResult
                            <*> fmap rePairs assignResult

      put $ a & currentESSAIdx .~ (reIdx <$> assignResult)
              & ig .~ insertDResult
              & essaEnvs . essaEnvArr .~ env'
    STypeScalar -> do
      let envExp = a ^. essaEnvs . essaEnvExp
          envArr = a ^. essaEnvs . essaEnvArr
          controlMaps   = unwrapBCConstraint ctrl
          controlBranch = if branch then cTrue <$> controlMaps else cFalse <$> controlMaps
          assignResult  = assignNewIdxs <$> (a ^. currentESSAIdx) <*> controlBranch
          insertCResult = insertC <$> fmap reMap assignResult
                                                <*> a ^. ig
          envExp'       = remapEnv (fmap rePairs assignResult) envExp
          envArr'       = remapEnv (fmap rePairs assignResult) envArr
          insertDResult = foldr
                            (\(old, new) g -> insertD new (fromESSA old) g)
                            <$> insertCResult
                            <*> fmap rePairs assignResult

      put $ a & currentESSAIdx .~ (reIdx <$> assignResult)
              & ig                    .~ insertDResult
              & essaEnvs . essaEnvExp .~ envExp'
              & essaEnvs . essaEnvArr .~ envArr'

withPi :: forall instr op env t ts t' prev benv s.
  Bool
  -> (instr op env t
       -> BCState s op prev (PutByType s benv () env)
            (instr op env t, AnalysisResult t' ts))
  -> instr op env t
  -> ControlConstraints PrimBool
  -> BCState s op prev (PutByType s benv () env) (instr op env t, AnalysisResult t' ts)
withPi = withPi' @env @benv False

withPiPersist :: forall instr op env t ts t' prev benv s.
  Bool
  -> (instr op env t
       -> BCState s op prev (PutByType s benv () env)
            (instr op env t, AnalysisResult t' ts))
  -> instr op env t
  -> ControlConstraints PrimBool
  -> BCState s op prev (PutByType s benv () env) (instr op env t, AnalysisResult t' ts)
withPiPersist = withPi' @env @benv True

withPi' :: forall env benv instr op t ts t' prev s.
  Persistent
  -> Bool
  -> (instr op env t
       -> BCState s op prev (PutByType s benv () env)
            (instr op env t, AnalysisResult t' ts))
  -> instr op env t
  -> ControlConstraints PrimBool
  -> BCState s op prev (PutByType s benv () env) (instr op env t, AnalysisResult t' ts)
withPi' persist branch f instr (TupRsingle ctrl) = do
  analysis <- get
  case analysis ^. level of
    -- === Arr Level ===
    STypeGround -> do
      let envs = analysis ^. essaEnvs
      _ <- putPiAssignment branch ctrl
      (instr', ar) <- f instr
      unless persist $ modify $ \st -> st & essaEnvs .~ envs
      return (instr', ar)

    -- === Exp Level ===
    STypeScalar -> do
      let envs = analysis ^. essaEnvs
      _ <- putPiAssignment branch ctrl
      (instr', ar) <- f instr
      unless persist $ modify $ \st -> st & essaEnvs .~ envs
      return (instr', ar)

-- Takes the value to start relabeling from and a mapping of indices to their constraints
-- Returns the map with new indices, a list pairing old and new indices, and the max assigned index
assignNewIdxs :: Int -> ControlMap t -> AssignResult t
assignNewIdxs firstIdx m =
     let k  = Map.keys m
         k' = zipWith (\idx@(ESSAIdx tp _) newI -> (idx, ESSAIdx tp newI)) k [firstIdx + 1..]
         newMap = foldr (\(old, new) m'-> Map.insert new (expectJust $ Map.lookup old m) m') Map.empty k'
         newIdx = case k' of
            [] -> firstIdx
            _  -> essaInt $ snd $ last k'
     in AssignResult newMap k' newIdx

data AssignResult t = AssignResult
  { reMap   :: ControlMap t
  , rePairs :: [(ESSAIdx t, ESSAIdx t)]
  , reIdx   :: Int
  }
  deriving Show
