{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# LANGUAGE LambdaCase #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.Optimize.ArrayInstr where
import Data.Array.Accelerate.AST.Operation
import Prelude hiding (snd, fst, init, exp)
import Control.Monad.State hiding (guard)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Array (ArrayR (ArrayR))
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Data.Array.Accelerate.Trafo.Exp.Bounds.ArrayInstr
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAEnv
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints
import Data.Array.Accelerate.Trafo.Exp.Bounds.BCState
import Data.Array.Accelerate.Trafo.Exp.Bounds.Optimize.Exp
import Lens.Micro
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.ConstraintArgs
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.RecChain
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.IG (basicDiffToConst)
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.LoopStack

-- Function to check if an array always has at least n elements on the outter-most dimensions.
-- Used to only persist assertion information outside algorithmic skeletons if they are executed at least once 
outterDimAtLeast :: Int -> ShapeR sh -> GroundVars benv sh -> BCState s op prev '(benv, env) Bool
outterDimAtLeast _ ShapeRz _ = return True
outterDimAtLeast n (ShapeRsnoc sh) (TupRpair gr' (TupRsingle gr)) = do
    a <- get
    let env = a ^. essaEnvs . essaEnvArr
        g   = _lower $ a ^. ig
        bSh = varToClosedForm env gr
        (HMaybe lowSh) = _lower $ unwrapBCConstraint bSh
        res = do 
            lowSh' <- lowSh
            cnstSh <- basicDiffToConst g lowSh'
            return (cnstSh >= n)
    -- reccurent case checks if the levels below are non-zero
    recRes <- outterDimAtLeast 1 sh gr'
    return $ maybe False (recRes &&) res
outterDimAtLeast _ _ _ = error "mismatched TupR"

isNotEmpty :: ShapeR sh -> GroundVars benv sh -> BCState s op prev '(benv, env) Bool
isNotEmpty = outterDimAtLeast 1

defaultBCMap
    :: (forall sh' s' t'.  op (Fun' (s' -> t') -> In sh' s'-> Out sh' t' -> ()))
    -> AbstInterpOperation op (Fun' (s  -> t ) -> In sh  s -> Out sh  t  -> ())
defaultBCMap mkMap = AbstInterpOperation $ 
  \(ArgFun f :>: input@(ArgArray _ (ArrayR shr itp) sh input') :>: output@(ArgArray _ (ArrayR _ otp) _ output') :>: ArgsNil) -> case f of
      _ | BCBodyDict <- oneParamFunc f, BCScalarDict <- reprBCScalar itp, BCScalarDict <- reprBCScalar otp -> do
        a <- get
        let env = a ^. essaEnvs . essaEnvArr
            -- iInput = bccsToScalar itp $ hfmap (varToESSA env) input'
            st  = a ^. stack
            -- unlift array constraints to point-wise argument
            dInput = bccsToScalar itp $ hfmap (varToDataConstraint    env) input'
            cInput = bccsToScalar itp $ hfmap (varToControlConstraint env) input'
            sInput = bccsToScalar itp $ hfmap (varToSCEVConstraint st env) input'
        let comp = optimizeBoundsFun' (diffArg1 $ NewBindArg dInput cInput sInput) f
        
        -- TODO: use the same index as the array to capture collective assertion. attempted, but buggy
        -- let comp = optimizeBoundsFun' (diffArg1 $ NewBindArg (hfmap (hfmap hjust) iInput)) f
            ((f', rOut), a') = runState comp (enterExpScope a)
            -- output array is constrained by the point-wise result
            iOut = hfmap (varToESSA env) output'
        put $ popLoopScope a' 
        let args' = ArgFun f' :>: input :>: output :>: ArgsNil

        -- check if assertion information can persist outside
        runs <- isNotEmpty shr sh
        unless runs $ modify $ \s -> s & essaEnvs .~ (a ^. essaEnvs) -- revert to initial state environments

        return (BCOptOperation mkMap args', iOut, output', mkArrayFuncRes otp rOut, True)

defaultBCBackpermute
    :: (forall sh1' sh2' t'. op (Fun' (sh2' -> sh1') -> In sh1' t' -> Out sh2' t' -> ()))
    -> AbstInterpOperation op (Fun' (sh2 -> sh1) -> In sh1 t -> Out sh2 t -> ())
defaultBCBackpermute mkBackpermute = AbstInterpOperation $
    \(ArgFun f :>: input@(ArgArray _ (ArrayR _ itp) _ input') :>: output@(ArgArray _ (ArrayR shr _) sh output') :>: ArgsNil) -> case f of
      _ | BCBodyDict <- oneParamFunc f, BCScalarDict <- reprBCScalar itp -> do
        a <- get
        let env = a ^. essaEnvs . essaEnvArr
            iSh = hfmap (varToESSA env) sh

            -- the iterator is between [0,size-1]
            dSh = hfmap (\i -> bccBind i (\i' -> bccPut (toCGType i) $ Bounds (hjust $ Diff $ fromConst (0 :: Int)) (hpure (Diff $ BDiff (Just i') (-1))))) iSh
            cSh = bccsEmpty sh
            sSh = bccsEmpty sh

        let comp = do optimizeBoundsFun' (diffArg1 $ NewBindArg dSh cSh sSh) f
            ((f', _), a') = runState comp (enterExpScope a)
            args' = ArgFun f' :>: input :>: output :>: ArgsNil
        put $ popLoopScope a'

        -- input constraints flow to output, as its only source
        let iOut = hfmap (varToESSA env) output'
            dOut = bccsToScalar itp $ hfmap (varToDataConstraint    env) input'
            cOut = bccsToScalar itp $ bccsEmpty input'
            sOut = bccsToScalar itp $ bccsEmpty input'
            rOut = analysisResult dOut cOut sOut

        -- check if assertion information can persist outside
        runs <- isNotEmpty shr sh
        unless runs $ modify $ \st -> st & essaEnvs .~ (a ^. essaEnvs) -- revert to initial state environments

        return (BCOptOperation mkBackpermute args', iOut, output', mkArrayFuncRes itp rOut, True)

defaultBCGenerate
    :: (forall sh' t'. op (Fun' (sh' -> t') -> Out sh' t' -> ()))
    -> AbstInterpOperation op (Fun' (sh -> t) -> Out sh t -> ())
defaultBCGenerate mkGenerate = AbstInterpOperation $
    \(ArgFun f :>: output@(ArgArray _ (ArrayR shr tp) sh output') :>: ArgsNil) -> case f of
      _ | BCBodyDict <- oneParamFunc f, BCScalarDict <- reprBCScalar tp -> do
        a <- get
        let env = a ^. essaEnvs . essaEnvArr
            iSh = hfmap (varToESSA env) sh
            -- the iterator is between [0,size-1]
            dIx = hfmap (\i -> bccBind i (\i' -> bccPut (toCGType i) $ Bounds (hjust $ Diff $ fromConst (0 :: Int)) (hpure (Diff $ BDiff (Just i') (-1))))) iSh
            cIx = bccsEmpty sh
            sIx = bccsEmpty sh

        -- rOut, the pointwise result is associated to output
        let comp = do optimizeBoundsFun' (diffArg1 $ NewBindArg dIx cIx sIx) f
            ((f', rOut), a') = runState comp (enterExpScope a)
        put $ popLoopScope a'
        let args' = ArgFun f' :>: output :>: ArgsNil
            iOut = hfmap (varToESSA env) output'

        -- check if assertion information can persist outside
        runs <- isNotEmpty shr sh
        unless runs $ modify $ \st -> st & essaEnvs .~ (a ^. essaEnvs) -- revert to initial state environments

        return (BCOptOperation mkGenerate args', iOut, output', mkArrayFuncRes tp rOut, False)

getInputArray :: TupR a (tag, ((), (t1, t2))) -> TupR a t2
getInputArray (TupRpair _ (TupRpair _ (TupRpair _ a))) = a
getInputArray _ = error "malformed primMaybe"

defaultBCPermute
  :: (forall sh1 e1. op (Fun' (e1 -> e1 -> e1) -> Mut sh1 e1 -> In sh (PrimMaybe (sh1, e1)) -> ()))
  -> AbstInterpOperation op (Fun' (e -> e -> e) -> Mut sh' e -> In sh (PrimMaybe (sh', e)) -> ())
defaultBCPermute mkPermute = AbstInterpOperation $ \case
    (ArgFun f :>: def@(ArgArray _ (ArrayR _ dtp) _ def') :>: input@(ArgArray _ (ArrayR (ShapeRsnoc _) mItp) (TupRpair _ (TupRsingle sh)) mInput') :>: ArgsNil) -> case f of
        _ | BCBodyDict <- twoParamFunc f, BCScalarDict <- reprBCScalar dtp, BCScalarDict <- reprBCScalar mItp -> do
            a <- get
            let env = a ^. essaEnvs . essaEnvArr

            let itp    = getInputArray mItp
                input' = getInputArray mInput'

            -- incoming elements are invariant, sourced from the input
            let dInput = bccsToScalar itp $ hfmap (varToDataConstraint    env) input'
                cInput = bccsToScalar itp $ bccsEmpty input'
            sInput <- mkInvarVars dInput

            -- first element that replaces default becomes a loop-variant accumulator
            let dAcc = bccsToScalar dtp $ hfmap (varToDataConstraint    env) input'
                cAcc = bccsToScalar dtp $ bccsEmpty input'

            -- Default array data constraints
                dDef         = bccsToScalar itp $ hfmap (varToDataConstraint    env) def'
            (sAcc, iAcc) <- mkInductionVars dAcc

            a' <- get
            let args = diffArg2 (NewBindArg dInput cInput sInput) (NewBindArg dAcc cAcc sAcc)
                ((f', rOut), aOut) = runState (optimizeBoundsFun' args f) (enterExpScope a')
            put $ popLoopScope aOut

            a'' <- get
            let inputSize = varToDataConstraint env sh
            -- first element set the accumulator, so there are [0,size-1] elements still to come
            let inputSpan' = interpretData (a'' ^. ig) interpretPrimAdd inputSize (bccPut (toCGType inputSize) $ pure $ fromConst (-1 :: Int))
            let inputSpan = bccPutInLower inputSpan' (fromConst (0 :: Int))
            dInputSpan <- dataToBasic inputSpan
            let tripCount = Exists <$> unwrapBCConstraint dInputSpan

            
            let chains       = hzipWith (computeChains (a'' ^. ig)) iAcc (rOut ^. rSCEV . rSCEVExp)
                closedForms' = hfmap (computeClosedForm (a'' ^. ig) tripCount) chains
                -- phi-join default case with replace+accumulate case
                closedForms  = phi dDef closedForms'

            let args' = ArgFun f' :>: def :>: input :>: ArgsNil
                res   = analysisResult closedForms (bccsToScalar dtp $ bccsEmpty def') (bccsToScalar dtp $ bccsEmpty def')
            
            -- it is not guaranteed that the colision function is ever called, so we must always revert
            modify $ \st -> st & essaEnvs .~ (a ^. essaEnvs) -- revert to initial state environments
            
            -- the essa-realocation of the mutable array is, however, persistent
            iOut <- traverseTupR bccReallocateMut $ hfmap (varToESSA env) def'

            return (BCOptOperation mkPermute args', iOut, def', mkArrayFuncRes dtp res, False)
    _ -> error "malformed input"

defaultBCPermuteUnique
  :: (forall sh1 e1. op (Mut sh1 e1 -> In sh (PrimMaybe (sh1, e1)) -> ()))
  -> AbstInterpOperation op (Mut sh' e -> In sh (PrimMaybe (sh', e)) -> ())
defaultBCPermuteUnique mkPermuteUnique = AbstInterpOperation $
  \(def@(ArgArray _ (ArrayR _ _) _ def') :>: input@(ArgArray _ _ _ mInput) :>: ArgsNil) -> do
      a <- get
      let env = a ^. essaEnvs . essaEnvArr
          input' = getInputArray mInput
          dDef = hfmap (varToDataConstraint env) def'  
          dInput = hfmap (varToDataConstraint env) input'
          -- either default or (uniquely) replaced
          dRes = phi dDef dInput
          cRes = bccsEmpty def'
          sRes = bccsEmpty def'
          iMut = hfmap (varToESSA env) def'
          rMut = analysisResult dRes cRes sRes
      let args' = def :>: input :>: ArgsNil
      return (BCOptOperation mkPermuteUnique args', iMut, def', rMut, False)

bccPutInLower :: BCConstraint c Int -> c Int -> BCConstraint c Int
bccPutInLower bc c =
  let u = unwrapBCConstraint bc 
      in bccPut (toCGType bc) $ Bounds c (_upper u)

defaultBCScan
  :: (forall sh' e'. op (Fun' (e' -> e' -> e') -> Exp' e' -> In (sh', Int) e' -> Out (sh', Int) e' -> ()))
  -> AbstInterpOperation op (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out (sh, Int) e -> ())
defaultBCScan mkScan = AbstInterpOperation $ \case
    (ArgFun f :>: ArgExp init :>: input@(ArgArray _ (ArrayR fullShr@(ShapeRsnoc _) itp) fullSh@(TupRpair _ (TupRsingle sh)) input') :>: output@(ArgArray _ (ArrayR _ otp) _ output') :>: ArgsNil) -> case f of
        _ | BCBodyDict <- twoParamFunc f, BCScalarDict <- reprBCScalar itp -> do
            a <- get
            let env = a ^. essaEnvs . essaEnvArr
            
            -- optimize the accumulator
            let ((init', rInit), aInit) = runState (optimizeBoundsExp init) (enterExpScope a)
            put $ popLoopScope aInit

            -- the input array is not loop variant; data and control constraints hold
            let dInput = bccsToScalar itp $ hfmap (varToDataConstraint    env) input'
                cInput = bccsToScalar itp $ hfmap (varToControlConstraint env) input'
            sInput <- mkInvarVars dInput

            -- accumulator is loop variant; data and control constraints are not consistent
            let dInit = bccsEmpty init'
                cInit = bccsEmpty init'
            -- get new ESSAIdx to indetify induction variable and make accumulator variable
            (sInit, iInit) <- mkInductionVars (rInit ^. rCS . rData)

            a' <- get    
            let args = diffArg2 (NewBindArg dInput cInput sInput) (NewBindArg dInit cInit sInit)
                ((f', rOut), aOut) = runState (optimizeBoundsFun' args f) (newLoopScope $ enterExpScope a')
            put $ popLoopScope $ popLoopScope aOut

            -- compute scev results
            a'' <- get
            -- a scan tracks the evolution from 0 to all elements folded within the accumulator
            let inputSize = varToDataConstraint env sh
            let inputSpan' = bccPutInLower inputSize (fromConst (0 :: Int))
            inputSpan <- dataToBasic inputSpan'
            let tripCount = Exists <$> unwrapBCConstraint inputSpan
                chains      = hzipWith (computeChains (a'' ^. ig)) iInit (rOut ^. rSCEV . rSCEVExp) 
                closedForms = hfmap (computeClosedForm (a'' ^. ig) tripCount) chains

            let args' = ArgFun f' :>: ArgExp init' :>: input :>: output :>: ArgsNil
                iOut  = hfmap (varToESSA env) output'
                res   = analysisResult closedForms (bccsToScalar otp $ bccsEmpty output') (bccsToScalar otp $ bccsEmpty output')

            -- check if assertion information can persist outside
            runs <- isNotEmpty fullShr fullSh
            unless runs $ modify $ \st -> st & essaEnvs .~ (a ^. essaEnvs) -- revert to initial state environments
            
            return (BCOptOperation mkScan args', iOut, output', mkArrayFuncRes itp res, False)
    _ -> error "malformed input"

defaultBCScan1
  :: (forall sh'.op (Fun' (e -> e -> e) -> In (sh', Int) e -> Out (sh', Int) e -> ()))
  -> AbstInterpOperation op (Fun' (e -> e -> e) -> In (sh, Int) e -> Out (sh, Int) e -> ())
defaultBCScan1 mkScan1 = AbstInterpOperation $ \case
    (ArgFun f :>: input@(ArgArray _ (ArrayR fullShr@(ShapeRsnoc _) itp) fullSh@(TupRpair _ (TupRsingle sh)) input') :>: output@(ArgArray _ _ _ output') :>: ArgsNil) -> case f of
        _ | BCBodyDict <- twoParamFunc f, BCScalarDict <- reprBCScalar itp -> do
            a <- get
            let env = a ^. essaEnvs . essaEnvArr

            -- the input array is not loop variant; data and control constraints hold
            let dInput = bccsToScalar itp $ hfmap (varToDataConstraint env) input'
                cInput = bccsToScalar itp $ hfmap (varToControlConstraint env) input'
            sInput <- mkInvarVars dInput

            -- accumulator is loop variant; data and control constraints are not consistent
            let dAcc = bccsToScalar itp $ bccsEmpty input'
                cAcc = bccsToScalar itp $ bccsEmpty input'
            (sAcc, iAcc) <- mkInductionVars dInput

            -- Optimize the folding function
            a' <- get
            let args = diffArg2 (NewBindArg dInput cInput sInput) (NewBindArg dAcc cAcc sAcc)
                ((f', rOut), aOut) = runState (optimizeBoundsFun' args f) (newLoopScope $ enterExpScope a')
            put $ popLoopScope $ popLoopScope aOut

            -- Compute SCEV results
            a'' <- get
            let inputSize = varToDataConstraint env sh
            -- first element was used as accumulator, so we subtract it
            let inputSpan' = interpretData (a'' ^. ig) interpretPrimAdd inputSize (bccPut (toCGType inputSize) $ pure $ fromConst (-1 :: Int))
                inputSpan = bccPutInLower inputSpan' (fromConst (0 :: Int))
            dInputSpan <- dataToBasic inputSpan
            let tripCount = Exists <$> unwrapBCConstraint dInputSpan
                chains      = hzipWith (computeChains (a'' ^. ig)) iAcc (rOut ^. rSCEV . rSCEVExp)
                closedForms = hfmap (computeClosedForm (a'' ^. ig) tripCount) chains

            let args' = ArgFun f' :>: input :>: output :>: ArgsNil
                iOut  = hfmap (varToESSA env) output'
                res   = analysisResult closedForms (bccsToScalar itp $ bccsEmpty output') (bccsToScalar itp $ bccsEmpty output')

            -- check if assertion information can persist outside
            runs <- outterDimAtLeast 2 fullShr fullSh
            unless runs $ modify $ \st -> st & essaEnvs .~ (a ^. essaEnvs) -- revert to initial state environments

            return (BCOptOperation mkScan1 args', iOut, output', mkArrayFuncRes itp res, False)
    _ -> error ""

defaultBCScan'
  :: (forall sh' e'. op (Fun' (e' -> e' -> e') -> Exp' e' -> In (sh', Int) e' -> Out (sh', Int) e' -> Out sh' e' -> ()))
  -> AbstInterpOperation op (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out (sh, Int) e -> Out sh e -> ())
defaultBCScan' mkScan' = AbstInterpOperation $ \case
    (ArgFun f :>: ArgExp init :>: input@(ArgArray _ (ArrayR fullShr@(ShapeRsnoc _) itp) fullSh@(TupRpair _ (TupRsingle sh)) input') :>: scanned@(ArgArray _ (ArrayR _ otp) _ scanned') :>: acc@(ArgArray _ (ArrayR _ rtp) _ acc') :>: ArgsNil) -> case f of
        _ | BCBodyDict <- twoParamFunc f, BCScalarDict <- reprBCScalar itp, BCScalarDict <- reprBCScalar otp -> do
                a <- get
                let env = a ^. essaEnvs . essaEnvArr
                    ((init', rInit), aInit) = runState (optimizeBoundsExp init) (enterExpScope a)
                put $ popLoopScope aInit

                -- the input array is not loop variant; data and control constraints hold
                let dInput = bccsToScalar itp $ hfmap (varToDataConstraint    env) input'
                    cInput = bccsToScalar itp $ hfmap (varToControlConstraint env) input'
                sInput <- mkInvarVars dInput

                -- accumulator is loop variant; data and control constraints are not consistent
                let dInit = bccsEmpty init'
                    cInit = bccsEmpty init'
                (sInit, iInit) <- mkInductionVars (rInit ^. rCS . rData)

                a' <- get
                let args = diffArg2 (NewBindArg dInput cInput sInput) (NewBindArg dInit cInit sInit)
                    ((f', rOut), aOut) = runState (optimizeBoundsFun' args f) (newLoopScope $ enterExpScope a')
                put $ popLoopScope $ popLoopScope aOut

                -- SCAN
                a'' <- get
                let dSize = varToDataConstraint env sh
                -- scan between 0 and inputSize-1
                let dSpan    = interpretData (a'' ^. ig) interpretPrimAdd dSize (bccPut (toCGType dSize) $ pure $ fromConst (-1 :: Int))
                    shSpan'  = bccPutInLower dSpan (fromConst (0 :: Int))
                shSpan <- dataToBasic shSpan'
                let tripCount   = Exists <$> unwrapBCConstraint shSpan
                    chains      = hzipWith (computeChains (a'' ^. ig)) iInit (rOut ^. rSCEV . rSCEVExp)
                    closedForms = hfmap (computeClosedForm (a'' ^. ig) tripCount) chains

                -- FOLD
                a''' <- get
                shSize <- dataToBasic dSize
                -- folding all elements gives the output scalar
                let tripCount' = Exists <$> unwrapBCConstraint shSize
                    closedForms' = hfmap (computeClosedForm (a''' ^. ig) tripCount') chains

                let args'   = ArgFun f' :>: ArgExp init' :>: input :>: scanned :>: acc :>: ArgsNil
                    output' = TupRpair scanned' acc'
                    iOut    = hfmap (varToESSA env) output'

                    res     = analysisResult (TupRpair closedForms closedForms') (bccsToScalar (TupRpair itp rtp) $ bccsEmpty (TupRpair scanned' acc')) (bccsToScalar (TupRpair itp rtp) $ bccsEmpty (TupRpair scanned' acc'))

                
                -- check if assertion information can persist outside
                runs <- isNotEmpty fullShr fullSh
                unless runs $ modify $ \st -> st & essaEnvs .~ (a ^. essaEnvs) -- revert to initial state environments

                return (BCOptOperation mkScan' args', iOut, output', mkArrayFuncRes (TupRpair itp rtp) res, False)
    _ -> error "malformed input"

defaultBCFold
  :: (forall sh' e'. op (Fun' (e' -> e' -> e') -> Exp' e' -> In (sh', Int) e' -> Out sh' e' -> ()))
  -> AbstInterpOperation op (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out sh e -> ())
defaultBCFold mkFold = AbstInterpOperation $ \case
    (ArgFun f :>: ArgExp init :>: input@(ArgArray _ (ArrayR fullShr@(ShapeRsnoc _) itp) fullSh@(TupRpair _ (TupRsingle sh)) input') :>: output@(ArgArray _ (ArrayR _ otp) _ output') :>: ArgsNil) -> case f of
        _ | BCBodyDict <- twoParamFunc f, BCScalarDict <- reprBCScalar itp -> do
            a <- get
            let env = a ^. essaEnvs . essaEnvArr
            
            -- optimize the initial accumulator
            let ((init', rInit), aInit) = runState (optimizeBoundsExp init) (enterExpScope a)
            put $ popLoopScope aInit

            -- the input array is not loop variant; data and control constraints hold
            let dInput = bccsToScalar itp $ hfmap (varToDataConstraint    env) input'
                cInput = bccsToScalar itp $ bccsEmpty input'
            sInput <- mkInvarVars dInput

            -- accumulator is loop variant; data and control constraints varry;
            let dInit = bccsEmpty init'
                cInit = bccsEmpty init'
            -- get new ESSAIdx to indetify induction variable and make accumulator variable
            (sInit, iInit) <- mkInductionVars (rInit ^. rCS . rData)

            a' <- get    
            let args = diffArg2 (NewBindArg dInput cInput sInput) (NewBindArg dInit cInit sInit)
                ((f', rOut), aOut) = runState (optimizeBoundsFun' args f) (newLoopScope $ enterExpScope a')
            put $ popLoopScope $ popLoopScope aOut

            -- compute scev results
            a'' <- get
            let dSize = varToDataConstraint env sh
            shSize <- dataToBasic dSize
            -- All elements are folded within the accumulator => tripCount = [size(input), size(input)]
            let tripCount = Exists <$> unwrapBCConstraint shSize
                chains      = hzipWith (computeChains (a'' ^. ig)) iInit (rOut ^. rSCEV . rSCEVExp) 
                closedForms = hfmap (computeClosedForm (a'' ^. ig) tripCount) chains

            let args' = ArgFun f' :>: ArgExp init' :>: input :>: output :>: ArgsNil
                iOut  = hfmap (varToESSA env) output'
                res   = analysisResult closedForms (bccsToScalar otp $ bccsEmpty output') (bccsToScalar otp $ bccsEmpty output')

            
            -- check if assertion information can persist outside
            runs <- isNotEmpty fullShr fullSh
            unless runs $ modify $ \st -> st & essaEnvs .~ (a ^. essaEnvs) -- revert to initial state environments

            return (BCOptOperation mkFold args', iOut, output', mkArrayFuncRes itp res, False)
    _ -> error "malformed  input"

defaultBCFold1
  :: (forall sh'. op (Fun' (e -> e -> e) -> In (sh', Int) e -> Out sh' e -> ()))
  -> AbstInterpOperation op (Fun' (e -> e -> e) -> In (sh, Int) e -> Out sh e -> ())
defaultBCFold1 mkFold1 = AbstInterpOperation $ \case
    (ArgFun f :>: input@(ArgArray _ (ArrayR fullShr@(ShapeRsnoc _) itp) fullSh@(TupRpair _ (TupRsingle sh)) input') :>: output@(ArgArray _ (ArrayR _ otp) _ output') :>: ArgsNil) -> case f of
        _ | BCBodyDict <- twoParamFunc f, BCScalarDict <- reprBCScalar itp, BCScalarDict <- reprBCScalar otp -> do
            a <- get
            let env = a ^. essaEnvs . essaEnvArr

            -- the input array is not loop variant; data and control constraints hold
            let dInput = bccsToScalar itp $ hfmap (varToDataConstraint env) input'
                cInput = bccsToScalar itp $ hfmap (varToControlConstraint env) input'
            sInput <- mkInvarVars dInput

            -- first element becomes the accumulator
            let dAcc = bccsToScalar itp $ bccsEmpty input'
                cAcc = bccsToScalar itp $ bccsEmpty input'
            (sAcc, iAcc) <- mkInductionVars dInput

            a' <- get
            let args = diffArg2 (NewBindArg dInput cInput sInput) (NewBindArg dAcc cAcc sAcc)
                ((f', rOut), aOut) = runState (optimizeBoundsFun' args f) (newLoopScope $ enterExpScope a')
            put $ popLoopScope $ popLoopScope aOut

            -- Compute SCEV results
            a'' <- get
            let inputSize = varToDataConstraint env sh
            -- exactly size(input)-1 more incoming elements
            dInputSize <- dataToBasic (interpretData (a'' ^. ig) interpretPrimAdd inputSize (bccPut (toCGType inputSize) $ pure $ fromConst (-1 :: Int)))
            let tripCount = Exists <$> unwrapBCConstraint dInputSize
                chains      = hzipWith (computeChains (a'' ^. ig)) iAcc (rOut ^. rSCEV . rSCEVExp)
                closedForms = hfmap (computeClosedForm (a'' ^. ig) tripCount) chains

            let args' = ArgFun f' :>: input :>: output :>: ArgsNil
                iOut  = hfmap (varToESSA env) output'
                res   = analysisResult closedForms (bccsToScalar itp $ bccsEmpty output') (bccsToScalar itp $ bccsEmpty output')

            -- check if assertion information can persist outside
            runs <- outterDimAtLeast 2 fullShr fullSh
            unless runs $ modify $ \st -> st & essaEnvs .~ (a ^. essaEnvs) -- revert to initial state environments    

            return (BCOptOperation mkFold1 args', iOut, output', mkArrayFuncRes itp res, False)
    _ -> error "malformed input"