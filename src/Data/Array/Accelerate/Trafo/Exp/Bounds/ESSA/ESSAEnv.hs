{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAEnv where
import Data.Array.Accelerate.Trafo.Exp.Bounds.ESSA.ESSAIdx
import Data.Array.Accelerate.Trafo.Exp.Bounds.CAS.Constraints
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Trafo.Exp.Bounds.Utils
import Lens.Micro.TH
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Exp.Bounds.SCEV.RecChain (ClosedFormConstraint)
import Data.Array.Accelerate.Type
import Debug.Trace as Debug

data EnvElem t = EnvElem {essaIdx :: BCConstraint ESSAIdx t, ctrlCnstr :: ControlConstraint t}

instance Show (EnvElem t) where
    show (EnvElem i c) =
        let
            i' = unwrapBCConstraint i
            c' = unwrapBCConstraint c
            in "(" ++ show i' ++ " " ++ show c' ++ ")"

type ESSAEnv t = HList EnvElem t

data ESSAEnvs envs = ESSAEnvs
    {  _essaEnvArr :: ESSAEnv (Fst envs)
    ,  _essaEnvExp :: ESSAEnv (Snd envs)
    }
makeLenses ''ESSAEnvs

declESSAEnv
    :: SType s
    -> LeftHandSide s v env env'
    -> ControlConstraints v
    -> Bounds Int
    -> ESSAEnv env
    -> (TupR (BCConstraint (HMaybe ESSAIdx)) v, Bounds Int, ESSAEnv env')
declESSAEnv s (LeftHandSideSingle tp) (TupRsingle br) oldIdx env =
    let newIdxs     = fmap (+1) oldIdx
        idxs = case (s, tp) of
            (STypeScalar,               tp') | BCScalarDict <- reprBCScalar tp'
                -> case tp' of 
                    (SingleScalarType tp'') | BCSingleDict <- reprBCSingle tp'' -> bccPut (ScalarConstraint tp' . toCSType tp') $ ESSAIdx tp'' <$> newIdxs
                    (VectorScalarType (VectorType _ tp'')) | BCSingleDict <- reprBCSingle tp'' -> bccPut (ScalarConstraint tp' . toCSType tp') $ ESSAIdx tp'' <$> newIdxs
            (STypeGround, GroundRbuffer tp') | BCScalarDict <- reprBCScalar tp'
                -> case tp' of 
                    (SingleScalarType tp'') | BCSingleDict <- reprBCSingle tp'' -> bccPut (BufferConstraint tp' . toCSType tp') $ ESSAIdx tp'' <$> newIdxs
                    (VectorScalarType (VectorType _ tp'')) | BCSingleDict <- reprBCSingle tp'' -> bccPut (BufferConstraint tp' . toCSType tp') $ ESSAIdx tp'' <$> newIdxs
            (STypeGround, GroundRscalar tp') | BCScalarDict <- reprBCScalar tp'
                -> case tp' of
                    (SingleScalarType tp'') | BCSingleDict <- reprBCSingle tp'' -> bccPut (ScalarConstraint tp' . toCSType tp') $ ESSAIdx tp'' <$> newIdxs
                    (VectorScalarType (VectorType _ tp'')) | BCSingleDict <- reprBCSingle tp'' -> bccPut (ScalarConstraint tp' . toCSType tp') $ ESSAIdx tp'' <$> newIdxs
        in (TupRsingle $ hfmap hjust idxs, newIdxs, HCons (EnvElem idxs br) env )
declESSAEnv s (LeftHandSidePair lhs1 lhs2) (TupRpair br1 br2) oldIdx env =
    let (idxs, midIdx, env' )  = declESSAEnv s lhs1 br1 oldIdx env
        (idxs', newIdx, env'') = declESSAEnv s lhs2 br2 midIdx env'
    in  (TupRpair idxs idxs', newIdx , env'')
declESSAEnv s (LeftHandSideWildcard tp) _ oldIdx env = case s of
    STypeGround -> (mapTupR (\gr -> bccPut (toCGType gr) $ pure hnothing) tp, oldIdx, env)
    STypeScalar -> (mapTupR (\gr -> bccPut (toCGType $ GroundRscalar gr) $ pure hnothing) tp, oldIdx, env)
declESSAEnv _ _ _ _ _ = error "mismatched tuple"

redeclESSAEnv
    :: SType s
    -> LeftHandSide s v env env'
    -> TupR (BCConstraint (HMaybe ESSAIdx)) v
    -> ESSAEnv env
    -> ESSAEnv env'
redeclESSAEnv s (LeftHandSideSingle tp) (TupRsingle essa) env = HCons (EnvElem (hfmap (hmaybe (error "expected just") id) essa) (bccEmpty gr)) env
    where gr = case s of
            STypeScalar -> GroundRscalar tp
            STypeGround -> tp
redeclESSAEnv s (LeftHandSidePair lhs1 lhs2) (TupRpair essa1 essa2) env =
    let env'  = redeclESSAEnv s lhs1 essa1 env
        in redeclESSAEnv s lhs2 essa2 env'
redeclESSAEnv _ (LeftHandSideWildcard _) _ env = env
redeclESSAEnv _ _ _ _ = error "mismatched tuple"

popESSAEnv :: forall env env' s v . SType s -> LeftHandSide s v env env' -> ESSAEnv env' -> (TupR (BCConstraint (HMaybe ESSAIdx)) v, ESSAEnv env)
popESSAEnv _ (LeftHandSideSingle _) (HCons e env') = (TupRsingle (hfmap hjust $ essaIdx e), env')
popESSAEnv s (LeftHandSidePair lhs1 lhs2) env = 
    let (idxs', env'  ) = popESSAEnv s lhs2 env
        (idxs'', env'') = popESSAEnv s lhs1 env'
        in (TupRpair idxs'' idxs', env'')
popESSAEnv s (LeftHandSideWildcard tp) env = 
    case s of 
        STypeGround -> (hfmap (\g -> bccPut (toCGType g) $ pure hnothing) tp, env)
        STypeScalar -> (hfmap (\g -> bccPut (toCGType (GroundRscalar g)) $ pure hnothing) tp, env)

getESSAEnv :: Idx env t -> ESSAEnv env -> EnvElem t
getESSAEnv ZeroIdx (HCons e _) = e
getESSAEnv (SuccIdx idxs) (HCons _ ssaIdxs) = getESSAEnv idxs ssaIdxs

modifyESSAEnv:: (EnvElem t -> EnvElem t) -> Idx env t -> ESSAEnv env -> ESSAEnv env
modifyESSAEnv f ZeroIdx (HCons e ls) = HCons (f e) ls
modifyESSAEnv f (SuccIdx idxs) (HCons e ls) = HCons e $ modifyESSAEnv f idxs ls

varToDataConstraint :: ESSAEnv env -> Var s env t -> DataConstraint t
varToDataConstraint env v = hfmap (hfmap Diff) $ varToClosedForm env v

varToClosedForm :: ESSAEnv env -> Var s env t -> ClosedFormConstraint t
varToClosedForm env (Var _ i) = hfmap (hjust . f) $ essaIdx (getESSAEnv i env)
    where f x = BDiff (Just x) 0

varToControlConstraint :: ESSAEnv env -> Var s env t -> ControlConstraint t
varToControlConstraint env var = ctrlCnstr $ getESSAEnv (varIdx var) env

varToESSA :: ESSAEnv env -> Var s env t -> BCConstraint ESSAIdx t
varToESSA env v = essaIdx $ getESSAEnv (varIdx v) env

remapEnv :: Bounds [(ESSAIdx t, ESSAIdx t)] -> ESSAEnv env -> ESSAEnv env
remapEnv (Bounds [] []) env = env
remapEnv mappings (HCons (EnvElem i c) env) =
    let bcMappings = bccPut (toCGType i) (fmap Tag mappings)
        bcResult = hzipWith (remapIdx . unTag) bcMappings i
        idxs     = hfmap (\(HPair a _) -> a) bcResult
        residual = fmap unTag <$> unwrapBCConstraint $ hfmap sndw bcResult
        in HCons (EnvElem idxs c) (remapEnv residual env)
remapEnv _ HEmpty = HEmpty

remapIdx :: [(ESSAIdx t, ESSAIdx t)] -> ESSAIdx a -> HPair ESSAIdx (Tag [(ESSAIdx t, ESSAIdx t)]) a
remapIdx ((old, new) : ls) target@(ESSAIdx tp _) | essaInt target == essaInt old = HPair (ESSAIdx tp $ essaInt new) (Tag ls)
remapIdx ((old, new) : ls) i =
    let (HPair rIdx (Tag rls)) = remapIdx ls i
        in HPair rIdx $ Tag $ (old, new) : rls
remapIdx [] i = HPair i (Tag [])