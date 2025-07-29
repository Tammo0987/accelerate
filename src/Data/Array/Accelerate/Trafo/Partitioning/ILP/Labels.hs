{-
Module      : Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew
Description : Labels representing nodes in the graph.

This module provides the labels that represent nodes in the graph. A node can
either be a computation or a buffer.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type

import Lens.Micro
import Lens.Micro.Mtl

import Data.Set (Set)

import Data.Hashable (Hashable, hashWithSalt)
import Prelude hiding (exp)

import qualified Data.Functor.Const as C
import Data.Coerce
import Control.Monad.State.Strict
import Data.Maybe (fromJust)
import Data.List ( intercalate )
import Debug.Trace



--------------------------------------------------------------------------------
-- Labels
--------------------------------------------------------------------------------

-- | The types a label can have.
data LabelType
  = Comp  -- ^ Label for computations.
  | GVal  -- ^ Label for ground values (buffers/scalars).

-- | Labels for referencing nodes.
--
-- A label uniquely identifies a node and optionally specifies the parent it
-- belongs to. Only 'Comp' labels may be parents.
--
-- A label of type 'Comp' is used to represent anything that is relevant for
-- reconstruction but not for the fusion/in-place updates ILP. This type mostly
-- represents the labels for bodies of functions, if-then-else branches, and
-- while loops.
--
-- @VLabel x Nothing@ means that label @x@ is top-level.
-- @VLabel x (Just y)@ means that label @x@ is a sub-computation of label @y@.
data Label (t :: LabelType) where
  Label :: Int      -- ^ The computation label.
        -> Parent   -- ^ The parent computation.
        -> Label t

type Parent = Maybe (Label Comp)

-- | Lens for getting and setting the label id.
labelId :: Lens' (Label t) Int
labelId f (Label i p) = f i <&> (`Label` p)

-- | Lens for getting and setting the parent label.
parent :: Lens' (Label t) Parent
parent f (Label i p) = f p <&> Label i

-- | Lens for setting and unsafely getting the parent.
parent' :: Lens' (Label t) (Label Comp)
parent' f (Label i p) = f (fromJust p) <&> (Label i . Just)

-- | Lens for interpreting any label as a computation label.
asComp :: Lens' (Label t) (Label Comp)
asComp f l = coerce <$> f (coerce l)

-- | Lens for interpreting any label as a buffer label.
asBuff :: Lens' (Label t) (Label GVal)
asBuff f l = coerce <$> f (coerce l)

instance Show (Label Comp) where
  show :: Label Comp -> String
  show c = "C" ++ intercalate "." (map show . reverse $ labelIds c)

instance Show (Label GVal) where
  show :: Label GVal -> String
  show b = "B" ++ intercalate "." (map show . reverse $ labelIds b)

labelIds :: Label t -> [Int]
labelIds (Label i p) = i : maybe [] labelIds p

instance Eq (Label t) where
  (==) :: Label t -> Label t -> Bool
  (==) l1 l2 = (l1^.labelId == l2^.labelId) && checkMismatch (l1^.parent) (l2^.parent) True

instance Ord (Label t) where
  compare :: Label t -> Label t -> Ordering
  compare l1 l2 = case compare (l1^.labelId) (l2^.labelId) of
    EQ  -> checkMismatch (l1^.parent) (l2^.parent) EQ
    ord -> ord

-- | Checks if two parents are equal and throw an error if they are not.
checkMismatch :: Parent -> Parent -> a -> a
checkMismatch (Just l1) (Just l2) | l1 == l2 = id
checkMismatch Nothing Nothing = id
checkMismatch _ _ = internalError "checkMismatch: Mismatching labels detected"

instance Hashable (Label t) where
  hashWithSalt :: Int -> Label t -> Int
  hashWithSalt s l = hashWithSalt s (l ^. labelId)

-- | Compute the nesting level of a label.
level :: Label t -> Int
level l = case l^.parent of
  Nothing -> 0
  Just p  -> 1 + level p

-- | Create a new label.
freshL' :: State (Label t) (Label t)
freshL' = id <%= (labelId +~ 1)

-- | Set of labels.
type Labels t = Set (Label t)

-- | Tuple of ground value labels.
type GVals = TupR (C.Const (Labels GVal))



--------------------------------------------------------------------------------
-- Labelled Environment
--------------------------------------------------------------------------------

-- | An 'ELabel' uniquely identifies an element of the environment.
newtype EnvLabel = EnvLabel { unELabel :: Int }
  deriving (Eq, Ord, Num)

instance Show EnvLabel where
  show :: EnvLabel -> String
  show (EnvLabel i) = "E" ++ show i

-- | A variable in the environment stores a tuple of buffers and their uniquenesses.
--   They are uniquely identified by their 'EnvLabel'.
type EnvVal t = (EnvLabel, GVals t, Uniquenesses t)

-- | A collection of variables in the environment. The structure of the 'EnvLabels'
--   can be used to extract individual 'EnvVal'.
type EnvVals t = (EnvLabels t, GVals t, Uniquenesses t)

-- | A 'TupR' of 'EnvLabel'.
type EnvLabels = TupR (C.Const EnvLabel)

-- | Create a fresh 'EnvLabel' from the current state.
freshE' :: State EnvLabel EnvLabel
freshE' = id <%= (+1)

-- | The environment used during graph construction.
--
-- The environment is basically just a fixed length list of buffers with some
-- associated type information.
--
-- We use a tuple of labels instead of a single label because after an
-- if-then-else there are now two labels that could be referenced depending
-- on the branch taken.
--
data GValEnv env where
  -- | The empty environment.
  EnvNil :: GValEnv ()
  -- | The non-empty environment.
  (:>>:) :: EnvVal t        -- ^ See 'EnvVal'.
         -> GValEnv env  -- ^ The rest of the environment.
         -> GValEnv (env, t)

instance Show (GValEnv env) where
  show :: GValEnv env -> String
  show EnvNil = "EnvNil"
  show (envl :>>: env) = show envl ++ " :>>: " ++ show env

-- TODO: Is this instance necessary?
instance Semigroup (GValEnv env) where
  (<>) :: GValEnv env -> GValEnv env -> GValEnv env
  (<>) EnvNil EnvNil = EnvNil
  (<>) ((e1, bs1, us1) :>>: env1) ((e2, bs2, us2) :>>: env2)
    | e1 == e2  = (e1, bs1 <> bs2, us1 <> us2) :>>: (env1 <> env2)
    | otherwise = internalError "mappend: Encountered diverging EnvLabels."

-- | Constructs a new 'GValEnv' by prepending labels for each element in the
--   left-hand side.
--
-- The case where the left-hand side and the right-hand side are incompatible
-- should neven happen, but in case it does just replicate the labels.
weakenEnv :: LeftHandSide s v env env' -> GVals v -> Uniquenesses v -> GValEnv env -> State EnvLabel (GValEnv env')
weakenEnv LeftHandSideWildcard{} _ _ = pure
weakenEnv LeftHandSideSingle{} bs us = \lenv -> freshE' >>= \e -> return ((e, bs, us) :>>: lenv)
weakenEnv (LeftHandSidePair l r) (TupRpair lbs rbs) (TupRpair lus rus) = weakenEnv l lbs lus >=> weakenEnv r rbs rus
weakenEnv (LeftHandSidePair _ _) _ _ = internalError "weakenEnv: Inaccesible left-hand side"



--------------------------------------------------------------------------------
-- Bound left-hand side
--------------------------------------------------------------------------------

-- | A 'LeftHandSide' with the values bound at its leaves.
data BoundLHS s v env env' where
  BoundLHSsingle
    :: EnvVal v
    -> s v
    -> BoundLHS s v env (env, v)

  BoundLHSwildcard
    :: TupR s v
    -> BoundLHS s v env env

  BoundLHSpair
    :: BoundLHS s v1       env  env'
    -> BoundLHS s v2       env' env''
    -> BoundLHS s (v1, v2) env  env''

instance Show (BoundLHS s v env env') where
  show :: BoundLHS s v env env' -> String
  show (BoundLHSsingle e _) = "BLHS(" ++ show e ++ ")"
  show (BoundLHSwildcard _) = "BLHS_"
  show (BoundLHSpair l r)   = "BLHS(" ++ show l ++ ", " ++ show r ++ ")"

type BoundGLHS = BoundLHS GroundR

-- | Get bindings from the environment and bind them to the left-hand side.
bindLHS :: LeftHandSide s v env env' -> GValEnv env' -> BoundLHS s v env env'
bindLHS (LeftHandSideSingle sv) (l :>>: _) = BoundLHSsingle l sv
bindLHS (LeftHandSideWildcard tr) _ = BoundLHSwildcard tr
bindLHS (LeftHandSidePair l r) env = BoundLHSpair (bindLHS l (stripLHS r env)) (bindLHS r env)

unbindLHS :: BoundLHS s v env env' -> LeftHandSide s v env env'
unbindLHS (BoundLHSsingle _ sv) = LeftHandSideSingle sv
unbindLHS (BoundLHSwildcard tr) = LeftHandSideWildcard tr
unbindLHS (BoundLHSpair l r)    = LeftHandSidePair (unbindLHS l) (unbindLHS r)

-- | Remove values bound by the left-hand side from the environment.
stripLHS :: LeftHandSide s v env env' -> GValEnv env' -> GValEnv env
stripLHS (LeftHandSideSingle _) (_ :>>: le') = le'
stripLHS (LeftHandSideWildcard _) le = le
stripLHS (LeftHandSidePair l r) le = stripLHS l (stripLHS r le)

createLHS :: BoundLHS s v _env _env'
          -> GValEnv env
          -> (forall env'. GValEnv env' -> LeftHandSide s v env env' -> r)
          -> r
createLHS (BoundLHSsingle e sv) env k = k (e :>>: env) (LeftHandSideSingle sv)
createLHS (BoundLHSwildcard tr) env k = k env (LeftHandSideWildcard tr)
createLHS (BoundLHSpair l r)    env k =
  createLHS   l env  $ \env'  l' ->
    createLHS r env' $ \env'' r' ->
      k env'' (LeftHandSidePair l' r')



--------------------------------------------------------------------------------
-- Labelled Arguments
--------------------------------------------------------------------------------

{- |
The code below is for retrieving the labels for arguments to a function.
When the argument is 'ArgVar' (scalar valued variable), we need to retrieve the label(s) of the buffer(s) from the environment.
When the argument is 'ArgExp' (expression), we need to retrieve the labels of buffers the expression depends on.
When the argument is 'ArgFun' (function), we need to retrieve the labels of buffers the function depends on.
When the argument is 'ArgArray' (array), we need to retrieve the label(s) of the array(s).

For now it doesn't seem that a tuple argument needs to know the exact structure of the tuple, only which labels it references.
This means it's sufficient to pair each argument with a set of labels.

The main difference is that 'ArgArray' is the only value that may be fused.
The other types of arguments only ever read a single value from an array and
can therefore not be fused.
-}

-- | A label to be stored with an argument, indicating whether an argument is an
--   array or not, and if so, which buffers it is associated with as a 'TupF'.
data ArgLabel t where
  -- | The argument is an array.
  Arr     :: EnvVals (Buffers e)  -- ^ The array values.
          -> EnvVals sh           -- ^ The shape values.
          -> ArgLabel (m sh e)
  -- | The argument is a scalar 'Var'', 'Exp'' or 'Fun''.
  NotArr  :: Labels GVal  -- ^ The variables referenced by the argument.
          -> ArgLabel (t e)

deriving instance Show (ArgLabel t)

-- | Get the set of dependent buffers of an 'ArgLabel'.
getLabelDeps :: ArgLabel t -> Labels GVal
getLabelDeps (Arr (_, arr, _) (_, sh, _)) = foldConstsR arr <> foldConstsR sh
getLabelDeps (NotArr deps) = deps

-- | Get the set of unique array dependencies of an 'ArgLabel'.
getLabelUniqueArrDeps :: ArgLabel t -> Labels GVal
getLabelUniqueArrDeps (Arr (_, arr, u) _) = uniqueLabels u arr
getLabelUniqueArrDeps (NotArr _) = internalError "getLabelUniqueArrDeps: Expected Arr but got NotArr"

-- | Given 'Uniquenesses', get the unique labels from 'GVals'.
uniqueLabels :: Uniquenesses e -> GVals e -> Labels GVal
uniqueLabels TupRunit TupRunit      = mempty
uniqueLabels (TupRsingle Shared) _  = mempty
uniqueLabels (TupRsingle Unique) bs = foldConstsR bs
uniqueLabels (TupRpair ul ur) (TupRpair l r) = uniqueLabels ul l <> uniqueLabels ur r
uniqueLabels _ _ = internalError "uniqueLabels: Tuple mismatch "

-- | Get the arrays of an 'ArgLabel'.
getLabelArrays :: ArgLabel (m sh e) -> GVals (Buffers e)
getLabelArrays (Arr (_, arr, _) (_, _, _)) = arr
getLabelArrays (NotArr _) = internalError "getLabelArrays: Expected Arr but got NotArr"

-- | Get the array dependencies of an 'ArgLabel'.
getLabelArrDeps :: ArgLabel (m sh e) -> Labels GVal
getLabelArrDeps = foldConstsR . getLabelArrays

-- | Get a single array dependency of an 'ArgLabel'.
getLabelArrDep :: ArgLabel (m sh e) -> Label GVal
getLabelArrDep = foldr1 const . getLabelArrDeps

-- | Get the shapes of an 'ArgLabel'.
getLabelShape :: ArgLabel (m sh e) -> GVals sh
getLabelShape (Arr (_, _, _) (_, sh, _)) = sh
getLabelShape (NotArr _) = internalError "getLabelShape: Expected Arr but got NotArr"

-- | Get the shape dependencies of an 'ArgLabel'.
getLabelShDeps :: ArgLabel (m sh e) -> Labels GVal
getLabelShDeps = foldConstsR . getLabelShape

-- | Check if two arguments use the same shape variables.
eqLabelShape :: ArgLabel (m1 sh1 e1) -> ArgLabel (m2 sh2 e2) -> Bool
eqLabelShape l1 l2 = eqConstsR (getLabelShape l1) (getLabelShape l2)

-- | The argument to a function paired with 'ArgLabels'
--
-- This should probably just copy the structure of 'Arg' but changing that now
-- takes a lot of work... Maybe make a version of each data-type that has a slot
-- for additional information? I.e. @data Arg' a env t where ...; type Arg = Arg' ()@?
-- It's common for compilers to add void-pointers in their structures to allow
-- for exactly this kind of extensibility.
data LabelledArg env t = L (Arg env t) (ArgLabel t)
  deriving (Show)

-- | Labelled arguments to be passed to a function.
type LabelledArgs env = PreArgs (LabelledArg env)

-- | Label the arguments to a function using the given environment.
labelArgs :: Args env args -> GValEnv env -> LabelledArgs env args
labelArgs ArgsNil _ = ArgsNil
labelArgs (arg :>: args) env =
  L arg (getArgLabels arg env) :>: labelArgs args env

-- | Get the 'ArgLabels' associated with 'Arg' from 'GValEnv'.
getArgLabels :: Arg env t -> GValEnv env -> ArgLabel t
getArgLabels (ArgVar vars) env = NotArr $ getVarsDeps vars env
getArgLabels (ArgExp exp)  env = NotArr $ getExpDeps  exp  env
getArgLabels (ArgFun fun)  env = NotArr $ getFunDeps  fun  env
getArgLabels (ArgArray _ (ArrayR _ _tp) sh arr) env
  = Arr (getVarsFromEnv arr env) (getVarsFromEnv sh env)

-- | Get the values associated with 'Vars' from 'GValEnv'.
getVarsFromEnv :: Vars a env b -> GValEnv env -> EnvVals b
getVarsFromEnv TupRunit         _   = (TupRunit, TupRunit, TupRunit)
getVarsFromEnv (TupRsingle var) env | (e, bs, u) <- getVarFromEnv var env
                                    = (TupRsingle (C.Const e), bs, u)
getVarsFromEnv (TupRpair l r)   env | (el, bsl, ul) <- getVarsFromEnv l env
                                    , (er, bsr, ur) <- getVarsFromEnv r env
                                    = (TupRpair el er, TupRpair bsl bsr, TupRpair ul ur)

-- | Get the value associated with a 'Var' from 'GValEnv'.
getVarFromEnv :: Var a env b -> GValEnv env -> EnvVal b
getVarFromEnv = lookupIdxInEnv . varIdx

-- | Get the value associated with an 'Idx' from 'GValEnv'.
lookupIdxInEnv :: Idx env t -> GValEnv env -> EnvVal t
lookupIdxInEnv ZeroIdx       (bs :>>: _)   = bs
lookupIdxInEnv (SuccIdx idx) (_  :>>: env) = lookupIdxInEnv idx env

-- | Get the dependencies of a tuple of variables.
getVarsDeps :: Vars s env t -> GValEnv env -> Labels GVal
getVarsDeps vars = foldConstsR . (^._2) . getVarsFromEnv vars

-- | Get the dependencies of a tuple of variables.
getVarDeps :: Var s env t -> GValEnv env -> Labels GVal
getVarDeps var = foldConstsR . (^._2) . getVarFromEnv var

-- | Get the dependencies of an expression.
getExpDeps :: OpenExp x env y -> GValEnv env -> Labels GVal
getExpDeps (ArrayInstr (Index     var) poe) env = getVarDeps var  env <> getExpDeps poe  env
getExpDeps (ArrayInstr (Parameter var) poe) env = getVarDeps var  env <> getExpDeps poe  env
getExpDeps (Let _ poe1 poe2)                env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (Evar _)                         _   = mempty
getExpDeps  Foreign{}                       _   = mempty
getExpDeps (Pair  poe1 poe2)                env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps  Nil                             _   = mempty
getExpDeps (VecPack _ poe)                  env = getExpDeps poe  env
getExpDeps (VecUnpack _ poe)                env = getExpDeps poe  env
getExpDeps (IndexSlice _ poe1 poe2)         env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (IndexFull  _ poe1 poe2)         env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (ToIndex    _ poe1 poe2)         env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (FromIndex  _ poe1 poe2)         env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (Case poe1 poes poe2)            env = getExpDeps poe1 env <>
                                                  foldMap ((`getExpDeps` env) . snd) poes <>
                                                  maybe mempty (`getExpDeps` env) poe2
getExpDeps (Cond poe1 poe2 exp3)            env = getExpDeps poe1 env <>
                                                  getExpDeps poe2 env <>
                                                  getExpDeps exp3 env
getExpDeps (While pof1 pof2 poe)            env = getFunDeps pof1 env <>
                                                  getFunDeps pof2 env <>
                                                  getExpDeps poe  env
getExpDeps (Const _ _)                      _   = mempty
getExpDeps (PrimConst _)                    _   = mempty
getExpDeps (PrimApp   _ poe)                env = getExpDeps poe  env
getExpDeps (ShapeSize _ poe)                env = getExpDeps poe  env
getExpDeps (Undef _)                        _   = mempty
getExpDeps  Coerce{}                        _   = mempty

-- | Get the dependencies of a function.
getFunDeps :: OpenFun x env y -> GValEnv env -> Labels GVal
getFunDeps (Body  poe) env = getExpDeps poe env
getFunDeps (Lam _ fun) env = getFunDeps fun env

-- -- | Remove the 'Buffers' type from 'ArgLabel'.
-- unbuffers :: forall e. TypeR e -> EnvVals (Distribute Buffer e) -> EnvVals e
-- unbuffers TupRunit _ = (TupRunit, TupRunit, TupRunit)
-- unbuffers (TupRsingle t) (TupRsingle (C.Const e), TupRsingle (C.Const bs), TupRsingle _)
--   = (TupRsingle (C.Const e), TupRsingle (C.Const bs), TupRsingle _)
-- unbuffers (TupRpair t1 t2) (TupRpair el er, TupRpair bsl bsr, TupRpair ul ur)
--   | (el', bsl', ul') <- unbuffers t1 (el, bsl, ul)
--   , (er', bsr', ur') <- unbuffers t2 (er, bsr, ur)
--   = (TupRpair el' er', TupRpair bsl' bsr', TupRpair ul' ur')
-- unbuffers _ _ = internalError "unbuffers: Tuple mismatch"



--------------------------------------------------------------------------------
-- Helpers for Labelled Environment
--------------------------------------------------------------------------------

-- | Map a function over the labels in the environment.
mapLEnv :: (forall t. GVals t -> GVals t) -> GValEnv env -> GValEnv env
mapLEnv _ EnvNil = EnvNil
mapLEnv f ((e, bs, us) :>>: env) = (e, f bs, us) :>>: mapLEnv f env

-- | Fold over the labels in the environment.
foldMapLEnv :: Monoid m => (forall t. GVals t -> m) -> GValEnv env -> m
foldMapLEnv _ EnvNil = mempty
foldMapLEnv f ((_, bs, _) :>>: env) = f bs <> foldMapLEnv f env

-- | Map a monadic function over the labels in the environment.
mapLEnvM :: Monad m => (forall t. GVals t -> m (GVals t)) -> GValEnv env -> m (GValEnv env)
mapLEnvM _ EnvNil = return EnvNil
mapLEnvM f ((e, bs, us) :>>: env) = do
  bs'  <- f bs
  env' <- mapLEnvM f env
  return ((e, bs', us) :>>: env')

-- | Flipped version of 'mapLEnvM'.
forLEnvM :: Monad m => GValEnv env -> (forall t. GVals t -> m (GVals t)) -> m (GValEnv env)
forLEnvM env f = mapLEnvM f env
{-# INLINE forLEnvM #-}

-- | Map a monadic action over the labels in the environment and discard the result.
mapLEnvM_ :: Monad m => (forall t. GVals t -> m ()) -> GValEnv env -> m ()
mapLEnvM_ _ EnvNil = return ()
mapLEnvM_ f ((_, bs, _) :>>: env) = f bs >> mapLEnvM_ f env

-- | Flipped version of 'mapLEnvM_'.
forLEnvM_ :: Monad m => GValEnv env -> (forall t. GVals t -> m ()) -> m ()
forLEnvM_ env f = mapLEnvM_ f env
{-# INLINE forLEnvM_ #-}

-- | Traverse over the labels in the environment.
traverseLEnv :: Applicative f => (forall t. GVals t -> f (GVals t)) -> GValEnv env -> f (GValEnv env)
traverseLEnv _ EnvNil = pure EnvNil
traverseLEnv f ((e, bs, us) :>>: env) = ((:>>:) . (e,,us) <$> f bs) <*> traverseLEnv f env

-- | Flipped version of 'traverseLEnv'.
forLEnv :: Applicative f => GValEnv env -> (forall t. GVals t -> f (GVals t)) -> f (GValEnv env)
forLEnv env f = traverseLEnv f env
{-# INLINE forLEnv #-}

-- | Traverse over the labels in the environment and discard the result.
traverseLEnv_ :: Applicative f => (forall t. GVals t -> f ()) -> GValEnv env -> f ()
traverseLEnv_ _ EnvNil = pure ()
traverseLEnv_ f ((_, bs, _) :>>: env) = f bs *> traverseLEnv_ f env

-- | Flipped version of 'traverseLEnv_'.
forLEnv_ :: Applicative f => GValEnv env -> (forall t. GVals t -> f ()) -> f ()
forLEnv_ env f = traverseLEnv_ f env
{-# INLINE forLEnv_ #-}



--------------------------------------------------------------------------------
-- Helpers for Labelled Arguments
--------------------------------------------------------------------------------

-- | Map a function over the labelled arguments.
mapLArgs :: (forall s. LabelledArg env s -> LabelledArg env s) -> LabelledArgs env t -> LabelledArgs env t
mapLArgs _ ArgsNil = ArgsNil
mapLArgs f (larg :>: largs) = f larg :>: mapLArgs f largs

-- | Fold over the labelled arguments and combine the resulting monoidal values.
foldMapLArgs :: Monoid m => (forall s. LabelledArg env s -> m) -> LabelledArgs env t -> m
foldMapLArgs _ ArgsNil = mempty
foldMapLArgs f (larg :>: largs) = f larg <> foldMapLArgs f largs

-- | Map a monadic function over the labelled arguments.
mapLArgsM :: Monad m => (forall s. LabelledArg env s -> m (LabelledArg env s)) -> LabelledArgs env t -> m (LabelledArgs env t)
mapLArgsM _ ArgsNil = return ArgsNil
mapLArgsM f (larg :>: largs) = do
  larg'  <- f larg
  largs' <- mapLArgsM f largs
  return (larg' :>: largs')

-- | Flipped version of 'mapLArgsM'.
forLArgsM :: Monad m => LabelledArgs env t -> (forall s. LabelledArg env s -> m (LabelledArg env s)) -> m (LabelledArgs env t)
forLArgsM largs f = mapLArgsM f largs
{-# INLINE forLArgsM #-}

-- | Map a monadic action over the labelled arguments and discard the result.
mapLArgsM_ :: Monad m => (forall s. LabelledArg env s -> m ()) -> LabelledArgs env t -> m ()
mapLArgsM_ _ ArgsNil = return ()
mapLArgsM_ f (larg :>: largs) = f larg >> mapLArgsM_ f largs

-- | Flipped version of 'mapLArgsM_'.
forLArgsM_ :: Monad m => LabelledArgs env t -> (forall s. LabelledArg env s -> m ()) -> m ()
forLArgsM_ largs f = mapLArgsM_ f largs
{-# INLINE forLArgsM_ #-}

-- | Map a monadic function over the labelled arguments and accumulate the result.
mapAccumLArgsM :: Monad m => (forall s. a -> LabelledArg env s -> m (a, LabelledArg env s)) -> a -> LabelledArgs env t -> m (a, LabelledArgs env t)
mapAccumLArgsM _ a ArgsNil = return (a, ArgsNil)
mapAccumLArgsM f a (larg :>: largs) = do
  (acc' , larg')  <- f a larg
  (acc'', largs') <- mapAccumLArgsM f acc' largs
  return (acc'', larg' :>: largs')

-- | Flipped version of 'mapAccumLArgsM'.
forAccumLArgsM :: Monad m => a -> LabelledArgs env t -> (forall s. a -> LabelledArg env s -> m (a, LabelledArg env s)) -> m (a, LabelledArgs env t)
forAccumLArgsM a largs f = mapAccumLArgsM f a largs
{-# INLINE forAccumLArgsM #-}

-- | Traverse over the labelled arguments.
traverseLArgs :: Applicative f => (forall s. LabelledArg env s -> f (LabelledArg env s)) -> LabelledArgs env t -> f (LabelledArgs env t)
traverseLArgs _ ArgsNil = pure ArgsNil
traverseLArgs f (larg :>: largs) = (:>:) <$> f larg <*> traverseLArgs f largs

-- | Flipped version of 'traverseLArgs'.
forLArgs :: Applicative f => LabelledArgs env t -> (forall s. LabelledArg env s -> f (LabelledArg env s)) -> f (LabelledArgs env t)
forLArgs largs f = traverseLArgs f largs
{-# INLINE forLArgs #-}

-- | Traverse over the labelled arguments and discard the result.
traverseLArgs_ :: Applicative f => (forall s. LabelledArg env s -> f ()) -> LabelledArgs env t -> f ()
traverseLArgs_ _ ArgsNil = pure ()
traverseLArgs_ f (larg :>: largs) = f larg *> traverseLArgs_ f largs

-- | Flipped version of 'traverseLArgs_'.
forLArgs_ :: Applicative f => LabelledArgs env t -> (forall s. LabelledArg env s -> f ()) -> f ()
forLArgs_ largs f = traverseLArgs_ f largs
{-# INLINE forLArgs_ #-}

-- | All arrays that the function reads from.
inputArrays :: LabelledArgs env t -> Labels GVal
inputArrays = foldMapLArgs \case
  L (ArgArray In  _ _ _) (Arr (_,arr,_) _) -> foldConstsR arr
  L (ArgArray Mut _ _ _) (Arr (_,arr,_) _) -> foldConstsR arr
  _ -> mempty

-- | All arrays that the function writes to.
outputArrays :: LabelledArgs env t -> Labels GVal
outputArrays = foldMapLArgs \case
  L (ArgArray Out _ _ _) (Arr (_,arr,_) _) -> foldConstsR arr
  L (ArgArray Mut _ _ _) (Arr (_,arr,_) _) -> foldConstsR arr
  _ -> mempty

-- | All non-array arguments and array shapes.
notArrays :: LabelledArgs env t -> Labels GVal
notArrays = foldMapLArgs \case
  L _ (Arr _ (_,sh,_)) -> foldConstsR sh
  L _ (NotArr deps)    -> deps

-- | Fold map over all inputs.
foldMapInputLabels :: Monoid m => (forall sh e. ArgLabel (In sh e) -> m) -> LabelledArgs env t -> m
foldMapInputLabels f = foldMapLArgs \case
  L (ArgArray In _ _ _) l -> f l
  _ -> mempty

-- | Fold map over all outputs.
foldMapOutputLabels :: Monoid m => (forall sh e. ArgLabel (Out sh e) -> m) -> LabelledArgs env t -> m
foldMapOutputLabels f = foldMapLArgs \case
  L (ArgArray Out _ _ _) l -> f l
  _ -> mempty



--------------------------------------------------------------------------------
-- Debugging
--------------------------------------------------------------------------------

-- | Trace a value using a function to format the output.
traceWith :: (Show a) => (a -> String) -> a -> a
traceWith f x = trace (f x) x
{-# INLINE traceWith #-}
