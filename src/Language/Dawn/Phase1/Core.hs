-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.
{-# LANGUAGE NamedFieldPuns #-}

module Language.Dawn.Phase1.Core
  ( (-->),
    (*),
    (+->),
    ($:),
    ($.),
    addDataDefs,
    addMissingStacks,
    checkType,
    composeSubst,
    ConsDef (..),
    ConsId,
    Context,
    DataDef (..),
    DataDefError (..),
    defineFn,
    defineFns,
    emptyEnv,
    ensureUniqueStackId,
    Env (..),
    Expr (..),
    FnDef (..),
    FnDefError (..),
    fnDefExpr,
    fnDefFnId,
    fnDeps,
    fnDepsSort,
    FnId,
    FnIds,
    forall,
    forall',
    freshTypeVar,
    HasTypeVars (..),
    inferNormType,
    inferType,
    instantiate,
    Intrinsic (..),
    intrinsicFnId,
    intrinsicType,
    Literal (..),
    MatchError (..),
    mgu,
    normalizeType,
    Pattern (..),
    removeTrivialStacks,
    replaceTypeVars,
    requantify,
    StackId,
    StackIds,
    Subs (..),
    Subst (..),
    tBool,
    tempStackIds,
    tU32,
    Type (..),
    TypeConsId,
    TypeError (..),
    TypeVar (..),
    TypeVars,
    uncondFnDeps,
    UnificationError (..),
    UnivQuants,
    VarId,
  )
where

import Control.Monad
import Control.Monad.Except
import Data.Either.Combinators
import Data.Graph
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.Word
import Prelude hiding ((*))

---------------------
-- Abstract Syntax --
---------------------

-- | Expressions
data Expr
  = EIntrinsic Intrinsic
  | EQuote Expr
  | ECompose [Expr]
  | EContext StackId Expr
  | ELit Literal
  | EMatch [(Pattern, Expr)]
  | ECons ConsId
  | ECall FnId
  deriving (Eq, Ord, Show)

data Literal
  = LBool Bool
  | LU32 Word32
  deriving (Eq, Ord, Show)

data Pattern
  = PEmpty
  | PProd Pattern Pattern
  | PLit Literal
  | PCons ConsId
  deriving (Eq, Ord, Show)

data Intrinsic
  = IPush
  | IPop
  | IClone
  | IDrop
  | IQuote
  | ICompose
  | IApply
  | IAnd
  | IOr
  | INot
  | IXor
  | IIncr
  | IDecr
  | IAdd
  | ISub
  | IBitAnd
  | IBitOr
  | IBitNot
  | IBitXor
  | IShl
  | IShr
  | IEq
  | ILt
  | IGt
  | ILteq
  | IGteq
  deriving (Eq, Ord, Show)

data Type
  = TVar TypeVar
  | TProd Type Type
  | TFn UnivQuants MultiIO
  | TCons [Type] TypeConsId
  deriving (Eq, Ord, Show)

-- | Multi-stack input/output
type MultiIO = Map.Map StackId (Type, Type)

-- | Stack identifier
type StackId = String

-- | Type Constructor identifier
type TypeConsId = String

-- | Constructor identifier
type ConsId = String

-- | Function identifier
type FnId = String

-- | Universal quantifiers
type UnivQuants = TypeVars

-- | Type variable set
type TypeVars = Set.Set TypeVar

-- | Type variable
newtype TypeVar = TypeVar VarId
  deriving (Eq, Ord, Show)

-- | Variable identifier
type VarId = Int

-------------------
-- Instantiation --
-------------------

class HasTypeVars t where
  -- | Rename the specified type variable
  renameTypeVar :: TypeVar -> TypeVar -> t -> t

  -- | Return free type variables
  ftv :: t -> TypeVars

  -- | Return bound type variables
  btv :: t -> TypeVars

  -- | Return all type variables, in the order they appear
  atv :: t -> [TypeVar]

instance HasTypeVars Type where
  renameTypeVar _ to t
    | to `elem` atv t =
      error "type variable shadowing"
  renameTypeVar from to t@(TVar tv)
    | tv == from = TVar to
    | otherwise = t
  renameTypeVar from to (TProd l r) =
    TProd (renameTypeVar from to l) (renameTypeVar from to r)
  renameTypeVar from to (TFn uqs mio) =
    TFn
      (Set.map (\tv -> if tv == from then to else tv) uqs)
      (renameTypeVar from to mio)
  renameTypeVar from to (TCons args tc) =
    TCons (renameTypeVar from to args) tc

  ftv (TVar tv) = Set.singleton tv
  ftv (TProd l r) = ftv l `Set.union` ftv r
  ftv (TFn qs io) = ftv io `Set.difference` qs
  ftv (TCons args _) = ftv args

  btv (TVar _) = Set.empty
  btv (TProd l r) = btv l `Set.union` btv r
  btv (TFn qs io) = qs `Set.union` btv io
  btv (TCons args _) = btv args

  atv (TVar tv) = [tv]
  atv (TProd l r) = atv l `union` atv r
  atv (TFn _ io) = atv io
  atv (TCons args _) = atv args

instance HasTypeVars a => HasTypeVars [a] where
  renameTypeVar from to ts = map (renameTypeVar from to) ts
  ftv = foldr (Set.union . ftv) Set.empty
  btv = foldr (Set.union . btv) Set.empty
  atv = nub . concatMap atv

instance (HasTypeVars a, HasTypeVars b) => HasTypeVars (a, b) where
  renameTypeVar from to (a, b) =
    (renameTypeVar from to a, renameTypeVar from to b)
  ftv (a, b) = ftv a `Set.union` ftv b
  btv (a, b) = btv a `Set.union` btv b
  atv (a, b) = atv a `union` atv b

instance HasTypeVars v => HasTypeVars (Map.Map k v) where
  renameTypeVar from to = Map.map (renameTypeVar from to)
  ftv = ftv . Map.elems
  btv = btv . Map.elems
  atv = atv . Map.elems

-- | Get a fresh type variable
freshTypeVar :: TypeVars -> (TypeVar, TypeVars)
freshTypeVar reserved = iter 0
  where
    iter n
      | TypeVar n `Set.member` reserved = iter (succ n)
      | otherwise = let tv = TypeVar n in (tv, Set.insert tv reserved)

-- | Replace the specified type variables with fresh type variables
replaceTypeVars :: HasTypeVars t => [TypeVar] -> t -> TypeVars -> (t, TypeVars)
replaceTypeVars [] t reserved = (t, reserved)
replaceTypeVars (tv : tvs) t reserved =
  let (tv', reserved') = freshTypeVar reserved
      t' = renameTypeVar tv tv' t
   in replaceTypeVars tvs t' reserved'

-- | Instantiate all quantified type variables with fresh type variables
instantiate :: HasTypeVars a => a -> TypeVars -> (a, TypeVars)
instantiate t reserved =
  let atvs = atv t
      ftvs = ftv t
      quantified = atvs \\ Set.toList ftvs
      conflicting = quantified `intersect` Set.toList reserved
      reserved' = reserved `Set.union` Set.fromList atvs
   in replaceTypeVars conflicting t reserved'

addMissingStack :: Type -> StackId -> TypeVars -> (Type, TypeVars)
addMissingStack (TFn qs mio) s reserved =
  let (tv, reserved') = freshTypeVar reserved
      mio' = Map.insert s (TVar tv, TVar tv) mio
   in (TFn (Set.insert tv qs) mio', reserved')

addMissingStacks :: (Type, Type, TypeVars) -> (Type, Type, TypeVars)
addMissingStacks (TProd l1 r1, TProd l2 r2, reserved) =
  let (l1', l2', reserved2) = addMissingStacks (l1, l2, reserved)
      (r1', r2', reserved3) = addMissingStacks (r1, r2, reserved2)
   in (TProd l1' r1', TProd l2' r2', reserved3)
addMissingStacks (TFn qs1 mio1, TFn qs2 mio2, reserved) =
  let mio12 = Map.intersectionWith (,) mio1 mio2
      (mio12', reserved') = Map.foldrWithKey folder (Map.empty, reserved) mio12
      mio1' = Map.map fst mio12' `Map.union` mio1
      mio2' = Map.map snd mio12' `Map.union` mio2
   in doAdd (TFn qs1 mio1', TFn qs2 mio2', reserved')
  where
    folder s ((i1, o1), (i2, o2)) (m, reserved) =
      let (i1', i2', reserved2) = addMissingStacks (i1, i2, reserved)
          (o1', o2', reserved3) = addMissingStacks (o1, o2, reserved2)
       in (Map.insert s ((i1', o1'), (i2', o2')) m, reserved3)
    doAdd
      ( f1@(TFn _ mio1),
        f2@(TFn _ mio2),
        reserved
        ) =
        let (ks1, ks2) = (Map.keys mio1, Map.keys mio2)
            (f1', reserved') = iter (f1, reserved) (ks2 \\ ks1)
            (f2', reserved'') = iter (f2, reserved') (ks1 \\ ks2)
         in (f1', f2', reserved'')
        where
          iter (f, reserved) [] = (f, reserved)
          iter (f, reserved) (s : ss) = iter (addMissingStack f s reserved) ss
addMissingStacks t = t

------------------
-- Substitution --
------------------

newtype Subst = Subst (Map.Map TypeVar Type)
  deriving (Eq, Ord, Show)

(+->) :: TypeVar -> Type -> Subst
u +-> t = Subst (Map.singleton u t)

class Subs t where
  -- | Apply substitutions with instantiation
  subs :: Subst -> t -> TypeVars -> (t, TypeVars)

instance Subs Type where
  subs (Subst m) (TVar tv) reserved = case Map.lookup tv m of
    Just t -> instantiate t reserved
    Nothing -> (TVar tv, reserved)
  subs s (TProd l r) reserved =
    let ((l', r'), reserved') = subs s (l, r) reserved
     in (TProd l' r', reserved')
  subs s@(Subst m) (TFn qs io) reserved =
    if any (`Map.member` m) qs
      then error "cannot substitute quantified variable"
      else
        let (io', reserved') = subs s io reserved
         in (TFn qs io', reserved')
  subs s (TCons args tc) reserved =
    let (args', reserved') = subs s args reserved
     in (TCons args' tc, reserved')

instance Subs a => Subs [a] where
  subs s ts reserved = foldr helper ([], reserved) ts
    where
      helper t (ts, reserved) =
        let (t', reserved') = subs s t reserved
         in (t' : ts, reserved')

instance (Subs a, Subs b) => Subs (a, b) where
  subs s (a, b) reserved =
    let (a', reserved') = subs s a reserved
        (b', reserved'') = subs s b reserved'
     in ((a', b'), reserved'')

instance (Ord k, Subs v) => Subs (Map.Map k v) where
  subs s m reserved = Map.foldrWithKey folder (Map.empty, reserved) m
    where
      folder k v (m', reserved) =
        let (v', reserved') = subs s v reserved
         in (Map.insert k v' m', reserved')

-- | Compose two substitutions such that:
-- |     subs (composeSubst s2 s1) == subs s2 . subs s1
composeSubst :: Subst -> Subst -> TypeVars -> (Subst, TypeVars)
composeSubst s2@(Subst m2) (Subst m1) reserved =
  let l1 = Map.toList m1
      (l1', reserved') = foldr folder ([], reserved) l1
      m1' = Map.fromList l1'
   in (Subst (m1' `Map.union` m2), reserved')
  where
    folder (tv, t) (sl, reserved) =
      let (t', reserved') = subs s2 t reserved
       in ((tv, t') : sl, reserved')

mergeSubst :: Subst -> Subst -> Subst
mergeSubst (Subst m1) (Subst m2) =
  if and (Map.elems (Map.intersectionWith (==) m1 m2))
    then Subst (Map.union m1 m2)
    else error "substitutions cannot be merged"

-----------------
-- Unification --
-----------------

data UnificationError
  = DoesNotUnify Type Type
  | OccursIn TypeVar Type
  deriving (Eq, Ord, Show)

-- | Find the most general unifier, s, of two Types,
-- | t and t', such that subs s t == subs s' t',
-- | where t and t' do not share any type variables.
mgu :: Type -> Type -> TypeVars -> Either UnificationError (Subst, TypeVars)
mgu (TProd l r) (TProd l' r') reserved = mguList [(l, l'), (r, r')] reserved
mgu f1@TFn {} f2@TFn {} reserved =
  let (TFn _ mio, TFn _ mio', reserved') = addMissingStacks (f1, f2, reserved)
      is = zip (map fst (Map.elems mio)) (map fst (Map.elems mio'))
      os = zip (map snd (Map.elems mio)) (map snd (Map.elems mio'))
   in mguList (is ++ os) reserved'
mgu (TCons args tc) (TCons args' tc') reserved
  | tc == tc' = mguList (zip args args') reserved
mgu t (TVar u) reserved = bindTypeVar u t reserved
mgu (TVar u) t reserved = bindTypeVar u t reserved
mgu t t' _ = throwError $ DoesNotUnify t t'

bindTypeVar :: TypeVar -> Type -> TypeVars -> Either UnificationError (Subst, TypeVars)
bindTypeVar u t reserved
  | TVar u == t = return (Subst Map.empty, reserved)
  | u `elem` ftv t = throwError $ OccursIn u t
  | otherwise = return (u +-> t, reserved)

mguList :: [(Type, Type)] -> TypeVars -> Either UnificationError (Subst, TypeVars)
mguList [] reserved = return (Subst Map.empty, reserved)
mguList ((t1, t2) : ts) reserved = do
  (s1, reserved2) <- mgu t1 t2 reserved
  let (ts', reserved3) = subs s1 ts reserved2
  (s2, reserved4) <- mguList ts' reserved3
  let (s3, reserved5) = composeSubst s2 s1 reserved4
  return (s3, reserved5)

--------------
-- Matching --
--------------

data MatchError
  = DoesNotMatch Type Type
  deriving (Eq, Ord, Show)

-- | Given two Types, t and t', that do not share any type variables,
-- | find the substitution, s, such that subs s t == t'.
match :: Type -> Type -> TypeVars -> Either MatchError (Subst, TypeVars)
match (TProd l r) (TProd l' r') reserved = matchList [(l, l'), (r, r')] reserved
match f1@TFn {} f2@TFn {} reserved =
  let (TFn _ mio, TFn _ mio', reserved') = addMissingStacks (f1, f2, reserved)
      is = zip (map fst (Map.elems mio)) (map fst (Map.elems mio'))
      os = zip (map snd (Map.elems mio)) (map snd (Map.elems mio'))
   in matchList (is ++ os) reserved'
match (TCons args tc) (TCons args' tc') reserved
  | tc == tc' = matchList (zip args args') reserved
match (TVar u) t reserved = return (u +-> t, reserved)
match t t' _ = throwError $ DoesNotMatch t t'

matchList :: [(Type, Type)] -> TypeVars -> Either MatchError (Subst, TypeVars)
matchList [] reserved = return (Subst Map.empty, reserved)
matchList ((t1, t2) : ts) reserved = do
  (s1, reserved2) <- match t1 t2 reserved
  let (ts', reserved3) = subs s1 ts reserved2
  (s2, reserved4) <- matchList ts' reserved3
  let s3 = mergeSubst s2 s1
  return (s3, reserved4)

---------------------------------
-- Intrinsic and Literal Types --
---------------------------------

infixl 2 $.

($.) :: MultiIO -> MultiIO -> MultiIO
($.) = Map.union

infixl 3 $:

($:) :: StackId -> (Type, Type) -> MultiIO
k $: v = Map.singleton k v

infixl 4 -->

(-->) :: Type -> Type -> (Type, Type)
i --> o = (i, o)

infixl 7 *

(*) = TProd

forall :: [Type] -> MultiIO -> Type
forall vs mio =
  let qs = Set.fromList (map (\(TVar tv) -> tv) vs)
   in TFn qs mio

forall' :: [Type] -> (Type, Type) -> Type
forall' vs io = forall vs ("$" $: io)

[v0, v1, v2, v3] = map (TVar . TypeVar) [0 .. 3]

tBool = TCons [] "Bool"

tU32 = TCons [] "U32"

type Context = [StackId]

intrinsicType :: Context -> Intrinsic -> Type
intrinsicType [_] IPush = error "nowhere to push from"
intrinsicType (to : from : _) IPush =
  forall [v0, v1, v2] (from $: v0 * v1 --> v0 $. to $: v2 --> v2 * v1)
intrinsicType [_] IPop = error "nowhere to pop to"
intrinsicType (from : to : _) IPop =
  forall [v0, v1, v2] (from $: v0 * v1 --> v0 $. to $: v2 --> v2 * v1)
intrinsicType (s : _) IClone = forall [v0, v1] (s $: v0 * v1 --> v0 * v1 * v1)
intrinsicType (s : _) IDrop = forall [v0, v1] (s $: v0 * v1 --> v0)
intrinsicType (s : _) IQuote =
  forall [v0, v1] (s $: v0 * v1 --> v0 * forall [v2] (s $: v2 --> v2 * v1))
intrinsicType (s : _) ICompose =
  forall
    [v0, v1, v2, v3]
    ( s $: v0 * forall [] (s $: v1 --> v2) * forall [] (s $: v2 --> v3)
        --> v0 * forall [] (s $: v1 --> v3)
    )
intrinsicType (s : _) IApply =
  forall [v0, v1] (s $: v0 * forall [] (s $: v0 --> v1) --> v1)
intrinsicType (s : _) IAnd =
  forall [v0] (s $: v0 * tBool * tBool --> v0 * tBool)
intrinsicType (s : _) IOr =
  forall [v0] (s $: v0 * tBool * tBool --> v0 * tBool)
intrinsicType (s : _) INot =
  forall [v0] (s $: v0 * tBool --> v0 * tBool)
intrinsicType (s : _) IXor =
  forall [v0] (s $: v0 * tBool * tBool --> v0 * tBool)
intrinsicType (s : _) IIncr =
  forall [v0] (s $: v0 * tU32 --> v0 * tU32)
intrinsicType (s : _) IDecr =
  forall [v0] (s $: v0 * tU32 --> v0 * tU32)
intrinsicType (s : _) IAdd =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tU32)
intrinsicType (s : _) ISub =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tU32)
intrinsicType (s : _) IBitAnd =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tU32)
intrinsicType (s : _) IBitOr =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tU32)
intrinsicType (s : _) IBitNot =
  forall [v0] (s $: v0 * tU32 --> v0 * tU32)
intrinsicType (s : _) IBitXor =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tU32)
intrinsicType (s : _) IShl =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tU32)
intrinsicType (s : _) IShr =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tU32)
intrinsicType (s : _) IEq =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tBool)
intrinsicType (s : _) ILt =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tBool)
intrinsicType (s : _) IGt =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tBool)
intrinsicType (s : _) ILteq =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tBool)
intrinsicType (s : _) IGteq =
  forall [v0] (s $: v0 * tU32 * tU32 --> v0 * tBool)

literalType :: Context -> Literal -> Type
literalType (s : _) (LBool _) = forall [v0] (s $: v0 --> v0 * tBool)
literalType (s : _) (LU32 _) = forall [v0] (s $: v0 --> v0 * tU32)

--------------------
-- Type Inference --
--------------------

data TypeError
  = UnificationError UnificationError
  | MatchError MatchError
  | UndefinedCons ConsId
  | UndefinedFn FnId
  deriving (Eq, Ord, Show)

data Env = Env
  { dataDefs :: Map.Map TypeConsId DataDef,
    typeConsArities :: Map.Map TypeConsId Int,
    consDefs :: Map.Map ConsId ConsDef,
    consTypes :: Map.Map ConsId ([Type], Type),
    fnDefs :: Map.Map FnId FnDef,
    fnTypes :: Map.Map FnId Type
  }
  deriving (Eq, Show)

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty

quoteType :: Context -> Type -> Type
quoteType (s : _) f@TFn {} =
  let (tv, _) = freshTypeVar (Set.fromList (atv f))
      v = TVar tv
   in forall [v] (s $: v --> v * f)

requantify :: Type -> Type
requantify t = recurse t
  where
    count (TVar tv) = Map.singleton tv 1
    count (TProd l r) = Map.unionWith (+) (count l) (count r)
    count (TFn _ mio) =
      let iter (i, o) = Map.unionWith (+) (count i) (count o)
       in foldr1 (Map.unionWith (+)) (map iter (Map.elems mio))
    count (TCons args _) =
      foldr (Map.unionWith (+) . count) Map.empty args
    counts = count t
    recurse t@(TVar _) = t
    recurse (TProd l r) = TProd (recurse l) (recurse r)
    recurse t@(TFn _ mio) =
      let counts' = count t
          deltas = Map.intersectionWith (-) counts counts'
          qs = Set.fromAscList $ Map.keys $ Map.filter (== 0) deltas
          mio' = Map.map (\(i, o) -> (recurse i, recurse o)) mio
          qs' = qs `Set.difference` btv mio'
       in TFn qs' mio'
    recurse t@(TCons _ _) = t -- Tfn is not allowed in TCons args

composeTypes :: [Type] -> Either UnificationError Type
composeTypes [] = return (forall' [v0] (v0 --> v0))
composeTypes [t@TFn {}] = return t
composeTypes (f1@TFn {} : f2@TFn {} : ts) = do
  let (f1', reserved1) = instantiate f1 Set.empty
  let (f2', reserved2) = instantiate f2 reserved1
  let (f1'', f2'', reserved3) = addMissingStacks (f1', f2', reserved2)
  let (TFn _ mio1, TFn _ mio2) = (f1'', f2'')
  let o1i2s = zip (map snd (Map.elems mio1)) (map fst (Map.elems mio2))
  (s, reserved4) <- mguList o1i2s reserved3
  let i1o2s = zip (map fst (Map.elems mio1)) (map snd (Map.elems mio2))
  let (io3s, _) = subs s i1o2s reserved4
  let mio3 = Map.fromDistinctAscList (zip (Map.keys mio1) io3s)
  let t3 = requantify (TFn Set.empty mio3)
  composeTypes (t3 : ts)

-- ensure unique StackIds by prepending "$", creating a temporary StackId
ensureUniqueStackId :: Context -> StackId -> StackId
ensureUniqueStackId ctx s | s `elem` ctx = ensureUniqueStackId ctx ('$' : s)
ensureUniqueStackId ctx s = s

stackTypes :: [Type] -> Type
stackTypes [t] = t
stackTypes (t : t' : ts) = iter (TProd t t') ts
  where
    iter t [] = t
    iter t (t' : ts) = iter (TProd t t') ts

patternType :: Env -> Context -> Pattern -> Either TypeError Type
patternType env (s : _) p = do
  (is, os) <- patternTypes env p
  let (tv, _) = freshTypeVar (Set.fromList (atv (is, os)))
      v = TVar tv
      i = stackTypes (v : is)
      o = stackTypes (v : os)
  return (requantify (TFn Set.empty (s $: i --> o)))
  where
    patternTypes :: Env -> Pattern -> Either TypeError ([Type], [Type])
    patternTypes env PEmpty = return ([], [])
    patternTypes env (PProd l r) = do
      (li, lo) <- patternTypes env l
      (ri, ro) <- patternTypes env r
      return (li ++ ri, lo ++ ro)
    patternTypes env (PLit (LBool _)) = return ([tBool], [])
    patternTypes env (PLit (LU32 _)) = return ([tU32], [])
    patternTypes Env {consTypes} (PCons cid) = case Map.lookup cid consTypes of
      Nothing -> throwError (UndefinedCons cid)
      -- Note: ECons inputs are PCons outputs
      Just (inTypes, outType) -> return ([outType], inTypes)

caseType :: Env -> Context -> (Pattern, Expr) -> Either TypeError Type
caseType env ctx (p, e) = do
  pt <- patternType env ctx p
  et <- inferType env ctx e
  mapLeft UnificationError (composeTypes [pt, et])

unifyCaseTypes :: [Type] -> Either UnificationError Type
unifyCaseTypes [] = error "empty match"
unifyCaseTypes [t@TFn {}] = return t
unifyCaseTypes (f1@TFn {} : f2@TFn {} : ts) = do
  let (f1', reserved1) = instantiate f1 Set.empty
  let (f2', reserved2) = instantiate f2 reserved1
  let (f1'', f2'', reserved3) = addMissingStacks (f1', f2', reserved2)
  (s, reserved4) <- mgu f1'' f2'' reserved3
  let TFn _ mio1 = f1''
  let (mio3, _) = subs s mio1 reserved4
  let t3 = requantify (TFn Set.empty mio3)
  unifyCaseTypes (t3 : ts)

getEConsType :: Env -> Context -> ConsId -> Either TypeError Type
getEConsType Env {consTypes} (s : _) cid = case Map.lookup cid consTypes of
  Nothing -> throwError (UndefinedCons cid)
  Just (inTypes, outType) ->
    let (tv, _) = freshTypeVar (Set.fromList (atv (inTypes, outType)))
        v = TVar tv
        i = stackTypes (v : inTypes)
     in return (requantify (TFn Set.empty (s $: i --> v * outType)))

getECallType :: Env -> FnId -> Either TypeError Type
getECallType Env {fnTypes} fid = case Map.lookup fid fnTypes of
  Nothing -> throwError (UndefinedFn fid)
  Just t -> return t

-- | Infer an expression's type in the given Env and Context.
-- | UndefinedFn is only thrown if the call occurs outside of
-- | a match or if all match cases call an undefined function.
inferType :: Env -> Context -> Expr -> Either TypeError Type
inferType env ctx (EIntrinsic i) = return $ intrinsicType ctx i
inferType env ctx (EQuote e) = do
  t <- inferType env ctx e
  return (quoteType ctx t)
inferType env ctx (ECompose es) = do
  ts <- mapM (inferType env ctx) es
  mapLeft UnificationError (composeTypes ts)
inferType env ctx (EContext s e) =
  inferType env (ensureUniqueStackId ctx s : ctx) e
inferType env ctx (ELit l) = return $ literalType ctx l
inferType env ctx (EMatch cases) = case map (caseType env ctx) cases of
  rs | all isUndefinedFnError rs -> head (filter isUndefinedFnError rs)
  rs | any isOtherError rs -> head (filter isOtherError rs)
  rs -> do
    ts <- sequence (filter isRight rs)
    mapLeft UnificationError (unifyCaseTypes ts)
  where
    isUndefinedFnError (Left (UndefinedFn _)) = True
    isUndefinedFnError _ = False
    isOtherError (Left (UndefinedFn _)) = False
    isOtherError (Left _) = True
    isOtherError _ = False
inferType env ctx (ECons cid) = getEConsType env ctx cid
inferType env ctx (ECall fid) = getECallType env fid

-------------------
-- Type Checking --
-------------------

strictCaseType :: Env -> Context -> (Pattern, Expr) -> Either TypeError Type
strictCaseType env ctx (p, e) = do
  pt <- patternType env ctx p
  et <- strictInferType env ctx e
  mapLeft UnificationError (composeTypes [pt, et])

-- | Infer an expression's type in the given Env and Context.
-- | UndefinedFn is thrown for any undefined function call.
strictInferType :: Env -> Context -> Expr -> Either TypeError Type
strictInferType env ctx (EQuote e) = do
  t <- strictInferType env ctx e
  return (quoteType ctx t)
strictInferType env ctx (ECompose es) = do
  ts <- mapM (strictInferType env ctx) es
  mapLeft UnificationError (composeTypes ts)
strictInferType env ctx (EContext s e) =
  strictInferType env (ensureUniqueStackId ctx s : ctx) e
strictInferType env ctx (EMatch cases) = do
  ts <- mapM (caseType env ctx) cases
  mapLeft UnificationError (unifyCaseTypes ts)
strictInferType env ctx e = inferType env ctx e

-- | Check an expression's type in the given Env and Context.
checkType :: Env -> Context -> Expr -> Type -> Either TypeError ()
checkType env ctx e f1 = do
  f2 <- strictInferType env ctx e
  let (f1', reserved1) = instantiate f1 Set.empty
  let (f2', reserved2) = instantiate f2 reserved1
  let (f1'', f2'', reserved3) = addMissingStacks (f1', f2', reserved2)
  void (mapLeft MatchError (match f2'' f1'' reserved3))

------------------------
-- Type Normalization --
------------------------

removeTrivialStacks :: Type -> Type
removeTrivialStacks t = recurse t
  where
    recurse t@(TVar _) = t
    recurse (TProd l r) = TProd (recurse l) (recurse r)
    recurse t@(TFn qs mio) =
      let mio' = Map.filter (not . isTrivial qs) mio
          mio'' = if null mio' then Map.fromAscList [head (Map.toAscList mio)] else mio'
          mio''' = Map.map (\(i, o) -> (recurse i, recurse o)) mio''
       in requantify (TFn Set.empty mio''')
    recurse t@(TCons _ _) = t -- Tfn is not allowed in TCons args
    isTrivial qs (TVar i, TVar o) | i `elem` qs && o `elem` qs = True
    isTrivial _ _ = False

normalizeTypeVars :: Type -> Type
normalizeTypeVars t =
  if not $ null $ ftv t
    then error "unexpected free type variables"
    else
      let (t', _) = instantiate t Set.empty
          maxId = maximum $ map (\(TypeVar id) -> id) (atv t')
          (t'', _) = instantiate t' (Set.fromList (map TypeVar [0 .. maxId]))
          (t''', _) = replaceTypeVars (atv t'') t'' Set.empty
       in t'''

normalizeType :: Type -> Type
normalizeType = normalizeTypeVars . removeTrivialStacks

inferNormType :: Env -> Context -> Expr -> Either TypeError Type
inferNormType env ctx e = do
  t <- inferType env ctx e
  return (normalizeType t)

-------------------------
-- Function Definition --
-------------------------

data FnDef = FnDef FnId Expr
  deriving (Eq, Show)

type StackIds = Set.Set StackId

type FnIds = Set.Set FnId

intrinsicFnId :: Intrinsic -> FnId
intrinsicFnId IPush = "push"
intrinsicFnId IPop = "pop"
intrinsicFnId IClone = "clone"
intrinsicFnId IDrop = "drop"
intrinsicFnId IQuote = "quote"
intrinsicFnId ICompose = "compose"
intrinsicFnId IApply = "apply"
intrinsicFnId IAnd = "and"
intrinsicFnId IOr = "or"
intrinsicFnId INot = "not"
intrinsicFnId IXor = "xor"
intrinsicFnId IIncr = "incr"
intrinsicFnId IDecr = "decr"
intrinsicFnId IAdd = "add"
intrinsicFnId ISub = "sub"
intrinsicFnId IBitAnd = "bit_and"
intrinsicFnId IBitOr = "bit_or"
intrinsicFnId IBitNot = "bit_not"
intrinsicFnId IBitXor = "bit_xor"
intrinsicFnId IShl = "shl"
intrinsicFnId IShr = "shr"
intrinsicFnId IEq = "eq"
intrinsicFnId ILt = "lt"
intrinsicFnId IGt = "gt"
intrinsicFnId ILteq = "lteq"
intrinsicFnId IGteq = "gteq"

intrinsicFnIds =
  Set.fromList
    [ "push",
      "pop",
      "clone",
      "drop",
      "quote",
      "compose",
      "apply",
      "and",
      "or",
      "not",
      "xor",
      "incr",
      "decr",
      "add",
      "sub",
      "bit_and",
      "bit_or",
      "bit_not",
      "bit_xor",
      "shl",
      "shr",
      "eq",
      "lt",
      "gt",
      "lteq",
      "gteq"
    ]

data FnDefError
  = FnAlreadyDefined FnId
  | FnTypeError FnId TypeError
  | FnStackError FnId StackIds
  deriving (Eq, Show)

tempStackIds :: Type -> StackIds
tempStackIds (TVar _) = Set.empty
tempStackIds (TProd l r) =
  tempStackIds l `Set.union` tempStackIds r
tempStackIds (TFn _ mio) =
  let sids = Set.filter ("$$" `isPrefixOf`) (Map.keysSet mio)
      folder (i, o) acc =
        tempStackIds i `Set.union` tempStackIds o `Set.union` acc
      sids' = foldr folder Set.empty (Map.elems mio)
   in sids `Set.union` sids'
tempStackIds (TCons _ _) = Set.empty -- Tfn is not allowed in TCons args

fnDefFnId :: FnDef -> FnId
fnDefFnId (FnDef fid _) = fid

fnDefExpr :: FnDef -> Expr
fnDefExpr (FnDef _ e) = e

fnDepsF :: (FnIds -> FnIds -> FnIds) -> Expr -> FnIds
fnDepsF mergeCases = helper
  where
    helper (EIntrinsic _) = Set.empty
    helper (EQuote e) = helper e
    helper (ECompose es) =
      foldr (Set.union . helper) Set.empty es
    helper (EContext s e) = helper e
    helper (ELit _) = Set.empty
    helper (EMatch cs) =
      let caseDeps = map (uncondFnDeps . snd) cs
       in foldr1 mergeCases caseDeps
    helper (ECons cid) = Set.empty
    helper (ECall fid) = Set.singleton fid

fnDeps :: Expr -> FnIds
fnDeps = fnDepsF Set.union

uncondFnDeps :: Expr -> FnIds
uncondFnDeps = fnDepsF Set.intersection

-- | Sort FnDef's such that f precedes g if f depends on g
-- | (directly or transitively) and g does not depend on f,
-- | or if f unconditionally depends on g and g does not
-- | unconditionally depend on f.
fnDepsSort :: [FnDef] -> [FnDef]
fnDepsSort defs =
  let (uncondDepsGraph, _, uncondDepsFidToVert) =
        graphFromEdges (map (fnDefToEdgeList uncondFnDeps) defs)
      (depsGraph, depsVertToTuple, depsFidToVert) =
        graphFromEdges (map (fnDefToEdgeList fnDeps) defs)
      dependencySortFns defs =
        let tupleToFnDef (def, _, _) = def
            vertToFnDef v = tupleToFnDef (depsVertToTuple v)
         in map vertToFnDef (topSort depsGraph)
      fnDepsOrdering f g =
        let (fid, gid) = (fnDefFnId f, fnDefFnId g)
            (Just fuv, Just guv) = (uncondDepsFidToVert fid, uncondDepsFidToVert gid)
            (Just fav, Just gav) = (depsFidToVert fid, depsFidToVert gid)
            fUncondDepsG = path uncondDepsGraph fuv guv
            gUncondDepsF = path uncondDepsGraph guv fuv
            fDepsG = path depsGraph fav gav
            gDepsF = path depsGraph gav fav
         in case (fUncondDepsG, gUncondDepsF, fDepsG, gDepsF) of
              (False, False, False, False) -> EQ
              (False, False, False, True) -> GT
              (False, False, True, False) -> LT
              (False, False, True, True) -> EQ
              (False, True, False, True) -> GT
              (False, True, True, True) -> GT
              (True, False, True, False) -> LT
              (True, False, True, True) -> LT
              (True, True, True, True) -> EQ
              _ -> error "unreachable"
   in sortBy fnDepsOrdering (dependencySortFns defs)
  where
    fnDefToEdgeList exprToDeps def@(FnDef fid e) = (def, fid, Set.toList (exprToDeps e))

defineFns :: Env -> [FnDef] -> ([FnDefError], Env)
defineFns env@Env {fnDefs} defs =
  let existingFnIds = Map.keysSet fnDefs `Set.union` intrinsicFnIds
      (errs1, defs') = removeAlreadyDefined existingFnIds defs
      newFnIds = Set.fromList (map fnDefFnId defs')
      sortedDefs = fnDepsSort defs'
      (errs2, env2, sortedDefs') = foldr (inferTypes newFnIds) ([], env, []) sortedDefs
      (errs3, env3, sortedDefs'') = foldr (inferTypes newFnIds) ([], env2, []) sortedDefs'
      (errs4, env4) = foldr (checkTypes newFnIds) ([], env3) sortedDefs''
   in (errs1 ++ errs2 ++ errs3 ++ errs4, env4)
  where
    removeAlreadyDefined :: FnIds -> [FnDef] -> ([FnDefError], [FnDef])
    removeAlreadyDefined fids [] = ([], [])
    removeAlreadyDefined fids (FnDef fid e : defs) =
      let (errs, defs') = removeAlreadyDefined (Set.insert fid fids) defs
       in if fid `Set.member` fids
            then (FnAlreadyDefined fid : errs, defs')
            else (errs, FnDef fid e : defs)

    inferTypes :: FnIds -> FnDef -> ([FnDefError], Env, [FnDef]) -> ([FnDefError], Env, [FnDef])
    inferTypes newFnIds def@(FnDef fid e) (errs, env@Env {fnDefs, fnTypes}, defs) =
      case inferNormType env ["$"] e of
        Left err -> (FnTypeError fid err : errs, env, defs)
        Right t
          | not (null (tempStackIds t)) ->
            (FnStackError fid (tempStackIds t) : errs, env, defs)
        Right t ->
          let fnDefs' = Map.insert fid def fnDefs
              fnTypes' = Map.insert fid t fnTypes
              env' = env {fnDefs = fnDefs', fnTypes = fnTypes'}
           in (errs, env', def : defs)

    checkTypes :: FnIds -> FnDef -> ([FnDefError], Env) -> ([FnDefError], Env)
    checkTypes newFnIds (FnDef fid e) (errs, env@Env {fnTypes}) =
      case checkType env ["$"] e (fnTypes Map.! fid) of
        Left err -> (FnTypeError fid err : errs, env {fnTypes = Map.delete fid fnTypes})
        Right () -> (errs, env)

defineFn :: Env -> FnDef -> Either FnDefError Env
defineFn env def = case defineFns env [def] of
  ([], env') -> return env'
  ([err], _) -> throwError err

------------------------------------
-- Algebraic Data Type Definition --
------------------------------------

data DataDef = DataDef [TypeVar] TypeConsId [ConsDef]
  deriving (Eq, Show)

data ConsDef = ConsDef [Type] ConsId
  deriving (Eq, Show)

data DataDefError
  = TypeConsAlreadyDefined TypeConsId
  | ConsAlreadyDefined TypeConsId ConsId
  | DuplicateTypeVar TypeConsId TypeVar
  | UndefinedTypeVar TypeConsId TypeVar
  | UndefinedTypeCons TypeConsId
  | TypeConsArityMismatch TypeConsId Type
  deriving (Eq, Show)

type TypeConsIds = Set.Set TypeConsId

type ConsIds = Set.Set ConsId

addDataDefs :: Env -> [DataDef] -> ([DataDefError], Env)
addDataDefs env@Env {dataDefs, consDefs} defs =
  let existingTypeConsIds = Map.keysSet dataDefs
      (errs1, defs1) = removeTypeConsAlreadyDefined (Map.keysSet dataDefs) defs
      (errs2, defs2) = removeConsAlreadyDefined (Map.keysSet consDefs) defs1
      env' = addDataDefs' env defs2
      (errs3, defs3) = removeOtherErrors env' defs2
      env'' = addDataDefs' env defs3
   in (errs1 ++ errs2 ++ errs3, env'')
  where
    removeTypeConsAlreadyDefined :: TypeConsIds -> [DataDef] -> ([DataDefError], [DataDef])
    removeTypeConsAlreadyDefined tcids [] = ([], [])
    removeTypeConsAlreadyDefined tcids (DataDef args tcid consDefs : defs) =
      let (errs, defs') = removeTypeConsAlreadyDefined (Set.insert tcid tcids) defs
       in if tcid `Set.member` tcids
            then (TypeConsAlreadyDefined tcid : errs, defs')
            else (errs, DataDef args tcid consDefs : defs)

    removeConsAlreadyDefined :: ConsIds -> [DataDef] -> ([DataDefError], [DataDef])
    removeConsAlreadyDefined cids [] = ([], [])
    removeConsAlreadyDefined cids (def@(DataDef args tcid consDefs) : defs) =
      let newConsIds = Set.fromList (map (\(ConsDef _ cid) -> cid) consDefs)
          cids' = cids `Set.union` newConsIds
          (errs, defs') = removeConsAlreadyDefined cids' defs
       in case checkConsDefs consDefs of
            Left err -> (err : errs, defs')
            Right () -> (errs, def : defs')
      where
        checkConsDefs :: [ConsDef] -> Either DataDefError ()
        checkConsDefs = mapM_ checkDef

        checkDef :: ConsDef -> Either DataDefError ()
        checkDef (ConsDef _ cid)
          | cid `Set.member` cids = throwError (ConsAlreadyDefined tcid cid)
        checkDef _ = return ()

    addDataDefs' :: Env -> [DataDef] -> Env
    addDataDefs' = foldr addDataDef
      where
        addDataDef
          def@(DataDef tvs tcid newConsDefs)
          env@Env {dataDefs, typeConsArities, consDefs, consTypes} =
            let dataDefs' = Map.insert tcid def dataDefs
                typeConsArities' = Map.insert tcid (length tvs) typeConsArities
                consDefs' = foldr addConsDef consDefs newConsDefs
                addConsDef def@(ConsDef _ cid) = Map.insert cid def
                consTypes' = foldr addConsType consTypes newConsDefs
                addConsType def@(ConsDef args cid) =
                  Map.insert cid (args, TCons (map TVar tvs) tcid)
             in env
                  { dataDefs = dataDefs',
                    typeConsArities = typeConsArities',
                    consDefs = consDefs',
                    consTypes = consTypes'
                  }

    removeOtherErrors :: Env -> [DataDef] -> ([DataDefError], [DataDef])
    removeOtherErrors env [] = ([], [])
    removeOtherErrors env (def : defs) =
      let (errs, defs') = removeOtherErrors env defs
       in case checkEach env def of
            Left err -> (err : errs, defs')
            Right () -> (errs, def : defs')

    checkEach :: Env -> DataDef -> Either DataDefError ()
    checkEach env@Env {dataDefs, typeConsArities} def = do
      _ <- checkDuplicateTypeVar def
      _ <- checkUndefinedTypeVar def
      _ <- checkTypeCons typeConsArities def
      return ()

    checkDuplicateTypeVar :: DataDef -> Either DataDefError ()
    checkDuplicateTypeVar (DataDef args tcid consDefs) =
      check Set.empty args
      where
        check :: TypeVars -> [TypeVar] -> Either DataDefError ()
        check tvs [] = return ()
        check tvs (tv : tvl)
          | tv `Set.member` tvs = throwError (DuplicateTypeVar tcid tv)
        check tvs (tv : tvl) = check (Set.insert tv tvs) tvl

    checkUndefinedTypeVar :: DataDef -> Either DataDefError ()
    checkUndefinedTypeVar (DataDef args tcid consDefs) =
      mapM_ (checkConsDef (Set.fromList args)) consDefs
      where
        checkConsDef :: TypeVars -> ConsDef -> Either DataDefError ()
        checkConsDef tvs (ConsDef args cid) = mapM_ (checkVar tvs) (atv args)

        checkVar :: TypeVars -> TypeVar -> Either DataDefError ()
        checkVar tvs tv | not (tv `Set.member` tvs) = throwError (UndefinedTypeVar tcid tv)
        checkVar tvs tv = return ()

    checkTypeCons :: Map.Map TypeConsId Int -> DataDef -> Either DataDefError ()
    checkTypeCons typeConsArities (DataDef _ tcid consDefs) =
      mapM_ checkConsDef consDefs
      where
        checkConsDef (ConsDef args _) = mapM_ checkArg args
        checkArg :: Type -> Either DataDefError ()
        checkArg (TVar _) = return ()
        checkArg (TCons args tcid)
          | not (tcid `Map.member` typeConsArities) =
            throwError (UndefinedTypeCons tcid)
        checkArg t@(TCons args tcid)
          | length args /= (typeConsArities Map.! tcid) =
            throwError (TypeConsArityMismatch tcid t)
        checkArg (TCons args tcid) = mapM_ checkArg args
