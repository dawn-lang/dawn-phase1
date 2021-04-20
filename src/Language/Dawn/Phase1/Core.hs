-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# LANGUAGE NamedFieldPuns #-}

module Language.Dawn.Phase1.Core
  ( (-->),
    (*),
    (+->),
    ($:),
    ($.),
    addMissingStacks,
    checkType,
    composeSubst,
    ConsDef (..),
    ConsId,
    Context,
    DataDef (..),
    DataDefError (..),
    defaultMultiStack,
    Element (..),
    emptyEnv,
    ensureUniqueStackId,
    Env (..),
    Expr (..),
    FnDecl (..),
    FnDeclError (..),
    FnDef (..),
    FnDefError (..),
    fnDefExpr,
    fnDefFnId,
    fnDeps,
    FnId,
    FnIds,
    forall,
    forall',
    freshTypeVar,
    fromStack,
    HasTypeVars (..),
    Include (..),
    inferNormType,
    inferType,
    instantiate,
    Intrinsic (..),
    intrinsicType,
    MatchError (..),
    mgu,
    MultiIO,
    MultiStack (..),
    normalizeType,
    Pattern (..),
    removeTrivialStacks,
    replaceTypeVars,
    requantify,
    Stack (..),
    stackAppend,
    StackId,
    StackIds,
    stackTypes,
    Subs (..),
    Subst (..),
    tempStackIds,
    TestDef (..),
    TestDefError (..),
    toStack,
    tryAddDataDefs,
    tryAddFnDecls,
    tryAddFnDefs,
    tryAddTestDef,
    tryAddTestDefs,
    Type (..),
    TypeConsId,
    TypeError (..),
    TypeVar (..),
    TypeVars,
    fnUDeps,
    UnificationError (..),
    UnivQuants,
    URIRef (..),
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

---------------
-- Utilities --
---------------

data Stack a
  = Empty
  | Stack a :*: a
  deriving (Eq, Ord, Show)

instance Foldable Stack where
  foldMap f Empty = mempty
  foldMap f (a :*: b) = foldMap f a `mappend` f b

toStack :: [a] -> Stack a
toStack vs = toStack' (reverse vs)
  where
    toStack' [] = Empty
    toStack' (v : vs) = toStack' vs :*: v

fromStack :: Stack a -> [a]
fromStack vs = reverse (fromStack' vs)
  where
    fromStack' Empty = []
    fromStack' (vs :*: v) = v : fromStack' vs

stackAppend :: Stack a -> Stack a -> Stack a
a `stackAppend` Empty = a
a `stackAppend` (bs :*: b) = (a `stackAppend` bs) :*: b

newtype MultiStack a = MultiStack (Map.Map StackId (Stack a))
  deriving (Eq, Show)

defaultMultiStack :: Stack a -> MultiStack a
defaultMultiStack s = MultiStack (Map.singleton "$" s)

---------------------
-- Abstract Syntax --
---------------------

-- | Expressions
data Expr
  = EIntrinsic Intrinsic
  | EQuote Expr
  | ECompose [Expr]
  | EContext StackId Expr
  | EMatch [(MultiStack Pattern, Expr)]
  | ECons ConsId
  | ECall FnId
  deriving (Eq, Show)

data Pattern
  = PCons (Stack Pattern) ConsId
  | PWild
  deriving (Eq, Show)

data Intrinsic
  = IPush
  | IPop
  | IClone
  | IDrop
  | IQuote
  | ICompose
  | IApply
  deriving (Eq, Ord, Show)

data Type
  = TVar TypeVar
  | TProd Type Type
  | TFn UnivQuants MultiIO
  | TCons [Type] TypeConsId
  deriving (Eq, Show)

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

instance HasTypeVars a => HasTypeVars (Stack a) where
  renameTypeVar from to ts = toStack (renameTypeVar from to (fromStack ts))
  ftv = ftv . fromStack
  btv = btv . fromStack
  atv = atv . fromStack

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

-- | Instantiate quantified type variables with fresh type variables
instantiate :: HasTypeVars a => a -> TypeVars -> (a, TypeVars)
instantiate t reserved =
  let atvs = atv t
      ftvs = ftv t
      quantified = atvs \\ Set.toList ftvs
      conflicting = quantified `intersect` Set.toList reserved
      reserved' = reserved `Set.union` Set.fromList atvs
   in replaceTypeVars conflicting t reserved'

-- | Instantiate all type variables with fresh type variables
instantiateAll :: HasTypeVars a => a -> TypeVars -> (a, TypeVars)
instantiateAll t reserved =
  let atvs = atv t
      reserved' = reserved `Set.union` Set.fromList atvs
   in replaceTypeVars atvs t reserved'

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
  deriving (Eq, Show)

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

instance Subs a => Subs (Stack a) where
  subs s ts reserved =
    let (ts', reserved') = subs s (fromStack ts) reserved
     in (toStack ts', reserved')

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
  deriving (Eq, Show)

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
  deriving (Eq, Show)

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

---------------------
-- Intrinsic Types --
---------------------

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

--------------------
-- Type Inference --
--------------------

data TypeError
  = UnificationError UnificationError
  | MatchError MatchError
  | UndefinedCons ConsId
  | UndefinedFn FnId
  | PatternArityMismatch ConsId Pattern
  deriving (Eq, Show)

data Env = Env
  { dataDefs :: Map.Map TypeConsId DataDef,
    typeConsArities :: Map.Map TypeConsId Int,
    consDefs :: Map.Map ConsId ConsDef,
    consTypes :: Map.Map ConsId ([Type], Type),
    fnDecls :: Map.Map FnId FnDecl,
    fnDefs :: Map.Map FnId FnDef,
    fnTypes :: Map.Map FnId Type,
    testDefs :: [TestDef]
  }
  deriving (Eq, Show)

emptyEnv :: Env
emptyEnv =
  Env Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty []

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

patternMultiStackType :: Env -> Context -> MultiStack Pattern -> Either TypeError Type
patternMultiStackType env@Env {consTypes} ctx@(s : _) (MultiStack m) = do
  (stackTypes, reserved) <- patternStackTypes (Map.toList m) Set.empty
  let folder ("$", io) (mio, reserved) = (Map.insert s io mio, reserved)
      folder (sid, io) (mio, reserved) =
        (Map.insert (ensureUniqueStackId ctx sid) io mio, reserved)
  let (mio, reserved') = foldr folder (Map.empty, reserved) stackTypes
  return (requantify (TFn Set.empty mio))
  where
    patternStackTypes ::
      [(StackId, Stack Pattern)] ->
      TypeVars ->
      Either TypeError ([(StackId, (Type, Type))], TypeVars)
    patternStackTypes [] reserved = return ([], reserved)
    patternStackTypes ((sid, ps) : pss) reserved = do
      (stackTypes, reserved') <- patternStackTypes pss reserved
      (i, o, reserved'') <- patternStackType ps reserved'
      let stackTypes' = (sid, (i, o)) : stackTypes
      return (stackTypes', reserved'')

    patternStackType :: Stack Pattern -> TypeVars -> Either TypeError (Type, Type, TypeVars)
    patternStackType ps reserved = do
      (pts, reserved') <- patternTypes ps reserved
      let (inTypes, outTypes) = unzip pts
      let (tv, reserved'') = freshTypeVar reserved'
          v = TVar tv
          i = stackTypes (v : inTypes)
          o = stackTypes (v : concat outTypes)
      return (i, o, reserved'')

    patternTypes :: Stack Pattern -> TypeVars -> Either TypeError ([(Type, [Type])], TypeVars)
    patternTypes Empty reserved = return ([], reserved)
    patternTypes (ps :*: p) reserved = do
      (ts, reserved') <- patternTypes ps reserved
      (it, ots, reserved'') <- patternType p reserved'
      return (ts ++ [(it, ots)], reserved'')

    patternType :: Pattern -> TypeVars -> Either TypeError (Type, [Type], TypeVars)
    patternType p@(PCons args cid) reserved = case Map.lookup cid consTypes of
      Nothing -> throwError (UndefinedCons cid)
      Just (eConsInTypes, eConsOutType)
        | not (null args) && length args /= length eConsInTypes ->
          throwError (PatternArityMismatch cid p)
      Just (eConsInTypes, eConsOutType) -> do
        let ((inType, outTypes), reserved1) = instantiateAll (eConsOutType, eConsInTypes) reserved
        (argsTypes, reserved2) <- patternTypes args reserved1
        let (argInTypes, argOutTypesList) = unzip argsTypes
        let (unmatchedOutTypes, matchedOutTypes) = splitAt (length outTypes - length args) outTypes
        (s, reserved3) <- mapLeft UnificationError (mguList (zip argInTypes matchedOutTypes) reserved2)
        let outTypes' = unmatchedOutTypes ++ concat argOutTypesList
        let ((inType', outTypes''), reserved4) = subs s (inType, outTypes') reserved3
        return (inType', outTypes'', reserved4)
    patternType PWild reserved =
      let (tv, reserved') = freshTypeVar reserved
       in return (TVar tv, [TVar tv], reserved')

caseType :: Env -> Context -> (MultiStack Pattern, Expr) -> Either TypeError Type
caseType env ctx (p, e) = do
  pt <- patternMultiStackType env ctx p
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

getECallType :: Env -> Context -> FnId -> Either TypeError Type
getECallType Env {fnTypes} ctx fid = case Map.lookup fid fnTypes of
  Nothing -> throwError (UndefinedFn fid)
  Just t -> return (getFnTypeInContext ctx t)

getFnTypeInContext :: Context -> Type -> Type
getFnTypeInContext ctx@(s : _) (TFn qs mio) = TFn qs (Map.mapKeys mapper mio)
  where
    mapper "$" = s
    mapper sid = ensureUniqueStackId ctx sid

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
inferType env ctx (ECall fid) = getECallType env ctx fid

-------------------
-- Type Checking --
-------------------

strictCaseType :: Env -> Context -> (MultiStack Pattern, Expr) -> Either TypeError Type
strictCaseType env ctx (p, e) = do
  pt <- patternMultiStackType env ctx p
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

-----------------------------------------
-- Function Declaration and Definition --
-----------------------------------------

data FnDecl = FnDecl FnId Type
  deriving (Eq, Show)

data FnDef = FnDef FnId Expr
  deriving (Eq, Show)

data FnDeclError
  = FnAlreadyDeclared FnId
  | FnDeclDuplicate FnId
  | FnDeclTempStack FnId StackIds
  deriving (Eq, Show)

data FnDefError
  = FnAlreadyDefined FnId
  | FnDefDuplicate FnId
  | UncondCallCycle [FnId]
  | FnTypeError FnId TypeError
  | FnDefTempStack FnId StackIds
  deriving (Eq, Show)

type StackIds = Set.Set StackId

type FnIds = Set.Set FnId

intrinsicFnIds =
  Set.fromList
    [ "push",
      "pop",
      "clone",
      "drop",
      "quote",
      "compose",
      "apply"
    ]

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

checkStackError :: Type -> Either StackIds ()
checkStackError t | null (tempStackIds t) = return ()
checkStackError t = throwError (tempStackIds t)

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = iter Set.empty
  where
    iter seen [] = Nothing
    iter seen (a : as) | a `Set.member` seen = Just a
    iter seen (a : as) = iter (Set.insert a seen) as

fnDeclFnId :: FnDecl -> FnId
fnDeclFnId (FnDecl fid _) = fid

tryAddFnDecl :: Env -> FnDecl -> Either FnDeclError Env
tryAddFnDecl env (FnDecl fid t)
  | fid `Set.member` intrinsicFnIds =
    throwError (FnAlreadyDeclared fid)
tryAddFnDecl env@Env {fnDecls} (FnDecl fid t)
  | fid `Map.member` fnDecls =
    throwError (FnAlreadyDeclared fid)
tryAddFnDecl env@Env {fnDecls, fnTypes} decl@(FnDecl fid t) = do
  mapLeft (FnDeclTempStack fid) (checkStackError t)
  let fnDecls' = Map.insert fid decl fnDecls
      fnTypes' = Map.insert fid t fnTypes
  return (env {fnDecls = fnDecls', fnTypes = fnTypes'})

tryAddFnDecls :: Env -> [FnDecl] -> Either FnDeclError Env
tryAddFnDecls env decls = do
  checkDuplicates decls
  foldM tryAddFnDecl env decls
  where
    checkDuplicates :: [FnDecl] -> Either FnDeclError ()
    checkDuplicates decls = case firstDuplicate (map fnDeclFnId decls) of
      Nothing -> return ()
      Just fid -> throwError (FnDeclDuplicate fid)

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
    helper (EMatch cs) =
      let caseDeps = map (fnDepsF mergeCases . snd) cs
       in foldr1 mergeCases caseDeps
    helper (ECons cid) = Set.empty
    helper (ECall fid) = Set.singleton fid

-- | Dependencies (conditional + unconditional)
fnDeps :: Expr -> FnIds
fnDeps = fnDepsF Set.union

-- | Unconditional dependencies
fnUDeps :: Expr -> FnIds
fnUDeps = fnDepsF Set.intersection

tryAddFnDefs :: Env -> [FnDef] -> Either FnDefError Env
tryAddFnDefs env@Env {fnDefs, fnTypes} defs = do
  mapM_ checkAlreadyDefined defs
  checkDuplicates defs
  let unknownType (FnDef fid _) = not (fid `Map.member` fnTypes)
      defsWithoutTypes = filter unknownType defs
      defToDeps d@(FnDef fid e) = (d, fid, Set.toList (fnDeps e))
      sccs = stronglyConnComp (map defToDeps defsWithoutTypes)
      defToUDeps d@(FnDef fid e) = (d, fid, Set.toList (fnUDeps e))
      mapper (AcyclicSCC v) = AcyclicSCC (AcyclicSCC v)
      mapper (CyclicSCC vs) = CyclicSCC (stronglyConnComp (map defToUDeps vs))
      sccs' = map mapper sccs
  env' <- inferFnTypes env sccs'
  checkFnTypes env' defs
  let fnDefs' = foldr (\def@(FnDef fid _) -> Map.insert fid def) fnDefs defs
  return env' {fnDefs = fnDefs'}
  where
    checkAlreadyDefined :: FnDef -> Either FnDefError ()
    checkAlreadyDefined (FnDef fid t)
      | fid `Set.member` intrinsicFnIds = throwError (FnAlreadyDefined fid)
    checkAlreadyDefined (FnDef fid t)
      | fid `Map.member` fnDefs = throwError (FnAlreadyDefined fid)
    checkAlreadyDefined def = return ()

    checkDuplicates :: [FnDef] -> Either FnDefError ()
    checkDuplicates defs = case firstDuplicate (map fnDefFnId defs) of
      Nothing -> return ()
      Just fid -> throwError (FnDefDuplicate fid)

    inferFnTypes :: Env -> [SCC (SCC FnDef)] -> Either FnDefError Env
    inferFnTypes env [] = return env
    inferFnTypes env (AcyclicSCC (AcyclicSCC def) : sccs) = do
      env' <- inferFnType env def
      inferFnTypes env' sccs
    inferFnTypes env (CyclicSCC sccs' : sccs) = do
      env' <- inferFnTypes' env sccs'
      env'' <- inferFnTypes' env' sccs'
      inferFnTypes env'' sccs

    inferFnTypes' :: Env -> [SCC FnDef] -> Either FnDefError Env
    inferFnTypes' env [] = return env
    inferFnTypes' env (AcyclicSCC def : sccs) = do
      env' <- inferFnType env def
      inferFnTypes' env' sccs
    inferFnTypes' env (CyclicSCC defs : sccs) =
      throwError (UncondCallCycle (map fnDefFnId defs))

    inferFnType :: Env -> FnDef -> Either FnDefError Env
    inferFnType env@Env {fnTypes} (FnDef fid e) = do
      t <- mapLeft (FnTypeError fid) (inferNormType env ["$"] e)
      mapLeft (FnDefTempStack fid) (checkStackError t)
      let fnTypes' = Map.insert fid t fnTypes
      return env {fnTypes = fnTypes'}

    checkFnTypes :: Env -> [FnDef] -> Either FnDefError ()
    checkFnTypes env [] = return ()
    checkFnTypes env@Env {fnTypes} (FnDef fid e : defs) = do
      mapLeft (FnTypeError fid) (checkType env ["$"] e (fnTypes Map.! fid))
      checkFnTypes env defs

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

tryAddDataDefs :: Env -> [DataDef] -> Either DataDefError Env
tryAddDataDefs env defs = case addDataDefs env defs of
  ([], env') -> return env'
  (err : errs, _) -> throwError err

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

---------------------
-- Test Definition --
---------------------

data TestDef = TestDef TestName Expr
  deriving (Eq, Show)

type TestName = String

data TestDefError
  = TestTypeError TestName TypeError
  | TestExpectsInputs TestName Type
  deriving (Eq, Show)

isTProd :: Type -> Bool
isTProd (TProd _ _) = True
isTProd _ = False

expectsInputs :: Type -> Bool
expectsInputs (TFn _ mio) = any (\(i, o) -> isTProd i) (Map.elems mio)
expectsInputs _ = False

tryAddTestDef :: Env -> TestDef -> Either TestDefError Env
tryAddTestDef env@Env {testDefs} def@(TestDef n e) = do
  t <- mapLeft (TestTypeError n) (inferNormType env ["$"] e)
  when (expectsInputs t) (throwError (TestExpectsInputs n t))
  return env {testDefs = testDefs ++ [def]}

tryAddTestDefs :: Env -> [TestDef] -> Either TestDefError Env
tryAddTestDefs = foldM tryAddTestDef

----------------------
-- Program Elements --
----------------------

newtype Include = Include URIRef
  deriving (Eq, Show)

type URIRef = String

data Element
  = EInclude Include
  | EDataDef DataDef
  | EFnDecl FnDecl
  | EFnDef FnDef
  | ETestDef TestDef
  deriving (Eq, Show)
