-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Core
  ( (-->),
    (*),
    (+->),
    composeSubst,
    Expr (..),
    forall,
    freshTypeVar,
    HasTypeVars (..),
    Id,
    inferType,
    instantiate,
    Intrinsic (..),
    intrinsicType,
    mgu,
    partialEval,
    replaceTypeVars,
    requantify,
    Result,
    Subs (..),
    Subst (..),
    Type (..),
    TypeVar (..),
    TypeVars,
    UnificationError (..),
    UnivQuants,
  )
where

import Control.Monad
import Control.Monad.Except
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude hiding ((*))

---------------------
-- Abstract Syntax --
---------------------

-- | Expressions
data Expr
  = EIntrinsic Intrinsic
  | EQuote Expr
  | ECompose [Expr]
  deriving (Eq, Ord, Show)

data Intrinsic
  = IClone
  | IDrop
  | ISwap
  | IQuote
  | ICompose
  | IApply
  deriving (Eq, Ord, Show)

data Type
  = TVar TypeVar
  | TProd Type Type
  | TFn UnivQuants (Type, Type)
  deriving (Eq, Ord, Show)

-- | Universal quantifiers
type UnivQuants = TypeVars

-- | Type variable set
type TypeVars = Set.Set TypeVar

-- | Type variable
newtype TypeVar = TypeVar Id
  deriving (Eq, Ord, Show)

-- | Numeric identifier
type Id = Int

---------------------
-- Intrinsic Types --
---------------------

infixl 4 -->

(-->) :: Type -> Type -> Type
i --> o = TFn Set.empty (i, o)

infixl 7 *

(*) = TProd

forall :: [Type] -> Type -> Type
forall vs (TFn qs io) =
  let qs' = Set.fromList (map (\(TVar tv) -> tv) vs)
   in TFn (qs' `Set.union` qs) io

[v0, v1, v2, v3] = map (TVar . TypeVar) [0 .. 3]

intrinsicType :: Intrinsic -> Type
intrinsicType IClone = forall [v0, v1] (v0 * v1 --> v0 * v1 * v1)
intrinsicType IDrop = forall [v0, v1] (v0 * v1 --> v0)
intrinsicType ISwap = forall [v0, v1, v2] (v0 * v1 * v2 --> v0 * v2 * v1)
intrinsicType IQuote =
  forall [v0, v1] (v0 * v1 --> v0 * forall [v2] (v2 --> v2 * v1))
intrinsicType ICompose =
  forall [v0, v1, v2, v3] (v0 * (v1 --> v2) * (v2 --> v3) --> v0 * (v1 --> v3))
intrinsicType IApply = forall [v0, v1] (v0 * (v0 --> v1) --> v1)

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
  renameTypeVar from to (TFn uqs io) =
    TFn
      (Set.map (\tv -> if tv == from then to else tv) uqs)
      (renameTypeVar from to io)

  ftv (TVar tv) = Set.singleton tv
  ftv (TProd l r) = ftv l `Set.union` ftv r
  ftv (TFn qs io) = ftv io `Set.difference` qs

  btv (TVar _) = Set.empty
  btv (TProd l r) = btv l `Set.union` btv r
  btv (TFn qs io) = qs `Set.union` btv io

  atv (TVar tv) = [tv]
  atv (TProd l r) = atv l `union` atv r
  atv (TFn _ io) = atv io

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

-----------------
-- Unification --
-----------------

data UnificationError
  = DoesNotUnify Type Type
  | OccursIn TypeVar Type
  deriving (Eq, Ord, Show)

type Result a = Either UnificationError a

-- | Find the most general unifier, s, of two Types,
-- | t and t', such that subs s t == subs s' t',
-- | where t and t' do not share any type variables.
mgu :: Type -> Type -> TypeVars -> Result (Subst, TypeVars)
mgu (TProd l r) (TProd l' r') reserved = mguList [(l, l'), (r, r')] reserved
mgu (TFn _ (i, o)) (TFn _ (i', o')) reserved =
  mguList [(i, i'), (o, o')] reserved
mgu t (TVar u) reserved = bindTypeVar u t reserved
mgu (TVar u) t reserved = bindTypeVar u t reserved
mgu t t' _ = throwError $ DoesNotUnify t t'

bindTypeVar :: TypeVar -> Type -> TypeVars -> Result (Subst, TypeVars)
bindTypeVar u t reserved
  | TVar u == t = return (Subst Map.empty, reserved)
  | u `elem` ftv t = throwError $ OccursIn u t
  | otherwise = return (u +-> t, reserved)

mguList :: [(Type, Type)] -> TypeVars -> Result (Subst, TypeVars)
mguList [] reserved = return (Subst Map.empty, reserved)
mguList ((t1, t2) : ts) reserved = do
  (s1, reserved2) <- mgu t1 t2 reserved
  let (ts', reserved3) = subs s1 ts reserved2
  (s2, reserved4) <- mguList ts' reserved3
  let (s3, reserved5) = composeSubst s2 s1 reserved4
  return (s3, reserved5)

--------------------
-- Type Inference --
--------------------

quoteType :: Type -> Result Type
quoteType f@TFn {} =
  let (tv, _) = freshTypeVar (Set.fromList (atv f))
      v = TVar tv
   in return (forall [v] (v --> v * f))

requantify :: Type -> Type
requantify t = recurse t
  where
    count (TVar tv) = Map.singleton tv 1
    count (TProd l r) = Map.unionWith (+) (count l) (count r)
    count (TFn _ (i, o)) = Map.unionWith (+) (count i) (count o)
    counts = count t
    recurse t@(TVar _) = t
    recurse (TProd l r) = TProd (recurse l) (recurse r)
    recurse t@(TFn _ (i, o)) =
      let counts' = count t
          deltas = Map.intersectionWith (-) counts counts'
          qs = Set.fromAscList $ Map.keys $ Map.filter (== 0) deltas
          io' = (recurse i, recurse o)
          qs' = qs `Set.difference` btv io'
       in TFn qs' io'

composeTypes :: Type -> Type -> Result Type
composeTypes f1@TFn {} f2@TFn {} = do
  let (f1', reserved1) = instantiate f1 Set.empty
  let (f2', reserved2) = instantiate f2 reserved1
  let (TFn _ (i1, o1), TFn _ (i2, o2)) = (f1', f2')
  (s, reserved3) <- mgu o1 i2 reserved2
  let (io3, _) = subs s (i1, o2) reserved3
  return (requantify (TFn Set.empty io3))

inferType :: Expr -> Result Type
inferType (EIntrinsic i) = return $ intrinsicType i
inferType (EQuote e) = do
  t <- inferType e
  quoteType t
inferType (ECompose []) = return (forall [v0] (v0 --> v0))
inferType (ECompose es) = do
  ts <- mapM inferType es
  foldM composeTypes (head ts) (tail ts)

------------------------
-- Partial Evaluation --
------------------------

partialEval :: Expr -> Expr
partialEval e@(EIntrinsic _) = e
partialEval (EQuote e) = EQuote (partialEval e)
partialEval (ECompose es) = case iter [] es of
  [e] -> e
  es -> ECompose es
  where
    iter es' [] = es'
    iter
      es'
      ( e@(EQuote (ECompose (EIntrinsic IClone : EIntrinsic IApply : _)))
          : EIntrinsic IClone
          : EIntrinsic IApply
          : es
        ) =
        iter (es' ++ [e, EIntrinsic IClone, EIntrinsic IApply]) es
    iter es' (EQuote e : EIntrinsic IClone : es) =
      iter es' (EQuote e : EQuote e : es)
    iter es' (EQuote _ : EIntrinsic IDrop : es) =
      iter es' es
    iter es' (EQuote e1 : EQuote e2 : EIntrinsic ISwap : es) =
      iter es' (EQuote e2 : EQuote e1 : es)
    iter es' (EQuote e : EIntrinsic IQuote : es) =
      iter es' (EQuote (EQuote e) : es)
    iter es' (EQuote e1 : EQuote e2 : EIntrinsic ICompose : es) =
      case (e1, e2) of
        (ECompose es1, ECompose es2) -> iter es' (EQuote (ECompose (es1 ++ es2)) : es)
        (ECompose es1, _) -> iter es' (EQuote (ECompose (es1 ++ [e2])) : es)
        (_, ECompose es2) -> iter es' (EQuote (ECompose (e1 : es2)) : es)
        (_, _) -> iter es' (EQuote (ECompose [e1, e2]) : es)
    iter es' (EQuote e : EIntrinsic IApply : es) =
      if null es'
        then iter [] (e : es)
        else iter (init es') (last es' : e : es)
    iter [] ((ECompose es'') : es) = iter [] (es'' ++ es)
    iter es' ((ECompose es'') : es) = iter (init es') (last es' : es'' ++ es)
    iter es' (e : es) = iter (es' ++ [e]) es
