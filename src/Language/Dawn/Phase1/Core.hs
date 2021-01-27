-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Core
  ( (-->),
    (*),
    (+->),
    ($:),
    ($.),
    addMissingStacks,
    composeSubst,
    Context,
    defineFn,
    defineFns,
    dependencySortFns,
    Expr (..),
    FnDef (..),
    FnDefError (..),
    fnDefType,
    FnEnv,
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
    mgu,
    normalizeType,
    Pattern (..),
    recFnDefType,
    removeTrivialStacks,
    replaceTypeVars,
    requantify,
    Result,
    StackId,
    StackIds,
    Subs (..),
    Subst (..),
    tempStackIds,
    Type (..),
    TypeCons (..),
    TypeVar (..),
    TypeVars,
    undefinedFnIds,
    UnificationError (..),
    UnivQuants,
    VarId,
  )
where

import Control.Monad
import Control.Monad.Except
import Data.Graph
import Data.List
import qualified Data.Map as Map
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
  deriving (Eq, Ord, Show)

data Type
  = TVar TypeVar
  | TProd Type Type
  | TFn UnivQuants MultiIO
  | TCons TypeCons
  deriving (Eq, Ord, Show)

newtype TypeCons = TypeCons String
  deriving (Eq, Ord, Show)

-- | Multi-stack input/output
type MultiIO = Map.Map StackId (Type, Type)

-- | Stack identifier
type StackId = String

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
  renameTypeVar from to t@(TCons _) = t

  ftv (TVar tv) = Set.singleton tv
  ftv (TProd l r) = ftv l `Set.union` ftv r
  ftv (TFn qs io) = ftv io `Set.difference` qs
  ftv (TCons _) = Set.empty

  btv (TVar _) = Set.empty
  btv (TProd l r) = btv l `Set.union` btv r
  btv (TFn qs io) = qs `Set.union` btv io
  btv (TCons _) = Set.empty

  atv (TVar tv) = [tv]
  atv (TProd l r) = atv l `union` atv r
  atv (TFn _ io) = atv io
  atv (TCons _) = []

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
      (mio12', reserved') = Map.foldlWithKey folder (Map.empty, reserved) mio12
      mio1' = Map.map fst mio12' `Map.union` mio1
      mio2' = Map.map snd mio12' `Map.union` mio2
   in doAdd (TFn qs1 mio1', TFn qs2 mio2', reserved')
  where
    folder (m, reserved) s ((i1, o1), (i2, o2)) =
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
  subs s t@(TCons _) reserved = (t, reserved)

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
  subs s m reserved = Map.foldlWithKey folder (Map.empty, reserved) m
    where
      folder (m', reserved) k v =
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
mgu f1@TFn {} f2@TFn {} reserved =
  let (TFn _ mio, TFn _ mio', reserved') = addMissingStacks (f1, f2, reserved)
      is = zip (map fst (Map.elems mio)) (map fst (Map.elems mio'))
      os = zip (map snd (Map.elems mio)) (map snd (Map.elems mio'))
   in mguList (is ++ os) reserved'
mgu (TCons (TypeCons s)) (TCons (TypeCons s')) reserved
  | s == s' = return (Subst Map.empty, reserved)
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

tBool = TCons (TypeCons "Bool")

tU32 = TCons (TypeCons "U32")

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

literalType :: Context -> Literal -> Type
literalType (s : _) (LBool _) = forall [v0] (s $: v0 --> v0 * tBool)
literalType (s : _) (LU32 _) = forall [v0] (s $: v0 --> v0 * tU32)

--------------------
-- Type Inference --
--------------------

type FnEnv = Map.Map FnId (Expr, Type)

quoteType :: Context -> Type -> Result Type
quoteType (s : _) f@TFn {} =
  let (tv, _) = freshTypeVar (Set.fromList (atv f))
      v = TVar tv
   in return (forall [v] (s $: v --> v * f))

requantify :: Type -> Type
requantify t = recurse t
  where
    count (TVar tv) = Map.singleton tv 1
    count (TProd l r) = Map.unionWith (+) (count l) (count r)
    count (TFn _ mio) =
      let iter (i, o) = Map.unionWith (+) (count i) (count o)
       in foldl1 (Map.unionWith (+)) (map iter (Map.elems mio))
    count (TCons _) = Map.empty
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
    recurse t@(TCons _) = t

composeTypes :: [Type] -> Result Type
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

stackTypes :: [Type] -> Type
stackTypes [t] = t
stackTypes (t : t' : ts) = iter (TProd t t') ts
  where
    iter t [] = t
    iter t (t' : ts) = iter (TProd t t') ts

patternType :: Context -> Pattern -> Type
patternType (s : _) p =
  let ts = patternTypes p
      (tv, _) = freshTypeVar Set.empty
      v = TVar tv
      i = stackTypes (v : ts)
   in forall [v] (s $: i --> v)
  where
    patternTypes :: Pattern -> [Type]
    patternTypes PEmpty = []
    patternTypes (PLit (LBool _)) = [tBool]
    patternTypes (PLit (LU32 _)) = [tU32]
    patternTypes (PProd l r) = patternTypes l ++ patternTypes r

caseType :: FnEnv -> Context -> (Pattern, Expr) -> Result Type
caseType env ctx (p, e) = do
  let pt = patternType ctx p
  et <- inferType env ctx e
  composeTypes [pt, et]

unifyCaseTypes :: [Type] -> Result Type
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

-- Infer an expression's type in the given FnEnv and Context. If there are any
-- ECall's to functions not in FnEnv, then a type of (∀ v0 v1 . v0 -> v1)
-- is assumed for those functions.
inferType :: FnEnv -> Context -> Expr -> Result Type
inferType env ctx (EIntrinsic i) = return $ intrinsicType ctx i
inferType env ctx (EQuote e) = do
  t <- inferType env ctx e
  quoteType ctx t
inferType env ctx (ECompose es) = do
  ts <- mapM (inferType env ctx) es
  composeTypes ts
inferType env ctx (EContext s e) =
  inferType env (ensureUniqueStackId ctx s : ctx) e
inferType env ctx (ELit l) = return $ literalType ctx l
inferType env ctx (EMatch cases) = do
  ts <- mapM (caseType env ctx) cases
  unifyCaseTypes ts
inferType env ctx (ECall fid) = case Map.lookup fid env of
  Nothing -> return (forall' [v0, v1] (v0 --> v1))
  Just (e, t) -> return t

-- ensure unique StackIds by prepending "$", creating a temporary StackId
ensureUniqueStackId :: Context -> StackId -> StackId
ensureUniqueStackId ctx s | s `elem` ctx = ensureUniqueStackId ctx ('$' : s)
ensureUniqueStackId ctx s = s

------------------------
-- Type Normalization --
------------------------

removeTrivialStacks :: Type -> Type
removeTrivialStacks t@(TVar _) = t
removeTrivialStacks (TProd l r) = TProd (removeTrivialStacks l) (removeTrivialStacks r)
removeTrivialStacks (TFn qs mio) =
  let trivialMIO = Map.filter (isTrivial qs) mio
      mio' = mio `Map.difference` trivialMIO
   in if null mio'
        then
          let v = TVar (Set.findMin qs)
           in forall' [v] (v --> v)
        else
          let ftvs = ftv trivialMIO
              qs' =
                if any (`elem` atv mio') (Set.elems ftvs)
                  then error "invalid reuse of trivial stack variable"
                  else qs `Set.difference` ftvs
              iter (i, o) = (removeTrivialStacks i, removeTrivialStacks o)
           in TFn qs' (Map.map iter mio')
  where
    isTrivial qs (TVar i, TVar o) | i == o && i `elem` qs = True
    isTrivial _ _ = False
removeTrivialStacks t@(TCons _) = t

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

inferNormType :: FnEnv -> Context -> Expr -> Result Type
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
      "shr"
    ]

data FnDefError
  = FnAlreadyDefined FnId
  | FnCallsUndefined FnId FnIds
  | FnTypeError FnId UnificationError
  | FnStackError FnId StackIds
  | FnTypeUnstable FnId
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
tempStackIds (TCons _) = Set.empty

undefinedFnIds :: FnEnv -> Expr -> FnIds
undefinedFnIds env (EIntrinsic _) = Set.empty
undefinedFnIds env (EQuote e) = undefinedFnIds env e
undefinedFnIds env (ECompose es) =
  foldr (Set.union . undefinedFnIds env) Set.empty es
undefinedFnIds env (EContext s e) = undefinedFnIds env e
undefinedFnIds env (ELit _) = Set.empty
undefinedFnIds env (EMatch cs) =
  foldr (Set.union . undefinedFnIds env . snd) Set.empty cs
undefinedFnIds env (ECall fid) =
  if Map.member fid env then Set.empty else Set.singleton fid

fnDefType :: FnEnv -> FnDef -> Either FnDefError Type
fnDefType env (FnDef fid e) =
  case inferNormType env ["$"] e of
    Left err -> throwError $ FnTypeError fid err
    Right t
      | not (null (tempStackIds t)) ->
        throwError $ FnStackError fid (tempStackIds t)
    Right t -> return t

recFnDefType :: FnEnv -> FnDef -> Either FnDefError Type
recFnDefType env (FnDef fid e) =
  case fnDefType env (FnDef fid e) of
    Left err -> Left err
    Right t -> case fnDefType (Map.insert fid (e, t) env) (FnDef fid e) of
      Left err -> Left err
      Right t' | t /= t' -> throwError (FnTypeUnstable fid)
      Right t' -> return t'

defineFn :: FnEnv -> FnDef -> Either FnDefError FnEnv
defineFn env (FnDef fid e)
  | fid `Set.member` intrinsicFnIds = throwError $ FnAlreadyDefined fid
  | fid `Map.member` env = throwError $ FnAlreadyDefined fid
  | otherwise = case undefinedFnIds env e of
    fids
      | not (null (Set.filter (/= fid) fids)) ->
        throwError $ FnCallsUndefined fid (Set.filter (/= fid) fids)
    fids | not (null fids) ->
      case recFnDefType env (FnDef fid e) of
        Left err -> Left err
        Right t -> return (Map.insert fid (e, t) env)
    _ ->
      case fnDefType env (FnDef fid e) of
        Left err -> Left err
        Right t -> return (Map.insert fid (e, t) env)

fnDefFnId :: FnDef -> FnId
fnDefFnId (FnDef fid _) = fid

fnIds :: Expr -> FnIds
fnIds (EIntrinsic _) = Set.empty
fnIds (EQuote e) = fnIds e
fnIds (ECompose es) =
  foldr (Set.union . fnIds) Set.empty es
fnIds (EContext s e) = fnIds e
fnIds (ELit _) = Set.empty
fnIds (EMatch cs) =
  foldr (Set.union . fnIds . snd) Set.empty cs
fnIds (ECall fid) = Set.singleton fid

-- | Sort FnDef's such that f precedes g if f calls g (directly or
-- | transitively) and g does not call f.
dependencySortFns :: [FnDef] -> [FnDef]
dependencySortFns defs =
  let fnDefToTuple def@(FnDef fid e) = (def, fid, Set.toList (fnIds e))
      (graph, vertToTuple, fidToVert) = graphFromEdges (map fnDefToTuple defs)
      tupleToFnDef (def, _, _) = def
      vertToFnDef v = tupleToFnDef (vertToTuple v)
   in map vertToFnDef (topSort graph)

defineFns :: FnEnv -> [FnDef] -> ([FnDefError], FnEnv)
defineFns env defs =
  let -- check for and remove FnAlreadyDefined
      existingFnIds = Map.keysSet env `Set.union` intrinsicFnIds
      (errs1, defs1) = removeAlreadyDefined existingFnIds defs
      -- check for and remove FnCallsUndefined
      newFnIds = Set.fromList (map fnDefFnId defs)
      allFnIds = existingFnIds `Set.union` newFnIds
      (errs2, defs2) = removeFnCallsUndefined allFnIds defs1
      -- topologically sort the FnDef's
      defs3 = dependencySortFns defs2
      -- call `fnDefType env` on each FnDef to produce env2
      (errs3, env2) = foldr folder1 ([], env) defs3
      -- call `fnDefType env2` on each FnDef to check for unstable types
      (errs4, env3) = foldr folder2 (errs2, env2) defs3
   in (errs1 ++ errs2 ++ errs3 ++ errs4, env3)
  where
    removeAlreadyDefined :: FnIds -> [FnDef] -> ([FnDefError], [FnDef])
    removeAlreadyDefined fids [] = ([], [])
    removeAlreadyDefined fids (FnDef fid e : defs) =
      let (errs, defs') = removeAlreadyDefined (Set.insert fid fids) defs
       in if fid `Set.member` fids
            then (FnAlreadyDefined fid : errs, defs')
            else (errs, FnDef fid e : defs)

    removeFnCallsUndefined :: FnIds -> [FnDef] -> ([FnDefError], [FnDef])
    removeFnCallsUndefined fids [] = ([], [])
    removeFnCallsUndefined fids (FnDef fid e : defs) =
      let (errs, defs') = removeFnCallsUndefined fids defs
          undefinedFnCalls = Set.filter (`Set.notMember` fids) (fnIds e)
       in if null undefinedFnCalls
            then (errs, FnDef fid e : defs)
            else (FnCallsUndefined fid undefinedFnCalls : errs, defs')

    folder1 (FnDef fid e) (errs, env) = case fnDefType env (FnDef fid e) of
      Left err -> (err : errs, env)
      Right t -> (errs, Map.insert fid (e, t) env)

    folder2 (FnDef fid e) (errs, env) = case fnDefType env (FnDef fid e) of
      Left err -> (err : errs, Map.delete fid env)
      Right t -> case Map.lookup fid env of
        Just (_, t') | t == t' -> (errs, Map.insert fid (e, t) env)
        _ -> (FnTypeUnstable fid : errs, Map.delete fid env)
