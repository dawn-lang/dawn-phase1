-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.
{-# LANGUAGE NamedFieldPuns #-}

module Language.Dawn.Phase1.Eval
  ( emptyEvalEnv,
    eval,
    eval',
    EvalEnv (..),
    evalWithFuel,
    fromVal,
    MultiStack (..),
    splitStackAt,
    toEvalEnv,
    toVal,
    Val (..),
  )
where

import Data.Bits
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Word
import Language.Dawn.Phase1.Core hiding ((*))
import Language.Dawn.Phase1.Utils

data EvalEnv = EvalEnv
  { consArities :: Map.Map ConsId Int,
    fnExprs :: Map.Map FnId Expr
  }
  deriving (Eq, Show)

emptyEvalEnv :: EvalEnv
emptyEvalEnv = EvalEnv Map.empty Map.empty

toEvalEnv :: Env -> EvalEnv
toEvalEnv Env {consTypes, fnDefs} =
  let consArities = Map.map (\(is, os) -> length is) consTypes
      fnExprs = Map.map fnDefExpr fnDefs
   in EvalEnv {consArities, fnExprs}

data Val
  = VQuote Expr
  | VCons (Stack Val) ConsId
  deriving (Eq, Ord, Show)

splitStackAt :: Int -> Stack a -> (Stack a, Stack a)
splitStackAt n s
  | n <= 0 = (s, Empty)
  | otherwise = splitStackAt' n s
  where
    splitStackAt' _ Empty = (Empty, Empty)
    splitStackAt' 1 (xs :*: x) = (xs, Empty :*: x)
    splitStackAt' m (xs :*: x) =
      let (xs', xs'') = splitStackAt' (m - 1) xs
       in (xs', xs'' :*: x)

newtype MultiStack = MultiStack (Map.Map StackId (Stack Val))
  deriving (Eq, Show)

toVal :: Expr -> Val
toVal (EQuote e) = VQuote e
toVal (ECons cid) = VCons Empty cid

fromVal :: Val -> Expr
fromVal (VQuote e) = EQuote e
fromVal (VCons Empty cid) = ECons cid
fromVal (VCons args cid) =
  ECompose (map fromVal (fromStack args) ++ [ECons cid])

insertStackOrDelete s Empty m = Map.delete s m
insertStackOrDelete s vs m = Map.insert s vs m

eval :: EvalEnv -> Context -> Expr -> MultiStack -> MultiStack
eval env (s : s' : _) (EIntrinsic IPush) (MultiStack m) =
  let vs = Map.findWithDefault Empty s m
      (vs' :*: v') = Map.findWithDefault Empty s' m
      m' = Map.insert s (vs :*: v') m
      m'' = insertStackOrDelete s' vs' m'
   in MultiStack m''
eval env (s : s' : _) (EIntrinsic IPop) (MultiStack m) =
  let (vs :*: v) = Map.findWithDefault Empty s m
      vs' = Map.findWithDefault Empty s' m
      m' = insertStackOrDelete s vs m
      m'' = Map.insert s' (vs' :*: v) m'
   in MultiStack m''
eval env (s : _) (EIntrinsic IClone) (MultiStack m) =
  let (vs :*: v) = Map.findWithDefault Empty s m
      m' = Map.insert s (vs :*: v :*: v) m
   in MultiStack m'
eval env (s : _) (EIntrinsic IDrop) (MultiStack m) =
  let (vs :*: v) = Map.findWithDefault Empty s m
      m' = insertStackOrDelete s vs m
   in MultiStack m'
eval env (s : _) (EIntrinsic IQuote) (MultiStack m) =
  let (vs :*: v) = Map.findWithDefault Empty s m
      m' = Map.insert s (vs :*: VQuote (fromVal v)) m
   in MultiStack m'
eval env (s : _) (EIntrinsic ICompose) (MultiStack m) =
  let (vs :*: VQuote a :*: VQuote b) = Map.findWithDefault Empty s m
      e = fromExprSeq (toExprSeq a ++ toExprSeq b)
      m' = Map.insert s (vs :*: VQuote e) m
   in MultiStack m'
eval env ctx@(s : _) (EIntrinsic IApply) (MultiStack m) =
  let (vs :*: VQuote e) = Map.findWithDefault Empty s m
      m' = insertStackOrDelete s vs m
   in eval env ctx e (MultiStack m')
eval env (s : _) e@(EQuote _) (MultiStack m) =
  let vs = Map.findWithDefault Empty s m
      m' = Map.insert s (vs :*: toVal e) m
   in MultiStack m'
eval env ctx (ECompose es) ms =
  let folder ms e = eval env ctx e ms
   in foldl folder ms es
eval env ctx (EContext s e) ms =
  eval env (ensureUniqueStackId ctx s : ctx) e ms
eval env ctx (EMatch cs) ms = iter ctx cs ms
  where
    iter :: Context -> [(Stack Pattern, Expr)] -> MultiStack -> MultiStack
    iter _ [] _ = error "Non-exhaustive patterns"
    iter ctx ((p, e) : cs) ms = case popPatternMatches ctx p ms of
      Nothing -> iter ctx cs ms
      Just ms' -> eval env ctx e ms'
eval env@EvalEnv {consArities} (s : _) (ECons cid) (MultiStack m) =
  let vs0 = Map.findWithDefault Empty s m
      (vs, vs') = splitStackAt (consArities Map.! cid) vs0
      vs'' = vs :*: VCons vs' cid
      m' = Map.insert s vs'' m
   in MultiStack m'
eval env@EvalEnv {fnExprs} ctx (ECall fid) ms = case Map.lookup fid fnExprs of
  Nothing -> error ("undefined function: " ++ fid)
  Just e -> eval env ctx e ms

eval' :: Expr -> MultiStack
eval' e = eval emptyEvalEnv ["$"] e (MultiStack Map.empty)

popPatternMatches :: Context -> Stack Pattern -> MultiStack -> Maybe MultiStack
popPatternMatches ctx Empty ms = Just ms
popPatternMatches (s : _) ps (MultiStack m) = do
  vs <- popPatternMatches' ps (m Map.! s)
  return (MultiStack (insertStackOrDelete s vs m))
  where
    popPatternMatches' :: Stack Pattern -> Stack Val -> Maybe (Stack Val)
    popPatternMatches' Empty vs = Just vs
    popPatternMatches' (ps :*: p) (vs :*: v) = do
      vss <- popPatternMatches' ps vs
      vs <- popPatternMatch p v
      return (vss `stackAppend` vs)

    popPatternMatch :: Pattern -> Val -> Maybe (Stack Val)
    popPatternMatch (PCons ps cid) (VCons vs cid') =
      if cid == cid' then popPatternMatches' ps vs else Nothing
    popPatternMatch PWild v = Just (Empty :*: v)

evalWithFuel :: EvalEnv -> Context -> (Int, Expr, MultiStack) -> (Int, Expr, MultiStack)
evalWithFuel env ctx (0, e, ms) = (0, e, ms)
evalWithFuel env ctx@(s : _) (fuel, EIntrinsic IApply, MultiStack m) =
  let (vs :*: VQuote e) = Map.findWithDefault Empty s m
      m' = insertStackOrDelete s vs m
   in evalWithFuel env ctx (fuel - 1, e, MultiStack m')
evalWithFuel env ctx (fuel, ECompose [], ms) = (fuel, ECompose [], ms)
evalWithFuel env ctx (fuel, ECompose [ECompose es], ms) =
  evalWithFuel env ctx (fuel, ECompose es, ms)
evalWithFuel env ctx (fuel, ECompose (e : es), ms) =
  case evalWithFuel env ctx (fuel, e, ms) of
    (fuel', ECompose [], ms') -> evalWithFuel env ctx (fuel', ECompose es, ms')
    (fuel', e', ms') -> evalWithFuel env ctx (fuel', ECompose (e' : es), ms')
evalWithFuel env ctx (fuel, EContext s e, ms) =
  case evalWithFuel env (s : ctx) (fuel, e, ms) of
    (fuel', ECompose [], ms') -> (fuel', ECompose [], ms')
    (fuel', e', ms') -> evalWithFuel env ctx (fuel', EContext s e', ms')
evalWithFuel env ctx (fuel, EMatch [], ms) = error "Non-exhaustive patterns"
evalWithFuel env ctx (fuel, EMatch ((p, e) : cs), ms) =
  case popPatternMatches ctx p ms of
    Nothing -> evalWithFuel env ctx (fuel - 1, EMatch cs, ms)
    Just ms' -> evalWithFuel env ctx (fuel - 1, e, ms')
evalWithFuel env@EvalEnv {fnExprs} ctx (fuel, ECall fid, ms) =
  case Map.lookup fid fnExprs of
    Nothing -> error ("undefined function: " ++ fid)
    Just e -> evalWithFuel env ctx (fuel - 1, e, ms)
evalWithFuel env ctx (fuel, e, ms) = (fuel - 1, ECompose [], eval env ctx e ms)
