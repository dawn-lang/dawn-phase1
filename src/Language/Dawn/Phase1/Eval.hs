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
    toEvalEnv,
    toVal,
    Val (..),
  )
where

import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Data.Bits
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.Word
import Language.Dawn.Phase1.Core hiding ((*))
import qualified Language.Dawn.Phase1.Core as Core
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
      fnExprs = Map.map (\(FnDef fid e) -> e) fnDefs
   in EvalEnv {consArities, fnExprs}

newtype MultiStack = MultiStack (Map.Map StackId [Val])
  deriving (Eq, Show)

data Val
  = VQuote Expr
  | VLit Literal
  | VCons [Val] ConsId
  deriving (Eq, Ord, Show)

toVal :: Expr -> Val
toVal (EQuote e) = VQuote e
toVal (ELit l) = VLit l

fromVal :: Val -> Expr
fromVal (VQuote e) = EQuote e
fromVal (VLit l) = ELit l

insertListOrDelete s [] m = Map.delete s m
insertListOrDelete s vs m = Map.insert s vs m

eval :: EvalEnv -> Context -> Expr -> MultiStack -> MultiStack
eval env (s : s' : _) (EIntrinsic IPush) (MultiStack m) =
  let vs = Map.findWithDefault [] s m
      (v' : vs') = Map.findWithDefault [] s' m
      m' = Map.insert s (v' : vs) m
      m'' = insertListOrDelete s' vs' m'
   in MultiStack m''
eval env (s : s' : _) (EIntrinsic IPop) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      vs' = Map.findWithDefault [] s' m
      m' = insertListOrDelete s vs m
      m'' = Map.insert s' (v : vs') m'
   in MultiStack m''
eval env (s : _) (EIntrinsic IClone) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      m' = Map.insert s (v : v : vs) m
   in MultiStack m'
eval env (s : _) (EIntrinsic IDrop) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s vs m
   in MultiStack m'
eval env (s : _) (EIntrinsic IQuote) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      m' = Map.insert s (VQuote (fromVal v) : vs) m
   in MultiStack m'
eval env (s : _) (EIntrinsic ICompose) (MultiStack m) =
  let (VQuote b : VQuote a : vs) = Map.findWithDefault [] s m
      e = fromExprSeq (toExprSeq a ++ toExprSeq b)
      m' = Map.insert s (VQuote e : vs) m
   in MultiStack m'
eval env ctx@(s : _) (EIntrinsic IApply) (MultiStack m) =
  let (VQuote e : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s vs m
   in eval env ctx e (MultiStack m')
eval env (s : _) (EIntrinsic IAnd) (MultiStack m) = evalBoolBinOp s m (&&)
eval env (s : _) (EIntrinsic IOr) (MultiStack m) = evalBoolBinOp s m (||)
eval env (s : _) (EIntrinsic INot) (MultiStack m) = evalBoolUnOp s m not
eval env (s : _) (EIntrinsic IXor) (MultiStack m) = evalBoolBinOp s m (/=)
eval env (s : _) (EIntrinsic IIncr) (MultiStack m) = evalUnOp s m (+ 1)
eval env (s : _) (EIntrinsic IDecr) (MultiStack m) = evalUnOp s m decr
eval env (s : _) (EIntrinsic IAdd) (MultiStack m) = evalBinOp s m (+)
eval env (s : _) (EIntrinsic ISub) (MultiStack m) = evalBinOp s m (-)
eval env (s : _) (EIntrinsic IBitAnd) (MultiStack m) = evalBinOp s m (.&.)
eval env (s : _) (EIntrinsic IBitOr) (MultiStack m) = evalBinOp s m (.|.)
eval env (s : _) (EIntrinsic IBitNot) (MultiStack m) = evalUnOp s m complement
eval env (s : _) (EIntrinsic IBitXor) (MultiStack m) = evalBinOp s m xor
eval env (s : _) (EIntrinsic IShl) (MultiStack m) = evalBinOp s m shl
eval env (s : _) (EIntrinsic IShr) (MultiStack m) = evalBinOp s m shr
eval env (s : _) (EIntrinsic IEq) (MultiStack m) = evalBinCmpOp s m (==)
eval env (s : _) (EIntrinsic ILt) (MultiStack m) = evalBinCmpOp s m (<)
eval env (s : _) (EIntrinsic IGt) (MultiStack m) = evalBinCmpOp s m (>)
eval env (s : _) (EIntrinsic ILteq) (MultiStack m) = evalBinCmpOp s m (<=)
eval env (s : _) (EIntrinsic IGteq) (MultiStack m) = evalBinCmpOp s m (>=)
eval env (s : _) e@(EQuote _) (MultiStack m) =
  let vs = Map.findWithDefault [] s m
      m' = Map.insert s (toVal e : vs) m
   in MultiStack m'
eval env ctx (ECompose es) ms =
  let folder ms e = eval env ctx e ms
   in foldl folder ms es
eval env ctx (EContext s e) ms =
  eval env (ensureUniqueStackId ctx s : ctx) e ms
eval env (s : _) e@(ELit _) (MultiStack m) =
  let vs = Map.findWithDefault [] s m
      m' = Map.insert s (toVal e : vs) m
   in MultiStack m'
eval env ctx (EMatch cs) ms = iter ctx cs ms
  where
    iter :: Context -> [(Pattern, Expr)] -> MultiStack -> MultiStack
    iter _ [] _ = error "Non-exhaustive patterns"
    iter ctx ((p, e) : cs) ms = case popPatternMatches ctx p ms of
      Nothing -> iter ctx cs ms
      Just ms' -> eval env ctx e ms'
eval env@EvalEnv {consArities} (s : _) (ECons cid) (MultiStack m) =
  let (vs, vs') = splitAt (consArities Map.! cid) (m Map.! s)
      vs'' = VCons vs cid : vs'
      m' = Map.insert s vs'' m
   in MultiStack m'
eval env@EvalEnv {fnExprs} ctx (ECall fid) ms = case Map.lookup fid fnExprs of
  Nothing -> error ("undefined function: " ++ fid)
  Just e -> eval env ctx e ms

eval' :: Expr -> MultiStack
eval' e = eval emptyEvalEnv ["$"] e (MultiStack Map.empty)

evalBoolUnOp s m op =
  let (VLit (LBool a) : vs) = Map.findWithDefault [] s m
      c = op a
      m' = Map.insert s (VLit (LBool c) : vs) m
   in MultiStack m'

evalBoolBinOp s m op =
  let (VLit (LBool b) : VLit (LBool a) : vs) = Map.findWithDefault [] s m
      c = op a b
      m' = Map.insert s (VLit (LBool c) : vs) m
   in MultiStack m'

evalUnOp s m op =
  let (VLit (LU32 a) : vs) = Map.findWithDefault [] s m
      c = op a
      m' = Map.insert s (VLit (LU32 c) : vs) m
   in MultiStack m'

evalBinOp s m op =
  let (VLit (LU32 b) : VLit (LU32 a) : vs) = Map.findWithDefault [] s m
      c = op a b
      m' = Map.insert s (VLit (LU32 c) : vs) m
   in MultiStack m'

evalBinCmpOp s m op =
  let (VLit (LU32 b) : VLit (LU32 a) : vs) = Map.findWithDefault [] s m
      c = op a b
      m' = Map.insert s (VLit (LBool c) : vs) m
   in MultiStack m'

decr :: Word32 -> Word32
decr a = a - 1

shl a b = a `shiftL` fromInteger (toInteger b)

shr a b = a `shiftR` fromInteger (toInteger b)

popPatternMatches :: Context -> Pattern -> MultiStack -> Maybe MultiStack
popPatternMatches ctx PEmpty ms = Just ms
popPatternMatches ctx@(s : _) (PProd l r) ms = case popPatternMatches ctx r ms of
  Nothing -> Nothing
  Just ms' -> popPatternMatches ctx l ms'
popPatternMatches (s : _) (PLit l) (MultiStack m) = case Map.findWithDefault [] s m of
  (VLit l' : vs) | l == l' -> Just (MultiStack (insertListOrDelete s vs m))
  (VLit l' : vs) -> Nothing
  _ -> error "EMatch arity/type mismatch"

evalWithFuel :: EvalEnv -> Context -> (Int, Expr, MultiStack) -> (Int, Expr, MultiStack)
evalWithFuel env ctx (0, e, ms) = (0, e, ms)
evalWithFuel env ctx@(s : _) (fuel, EIntrinsic IApply, MultiStack m) =
  let (VQuote e : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s vs m
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
