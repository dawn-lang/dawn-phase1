-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Eval
  ( eval,
    eval',
    evalWithFuel,
    fromVal,
    MultiStack (..),
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
import Language.Dawn.Phase1.Utils

newtype MultiStack = MultiStack (Map.Map StackId [Val])
  deriving (Eq, Show)

data Val
  = VQuote Expr
  | VLit Literal
  deriving (Eq, Ord, Show)

toVal :: Expr -> Val
toVal (EQuote e) = VQuote e
toVal (ELit l) = VLit l

fromVal :: Val -> Expr
fromVal (VQuote e) = EQuote e
fromVal (VLit l) = ELit l

insertListOrDelete s [] m = Map.delete s m
insertListOrDelete s vs m = Map.insert s vs m

eval :: FnEnv -> Context -> Expr -> MultiStack -> MultiStack
eval env (s : s' : _) (EIntrinsic IPush) (MultiStack m) =
  let vs = Map.findWithDefault [] s m
      (v' : vs') = Map.findWithDefault [] s' m
      m' = insertListOrDelete s (v' : vs) m
      m'' = insertListOrDelete s' vs' m'
   in MultiStack m''
eval env (s : s' : _) (EIntrinsic IPop) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      vs' = Map.findWithDefault [] s' m
      m' = insertListOrDelete s vs m
      m'' = insertListOrDelete s' (v : vs') m'
   in MultiStack m''
eval env (s : _) (EIntrinsic IClone) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s (v : v : vs) m
   in MultiStack m'
eval env (s : _) (EIntrinsic IDrop) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s vs m
   in MultiStack m'
eval env (s : _) (EIntrinsic IQuote) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s (VQuote (fromVal v) : vs) m
   in MultiStack m'
eval env (s : _) (EIntrinsic ICompose) (MultiStack m) =
  let (VQuote b : VQuote a : vs) = Map.findWithDefault [] s m
      e = fromExprSeq (toExprSeq a ++ toExprSeq b)
      m' = insertListOrDelete s (VQuote e : vs) m
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
      m' = insertListOrDelete s (toVal e : vs) m
   in MultiStack m'
eval env ctx (ECompose es) ms =
  let folder ms e = eval env ctx e ms
   in foldl folder ms es
eval env ctx (EContext s e) ms = eval env (s : ctx) e ms
eval env (s : _) e@(ELit _) (MultiStack m) =
  let vs = Map.findWithDefault [] s m
      m' = insertListOrDelete s (toVal e : vs) m
   in MultiStack m'
eval env ctx (EMatch cs) ms = iter ctx cs ms
  where
    iter :: Context -> [(Pattern, Expr)] -> MultiStack -> MultiStack
    iter _ [] _ = error "Non-exhaustive patterns"
    iter ctx ((p, e) : cs) ms = case popPatternMatches ctx p ms of
      Nothing -> iter ctx cs ms
      Just ms' -> eval env ctx e ms'
eval env ctx (ECall fid) ms = case Map.lookup fid env of
  Nothing -> error ("undefined function: " ++ fid)
  Just (e, t) -> eval env ctx e ms

eval' :: Expr -> MultiStack
eval' e = eval Map.empty ["$"] e (MultiStack Map.empty)

evalBoolUnOp s m op =
  let (VLit (LBool a) : vs) = Map.findWithDefault [] s m
      c = op a
      m' = insertListOrDelete s (VLit (LBool c) : vs) m
   in MultiStack m'

evalBoolBinOp s m op =
  let (VLit (LBool b) : VLit (LBool a) : vs) = Map.findWithDefault [] s m
      c = op a b
      m' = insertListOrDelete s (VLit (LBool c) : vs) m
   in MultiStack m'

evalUnOp s m op =
  let (VLit (LU32 a) : vs) = Map.findWithDefault [] s m
      c = op a
      m' = insertListOrDelete s (VLit (LU32 c) : vs) m
   in MultiStack m'

evalBinOp s m op =
  let (VLit (LU32 b) : VLit (LU32 a) : vs) = Map.findWithDefault [] s m
      c = op a b
      m' = insertListOrDelete s (VLit (LU32 c) : vs) m
   in MultiStack m'

evalBinCmpOp s m op =
  let (VLit (LU32 b) : VLit (LU32 a) : vs) = Map.findWithDefault [] s m
      c = op a b
      m' = insertListOrDelete s (VLit (LBool c) : vs) m
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

evalWithFuel :: FnEnv -> Context -> (Int, Expr, MultiStack) -> (Int, Expr, MultiStack)
evalWithFuel env ctx (0, e, ms) = (0, e, ms)
evalWithFuel env ctx@(s : _) (fuel, EIntrinsic IApply, MultiStack m) =
  let (VQuote e : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s vs m
  in evalWithFuel env ctx (fuel - 1, e, MultiStack m')
evalWithFuel env ctx (fuel, ECompose [], ms) = (fuel, ECompose [], ms)
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
evalWithFuel env ctx (fuel, ECall fid, ms) = case Map.lookup fid env of
  Nothing -> error ("undefined function: " ++ fid)
  Just (e, t) -> evalWithFuel env ctx (fuel - 1, e, ms)
evalWithFuel env ctx (fuel, e, ms) = (fuel - 1, ECompose [], eval env ctx e ms)
