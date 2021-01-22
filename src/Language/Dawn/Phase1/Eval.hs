-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Eval
  ( eval,
    eval',
    fromVal,
    MultiStack (..),
    toVal,
    Val (..),
  )
where

import Control.Monad
import Control.Monad.Except
import Data.Bits
import Data.List
import qualified Data.Map as Map
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

eval :: Context -> Expr -> MultiStack -> MultiStack
eval (s : s' : _) (EIntrinsic IPush) (MultiStack m) =
  let vs = Map.findWithDefault [] s m
      (v' : vs') = Map.findWithDefault [] s' m
      m' = insertListOrDelete s (v' : vs) m
      m'' = insertListOrDelete s' vs' m'
   in MultiStack m''
eval (s : s' : _) (EIntrinsic IPop) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      vs' = Map.findWithDefault [] s' m
      m' = insertListOrDelete s vs m
      m'' = insertListOrDelete s' (v : vs') m'
   in MultiStack m''
eval (s : _) (EIntrinsic IClone) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s (v : v : vs) m
   in MultiStack m'
eval (s : _) (EIntrinsic IDrop) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s vs m
   in MultiStack m'
eval (s : _) (EIntrinsic IQuote) (MultiStack m) =
  let (v : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s (VQuote (fromVal v) : vs) m
   in MultiStack m'
eval (s : _) (EIntrinsic ICompose) (MultiStack m) =
  let (VQuote b : VQuote a : vs) = Map.findWithDefault [] s m
      e = fromExprSeq (toExprSeq a ++ toExprSeq b)
      m' = insertListOrDelete s (VQuote e : vs) m
   in MultiStack m'
eval ctx@(s : _) (EIntrinsic IApply) (MultiStack m) =
  let (VQuote e : vs) = Map.findWithDefault [] s m
      m' = insertListOrDelete s vs m
   in eval ctx e (MultiStack m')
eval (s : _) (EIntrinsic IEqz) (MultiStack m) =
  let (VLit (LU32 a) : vs) = Map.findWithDefault [] s m
      c = if a == 0 then 1 else 0
      m' = insertListOrDelete s (VLit (LU32 c) : vs) m
   in MultiStack m'
eval (s : _) (EIntrinsic IAdd) (MultiStack m) = evalBinOp s m (+)
eval (s : _) (EIntrinsic ISub) (MultiStack m) = evalBinOp s m (-)
eval (s : _) (EIntrinsic IBitAnd) (MultiStack m) = evalBinOp s m (.&.)
eval (s : _) (EIntrinsic IBitOr) (MultiStack m) = evalBinOp s m (.|.)
eval (s : _) (EIntrinsic IBitXor) (MultiStack m) = evalBinOp s m xor
eval (s : _) (EIntrinsic IShl) (MultiStack m) = evalBinOp s m shl
eval (s : _) (EIntrinsic IShr) (MultiStack m) = evalBinOp s m shr
eval (s : _) e@(EQuote _) (MultiStack m) =
  let vs = Map.findWithDefault [] s m
      m' = insertListOrDelete s (toVal e : vs) m
   in MultiStack m'
eval ctx (ECompose es) ms =
  let folder ms e = eval ctx e ms
   in foldl folder ms es
eval ctx (EContext s e) ms = eval (s : ctx) e ms
eval (s : _) e@(ELit _) (MultiStack m) =
  let vs = Map.findWithDefault [] s m
      m' = insertListOrDelete s (toVal e : vs) m
   in MultiStack m'

eval' :: Expr -> MultiStack
eval' e = eval ["$"] e (MultiStack Map.empty)

evalBinOp s m op =
  let (VLit (LU32 b) : VLit (LU32 a) : vs) = Map.findWithDefault [] s m
      c = op a b
      m' = insertListOrDelete s (VLit (LU32 c) : vs) m
   in MultiStack m'

shl a b = a `shiftL` fromInteger (toInteger b)

shr a b = a `shiftR` fromInteger (toInteger b)
