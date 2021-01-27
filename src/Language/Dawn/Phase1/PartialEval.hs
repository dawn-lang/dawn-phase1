-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.PartialEval
  ( partialEval,
    partialEval',
  )
where

import Control.Monad
import Control.Monad.Except
import Data.Bits
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core hiding ((*))
import Language.Dawn.Phase1.Utils

-- | Returns True if the expression is a literal
isLiteral :: Expr -> Bool
isLiteral (EQuote _) = True
isLiteral (ELit _) = True
isLiteral _ = False

simplify :: Int -> [Expr] -> [Expr] -> (Int, [Expr])
-- if we're done, we're done
simplify fuel es' [] = (fuel, es')
-- if we're out of fuel, return as is
simplify 0 es' es = (0, es' ++ es)
-- apply IClone/IDrop/IQuote to literals
simplify fuel es' (e : EIntrinsic IClone : es)
  | isLiteral e = simplify (fuel - 1) [] (es' ++ e : e : es)
simplify fuel es' (e : EIntrinsic IDrop : es)
  | isLiteral e = simplify (fuel - 1) [] (es' ++ es)
simplify fuel es' (e : EIntrinsic IQuote : es)
  | isLiteral e = simplify (fuel - 1) [] (es' ++ EQuote e : es)
-- apply ICompose to EQuotes
simplify fuel es' (EQuote e1 : EQuote e2 : EIntrinsic ICompose : es) =
  simplify (fuel - 1) [] (es' ++ EQuote (ECompose [e1, e2]) : es)
-- apply IApply to EQuotes
simplify fuel es' (EQuote e : EIntrinsic IApply : es) =
  simplify (fuel - 1) [] (es' ++ e : es)
-- recurse into EQuotes
simplify fuel es' ((EQuote e) : es) =
  let (fuel', es'') = simplify fuel [] (toExprSeq e)
      e' = fromExprSeq es''
   in simplify fuel' (es' ++ [EQuote e']) es
-- expand ECompose
simplify fuel es' ((ECompose es'') : es) = simplify (fuel - 1) [] (es' ++ es'' ++ es)
-- arithmetic
simplify fuel es' (ELit (LU32 a) : ELit (LU32 b) : EIntrinsic IAdd : es) =
  let c = a + b
   in simplify (fuel - 1) [] (es' ++ ELit (LU32 c) : es)
simplify fuel es' (ELit (LU32 a) : ELit (LU32 b) : EIntrinsic ISub : es) =
  let c = a - b
   in simplify (fuel - 1) [] (es' ++ ELit (LU32 c) : es)
simplify fuel es' (ELit (LU32 a) : ELit (LU32 b) : EIntrinsic IBitAnd : es) =
  let c = a .&. b
   in simplify (fuel - 1) [] (es' ++ ELit (LU32 c) : es)
simplify fuel es' (ELit (LU32 a) : ELit (LU32 b) : EIntrinsic IBitOr : es) =
  let c = a .|. b
   in simplify (fuel - 1) [] (es' ++ ELit (LU32 c) : es)
simplify fuel es' (ELit (LU32 a) : EIntrinsic IBitNot : es) =
  let c = complement a
   in simplify (fuel - 1) [] (es' ++ ELit (LU32 c) : es)
simplify fuel es' (ELit (LU32 a) : ELit (LU32 b) : EIntrinsic IBitXor : es) =
  let c = a `xor` b
   in simplify (fuel - 1) [] (es' ++ ELit (LU32 c) : es)
simplify fuel es' (ELit (LU32 a) : ELit (LU32 b) : EIntrinsic IShl : es) =
  let c = a `shiftL` fromInteger (toInteger b)
   in simplify (fuel - 1) [] (es' ++ ELit (LU32 c) : es)
simplify fuel es' (ELit (LU32 a) : ELit (LU32 b) : EIntrinsic IShr : es) =
  let c = a `shiftR` fromInteger (toInteger b)
   in simplify (fuel - 1) [] (es' ++ ELit (LU32 c) : es)
-- otherwise, skip
simplify fuel es' (e : es) = simplify fuel (es' ++ [e]) es

partialEval :: Int -> Expr -> (Int, Expr)
partialEval fuel e =
  let (fuel', es') = simplify fuel [] (toExprSeq e)
   in (fuel', fromExprSeq es')

partialEval' :: Expr -> Expr
partialEval' e = snd (partialEval 100 e)
