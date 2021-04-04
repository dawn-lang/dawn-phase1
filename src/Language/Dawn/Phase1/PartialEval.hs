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
isLiteral (ECons _) = True
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
-- annihilate Push-Pop and Pop-Push
simplify fuel es' ((EContext s (EIntrinsic IPush)) : (EContext s' (EIntrinsic IPop)) : es)
  | s == s' = simplify (fuel - 1) [] (es' ++ es)
simplify fuel es' ((EContext s (EIntrinsic IPop)) : (EContext s' (EIntrinsic IPush)) : es)
  | s == s' = simplify (fuel - 1) [] (es' ++ es)
-- otherwise, skip
simplify fuel es' (e : es) = simplify fuel (es' ++ [e]) es

partialEval :: Int -> Expr -> (Int, Expr)
partialEval fuel e =
  let (fuel', es') = simplify fuel [] (toExprSeq e)
   in (fuel', fromExprSeq es')

partialEval' :: Expr -> Expr
partialEval' e = snd (partialEval 100 e)
