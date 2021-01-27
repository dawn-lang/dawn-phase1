-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Exprs
  ( allExprsOfWidthUpToDepth,
    allExprsUpToWidthAndDepth,
    allGroupings,
    allUnquotedExprsOfWidth,
    intToIntrinsic,
  )
where

import Control.Monad
import Language.Dawn.Phase1.Core

intToIntrinsic :: Int -> Expr
intToIntrinsic 0 = EContext "$a" (EIntrinsic IPush)
intToIntrinsic 1 = EContext "$a" (EIntrinsic IPop)
intToIntrinsic 2 = EContext "$b" (EIntrinsic IPush)
intToIntrinsic 3 = EContext "$b" (EIntrinsic IPop)
intToIntrinsic 4 = EIntrinsic IClone
intToIntrinsic 5 = EIntrinsic IDrop
intToIntrinsic 6 = EIntrinsic IQuote
intToIntrinsic 7 = EIntrinsic ICompose
intToIntrinsic 8 = EIntrinsic IApply
intToIntrinsic 9 = ELit (LBool False)
intToIntrinsic 10 = ELit (LBool True)
intToIntrinsic 11 = EIntrinsic IAnd
intToIntrinsic 12 = EIntrinsic IOr
intToIntrinsic 13 = EIntrinsic INot
intToIntrinsic 14 = EIntrinsic IXor
intToIntrinsic 15 = ELit (LU32 0)
intToIntrinsic 16 = ELit (LU32 1)
intToIntrinsic 17 = EIntrinsic IIncr
intToIntrinsic 18 = EIntrinsic IDecr
intToIntrinsic 19 = EIntrinsic IAdd
intToIntrinsic 20 = EIntrinsic ISub
intToIntrinsic 21 = EIntrinsic IBitAnd
intToIntrinsic 22 = EIntrinsic IBitOr
intToIntrinsic 23 = EIntrinsic IBitNot
intToIntrinsic 24 = EIntrinsic IBitXor
intToIntrinsic 25 = EIntrinsic IShl
intToIntrinsic 26 = EIntrinsic IShr

allIntCombinations :: Int -> Int -> Int -> [[Int]]
allIntCombinations width min max = replicateM width [min .. max]

allIntrinsicCombinations :: Int -> [[Expr]]
allIntrinsicCombinations width =
  map (map intToIntrinsic) (allIntCombinations width 0 26)

allUnquotedExprsOfWidth :: Int -> [Expr]
allUnquotedExprsOfWidth width = map ECompose (allIntrinsicCombinations width)

allGroupings :: Expr -> [Expr]
allGroupings e@(ECompose []) = [e]
allGroupings e@(ECompose [_]) = [e]
allGroupings e@(ECompose [_, _]) = [e]
allGroupings (ECompose es) = iter 1 []
  where
    iter n gs | n == length es = gs
    iter n gs =
      let (les, res) = splitAt n es
          lgs = allGroupings (ECompose les)
          rgs = allGroupings (ECompose res)
          gs' = [ECompose [lt, rt] | lt <- lgs, rt <- rgs]
       in iter (n + 1) (gs ++ gs')

allExprsOfWidthUpToDepth :: Int -> Int -> [Expr]
allExprsOfWidthUpToDepth width depth =
  let allIntrs = allIntrinsicCombinations width
      allDepths = allIntCombinations width 0 depth
      allQuoted = [doQuotes ds is | is <- allIntrs, ds <- allDepths]
      allGrouped = doGrouping allQuoted
   in map ECompose allGrouped
  where
    doQuotes :: [Int] -> [Expr] -> [Expr]
    doQuotes ds is = zipWith doQuote ds is
    doQuote :: Int -> Expr -> Expr
    doQuote d e
      | d == 0 = e
      | otherwise = doQuote (d - 1) (EQuote e)

    -- TODO: this does not appear to work properly at width 3
    -- TODO: insert groupings as they're discovered?
    doGrouping :: [[Expr]] -> [[Expr]]
    doGrouping [] = []
    doGrouping allQuoted =
      let new = concatMap findGroupings allQuoted
       in allQuoted ++ doGrouping new

    -- TODO: eliminate duplicates
    -- TODO: recursive search and grouping inside of quotes
    findGroupings :: [Expr] -> [[Expr]]
    findGroupings [EQuote (ECompose (e : es))] =
      map (\es -> [EQuote (ECompose es)]) (findGroupings_ [e] es [])
    findGroupings (e : es) = findGroupings_ [e] es []

    findGroupings_ :: [Expr] -> [Expr] -> [[Expr]] -> [[Expr]]
    findGroupings_ _ [] os = os
    findGroupings_ ((EQuote l) : ls) ((EQuote r) : rs) os =
      let o = reverse ls ++ [EQuote (ECompose [l, r])] ++ rs
       in findGroupings_ (EQuote r : EQuote l : ls) rs (o : os)
    findGroupings_ (l : ls) (r : rs) os =
      findGroupings_ (r : l : ls) rs os

allExprsUpToWidthAndDepth :: Int -> Int -> [Expr]
allExprsUpToWidthAndDepth width depth =
  concatMap (`allExprsOfWidthUpToDepth` depth) [1 .. width]
