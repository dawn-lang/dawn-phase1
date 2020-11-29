-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Exprs
  ( allExprsOfWidthUpToDepth,
    allExprsUpToWidthAndDepth,
    allUnquotedExprsOfWidth,
    intToIntrinsic,
  )
where

import Control.Monad
import Language.Dawn.Phase1.Core

intToIntrinsic :: Int -> Expr
intToIntrinsic 0 = EIntrinsic IClone
intToIntrinsic 1 = EIntrinsic IDrop
intToIntrinsic 2 = EIntrinsic ISwap
intToIntrinsic 3 = EIntrinsic IQuote
intToIntrinsic 4 = EIntrinsic ICompose
intToIntrinsic 5 = EIntrinsic IApply

allIntCombinations :: Int -> Int -> Int -> [[Int]]
allIntCombinations width min max = replicateM width [min .. max]

allIntrinsicCombinations :: Int -> [[Expr]]
allIntrinsicCombinations width =
  map (map intToIntrinsic) (allIntCombinations width 0 5)

allUnquotedExprsOfWidth :: Int -> [Expr]
allUnquotedExprsOfWidth width = map ECompose (allIntrinsicCombinations width)

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
