-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.EvalSpec (spec) where

import Control.Exception
import Control.Monad
import Data.Either
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Exprs
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.PartialEval
import Language.Dawn.Phase1.Utils
import Test.Hspec
import Prelude hiding (drop, (*))

[clone, drop, quote, compose, apply] =
  map EIntrinsic [IClone, IDrop, IQuote, ICompose, IApply]

spec :: Spec
spec = do
  describe "eval'" $ do
    it "evals `[clone] clone`" $ do
      let (Right e) = parseExpr "[clone] clone"
      let (Right vs) = parseVals "[clone] [clone]"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `[clone] drop`" $ do
      let (Right e) = parseExpr "[clone] drop"
      let ms = MultiStack Map.empty
      eval' e `shouldBe` ms

    it "evals `[clone] quote`" $ do
      let (Right e) = parseExpr "[clone] quote"
      let (Right vs) = parseVals "[[clone]]"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `[clone] [clone] compose`" $ do
      let (Right e) = parseExpr "[clone] [clone] compose"
      let (Right vs) = parseVals "[clone clone]"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 [clone] apply`" $ do
      let (Right e) = parseExpr "0 [clone] apply"
      let (Right vs) = parseVals "0 0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `[drop] (clone compose)`" $ do
      let (Right e) = parseExpr "[drop] (clone compose)"
      let (Right vs) = parseVals "[drop drop]"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `True True and`" $ do
      let (Right e) = parseExpr "True True and"
      let (Right vs) = parseVals "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `True False or`" $ do
      let (Right e) = parseExpr "True False or"
      let (Right vs) = parseVals "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `False not`" $ do
      let (Right e) = parseExpr "False not"
      let (Right vs) = parseVals "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `True False xor`" $ do
      let (Right e) = parseExpr "True False xor"
      let (Right vs) = parseVals "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 incr`" $ do
      let (Right e) = parseExpr "0 incr"
      let (Right vs) = parseVals "1"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 decr`" $ do
      let (Right e) = parseExpr "1 decr"
      let (Right vs) = parseVals "0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `2 2 add`" $ do
      let (Right e) = parseExpr "2 2 add"
      let (Right vs) = parseVals "4"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `4 2 sub`" $ do
      let (Right e) = parseExpr "4 2 sub"
      let (Right vs) = parseVals "2"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `2 3 bit_and`" $ do
      let (Right e) = parseExpr "2 3 bit_and"
      let (Right vs) = parseVals "2"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 2 bit_or`" $ do
      let (Right e) = parseExpr "1 2 bit_or"
      let (Right vs) = parseVals "3"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 bit_not bit_not`" $ do
      let (Right e) = parseExpr "0 bit_not bit_not"
      let (Right vs) = parseVals "0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 6 bit_xor`" $ do
      let (Right e) = parseExpr "5 6 bit_xor"
      let (Right vs) = parseVals "3"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 2 shl`" $ do
      let (Right e) = parseExpr "1 2 shl"
      let (Right vs) = parseVals "4"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `8 2 shr`" $ do
      let (Right e) = parseExpr "8 2 shr"
      let (Right vs) = parseVals "2"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 5 eq`" $ do
      let (Right e) = parseExpr "5 5 eq"
      let (Right vs) = parseVals "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 5 lt`" $ do
      let (Right e) = parseExpr "5 5 lt"
      let (Right vs) = parseVals "False"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 5 gt`" $ do
      let (Right e) = parseExpr "5 5 gt"
      let (Right vs) = parseVals "False"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 5 lteq`" $ do
      let (Right e) = parseExpr "5 5 lteq"
      let (Right vs) = parseVals "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 5 gteq`" $ do
      let (Right e) = parseExpr "5 5 gteq"
      let (Right vs) = parseVals "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 1 $a<- $b<- $a-> $b->`" $ do
      let (Right e) = parseExpr "0 1 $a<- $b<- $a-> $b->"
      let (Right vs) = parseVals "1 0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `{match {case =>}}`" $ do
      let (Right e) = parseExpr "{match {case =>}}"
      let ms = MultiStack Map.empty
      eval' e `shouldBe` ms

    it "evals `0 {match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "0 {match {case 0 => 1} {case => drop 0}}"
      let (Right vs) = parseVals "1"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 {match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "1 {match {case 0 => 1} {case => drop 0}}"
      let (Right vs) = parseVals "0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 0 {match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "0 0 {match {case 0 0 => 1} {case => drop drop 0}}"
      let (Right vs) = parseVals "1"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 1 {match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "0 1 {match {case 0 0 => 1} {case => drop drop 0}}"
      let (Right vs) = parseVals "0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals fib" $ do
      let (Right env) = defineFn Map.empty swap
      let (Right env') = defineFn env fib
      let (Right e) = parseExpr "0 fib"
      let (Right vs) = parseVals "0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval env' ["$"] e (MultiStack Map.empty) `shouldBe` ms

      let (Right e) = parseExpr "1 fib"
      let (Right vs) = parseVals "1"
      let ms = MultiStack (Map.singleton "$" vs)
      eval env' ["$"] e (MultiStack Map.empty) `shouldBe` ms

      let (Right e) = parseExpr "6 fib"
      let (Right vs) = parseVals "8"
      let ms = MultiStack (Map.singleton "$" vs)
      eval env' ["$"] e (MultiStack Map.empty) `shouldBe` ms

  describe "evalWithFuel" $ do
    it "stops at 0 fuel" $ do
      let (Right e) = parseExpr "0"
      let ms = MultiStack Map.empty
      evalWithFuel Map.empty ["$"] (0, e, ms) `shouldBe` (0, e, ms)

    it "allows negative fuel" $ do
      let (Right e) = parseExpr "0"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseVals "0"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel Map.empty ["$"] (-1, e, ms) `shouldBe` (-2, e', ms')

    it "evals `0 [clone] apply`" $ do
      let (Right e) = parseExpr "0 [clone] apply"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseVals "0 0"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel Map.empty ["$"] (4, e, ms) `shouldBe` (0, e', ms')

    it "evals `0 1 $a<- $b<- $a-> $b->`" $ do
      let (Right e) = parseExpr "0 1 $a<- $b<- $a-> $b->"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseVals "1 0"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel Map.empty ["$"] (6, e, ms) `shouldBe` (0, e', ms')

    it "evals `{match {case =>}}`" $ do
      let (Right e) = parseExpr "{match {case =>}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let ms' = MultiStack Map.empty
      evalWithFuel Map.empty ["$"] (1, e, ms) `shouldBe` (0, e', ms')

    it "evals `0 {match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "0 {match {case 0 => 1} {case => drop 0}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseVals "1"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel Map.empty ["$"] (3, e, ms) `shouldBe` (0, e', ms')

    it "evals `1 {match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "1 {match {case 0 => 1} {case => drop 0}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseVals "0"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel Map.empty ["$"] (5, e, ms) `shouldBe` (0, e', ms')

    it "evals `0 0 {match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "0 0 {match {case 0 0 => 1} {case => drop drop 0}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseVals "1"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel Map.empty ["$"] (4, e, ms) `shouldBe` (0, e', ms')

    it "evals `0 1 {match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "0 1 {match {case 0 0 => 1} {case => drop drop 0}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseVals "0"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel Map.empty ["$"] (7, e, ms) `shouldBe` (0, e', ms')

    it "evals `fib`" $ do
      let ([], env) = defineFns Map.empty [swap, fib]
          evalFib n =
            let (Right e) = parseExpr (show n ++ " fib")
                ms = MultiStack Map.empty
                e' = ECompose []
             in evalWithFuel env ["$"] (-1, e, ms)
          n `inSteps` steps =
            let (Right vs) = parseVals (show n)
             in (-1 - steps, ECompose [], MultiStack (Map.singleton "$" vs))

      evalFib 0 `shouldBe` 0 `inSteps` 4
      evalFib 1 `shouldBe` 1 `inSteps` 5
      evalFib 2 `shouldBe` 1 `inSteps` 23
      evalFib 3 `shouldBe` 2 `inSteps` 42
      evalFib 4 `shouldBe` 3 `inSteps` 79
      evalFib 5 `shouldBe` 5 `inSteps` 135
      evalFib 6 `shouldBe` 8 `inSteps` 228
      evalFib 7 `shouldBe` 13 `inSteps` 377
      evalFib 8 `shouldBe` 21 `inSteps` 619
      evalFib 9 `shouldBe` 34 `inSteps` 1010

swapSrc = "{fn swap => $a<- $b<- $a-> $b->}"

(Right swap) = parseFnDef swapSrc

fibSrc =
  unlines
    [ "{fn fib => {match",
      "  {case 0 => 0}",
      "  {case 1 => 1}",
      "  {case => clone 1 sub fib swap 2 sub fib add}",
      "}}"
    ]

(Right fib) = parseFnDef fibSrc
