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

swapSrc = "{fn swap = $a<- $b<- $a-> $b->}"

(Right swap) = parseFnDef swapSrc

fibSrc =
  unlines
    [ "{fn fib = {match",
      "  {case 0 => 0}",
      "  {case 1 => 1}",
      "  {case => clone 1 sub fib swap 2 sub fib add}",
      "}}"
    ]

(Right fib) = parseFnDef fibSrc
