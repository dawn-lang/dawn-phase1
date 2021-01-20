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
      let (Right v) = parseVal "[clone] [clone]"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `[clone] drop`" $ do
      let (Right e) = parseExpr "[clone] drop"
      let ms = MultiStack Map.empty
      eval' e `shouldBe` ms

    it "evals `[clone] quote`" $ do
      let (Right e) = parseExpr "[clone] quote"
      let (Right v) = parseVal "[[clone]]"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `[clone] [clone] compose`" $ do
      let (Right e) = parseExpr "[clone] [clone] compose"
      let (Right v) = parseVal "[clone clone]"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 [clone] apply`" $ do
      let (Right e) = parseExpr "0 [clone] apply"
      let (Right v) = parseVal "0 0"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 [clone] apply`" $ do
      let (Right e) = parseExpr "0 [clone] apply"
      let (Right v) = parseVal "0 0"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `[drop] (clone compose)`" $ do
      let (Right e) = parseExpr "[drop] (clone compose)"
      let (Right v) = parseVal "[drop drop]"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 eqz`" $ do
      let (Right e) = parseExpr "0 eqz"
      let (Right v) = parseVal "1"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 eqz`" $ do
      let (Right e) = parseExpr "1 eqz"
      let (Right v) = parseVal "0"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `2 2 add`" $ do
      let (Right e) = parseExpr "2 2 add"
      let (Right v) = parseVal "4"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `4 2 sub`" $ do
      let (Right e) = parseExpr "4 2 sub"
      let (Right v) = parseVal "2"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `2 3 bit_and`" $ do
      let (Right e) = parseExpr "2 3 bit_and"
      let (Right v) = parseVal "2"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 2 bit_or`" $ do
      let (Right e) = parseExpr "1 2 bit_or"
      let (Right v) = parseVal "3"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 6 bit_xor`" $ do
      let (Right e) = parseExpr "5 6 bit_xor"
      let (Right v) = parseVal "3"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 2 shl`" $ do
      let (Right e) = parseExpr "1 2 shl"
      let (Right v) = parseVal "4"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `8 2 shr`" $ do
      let (Right e) = parseExpr "8 2 shr"
      let (Right v) = parseVal "2"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 1 $a<- $b<- $a-> $b->`" $ do
      let (Right e) = parseExpr "0 1 $a<- $b<- $a-> $b->"
      let (Right v) = parseVal "1 0"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 1 ($a: push eqz pop) sub eqz`" $ do
      let (Right e) = parseExpr "0 1 ($a: push eqz pop) sub eqz"
      let (Right v) = parseVal "1"
      let vs = reverse (toValSeq v)
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms
