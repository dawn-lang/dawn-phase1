-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.ParseSpec (spec) where

import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Parse
import Test.Hspec
import Text.Parsec.Error
import Text.Parsec.Pos
import Prelude hiding (drop, (*))

[clone, drop, swap, quote, compose, apply] =
  map EIntrinsic [IClone, IDrop, ISwap, IQuote, ICompose, IApply]

spec :: Spec
spec = do
  describe "parseExpr" $ do
    it "parses ``" $ do
      parseExpr "" `shouldBe` Right (ECompose [])

    it "parses `()`" $ do
      parseExpr "()" `shouldBe` Right (ECompose [])

    it "parses `clone`" $ do
      parseExpr "clone" `shouldBe` Right clone

    it "parses `drop`" $ do
      parseExpr "drop" `shouldBe` Right drop

    it "parses `swap`" $ do
      parseExpr "swap" `shouldBe` Right swap

    it "parses `quote`" $ do
      parseExpr "quote" `shouldBe` Right quote

    it "parses `compose`" $ do
      parseExpr "compose" `shouldBe` Right compose

    it "parses `apply`" $ do
      parseExpr "apply" `shouldBe` Right apply

    it "parses `clone drop swap quote compose apply`" $ do
      parseExpr "clone drop swap quote compose apply"
        `shouldBe` Right (ECompose [clone, drop, swap, quote, compose, apply])

    it "parses `[clone] apply`" $ do
      parseExpr "[clone] apply"
        `shouldBe` Right (ECompose [EQuote clone, apply])

    it "parses `[[clone] apply]`" $ do
      parseExpr "[[clone] apply]"
        `shouldBe` Right (EQuote (ECompose [EQuote clone, apply]))

    it "parses `(clone swap) clone`" $ do
      parseExpr "(clone swap) clone"
        `shouldBe` Right  (ECompose [ECompose [clone, swap], clone])

    it "parses `clone (swap clone)`" $ do
      parseExpr "clone (swap clone)"
        `shouldBe` Right  (ECompose [clone, ECompose [swap, clone]])

    it "fails on `foo`" $ do
      let (Left err) = parseExpr "foo"
      let pos = errorPos err
      sourceLine pos `shouldBe` 1
      sourceColumn pos `shouldBe` 1
