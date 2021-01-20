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

[clone, drop, quote, compose, apply] =
  map EIntrinsic [IClone, IDrop, IQuote, ICompose, IApply]

spec :: Spec
spec = do
  describe "parseExpr" $ do
    it "parses ``" $ do
      parseExpr "" `shouldBe` Right (ECompose [])

    it "parses `()`" $ do
      parseExpr "()" `shouldBe` Right (ECompose [])

    it "parses `push`" $ do
      parseExpr "push"
        `shouldBe` Right (EIntrinsic IPush)

    it "parses `pop`" $ do
      parseExpr "pop"
        `shouldBe` Right (EIntrinsic IPop)

    it "parses `clone`" $ do
      parseExpr "clone" `shouldBe` Right clone

    it "parses `drop`" $ do
      parseExpr "drop" `shouldBe` Right drop

    it "parses `quote`" $ do
      parseExpr "quote" `shouldBe` Right quote

    it "parses `compose`" $ do
      parseExpr "compose" `shouldBe` Right compose

    it "parses `apply`" $ do
      parseExpr "apply" `shouldBe` Right apply

    it "parses `eqz`" $ do
      parseExpr "eqz" `shouldBe` Right (EIntrinsic IEqz)

    it "parses `add`" $ do
      parseExpr "add" `shouldBe` Right (EIntrinsic IAdd)

    it "parses `sub`" $ do
      parseExpr "sub" `shouldBe` Right (EIntrinsic ISub)

    it "parses `bit_and`" $ do
      parseExpr "bit_and" `shouldBe` Right (EIntrinsic IBitAnd)

    it "parses `bit_or`" $ do
      parseExpr "bit_or" `shouldBe` Right (EIntrinsic IBitOr)

    it "parses `bit_xor`" $ do
      parseExpr "bit_xor" `shouldBe` Right (EIntrinsic IBitXor)

    it "parses `shl`" $ do
      parseExpr "shl" `shouldBe` Right (EIntrinsic IShl)

    it "parses `shr`" $ do
      parseExpr "shr" `shouldBe` Right (EIntrinsic IShr)

    it "parses `clone drop quote compose apply`" $ do
      parseExpr "clone drop quote compose apply"
        `shouldBe` Right (ECompose [clone, drop, quote, compose, apply])

    it "parses `[clone] apply`" $ do
      parseExpr "[clone] apply"
        `shouldBe` Right (ECompose [EQuote clone, apply])

    it "parses `[[clone] apply]`" $ do
      parseExpr "[[clone] apply]"
        `shouldBe` Right (EQuote (ECompose [EQuote clone, apply]))

    it "parses `(clone drop) clone`" $ do
      parseExpr "(clone drop) clone"
        `shouldBe` Right (ECompose [ECompose [clone, drop], clone])

    it "parses `clone (drop clone)`" $ do
      parseExpr "clone (drop clone)"
        `shouldBe` Right (ECompose [clone, ECompose [drop, clone]])

    it "fails on `foo`" $ do
      let (Left err) = parseExpr "foo"
      let pos = errorPos err
      sourceLine pos `shouldBe` 1
      sourceColumn pos `shouldBe` 1

    it "parses `($a: drop)`" $ do
      parseExpr "($a: drop)"
        `shouldBe` Right (EContext "$a" (EIntrinsic IDrop))

    it "parses `($_Ab12_C: drop)`" $ do
      parseExpr "($_Ab12_C: drop)"
        `shouldBe` Right (EContext "$_Ab12_C" (EIntrinsic IDrop))

    it "fails on `($1234: drop)`" $ do
      let (Left err) = parseExpr "($1234: drop)"
      let pos = errorPos err
      sourceLine pos `shouldBe` 1
      sourceColumn pos `shouldBe` 3

    it "parses `$a<-`" $ do
      parseExpr "$a<-"
        `shouldBe` Right (EContext "$a" (EIntrinsic IPush))

    it "parses `$a->`" $ do
      parseExpr "$a->"
        `shouldBe` Right (EContext "$a" (EIntrinsic IPop))

    it "parses `123`" $ do
      parseExpr "123"
        `shouldBe` Right (ELit (LU32 123))

    it "parses `($a: 123)`" $ do
      parseExpr "($a: 123)"
        `shouldBe` Right (EContext "$a" (ELit (LU32 123)))
