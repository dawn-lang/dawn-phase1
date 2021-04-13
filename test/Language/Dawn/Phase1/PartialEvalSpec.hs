-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option. This file may not be
-- copied, modified, or distributed except according to those terms.

module Language.Dawn.Phase1.PartialEvalSpec (spec) where

import Control.Exception
import Control.Monad
import Data.Either
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
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
  describe "partialEval'" $ do
    it "evals `[clone] clone`" $ do
      let e = ECompose [EQuote clone, clone]
      let e' = ECompose [EQuote clone, EQuote clone]
      partialEval' e `shouldBe` e'

    it "evals `[clone] drop`" $ do
      let e = ECompose [EQuote clone, drop]
      let e' = ECompose []
      partialEval' e `shouldBe` e'

    it "evals `[clone] quote`" $ do
      let e = ECompose [EQuote clone, quote]
      let e' = EQuote (EQuote clone)
      partialEval' e `shouldBe` e'

    it "evals `[clone] [clone] compose`" $ do
      let e = ECompose [EQuote clone, EQuote clone, compose]
      let e' = EQuote (ECompose [clone, clone])
      partialEval' e `shouldBe` e'

    it "evals `[clone] apply`" $ do
      let e = ECompose [EQuote clone, apply]
      let e' = clone
      partialEval' e `shouldBe` e'

    it "evals `[([drop] clone) compose]`" $ do
      let (Right e) = parseExpr "[([drop] clone) compose]"
      let (Right e') = parseExpr "[[drop drop]]"
      partialEval' e `shouldBe` e'

    it "evals `[drop] (clone compose)`" $ do
      let (Right e) = parseExpr "[drop] (clone compose)"
      let (Right e') = parseExpr "[drop drop]"
      partialEval' e `shouldBe` e'

    it "evals `[clone apply] clone apply`" $ do
      let (Right e0) = parseExpr "[clone apply] clone apply"
      let (Right e1) = parseExpr "[clone apply] [clone apply] apply"
      let (Right e2) = parseExpr "[clone apply] (clone apply)"
      partialEval 1 e0 `shouldBe` (0, e1)
      partialEval 2 e0 `shouldBe` (0, e2)
      partialEval 3 e0 `shouldBe` (0, e0)
      partialEval 4 e0 `shouldBe` (0, e1)
      partialEval 5 e0 `shouldBe` (0, e2)
      partialEval 6 e0 `shouldBe` (0, e0)

    it "evals `{spread $a $a $b} {collect $a $a $b}`" $ do
      let (Right e) = parseExpr "{spread $a $a $b} {collect $a $a $b}"
      let (Right e') = parseExpr ""
      partialEval' e `shouldBe` e'
