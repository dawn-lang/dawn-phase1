-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

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

[clone, drop, swap, quote, compose, apply] =
  map EIntrinsic [IClone, IDrop, ISwap, IQuote, ICompose, IApply]

spec :: Spec
spec = do
  describe "partialEval" $ do
    it "evals `[clone] clone`" $ do
      let e = ECompose [EQuote clone, clone]
      let e' = ECompose [EQuote clone, EQuote clone]
      partialEval e `shouldBe` e'

    it "evals `[clone] drop`" $ do
      let e = ECompose [EQuote clone, drop]
      let e' = ECompose []
      partialEval e `shouldBe` e'

    it "evals `[clone] [drop] swap`" $ do
      let e = ECompose [EQuote clone, EQuote drop, swap]
      let e' = ECompose [EQuote drop, EQuote clone]
      partialEval e `shouldBe` e'

    it "evals `[clone] quote`" $ do
      let e = ECompose [EQuote clone, quote]
      let e' = EQuote (EQuote clone)
      partialEval e `shouldBe` e'

    it "evals `[clone] [clone] compose`" $ do
      let e = ECompose [EQuote clone, EQuote clone, compose]
      let e' = EQuote (ECompose [clone, clone])
      partialEval e `shouldBe` e'

    it "evals `[clone] apply`" $ do
      let e = ECompose [EQuote clone, apply]
      let e' = clone
      partialEval e `shouldBe` e'

    it "evals `[([swap] clone) compose]`" $ do
      let (Right e) = parseExpr "[([swap] clone) compose]"
      let (Right e') = parseExpr "[[swap swap]]"
      partialEval e `shouldBe` e'

    it "evals `[swap] (clone compose)`" $ do
      let (Right e) = parseExpr "[swap] (clone compose)"
      let (Right e') = parseExpr "[swap swap]"
      partialEval e `shouldBe` e'

    it "evals `[clone apply] clone apply`" $ do
      let (Right e) = parseExpr "[clone apply] clone apply"
      let (Right e') = parseExpr "[clone apply] clone apply"
      partialEval e `shouldBe` e'
