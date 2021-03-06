-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Language.Dawn.Phase1.UtilsSpec (spec) where

import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.Utils
import Test.Hspec
import Text.Parsec.Error
import Text.Parsec.Pos
import Prelude hiding (drop, (*))

[v0, v1] = map (TVar . TypeVar) [0 .. 1]

spec :: Spec
spec = do
  describe "removeTrivialStacks" $ do
    it "removes trivial stacks" $ do
      let t = forall [v0, v1] ("$" $: v0 --> v0 $. "$a" $: v0 --> v0)
      let t' = forall [v0] ("$" $: v0 --> v0)
      removeTrivialStacks t `shouldBe` t'

    it "leaves `∀v0 . v0 -> v0`" $ do
      let t = forall' [v0] (v0 --> v0)
      removeTrivialStacks t `shouldBe` t
