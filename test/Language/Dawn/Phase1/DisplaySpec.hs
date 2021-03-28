-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.DisplaySpec (spec) where

import Data.Either.Combinators
import qualified Data.Map as Map
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Parse
import Test.Hspec

spec :: Spec
spec = do
  describe "Display Val" $ do
    it "displays `1 2 True B0`" $ do
      let str = "1 2 True B0"
      let (Right vs) = parseValStack str
      display vs `shouldBe` str

    it "displays `B0`" $ do
      let str = "B0"
      let (Right vs) = parseValStack str
      display vs `shouldBe` str

    it "displays `(0 1 Pair)`" $ do
      let str = "(0 1 Pair)"
      let (Right vs) = parseValStack str
      display vs `shouldBe` str

    it "displays `(Empty B0 Push)`" $ do
      let str = "(Empty B0 Push)"
      let (Right vs) = parseValStack str
      display vs `shouldBe` str

    it "displays `((Empty B0 A) Foo B)`" $ do
      let str = "((Empty B0 A) Foo B)"
      let (Right vs) = parseValStack str
      display vs `shouldBe` str

  describe "Display MultiStack" $ do
    it "displays in order" $ do
      let str = "1 2 True B0"
      let (Right vs) = parseValStack str
      -- Note: values are reversed so that the top of the stack
      -- is the front of the list and is easily accessible.
      let ms = MultiStack (Map.singleton "$" vs)
      display ms `shouldBe` "{$: 1 2 True B0}"
