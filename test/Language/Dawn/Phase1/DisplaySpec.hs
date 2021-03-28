-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.DisplaySpec (spec) where

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
      let (Right val) = parseVals str
      unwords (map display val) `shouldBe` str

    it "displays `B0`" $ do
      let str = "B0"
      let (Right val) = parseVals str
      unwords (map display val) `shouldBe` str

    it "displays `(Empty B0 Push)`" $ do
      let str = "(Empty B0 Push)"
      let (Right val) = parseVals str
      unwords (map display val) `shouldBe` str

    it "displays `((Empty B0 A) Foo B)`" $ do
      let str = "((Empty B0 A) Foo B)"
      let (Right val) = parseVals str
      unwords (map display val) `shouldBe` str
