-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# LANGUAGE NamedFieldPuns #-}

module Language.Dawn.Phase1.PreludeSpec (spec) where

import qualified Data.Map as Map
import Data.Maybe
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.Prelude
import Test.Hspec

spec :: Spec
spec = do
  describe "preludeEnv" $ do
    it "includes Bit" $ do
      let Env {dataDefs, typeConsArities, consDefs, consTypes} = preludeEnv
      isJust (Map.lookup "Bit" dataDefs) `shouldBe` True
      Map.lookup "Bit" typeConsArities `shouldBe` Just 0
      isJust (Map.lookup "B0" consDefs) `shouldBe` True
      isJust (Map.lookup "B1" consDefs) `shouldBe` True
      Map.lookup "B0" consTypes `shouldBe` Just ([], TCons [] "Bit")
      Map.lookup "B1" consTypes `shouldBe` Just ([], TCons [] "Bit")

    it "includes Byte" $ do
      let Env {dataDefs, typeConsArities, consDefs, consTypes} = preludeEnv
      isJust (Map.lookup "Byte" dataDefs) `shouldBe` True
      Map.lookup "Byte" typeConsArities `shouldBe` Just 0
      isJust (Map.lookup "Byte" consDefs) `shouldBe` True
      Map.lookup "Byte" consTypes `shouldBe` Just (replicate 8 (TCons [] "Bit"), TCons [] "Byte")
