-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Language.Dawn.Phase1.TryAddElementsSpec (spec) where

import Control.Monad.Except
import Data.Either
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Exprs
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.TryAddElements
import Language.Dawn.Phase1.Utils
import Test.Hspec

spec :: Spec
spec = do
  describe "tryAddElements" $ do
    it "adds Bool, Nat, and is_odd" $ do
      let boolDefSrc = "{data Bool {cons False} {cons True}}"
      let natDefSrc = "{data Nat {cons Z} {cons Nat S}}"
      let isOddDeclSrc = "{fn is_odd :: forall v0 . v0 Nat -> v0 Bool}"
      let isOddDefSrc =
            unlines
              [ "{fn is_odd => {match",
                "    {case Z => False}",
                "    {case (Z S) => True}",
                "    {case (S S) => is_odd}",
                "}}"
              ]
      let (Right elems) =
            parseElements
              (unlines [boolDefSrc, natDefSrc, isOddDeclSrc, isOddDefSrc])
      let (Right boolDef) = parseDataDef boolDefSrc
      let (Right natDef) = parseDataDef natDefSrc
      let (Right isOddDecl) = parseFnDecl isOddDeclSrc
      let (Right isOddDef) = parseFnDef isOddDefSrc
      let ([], env) = addDataDefs emptyEnv [boolDef, natDef]
      let (Right env') = tryAddFnDecl env isOddDecl
      let (Right env'') = tryAddFnDefs env' [isOddDef]
      result <- runExceptT (tryAddElements emptyEnv elems)
      result `shouldBe` Right env''

    it "includes `test/Test1.dn`" $ do
      let src1 = "{include \"test/Test1.dn\"}"
      let (Right elems1) = parseElements src1
      result1 <- runExceptT (tryAddElements emptyEnv elems1)

      let src2 =
            unlines
              [ "{data Test1 {cons Test1}}",
                "{fn test1 :: Test1}",
                "{fn test1 => Test1}",
                ""
              ]
      let (Right elems2) = parseElements src2
      (Right env) <- runExceptT (tryAddElements emptyEnv elems2)

      result1 `shouldBe` Right env

    it "includes `test/Test2.dn`" $ do
      let src1 = "{include \"test/Test2.dn\"}"
      let (Right elems1) = parseElements src1
      result1 <- runExceptT (tryAddElements emptyEnv elems1)

      let src2 =
            unlines
              [ "{data Test1 {cons Test1}}",
                "{fn test1 :: Test1}",
                "{fn test1 => Test1}",
                "{data Test2 {cons Test2}}",
                "{fn test2 => Test2}",
                ""
              ]
      let (Right elems2) = parseElements src2
      (Right env) <- runExceptT (tryAddElements emptyEnv elems2)

      result1 `shouldBe` Right env
