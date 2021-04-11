-- Copyright (c) 2021 Scott J Maddox
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
    it "displays `Z (Z S) True B0`" $ do
      let str = "Z (Z S) True B0"
      let (Right vs) = parseValStack str
      display vs `shouldBe` str

    it "displays `B0`" $ do
      let str = "B0"
      let (Right vs) = parseValStack str
      display vs `shouldBe` str

    it "displays `(Z (Z S) Pair)`" $ do
      let str = "(Z (Z S) Pair)"
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

  describe "Display MultiStack Val" $ do
    it "displays in order" $ do
      let str = "(Z S) ((Z S) S) True B0"
      let (Right vs) = parseValStack str
      -- Note: values are reversed so that the top of the stack
      -- is the front of the list and is easily accessible.
      let ms = MultiStack (Map.singleton "$" vs)
      display ms `shouldBe` "{$ (Z S) ((Z S) S) True B0}"

  describe "Display Type" $ do
    it "displays `(forall v0 . v0 Nat -> v0)`" $ do
      let (Right t) = parseFnType "forall v0 . v0 Nat -> v0"
      display t `shouldBe` "(∀ v0 . v0 Nat -> v0)"

    it "displays `(forall v0 . v0 Nat -> v0 Nat)`" $ do
      let (Right t) = parseFnType "forall v0 . v0 Nat -> v0 Nat"
      display t `shouldBe` "(∀ v0 . v0 Nat -> v0 Nat)"

    it "displays `(forall v0 v1 . v0 (v1 Stack) -> v0 (v1 Stack) v1)`" $ do
      let (Right t) = parseFnType "forall v0 v1 . v0 (v1 Stack) -> v0 (v1 Stack) v1"
      display t `shouldBe` "(∀ v0 v1 . v0 (v1 Stack) -> v0 (v1 Stack) v1)"

    it "displays `(forall v0 . v0 (Bit Stack) -> v0 (Bit Stack))`" $ do
      let (Right t) = parseFnType "forall v0 . v0 (Bit Stack) -> v0 (Bit Stack)"
      display t `shouldBe` "(∀ v0 . v0 (Bit Stack) -> v0 (Bit Stack))"

    it "displays `(forall v0 . v0 (Bit Stack) -> v0)`" $ do
      let (Right t) = parseFnType "forall v0 . v0 (Bit Stack) -> v0"
      display t `shouldBe` "(∀ v0 . v0 (Bit Stack) -> v0)"

    it "displays `(forall v0 . v0 (Bit Stack) -> v0 (Bit Stack) Bit)`" $ do
      let (Right t) = parseFnType "forall v0 . v0 (Bit Stack) -> v0 (Bit Stack) Bit"
      display t `shouldBe` "(∀ v0 . v0 (Bit Stack) -> v0 (Bit Stack) Bit)"

    it "displays `(forall v0 v1 . v0 (Nat (v1 Stack) Pair) -> v0 Nat (v1 Stack) v1)`" $ do
      let (Right t) = parseFnType "forall v0 v1 . v0 (Nat (v1 Stack) Pair) -> v0 Nat (v1 Stack) v1"
      display t `shouldBe` "(∀ v0 v1 . v0 (Nat (v1 Stack) Pair) -> v0 Nat (v1 Stack) v1)"

    it "displays `(forall v0 v1 v2 . v0 ((v1 Stack) (v2 Stack) Pair) -> v0 (v1 Stack) v1 (v2 Stack) v2)`" $ do
      let (Right t) = parseFnType "forall v0 v1 v2 . v0 ((v1 Stack) (v2 Stack) Pair) -> v0 (v1 Stack) v1 (v2 Stack) v2"
      display t `shouldBe` "(∀ v0 v1 v2 . v0 ((v1 Stack) (v2 Stack) Pair) -> v0 (v1 Stack) v1 (v2 Stack) v2)"
