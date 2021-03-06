-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# LANGUAGE NamedFieldPuns #-}

module Language.Dawn.Phase1.CoreSpec (spec, testEnv) where

import Control.Exception
import Control.Monad
import Data.Either
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Exprs
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.Prelude
import Language.Dawn.Phase1.Utils
import Test.Hspec
import Prelude hiding (drop, (*))

[tv0, tv1, tv2, tv3, tv4, tv5, _, _, tv8] = map TypeVar [0 .. 8]

[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] = map (TVar . TypeVar) [0 .. 10]

tBool = TCons [] "Bool"

tNat = TCons [] "Nat"

spec :: Spec
spec = do
  describe "renameTypeVar" $ do
    it "renames the specified type variable" $ do
      renameTypeVar tv0 tv2 (forall' [v0, v1] (v0 --> v0 * v1))
        `shouldBe` forall' [v2, v1] (v2 --> v2 * v1)

    it "throws on type variable shadowing" $ do
      evaluate (renameTypeVar tv0 tv1 (forall' [v0, v1] (v0 --> v0 * v1)))
        `shouldThrow` anyException

  describe "ftv" $ do
    it "returns the free type variables" $ do
      ftv (forall' [v2] (v2 * v0 --> v2 * v3 * forall' [v1] (v1 * v4 --> v1 * v5)))
        `shouldBe` Set.fromList (map TypeVar [0, 3, 4, 5])

  describe "atv" $ do
    it "returns all type variables, in the order they appear" $ do
      atv (forall' [v2] (v2 * v0 --> v2 * v3 * forall' [v1] (v1 * v4 --> v1 * v5)))
        `shouldBe` map TypeVar [2, 0, 3, 1, 4, 5]

  describe "freshTypeVar" $ do
    it "returns the first fresh type variable" $ do
      freshTypeVar (Set.fromList (map TypeVar [0, 1, 2, 4, 5]))
        `shouldBe` (TypeVar 3, Set.fromList (map TypeVar [0, 1, 2, 3, 4, 5]))

  describe "replaceTypeVars" $ do
    it "replaces the specified type variables with fresh type variables" $ do
      let tvs = [tv2, tv1]
      let t = forall' [v1] (v1 --> v1 * v2)
      let reserved = Set.fromList [tv0, tv1, tv2, tv3]
      let t' = forall' [v5] (v5 --> v5 * v4)
      let reserved' = Set.fromList [tv0, tv1, tv2, tv3, tv4, tv5]
      replaceTypeVars tvs t reserved
        `shouldBe` (t', reserved')

  describe "instantiate" $ do
    it "instantiates all quantified type variables with fresh type variables" $ do
      let t = forall' [v1] (v1 --> v1 * v2)
      let reserved = Set.fromList [tv0, tv1, tv2, tv3]
      let t' = forall' [v4] (v4 --> v4 * v2)
      let reserved' = Set.fromList [tv0, tv1, tv2, tv3, tv4]
      instantiate t reserved
        `shouldBe` (t', reserved')

  describe "addMissingStacks" $ do
    it "adds missing stacks" $ do
      let t1 = forall [v0] ("a" $: v0 --> v0)
      let t2 = forall [v1] ("b" $: v1 --> v1)
      let reserved = Set.fromList [tv0, tv1]
      let t1' = forall [v0, v2] ("a" $: v0 --> v0 $. "b" $: v2 --> v2)
      let t2' = forall [v1, v3] ("a" $: v3 --> v3 $. "b" $: v1 --> v1)
      let reserved' = Set.fromList [tv0, tv1, tv2, tv3]
      addMissingStacks (t1, t2, reserved) `shouldBe` (t1', t2', reserved')

    it "adds missing stacks in nested function types" $ do
      let nt1 = forall [v2] ("a" $: v2 --> v2)
      let nt2 = forall [v3] ("b" $: v3 --> v3)
      let t1 = forall' [v0] (v0 * nt1 --> v0)
      let t2 = forall' [v1] (v1 * nt2 --> v1)
      let reserved = Set.fromList [tv0, tv1, tv2, tv3]
      let nt1' = forall [v2, v4] ("a" $: v2 --> v2 $. "b" $: v4 --> v4)
      let nt2' = forall [v3, v5] ("a" $: v5 --> v5 $. "b" $: v3 --> v3)
      let t1' = forall' [v0] (v0 * nt1' --> v0)
      let t2' = forall' [v1] (v1 * nt2' --> v1)
      let reserved' = Set.fromList [tv0, tv1, tv2, tv3, tv4, tv5]
      addMissingStacks (t1, t2, reserved) `shouldBe` (t1', t2', reserved')

  describe "subs" $ do
    it "applies substitutions" $ do
      let t = forall' [v1] (v0 --> v0 * v1)
      let t' = forall' [v1] (v2 --> v2 * v1)
      subs (tv0 +-> v2) t (Set.fromList $ atv t)
        `shouldBe` (t', Set.fromList $ atv t ++ atv t')

    it "instantiates quantified type variables" $ do
      let s = tv0 +-> forall' [v1] (v1 --> v1 * v2)
      let t = v0
      let reserved = Set.fromList [tv0, tv1, tv2]
      let t' = forall' [v3] (v3 --> v3 * v2)
      let reserved' = Set.fromList [tv0, tv1, tv2, tv3]
      subs s t reserved
        `shouldBe` (t', reserved')

  describe "composeSubst" $ do
    it "composes substitutions" $ do
      let reserved = Set.fromList [tv0, tv1, tv2]
      composeSubst (tv1 +-> v2) (tv0 +-> v1) reserved
        `shouldBe` (Subst (Map.fromList [(tv0, v2), (tv1, v2)]), reserved)

    it "avoids type variable capture" $ do
      let s1 = tv0 +-> forall' [v2] (v2 --> v2 * v1)
      let s2 = tv1 +-> forall' [v2, v3] (v2 * v3 --> v2 * v3)
      let reserved = Set.fromList [tv0, tv1, tv2, tv3]

      let s1' = tv0 +-> forall' [v2] (v2 --> v2 * forall' [v4, v5] (v4 * v5 --> v4 * v5))
      let s2' = tv1 +-> forall' [v2, v3] (v2 * v3 --> v2 * v3)
      let reserved' = Set.fromList [tv0, tv1, tv2, tv3, tv4, tv5]

      composeSubst s2 s1 reserved `shouldBe` composeSubst s2' s1' reserved'

  describe "mgu" $ do
    it "finds the most general unifier" $ do
      let t =
            forall'
              [v0, v2]
              ( v0 --> v0 * forall' [v1] (v1 --> v1 * v2) * v2 * v2
              )
      let t' =
            forall'
              [v3, v4, v5, v7, v8]
              ( v3 * v4 --> v3 * v4 * v5 * forall' [v6] (v6 --> v6 * v7) * v8
              )
      let reserved = Set.fromList (map TypeVar [0 .. 8])
      let s =
            Subst $
              Map.fromList
                [ (tv0, v3 * v4),
                  (tv5, forall' [v1] (v1 --> v1 * forall' [v9] (v9 --> v9 * v7))),
                  (tv2, forall' [v6] (v6 --> v6 * v7)),
                  (tv8, forall' [v10] (v10 --> v10 * v7))
                ]
      let reserved' = Set.fromList (map TypeVar [0 .. 10])
      mgu t t' reserved `shouldBe` Right (s, reserved')

    it "adds missing stacks" $ do
      let nt1 = forall [v2] ("a" $: v2 --> v2)
      let nt2 = forall [v3] ("b" $: v3 --> v3)
      let t1 = v0 * nt1
      let t2 = v1 * nt2
      let reserved = Set.fromList (map TypeVar [0 .. 3])
      let s = Subst $ Map.fromList [(tv1, v0), (tv3, v4), (tv5, v2)]
      let reserved' = Set.fromList (map TypeVar [0 .. 5])
      mgu t1 t2 reserved `shouldBe` Right (s, reserved')

  describe "requantify" $ do
    it "properly requantifies" $ do
      let t =
            forall'
              [v0, v1, v2]
              ( v0 * forall' [] (v1 --> v1)
                  --> v0 * forall' [] (v1 --> v1 * forall' [] (v2 --> v2))
              )
      let t' =
            forall'
              [v0, v1]
              ( v0 * forall' [] (v1 --> v1)
                  --> v0 * forall' [] (v1 --> v1 * forall' [v2] (v2 --> v2))
              )
      requantify t `shouldBe` t'

  describe "inferType invariants" $ do
    it "does not infer free type variables" $ do
      let iter e = case inferType' e of
            Left _ -> return ()
            Right t -> (display e, ftv t) `shouldBe` (display e, Set.empty)
      mapM_ iter (allExprsUpToWidthAndDepth 3 1)

    it "does not infer duplicate quantifiers" $ do
      let count :: Type -> Map.Map TypeVar Int
          count (TVar _) = Map.empty
          count (TProd l r) = Map.unionWith (+) (count l) (count r)
          count (TFn qs mio) =
            let iter' (i, o) = Map.unionWith (+) (count i) (count o)
                counts = foldr1 (Map.unionWith (+)) (map iter' (Map.elems mio))
                counts' = foldr (`Map.insert` 1) Map.empty (Set.toList qs)
             in Map.unionWith (+) counts counts'
          count (TCons _ _) = Map.empty -- Tfn is not allowed in TCons args
      let iter e = case inferType' e of
            Left _ -> return ()
            Right t ->
              (display e, any (> 1) (Map.elems (count t)))
                `shouldBe` (display e, False)
      mapM_ iter (allExprsUpToWidthAndDepth 3 1)

    it "does not infer unused quantifiers" $ do
      let iter e = case inferType' e of
            Left _ -> return ()
            Right t -> (display e, unusedQuantifiers t) `shouldBe` (display e, Set.empty)
      mapM_ iter (allExprsUpToWidthAndDepth 3 1)

  describe "inferType examples" $ do
    it "infers `[clone] apply` == `clone` " $ do
      let (Right e1) = parseExpr "[clone] apply"
      let (Right e2) = parseExpr "clone"
      inferNormType' e1 `shouldBe` inferNormType' e2

    it "infers `{$a push} {$b push} {$a pop} {$b pop}` is swap" $ do
      let (Right e) = parseExpr "{$a push} {$b push} {$a pop} {$b pop}"
      inferNormType' e
        `shouldBe` Right (forall' [v0, v1, v2] (v0 * v1 * v2 --> v0 * v2 * v1))

    it "infers `$a<- $b<- $a-> $b->` is swap" $ do
      let (Right e) = parseExpr "$a<- $b<- $a-> $b->"
      inferNormType' e
        `shouldBe` Right (forall' [v0, v1, v2] (v0 * v1 * v2 --> v0 * v2 * v1))

    it "infers `{$c swap}`" $ do
      let (Right e) = parseExpr "{$c $a<- $b<- $a-> $b->}"
      inferNormType' e
        `shouldBe` Right
          ( forall
              [v0, v1, v2]
              ("$c" $: v0 * v1 * v2 --> v0 * v2 * v1)
          )

    it "infers `{$a swap}`" $ do
      let (Right e) = parseExpr "{$a $a<- $b<- $a-> $b->}"
      inferNormType' e
        `shouldBe` Right
          ( forall
              [v0, v1, v2]
              ("$a" $: v0 * v1 * v2 --> v0 * v2 * v1)
          )

    it "infers `[clone] [swap apply] apply`" $ do
      let (Right e) = parseExpr "[clone] [$a<- $b<- $a-> $b-> apply] apply"
      let nnf = forall' [v1, v2] (v1 * v2 --> v1 * v2 * v2)
      let nf = forall' [] (v0 * nnf --> v3)
      let f = forall' [v0, v3] (v0 * nf --> v3)
      inferNormType' e `shouldBe` Right f

    it "infers `$a<- $b<- $a-> $b->` is swap in any context" $ do
      let (Right e) = parseExpr "$a<- $b<- $a-> $b->"
      inferNormType emptyEnv ["$"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$" $: v0 * v1 * v2 --> v0 * v2 * v1))
      inferNormType emptyEnv ["$a"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$a" $: v0 * v1 * v2 --> v0 * v2 * v1))
      inferNormType emptyEnv ["$b"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$b" $: v0 * v1 * v2 --> v0 * v2 * v1))
      inferNormType emptyEnv ["$c"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$c" $: v0 * v1 * v2 --> v0 * v2 * v1))

    it "infers `[drop]" $ do
      let (Right e) = parseExpr "[drop]"
      inferNormType' e
        `shouldBe` Right (forall' [v0] (v0 --> v0 * forall' [v1, v2] (v1 * v2 --> v1)))

    it "infers `{$a [drop]}`" $ do
      let (Right e) = parseExpr "{$a [drop]}"
      inferNormType' e
        `shouldBe` Right
          ( forall [v0] ("$a" $: v0 --> v0 * forall [v1, v2] ("$a" $: v1 * v2 --> v1))
          )

    it "infers `{match {case =>}}`" $ do
      let (Right e) = parseExpr "{match {case =>}}"
      let (Right e') = parseExpr ""
      inferNormType emptyEnv ["$"] e
        `shouldBe` inferNormType emptyEnv ["$"] e'

    it "infers `{match {case Z => Z S} {case => drop Z}}`" $ do
      let (Right e) = parseExpr "{match {case Z => Z S} {case => drop Z}}"
      inferNormType testEnv ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tNat --> v0 * tNat))

    it "infers `{match {case Z Z => Z S} {case => drop drop Z}}`" $ do
      let (Right e) = parseExpr "{match {case Z Z => Z S} {case => drop drop Z}}"
      inferNormType testEnv ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tNat * tNat --> v0 * tNat))

    it "infers `{match {case Z => [clone] apply} {case => drop [clone] apply}}`" $ do
      let (Right e) = parseExpr "{match {case Z => [clone] apply} {case => drop [clone] apply}}"
      inferNormType testEnv ["$"] e
        `shouldBe` Right (forall' [v0, v1] (v0 * v1 * tNat --> v0 * v1 * v1))

    it "infers `{match {case B0 => B1} {case B1 => B0}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let (Right env) = tryAddDataDefs emptyEnv [d]
      let (Right e) = parseExpr "{match {case B0 => B1} {case B1 => B0}}"
      let tBit = TCons [] "Bit"
      inferNormType env ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tBit --> v0 * tBit))

    it "infers `{$a {match {case B0 => B1} {case B1 => B0}}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let (Right env) = tryAddDataDefs emptyEnv [d]
      let (Right e) = parseExpr "{$a {match {case B0 => B1} {case B1 => B0}}}"
      let tBit = TCons [] "Bit"
      inferNormType env ["$"] e
        `shouldBe` Right (forall [v0] ("$a" $: v0 * tBit --> v0 * tBit))

    it "infers `{match {case Z => }}`" $ do
      let (Right e) = parseExpr "{match {case Z => }}"
      let (Right t) = parseFnType "forall v0 . v0 Nat -> v0"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case S => }}`" $ do
      let (Right e) = parseExpr "{match {case S => }}"
      let (Right t) = parseFnType "forall v0 . v0 Nat -> v0 Nat"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case (Z S) => }}`" $ do
      let (Right e) = parseExpr "{match {case (Z S) => }}"
      let (Right t) = parseFnType "forall v0 . v0 Nat -> v0"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case (S S) => }}`" $ do
      let (Right e) = parseExpr "{match {case (S S) => }}"
      let (Right t) = parseFnType "forall v0 . v0 Nat -> v0 Nat"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case Push =>}}`" $ do
      let (Right e) = parseExpr "{match {case Push =>}}"
      let (Right t) = parseFnType "forall v0 v1 . v0 (v1 Stack) -> v0 (v1 Stack) v1"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case (_ B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "{match {case (_ B0 Push) =>}}"
      let (Right t) = parseFnType "forall v0 . v0 (Bit Stack) -> v0 (Bit Stack)"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case (Empty B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "{match {case (Empty B0 Push) =>}}"
      let (Right t) = parseFnType "forall v0 . v0 (Bit Stack) -> v0"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case (Push B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "{match {case (Push B0 Push) =>}}"
      let (Right t) = parseFnType "forall v0 . v0 (Bit Stack) -> v0 (Bit Stack) Bit"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case ((_ B1 Push) B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "{match {case ((_ B1 Push) B0 Push) =>}}"
      let (Right t) = parseFnType "forall v0 . v0 (Bit Stack) -> v0 (Bit Stack)"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case (S Push Pair) =>}}`" $ do
      let (Right e) = parseExpr "{match {case (S Push Pair) =>}}"
      let (Right t) = parseFnType "forall v0 v1 . v0 (Nat (v1 Stack) Pair) -> v0 Nat (v1 Stack) v1"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case (Push Push Pair) =>}}`" $ do
      let (Right e) = parseExpr "{match {case (Push Push Pair) =>}}"
      let (Right t) = parseFnType "forall v0 v1 v2 . v0 ((v1 Stack) (v2 Stack) Pair) -> v0 (v1 Stack) v1 (v2 Stack) v2"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case (Push _ Pair) =>}}`" $ do
      let (Right e) = parseExpr "{match {case (Push _ Pair) =>}}"
      let (Right t) = parseFnType "forall v0 v1 v2 . v0 ((v1 Stack) v2 Pair) -> v0 (v1 Stack) v1 v2"
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "throws UndefinedCons on `Test`" $ do
      let (Right e) = parseExpr "Test"
      inferNormType emptyEnv ["$"] e
        `shouldBe` Left (UndefinedCons "Test")

    it "throws UndefinedFn on `test`" $ do
      let (Right e) = parseExpr "test"
      inferNormType emptyEnv ["$"] e
        `shouldBe` Left (UndefinedFn "test")

    it "infers `{match {case True => test} {case False =>}}`" $ do
      let (Right e) = parseExpr "{match {case True => test} {case False =>}}"
      inferNormType testEnv ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tBool --> v0))

    it "infers `nat_add`" $ do
      let (Right e) = parseExpr "nat_add"
      inferNormType testEnv ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tNat * tNat --> v0 * tNat))

    it "infers `{$a nat_add}`" $ do
      let (Right e) = parseExpr "{$a nat_add}"
      inferNormType testEnv ["$"] e
        `shouldBe` Right (forall [v0] ("$a" $: v0 * tNat * tNat --> v0 * tNat))

    it "infers `{match {case {$$ S} =>}}`" $ do
      let (Right e) = parseExpr "{match {case {$$ S} =>}}"
      let t = forall [v0] ("$$" $: v0 * tNat --> v0 * tNat)
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case {$$ S S} =>}}`" $ do
      let (Right e) = parseExpr "{match {case {$$ S S} =>}}"
      let t = forall [v0] ("$$" $: v0 * tNat * tNat --> v0 * tNat * tNat)
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{match {case {$a S} {$b S} =>}}`" $ do
      let (Right e) = parseExpr "{match {case {$a S} {$b S} =>}}"
      let t = forall [v0, v1] ("$a" $: v0 * tNat --> v0 * tNat $. "$b" $: v1 * tNat --> v1 * tNat)
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{$a {match {case {$$ S} =>}}}`" $ do
      let (Right e) = parseExpr "{$a {match {case {$$ S} =>}}}"
      let t = forall [v0] ("$$" $: v0 * tNat --> v0 * tNat)
      inferNormType testEnv ["$"] e `shouldBe` Right t

    it "infers `{$$ {match {case {$$ S} =>}}}`" $ do
      let (Right e) = parseExpr "{$$ {match {case {$$ S} =>}}}"
      let t = forall [v0] ("$$$" $: v0 * tNat --> v0 * tNat)
      inferNormType testEnv ["$"] e `shouldBe` Right t

  describe "checkType" $ do
    it "succeeds on exact match" $ do
      let (Right e) = parseExpr "bool_and"
      let t = forall' [v0] (v0 * tBool * tBool --> v0 * tBool)
      checkType testEnv ["$"] e t `shouldBe` Right ()

    it "succeeds on variable rename" $ do
      let (Right e) = parseExpr "bool_and"
      let t = forall' [v3] (v3 * tBool * tBool --> v3 * tBool)
      checkType testEnv ["$"] e t `shouldBe` Right ()

    it "fails on type constant mismatch" $ do
      let (Right e) = parseExpr "bool_and"
      let t = forall' [v0] (v0 * tNat * tNat --> v0 * tNat)
      checkType testEnv ["$"] e t `shouldBe` Left (MatchError (DoesNotMatch tBool tNat))

    it "fails if the specified type is too general" $ do
      let (Right e) = parseExpr "bool_and"
      let t = forall' [v0, v1] (v0 * v1 * v1 --> v0 * v1)
      checkType testEnv ["$"] e t `shouldBe` Left (MatchError (DoesNotMatch tBool v1))

  describe "fnDeps" $ do
    it "returns all dependencies" $ do
      let (Right e) =
            parseExpr
              ( unlines
                  [ "f1 {match ",
                    "    {case True => f2 f3 {match {case True => f4} {case => f4 f5 f6}}}",
                    "    {case => f2 f4 f5}",
                    "}"
                  ]
              )
      fnDeps e `shouldBe` Set.fromList ["f1", "f2", "f3", "f4", "f5", "f6"]

  describe "fnUDeps" $ do
    it "returns unconditional dependencies" $ do
      let (Right e) =
            parseExpr
              ( unlines
                  [ "f1 {match ",
                    "    {case True => f2 f3 {match {case True => f4} {case => f4 f5 f6}}}",
                    "    {case => f2 f4 f5}",
                    "}"
                  ]
              )
      fnUDeps e `shouldBe` Set.fromList ["f1", "f2", "f4"]

  describe "tryAddFnDecls" $ do
    it "adds drop2" $ do
      let (Right f) = parseFnDecl "{fn drop2 :: forall v0 v1 v2 . v0 v1 v2 -> v0}"
      let (Right t) = parseFnType "forall v0 v1 v2 . v0 v1 v2 -> v0"
      tryAddFnDecls emptyEnv [f]
        `shouldBe` Right
          ( emptyEnv
              { fnDecls = Map.singleton "drop2" f,
                fnTypes = Map.singleton "drop2" t
              }
          )

    it "fails with FnAlreadyDeclared" $ do
      let (Right f) = parseFnDecl "{fn drop2 :: forall v0 v1 v2 . v0 v1 v2 -> v0}"
      let (Right env) = tryAddFnDecls emptyEnv [f]
      tryAddFnDecls env [f]
        `shouldBe` Left (FnAlreadyDeclared "drop2")

    it "fails with FnDeclDuplicate" $ do
      let (Right f) = parseFnDecl "{fn drop2 :: forall v0 v1 v2 . v0 v1 v2 -> v0}"
      tryAddFnDecls emptyEnv [f, f]
        `shouldBe` Left (FnDeclDuplicate "drop2")

    it "fails with FnDeclTempStack" $ do
      let (Right f) = parseFnDecl "{fn pass :: forall v0 . {$$ v0 -> v0}}"
      tryAddFnDecls emptyEnv [f]
        `shouldBe` Left (FnDeclTempStack "pass" (Set.singleton "$$"))

  describe "tryAddFnDefs" $ do
    it "defines drop2" $ do
      let (Right f) = parseFnDef "{fn drop2 => drop drop}"
      let (Right t) = inferNormType emptyEnv ["$"] (fnDefExpr f)
      tryAddFnDefs emptyEnv [f]
        `shouldBe` Right
          ( emptyEnv
              { fnDefs = Map.singleton "drop2" f,
                fnTypes = Map.singleton "drop2" t
              }
          )

    it "fails with FnAlreadyDefined" $ do
      let (Right f) = parseFnDef "{fn clone => clone}"
      tryAddFnDefs emptyEnv [f]
        `shouldBe` Left (FnAlreadyDefined "clone")

      let (Right f) = parseFnDef "{fn drop2 => drop drop}"
      let (Right env) = tryAddFnDefs emptyEnv [f]
      tryAddFnDefs env [f]
        `shouldBe` Left (FnAlreadyDefined "drop2")

    it "fails with FnDefDuplicate" $ do
      let (Right f) = parseFnDef "{fn drop2 => drop drop}"
      tryAddFnDefs emptyEnv [f, f]
        `shouldBe` Left (FnDefDuplicate "drop2")

    it "fails with FnTypeError UndefinedFn" $ do
      let (Right f) = parseFnDef "{fn test1 => clone test2 clone test3}"
      tryAddFnDefs emptyEnv [f]
        `shouldBe` Left (FnTypeError "test1" (UndefinedFn "test2"))

    it "fails with FnTypeError" $ do
      let (Right f) = parseFnDef "{fn test => clone apply}"
      let (Right e) = parseExpr "clone apply"
      let (Left err) = inferNormType emptyEnv ["$"] e
      tryAddFnDefs emptyEnv [f]
        `shouldBe` Left (FnTypeError "test" err)

    it "fails with FnDefTempStack" $ do
      let (Right f) = parseFnDef "{fn test => {$a $a<-} {$b $b<-}}"
      tryAddFnDefs emptyEnv [f]
        `shouldBe` Left (FnDefTempStack "test" (Set.fromList ["$$a", "$$b"]))

    it "defines fib" $ do
      let (Right f) =
            parseFnDef
              ( unlines
                  [ "{fn fib =>",
                    "  {match",
                    "    {case Z => Z}",
                    "    {case (Z S) => Z S}",
                    "    {case => clone nat_decr fib swap nat_decr nat_decr fib nat_add}",
                    "  }",
                    "}"
                  ]
              )
      let t = forall' [v0] (v0 * tNat --> v0 * tNat)
      let Env {fnDefs, fnTypes} = testEnv
      tryAddFnDefs testEnv [f]
        `shouldBe` Right
          ( testEnv
              { fnDefs = Map.insert "fib" f fnDefs,
                fnTypes = Map.insert "fib" t fnTypes
              }
          )

    it "defines drop2 and drop3" $ do
      let (Right drop2) = parseFnDef "{fn drop2 => drop drop}"
      let (Right drop3) = parseFnDef "{fn drop3 => drop2 drop}"
      let env =
            ( emptyEnv
                { fnDefs = Map.fromList [("drop2", drop2), ("drop3", drop3)],
                  fnTypes =
                    Map.fromList
                      [ ("drop2", forall' [v0, v1, v2] (v0 * v1 * v2 --> v0)),
                        ("drop3", forall' [v0, v1, v2, v3] (v0 * v1 * v2 * v3 --> v0))
                      ]
                }
            )
      tryAddFnDefs emptyEnv [drop2, drop3]
        `shouldBe` Right env

    it "defines mutually recursive fns" $ do
      let (Right decr_even) =
            parseFnDef
              ( unlines
                  [ "{fn decr_even =>",
                    "  clone nat_is_odd",
                    "  {match",
                    "    {case Z False => }",
                    "    {case _ False => (Z S) nat_sub decr_odd}",
                    "    {case => drop decr_odd}",
                    "  }",
                    "}"
                  ]
              )
      let decr_even_t = forall' [v0] (v0 * tNat --> v0)
      let (Right decr_odd) =
            parseFnDef
              ( unlines
                  [ "{fn decr_odd =>",
                    "  clone nat_is_odd",
                    "  {match",
                    "    {case Z True => }",
                    "    {case _ True => (Z S) nat_sub decr_even}",
                    "    {case => drop decr_even}",
                    "  }",
                    "}"
                  ]
              )
      let decr_odd_t = forall' [v0] (v0 * tNat --> v0)
      let (Right count_down) = parseFnDef "{fn count_down => decr_odd}"
      let count_down_t = forall' [v0] (v0 * tNat --> v0)
      let Env {fnDefs, fnTypes} = testEnv
      let fnDefs' =
            fnDefs
              `Map.union` Map.fromList
                [ ("decr_even", decr_even),
                  ("decr_odd", decr_odd),
                  ("count_down", count_down)
                ]
      let fnTypes' =
            fnTypes
              `Map.union` Map.fromList
                [ ("decr_even", decr_even_t),
                  ("decr_odd", decr_odd_t),
                  ("count_down", count_down_t)
                ]
      let env = (testEnv {fnDefs = fnDefs', fnTypes = fnTypes'})
      tryAddFnDefs testEnv [decr_even, decr_odd, count_down]
        `shouldBe` Right env

    it "succeeds on direct recursion in one match case" $ do
      let (Right fib) =
            parseFnDef
              ( unlines
                  [ "{fn fib =>",
                    "  {match",
                    "    {case Z => Z}",
                    "    {case (Z S) => Z S}",
                    "    {case => clone nat_decr fib $a<- $b<- $a-> $b-> nat_decr nat_decr fib nat_add}",
                    "  }",
                    "}"
                  ]
              )
      let fib_t = forall' [v0] (v0 * tNat --> v0 * tNat)
      let Env {fnDefs, fnTypes} = testEnv
      let fnDefs' =
            fnDefs
              `Map.union` Map.fromList
                [ ("fib", fib)
                ]
      let fnTypes' =
            fnTypes
              `Map.union` Map.fromList
                [ ("fib", fib_t)
                ]
      let env = (testEnv {fnDefs = fnDefs', fnTypes = fnTypes'})
      tryAddFnDefs testEnv [fib] `shouldBe` Right env

    it "fails on direct recursion outside of match expr" $ do
      let (Right diverge) = parseFnDef "{fn diverge => drop diverge (Z S)}"
      let err = UncondCallCycle ["diverge"]
      tryAddFnDefs emptyEnv [diverge] `shouldBe` Left err

    it "fails on direct recursion in all match cases" $ do
      let (Right foo) =
            parseFnDef
              ( unlines
                  [ "{fn foo =>",
                    "  {match",
                    "    {case False => True foo}",
                    "    {case True => False foo}",
                    "  }",
                    "}"
                  ]
              )
      let foo_t = forall' [v0] (v0 * tNat --> v0 * tNat)
      let err = UncondCallCycle ["foo"]
      tryAddFnDefs testEnv [foo] `shouldBe` Left err

    it "succeeds on mutual recursion in one match case in each function" $ do
      let (Right is_even) =
            parseFnDef
              ( unlines
                  [ "{fn is_even =>",
                    "  {match",
                    "    {case Z => True}",
                    "    {case => nat_decr is_odd}",
                    "  }",
                    "}"
                  ]
              )
      let is_even_t = forall' [v0] (v0 * tNat --> v0 * tBool)

      let (Right is_odd) =
            parseFnDef
              ( unlines
                  [ "{fn is_odd =>",
                    "  {match",
                    "    {case Z => False}",
                    "    {case => nat_decr is_even}",
                    "  }",
                    "}"
                  ]
              )
      let is_odd_t = forall' [v0] (v0 * tNat --> v0 * tBool)

      let Env {fnDefs, fnTypes} = testEnv
      let fnDefs' =
            fnDefs
              `Map.union` Map.fromList
                [ ("is_even", is_even),
                  ("is_odd", is_odd)
                ]
      let fnTypes' =
            fnTypes
              `Map.union` Map.fromList
                [ ("is_even", is_even_t),
                  ("is_odd", is_odd_t)
                ]
      let env = (testEnv {fnDefs = fnDefs', fnTypes = fnTypes'})
      tryAddFnDefs testEnv [is_even, is_odd] `shouldBe` Right env

    it "fails on mutual recursion outside of match expr" $ do
      let (Right f1) = parseFnDef "{fn f1 => nat_decr f2}"
      let f1_t = forall' [v0] (v0 * tNat --> v0 * tBool)

      let (Right f2) = parseFnDef "{fn f2 => nat_decr f1}"
      let f2_t = forall' [v0] (v0 * tNat --> v0 * tBool)

      let err = UncondCallCycle ["f1", "f2"]
      tryAddFnDefs testEnv [f1, f2] `shouldBe` Left err

    it "fails on mutual recursion in all match cases" $ do
      let (Right is_even) =
            parseFnDef
              ( unlines
                  [ "{fn is_even =>",
                    "  {match",
                    "    {case Z => nat_incr is_odd}",
                    "    {case => nat_decr is_odd}",
                    "  }",
                    "}"
                  ]
              )
      let is_even_t = forall' [v0] (v0 * tNat --> v0 * tBool)

      let (Right is_odd) =
            parseFnDef
              ( unlines
                  [ "{fn is_odd =>",
                    "  {match",
                    "    {case Z => nat_incr is_even}",
                    "    {case => nat_decr is_even}",
                    "  }",
                    "}"
                  ]
              )
      let is_odd_t = forall' [v0] (v0 * tNat --> v0 * tBool)

      let err = UncondCallCycle ["is_even", "is_odd"]
      tryAddFnDefs testEnv [is_even, is_odd] `shouldBe` Left err

    it "succeeds on mutual recursion in all but some match cases in one function (1)" $ do
      let (Right is_even) =
            parseFnDef
              ( unlines
                  [ "{fn is_even =>",
                    "  {match",
                    "    {case Z => True}",
                    "    {case (Z S) => False}",
                    "    {case => nat_decr is_odd}",
                    "  }",
                    "}"
                  ]
              )
      let is_even_t = forall' [v0] (v0 * tNat --> v0 * tBool)

      let (Right is_odd) = parseFnDef "{fn is_odd => nat_decr is_even}"
      let is_odd_t = forall' [v0] (v0 * tNat --> v0 * tBool)

      let Env {fnDefs, fnTypes} = testEnv
      let fnDefs' =
            fnDefs
              `Map.union` Map.fromList
                [ ("is_even", is_even),
                  ("is_odd", is_odd)
                ]
      let fnTypes' =
            fnTypes
              `Map.union` Map.fromList
                [ ("is_even", is_even_t),
                  ("is_odd", is_odd_t)
                ]
      let env = (testEnv {fnDefs = fnDefs', fnTypes = fnTypes'})
      tryAddFnDefs testEnv [is_odd, is_even] `shouldBe` Right env

    it "succeeds on mutual recursion in all but some match cases in one function (2)" $ do
      let (Right is_odd) =
            parseFnDef
              ( unlines
                  [ "{fn is_odd =>",
                    "  {match",
                    "    {case Z => False}",
                    "    {case (Z S) => True}",
                    "    {case => nat_decr is_even}",
                    "  }",
                    "}"
                  ]
              )
      let is_odd_t = forall' [v0] (v0 * tNat --> v0 * tBool)

      let (Right is_even) = parseFnDef "{fn is_even => nat_decr is_odd}"
      let is_even_t = forall' [v0] (v0 * tNat --> v0 * tBool)

      let Env {fnDefs, fnTypes} = testEnv
      let fnDefs' =
            fnDefs
              `Map.union` Map.fromList
                [ ("is_even", is_even),
                  ("is_odd", is_odd)
                ]
      let fnTypes' =
            fnTypes
              `Map.union` Map.fromList
                [ ("is_even", is_even_t),
                  ("is_odd", is_odd_t)
                ]
      let env = (testEnv {fnDefs = fnDefs', fnTypes = fnTypes'})
      tryAddFnDefs testEnv [is_odd, is_even] `shouldBe` Right env

    it "defines tail recursive fib" $ do
      let fib_t = forall' [v0] (v0 * tNat --> v0 * tNat)
      let _fib_t =
            forall
              [v0, v1, v2]
              ( "$" $: v0 * tNat --> v0 * tNat
                  $. "$a" $: v1 * tNat --> v1
                  $. "$b" $: v2 * tNat --> v2
              )
      let Env {fnDefs, fnTypes} = testEnv
      let fnDefs' =
            fnDefs
              `Map.union` Map.fromList
                [ ("fib", fastFib),
                  ("_fib", _fastFib)
                ]
      let fnTypes' =
            fnTypes
              `Map.union` Map.fromList
                [ ("fib", fib_t),
                  ("_fib", _fib_t)
                ]
      let env = (testEnv {fnDefs = fnDefs', fnTypes = fnTypes'})
      tryAddFnDefs testEnv [fastFib, _fastFib] `shouldBe` Right env

    it "adds disconnected cyclic defs" $ do
      let (Right env) = tryAddDataDefs emptyEnv [dBool, dList]
      let defs = [bool_and_d, list_append_d, _list_append_d]
      let Env {fnDefs, fnTypes} = env
      let fnDefs' =
            fnDefs
              `Map.union` Map.fromList
                [ ("bool_and", bool_and_d),
                  ("list_append", list_append_d),
                  ("_list_append", _list_append_d)
                ]
      let fnTypes' =
            fnTypes
              `Map.union` Map.fromList
                [ ("bool_and", bool_and_t),
                  ("list_append", list_append_t),
                  ("_list_append", _list_append_t)
                ]
      let env' = env {fnDefs = fnDefs', fnTypes = fnTypes'}
      tryAddFnDefs env defs `shouldBe` Right env'

  describe "tryAddDataDefs" $ do
    it "adds `{data Bit {cons B0} {cons B1}}`" $ do
      let (Right def) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let dataDefs = Map.singleton "Bit" def
      let typeConsArities = Map.singleton "Bit" 0
      let consDefs = Map.fromList [("B0", ConsDef [] "B0"), ("B1", ConsDef [] "B1")]
      let tBit = TCons [] "Bit"
      let consTypes = Map.fromList [("B0", ([], tBit)), ("B1", ([], tBit))]
      tryAddDataDefs emptyEnv [def]
        `shouldBe` Right (emptyEnv {dataDefs, typeConsArities, consDefs, consTypes})

    it "adds `{data v0 v1 Pair {cons v0 v1 Pair}}`" $ do
      let (Right def) = parseDataDef "{data v0 v1 Pair {cons v0 v1 Pair}}"
      let dataDefs = Map.singleton "Pair" def
      let typeConsArities = Map.singleton "Pair" 2
      let consDefs = Map.fromList [("Pair", ConsDef [v0, v1] "Pair")]
      let consTypes = Map.fromList [("Pair", ([v0, v1], TCons [v0, v1] "Pair"))]
      tryAddDataDefs emptyEnv [def]
        `shouldBe` Right (emptyEnv {dataDefs, typeConsArities, consDefs, consTypes})

    it "adds `{data v0 v1 SwapPair {cons v1 v0 SwapPair}}`" $ do
      let (Right def) = parseDataDef "{data v0 v1 SwapPair {cons v1 v0 SwapPair}}"
      let dataDefs = Map.singleton "SwapPair" def
      let typeConsArities = Map.singleton "SwapPair" 2
      let consDefs = Map.fromList [("SwapPair", ConsDef [v1, v0] "SwapPair")]
      let consTypes = Map.fromList [("SwapPair", ([v1, v0], TCons [v0, v1] "SwapPair"))]
      tryAddDataDefs emptyEnv [def]
        `shouldBe` Right (emptyEnv {dataDefs, typeConsArities, consDefs, consTypes})

    it "adds `{data v0 Stack {cons Empty} {cons (v0 Stack) v0 Push}}`" $ do
      let (Right def) =
            parseDataDef
              "{data v0 Stack {cons Empty} {cons (v0 Stack) v0 Push}}"
      let dataDefs = Map.singleton "Stack" def
      let typeConsArities = Map.singleton "Stack" 1
      let tStack = TCons [v0] "Stack"
      let consDefs =
            Map.fromList
              [ ("Empty", ConsDef [] "Empty"),
                ("Push", ConsDef [tStack, v0] "Push")
              ]
      let consTypes =
            Map.fromList
              [ ("Empty", ([], tStack)),
                ("Push", ([tStack, v0], tStack))
              ]
      tryAddDataDefs emptyEnv [def]
        `shouldBe` Right (emptyEnv {dataDefs, typeConsArities, consDefs, consTypes})

    it "adds mutually recursive definitions" $ do
      let (Right defA) =
            parseDataDef
              "{data v0 v1 A {cons EmptyA} {cons (v0 v1 B) v0 A}}"
      let (Right defB) =
            parseDataDef
              "{data v0 v1 B {cons EmptyB} {cons (v0 v1 A) v1 B}}"
      let dataDefs = Map.fromList [("A", defA), ("B", defB)]
      let typeConsArities = Map.fromList [("A", 2), ("B", 2)]
      let (tA, tB) = (TCons [v0, v1] "A", TCons [v0, v1] "B")
      let consDefs =
            Map.fromList
              [ ("EmptyA", ConsDef [] "EmptyA"),
                ("A", ConsDef [tB, v0] "A"),
                ("EmptyB", ConsDef [] "EmptyB"),
                ("B", ConsDef [tA, v1] "B")
              ]
      let consTypes =
            Map.fromList
              [ ("EmptyA", ([], tA)),
                ("A", ([tB, v0], tA)),
                ("EmptyB", ([], tB)),
                ("B", ([tA, v1], tB))
              ]
      tryAddDataDefs emptyEnv [defA, defB]
        `shouldBe` Right (emptyEnv {dataDefs, typeConsArities, consDefs, consTypes})

    it "fails with TypeConsAlreadyDefined" $ do
      let (Right def) = parseDataDef "{data Foo}"
      let (Right env) = tryAddDataDefs emptyEnv [def]
      tryAddDataDefs env [def]
        `shouldBe` Left (TypeConsAlreadyDefined "Foo")
      tryAddDataDefs emptyEnv [def, def]
        `shouldBe` Left (TypeConsAlreadyDefined "Foo")

    it "fails with ConsAlreadyDefined" $ do
      let (Right def1) = parseDataDef "{data Bit1 {cons B0} {cons B1}}"
      let (Right def2) = parseDataDef "{data Bit2 {cons B0} {cons B1}}"
      let (Right env) = tryAddDataDefs emptyEnv [def1]
      tryAddDataDefs env [def2]
        `shouldBe` Left (ConsAlreadyDefined "Bit2" "B0")
      tryAddDataDefs emptyEnv [def1, def2]
        `shouldBe` Left (ConsAlreadyDefined "Bit2" "B0")

    it "fails with DuplicateTypeVar" $ do
      let (Right def) = parseDataDef "{data v0 v0 Test {cons v0 v0 Test}}"
      tryAddDataDefs emptyEnv [def]
        `shouldBe` Left (DuplicateTypeVar "Test" tv0)

    it "fails with UndefinedTypeVar" $ do
      let (Right def) = parseDataDef "{data Stack {cons Empty} {cons Stack v0 Push}}"
      tryAddDataDefs emptyEnv [def]
        `shouldBe` Left (UndefinedTypeVar "Stack" tv0)

    it "fails with UndefinedTypeCons" $ do
      let (Right def) =
            parseDataDef
              "{data v0 v1 A {cons EmptyA} {cons (v0 v1 B) v0 A}}"
      tryAddDataDefs emptyEnv [def]
        `shouldBe` Left (UndefinedTypeCons "B")

    it "fails with TypeConsArityMismatch" $ do
      let (Right def) =
            parseDataDef
              "{data v0 Stack {cons Empty} {cons Stack v0 Push}}"
      tryAddDataDefs emptyEnv [def]
        `shouldBe` Left (TypeConsArityMismatch "Stack" (TCons [] "Stack"))

  describe "tryAddTestDef" $ do
    it "adds test definition" $ do
      let testDefSrc = "{test \"this is a test description\" => Z {match {case Z =>}}}"
      let (Right testDef) = parseTestDef testDefSrc
      let testDefs = [testDef]
      let env = testEnv {testDefs}
      tryAddTestDef testEnv testDef
        `shouldBe` Right env

(Right d_swap) = parseFnDef "{fn swap => $a<- $b<- $a-> $b->}"

(Right dBool) = parseDataDef "{data Bool {cons False} {cons True}}"

(Right bool_and_t) = parseFnType "Bool Bool -> Bool"

(Right bool_and_d) =
  parseFnDef
    ( unlines
        [ "{fn bool_and => {match",
          "    {case True True => True}",
          "    {case => drop drop False}",
          "}}"
        ]
    )

(Right dNat) = parseDataDef "{data Nat {cons Z} {cons Nat S}}"

(Right d_nat_incr) = parseFnDef "{fn nat_incr => S}"

(Right d_nat_decr) =
  parseFnDef
    ( unlines
        [ "{fn nat_decr => {match",
          "    {case Z => Z}",
          "    {case S =>}",
          "}}"
        ]
    )

(Right d_nat_add) =
  parseFnDef
    ( unlines
        [ "{fn nat_add => {match",
          "    {case Z =>}",
          "    {case S => $$<- S $$-> nat_add}",
          "}}"
        ]
    )

(Right d_nat_sub) =
  parseFnDef
    ( unlines
        [ "{fn nat_sub => {match",
          "    {case _ Z =>}",
          "    {case Z S => drop Z}",
          "    {case S S => nat_sub}",
          "}}"
        ]
    )

(Right d_nat_is_odd) =
  parseFnDef
    ( unlines
        [ "{fn nat_is_odd => {match",
          "    {case Z => False}",
          "    {case (Z S) => True}",
          "    {case (S S) => nat_is_odd}",
          "}}"
        ]
    )

(Right dList) = parseDataDef "{data v0 List {cons Nil} {cons v0 (v0 List) Cons}}"

(Right list_append_t) = parseFnType "(v1 List) (v1 List) -> (v1 List)"

(Right list_append_d) = parseFnDef "{fn list_append => {spread $a $b} _list_append $a->}"

(Right _list_append_t) =
  parseFnType "forall v0 v1 v2 . {$a v0 (v1 List) -> v0 (v1 List)} {$b v2 (v1 List) -> v2}"

(Right _list_append_d) =
  parseFnDef
    ( unlines
        [ "{fn _list_append => {match",
          "    {case {$a Nil} => $b-> $a<-}",
          "    {case {$a Cons} => _list_append {$a Cons}}",
          "}}"
        ]
    )

(Right dStack) =
  parseDataDef
    "{data v0 Stack {cons Empty} {cons (v0 Stack) v0 Push}}"

(Right dPair) = parseDataDef "{data v0 v1 Pair {cons v0 v1 Pair}}"

(Right testEnv) =
  let (Right env) = tryAddDataDefs preludeEnv [dBool, dNat, dStack, dPair]
   in tryAddFnDefs env [d_swap, bool_and_d, d_nat_incr, d_nat_decr, d_nat_add, d_nat_sub, d_nat_is_odd]

fastFibSrc = "{fn fib => {$a Z} {$b (Z S)} _fib}"

_fastFibSrc =
  unlines
    [ "{fn _fib => {match",
      "  {case Z => {$b drop} $a->}",
      "  {case S => {$b clone pop $a-> nat_add} $a<- _fib}",
      "}}"
    ]

(Right fastFib) = parseFnDef fastFibSrc

(Right _fastFib) = parseFnDef _fastFibSrc
