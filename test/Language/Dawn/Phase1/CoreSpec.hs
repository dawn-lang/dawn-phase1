-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.CoreSpec (spec) where

import Control.Exception
import Control.Monad
import Data.Either
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Exprs
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.Utils
import Test.Hspec
import Prelude hiding (drop, (*))

[tv0, tv1, tv2, tv3, tv4, tv5, _, _, tv8] = map TypeVar [0 .. 8]

[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] = map (TVar . TypeVar) [0 .. 10]

tU32 = TCons (TypeCons "U32")

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
                counts = foldl1 (Map.unionWith (+)) (map iter' (Map.elems mio))
                counts' = foldl (\m v -> Map.insert v 1 m) Map.empty (Set.toList qs)
             in Map.unionWith (+) counts counts'
          count (TCons _) = Map.empty
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

    it "infers `($a: push) ($b: push) ($a: pop) ($b: pop)` is swap" $ do
      let (Right e) = parseExpr "($a: push) ($b: push) ($a: pop) ($b: pop)"
      inferNormType' e
        `shouldBe` Right (forall' [v0, v1, v2] (v0 * v1 * v2 --> v0 * v2 * v1))

    it "infers `$a<- $b<- $a-> $b->` is swap" $ do
      let (Right e) = parseExpr "$a<- $b<- $a-> $b->"
      inferNormType' e
        `shouldBe` Right (forall' [v0, v1, v2] (v0 * v1 * v2 --> v0 * v2 * v1))

    it "infers `[clone] [swap apply] apply`" $ do
      let (Right e) = parseExpr "[clone] [$a<- $b<- $a-> $b-> apply] apply"
      let nnf = forall' [v1, v2] (v1 * v2 --> v1 * v2 * v2)
      let nf = forall' [] (v0 * nnf --> v3)
      let f = forall' [v0, v3] (v0 * nf --> v3)
      inferNormType' e `shouldBe` Right f

    it "infers `$a<- $b<- $a-> $b->` is swap in any context" $ do
      let (Right e) = parseExpr "$a<- $b<- $a-> $b->"
      inferNormType ["$"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$" $: v0 * v1 * v2 --> v0 * v2 * v1))
      inferNormType ["$a"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$a" $: v0 * v1 * v2 --> v0 * v2 * v1))
      inferNormType ["$b"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$b" $: v0 * v1 * v2 --> v0 * v2 * v1))
      inferNormType ["$c"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$c" $: v0 * v1 * v2 --> v0 * v2 * v1))

    it "infers `[drop]" $ do
      let (Right e) = parseExpr "[drop]"
      inferNormType' e
        `shouldBe` Right (forall' [v0] (v0 --> v0 * forall' [v1, v2] (v1 * v2 --> v1)))

    it "infers `($a: [drop])" $ do
      let (Right e) = parseExpr "($a: [drop])"
      inferNormType' e
        `shouldBe` Right
          ( forall [v0] ("$a" $: v0 --> v0 * forall [v1, v2] ("$a" $: v1 * v2 --> v1))
          )

    it "infers `123`" $ do
      let (Right e) = parseExpr "123"
      let t = TCons (TypeCons "U32")
      inferNormType ["$"] e
        `shouldBe` Right (forall [v0] ("$" $: v0 --> v0 * t))

    it "infers `($a: 123)`" $ do
      let (Right e) = parseExpr "($a: 123)"
      let t = TCons (TypeCons "U32")
      inferNormType ["$"] e
        `shouldBe` Right (forall [v0] ("$a" $: v0 --> v0 * t))

    it "infers `{match {case =>}}`" $ do
      let (Right e) = parseExpr "{match {case =>}}"
      let (Right e') = parseExpr ""
      inferNormType ["$"] e
        `shouldBe` inferNormType ["$"] e'

    it "infers `{match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "{match {case 0 => 1} {case => drop 0}}"
      inferNormType ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tU32 --> v0 * tU32))

    it "infers `{match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "{match {case 0 0 => 1} {case => drop drop 0}}"
      inferNormType ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tU32 * tU32 --> v0 * tU32))
