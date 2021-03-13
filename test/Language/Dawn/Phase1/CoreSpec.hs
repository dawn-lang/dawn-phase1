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

    it "infers `{$a push} {$b push} {$a pop} {$b pop}` is swap" $ do
      let (Right e) = parseExpr "{$a push} {$b push} {$a pop} {$b pop}"
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
      inferNormType Map.empty ["$"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$" $: v0 * v1 * v2 --> v0 * v2 * v1))
      inferNormType Map.empty ["$a"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$a" $: v0 * v1 * v2 --> v0 * v2 * v1))
      inferNormType Map.empty ["$b"] e
        `shouldBe` Right (forall [v0, v1, v2] ("$b" $: v0 * v1 * v2 --> v0 * v2 * v1))
      inferNormType Map.empty ["$c"] e
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

    it "infers `123`" $ do
      let (Right e) = parseExpr "123"
      let t = TCons (TypeCons "U32")
      inferNormType Map.empty ["$"] e
        `shouldBe` Right (forall [v0] ("$" $: v0 --> v0 * t))

    it "infers `{$a 123}`" $ do
      let (Right e) = parseExpr "{$a 123}"
      let t = TCons (TypeCons "U32")
      inferNormType Map.empty ["$"] e
        `shouldBe` Right (forall [v0] ("$a" $: v0 --> v0 * t))

    it "infers `{match {case =>}}`" $ do
      let (Right e) = parseExpr "{match {case =>}}"
      let (Right e') = parseExpr ""
      inferNormType Map.empty ["$"] e
        `shouldBe` inferNormType Map.empty ["$"] e'

    it "infers `{match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "{match {case 0 => 1} {case => drop 0}}"
      inferNormType Map.empty ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tU32 --> v0 * tU32))

    it "infers `{match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "{match {case 0 0 => 1} {case => drop drop 0}}"
      inferNormType Map.empty ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tU32 * tU32 --> v0 * tU32))

    it "infers `{match {case 0 => [clone] apply} {case => drop [clone] apply}}`" $ do
      let (Right e) = parseExpr "{match {case 0 => [clone] apply} {case => drop [clone] apply}}"
      inferNormType Map.empty ["$"] e
        `shouldBe` Right (forall' [v0, v1] (v0 * v1 * tU32 --> v0 * v1 * v1))

    it "throws UndefinedFn on `test`" $ do
      let (Right e) = parseExpr "test"
      inferNormType Map.empty ["$"] e
        `shouldBe` Left (UndefinedFn "test")

    it "throws UndefinedFn on `{match {case True => test} {case False =>}}`" $ do
      let (Right e) = parseExpr "{match {case True => test} {case False =>}}"
      inferNormType Map.empty ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tBool --> v0))

  describe "defineFn examples" $ do
    it "defines drop2" $ do
      let (Right f) = parseFnDef "{fn drop2 = drop drop}"
      let (Right e) = parseExpr "drop drop"
      let (Right t) = inferNormType Map.empty ["$"] e
      defineFn Map.empty f
        `shouldBe` Right (Map.singleton "drop2" (e, t))

    it "fails with FnAlreadyDefined" $ do
      let (Right f) = parseFnDef "{fn clone = clone}"
      defineFn Map.empty f
        `shouldBe` Left (FnAlreadyDefined "clone")

      let (Right f) = parseFnDef "{fn drop2 = drop drop}"
      let (Right env) = defineFn Map.empty f
      defineFn env f
        `shouldBe` Left (FnAlreadyDefined "drop2")

    it "fails with FnTypeError UndefinedFn" $ do
      let (Right f) = parseFnDef "{fn test1 = clone test2 clone test3}"
      defineFn Map.empty f
        `shouldBe` Left (FnTypeError "test1" (UndefinedFn "test2"))

    it "fails with FnTypeError" $ do
      let (Right f) = parseFnDef "{fn test = clone apply}"
      let (Right e) = parseExpr "clone apply"
      let (Left err) = inferNormType Map.empty ["$"] e
      defineFn Map.empty f
        `shouldBe` Left (FnTypeError "test" err)

    it "fails with FnStackError" $ do
      let (Right f) = parseFnDef "{fn test = {$a $a<-} {$b $b<-}}"
      defineFn Map.empty f
        `shouldBe` Left (FnStackError "test" (Set.fromList ["$$a", "$$b"]))

    it "defines fib" $ do
      let (Right f) = parseFnDef "{fn swap = $a<- $b<- $a-> $b->}"
      let (Right env) = defineFn Map.empty f
      let eSrc =
            "{match "
              ++ "  {case 0 => 0} "
              ++ "  {case 1 => 1} "
              ++ "  {case => clone 1 sub fib swap 2 sub fib add} "
              ++ "}"
      let fSrc = "{fn fib = " ++ eSrc ++ "}"
      let (Right f) = parseFnDef fSrc
      let (Right e) = parseExpr eSrc
      let t = forall' [v0] (v0 * tU32 --> v0 * tU32)
      defineFn env f
        `shouldBe` Right (Map.insert "fib" (e, t) env)
  
  describe "checkType" $ do
    it "succeeds on exact match" $ do
      let (Right e) = parseExpr "and"
      let t = forall' [v0] (v0 * tBool * tBool --> v0 * tBool)
      checkType' e t `shouldBe` Right ()

    it "succeeds on variable rename" $ do
      let (Right e) = parseExpr "and"
      let t = forall' [v3] (v3 * tBool * tBool --> v3 * tBool)
      checkType' e t `shouldBe` Right ()

    it "fails on type constant mismatch" $ do
      let (Right e) = parseExpr "and"
      let t = forall' [v0] (v0 * tU32 * tU32 --> v0 * tU32)
      checkType' e t `shouldBe` Left (MatchError (DoesNotMatch tBool tU32))

    it "fails if the specified type is too general" $ do
      let (Right e) = parseExpr "and"
      let t = forall' [v0, v1] (v0 * v1 * v1 --> v0 * v1)
      checkType' e t `shouldBe` Left (MatchError (DoesNotMatch tBool v1))

  describe "dependencySortFns examples" $ do
    it "sorts drop2 drop3" $ do
      let (Right drop2) = parseFnDef "{fn drop2 = drop drop}"
      let (Right drop3) = parseFnDef "{fn drop3 = drop2 drop}"
      dependencySortFns [drop2, drop3]
        `shouldBe` [drop3, drop2]

  describe "defineFns examples" $ do
    it "defines drop2 and drop3" $ do
      let (Right drop2) = parseFnDef "{fn drop2 = drop drop}"
      let (Right drop3) = parseFnDef "{fn drop3 = drop2 drop}"
      let (Right drop2e) = parseExpr "drop drop"
      let (Right drop2t) = inferNormType Map.empty ["$"] drop2e
      let (Right drop3e) = parseExpr "drop2 drop"
      let (Right drop3te) = parseExpr "drop drop drop"
      let (Right drop3t) = inferNormType Map.empty ["$"] drop3te
      let errs = []
      let env :: FnEnv
          env = Map.fromList [("drop2", (drop2e, drop2t)), ("drop3", (drop3e, drop3t))]
      defineFns Map.empty [drop2, drop3]
        `shouldBe` (errs, env)

    it "defines mutually recursive fns" $ do
      let is_odd_es = "1 bit_and"
      let (Right is_odd) = parseFnDef ("{fn is_odd = " ++ is_odd_es ++ "}")
      let (Right is_odd_e) = parseExpr is_odd_es
      let is_odd_t = forall' [v0] (v0 * tU32 --> v0 * tU32)

      let decr_even_es = "clone is_odd {match {case 0 0 => } {case 0 => 1 sub decr_odd} {case => drop decr_odd}}"
      let (Right decr_even) = parseFnDef ("{fn decr_even = " ++ decr_even_es ++ "}")
      let (Right decr_even_e) = parseExpr decr_even_es
      let decr_even_t = forall' [v0] (v0 * tU32 --> v0)

      let decr_odd_es = "clone is_odd {match {case 0 1 => } {case 1 => 1 sub decr_even} {case => drop decr_even}}"
      let (Right decr_odd) = parseFnDef ("{fn decr_odd = " ++ decr_odd_es ++ "}")
      let (Right decr_odd_e) = parseExpr decr_odd_es
      let decr_odd_t = forall' [v0] (v0 * tU32 --> v0)

      let count_down_es = "decr_odd"
      let (Right count_down) = parseFnDef ("{fn count_down = " ++ count_down_es ++ "}")
      let (Right count_down_e) = parseExpr count_down_es
      let count_down_t = forall' [v0] (v0 * tU32 --> v0)

      let errs = []
      let env :: FnEnv
          env =
            Map.fromList
              [ ("is_odd", (is_odd_e, is_odd_t)),
                ("decr_even", (decr_even_e, decr_even_t)),
                ("decr_odd", (decr_odd_e, decr_odd_t)),
                ("count_down", (count_down_e, count_down_t))
              ]
      defineFns Map.empty [is_odd, decr_even, decr_odd, count_down]
        `shouldBe` (errs, env)
