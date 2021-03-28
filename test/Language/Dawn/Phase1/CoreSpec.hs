-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.
{-# LANGUAGE NamedFieldPuns #-}

module Language.Dawn.Phase1.CoreSpec (spec) where

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

    it "infers `123`" $ do
      let (Right e) = parseExpr "123"
      let t = TCons [] "U32"
      inferNormType emptyEnv ["$"] e
        `shouldBe` Right (forall [v0] ("$" $: v0 --> v0 * t))

    it "infers `{$a 123}`" $ do
      let (Right e) = parseExpr "{$a 123}"
      let t = TCons [] "U32"
      inferNormType emptyEnv ["$"] e
        `shouldBe` Right (forall [v0] ("$a" $: v0 --> v0 * t))

    it "infers `{match {case =>}}`" $ do
      let (Right e) = parseExpr "{match {case =>}}"
      let (Right e') = parseExpr ""
      inferNormType emptyEnv ["$"] e
        `shouldBe` inferNormType emptyEnv ["$"] e'

    it "infers `{match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "{match {case 0 => 1} {case => drop 0}}"
      inferNormType emptyEnv ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tU32 --> v0 * tU32))

    it "infers `{match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "{match {case 0 0 => 1} {case => drop drop 0}}"
      inferNormType emptyEnv ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tU32 * tU32 --> v0 * tU32))

    it "infers `{match {case 0 => [clone] apply} {case => drop [clone] apply}}`" $ do
      let (Right e) = parseExpr "{match {case 0 => [clone] apply} {case => drop [clone] apply}}"
      inferNormType emptyEnv ["$"] e
        `shouldBe` Right (forall' [v0, v1] (v0 * v1 * tU32 --> v0 * v1 * v1))

    it "infers `{match {case B0 => B1} {case B1 => B0}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "{match {case B0 => B1} {case B1 => B0}}"
      let tBit = TCons [] "Bit"
      inferNormType env ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tBit --> v0 * tBit))

    it "infers `{$a {match {case B0 => B1} {case B1 => B0}}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "{$a {match {case B0 => B1} {case B1 => B0}}}"
      let tBit = TCons [] "Bit"
      inferNormType env ["$"] e
        `shouldBe` Right (forall [v0] ("$a" $: v0 * tBit --> v0 * tBit))

    it "throws UndefinedFn on `test`" $ do
      let (Right e) = parseExpr "test"
      inferNormType emptyEnv ["$"] e
        `shouldBe` Left (UndefinedFn "test")

    it "throws UndefinedFn on `{match {case True => test} {case False =>}}`" $ do
      let (Right e) = parseExpr "{match {case True => test} {case False =>}}"
      inferNormType emptyEnv ["$"] e
        `shouldBe` Right (forall' [v0] (v0 * tBool --> v0))

  describe "defineFn examples" $ do
    it "defines drop2" $ do
      let (Right f) = parseFnDef "{fn drop2 => drop drop}"
      let (Right t) = inferNormType emptyEnv ["$"] (fnDefExpr f)
      defineFn emptyEnv f
        `shouldBe` Right
          ( emptyEnv
              { fnDefs = Map.singleton "drop2" f,
                fnTypes = Map.singleton "drop2" t
              }
          )

    it "fails with FnAlreadyDefined" $ do
      let (Right f) = parseFnDef "{fn clone => clone}"
      defineFn emptyEnv f
        `shouldBe` Left (FnAlreadyDefined "clone")

      let (Right f) = parseFnDef "{fn drop2 => drop drop}"
      let (Right env) = defineFn emptyEnv f
      defineFn env f
        `shouldBe` Left (FnAlreadyDefined "drop2")

    it "fails with FnTypeError UndefinedFn" $ do
      let (Right f) = parseFnDef "{fn test1 => clone test2 clone test3}"
      defineFn emptyEnv f
        `shouldBe` Left (FnTypeError "test1" (UndefinedFn "test2"))

    it "fails with FnTypeError" $ do
      let (Right f) = parseFnDef "{fn test => clone apply}"
      let (Right e) = parseExpr "clone apply"
      let (Left err) = inferNormType emptyEnv ["$"] e
      defineFn emptyEnv f
        `shouldBe` Left (FnTypeError "test" err)

    it "fails with FnStackError" $ do
      let (Right f) = parseFnDef "{fn test => {$a $a<-} {$b $b<-}}"
      defineFn emptyEnv f
        `shouldBe` Left (FnStackError "test" (Set.fromList ["$$a", "$$b"]))

    it "defines fib" $ do
      let (Right f) = parseFnDef "{fn swap => $a<- $b<- $a-> $b->}"
      let (Right env@Env {fnDefs, fnTypes}) = defineFn emptyEnv f
      let (Right f) =
            parseFnDef
              ( unlines
                  [ "{fn fib =>",
                    "  {match",
                    "    {case 0 => 0}",
                    "    {case 1 => 1}",
                    "    {case => clone 1 sub fib swap 2 sub fib add}",
                    "  }",
                    "}"
                  ]
              )
      let t = forall' [v0] (v0 * tU32 --> v0 * tU32)
      defineFn env f
        `shouldBe` Right
          ( env
              { fnDefs = Map.insert "fib" f fnDefs,
                fnTypes = Map.insert "fib" t fnTypes
              }
          )

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

  describe "fnDeps" $ do
    it "returns all dependencies" $ do
      let (Right e) = parseExpr "f1 {match {case True => f2 f3} {case => f2 f4}}"
      fnDeps e `shouldBe` Set.fromList ["f1", "f2", "f3", "f4"]

  describe "uncondFnDeps" $ do
    it "returns unconditional dependencies" $ do
      let (Right e) = parseExpr "f1 {match {case True => f2 f3} {case => f2 f4}}"
      uncondFnDeps e `shouldBe` Set.fromList ["f1", "f2"]

  describe "fnDepsSort" $ do
    -- f ~> g := f directly depends on g
    -- f ~!> g := f directly and unconditionally depends on g
    -- f ~?> g := f directly and conditionally depends on g
    -- f ~~> g := f transitively depends on g

    it "f < g if f ~!> g and not g ~~> f" $ do
      let (Right f) = parseFnDef "{fn f => g}"
      let (Right g) = parseFnDef "{fn g => }"
      fnDeps (fnDefExpr f) `shouldBe` Set.fromList ["g"]
      uncondFnDeps (fnDefExpr f) `shouldBe` Set.fromList ["g"]
      fnDeps (fnDefExpr g) `shouldBe` Set.fromList []
      uncondFnDeps (fnDefExpr g) `shouldBe` Set.fromList []
      fnDepsSort [f, g] `shouldBe` [f, g]
      fnDepsSort [g, f] `shouldBe` [f, g]

    it "f < g if f ~?> g and not g ~~> f" $ do
      let (Right f) = parseFnDef "{fn f => {match {case False => g} {case True => }}}"
      let (Right g) = parseFnDef "{fn g => }"
      fnDeps (fnDefExpr f) `shouldBe` Set.fromList ["g"]
      uncondFnDeps (fnDefExpr f) `shouldBe` Set.fromList []
      fnDeps (fnDefExpr g) `shouldBe` Set.fromList []
      uncondFnDeps (fnDefExpr g) `shouldBe` Set.fromList []
      fnDepsSort [f, g] `shouldBe` [f, g]
      fnDepsSort [g, f] `shouldBe` [f, g]

    it "f < g if f ~!> g and g ~?> f" $ do
      let (Right f) = parseFnDef "{fn f => g}"
      let (Right g) = parseFnDef "{fn g => {match {case False => f} {case True => }}}"
      fnDeps (fnDefExpr f) `shouldBe` Set.fromList ["g"]
      uncondFnDeps (fnDefExpr f) `shouldBe` Set.fromList ["g"]
      fnDeps (fnDefExpr g) `shouldBe` Set.fromList ["f"]
      uncondFnDeps (fnDefExpr g) `shouldBe` Set.fromList []
      fnDepsSort [f, g] `shouldBe` [f, g]
      fnDepsSort [g, f] `shouldBe` [f, g]

    it "f < g if f ~~!> g and not g ~~> f" $ do
      let (Right f) = parseFnDef "{fn f => h}"
      let (Right h) = parseFnDef "{fn h => g}"
      let (Right g) = parseFnDef "{fn g => }"
      fnDeps (fnDefExpr f) `shouldBe` Set.fromList ["h"]
      uncondFnDeps (fnDefExpr f) `shouldBe` Set.fromList ["h"]
      fnDeps (fnDefExpr h) `shouldBe` Set.fromList ["g"]
      uncondFnDeps (fnDefExpr h) `shouldBe` Set.fromList ["g"]
      fnDeps (fnDefExpr g) `shouldBe` Set.fromList []
      uncondFnDeps (fnDefExpr g) `shouldBe` Set.fromList []
      let fnDefs = [f, h, g]
      mapM_ (\defs -> fnDepsSort defs `shouldBe` fnDefs) (permutations fnDefs)

    it "f < g if f ~~?> g and not g ~~> f" $ do
      let (Right f) = parseFnDef "{fn f => {match {case False => h} {case True => }}}"
      let (Right h) = parseFnDef "{fn h => {match {case False => g} {case True => }}}"
      let (Right g) = parseFnDef "{fn g => }"
      fnDeps (fnDefExpr f) `shouldBe` Set.fromList ["h"]
      uncondFnDeps (fnDefExpr f) `shouldBe` Set.fromList []
      fnDeps (fnDefExpr h) `shouldBe` Set.fromList ["g"]
      uncondFnDeps (fnDefExpr h) `shouldBe` Set.fromList []
      fnDeps (fnDefExpr g) `shouldBe` Set.fromList []
      uncondFnDeps (fnDefExpr g) `shouldBe` Set.fromList []
      let fnDefs = [f, h, g]
      mapM_ (\defs -> fnDepsSort defs `shouldBe` fnDefs) (permutations fnDefs)

    it "f < g if f ~~!> g and g ~?> f" $ do
      let (Right f) = parseFnDef "{fn f => h}"
      let (Right h) = parseFnDef "{fn h => g}"
      let (Right g) = parseFnDef "{fn g => {match {case False => f} {case True => }}}"
      fnDeps (fnDefExpr f) `shouldBe` Set.fromList ["h"]
      uncondFnDeps (fnDefExpr f) `shouldBe` Set.fromList ["h"]
      fnDeps (fnDefExpr h) `shouldBe` Set.fromList ["g"]
      uncondFnDeps (fnDefExpr h) `shouldBe` Set.fromList ["g"]
      fnDeps (fnDefExpr g) `shouldBe` Set.fromList ["f"]
      uncondFnDeps (fnDefExpr g) `shouldBe` Set.fromList []
      let fnDefs = [f, h, g]
      mapM_ (\defs -> fnDepsSort defs `shouldBe` fnDefs) (permutations fnDefs)

  describe "defineFns examples" $ do
    it "defines drop2 and drop3" $ do
      let (Right drop2) = parseFnDef "{fn drop2 => drop drop}"
      let (Right drop3) = parseFnDef "{fn drop3 => drop2 drop}"
      let errs = []
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
      defineFns emptyEnv [drop2, drop3]
        `shouldBe` (errs, env)

    it "defines mutually recursive fns" $ do
      let (Right is_odd) = parseFnDef "{fn is_odd => 1 bit_and}"
      let is_odd_t = forall' [v0] (v0 * tU32 --> v0 * tU32)
      let (Right decr_even) =
            parseFnDef
              ( unlines
                  [ "{fn decr_even =>",
                    "  clone is_odd",
                    "  {match",
                    "    {case 0 0 => }",
                    "    {case 0 => 1 sub decr_odd}",
                    "    {case => drop decr_odd}",
                    "  }",
                    "}"
                  ]
              )
      let decr_even_t = forall' [v0] (v0 * tU32 --> v0)
      let (Right decr_odd) =
            parseFnDef
              ( unlines
                  [ "{fn decr_odd =>",
                    "  clone is_odd",
                    "  {match",
                    "    {case 0 1 => }",
                    "    {case 1 => 1 sub decr_even}",
                    "    {case => drop decr_even}",
                    "  }",
                    "}"
                  ]
              )
      let decr_odd_t = forall' [v0] (v0 * tU32 --> v0)
      let (Right count_down) = parseFnDef "{fn count_down => decr_odd}"
      let count_down_t = forall' [v0] (v0 * tU32 --> v0)
      let errs = []
      let env :: Env
          env =
            ( emptyEnv
                { fnDefs =
                    Map.fromList
                      [ ("is_odd", is_odd),
                        ("decr_even", decr_even),
                        ("decr_odd", decr_odd),
                        ("count_down", count_down)
                      ],
                  fnTypes =
                    Map.fromList
                      [ ("is_odd", is_odd_t),
                        ("decr_even", decr_even_t),
                        ("decr_odd", decr_odd_t),
                        ("count_down", count_down_t)
                      ]
                }
            )
      defineFns emptyEnv [is_odd, decr_even, decr_odd, count_down]
        `shouldBe` (errs, env)

    it "succeeds on direct recursion in one match case" $ do
      let (Right fib) =
            parseFnDef
              ( unlines
                  [ "{fn fib =>",
                    "  {match",
                    "    {case 0 => 0}",
                    "    {case 1 => 1}",
                    "    {case => clone 1 sub fib $a<- $b<- $a-> $b-> 2 sub fib add}",
                    "  }",
                    "}"
                  ]
              )
      let fib_t = forall' [v0] (v0 * tU32 --> v0 * tU32)
      let errs = []
      let env =
            emptyEnv
              { fnDefs = Map.singleton "fib" fib,
                fnTypes = Map.singleton "fib" fib_t
              }
      defineFns emptyEnv [fib] `shouldBe` (errs, env)

    it "fails on direct recursion outside of match expr" $ do
      let (Right diverge) = parseFnDef "{fn diverge => drop diverge 1}"
      let errs = [FnTypeError "diverge" (UndefinedFn "diverge")]
      let env = emptyEnv
      defineFns emptyEnv [diverge] `shouldBe` (errs, env)

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
      let foo_t = forall' [v0] (v0 * tU32 --> v0 * tU32)
      let errs = [FnTypeError "foo" (UndefinedFn "foo")]
      let env = emptyEnv
      defineFns emptyEnv [foo] `shouldBe` (errs, env)

    it "succeeds on mutual recursion in one match case in each function" $ do
      let (Right is_even) =
            parseFnDef
              ( unlines
                  [ "{fn is_even =>",
                    "  {match",
                    "    {case 0 => True}",
                    "    {case => decr is_odd}",
                    "  }",
                    "}"
                  ]
              )
      let is_even_t = forall' [v0] (v0 * tU32 --> v0 * tBool)

      let (Right is_odd) =
            parseFnDef
              ( unlines
                  [ "{fn is_odd =>",
                    "  {match",
                    "    {case 0 => False}",
                    "    {case => decr is_even}",
                    "  }",
                    "}"
                  ]
              )
      let is_odd_t = forall' [v0] (v0 * tU32 --> v0 * tBool)

      let errs = []
      let env =
            emptyEnv
              { fnDefs = Map.fromList [("is_even", is_even), ("is_odd", is_odd)],
                fnTypes = Map.fromList [("is_even", is_even_t), ("is_odd", is_odd_t)]
              }
      defineFns emptyEnv [is_even, is_odd] `shouldBe` (errs, env)

    it "fails on mutual recursion outside of match expr" $ do
      let (Right f1) = parseFnDef "{fn f1 => decr f2}"
      let f1_t = forall' [v0] (v0 * tU32 --> v0 * tBool)

      let (Right f2) = parseFnDef "{fn f2 => decr f1}"
      let f2_t = forall' [v0] (v0 * tU32 --> v0 * tBool)

      let errs =
            [ FnTypeError "f1" (UndefinedFn "f2"),
              FnTypeError "f2" (UndefinedFn "f1")
            ]
      let env = emptyEnv
      defineFns emptyEnv [f1, f2] `shouldBe` (errs, env)

    it "fails on mutual recursion in all match cases" $ do
      let (Right is_even) =
            parseFnDef
              ( unlines
                  [ "{fn is_even =>",
                    "  {match",
                    "    {case 0 => incr is_odd}",
                    "    {case => decr is_odd}",
                    "  }",
                    "}"
                  ]
              )
      let is_even_t = forall' [v0] (v0 * tU32 --> v0 * tBool)

      let (Right is_odd) =
            parseFnDef
              ( unlines
                  [ "{fn is_odd =>",
                    "  {match",
                    "    {case 0 => incr is_even}",
                    "    {case => decr is_even}",
                    "  }",
                    "}"
                  ]
              )
      let is_odd_t = forall' [v0] (v0 * tU32 --> v0 * tBool)

      let errs =
            [ FnTypeError "is_even" (UndefinedFn "is_odd"),
              FnTypeError "is_odd" (UndefinedFn "is_even")
            ]
      let env = emptyEnv
      defineFns emptyEnv [is_even, is_odd] `shouldBe` (errs, env)

    it "succeeds on mutual recursion in all but some match cases in one function (1)" $ do
      let (Right is_even) =
            parseFnDef
              ( unlines
                  [ "{fn is_even =>",
                    "  {match",
                    "    {case 0 => True}",
                    "    {case 1 => False}",
                    "    {case => decr is_odd}",
                    "  }",
                    "}"
                  ]
              )
      let is_even_t = forall' [v0] (v0 * tU32 --> v0 * tBool)

      let (Right is_odd) = parseFnDef "{fn is_odd => decr is_even}"
      let is_odd_t = forall' [v0] (v0 * tU32 --> v0 * tBool)

      let errs = []
      let env =
            emptyEnv
              { fnDefs = Map.fromList [("is_even", is_even), ("is_odd", is_odd)],
                fnTypes = Map.fromList [("is_even", is_even_t), ("is_odd", is_odd_t)]
              }
      defineFns emptyEnv [is_odd, is_even] `shouldBe` (errs, env)

    it "succeeds on mutual recursion in all but some match cases in one function (2)" $ do
      let (Right is_odd) =
            parseFnDef
              ( unlines
                  [ "{fn is_odd =>",
                    "  {match",
                    "    {case 0 => False}",
                    "    {case 1 => True}",
                    "    {case => decr is_even}",
                    "  }",
                    "}"
                  ]
              )
      let is_odd_t = forall' [v0] (v0 * tU32 --> v0 * tBool)

      let (Right is_even) = parseFnDef "{fn is_even => decr is_odd}"
      let is_even_t = forall' [v0] (v0 * tU32 --> v0 * tBool)

      let errs = []
      let env =
            emptyEnv
              { fnDefs = Map.fromList [("is_even", is_even), ("is_odd", is_odd)],
                fnTypes = Map.fromList [("is_even", is_even_t), ("is_odd", is_odd_t)]
              }
      defineFns emptyEnv [is_odd, is_even] `shouldBe` (errs, env)

    it "defines tail recursive fib" $ do
      let errs = []
      let env =
            emptyEnv
              { fnDefs =
                  Map.fromList
                    [ ("fib", fastFib),
                      ("_fib", _fastFib)
                    ],
                fnTypes =
                  Map.fromList
                    [ ("fib", forall' [v0] (v0 * tU32 --> v0 * tU32)),
                      ( "_fib",
                        forall
                          [v0, v1, v2]
                          ( "$" $: v0 * tU32 --> v0 * tU32
                              $. "$a" $: v1 * tU32 --> v1
                              $. "$b" $: v2 * tU32 --> v2
                          )
                      )
                    ]
              }
      defineFns emptyEnv [fastFib, _fastFib] `shouldBe` (errs, env)

  describe "addDataDefs" $ do
    it "adds `{data Bit {cons B0} {cons B1}}`" $ do
      let (Right def) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let dataDefs = Map.singleton "Bit" def
      let typeConsArities = Map.singleton "Bit" 0
      let consDefs = Map.fromList [("B0", ConsDef [] "B0"), ("B1", ConsDef [] "B1")]
      let tBit = TCons [] "Bit"
      let consTypes = Map.fromList [("B0", ([], tBit)), ("B1", ([], tBit))]
      addDataDefs emptyEnv [def]
        `shouldBe` ([], emptyEnv {dataDefs, typeConsArities, consDefs, consTypes})

    it "adds `{data v0 v1 Pair {cons v0 v1 Pair}}`" $ do
      let (Right def) = parseDataDef "{data v0 v1 Pair {cons v0 v1 Pair}}"
      let dataDefs = Map.singleton "Pair" def
      let typeConsArities = Map.singleton "Pair" 2
      let consDefs = Map.fromList [("Pair", ConsDef [v0, v1] "Pair")]
      let consTypes = Map.fromList [("Pair", ([v0, v1], TCons [v0, v1] "Pair"))]
      addDataDefs emptyEnv [def]
        `shouldBe` ([], emptyEnv {dataDefs, typeConsArities, consDefs, consTypes})

    it "adds `{data v0 v1 SwapPair {cons v1 v0 SwapPair}}`" $ do
      let (Right def) = parseDataDef "{data v0 v1 SwapPair {cons v1 v0 SwapPair}}"
      let dataDefs = Map.singleton "SwapPair" def
      let typeConsArities = Map.singleton "SwapPair" 2
      let consDefs = Map.fromList [("SwapPair", ConsDef [v1, v0] "SwapPair")]
      let consTypes = Map.fromList [("SwapPair", ([v1, v0], TCons [v0, v1] "SwapPair"))]
      addDataDefs emptyEnv [def]
        `shouldBe` ([], emptyEnv {dataDefs, typeConsArities, consDefs, consTypes})

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
      addDataDefs emptyEnv [def]
        `shouldBe` ([], emptyEnv {dataDefs, typeConsArities, consDefs, consTypes})

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
      addDataDefs emptyEnv [defA, defB]
        `shouldBe` ([], emptyEnv {dataDefs, typeConsArities, consDefs, consTypes})

    it "fails with TypeConsAlreadyDefined" $ do
      let (Right def) = parseDataDef "{data Foo}"
      let ([], env) = addDataDefs emptyEnv [def]
      addDataDefs env [def]
        `shouldBe` ([TypeConsAlreadyDefined "Foo"], env)
      addDataDefs emptyEnv [def, def]
        `shouldBe` ([TypeConsAlreadyDefined "Foo"], env)

    it "fails with ConsAlreadyDefined" $ do
      let (Right def1) = parseDataDef "{data Bit1 {cons B0} {cons B1}}"
      let (Right def2) = parseDataDef "{data Bit2 {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [def1]
      addDataDefs env [def2]
        `shouldBe` ([ConsAlreadyDefined "Bit2" "B0"], env)
      addDataDefs emptyEnv [def1, def2]
        `shouldBe` ([ConsAlreadyDefined "Bit2" "B0"], env)

    it "fails with DuplicateTypeVar" $ do
      let (Right def) = parseDataDef "{data v0 v0 Test {cons v0 v0 Test}}"
      addDataDefs emptyEnv [def]
        `shouldBe` ([DuplicateTypeVar "Test" tv0], emptyEnv)

    it "fails with UndefinedTypeVar" $ do
      let (Right def) = parseDataDef "{data Stack {cons Empty} {cons Stack v0 Push}}"
      addDataDefs emptyEnv [def]
        `shouldBe` ([UndefinedTypeVar "Stack" tv0], emptyEnv)

    it "fails with UndefinedTypeCons" $ do
      let (Right def) =
            parseDataDef
              "{data v0 v1 A {cons EmptyA} {cons (v0 v1 B) v0 A}}"
      addDataDefs emptyEnv [def]
        `shouldBe` ([UndefinedTypeCons "B"], emptyEnv)

    it "fails with TypeConsArityMismatch" $ do
      let (Right def) =
            parseDataDef
              "{data v0 Stack {cons Empty} {cons Stack v0 Push}}"
      addDataDefs emptyEnv [def]
        `shouldBe` ([TypeConsArityMismatch "Stack" (TCons [] "Stack")], emptyEnv)

fastFibSrc = "{fn fib => {$a 0} {$b 1} _fib}"

_fastFibSrc =
  unlines
    [ "{fn _fib => {match",
      "  {case 0 => {$b drop} $a->}",
      "  {case => decr {$b clone pop $a-> add} $a<- _fib}",
      "}}"
    ]

(Right fastFib) = parseFnDef fastFibSrc

(Right _fastFib) = parseFnDef _fastFibSrc
