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

[clone, drop, swap, quote, compose, apply] =
  map EIntrinsic [IClone, IDrop, ISwap, IQuote, ICompose, IApply]

spec :: Spec
spec = do
  describe "renameTypeVar" $ do
    it "renames the specified type variable" $ do
      renameTypeVar tv0 tv2 (forall [v0, v1] (v0 --> v0 * v1))
        `shouldBe` forall [v2, v1] (v2 --> v2 * v1)

    it "throws on type variable shadowing" $ do
      evaluate (renameTypeVar tv0 tv1 (forall [v0, v1] (v0 --> v0 * v1)))
        `shouldThrow` anyException

  describe "ftv" $ do
    it "returns the free type variables" $ do
      ftv (forall [v2] (v2 * v0 --> v2 * v3 * forall [v1] (v1 * v4 --> v1 * v5)))
        `shouldBe` Set.fromList (map TypeVar [0, 3, 4, 5])

  describe "atv" $ do
    it "returns all type variables, in the order they appear" $ do
      atv (forall [v2] (v2 * v0 --> v2 * v3 * forall [v1] (v1 * v4 --> v1 * v5)))
        `shouldBe` map TypeVar [2, 0, 3, 1, 4, 5]

  describe "freshTypeVar" $ do
    it "returns the first fresh type variable" $ do
      freshTypeVar (Set.fromList (map TypeVar [0, 1, 2, 4, 5]))
        `shouldBe` (TypeVar 3, Set.fromList (map TypeVar [0, 1, 2, 3, 4, 5]))

  describe "replaceTypeVars" $ do
    it "replaces the specified type variables with fresh type variables" $ do
      let tvs = [tv2, tv1]
      let t = forall [v1] (v1 --> v1 * v2)
      let reserved = Set.fromList [tv0, tv1, tv2, tv3]
      let t' = forall [v5] (v5 --> v5 * v4)
      let reserved' = Set.fromList [tv0, tv1, tv2, tv3, tv4, tv5]
      replaceTypeVars tvs t reserved
        `shouldBe` (t', reserved')

  describe "instantiate" $ do
    it "instantiates all quantified type variables with fresh type variables" $ do
      let t = forall [v1] (v1 --> v1 * v2)
      let reserved = Set.fromList [tv0, tv1, tv2, tv3]
      let t' = forall [v4] (v4 --> v4 * v2)
      let reserved' = Set.fromList [tv0, tv1, tv2, tv3, tv4]
      instantiate t reserved
        `shouldBe` (t', reserved')

  describe "subs" $ do
    it "applies substitutions" $ do
      let t = forall [v1] (v0 --> v0 * v1)
      let t' = forall [v1] (v2 --> v2 * v1)
      subs (tv0 +-> v2) t (Set.fromList $ atv t)
        `shouldBe` (t', Set.fromList $ atv t ++ atv t')

    it "instantiates quantified type variables" $ do
      let s = tv0 +-> forall [v1] (v1 --> v1 * v2)
      let t = v0
      let reserved = Set.fromList [tv0, tv1, tv2]
      let t' = forall [v3] (v3 --> v3 * v2)
      let reserved' = Set.fromList [tv0, tv1, tv2, tv3]
      subs s t reserved
        `shouldBe` (t', reserved')

  describe "composeSubst" $ do
    it "composes substitutions" $ do
      let reserved = Set.fromList [tv0, tv1, tv2]
      composeSubst (tv1 +-> v2) (tv0 +-> v1) reserved
        `shouldBe` (Subst (Map.fromList [(tv0, v2), (tv1, v2)]), reserved)

    it "avoids type variable capture" $ do
      let s1 = tv0 +-> forall [v2] (v2 --> v2 * v1)
      let s2 = tv1 +-> forall [v2, v3] (v2 * v3 --> v2 * v3)
      let reserved = Set.fromList [tv0, tv1, tv2, tv3]

      let s1' = tv0 +-> forall [v2] (v2 --> v2 * forall [v4, v5] (v4 * v5 --> v4 * v5))
      let s2' = tv1 +-> forall [v2, v3] (v2 * v3 --> v2 * v3)
      let reserved' = Set.fromList [tv0, tv1, tv2, tv3, tv4, tv5]

      composeSubst s2 s1 reserved `shouldBe` composeSubst s2' s1' reserved'

  describe "mgu" $ do
    it "finds the most general unifier" $ do
      let t =
            forall
              [v0, v2]
              ( v0 --> v0 * forall [v1] (v1 --> v1 * v2) * v2 * v2
              )
      let t' =
            forall
              [v3, v4, v5, v7, v8]
              ( v3 * v4 --> v3 * v4 * v5 * forall [v6] (v6 --> v6 * v7) * v8
              )
      let reserved = Set.fromList (map TypeVar [0 .. 8])
      let s =
            Subst $
              Map.fromList
                [ (tv0, v3 * v4),
                  (tv5, forall [v1] (v1 --> v1 * forall [v9] (v9 --> v9 * v7))),
                  (tv2, forall [v6] (v6 --> v6 * v7)),
                  (tv8, forall [v10] (v10 --> v10 * v7))
                ]
      let reserved' = Set.fromList (map TypeVar [0 .. 10])
      mgu t t' reserved `shouldBe` Right (s, reserved')

  describe "requantify" $ do
    it "properly requantifies" $ do
      let t =
            forall
              [v0, v1, v2]
              ( v0 * forall [] (v1 --> v1)
                  --> v0 * forall [] (v1 --> v1 * forall [] (v2 --> v2))
              )
      let t' =
            forall
              [v0, v1]
              ( v0 * forall [] (v1 --> v1)
                  --> v0 * forall [] (v1 --> v1 * forall [v2] (v2 --> v2))
              )
      requantify t `shouldBe` t'

  describe "inferType" $ do
    it "infers `[clone] apply` == `clone` " $ do
      let e1 = ECompose [EQuote (EIntrinsic IClone), EIntrinsic IApply]
      let e2 = EIntrinsic IClone
      inferNormType e1 `shouldBe` inferNormType e2

    it "does not infer free type variables" $ do
      let iter e = case inferType e of
            Left _ -> return ()
            Right t -> (display e, ftv t) `shouldBe` (display e, Set.empty)
      mapM_ iter (allExprsUpToWidthAndDepth 3 1)

    it "does not infer duplicate quantifiers" $ do
      let count :: Type -> Map.Map TypeVar Int
          count (TVar _) = Map.empty
          count (TProd l r) = Map.unionWith (+) (count l) (count r)
          count (TFn qs (i, o)) =
            Map.unionWith
              (+)
              (Map.fromList (map (\v -> (v, 1)) (Set.toList qs)))
              (Map.unionWith (+) (count i) (count o))
      let iter e = case inferType e of
            Left _ -> return ()
            Right t ->
              (display e, any (> 1) (Map.elems (count t)))
                `shouldBe` (display e, False)
      mapM_ iter (allExprsUpToWidthAndDepth 3 1)

    it "does not infer unused quantifiers" $ do
      let iter e = case inferType e of
            Left _ -> return ()
            Right t -> (display e, unusedQuantifiers t) `shouldBe` (display e, Set.empty)
      mapM_ iter (allExprsUpToWidthAndDepth 3 1)

    it "infers `[clone] [swap apply] apply`" $ do
      let e = ECompose [EQuote clone, EQuote (ECompose [swap, apply]), apply]
      inferNormType e
        `shouldBe` Right
          ( forall [v0, v3] (v0 * (v0 * forall [v1, v2] (v1 * v2 --> v1 * v2 * v2) --> v3) --> v3)
          )

    it "infers `(clone [drop]) compose` == `clone ([drop] compose)`" $ do
      let (Right e1) = parseExpr "(clone [drop]) compose"
      let (Right e2) = parseExpr "clone ([drop] compose)"
      inferNormType e1 `shouldBe` inferNormType e2

    it "infers the same type for all groupings" $ do
      let iter e = do
            let d = display e
            let es = allGroupings e
            let ts = filter isRight (map inferNormType es)
            when
              (length ts > 1)
              (mapM_ (\t' -> (d, head ts) `shouldBe` (d, t')) (tail ts))
      mapM_ iter (allExprsUpToWidthAndDepth 3 1)

  describe "partialEval" $ do
    it "preserves types" $ do
      let iter e = case inferNormType e of
            Left _ -> return ()
            Right t -> (display e, Right t) `shouldBe` (display e, inferNormType (partialEval e))
      mapM_ iter (allExprsUpToWidthAndDepth 2 1)

    it "preserves type of `[clone] clone compose`" $ do
      let (Right e) = parseExpr "[clone] clone compose"
      fmap display (inferNormType e)
        `shouldBe` fmap display (inferNormType (partialEval e))

    it "preserves type of `[clone] [[drop] compose] compose`" $ do
      let (Right e) = parseExpr "[clone] [[drop] compose] compose"
      fmap display (inferNormType e)
        `shouldBe` fmap display (inferNormType (partialEval e))

    it "evals `[clone] clone`" $ do
      let e = ECompose [EQuote clone, clone]
      let e' = ECompose [EQuote clone, EQuote clone]
      partialEval e `shouldBe` e'

    it "evals `[clone] drop`" $ do
      let e = ECompose [EQuote clone, drop]
      let e' = ECompose []
      partialEval e `shouldBe` e'

    it "evals `[clone] [drop] swap`" $ do
      let e = ECompose [EQuote clone, EQuote drop, swap]
      let e' = ECompose [EQuote drop, EQuote clone]
      partialEval e `shouldBe` e'

    it "evals `[clone] quote`" $ do
      let e = ECompose [EQuote clone, quote]
      let e' = EQuote (EQuote clone)
      partialEval e `shouldBe` e'

    it "evals `[clone] [clone] compose`" $ do
      let e = ECompose [EQuote clone, EQuote clone, compose]
      let e' = EQuote (ECompose [clone, clone])
      partialEval e `shouldBe` e'

    it "evals `[clone] apply`" $ do
      let e = ECompose [EQuote clone, apply]
      let e' = clone
      partialEval e `shouldBe` e'
