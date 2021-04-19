-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Language.Dawn.Phase1.EvalSpec (spec) where

import Control.Exception
import Control.Monad
import Data.Either
import Data.Either.Combinators
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.CoreSpec hiding (spec)
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Exprs
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.PartialEval
import Language.Dawn.Phase1.Utils
import Test.Hspec
import Prelude hiding (drop, (*))

[clone, drop, quote, compose, apply] =
  map EIntrinsic [IClone, IDrop, IQuote, ICompose, IApply]

spec :: Spec
spec = do
  describe "splitStackAt" $ do
    it "splits `` at 0" $ do
      let (Right vs) = parseValStack ""
      splitStackAt 0 vs `shouldBe` (Empty, Empty)

    it "splits `Z` at 0" $ do
      let (Right vs) = parseValStack "Z"
      splitStackAt 0 vs `shouldBe` (vs, Empty)

    it "splits `Z` at 1" $ do
      let (Right vs) = parseValStack "Z"
      splitStackAt 1 vs `shouldBe` (Empty, vs)

    it "splits `Z Z` at 0" $ do
      let (Right vs) = parseValStack "Z Z"
      splitStackAt 0 vs `shouldBe` (vs, Empty)

    it "splits `Z Z` at 1" $ do
      let (Right vs) = parseValStack "Z Z"
      let (Right vs') = parseValStack "Z"
      splitStackAt 1 vs `shouldBe` (vs', vs')

    it "splits `Z Z` at 2" $ do
      let (Right vs) = parseValStack "Z Z"
      splitStackAt 2 vs `shouldBe` (Empty, vs)

  describe "eval" $ do
    it "evals `[clone] clone`" $ do
      let (Right e) = parseExpr "[clone] clone"
      let (Right msv) = parseValMultiStack "[clone] [clone]"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` msv

    it "evals `[clone] drop`" $ do
      let (Right e) = parseExpr "[clone] drop"
      let ms = MultiStack Map.empty
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `[clone] quote`" $ do
      let (Right e) = parseExpr "[clone] quote"
      let (Right ms) = parseValMultiStack "[[clone]]"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `[clone] [clone] compose`" $ do
      let (Right e) = parseExpr "[clone] [clone] compose"
      let (Right ms) = parseValMultiStack "[clone clone]"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `Z [clone] apply`" $ do
      let (Right e) = parseExpr "Z [clone] apply"
      let (Right ms) = parseValMultiStack "Z Z"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `[drop] (clone compose)`" $ do
      let (Right e) = parseExpr "[drop] (clone compose)"
      let (Right ms) = parseValMultiStack "[drop drop]"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `True True bool_and`" $ do
      let (Right e) = parseExpr "True True bool_and"
      let (Right ms) = parseValMultiStack "True"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `Z (Z S) $a<- $b<- $a-> $b->`" $ do
      let (Right e) = parseExpr "Z (Z S) $a<- $b<- $a-> $b->"
      let (Right ms) = parseValMultiStack "(Z S) Z"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `{match {case =>}}`" $ do
      let (Right e) = parseExpr "{match {case =>}}"
      let ms = MultiStack Map.empty
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `Z {match {case Z => (Z S)} {case => drop Z}}`" $ do
      let (Right e) = parseExpr "Z {match {case Z => (Z S)} {case => drop Z}}"
      let (Right ms) = parseValMultiStack "(Z S)"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `(Z S) {match {case Z => (Z S)} {case => drop Z}}`" $ do
      let (Right e) = parseExpr "(Z S) {match {case Z => (Z S)} {case => drop Z}}"
      let (Right ms) = parseValMultiStack "Z"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `Z Z {match {case Z Z => (Z S)} {case => drop drop Z}}`" $ do
      let (Right e) = parseExpr "Z Z {match {case Z Z => (Z S)} {case => drop drop Z}}"
      let (Right ms) = parseValMultiStack "(Z S)"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `Z (Z S) {match {case Z Z => (Z S)} {case => drop drop Z}}`" $ do
      let (Right e) = parseExpr "Z (Z S) {match {case Z Z => (Z S)} {case => drop drop Z}}"
      let (Right ms) = parseValMultiStack "Z"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `Z (Z S) swap`" $ do
      let (Right e) = parseExpr "Z (Z S) swap"
      let ms = MultiStack Map.empty
      let (Right ms') = parseValMultiStack "(Z S) Z"
      eval (toEvalEnv testEnv) ["$"] e ms `shouldBe` ms'

    it "evals `{$c Z (Z S) swap}`" $ do
      let (Right e) = parseExpr "{$c Z (Z S) swap}"
      let ms = MultiStack Map.empty
      let (Right ms') = parseValMultiStack "{$c (Z S) Z}"
      eval (toEvalEnv testEnv) ["$"] e ms `shouldBe` ms'

    it "evals `{$a Z (Z S) swap}`" $ do
      let (Right e) = parseExpr "{$a Z (Z S) swap}"
      let ms = MultiStack Map.empty
      let (Right ms') = parseValMultiStack "{$a (Z S) Z}"
      eval (toEvalEnv testEnv) ["$"] e ms `shouldBe` ms'

    it "evals fib" $ do
      let (Right env) = tryAddFnDefs testEnv [fib]
      let (Right e) = parseExpr "Z fib"
      let (Right ms) = parseValMultiStack "Z"
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms

      let (Right e) = parseExpr "(Z S) fib"
      let (Right ms) = parseValMultiStack "(Z S)"
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms

      let (Right e) = parseExpr "((((((Z S) S) S) S) S) S) fib"
      let (Right ms) = parseValMultiStack "((((((((Z S) S) S) S) S) S) S) S)"
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `B0 {match {case B0 => B1} {case B1 => B0}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "B0 {match {case B0 => B1} {case B1 => B0}}"
      let (Right ms') = parseValMultiStack "B1"
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `{$a B0 {match {case B0 => B1} {case B1 => B0}}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "{$a B0 {match {case B0 => B1} {case B1 => B0}}}"
      let (Right ms') = parseValMultiStack "{$a B1}"
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z True Pair {match {case Pair => }}`" $ do
      let (Right e) = parseExpr "Z True Pair {match {case Pair => }}"
      let (Right ms') = parseValMultiStack "Z True"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z Z`" $ do
      let (Right e) = parseExpr "Z Z"
      let (Right ms') = parseValMultiStack "Z Z"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals recursive Nat pattern (Z S)" $ do
      let (Right d) = parseDataDef "{data Nat {cons Z} {cons Nat S}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "Z S {match {case (Z S) => }}"
      let ms = MultiStack Map.empty
      eval (toEvalEnv env) ["$"] e ms `shouldBe` ms

    it "evals recursive Nat pattern ((Z S) S)" $ do
      let (Right d) = parseDataDef "{data Nat {cons Z} {cons Nat S}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "Z S S {match {case (S S) => }}"
      let (Right ms') = parseValMultiStack "Z"
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals recursive Bit Stack pattern (Z S)" $ do
      let (Right dBit) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let (Right dStack) =
            parseDataDef
              "{data v0 Stack {cons Empty} {cons (v0 Stack) v0 Push}}"
      let ([], env) = addDataDefs emptyEnv [dBit, dStack]
      let (Right e) =
            parseExpr
              "Empty B0 Push {match {case (Empty B0 Push) => }}"
      let ms = MultiStack Map.empty
      eval (toEvalEnv env) ["$"] e ms `shouldBe` ms

    it "evals recursive Bit Stack pattern ((Z S) S)" $ do
      let (Right dBit) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let (Right dStack) =
            parseDataDef
              "{data v0 Stack {cons Empty} {cons (v0 Stack) v0 Push}}"
      let ([], env) = addDataDefs emptyEnv [dBit, dStack]
      let (Right e) =
            parseExpr
              "Empty B1 Push B0 Push {match {case (Push B0 Push) => }}"
      let (Right ms') = parseValMultiStack "Empty B1"
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z {match {case Z => }}`" $ do
      let (Right e) = parseExpr "Z {match {case Z => }}"
      let ms' = MultiStack Map.empty
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z S {match {case S => }}`" $ do
      let (Right e) = parseExpr "Z S {match {case S => }}"
      let (Right ms') = parseValMultiStack "Z"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z S {match {case (Z S) => }}`" $ do
      let (Right e) = parseExpr "Z S {match {case (Z S) => }}"
      let ms' = MultiStack Map.empty
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z S S {match {case (S S) => }}`" $ do
      let (Right e) = parseExpr "Z S S {match {case (S S) => }}"
      let (Right ms') = parseValMultiStack "Z"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty Z Push {match {case Push =>}}`" $ do
      let (Right e) = parseExpr "Empty Z Push {match {case Push =>}}"
      let (Right ms') = parseValMultiStack "Empty Z"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty B0 Push {match {case (B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "Empty B0 Push {match {case (B0 Push) =>}}"
      let (Right ms') = parseValMultiStack "Empty"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty B0 Push {match {case (Empty B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "Empty B0 Push {match {case (Empty B0 Push) =>}}"
      let ms' = MultiStack Map.empty
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty B1 Push B0 Push {match {case (Push B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "Empty B1 Push B0 Push {match {case (Push B0 Push) =>}}"
      let (Right ms') = parseValMultiStack "Empty B1"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty B1 Push B0 Push {match {case ((B1 Push) B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "Empty B1 Push B0 Push {match {case ((B1 Push) B0 Push) =>}}"
      let (Right ms') = parseValMultiStack "Empty"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z S Empty B0 Push Pair {match {case (S Push Pair) =>}}`" $ do
      let (Right e) = parseExpr "Z S Empty B0 Push Pair {match {case (S Push Pair) =>}}"
      let (Right ms') = parseValMultiStack "Z Empty B0"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty Z Push Empty B0 Push Pair {match {case (Push Push Pair) =>}}`" $ do
      let (Right e) = parseExpr "Empty Z Push Empty B0 Push Pair {match {case (Push Push Pair) =>}}"
      let (Right ms') = parseValMultiStack "Empty Z Empty B0"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty Z Push Empty B0 Push Pair {match {case (Push _ Pair) =>}}`" $ do
      let (Right e) = parseExpr "Empty Z Push Empty B0 Push Pair {match {case (Push _ Pair) =>}}"
      let (Right ms') = parseValMultiStack "Empty Z (Empty B0 Push)"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "infers `Z (Z S) nat_add`" $ do
      let (Right e) = parseExpr "Z (Z S) nat_add"
      let (Right ms') = parseValMultiStack "(Z S)"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "infers `{$a Z (Z S) nat_add}`" $ do
      let (Right e) = parseExpr "{$a Z (Z S) nat_add}"
      let (Right ms') = parseValMultiStack "{$a (Z S)}"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `{$$ Z S} {match {case {$$ S} =>}}`" $ do
      let (Right e) = parseExpr "{$$ Z S} {match {case {$$ S} =>}}"
      let (Right ms') = parseValMultiStack "{$$ Z}"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `{$$ Z S Z S} {match {case {$$ S S} =>}}`" $ do
      let (Right e) = parseExpr "{$$ Z S Z S} {match {case {$$ S S} =>}}"
      let (Right ms') = parseValMultiStack "{$$ Z Z}"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `{$a Z S} {$b Z S} {match {case {$a S} {$b S} =>}}`" $ do
      let (Right e) = parseExpr "{$a Z S} {$b Z S} {match {case {$a S} {$b S} =>}}"
      let (Right ms') = parseValMultiStack "{$a Z} {$b Z}"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `{$$ Z S} {$a {match {case {$$ S} =>}}}`" $ do
      let (Right e) = parseExpr "{$$ Z S} {$a {match {case {$$ S} =>}}}"
      let (Right ms') = parseValMultiStack "{$$ Z}"
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `{$$ {$$ Z S} {match {case {$$ S} =>}}}`" $ do
      let (Right e) = parseExpr "{$$ {$$ Z S} {match {case {$$ S} =>}}}"
      let (Right vs) = parseValStack "Z"
      let ms' = MultiStack (Map.singleton "$$$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

  describe "evalWithFuel" $ do
    it "stops at Z fuel" $ do
      let (Right e) = parseExpr "Z"
      let ms = MultiStack Map.empty
      evalWithFuel (toEvalEnv testEnv) ["$"] (0, e, ms) `shouldBe` (0, e, ms)

    it "allows negative fuel" $ do
      let (Right e) = parseExpr "Z"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right ms') = parseValMultiStack "Z"
      evalWithFuel (toEvalEnv testEnv) ["$"] (-1, e, ms) `shouldBe` (-2, e', ms')

    it "evals `Z [clone] apply`" $ do
      let (Right e) = parseExpr "Z [clone] apply"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right ms') = parseValMultiStack "Z Z"
      evalWithFuel (toEvalEnv testEnv) ["$"] (4, e, ms) `shouldBe` (0, e', ms')

    it "evals `Z (Z S) swap`" $ do
      let (Right e) = parseExpr "Z (Z S) swap"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right ms') = parseValMultiStack "(Z S) Z"
      evalWithFuel (toEvalEnv testEnv) ["$"] (8, e, ms) `shouldBe` (0, e', ms')

    it "evals `{match {case =>}}`" $ do
      let (Right e) = parseExpr "{match {case =>}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let ms' = MultiStack Map.empty
      evalWithFuel (toEvalEnv testEnv) ["$"] (1, e, ms) `shouldBe` (0, e', ms')

    it "evals `Z {match {case Z => (Z S)} {case => drop Z}}`" $ do
      let (Right e) = parseExpr "Z {match {case Z => (Z S)} {case => drop Z}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right ms') = parseValMultiStack "(Z S)"
      evalWithFuel (toEvalEnv testEnv) ["$"] (4, e, ms) `shouldBe` (0, e', ms')

    it "evals `(Z S) {match {case Z => (Z S)} {case => drop Z}}`" $ do
      let (Right e) = parseExpr "(Z S) {match {case Z => (Z S)} {case => drop Z}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right ms') = parseValMultiStack "Z"
      evalWithFuel (toEvalEnv testEnv) ["$"] (6, e, ms) `shouldBe` (0, e', ms')

    it "evals `Z Z {match {case Z Z => (Z S)} {case => drop drop Z}}`" $ do
      let (Right e) = parseExpr "Z Z {match {case Z Z => (Z S)} {case => drop drop Z}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right ms') = parseValMultiStack "(Z S)"
      evalWithFuel (toEvalEnv testEnv) ["$"] (5, e, ms) `shouldBe` (0, e', ms')

    it "evals `Z (Z S) {match {case Z Z => (Z S)} {case => drop drop Z}}`" $ do
      let (Right e) = parseExpr "Z (Z S) {match {case Z Z => (Z S)} {case => drop drop Z}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right ms') = parseValMultiStack "Z"
      evalWithFuel (toEvalEnv testEnv) ["$"] (8, e, ms) `shouldBe` (0, e', ms')

    it "evals `fib`" $ do
      let intToNatStr 0 = "Z"
          intToNatStr i = "(" ++ intToNatStr (i - 1) ++ " S)"
      let (Right env) = tryAddFnDefs testEnv [fib]
          evalFib n =
            let (Right e) = parseExpr (intToNatStr n ++ " fib")
                ms = MultiStack Map.empty
                e' = ECompose []
             in evalWithFuel (toEvalEnv env) ["$"] (-1, e, ms)
          n `inSteps` steps =
            let (Right ms) = parseValMultiStack (intToNatStr n)
             in (-1 - steps, ECompose [], ms)

      evalFib 0 `shouldBe` 0 `inSteps` 4
      evalFib 1 `shouldBe` 1 `inSteps` 7
      evalFib 2 `shouldBe` 1 `inSteps` 32
      evalFib 3 `shouldBe` 2 `inSteps` 65
      evalFib 4 `shouldBe` 3 `inSteps` 122
      evalFib 5 `shouldBe` 5 `inSteps` 217
      evalFib 6 `shouldBe` 8 `inSteps` 374
      evalFib 7 `shouldBe` 13 `inSteps` 637
      evalFib 8 `shouldBe` 21 `inSteps` 1074
      evalFib 9 `shouldBe` 34 `inSteps` 1803

    it "evals tail recursive fib" $ do
      let intToNatStr 0 = "Z"
          intToNatStr i = "(" ++ intToNatStr (i - 1) ++ " S)"
      let (Right env) = tryAddFnDefs testEnv [fastFib, _fastFib]
          evalFastFib n =
            let (Right e) = parseExpr (intToNatStr n ++ " fib")
                ms = MultiStack Map.empty
                e' = ECompose []
             in evalWithFuel (toEvalEnv env) ["$"] (-1, e, ms)
          n `inSteps` steps =
            let (Right ms) = parseValMultiStack (intToNatStr n)
             in (-1 - steps, ECompose [], ms)

      evalFastFib 0 `shouldBe` 0 `inSteps` 9
      evalFastFib 1 `shouldBe` 1 `inSteps` 19
      evalFastFib 2 `shouldBe` 1 `inSteps` 35
      evalFastFib 3 `shouldBe` 2 `inSteps` 51
      evalFastFib 4 `shouldBe` 3 `inSteps` 73
      evalFastFib 5 `shouldBe` 5 `inSteps` 101
      evalFastFib 6 `shouldBe` 8 `inSteps` 141
      evalFastFib 7 `shouldBe` 13 `inSteps` 199
      evalFastFib 8 `shouldBe` 21 `inSteps` 287
      evalFastFib 9 `shouldBe` 34 `inSteps` 423

    it "evals `B0 {match {case B0 => B1} {case B1 => B0}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "B0 {match {case B0 => B1} {case B1 => B0}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right ms') = parseValMultiStack "B1"
      evalWithFuel (toEvalEnv env) ["$"] (3, e, ms) `shouldBe` (0, e', ms')

    it "evals `{$a B0 {match {case B0 => B1} {case B1 => B0}}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "{$a B0 {match {case B0 => B1} {case B1 => B0}}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right ms') = parseValMultiStack "{$a B1}"
      evalWithFuel (toEvalEnv env) ["$"] (3, e, ms) `shouldBe` (0, e', ms')

    it "evals `Z True Pair {match {case Pair => }}`" $ do
      let (Right e) = parseExpr "Z True Pair {match {case Pair => }}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right ms') = parseValMultiStack "Z True"
      evalWithFuel (toEvalEnv testEnv) ["$"] (4, e, ms) `shouldBe` (0, e', ms')

fibSrc =
  unlines
    [ "{fn fib => {match",
      "  {case Z => Z}",
      "  {case (Z S) => (Z S)}",
      "  {case => clone nat_decr fib swap nat_decr nat_decr fib nat_add}",
      "}}"
    ]

(Right fib) = parseFnDef fibSrc

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
