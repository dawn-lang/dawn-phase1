-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

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

  describe "eval'" $ do
    it "evals `[clone] clone`" $ do
      let (Right e) = parseExpr "[clone] clone"
      let (Right vs) = parseValStack "[clone] [clone]"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `[clone] drop`" $ do
      let (Right e) = parseExpr "[clone] drop"
      let ms = MultiStack Map.empty
      eval' e `shouldBe` ms

    it "evals `[clone] quote`" $ do
      let (Right e) = parseExpr "[clone] quote"
      let (Right vs) = parseValStack "[[clone]]"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `[clone] [clone] compose`" $ do
      let (Right e) = parseExpr "[clone] [clone] compose"
      let (Right vs) = parseValStack "[clone clone]"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 [clone] apply`" $ do
      let (Right e) = parseExpr "0 [clone] apply"
      let (Right vs) = parseValStack "0 0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `[drop] (clone compose)`" $ do
      let (Right e) = parseExpr "[drop] (clone compose)"
      let (Right vs) = parseValStack "[drop drop]"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `True True and`" $ do
      let (Right e) = parseExpr "True True and"
      let (Right vs) = parseValStack "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `True False or`" $ do
      let (Right e) = parseExpr "True False or"
      let (Right vs) = parseValStack "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `False not`" $ do
      let (Right e) = parseExpr "False not"
      let (Right vs) = parseValStack "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `True False xor`" $ do
      let (Right e) = parseExpr "True False xor"
      let (Right vs) = parseValStack "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 incr`" $ do
      let (Right e) = parseExpr "0 incr"
      let (Right vs) = parseValStack "1"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 decr`" $ do
      let (Right e) = parseExpr "1 decr"
      let (Right vs) = parseValStack "0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `2 2 add`" $ do
      let (Right e) = parseExpr "2 2 add"
      let (Right vs) = parseValStack "4"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `4 2 sub`" $ do
      let (Right e) = parseExpr "4 2 sub"
      let (Right vs) = parseValStack "2"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `2 3 bit_and`" $ do
      let (Right e) = parseExpr "2 3 bit_and"
      let (Right vs) = parseValStack "2"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 2 bit_or`" $ do
      let (Right e) = parseExpr "1 2 bit_or"
      let (Right vs) = parseValStack "3"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 bit_not bit_not`" $ do
      let (Right e) = parseExpr "0 bit_not bit_not"
      let (Right vs) = parseValStack "0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 6 bit_xor`" $ do
      let (Right e) = parseExpr "5 6 bit_xor"
      let (Right vs) = parseValStack "3"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 2 shl`" $ do
      let (Right e) = parseExpr "1 2 shl"
      let (Right vs) = parseValStack "4"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `8 2 shr`" $ do
      let (Right e) = parseExpr "8 2 shr"
      let (Right vs) = parseValStack "2"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 5 eq`" $ do
      let (Right e) = parseExpr "5 5 eq"
      let (Right vs) = parseValStack "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 5 lt`" $ do
      let (Right e) = parseExpr "5 5 lt"
      let (Right vs) = parseValStack "False"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 5 gt`" $ do
      let (Right e) = parseExpr "5 5 gt"
      let (Right vs) = parseValStack "False"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 5 lteq`" $ do
      let (Right e) = parseExpr "5 5 lteq"
      let (Right vs) = parseValStack "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `5 5 gteq`" $ do
      let (Right e) = parseExpr "5 5 gteq"
      let (Right vs) = parseValStack "True"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 1 $a<- $b<- $a-> $b->`" $ do
      let (Right e) = parseExpr "0 1 $a<- $b<- $a-> $b->"
      let (Right vs) = parseValStack "1 0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `{match {case =>}}`" $ do
      let (Right e) = parseExpr "{match {case =>}}"
      let ms = MultiStack Map.empty
      eval' e `shouldBe` ms

    it "evals `0 {match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "0 {match {case 0 => 1} {case => drop 0}}"
      let (Right vs) = parseValStack "1"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `1 {match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "1 {match {case 0 => 1} {case => drop 0}}"
      let (Right vs) = parseValStack "0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 0 {match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "0 0 {match {case 0 0 => 1} {case => drop drop 0}}"
      let (Right vs) = parseValStack "1"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 1 {match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "0 1 {match {case 0 0 => 1} {case => drop drop 0}}"
      let (Right vs) = parseValStack "0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval' e `shouldBe` ms

    it "evals `0 1 swap`" $ do
      let ([], env) = addFnDefs emptyEnv [swap]
      let (Right e) = parseExpr "0 1 swap"
      let (Right vs) = parseValStack "1 0"
      let ms = MultiStack Map.empty
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv env) ["$"] e ms `shouldBe` ms'

    it "evals `{$c 0 1 swap}`" $ do
      let ([], env) = addFnDefs emptyEnv [swap]
      let (Right e) = parseExpr "{$c 0 1 swap}"
      let (Right vs) = parseValStack "1 0"
      let ms = MultiStack Map.empty
      let ms' = MultiStack (Map.singleton "$c" vs)
      eval (toEvalEnv env) ["$"] e ms `shouldBe` ms'

    it "evals `{$a 0 1 swap}`" $ do
      let ([], env) = addFnDefs emptyEnv [swap]
      let (Right e) = parseExpr "{$a 0 1 swap}"
      let (Right vs) = parseValStack "1 0"
      let ms = MultiStack Map.empty
      let ms' = MultiStack (Map.singleton "$a" vs)
      eval (toEvalEnv env) ["$"] e ms `shouldBe` ms'

    it "evals fib" $ do
      let ([], env) = addFnDefs emptyEnv [swap, fib]
      let (Right e) = parseExpr "0 fib"
      let (Right vs) = parseValStack "0"
      let ms = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms

      let (Right e) = parseExpr "1 fib"
      let (Right vs) = parseValStack "1"
      let ms = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms

      let (Right e) = parseExpr "6 fib"
      let (Right vs) = parseValStack "8"
      let ms = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms

    it "evals `B0 {match {case B0 => B1} {case B1 => B0}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "B0 {match {case B0 => B1} {case B1 => B0}}"
      let (Right vs) = parseValStack "B1"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `{$a B0 {match {case B0 => B1} {case B1 => B0}}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "{$a B0 {match {case B0 => B1} {case B1 => B0}}}"
      let (Right vs) = parseValStack "B1"
      let ms' = MultiStack (Map.singleton "$a" vs)
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `0 True Pair {match {case Pair => }}`" $ do
      let (Right d) = parseDataDef "{data v0 v1 Pair {cons v0 v1 Pair}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "0 True Pair {match {case Pair => }}"
      let (Right vs) = parseValStack "0 True"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z Z`" $ do
      let (Right d) = parseDataDef "{data Nat {cons Z} {cons Nat S}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "Z Z"
      let (Right vs) = parseValStack "Z Z"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals recursive Nat pattern (1)" $ do
      let (Right d) = parseDataDef "{data Nat {cons Z} {cons Nat S}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "Z S {match {case (Z S) => }}"
      let ms = MultiStack Map.empty
      eval (toEvalEnv env) ["$"] e ms `shouldBe` ms

    it "evals recursive Nat pattern (2)" $ do
      let (Right d) = parseDataDef "{data Nat {cons Z} {cons Nat S}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "Z S S {match {case (S S) => }}"
      let (Right vs) = parseValStack "Z"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals recursive Bit Stack pattern (1)" $ do
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

    it "evals recursive Bit Stack pattern (2)" $ do
      let (Right dBit) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let (Right dStack) =
            parseDataDef
              "{data v0 Stack {cons Empty} {cons (v0 Stack) v0 Push}}"
      let ([], env) = addDataDefs emptyEnv [dBit, dStack]
      let (Right e) =
            parseExpr
              "Empty B1 Push B0 Push {match {case (Push B0 Push) => }}"
      let (Right vs) = parseValStack "Empty B1"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv env) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z {match {case Z => }}`" $ do
      let (Right e) = parseExpr "Z {match {case Z => }}"
      let ms' = MultiStack Map.empty
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z S {match {case S => }}`" $ do
      let (Right e) = parseExpr "Z S {match {case S => }}"
      let (Right vs) = parseValStack "Z"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z S {match {case (Z S) => }}`" $ do
      let (Right e) = parseExpr "Z S {match {case (Z S) => }}"
      let ms' = MultiStack Map.empty
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z S S {match {case (S S) => }}`" $ do
      let (Right e) = parseExpr "Z S S {match {case (S S) => }}"
      let (Right vs) = parseValStack "Z"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty Z Push {match {case Push =>}}`" $ do
      let (Right e) = parseExpr "Empty Z Push {match {case Push =>}}"
      let (Right vs) = parseValStack "Empty Z"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty B0 Push {match {case (B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "Empty B0 Push {match {case (B0 Push) =>}}"
      let (Right vs) = parseValStack "Empty"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty B0 Push {match {case (Empty B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "Empty B0 Push {match {case (Empty B0 Push) =>}}"
      let ms' = MultiStack Map.empty
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty B1 Push B0 Push {match {case (Push B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "Empty B1 Push B0 Push {match {case (Push B0 Push) =>}}"
      let (Right vs) = parseValStack "Empty B1"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty B1 Push B0 Push {match {case ((B1 Push) B0 Push) =>}}`" $ do
      let (Right e) = parseExpr "Empty B1 Push B0 Push {match {case ((B1 Push) B0 Push) =>}}"
      let (Right vs) = parseValStack "Empty"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Z S Empty B0 Push Pair {match {case (S Push Pair) =>}}`" $ do
      let (Right e) = parseExpr "Z S Empty B0 Push Pair {match {case (S Push Pair) =>}}"
      let (Right vs) = parseValStack "Z Empty B0"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty Z Push Empty B0 Push Pair {match {case (Push Push Pair) =>}}`" $ do
      let (Right e) = parseExpr "Empty Z Push Empty B0 Push Pair {match {case (Push Push Pair) =>}}"
      let (Right vs) = parseValStack "Empty Z Empty B0"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "evals `Empty Z Push Empty B0 Push Pair {match {case (Push _ Pair) =>}}`" $ do
      let (Right e) = parseExpr "Empty Z Push Empty B0 Push Pair {match {case (Push _ Pair) =>}}"
      let (Right vs) = parseValStack "Empty Z (Empty B0 Push)"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "infers `Z (Z S) nat_add`" $ do
      let (Right e) = parseExpr "Z (Z S) nat_add"
      let (Right vs) = parseValStack "(Z S)"
      let ms' = MultiStack (Map.singleton "$" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

    it "infers `{$a Z (Z S) nat_add}`" $ do
      let (Right e) = parseExpr "{$a Z (Z S) nat_add}"
      let (Right vs) = parseValStack "(Z S)"
      let ms' = MultiStack (Map.singleton "$a" vs)
      eval (toEvalEnv testEnv) ["$"] e (MultiStack Map.empty) `shouldBe` ms'

  describe "evalWithFuel" $ do
    it "stops at 0 fuel" $ do
      let (Right e) = parseExpr "0"
      let ms = MultiStack Map.empty
      evalWithFuel emptyEvalEnv ["$"] (0, e, ms) `shouldBe` (0, e, ms)

    it "allows negative fuel" $ do
      let (Right e) = parseExpr "0"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseValStack "0"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel emptyEvalEnv ["$"] (-1, e, ms) `shouldBe` (-2, e', ms')

    it "evals `0 [clone] apply`" $ do
      let (Right e) = parseExpr "0 [clone] apply"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseValStack "0 0"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel emptyEvalEnv ["$"] (4, e, ms) `shouldBe` (0, e', ms')

    it "evals `0 1 $a<- $b<- $a-> $b->`" $ do
      let (Right e) = parseExpr "0 1 $a<- $b<- $a-> $b->"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseValStack "1 0"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel emptyEvalEnv ["$"] (6, e, ms) `shouldBe` (0, e', ms')

    it "evals `{match {case =>}}`" $ do
      let (Right e) = parseExpr "{match {case =>}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let ms' = MultiStack Map.empty
      evalWithFuel emptyEvalEnv ["$"] (1, e, ms) `shouldBe` (0, e', ms')

    it "evals `0 {match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "0 {match {case 0 => 1} {case => drop 0}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseValStack "1"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel emptyEvalEnv ["$"] (3, e, ms) `shouldBe` (0, e', ms')

    it "evals `1 {match {case 0 => 1} {case => drop 0}}`" $ do
      let (Right e) = parseExpr "1 {match {case 0 => 1} {case => drop 0}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseValStack "0"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel emptyEvalEnv ["$"] (5, e, ms) `shouldBe` (0, e', ms')

    it "evals `0 0 {match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "0 0 {match {case 0 0 => 1} {case => drop drop 0}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseValStack "1"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel emptyEvalEnv ["$"] (4, e, ms) `shouldBe` (0, e', ms')

    it "evals `0 1 {match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      let (Right e) = parseExpr "0 1 {match {case 0 0 => 1} {case => drop drop 0}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseValStack "0"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel emptyEvalEnv ["$"] (7, e, ms) `shouldBe` (0, e', ms')

    it "evals `fib`" $ do
      let ([], env) = addFnDefs emptyEnv [swap, fib]
          evalFib n =
            let (Right e) = parseExpr (show n ++ " fib")
                ms = MultiStack Map.empty
                e' = ECompose []
             in evalWithFuel (toEvalEnv env) ["$"] (-1, e, ms)
          n `inSteps` steps =
            let (Right vs) = parseValStack (show n)
             in (-1 - steps, ECompose [], MultiStack (Map.singleton "$" vs))

      evalFib 0 `shouldBe` 0 `inSteps` 4
      evalFib 1 `shouldBe` 1 `inSteps` 5
      evalFib 2 `shouldBe` 1 `inSteps` 23
      evalFib 3 `shouldBe` 2 `inSteps` 42
      evalFib 4 `shouldBe` 3 `inSteps` 79
      evalFib 5 `shouldBe` 5 `inSteps` 135
      evalFib 6 `shouldBe` 8 `inSteps` 228
      evalFib 7 `shouldBe` 13 `inSteps` 377
      evalFib 8 `shouldBe` 21 `inSteps` 619
      evalFib 9 `shouldBe` 34 `inSteps` 1010

    it "evals tail recursive fib" $ do
      let ([], env) = addFnDefs emptyEnv [fastFib, _fastFib]
          evalFastFib n =
            let (Right e) = parseExpr (show n ++ " fib")
                ms = MultiStack Map.empty
                e' = ECompose []
             in evalWithFuel (toEvalEnv env) ["$"] (-1, e, ms)
          n `inSteps` steps =
            let (Right vs) = parseValStack (show n)
             in (-1 - steps, ECompose [], MultiStack (Map.singleton "$" vs))

      evalFastFib 0 `shouldBe` 0 `inSteps` 8
      evalFastFib 1 `shouldBe` 1 `inSteps` 17
      evalFastFib 2 `shouldBe` 1 `inSteps` 26
      evalFastFib 3 `shouldBe` 2 `inSteps` 35
      evalFastFib 4 `shouldBe` 3 `inSteps` 44
      evalFastFib 5 `shouldBe` 5 `inSteps` 53
      evalFastFib 6 `shouldBe` 8 `inSteps` 62
      evalFastFib 7 `shouldBe` 13 `inSteps` 71
      evalFastFib 8 `shouldBe` 21 `inSteps` 80
      evalFastFib 9 `shouldBe` 34 `inSteps` 89

    it "evals `B0 {match {case B0 => B1} {case B1 => B0}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "B0 {match {case B0 => B1} {case B1 => B0}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseValStack "B1"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel (toEvalEnv env) ["$"] (3, e, ms) `shouldBe` (0, e', ms')

    it "evals `{$a B0 {match {case B0 => B1} {case B1 => B0}}}`" $ do
      let (Right d) = parseDataDef "{data Bit {cons B0} {cons B1}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "{$a B0 {match {case B0 => B1} {case B1 => B0}}}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseValStack "B1"
      let ms' = MultiStack (Map.singleton "$a" vs)
      evalWithFuel (toEvalEnv env) ["$"] (3, e, ms) `shouldBe` (0, e', ms')

    it "evals `0 True Pair {match {case Pair => }}`" $ do
      let (Right d) = parseDataDef "{data v0 v1 Pair {cons v0 v1 Pair}}"
      let ([], env) = addDataDefs emptyEnv [d]
      let (Right e) = parseExpr "0 True Pair {match {case Pair => }}"
      let ms = MultiStack Map.empty
      let e' = ECompose []
      let (Right vs) = parseValStack "0 True"
      let ms' = MultiStack (Map.singleton "$" vs)
      evalWithFuel (toEvalEnv env) ["$"] (4, e, ms) `shouldBe` (0, e', ms')

swapSrc = "{fn swap => $a<- $b<- $a-> $b->}"

(Right swap) = parseFnDef swapSrc

fibSrc =
  unlines
    [ "{fn fib => {match",
      "  {case 0 => 0}",
      "  {case 1 => 1}",
      "  {case => clone 1 sub fib swap 2 sub fib add}",
      "}}"
    ]

(Right fib) = parseFnDef fibSrc

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
