-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.ParseSpec (spec) where

import Data.Either.Combinators
import qualified Data.Map as Map
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Parse
import Test.Hspec
import Text.Parsec.Error
import Text.Parsec.Pos
import Prelude hiding (drop, (*))

[tv0, tv1] = map TypeVar [0 .. 1]

[v0, v1, v2] = map (TVar . TypeVar) [0 .. 2]

[clone, drop, quote, compose, apply] =
  map EIntrinsic [IClone, IDrop, IQuote, ICompose, IApply]

spec :: Spec
spec = do
  describe "parseExpr" $ do
    it "parses ``" $ do
      parseExpr "" `shouldBe` Right (ECompose [])

    it "parses `()`" $ do
      parseExpr "()" `shouldBe` Right (ECompose [])

    it "parses `push`" $ do
      parseExpr "push"
        `shouldBe` Right (EIntrinsic IPush)

    it "parses `pop`" $ do
      parseExpr "pop"
        `shouldBe` Right (EIntrinsic IPop)

    it "parses `clone`" $ do
      parseExpr "clone" `shouldBe` Right clone

    it "parses `drop`" $ do
      parseExpr "drop" `shouldBe` Right drop

    it "parses `quote`" $ do
      parseExpr "quote" `shouldBe` Right quote

    it "parses `compose`" $ do
      parseExpr "compose" `shouldBe` Right compose

    it "parses `apply`" $ do
      parseExpr "apply" `shouldBe` Right apply

    it "parses `clone drop quote compose apply`" $ do
      parseExpr "clone drop quote compose apply"
        `shouldBe` Right (ECompose [clone, drop, quote, compose, apply])

    it "parses `[clone] apply`" $ do
      parseExpr "[clone] apply"
        `shouldBe` Right (ECompose [EQuote clone, apply])

    it "parses `[[clone] apply]`" $ do
      parseExpr "[[clone] apply]"
        `shouldBe` Right (EQuote (ECompose [EQuote clone, apply]))

    it "parses `(clone drop) clone`" $ do
      parseExpr "(clone drop) clone"
        `shouldBe` Right (ECompose [ECompose [clone, drop], clone])

    it "parses `clone (drop clone)`" $ do
      parseExpr "clone (drop clone)"
        `shouldBe` Right (ECompose [clone, ECompose [drop, clone]])

    it "parses `foo`" $ do
      parseExpr "foo"
        `shouldBe` Right (ECall "foo")

    it "parses `{$a drop}`" $ do
      parseExpr "{$a drop}"
        `shouldBe` Right (EContext "$a" (EIntrinsic IDrop))

    it "parses `{$_Ab12_C drop}`" $ do
      parseExpr "{$_Ab12_C drop}"
        `shouldBe` Right (EContext "$_Ab12_C" (EIntrinsic IDrop))

    it "fails on `{$1234 drop}`" $ do
      let (Left err) = parseExpr "{$1234 drop}"
      let pos = errorPos err
      sourceLine pos `shouldBe` 1
      sourceColumn pos `shouldBe` 3

    it "parses `$a<-`" $ do
      parseExpr "$a<-"
        `shouldBe` Right (EContext "$a" (EIntrinsic IPush))

    it "parses `$a->`" $ do
      parseExpr "$a->"
        `shouldBe` Right (EContext "$a" (EIntrinsic IPop))

    it "parses `False`" $ do
      parseExpr "False"
        `shouldBe` Right (ECons "False")

    it "parses `True`" $ do
      parseExpr "True"
        `shouldBe` Right (ECons "True")

    it "parses `{$a False}`" $ do
      parseExpr "{$a False}"
        `shouldBe` Right (EContext "$a" (ECons "False"))

    it "fails on `{match }`" $ do
      let (Left err) = parseExpr "{match }"
      let pos = errorPos err
      sourceLine pos `shouldBe` 1
      sourceColumn pos `shouldBe` 8

    it "parses `{match {case =>}}`" $ do
      parseExpr "{match {case =>}}"
        `shouldBe` Right (EMatch [(defaultMultiStack Empty, ECompose [])])

    it "parses `{match {case Z => Z S} {case => drop Z}}`" $ do
      parseExpr "{match {case Z => Z S} {case => drop Z}}"
        `shouldBe` Right
          ( EMatch
              [ (defaultMultiStack (Empty :*: PCons Empty "Z"), ECompose [ECons "Z", ECons "S"]),
                (defaultMultiStack Empty, ECompose [drop, ECons "Z"])
              ]
          )

    it "parses `{match {case Z Z => Z S} {case => drop drop Z}}`" $ do
      parseExpr "{match {case Z Z => Z S} {case => drop drop Z}}"
        `shouldBe` Right
          ( EMatch
              [ ( defaultMultiStack (Empty :*: PCons Empty "Z" :*: PCons Empty "Z"),
                  ECompose [ECons "Z", ECons "S"]
                ),
                (defaultMultiStack Empty, ECompose [drop, drop, ECons "Z"])
              ]
          )

    it "parses `drop2`" $ do
      parseExpr "drop2"
        `shouldBe` Right (ECall "drop2")

    it "parses `{spread $a $a $b}`" $ do
      parseExpr "{spread $a $a $b}"
        `shouldBe` parseExpr "($s1<- $s2<- $s3<-) ($s3-> $a<-) ($s2-> $a<-) ($s1-> $b<-)"

    it "parses `{collect $a $a $b}`" $ do
      parseExpr "{collect $a $a $b}"
        `shouldBe` parseExpr "($b-> $s1<-) ($a-> $s2<-) ($a-> $s3<-) ($s3-> $s2-> $s1->)"

    it "parses `B0`" $ do
      parseExpr "B0" `shouldBe` Right (ECons "B0")

    it "parses `{match {case B0 => }}`" $ do
      parseExpr "{match {case B0 => }}"
        `shouldBe` Right
          ( EMatch
              [ (defaultMultiStack (Empty :*: PCons Empty "B0"), ECompose [])
              ]
          )

    it "parses `{match {case (Z S) => }}`" $ do
      let pZ = PCons Empty "Z"
      let pS n = PCons (Empty :*: n) "S"
      parseExpr "{match {case (Z S) => }}"
        `shouldBe` Right (EMatch [(defaultMultiStack (Empty :*: pS pZ), ECompose [])])

    it "parses `{match {case _ => }}`" $ do
      parseExpr "{match {case _ => }}"
        `shouldBe` Right (EMatch [(defaultMultiStack (Empty :*: PWild), ECompose [])])

    it "parses `{match {case (Z _ Pair) => }}`" $ do
      let pPair a b = PCons (Empty :*: a :*: b) "Pair"
      let pZ = PCons Empty "Z"
      parseExpr "{match {case (Z _ Pair) => }}"
        `shouldBe` Right
          ( EMatch
              [ (defaultMultiStack (Empty :*: pPair pZ PWild), ECompose [])
              ]
          )

    it "parses `{match {case {$tmp S} =>}}`" $ do
      let msp =
            MultiStack
              ( Map.fromList
                  [ ("$tmp", Empty :*: PCons Empty "S")
                  ]
              )
      parseExpr "{match {case {$tmp S} =>}}"
        `shouldBe` Right (EMatch [(msp, ECompose [])])

    it "parses `{match {case {$tmp S S} =>}}`" $ do
      let msp =
            MultiStack
              ( Map.fromList
                  [ ("$tmp", Empty :*: PCons Empty "S" :*: PCons Empty "S")
                  ]
              )
      parseExpr "{match {case {$tmp S S} =>}}"
        `shouldBe` Right (EMatch [(msp, ECompose [])])

    it "parses `{match {case {$a S} {$b S} =>}}`" $ do
      let msp =
            MultiStack
              ( Map.fromList
                  [ ("$a", Empty :*: PCons Empty "S"),
                    ("$b", Empty :*: PCons Empty "S")
                  ]
              )
      parseExpr "{match {case {$a S} {$b S} =>}}"
        `shouldBe` Right (EMatch [(msp, ECompose [])])

  describe "parseValStack" $ do
    it "parses `[clone] [drop] Z`" $ do
      mapRight fromStack (parseValStack "[clone] [drop] Z")
        `shouldBe` Right [VQuote clone, VQuote drop, VCons Empty "Z"]

    it "parses `B0`" $ do
      mapRight fromStack (parseValStack "B0")
        `shouldBe` Right [VCons Empty "B0"]

    it "parses `(Empty B0 Push)`" $ do
      mapRight fromStack (parseValStack "(Empty B0 Push)")
        `shouldBe` Right [VCons (toStack [VCons Empty "Empty", VCons Empty "B0"]) "Push"]

    it "parses `((Empty B0 A) Foo B)`" $ do
      mapRight fromStack (parseValStack "((Empty B0 A) Foo B)")
        `shouldBe` Right
          [ VCons
              ( toStack
                  [ VCons
                      ( toStack
                          [ VCons Empty "Empty",
                            VCons Empty "B0"
                          ]
                      )
                      "A",
                    VCons Empty "Foo"
                  ]
              )
              "B"
          ]

    it "parses `(((v0 Stack) Stack) Foo)`" $ do
      mapRight fromStack (parseValStack "(((B0 Stack) Stack) Foo)")
        `shouldBe` Right
          [ VCons
              ( Empty
                  :*: VCons
                    ( Empty
                        :*: VCons
                          ( Empty :*: VCons Empty "B0"
                          )
                          "Stack"
                    )
                    "Stack"
              )
              "Foo"
          ]

  describe "parseFnDef" $ do
    it "parses `{fn drop2 => drop drop}`" $ do
      let (Right e) = parseExpr "drop drop"
      parseFnDef "{fn drop2 => drop drop}"
        `shouldBe` Right (FnDef "drop2" e)

    it "parses fib" $ do
      let fibExprSrc =
            unlines
              [ "{match",
                "  {case Z => Z}",
                "  {case (Z S) => (Z S)}",
                "  {case => clone nat_decr fib swap nat_decr nat_decr fib nat_add}",
                "}"
              ]
      let fibSrc = "{fn fib => " ++ fibExprSrc ++ "}"
      let (Right e) = parseExpr fibExprSrc
      parseFnDef fibSrc
        `shouldBe` Right (FnDef "fib" e)

    it "parses tail recursive fib" $ do
      let fibExprSrc = "{$a Z} {$b (Z S)} _fib"
      let fibSrc = "{fn fib => " ++ fibExprSrc ++ "}"
      let (Right e) = parseExpr fibExprSrc
      parseFnDef fibSrc
        `shouldBe` Right (FnDef "fib" e)

      let _fibExprSrc =
            unlines
              [ "  {match",
                "  {case Z => {$b drop} $a->}",
                "  {case => nat_decr {$b clone pop $a-> nat_add} $a<- _fib}",
                "  }"
              ]
      let _fibSrc = "{fn _fib => " ++ _fibExprSrc ++ "}"
      let (Right e) = parseExpr _fibExprSrc
      parseFnDef _fibSrc
        `shouldBe` Right (FnDef "_fib" e)

  describe "parseDataDef" $ do
    it "parses `{data Bit {cons B0} {cons B1}}`" $ do
      parseDataDef "{data Bit {cons B0} {cons B1}}"
        `shouldBe` Right
          ( DataDef
              []
              "Bit"
              [ ConsDef [] "B0",
                ConsDef [] "B1"
              ]
          )

    it "parses `{data NewU32 {cons U32 NewU32}}`" $ do
      parseDataDef "{data NewU32 {cons U32 NewU32}}"
        `shouldBe` Right
          ( DataDef
              []
              "NewU32"
              [ConsDef [TCons [] "U32"] "NewU32"]
          )

    it "parses `{data v0 v1 Pair {cons v0 v1 Pair}}`" $ do
      parseDataDef "{data v0 v1 Pair {cons v0 v1 Pair}}"
        `shouldBe` Right
          ( DataDef
              [tv0, tv1]
              "Pair"
              [ ConsDef [v0, v1] "Pair"
              ]
          )

    it "parses `{data v0 v1 SwapPair {cons v1 v0 SwapPair}}`" $ do
      parseDataDef "{data v0 v1 SwapPair {cons v1 v0 SwapPair}}"
        `shouldBe` Right
          ( DataDef
              [tv0, tv1]
              "SwapPair"
              [ ConsDef [v1, v0] "SwapPair"
              ]
          )

    it "parses `{data v0 Stack {cons Empty} {cons (v0 Stack) v0 Push}}`" $ do
      parseDataDef "{data v0 Stack {cons Empty} {cons (v0 Stack) v0 Push}}"
        `shouldBe` Right
          ( DataDef
              [tv0]
              "Stack"
              [ ConsDef [] "Empty",
                ConsDef [TCons [v0] "Stack", v0] "Push"
              ]
          )

    it "parses `{data v0 Foo {cons ((v0 Stack) Stack) Foo}}`" $ do
      parseDataDef "{data v0 Foo {cons ((v0 Stack) Stack) Foo}}"
        `shouldBe` Right
          ( DataDef
              [tv0]
              "Foo"
              [ ConsDef [TCons [TCons [v0] "Stack"] "Stack"] "Foo"
              ]
          )

  describe "parseType" $ do
    it "parses `v0`" $ do
      parseType "v0" `shouldBe` Right v0

    it "parses `v0 v1`" $ do
      parseType "v0 v1" `shouldBe` Right (v0 * v1)

    it "parses `v0 v1 v2`" $ do
      parseType "v0 v1 v2" `shouldBe` Right (v0 * v1 * v2)

    it "parses `(forall v0 . v0 -> v0)`" $ do
      parseType "(forall v0 . v0 -> v0)"
        `shouldBe` Right (forall' [v0] (v0 --> v0))

    it "parses `(forall v0 v1 . v0 (forall . v0 -> v1) -> v1)`" $ do
      parseType "(forall v0 v1 . v0 (forall . v0 -> v1) -> v1)"
        `shouldBe` Right (forall' [v0, v1] (v0 * forall' [] (v0 --> v1) --> v1))

    it "parses `Bit`" $ do
      parseType "Bit" `shouldBe` Right (TCons [] "Bit")

    it "parses `(v0 Stack)`" $ do
      parseType "(v0 Stack)" `shouldBe` Right (TCons [v0] "Stack")

    it "parses `(forall v0 v1 . v0 (v1 Stack) -> v0 (Bit Stack) Bit)`" $ do
      let tStack t = TCons [t] "Stack"
      let tBit = TCons [] "Bit"
      parseType "(forall v0 v1 . v0 (v1 Stack) -> v0 (Bit Stack) Bit)"
        `shouldBe` Right
          ( forall'
              [v0, v1]
              (v0 * tStack v1 --> v0 * tStack tBit * tBit)
          )

  describe "parseDefs" $ do
    it "parses data and fn defs" $ do
      let drop2Src = "{fn drop2 => drop drop}"
      let boolSrc = "{data Bool {cons False} {cons True}}"
      let src = unlines [drop2Src, boolSrc]
      let (Right drop2Def) = parseFnDef drop2Src
      let (Right boolDef) = parseDataDef boolSrc
      parseDefs src
        `shouldBe` Right ([boolDef], [drop2Def])
