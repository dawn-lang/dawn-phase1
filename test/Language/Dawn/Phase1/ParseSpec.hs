-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Language.Dawn.Phase1.ParseSpec (spec) where

import Data.Either.Combinators
import qualified Data.Map as Map
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.Utils
import Test.Hspec
import Text.Parsec.Error
import Text.Parsec.Pos
import Prelude hiding (drop, (*))

[tv0, tv1] = map TypeVar [0 .. 1]

[v0, v1, v2] = map (TVar . TypeVar) [0 .. 2]

[clone, drop, quote, compose, apply] =
  map EIntrinsic [IClone, IDrop, IQuote, ICompose, IApply]

tBool = TCons [] "Bool"

tNat = TCons [] "Nat"

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

    it "parses `{$ drop}`" $ do
      parseExpr "{$ drop}"
        `shouldBe` Right (EContext "$" (EIntrinsic IDrop))

    it "parses `{$a drop}`" $ do
      parseExpr "{$a drop}"
        `shouldBe` Right (EContext "$a" (EIntrinsic IDrop))

    it "parses `{$_Ab12_C drop}`" $ do
      parseExpr "{$_Ab12_C drop}"
        `shouldBe` Right (EContext "$_Ab12_C" (EIntrinsic IDrop))

    it "parses `{$1234 drop}`" $ do
      parseExpr "{$1234 drop}"
        `shouldBe` Right (EContext "$1234" (EIntrinsic IDrop))

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

    it "parses `bool_and`" $ do
      parseExpr "bool_and" `shouldBe` Right (ECall "bool_and")

    it "parses `b'a'`" $ do
      let (Right e) = parseExpr "(B0 B1 B1 B0 B0 B0 B0 B1 Byte)"
      parseExpr "b'a'" `shouldBe` Right e
    
    it "parses `b'\\x7F'`"$ do
      let (Right e) = parseExpr "(B0 B1 B1 B1 B1 B1 B1 B1 Byte)"
      parseExpr "b'\\x7F'" `shouldBe` Right e

    it "parses `b'\\0'`" $ do
      let (Right e) = parseExpr "(B0 B0 B0 B0 B0 B0 B0 B0 Byte)"
      parseExpr "b'\\0'" `shouldBe` Right e

    it "parses `b'\\n'`"$ do
      let (Right e) = parseExpr "(B0 B0 B0 B0 B1 B0 B1 B0 Byte)"
      parseExpr "b'\\n'" `shouldBe` Right e

    it "parses `b'\\r'`"$ do
      let (Right e) = parseExpr "(B0 B0 B0 B0 B1 B1 B0 B1 Byte)"
      parseExpr "b'\\r'" `shouldBe` Right e

    it "parses `b'\\t'`"$ do
      let (Right e) = parseExpr "(B0 B0 B0 B0 B1 B0 B0 B1 Byte)"
      parseExpr "b'\\t'" `shouldBe` Right e

    it "parses `b'\\\\'`"$ do
      let (Right e) = parseExpr "(B0 B1 B0 B1 B1 B1 B0 B0 Byte)"
      parseExpr "b'\\\\'" `shouldBe` Right e

    it "parses `b'\\\''`"$ do
      let (Right e) = parseExpr "(B0 B0 B1 B0 B0 B1 B1 B1 Byte)"
      parseExpr "b'\\\''" `shouldBe` Right e

    it "parses `b'\\\"'`"$ do
      let (Right e) = parseExpr "(B0 B0 B1 B0 B0 B0 B1 B0 Byte)"
      parseExpr "b'\\\"'" `shouldBe` Right e

  describe "parsePattern" $ do
    it "parses `b'a'`" $ do
      let (Right e) = parsePattern "(B0 B1 B1 B0 B0 B0 B0 B1 Byte)"
      parsePattern "b'a'" `shouldBe` Right e
    
    it "parses `b'\\x7F'`"$ do
      let (Right e) = parsePattern "(B0 B1 B1 B1 B1 B1 B1 B1 Byte)"
      parsePattern "b'\\x7F'" `shouldBe` Right e

    it "parses `b'\\0'`" $ do
      let (Right e) = parsePattern "(B0 B0 B0 B0 B0 B0 B0 B0 Byte)"
      parsePattern "b'\\0'" `shouldBe` Right e

    it "parses `b'\\n'`"$ do
      let (Right e) = parsePattern "(B0 B0 B0 B0 B1 B0 B1 B0 Byte)"
      parsePattern "b'\\n'" `shouldBe` Right e

    it "parses `b'\\r'`"$ do
      let (Right e) = parsePattern "(B0 B0 B0 B0 B1 B1 B0 B1 Byte)"
      parsePattern "b'\\r'" `shouldBe` Right e

    it "parses `b'\\t'`"$ do
      let (Right e) = parsePattern "(B0 B0 B0 B0 B1 B0 B0 B1 Byte)"
      parsePattern "b'\\t'" `shouldBe` Right e

    it "parses `b'\\\\'`"$ do
      let (Right e) = parsePattern "(B0 B1 B0 B1 B1 B1 B0 B0 Byte)"
      parsePattern "b'\\\\'" `shouldBe` Right e

    it "parses `b'\\\''`"$ do
      let (Right e) = parsePattern "(B0 B0 B1 B0 B0 B1 B1 B1 Byte)"
      parsePattern "b'\\\''" `shouldBe` Right e

    it "parses `b'\\\"'`"$ do
      let (Right e) = parsePattern "(B0 B0 B1 B0 B0 B0 B1 B0 Byte)"
      parsePattern "b'\\\"'" `shouldBe` Right e

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

  describe "parseValMultiStack" $ do
    it "parses `Z`" $ do
      let (Right s) = parseValStack "Z"
      parseValMultiStack "Z"
        `shouldBe` Right (MultiStack (Map.fromList [("$", s)]))

    it "parses `{$a Z} {$b Z}`" $ do
      let (Right s) = parseValStack "Z"
      parseValMultiStack "{$a Z} {$b Z}"
        `shouldBe` Right (MultiStack (Map.fromList [("$a", s), ("$b", s)]))

  describe "parseFnDecl" $ do
    it "parses `{fn drop2 :: forall v0 v1 v2 . v0 v1 v2 -> v0}`" $ do
      let (Right t) = parseFnType "forall v0 v1 v2 . v0 v1 v2 -> v0"
      parseFnDecl "{fn drop2 :: forall v0 v1 v2 . v0 v1 v2 -> v0}"
        `shouldBe` Right (FnDecl "drop2" t)

    it "parses `{fn drop2 :: v1 v2 -> }`" $ do
      let (Right t) = parseFnType "v1 v2 ->"
      parseFnDecl "{fn drop2 :: v1 v2 -> }"
        `shouldBe` Right (FnDecl "drop2" t)

    it "parses `{fn zero :: Nat}`" $ do
      let (Right t) = parseProdType "Nat"
      let t' = fromShorthandFnType ([], [t])
      parseFnDecl "{fn zero :: Nat}"
        `shouldBe` Right (FnDecl "zero" t')

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

  describe "parseProdType" $ do
    it "parses `v0`" $ do
      parseProdType "v0" `shouldBe` Right v0

    it "parses `v0 v1`" $ do
      parseProdType "v0 v1" `shouldBe` Right (v0 * v1)

    it "parses `v0 v1 v2`" $ do
      parseProdType "v0 v1 v2" `shouldBe` Right (v0 * v1 * v2)

    it "parses `Bit`" $ do
      parseProdType "Bit" `shouldBe` Right (TCons [] "Bit")

    it "parses `(v0 Stack)`" $ do
      parseProdType "(v0 Stack)" `shouldBe` Right (TCons [v0] "Stack")

  describe "parseFnType" $ do
    it "parses `(forall v0 . v0 -> v0)`" $ do
      parseFnType "forall v0 . v0 -> v0"
        `shouldBe` Right (forall' [v0] (v0 --> v0))

    it "parses `(forall v0 v1 . v0 (forall . v0 -> v1) -> v1)`" $ do
      parseFnType "forall v0 v1 . v0 (forall . v0 -> v1) -> v1"
        `shouldBe` Right (forall' [v0, v1] (v0 * forall' [] (v0 --> v1) --> v1))

    it "parses `(forall v0 v1 . v0 (v1 Stack) -> v0 (Bit Stack) Bit)`" $ do
      let tStack t = TCons [t] "Stack"
      let tBit = TCons [] "Bit"
      parseFnType "forall v0 v1 . v0 (v1 Stack) -> v0 (Bit Stack) Bit"
        `shouldBe` Right
          ( forall'
              [v0, v1]
              (v0 * tStack v1 --> v0 * tStack tBit * tBit)
          )

    it "parses `(forall v0 . {$tmp v0 Bit -> v0 Bit})`" $ do
      let tBit = TCons [] "Bit"
      parseFnType "forall v0 . {$tmp v0 Bit -> v0 Bit}"
        `shouldBe` Right (forall [v0] ("$tmp" $: v0 * tBit --> v0 * tBit))

    it "parses `(forall v0 v1 v2 . {$a v0 v1 -> v0 v2} {$b v0 v2 -> v0 v1})`" $ do
      parseFnType "forall v0 v1 v2 . {$a v0 v1 -> v0 v2} {$b v0 v2 -> v0 v1}"
        `shouldBe` Right
          ( forall
              [v0, v1, v2]
              ("$a" $: v0 * v1 --> v0 * v2 $. "$b" $: v0 * v2 --> v0 * v1)
          )

  describe "parseShorthandFnType" $ do
    it "parses ` -> `" $ do
      parseShorthandFnType " -> "
        `shouldBe` Right ([], [])

    it "parses `Nat -> Bool`" $ do
      parseShorthandFnType "Nat -> Bool"
        `shouldBe` Right ([tNat], [tBool])

    it "parses `v1 -> v1 v1`" $ do
      parseShorthandFnType "v1 -> v1 v1"
        `shouldBe` Right ([v1], [v1, v1])

  describe "parseStackId" $ do
    it "parses `$`" $ do
      parseStackId "$" `shouldBe` Right "$"

    it "parses `$0`" $ do
      parseStackId "$0" `shouldBe` Right "$0"

    it "parses `$_`" $ do
      parseStackId "$_" `shouldBe` Right "$_"

    it "parses `$a`" $ do
      parseStackId "$a" `shouldBe` Right "$a"

    it "parses `$A`" $ do
      parseStackId "$A" `shouldBe` Right "$A"

    it "parses `$_0123456789abcABC_`" $ do
      parseStackId "$_0123456789abcABC_" `shouldBe` Right "$_0123456789abcABC_"

    it "parses `$$`" $ do
      parseStackId "$$" `shouldBe` Right "$$"

    it "parses `$$1`" $ do
      parseStackId "$$1" `shouldBe` Right "$$1"

  describe "parseInclude" $ do
    it "parses `{include \"src/prelude.dn\"}`" $ do
      parseInclude "{include \"src/prelude.dn\"}"
        `shouldBe` Right (Include "src/prelude.dn")

  describe "parseTestDef" $ do
    it "parses `{test \"this is a test description\" => Z {match {case Z =>}}}`" $ do
      let (Right e) = parseExpr "Z {match {case Z =>}}"
      parseTestDef "{test \"this is a test description\" => Z {match {case Z =>}}}"
        `shouldBe` Right (TestDef "this is a test description" e)

  describe "parseElements" $ do
    it "parses test definitions" $ do
      let testDefSrc = "{test \"this is a test description\" => Z {match {case Z =>}}}"
      let (Right testDef) = parseTestDef testDefSrc
      parseElements testDefSrc `shouldBe` Right [ETestDef testDef]

    it "parses all declarations and definitions" $ do
      let drop2DeclSrc = "{fn drop2 :: forall v0 v1 v2 . v0 v1 v2 -> v0}"
      let drop2DefSrc = "{fn drop2 => drop drop}"
      let boolDefSrc = "{data Bool {cons False} {cons True}}"
      let testDefSrc = "{test \"this is a test description\" => Z {match {case Z =>}}}"
      let src = unlines [drop2DeclSrc, drop2DefSrc, boolDefSrc, testDefSrc]
      let (Right drop2Decl) = parseFnDecl drop2DeclSrc
      let (Right drop2Def) = parseFnDef drop2DefSrc
      let (Right boolDef) = parseDataDef boolDefSrc
      let (Right testDef) = parseTestDef testDefSrc
      parseElements src
        `shouldBe` Right
          [ EFnDecl drop2Decl,
            EFnDef drop2Def,
            EDataDef boolDef,
            ETestDef testDef
          ]

    it "parses `{include \"test/Test1.dn\"}`" $ do
      parseElements "{include \"test/Test1.dn\"}"
        `shouldBe` Right [EInclude (Include "test/Test1.dn")]

    it "skips comments" $ do
      let src = "-- this is a comment\n{include \"test/Test1.dn\"}"
      parseElements src `shouldBe` Right [EInclude (Include "test/Test1.dn")]

    it "skips comment on last line" $ do
      let src = "-- this is a comment on the last line"
      parseElements src `shouldBe` Right []

    it "skips copyright header" $ do
      let src =
            unlines
              [ "-- Copyright (c) 2021 Scott J Maddox",
                "--",
                "-- This Source Code Form is subject to the terms of the Mozilla Public",
                "-- License, v. 2.0. If a copy of the MPL was not distributed with this",
                "-- file, You can obtain one at https://mozilla.org/MPL/2.0/.",
                ""
              ]
      parseElements src `shouldBe` Right []

    it "parses contents of Test1.dn" $ do
      let src =
            unlines
              [ "-- Copyright (c) 2021 Scott J Maddox",
                "--",
                "-- This Source Code Form is subject to the terms of the Mozilla Public",
                "-- License, v. 2.0. If a copy of the MPL was not distributed with this",
                "-- file, You can obtain one at https://mozilla.org/MPL/2.0/.",
                "",
                "{data Test1 {cons Test1}}",
                "{fn test1 :: Test1}",
                "{fn test1 => Test1}",
                ""
              ]
      let (Right elems) =
            parseElements
              ( unlines
                  [ "{data Test1 {cons Test1}}",
                    "{fn test1 :: Test1}",
                    "{fn test1 => Test1}",
                    ""
                  ]
              )
      parseElements src `shouldBe` Right elems

  describe "parseElementsFromFile" $ do
    it "parses Test1.dn" $ do
      result <- parseElementsFromFile "test/Test1.dn"
      let (Right elems) =
            parseElements
              ( unlines
                  [ "{data Test1 {cons Test1}}",
                    "{fn test1 :: Test1}",
                    "{fn test1 => Test1}",
                    ""
                  ]
              )
      result `shouldBe` Right elems
