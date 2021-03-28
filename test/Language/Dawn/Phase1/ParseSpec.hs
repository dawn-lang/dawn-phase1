-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.ParseSpec (spec) where

import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Parse
import Test.Hspec
import Text.Parsec.Error
import Text.Parsec.Pos
import Prelude hiding (drop, (*))

[tv0, tv1, tv2, tv3, tv4, tv5, _, _, tv8] = map TypeVar [0 .. 8]

[v0, v1, v2, v3, v4, v5, v6, v7, v8] = map (TVar . TypeVar) [0 .. 8]

[clone, drop, quote, compose, apply] =
  map EIntrinsic [IClone, IDrop, IQuote, ICompose, IApply]

pBool n = PLit (LBool n)

eBool n = ELit (LBool n)

pU32 n = PLit (LU32 n)

eU32 n = ELit (LU32 n)

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

    it "parses `and`" $ do
      parseExpr "and" `shouldBe` Right (EIntrinsic IAnd)

    it "parses `or`" $ do
      parseExpr "or" `shouldBe` Right (EIntrinsic IOr)

    it "parses `not`" $ do
      parseExpr "not" `shouldBe` Right (EIntrinsic INot)

    it "parses `xor`" $ do
      parseExpr "xor" `shouldBe` Right (EIntrinsic IXor)

    it "parses `incr`" $ do
      parseExpr "incr" `shouldBe` Right (EIntrinsic IIncr)

    it "parses `decr`" $ do
      parseExpr "decr" `shouldBe` Right (EIntrinsic IDecr)

    it "parses `add`" $ do
      parseExpr "add" `shouldBe` Right (EIntrinsic IAdd)

    it "parses `sub`" $ do
      parseExpr "sub" `shouldBe` Right (EIntrinsic ISub)

    it "parses `bit_and`" $ do
      parseExpr "bit_and" `shouldBe` Right (EIntrinsic IBitAnd)

    it "parses `bit_or`" $ do
      parseExpr "bit_or" `shouldBe` Right (EIntrinsic IBitOr)

    it "parses `bit_not`" $ do
      parseExpr "bit_not" `shouldBe` Right (EIntrinsic IBitNot)

    it "parses `bit_xor`" $ do
      parseExpr "bit_xor" `shouldBe` Right (EIntrinsic IBitXor)

    it "parses `shl`" $ do
      parseExpr "shl" `shouldBe` Right (EIntrinsic IShl)

    it "parses `shr`" $ do
      parseExpr "shr" `shouldBe` Right (EIntrinsic IShr)

    it "parses `eq`" $ do
      parseExpr "eq" `shouldBe` Right (EIntrinsic IEq)

    it "parses `lt`" $ do
      parseExpr "lt" `shouldBe` Right (EIntrinsic ILt)

    it "parses `gt`" $ do
      parseExpr "gt" `shouldBe` Right (EIntrinsic IGt)

    it "parses `lteq`" $ do
      parseExpr "lteq" `shouldBe` Right (EIntrinsic ILteq)

    it "parses `gteq`" $ do
      parseExpr "gteq" `shouldBe` Right (EIntrinsic IGteq)

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
        `shouldBe` Right (ELit (LBool False))

    it "parses `True`" $ do
      parseExpr "True"
        `shouldBe` Right (ELit (LBool True))

    it "parses `123`" $ do
      parseExpr "123"
        `shouldBe` Right (ELit (LU32 123))

    it "fails `999999999999`" $ do
      let (Left err) = parseExpr "999999999999"
      let pos = errorPos err
      sourceLine pos `shouldBe` 1
      sourceColumn pos `shouldBe` 13

    it "parses `{$a False}`" $ do
      parseExpr "{$a False}"
        `shouldBe` Right (EContext "$a" (ELit (LBool False)))

    it "parses `{$a 123}`" $ do
      parseExpr "{$a 123}"
        `shouldBe` Right (EContext "$a" (ELit (LU32 123)))

    it "fails on `{match }`" $ do
      let (Left err) = parseExpr "{match }"
      let pos = errorPos err
      sourceLine pos `shouldBe` 1
      sourceColumn pos `shouldBe` 8

    it "parses `{match {case =>}}`" $ do
      parseExpr "{match {case =>}}"
        `shouldBe` Right (EMatch [(PEmpty, ECompose [])])

    it "parses `{match {case 0 => 1} {case => drop 0}}`" $ do
      parseExpr "{match {case 0 => 1} {case => drop 0}}"
        `shouldBe` Right
          ( EMatch
              [ (pU32 0, eU32 1),
                (PEmpty, ECompose [drop, eU32 0])
              ]
          )

    it "parses `{match {case 0 0 => 1} {case => drop drop 0}}`" $ do
      parseExpr "{match {case 0 0 => 1} {case => drop drop 0}}"
        `shouldBe` Right
          ( EMatch
              [ (PProd (pU32 0) (pU32 0), eU32 1),
                (PEmpty, ECompose [drop, drop, eU32 0])
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

  describe "parseVal" $ do
    it "parses `[clone] [drop] 0`" $ do
      -- Note that the values are in reverse, so that `eval` can
      -- easily pattern match on the top of the stack.
      parseVals "[clone] [drop] 0"
        `shouldBe` Right [VLit (LU32 0), VQuote drop, VQuote clone]

    it "parses `B0`" $ do
      parseVals "B0"
        `shouldBe` Right [VCons [] "B0"]

    it "parses `(Empty B0 Push)`" $ do
      parseVals "(Empty B0 Push)"
        `shouldBe` Right [VCons [VCons [] "Empty", VCons [] "B0"] "Push"]

  describe "parseFnDef `and`" $ do
    it "parses `{fn drop2 => drop drop}`" $ do
      let (Right e) = parseExpr "drop drop"
      parseFnDef "{fn drop2 => drop drop}"
        `shouldBe` Right (FnDef "drop2" e)

    it "parses fib" $ do
      let fibExprSrc =
            unlines
              [ "{match",
                "  {case 0 => 0}",
                "  {case 1 => 1}",
                "  {case => clone 1 sub fib swap 2 sub fib add}",
                "}"
              ]
      let fibSrc = "{fn fib => " ++ fibExprSrc ++ "}"
      let (Right e) = parseExpr fibExprSrc
      parseFnDef fibSrc
        `shouldBe` Right (FnDef "fib" e)

    it "parses tail recursive fib" $ do
      let fibExprSrc = "{$a 0} {$b 1} _fib"
      let fibSrc = "{fn fib => " ++ fibExprSrc ++ "}"
      let (Right e) = parseExpr fibExprSrc
      parseFnDef fibSrc
        `shouldBe` Right (FnDef "fib" e)

      let _fibExprSrc =
            unlines
              [ "  {match",
                "  {case 0 => {$b drop} $a->}",
                "  {case => decr {$b clone pop $a-> add} $a<- _fib}",
                "  }"
              ]
      let _fibSrc = "{fn _fib => " ++ _fibExprSrc ++ "}"
      let (Right e) = parseExpr _fibExprSrc
      parseFnDef _fibSrc
        `shouldBe` Right (FnDef "_fib" e)

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

    it "parses `B0`" $ do
      parseExpr "B0" `shouldBe` Right (ECons "B0")

    it "parses `{match {case B0 => }}`" $ do
      parseExpr "{match {case B0 => }}"
        `shouldBe` Right (EMatch [(PCons "B0", ECompose [])])
