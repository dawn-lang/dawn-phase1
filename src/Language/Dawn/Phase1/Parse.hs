-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Language.Dawn.Phase1.Parse
  ( dataDef,
    element,
    expr,
    fnDef,
    keyword,
    parseDataDef,
    parseElements,
    parseElementsFromFile,
    parseExpr,
    parseFnDecl,
    parseFnDef,
    parseFnType,
    parseInclude,
    parsePattern,
    parseProdType,
    parseShorthandFnType,
    parseTestDef,
    parseValMultiStack,
    parseValStack,
  )
where

import Control.Monad (fail, void, when)
import Data.Bits
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core hiding ((*))
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Utils
import Numeric
import Text.Parsec hiding (Empty)
import Text.Parsec.String
import Prelude hiding (drop)

parseElementsFromFile :: FilePath -> IO (Either ParseError [Element])
parseElementsFromFile = parseFromFile (skip *> elements <* eof)

parseElements :: String -> Either ParseError [Element]
parseElements = parse (skip *> elements <* eof) ""

parseInclude :: String -> Either ParseError Include
parseInclude = parse (skip *> include <* eof) ""

parseProdType :: String -> Either ParseError Type
parseProdType = parse (skip *> prodType <* eof) ""

parseShorthandFnType :: String -> Either ParseError ShorthandFnType
parseShorthandFnType = parse (skip *> shorthandFnType <* eof) ""

parseFnType :: String -> Either ParseError Type
parseFnType = parse (skip *> fnType <* eof) ""

parseDataDef :: String -> Either ParseError DataDef
parseDataDef = parse (skip *> dataDef <* eof) ""

parseFnDecl :: String -> Either ParseError FnDecl
parseFnDecl = parse (skip *> fnDecl <* eof) ""

parseFnDef :: String -> Either ParseError FnDef
parseFnDef = parse (skip *> fnDef <* eof) ""

parseTestDef :: String -> Either ParseError TestDef
parseTestDef = parse (skip *> testDef <* eof) ""

parseExpr :: String -> Either ParseError Expr
parseExpr = parse (skip *> expr <* eof) ""

parsePattern :: String -> Either ParseError Pattern
parsePattern = parse (skip *> pat <* eof) ""

parseValStack :: String -> Either ParseError (Stack Val)
parseValStack = parse (skip *> valStack <* eof) ""

parseValMultiStack :: String -> Either ParseError (MultiStack Val)
parseValMultiStack = parse (skip *> valMultiStack <* eof) ""

elements :: Parser [Element]
elements = many element

element :: Parser Element
element =
  betweenBraces
    ( includeElement <|> dataDefElement <|> fnElement <|> testDefElement
    )

includeElement :: Parser Element
includeElement =
  EInclude <$> (Include <$> (keyword "include" *> stringLiteral))

dataDefElement :: Parser Element
dataDefElement =
  EDataDef <$> (DataDef <$> (keyword "data" *> many typeVar) <*> consId <*> many consDef)

fnElement :: Parser Element
fnElement = do
  fid <- keyword "fn" *> fnId
  EFnDecl . FnDecl fid <$> (symbol "::" *> fnDeclType)
    <|> EFnDef . FnDef fid <$> (symbol "=>" *> expr)

testDefElement :: Parser Element
testDefElement =
  ETestDef <$> (TestDef <$> (keyword "test" *> stringLiteral) <*> (symbol "=>" *> expr))

include :: Parser Include
include = Include <$> betweenBraces (keyword "include" *> stringLiteral)

stringLiteral :: Parser String
stringLiteral = lexeme (between (char '"') (char '"') (many stringLiteralChar))

stringLiteralChar :: Parser Char
stringLiteralChar = escapedChar <|> noneOf "\0\n\r\""

escapedChar :: Parser Char
escapedChar =
  char '\\'
    *> ( escapedHex
           <|> (char '0' >> return '\0')
           <|> (char 'n' >> return '\n')
           <|> (char 'r' >> return '\r')
           <|> (char 't' >> return '\t')
           <|> (char '\\' >> return '\\')
           <|> (char '\'' >> return '\'')
           <|> (char '"' >> return '"')
       )
  where
    escapedHex :: Parser Char
    escapedHex = do
      _ <- char 'x'
      h <- hexDigit
      l <- hexDigit
      let [(i, "")] = readHex [h, l]
      return (toEnum i)

byteLiteral :: Parser Int
byteLiteral = lexeme (between (string "b'") (char '\'') byteLiteralChar)

byteLiteralChar :: Parser Int
byteLiteralChar = fromEnum <$> escapedChar <|> fromEnum <$> noneOf "\0\n\r\'"

bitToBitConsId :: Int -> ConsId
bitToBitConsId i = if (i .&. 1) == 0 then "B0" else "B1"

byteToBitConsIds :: Int -> [ConsId]
byteToBitConsIds i =
  let bitIndexes = reverse [0 .. 7]
      bitValues = map (\offset -> i `shiftR` offset) bitIndexes
   in map bitToBitConsId bitValues

toByteECons :: Int -> Expr
toByteECons i = ECompose (map ECons (byteToBitConsIds i) ++ [ECons "Byte"])

toBytePCons :: Int -> Pattern
toBytePCons i = PCons (toStack (map (PCons Empty) (byteToBitConsIds i))) "Byte"

fnType :: Parser Type
fnType =
  fromShorthandFnType <$> try shorthandFnType
    <|> fullFnType

shorthandFnType :: Parser ShorthandFnType
shorthandFnType = (,) <$> many singleType <*> (symbol "->" *> many singleType)

fullFnType :: Parser Type
fullFnType = TFn <$> univQuants <*> multiIO

prodType :: Parser Type
prodType = stackTypes <$> many1 singleType

singleType :: Parser Type
singleType = varType <|> simpleConsType <|> betweenParens (fullFnType <|> consType)

univQuants :: Parser UnivQuants
univQuants = keyword "forall" *> (Set.fromList <$> many typeVar) <* symbol "."

multiIO :: Parser MultiIO
multiIO =
  Map.fromList <$> many1 (betweenBraces ((,) <$> stackId <*> singleIO))
    <|> Map.singleton "$" <$> singleIO

singleIO :: Parser (Type, Type)
singleIO = (,) <$> prodType <*> (symbol "->" *> prodType)

dataDef :: Parser DataDef
dataDef =
  betweenBraces
    ( DataDef <$> (keyword "data" *> many typeVar) <*> consId <*> many consDef
    )

consDef :: Parser ConsDef
consDef = betweenBraces (ConsDef <$> (keyword "cons" *> consTypeArgs) <*> consId)

simpleConsType :: Parser Type
simpleConsType = TCons [] <$> consId

consType :: Parser Type
consType = TCons <$> consTypeArgs <*> consId

consTypeArgs :: Parser [Type]
consTypeArgs = do
  argsAndConsId <- lookAhead (try (many1 consTypeArg))
  case last argsAndConsId of
    TCons [] cid -> count (length argsAndConsId - 1) consTypeArg
    _ -> fail "expected consId"
  where
    consTypeArg = simpleConsType <|> varType <|> betweenParens consTypeArg'
    consTypeArg' = try consType <|> varType <|> betweenParens consTypeArg'

varType :: Parser Type
varType = TVar <$> typeVar

typeVar :: Parser TypeVar
typeVar = TypeVar . fromInteger <$> (char 'v' *> integer)

fnDecl :: Parser FnDecl
fnDecl = betweenBraces (FnDecl <$> (keyword "fn" *> fnId) <*> (symbol "::" *> fnDeclType))

fnDeclType :: Parser Type
fnDeclType =
  try fnType
    <|> (\ts -> fromShorthandFnType ([], ts)) <$> many prodType

fnDef :: Parser FnDef
fnDef = betweenBraces (FnDef <$> (keyword "fn" *> fnId) <*> (symbol "=>" *> expr))

testDef :: Parser TestDef
testDef =
  betweenBraces
    ( TestDef <$> (keyword "test" *> stringLiteral) <*> (symbol "=>" *> expr)
    )

expr :: Parser Expr
expr =
  fromExprSeq
    <$> many
      ( bracedExpr <|> groupedExpr <|> quotedExpr <|> sugarExpr
          <|> intrinsicExpr
          <|> try (toByteECons <$> byteLiteral)
          <|> consExpr
          <|> callExpr
      )

valMultiStack :: Parser (MultiStack Val)
valMultiStack =
  MultiStack
    <$> ( Map.fromList <$> many1 (betweenBraces ((,) <$> stackId <*> valStack))
            <|> Map.singleton "$" <$> valStack
            <|> return Map.empty
        )

valStack :: Parser (Stack Val)
valStack = toStack <$> many val

val :: Parser Val
val = quotedVal <|> simpleConsVal <|> betweenParens consVal

simpleConsVal :: Parser Val
simpleConsVal = VCons Empty <$> consId

consVal :: Parser Val
consVal = do
  args <- many val
  let (args', args'') = splitAt (length args - 1) args
  case args'' of
    [VCons Empty cid] -> return (VCons (toStack args') cid)
    _ -> fail "expected consId"

false = try (keyword "False") >> return False

true = try (keyword "True") >> return True

integer :: Parser Integer
integer = read <$> lexeme (many1 digit)

betweenParens = between (symbol "(") (symbol ")")

betweenBraces = between (symbol "{") (symbol "}")

bracedExpr =
  betweenBraces
    ( EContext <$> stackId <*> expr
        <|> EMatch <$> (keyword "match" *> many1 matchExprCase)
        <|> desugarSpread <$> (keyword "spread" *> many1 stackId)
        <|> desugarCollect <$> (keyword "collect" *> many1 stackId)
    )

matchExprCase :: Parser (MultiStack Pattern, Expr)
matchExprCase =
  betweenBraces
    ( (,) <$> (keyword "case" *> patMultiStack) <*> (symbol "=>" *> expr)
    )

patMultiStack :: Parser (MultiStack Pattern)
patMultiStack =
  MultiStack
    <$> ( Map.fromList <$> many1 (betweenBraces ((,) <$> stackId <*> patStack))
            <|> Map.singleton "$" <$> patStack
        )

patStack :: Parser (Stack Pattern)
patStack = toStack <$> many pat

pat :: Parser Pattern
pat =
  try (toBytePCons <$> byteLiteral)
    <|> simpleConsPat
    <|> betweenParens consPat
    <|> wildPat

simpleConsPat :: Parser Pattern
simpleConsPat = PCons Empty <$> consId

consPat :: Parser Pattern
consPat = do
  args <- many pat
  let (args', args'') = splitAt (length args - 1) args
  case args'' of
    [PCons Empty cid] -> return (PCons (toStack args') cid)
    _ -> fail "expected consId"

wildPat :: Parser Pattern
wildPat = keyword "_" >> return PWild

desugarSpread :: [StackId] -> Expr
desugarSpread dstStackIds =
  let tmpStackIds = map (\i -> "$s" ++ show i) [1 .. (length dstStackIds)]
      e = ECompose (map ePushTo tmpStackIds)
      folder (tmp, dst) es = ECompose [ePopFrom tmp, ePushTo dst] : es
      es = foldr folder [] (zip (reverse tmpStackIds) dstStackIds)
   in ECompose (e : es)

desugarCollect :: [StackId] -> Expr
desugarCollect srcStackIds =
  let tmpStackIds = map (\i -> "$s" ++ show i) [1 .. (length srcStackIds)]
      folder (src, tmp) es = ECompose [ePopFrom src, ePushTo tmp] : es
      es = foldr folder [] (zip (reverse srcStackIds) tmpStackIds)
      e = ECompose (map ePopFrom (reverse tmpStackIds))
   in ECompose (es ++ [e])

ePushTo s = EContext s (EIntrinsic IPush)

ePopFrom s = EContext s (EIntrinsic IPop)

groupedExpr = betweenParens expr

quotedExpr = between (symbol "[") (symbol "]") (EQuote <$> expr)

quotedVal = between (symbol "[") (symbol "]") (VQuote <$> expr)

sugarExpr = sugar EContext EIntrinsic

sugar contextCons intrinsicCons =
  contextCons <$> stackId_
    <*> ( (symbol "<-" >> return (intrinsicCons IPush))
            <|> (symbol "->" >> return (intrinsicCons IPop))
        )

intrinsicExpr = intrinsic EIntrinsic

intrinsic cons =
  try (keyword "push" >> return (cons IPush))
    <|> try (keyword "pop" >> return (cons IPop))
    <|> try (keyword "clone" >> return (cons IClone))
    <|> try (keyword "drop" >> return (cons IDrop))
    <|> try (keyword "quote" >> return (cons IQuote))
    <|> try (keyword "compose" >> return (cons ICompose))
    <|> try (keyword "apply" >> return (cons IApply))

consExpr = ECons <$> consId

callExpr = ECall <$> fnId

stackId = lexeme stackId_

consId = lexeme ((:) <$> consIdFirstChar <*> many consIdChar)
  where
    consIdFirstChar = upper
    consIdChar = letter <|> char '_' <|> digit

fnId = lexeme ((:) <$> fnIdFirstChar <*> many fnIdChar)
  where
    fnIdFirstChar = lower <|> char '_'
    fnIdChar = letter <|> char '_' <|> digit

stackId_ = (:) <$> char '$' <*> ident_

ident_ = (:) <$> identFirstChar <*> many identChar

identFirstChar = letter <|> char '_'

identChar = letter <|> char '_' <|> digit

notChar :: Char -> Parser Char
notChar c = satisfy (/= c)

lineComment = string "--" *> many (notChar '\n') <* optional (char '\n')

skip = void (many (void space <|> try (void lineComment)))

lexeme p = p <* skip

keyword s = void $ lexeme (string s <* notFollowedBy identChar)

symbol s = void $ lexeme (string s)
