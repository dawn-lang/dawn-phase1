-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Parse
  ( dataDef,
    expr,
    fnDef,
    keyword,
    parseDataDef,
    parseDefs,
    parseExpr,
    parseFnDef,
    parseType,
    parseValStack,
  )
where

import Control.Monad (fail, void, when)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Utils
import Text.Parsec hiding (Empty)
import Text.Parsec.String
import Prelude hiding (drop)

parseDefs :: String -> Either ParseError ([DataDef], [FnDef])
parseDefs = parse (skipMany space *> defs <* eof) ""
  where
    defs = do
      ds <- many def
      let folder (Left ddef) (ddefs, fdefs) = (ddef : ddefs, fdefs)
          folder (Right fdef) (ddefs, fdefs) = (ddefs, fdef : fdefs)
      return (foldr folder ([], []) ds)
    def = try (Left <$> dataDef) <|> try (Right <$> fnDef)

parseType :: String -> Either ParseError Type
parseType = parse (skipMany space *> type' <* eof) ""

parseDataDef :: String -> Either ParseError DataDef
parseDataDef = parse (skipMany space *> dataDef <* eof) ""

parseFnDef :: String -> Either ParseError FnDef
parseFnDef = parse (skipMany space *> fnDef <* eof) ""

parseExpr :: String -> Either ParseError Expr
parseExpr = parse (skipMany space *> expr <* eof) ""

parseValStack :: String -> Either ParseError (Stack Val)
parseValStack = parse (skipMany space *> (toStack <$> many val) <* eof) ""

type' :: Parser Type
type' = stackTypes <$> many1 nonProdType

nonProdType :: Parser Type
nonProdType = varType <|> simpleConsType <|> betweenParens (fnType <|> consType)

fnType :: Parser Type
fnType = TFn <$> univQuants <*> multiIO

univQuants :: Parser UnivQuants
univQuants = keyword "forall" *> (Set.fromList <$> many typeVar) <* symbol "."

multiIO :: Parser MultiIO
multiIO =
  betweenBraces undefined -- TODO
    <|> Map.singleton "$" <$> singleIO

singleIO :: Parser (Type, Type)
singleIO = (,) <$> type' <*> (symbol "->" *> type')

dataDef :: Parser DataDef
dataDef =
  betweenBraces
    ( DataDef <$> (keyword "data" *> many typeVar) <*> consId <*> many consDef
    )

consDef :: Parser ConsDef
consDef = betweenBraces (ConsDef <$> (keyword "cons" *> consTypeArgs) <*> consId)

simpleConsType :: Parser Type
simpleConsType = lexeme (TCons [] <$> consId)

consType :: Parser Type
consType = lexeme (TCons <$> consTypeArgs <*> consId)

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
varType = lexeme (TVar <$> typeVar)

typeVar :: Parser TypeVar
typeVar = TypeVar . fromInteger <$> (char 'v' *> integer)

fnDef :: Parser FnDef
fnDef = betweenBraces (FnDef <$> (keyword "fn" *> fnId) <*> (symbol "=>" *> expr))

expr :: Parser Expr
expr =
  fromExprSeq
    <$> many
      ( bracedExpr <|> groupedExpr <|> quotedExpr <|> sugarExpr
          <|> intrinsicExpr
          <|> consExpr
          <|> callExpr
      )

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

matchExprCase :: Parser (Stack Pattern, Expr)
matchExprCase =
  betweenBraces
    ( (,) <$> (keyword "case" *> (toStack <$> many pat)) <*> (symbol "=>" *> expr)
    )

pat :: Parser Pattern
pat = simpleConsPat <|> betweenParens consPat <|> wildPat

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

keyword s = void $ lexeme (string s <* notFollowedBy identChar)

symbol s = void $ lexeme (string s)

lexeme p = p <* (skip <|> eof)

skip = void $ many space
