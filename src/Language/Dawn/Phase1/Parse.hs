-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Parse
  ( expr,
    fnDef,
    keyword,
    parseDataDef,
    parseExpr,
    parseFnDef,
    parseVals,
  )
where

import Control.Monad (fail, void, when)
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Utils
import Text.Parsec
import Text.Parsec.String
import Prelude hiding (drop)

parseDataDef :: String -> Either ParseError DataDef
parseDataDef = parse (skipMany space *> dataDef <* eof) ""

parseFnDef :: String -> Either ParseError FnDef
parseFnDef = parse (skipMany space *> fnDef <* eof) ""

parseExpr :: String -> Either ParseError Expr
parseExpr = parse (skipMany space *> expr <* eof) ""

parseVals :: String -> Either ParseError [Val]
parseVals = parse (skipMany space *> vals <* eof) ""

dataDef :: Parser DataDef
dataDef =
  betweenBraces
    ( DataDef <$> (keyword "data" *> many typeVar) <*> consId <*> many consDef
    )

consDef :: Parser ConsDef
consDef = betweenBraces innerConsDef
  where
    innerConsDef = do
      _ <- keyword "cons"
      args <- many consDefArgs
      let (args', args'') = splitAt (length args - 1) args
      case args'' of
        [TCons [] cid] -> return (ConsDef args' cid)
        _ -> fail "expected consId"

consDefArgs :: Parser Type
consDefArgs = simpleConsType <|> varType <|> betweenParens consDefArgs'
  where
    consDefArgs' = try consType <|> varType <|> betweenParens consDefArgs'

simpleConsType :: Parser Type
simpleConsType = lexeme (TCons [] <$> consId)

consType :: Parser Type
consType = lexeme (TCons <$> many varType <*> consId)

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
      ( literalExpr <|> bracedExpr <|> groupedExpr <|> quotedExpr <|> sugarExpr
          <|> intrinsicExpr
          <|> consExpr
          <|> callExpr
      )

vals :: Parser [Val]
vals = reverse <$> many (literalVal <|> quotedVal)

literalExpr = ELit <$> literal

literalPattern = PLit <$> literal

literalVal = VLit <$> literal

literal = boolLit <|> u32Lit

boolLit :: Parser Literal
boolLit = LBool <$> (false <|> true)

false = try (keyword "False") >> return False

true = try (keyword "True") >> return True

u32Lit :: Parser Literal
u32Lit = do
  integer <- integer
  let i = fromInteger integer
  let integer' = toInteger i
  when (integer /= integer') (fail "literal overflow")
  return (LU32 i)

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

matchExprCase :: Parser (Pattern, Expr)
matchExprCase = betweenBraces ((,) <$> (keyword "case" *> pattern') <*> (symbol "=>" *> expr))

pattern' :: Parser Pattern
pattern' =
  try (PProd <$> literalOrConsPattern <*> literalOrConsPattern)
    <|> try literalPattern
    <|> try consPattern
    <|> return PEmpty
  where
    literalOrConsPattern = try literalPattern <|> consPattern

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
    <|> try (keyword "and" >> return (cons IAnd))
    <|> try (keyword "or" >> return (cons IOr))
    <|> try (keyword "not" >> return (cons INot))
    <|> try (keyword "xor" >> return (cons IXor))
    <|> try (keyword "incr" >> return (cons IIncr))
    <|> try (keyword "decr" >> return (cons IDecr))
    <|> try (keyword "add" >> return (cons IAdd))
    <|> try (keyword "sub" >> return (cons ISub))
    <|> try (keyword "bit_and" >> return (cons IBitAnd))
    <|> try (keyword "bit_or" >> return (cons IBitOr))
    <|> try (keyword "bit_not" >> return (cons IBitNot))
    <|> try (keyword "bit_xor" >> return (cons IBitXor))
    <|> try (keyword "shl" >> return (cons IShl))
    <|> try (keyword "shr" >> return (cons IShr))
    <|> try (keyword "eq" >> return (cons IEq))
    <|> try (keyword "lt" >> return (cons ILt))
    <|> try (keyword "gt" >> return (cons IGt))
    <|> try (keyword "lteq" >> return (cons ILteq))
    <|> try (keyword "gteq" >> return (cons IGteq))

consExpr = ECons <$> consId

consPattern = PCons <$> consId

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
