-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Parse
  ( expr,
    fnDef,
    keyword,
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

parseFnDef :: String -> Either ParseError FnDef
parseFnDef = parse (skipMany space *> fnDef <* eof) ""

parseExpr :: String -> Either ParseError Expr
parseExpr = parse (skipMany space *> expr <* eof) ""

parseVals :: String -> Either ParseError [Val]
parseVals = parse (skipMany space *> vals <* eof) ""

fnDef :: Parser FnDef
fnDef = betweenBraces (FnDef <$> (keyword "fn" *> fnId) <*> (symbol "=" *> expr))

expr :: Parser Expr
expr =
  fromExprSeq
    <$> many
      ( literalExpr <|> bracedExpr <|> groupedExpr <|> quotedExpr <|> sugarExpr
          <|> intrinsicExpr
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

betweenBraces = between (symbol "{") (symbol "}")

bracedExpr =
  betweenBraces
    ( EContext <$> stackId <*> expr
        <|> EMatch <$> (keyword "match" *> many1 matchExprCase)
    )

matchExprCase :: Parser (Pattern, Expr)
matchExprCase = betweenBraces ((,) <$> (keyword "case" *> pattern') <*> (symbol "=>" *> expr))

pattern' :: Parser Pattern
pattern' =
  try (PProd <$> literalPattern <*> literalPattern)
    <|> try literalPattern
    <|> return PEmpty

groupedExpr = between (symbol "(") (symbol ")") expr

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

callExpr = ECall <$> fnId

stackId = lexeme stackId_

fnId = lexeme ident_

stackId_ = (:) <$> char '$' <*> ident_

ident_ = (:) <$> identFirstChar <*> many identChar

identFirstChar = letter <|> char '_'

identChar = letter <|> char '_' <|> digit

keyword s = void $ lexeme (string s <* notFollowedBy identChar)

symbol s = void $ lexeme (string s)

lexeme p = p <* (skip <|> eof)

skip = void $ many space
