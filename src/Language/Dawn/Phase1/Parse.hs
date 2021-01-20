-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Parse (parseExpr) where

import Control.Monad (void)
import Language.Dawn.Phase1.Core
import Text.Parsec
import Text.Parsec.String
import Prelude hiding (drop)

parseExpr :: String -> Either ParseError Expr
parseExpr = parse (skipMany space *> expr <* eof) ""

expr :: Parser Expr
expr = do
  es <- many (literal <|> grouped <|> quoted <|> sugar <|> intrinsic)
  case es of
    [] -> return (ECompose [])
    [e] -> return e
    es -> return (ECompose es)

literal :: Parser Expr
literal = ELit . LU32 . fromInteger <$> integer_literal

integer_literal :: Parser Integer
integer_literal = read <$> lexeme (many1 digit)

grouped = between (symbol '(') (symbol ')') (context <|> expr)

context = EContext <$> (stackId <* symbol ':') <*> expr

quoted = between (symbol '[') (symbol ']') (EQuote <$> expr)

sugar =
  EContext <$> stackId_
    <*> ( (keyword "<-" >> return (EIntrinsic IPush))
            <|> (keyword "->" >> return (EIntrinsic IPop))
        )

intrinsic =
  try (keyword "push" >> return (EIntrinsic IPush))
    <|> try (keyword "pop" >> return (EIntrinsic IPop))
    <|> try (keyword "clone" >> return (EIntrinsic IClone))
    <|> try (keyword "drop" >> return (EIntrinsic IDrop))
    <|> try (keyword "quote" >> return (EIntrinsic IQuote))
    <|> try (keyword "compose" >> return (EIntrinsic ICompose))
    <|> try (keyword "apply" >> return (EIntrinsic IApply))
    <|> try (keyword "eqz" >> return (EIntrinsic IEqz))
    <|> try (keyword "add" >> return (EIntrinsic IAdd))
    <|> try (keyword "sub" >> return (EIntrinsic ISub))
    <|> try (keyword "bit_and" >> return (EIntrinsic IBitAnd))
    <|> try (keyword "bit_or" >> return (EIntrinsic IBitOr))
    <|> try (keyword "bit_xor" >> return (EIntrinsic IBitXor))
    <|> try (keyword "shl" >> return (EIntrinsic IShl))
    <|> try (keyword "shr" >> return (EIntrinsic IShr))

stackId = lexeme stackId_

stackId_ = (:) <$> char '$' <*> ident_

ident_ = (:) <$> firstChar <*> many nonFirstChar
  where
    firstChar = letter <|> char '_'
    nonFirstChar = digit <|> firstChar

keyword s = void $ lexeme (string s)

symbol c = void $ lexeme (char c)

lexeme p = p <* (skip <|> eof)

skip = void $ many space
