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
  es <- many (grouped <|> quoted <|> sugar <|> intrinsic)
  case es of
    [] -> return (ECompose [])
    [e] -> return e
    es -> return (ECompose es)

grouped = between (symbol '(') (symbol ')') (context <|> expr)

context = EContext <$> (stackId <* symbol ':') <*> expr

quoted = between (symbol '[') (symbol ']') (EQuote <$> expr)

sugar =
  EContext <$> stackId_
    <*> ( (keyword "<-" >> return (EIntrinsic IPush))
            <|> (keyword "->" >> return (EIntrinsic IPop))
        )

intrinsic =
  try push <|> try pop <|> try clone <|> try drop <|> try quote <|> try compose <|> try apply

push = keyword "push" >> return (EIntrinsic IPush)

pop = keyword "pop" >> return (EIntrinsic IPop)

clone = keyword "clone" >> return (EIntrinsic IClone)

drop = keyword "drop" >> return (EIntrinsic IDrop)

quote = keyword "quote" >> return (EIntrinsic IQuote)

compose = keyword "compose" >> return (EIntrinsic ICompose)

apply = keyword "apply" >> return (EIntrinsic IApply)

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
