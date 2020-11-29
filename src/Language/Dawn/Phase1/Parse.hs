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
parseExpr = parse (expr <* eof) ""

expr :: Parser Expr
expr = skipMany space *> composed

composed = do
  es <- many1 (quoted <|> intrinsic)
  case es of
    [e] -> return e
    es -> return (ECompose es)

quoted = between (symbol '[') (symbol ']') (EQuote <$> expr)

intrinsic = try clone <|> drop <|> swap <|> quote <|> compose <|> apply

clone = keyword "clone" >> return (EIntrinsic IClone)

drop = keyword "drop" >> return (EIntrinsic IDrop)

swap = keyword "swap" >> return (EIntrinsic ISwap)

quote = keyword "quote" >> return (EIntrinsic IQuote)

compose = keyword "compose" >> return (EIntrinsic ICompose)

apply = keyword "apply" >> return (EIntrinsic IApply)

keyword s = void $ lexeme (string s)

symbol c = void $ lexeme (char c)

lexeme p = p <* (skip <|> eof)

skip = void $ many space
