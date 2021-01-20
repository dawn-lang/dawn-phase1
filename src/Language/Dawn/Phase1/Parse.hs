-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Parse (parseExpr, parseVal) where

import Control.Monad (void)
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Utils
import Text.Parsec
import Text.Parsec.String
import Prelude hiding (drop)

parseExpr :: String -> Either ParseError Expr
parseExpr = parse (skipMany space *> expr <* eof) ""

parseVal :: String -> Either ParseError Val
parseVal = parse (skipMany space *> val <* eof) ""

expr :: Parser Expr
expr =
  fromExprSeq
    <$> many
      ( literalExpr <|> groupedExpr <|> quotedExpr <|> sugarExpr <|> intrinsicExpr
      )

val :: Parser Val
val =
  fromValSeq
    <$> many
      ( literalVal <|> groupedVal <|> quotedVal <|> sugarVal <|> intrinsicVal
      )

literalExpr = literal ELit

literalVal = literal VLit

literal litCons = litCons . LU32 . fromInteger <$> integer_literal

integer_literal = read <$> lexeme (many1 digit)

groupedExpr = between (symbol '(') (symbol ')') (contextExpr <|> expr)

groupedVal = between (symbol '(') (symbol ')') (contextVal <|> val)

contextExpr = EContext <$> (stackId <* symbol ':') <*> expr

contextVal = VContext <$> (stackId <* symbol ':') <*> val

quotedExpr = between (symbol '[') (symbol ']') (EQuote <$> expr)

quotedVal = between (symbol '[') (symbol ']') (VQuote <$> val)

sugarExpr = sugar EContext EIntrinsic

sugarVal = sugar VContext VIntrinsic

sugar contextCons intrinsicCons =
  contextCons <$> stackId_
    <*> ( (keyword "<-" >> return (intrinsicCons IPush))
            <|> (keyword "->" >> return (intrinsicCons IPop))
        )

intrinsicExpr = intrinsic EIntrinsic

intrinsicVal = intrinsic VIntrinsic

intrinsic cons =
  try (keyword "push" >> return (cons IPush))
    <|> try (keyword "pop" >> return (cons IPop))
    <|> try (keyword "clone" >> return (cons IClone))
    <|> try (keyword "drop" >> return (cons IDrop))
    <|> try (keyword "quote" >> return (cons IQuote))
    <|> try (keyword "compose" >> return (cons ICompose))
    <|> try (keyword "apply" >> return (cons IApply))
    <|> try (keyword "eqz" >> return (cons IEqz))
    <|> try (keyword "add" >> return (cons IAdd))
    <|> try (keyword "sub" >> return (cons ISub))
    <|> try (keyword "bit_and" >> return (cons IBitAnd))
    <|> try (keyword "bit_or" >> return (cons IBitOr))
    <|> try (keyword "bit_xor" >> return (cons IBitXor))
    <|> try (keyword "shl" >> return (cons IShl))
    <|> try (keyword "shr" >> return (cons IShr))

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
