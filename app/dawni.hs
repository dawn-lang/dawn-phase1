-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Main where

import qualified Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.PartialEval
import Language.Dawn.Phase1.Utils
import System.Console.Haskeline hiding (display)
import System.Exit
import System.IO
import Text.Parsec
import Text.Parsec.String

main = do
  putStrLn "Dawn Phase 1 Interpreter"
  runInputT defaultSettings (readEvalPrintLoop (MultiStack Map.empty))

readEvalPrintLoop :: MultiStack -> InputT IO MultiStack
readEvalPrintLoop ms = do
  ms' <- readEvalPrint ms
  readEvalPrintLoop ms'

readEvalPrint :: MultiStack -> InputT IO MultiStack
readEvalPrint ms = do
  maybeLine <- getInputLine "> "
  case maybeLine of
    Nothing -> return ms
    Just line -> case parseCommand line of
      Left err -> do
        outputStrLn (show err)
        return ms
      Right CmdExit -> liftIO exitSuccess
      Right CmdClear -> do
        return (MultiStack Map.empty)
      Right (CmdPrint e) -> do
        printExprType e
        return ms
      Right (CmdPartialEval e) -> do
        printExprType (partialEval' e)
        return ms
      Right (CmdEval e) ->
        case inferNormType' e of
          Left err -> do
            outputStrLn $ display e ++ " is not typeable. " ++ display err
            return ms
          Right t -> do
            result <- tryEval e ms
            case result :: Either SomeException MultiStack of
              Left err -> do
                outputStrLn $ show err
                return ms
              Right ms' -> do
                outputStrLn $ display ms'
                return ms'

printExprType e =
  case inferNormType' e of
    Left err -> outputStrLn $ display e ++ " is not typeable. " ++ display err
    Right t -> outputStrLn $ display e ++ " :: " ++ display t

tryEval :: Expr -> MultiStack -> InputT IO (Either SomeException MultiStack)
tryEval e ms =
  liftIO (Control.Exception.try (Control.Exception.evaluate (eval ["$"] e ms)))

parseCommand :: String -> Either ParseError Command
parseCommand = parse (skipMany space *> command <* eof) ""

command :: Parser Command
command =
  try (keyword ":exit" >> return CmdExit)
    <|> try (keyword ":clear" >> return CmdClear)
    <|> try (CmdPrint <$> (keyword ":print" *> expr))
    <|> try (CmdPartialEval <$> (keyword ":partialEval" *> expr))
    <|> CmdEval <$> expr

data Command
  = CmdExit
  | CmdClear
  | CmdPrint Expr
  | CmdPartialEval Expr
  | CmdEval Expr
