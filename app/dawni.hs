-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Main where

import Control.Exception (SomeException)
import qualified Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
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
  runInputT defaultSettings (readEvalPrintLoop (Map.empty, MultiStack Map.empty))

readEvalPrintLoop :: (FnEnv, MultiStack) -> InputT IO (FnEnv, MultiStack)
readEvalPrintLoop (env, ms) = do
  (env', ms') <- readEvalPrint (env, ms)
  readEvalPrintLoop (env', ms')

readEvalPrint :: (FnEnv, MultiStack) -> InputT IO (FnEnv, MultiStack)
readEvalPrint (env, ms) = do
  maybeLine <- getInputLine "> "
  case maybeLine of
    Nothing -> return (env, ms)
    Just line -> case parseCommand line of
      Left err -> do
        outputStrLn (show err)
        return (env, ms)
      Right CmdExit -> liftIO exitSuccess
      Right CmdClear -> do
        return (Map.empty, MultiStack Map.empty)
      Right (CmdPrint e) -> do
        printExprType env e
        return (env, ms)
      Right (CmdPartialEval e) -> do
        printExprType env (partialEval' e)
        return (env, ms)
      Right (CmdFnDef (FnDef fid e)) -> case defineFn env (FnDef fid e) of
        Left (FnAlreadyDefined fid) -> do
          outputStrLn ("Error: already defined: " ++ fid)
          return (env, ms)
        Left (FnCallsUndefined fid fids) -> do
          let s = intercalate ", " (Set.toList fids)
          outputStrLn ("Error: undefined: " ++ s)
          return (env, ms)
        Left (FnTypeError fid err) -> do
          printInferTypeError e err
          return (env, ms)
        Left (FnStackError fid sids) -> do
          let s = intercalate ", " (Set.toList sids)
          outputStrLn ("Error: exposed temporary stacks: " ++ s)
          return (env, ms)
        Left (FnTypeUnstable _) -> do
          outputStrLn ("Error: function type diverges: " ++ fid)
          return (env, ms)
        Right env' -> do
          let (Just (_, t)) = Map.lookup fid env'
          outputStrLn $ fid ++ " :: " ++ display t
          return (env', ms)
      Right (CmdEval e)
        | not (null (undefinedFnIds env e)) -> do
          printUndefinedFnIdsError env e
          return (env, ms)
        | otherwise -> case inferNormType env ["$"] e of
          Left err -> do
            printInferTypeError e err
            return (env, ms)
          Right t | exposedTempStackIds t -> do
            printExposedTempStackIds t
            return (env, ms)
          Right t -> do
            result <- tryEval env e ms
            case result :: Either SomeException MultiStack of
              Left err -> do
                outputStrLn $ show err
                return (env, ms)
              Right ms' -> do
                outputStrLn $ display ms'
                return (env, ms')

printUndefinedFnIdsError env e =
  outputStrLn ("Error: undefined: " ++ head (Set.toList (undefinedFnIds env e)))

printInferTypeError e err =
  outputStrLn $ "Error: " ++ display e ++ " is not typeable. " ++ display err

exposedTempStackIds t = not (null (tempStackIds t))

printExposedTempStackIds t = do
  let s = intercalate ", " (Set.toList (tempStackIds t))
  outputStrLn ("Error: exposed temporary stacks: " ++ s)

printExprType env e =
  case inferNormType env ["$"] e of
    Left err -> printInferTypeError e err
    Right t | exposedTempStackIds t -> printExposedTempStackIds t
    Right t -> outputStrLn $ display e ++ " :: " ++ display t

tryEval :: FnEnv -> Expr -> MultiStack -> InputT IO (Either SomeException MultiStack)
tryEval env e ms =
  liftIO (Control.Exception.try (Control.Exception.evaluate (eval env ["$"] e ms)))

parseCommand :: String -> Either ParseError Command
parseCommand = parse (skipMany space *> command <* eof) ""

command :: Parser Command
command =
  try (keyword ":exit" >> return CmdExit)
    <|> try (keyword ":clear" >> return CmdClear)
    <|> try (CmdPrint <$> (keyword ":print" *> expr))
    <|> try (CmdPartialEval <$> (keyword ":partialEval" *> expr))
    <|> try (CmdFnDef <$> fnDef)
    <|> CmdEval <$> expr

data Command
  = CmdExit
  | CmdClear
  | CmdPrint Expr
  | CmdPartialEval Expr
  | CmdFnDef FnDef
  | CmdEval Expr
