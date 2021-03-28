-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.
{-# LANGUAGE NamedFieldPuns #-}

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
  runInputT defaultSettings (readEvalPrintLoop (emptyEnv, MultiStack Map.empty))

readEvalPrintLoop :: (Env, MultiStack) -> InputT IO (Env, MultiStack)
readEvalPrintLoop (env, ms) = do
  (env', ms') <- readEvalPrint (env, ms)
  readEvalPrintLoop (env', ms')

readEvalPrint :: (Env, MultiStack) -> InputT IO (Env, MultiStack)
readEvalPrint (env, ms) = do
  maybeLine <- getInputLine "> "
  case maybeLine of
    Nothing -> return (env, ms)
    Just line -> case parseCommand line of
      Left err -> do
        outputStrLn (show err)
        return (env, ms)
      Right CmdExit -> liftIO exitSuccess
      Right CmdReset -> do
        return (emptyEnv, MultiStack Map.empty)
      Right CmdDrop -> do
        return (env, MultiStack Map.empty)
      Right (CmdType e) -> do
        printExprType env e
        return (env, ms)
      Right (CmdTrace e) ->
        let e' = fromExprSeq (toExprSeq (multiStackToExpr ms) ++ toExprSeq e)
         in case inferNormType env ["$"] e' of
              Left err -> do
                printInferTypeError e' err
                return (env, ms)
              Right t | exposedTempStackIds t -> do
                printExposedTempStackIds t
                return (env, ms)
              Right t | expectsInputs t -> do
                printExpectsInputs t
                return (env, ms)
              Right t -> do
                result <- tryTraceEval (toEvalEnv env) e ms
                case result :: Either SomeException (Expr, MultiStack) of
                  Left err -> do
                    outputStrLn $ show err
                    return (env, ms)
                  Right (e', ms') -> do
                    return (env, ms')
      Right (CmdPartialEval e) -> do
        printExprType env (partialEval' e)
        return (env, ms)
      Right (CmdDataDefs defs) -> case addDataDefs env defs of
        ([], env') -> return (env', ms)
        (err : errs, env') -> do
          outputStrLn ("Error: " ++ display err)
          return (env, ms)
      Right (CmdFnDef (FnDef fid e)) -> case defineFn env (FnDef fid e) of
        Left (FnAlreadyDefined fid) -> do
          outputStrLn ("Error: already defined: " ++ fid)
          return (env, ms)
        Left (FnTypeError fid err) -> do
          printInferTypeError e err
          return (env, ms)
        Left (FnStackError fid sids) -> do
          let s = intercalate ", " (Set.toList sids)
          outputStrLn ("Error: exposed temporary stacks: " ++ s)
          return (env, ms)
        Right env'@Env {fnTypes} -> do
          let (Just t) = Map.lookup fid fnTypes
          outputStrLn $ fid ++ " :: " ++ display t
          return (env', ms)
      Right (CmdEval e) ->
        let e' = fromExprSeq (toExprSeq (multiStackToExpr ms) ++ toExprSeq e)
         in case inferNormType env ["$"] e' of
              Left err -> do
                printInferTypeError e' err
                return (env, ms)
              Right t | exposedTempStackIds t -> do
                printExposedTempStackIds t
                return (env, ms)
              Right t | expectsInputs t -> do
                printExpectsInputs t
                return (env, ms)
              Right t -> do
                result <- tryEval (toEvalEnv env) e ms
                case result :: Either SomeException MultiStack of
                  Left err -> do
                    outputStrLn $ show err
                    return (env, ms)
                  Right ms' -> do
                    outputStrLn $ display ms'
                    return (env, ms')

multiStackToExpr :: MultiStack -> Expr
multiStackToExpr (MultiStack ms) =
  let mapper ("$", v) = ECompose (map fromVal v)
      mapper (s, v) = EContext s (ECompose (map fromVal v))
   in ECompose (map mapper (Map.toAscList ms))

printInferTypeError e err =
  outputStrLn $ "Error: " ++ display e ++ " is not typeable. " ++ display err

exposedTempStackIds t = not (null (tempStackIds t))

expectsInputs (TFn _ mio) =
  let isTProd (TProd _ _) = True
      isTProd _ = False
   in any (\(s, (i, o)) -> isTProd i) (Map.toAscList mio)
expectsInputs _ = False

printExpectsInputs t = do
  outputStrLn ("Error: missing expected input: " ++ display t)

printExposedTempStackIds t = do
  let s = intercalate ", " (Set.toList (tempStackIds t))
  outputStrLn ("Error: exposed temporary stacks: " ++ s)

printExprType env e =
  case inferNormType env ["$"] e of
    Left err -> printInferTypeError e err
    Right t | exposedTempStackIds t -> printExposedTempStackIds t
    Right t -> outputStrLn $ display e ++ " :: " ++ display t

tryTraceEval :: EvalEnv -> Expr -> MultiStack -> InputT IO (Either SomeException (Expr, MultiStack))
tryTraceEval env e@(ECompose []) ms = do
  outputStrLn $ display ms
  return (Right (e, ms))
tryTraceEval env e ms = do
  outputStrLn $ display ms ++ " " ++ display e
  result <- liftIO (Control.Exception.try (Control.Exception.evaluate (evalWithFuel env ["$"] (1, e, ms))))
  case result of
    Left err -> return (Left err)
    Right (_, e', ms') -> tryTraceEval env e' ms'

tryEval :: EvalEnv -> Expr -> MultiStack -> InputT IO (Either SomeException MultiStack)
tryEval env e ms =
  liftIO (Control.Exception.try (Control.Exception.evaluate (eval env ["$"] e ms)))

parseCommand :: String -> Either ParseError Command
parseCommand = parse (skipMany space *> command <* eof) ""

command :: Parser Command
command =
  try (keyword ":exit" >> return CmdExit)
    <|> try (keyword ":reset" >> return CmdReset)
    <|> try (keyword ":drop" >> return CmdDrop)
    <|> try (CmdType <$> (keyword ":type" *> expr))
    <|> try (CmdTrace <$> (keyword ":trace" *> expr))
    <|> try (CmdPartialEval <$> (keyword ":partialEval" *> expr))
    <|> try (CmdDataDefs <$> many1 dataDef)
    <|> try (CmdFnDef <$> fnDef)
    <|> CmdEval <$> expr

data Command
  = CmdExit
  | CmdReset
  | CmdDrop
  | CmdType Expr
  | CmdTrace Expr
  | CmdPartialEval Expr
  | CmdDataDefs [DataDef]
  | CmdFnDef FnDef
  | CmdEval Expr
