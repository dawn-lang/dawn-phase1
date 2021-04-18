-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# LANGUAGE NamedFieldPuns #-}

module Main where

import Control.Exception (SomeException)
import qualified Control.Exception
import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import Data.Either.Combinators
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.PartialEval
import Language.Dawn.Phase1.Prelude
import Language.Dawn.Phase1.TryAddElements
import Language.Dawn.Phase1.Utils
import System.Console.ANSI
import System.Console.Haskeline hiding (display)
import System.Environment
import System.Exit
import System.IO
import Text.Parsec
import Text.Parsec.String

main = do
  args <- getArgs
  case args of
    [] -> do
      putStrLn "Dawn Phase 1 Interpreter"
      runInputT defaultSettings (readEvalPrintLoop (preludeEnv, MultiStack Map.empty))
      return ()
    ("--test" : args') -> do
      case args' of
        [] -> do
          putStrLn "Usage: --test FILE_PATH"
          return ()
        (path : args') -> do
          runInputT defaultSettings (doCliTest path)

doCliTest path = do
  env <- doAddElements preludeEnv [EInclude (Include path)]
  runTests env
  return ()

readEvalPrintLoop :: (Env, MultiStack Val) -> InputT IO (Env, MultiStack Val)
readEvalPrintLoop (env, ms) = do
  (env', ms') <- readEvalPrint (env, ms)
  readEvalPrintLoop (env', ms')

readEvalPrint :: (Env, MultiStack Val) -> InputT IO (Env, MultiStack Val)
readEvalPrint (env, ms) = do
  maybeLine <- getInputLine ">>> "
  case maybeLine of
    Nothing -> return (env, ms)
    Just line -> case parseCommand line of
      Left err -> do
        outputStrLn (show err)
        return (env, ms)
      Right CmdExit -> liftIO exitSuccess
      Right CmdReset -> do
        return (preludeEnv, MultiStack Map.empty)
      Right CmdDrop -> do
        return (env, MultiStack Map.empty)
      Right CmdTest -> do
        runTests env
        return (env, ms)
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
                case result :: Either SomeException (Expr, MultiStack Val) of
                  Left err -> do
                    outputStrLn $ show err
                    return (env, ms)
                  Right (e', ms') -> do
                    return (env, ms')
      Right (CmdPartialEval e) -> do
        printExprType env (partialEval' e)
        return (env, ms)
      Right (CmdAddElements elems) -> do
        env' <- doAddElements env elems
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
                case result :: Either SomeException (MultiStack Val) of
                  Left err -> do
                    outputStrLn $ show err
                    return (env, ms)
                  Right ms' -> do
                    outputStrLn $ display ms'
                    return (env, ms')

doAddElements env elems = do
  result <- tryTryAddElements env elems
  case result :: Either SomeException (Either ElementError Env) of
    Left err -> do
      outputStrLn ("Error: " ++ show err)
      return env
    Right (Left err) -> do
      outputStrLn ("Error: " ++ display err)
      return env
    Right (Right env') -> return env'

multiStackToExpr :: MultiStack Val -> Expr
multiStackToExpr (MultiStack ms) =
  let mapper ("$", vs) = ECompose (map fromVal (fromStack vs))
      mapper (s, vs) = EContext s (ECompose (map fromVal (fromStack vs)))
   in ECompose (map mapper (Map.toAscList ms))

printInferTypeError :: (MonadIO m, Display t1, Display t2) => t1 -> t2 -> InputT m ()
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

tryTraceEval :: EvalEnv -> Expr -> MultiStack Val -> InputT IO (Either SomeException (Expr, MultiStack Val))
tryTraceEval env e@(ECompose []) ms = do
  outputStrLn $ display ms
  return (Right (e, ms))
tryTraceEval env e ms = do
  outputStrLn $ display ms ++ " " ++ display e
  result <- liftIO (Control.Exception.try (Control.Exception.evaluate (evalWithFuel env ["$"] (1, e, ms))))
  case result of
    Left err -> return (Left err)
    Right (_, e', ms') -> tryTraceEval env e' ms'

tryEval :: EvalEnv -> Expr -> MultiStack Val -> InputT IO (Either SomeException (MultiStack Val))
tryEval env e ms =
  liftIO (Control.Exception.try (Control.Exception.evaluate (eval env ["$"] e ms)))

tryTryAddElements ::
  Env ->
  [Element] ->
  InputT IO (Either SomeException (Either ElementError Env))
tryTryAddElements env elems =
  liftIO $ Control.Exception.try $ runExceptT $ tryAddElements env elems

runTests :: Env -> InputT IO ()
runTests env@Env {testDefs} = do
  let evalEnv = toEvalEnv env
  results <- mapM (runTest evalEnv) testDefs
  let total = length results
  let passed = length (filter isRight results)
  let failed = length (filter isLeft results)
  mapM_ (uncurry printTestError) (zip testDefs results)
  outputStr ("\nRan " ++ show total ++ " tests. ")
  outputStr (show passed ++ " passed. ")
  outputStr (show failed ++ " failed.")
  outputStrLn "\n"

runTest :: EvalEnv -> TestDef -> InputT IO (Either SomeException ())
runTest evalEnv (TestDef n e) = do
  outputStr $ n ++ " ... "
  result <- tryEval evalEnv e (MultiStack Map.empty)
  case result :: Either SomeException (MultiStack Val) of
    Left err -> do
      outputStrLn (setSGRCode [SetColor Foreground Vivid Red] ++ "Fail" ++ setSGRCode [Reset])
      return (Left err)
    Right ms' -> do
      outputStrLn (setSGRCode [SetColor Foreground Vivid Green] ++ "Pass" ++ setSGRCode [Reset])
      return (Right ())

printTestError :: TestDef -> Either SomeException () -> InputT IO ()
printTestError (TestDef n _) (Left err) = do
  outputStrLn ""
  outputStrLn (replicate 70 '=')
  outputStrLn n
  outputStrLn (replicate 70 '=')
  outputStrLn (show err)
  outputStrLn (replicate 70 '-')
  return ()
printTestError _ _ = return ()

parseCommand :: String -> Either ParseError Command
parseCommand = parse (skipMany space *> command <* eof) ""

command :: Parser Command
command =
  try (keyword ":exit" >> return CmdExit)
    <|> try (keyword ":reset" >> return CmdReset)
    <|> try (keyword ":drop" >> return CmdDrop)
    <|> try (keyword ":test" >> return CmdTest)
    <|> try (CmdType <$> (keyword ":type" *> expr))
    <|> try (CmdTrace <$> (keyword ":trace" *> expr))
    <|> try (CmdPartialEval <$> (keyword ":partialEval" *> expr))
    <|> try (CmdAddElements <$> many1 element)
    <|> CmdEval <$> expr

data Command
  = CmdExit
  | CmdReset
  | CmdDrop
  | CmdTest
  | CmdType Expr
  | CmdTrace Expr
  | CmdPartialEval Expr
  | CmdAddElements [Element]
  | CmdEval Expr
