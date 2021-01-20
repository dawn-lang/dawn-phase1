-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Main where

import Control.Exception
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
import System.IO

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
    Just line | ":print " `isPrefixOf` line -> do
      case parseExpr (fromJust $ stripPrefix ":print " line) of
        Left err -> outputStrLn (show err)
        Right e ->
          case inferNormType' e of
            Left err -> outputStrLn $ display e ++ " is not typeable. " ++ display err
            Right t -> outputStrLn $ display e ++ " :: " ++ display t
      return ms
    Just line ->
      case parseExpr line of
        Left err -> do
          outputStrLn (show err)
          return ms
        Right e ->
          case inferNormType' e of
            Left err -> do
              outputStrLn $ display e ++ " is not typeable. " ++ display err
              return ms
            Right t -> do
              result <- try' (evaluate (eval ["$"] e ms))
              case (result :: Either SomeException MultiStack) of
                Left err -> do
                  outputStrLn $ show err
                  return ms
                Right ms' -> do
                  outputStrLn $ display ms'
                  return ms'

try' :: Exception e => IO a -> InputT IO (Either e a)
try' = liftIO . Control.Exception.try
