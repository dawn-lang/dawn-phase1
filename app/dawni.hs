-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Main where

import Control.Monad
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Parse
import Language.Dawn.Phase1.PartialEval
import Language.Dawn.Phase1.Utils
import System.Console.Haskeline hiding (display)
import System.IO

main = do
  putStrLn "Dawn Phase 1 Interpreter"
  runInputT defaultSettings readEvalPrintLoop

readEvalPrintLoop = readEvalPrint >> readEvalPrintLoop

readEvalPrint = do
  maybeLine <- getInputLine "> "
  case maybeLine of
    Nothing -> return ()
    Just line -> case parseExpr line of
      Left err -> outputStrLn (show err)
      Right e -> do
        printExprType e
        when (e /= partialEval e) $ printExprType (partialEval e)

printExprType e = do
  outputStr (display e)
  case inferType e of
    Left e -> outputStrLn $ " is not typeable. " ++ display e
    Right t -> outputStrLn $ " :: " ++ display (normalizeType t)
