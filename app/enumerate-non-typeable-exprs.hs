-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Main where

import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Exprs
import Language.Dawn.Phase1.Utils

main = do
  mapM printExprType (allExprsUpToWidthAndDepth 3 1)

printExprType e = do
  case inferType' e of
    Left err -> putStrLn $ display e ++ " is not typeable. " ++ display err
    Right _ -> return ()
