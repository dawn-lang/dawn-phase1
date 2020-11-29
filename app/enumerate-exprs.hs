-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Main where

import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Exprs
import Language.Dawn.Phase1.Utils

main = do
  mapM printExprType (allExprsUpToWidthAndDepth 3 1)

printExprType e = do
  putStr ("`" ++ display e ++ "`")
  case inferType e of
    Left err -> putStrLn $ " is not typeable. " ++ display err
    Right t -> putStrLn $ " :: " ++ display (normalizeType t)
