-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Main where

import Control.Monad
import Data.Either
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Exprs
import Language.Dawn.Phase1.PartialEval
import Language.Dawn.Phase1.Utils

main = do
  let iter e = do
        let t = inferNormType e
        let e' = partialEval e
        let t' = inferNormType e'
        when
          ((isRight t || isRight t') && t /= t')
          ( do
              printExprType e t
              printExprType e' t'
              putStrLn ""
          )
  mapM iter (allExprsUpToWidthAndDepth 4 1)

printExprType e t = do
  case t of
    Left err -> putStrLn $ display e ++ " is not typeable. " ++ display err
    Right t' -> putStrLn $ display e ++ " :: " ++ display t'
