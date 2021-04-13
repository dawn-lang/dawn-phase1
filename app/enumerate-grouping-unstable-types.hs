-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option. This file may not be
-- copied, modified, or distributed except according to those terms.

module Main where

import Control.Monad
import Data.Either
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Display
import Language.Dawn.Phase1.Exprs
import Language.Dawn.Phase1.Utils

main = do
  mapM printExprType (allExprsUpToWidthAndDepth 4 1)

printExprType e = do
  let t = inferNormType' e
  let es = allGroupings e
  let ts = filter isRight (map inferNormType' es)
  when
    (length ts > 1 && any (/= t) ts)
    ( do
        mapM_
          ( \(e', t') -> case t' of
              Left err -> putStrLn $ display e' ++ " is not typeable. " ++ display err
              Right t'' -> putStrLn $ display e' ++ " :: " ++ display t''
          )
          (zip es ts)
        putStrLn ""
    )
