-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.
{-# LANGUAGE NamedFieldPuns #-}

module Language.Dawn.Phase1.TryAddElements
  ( ElementError (..),
    tryAddElements,
  )
where

import Control.Monad.Except
import Data.Bifunctor
import Data.Either.Combinators
import Data.List.Extra
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Parse (parseElementsFromFile)
import Text.Parsec

data ElementError
  = IncludeElementError ParseError
  | DataDefElementError DataDefError
  | FnDeclElementError FnDeclError
  | FnDefElementError FnDefError
  | TestDefElementError TestDefError
  deriving (Eq, Show)

getDataDefs :: [Element] -> [DataDef]
getDataDefs [] = []
getDataDefs (EDataDef d : es) = d : getDataDefs es
getDataDefs (e : es) = getDataDefs es

getFnDecls :: [Element] -> [FnDecl]
getFnDecls [] = []
getFnDecls (EFnDecl d : es) = d : getFnDecls es
getFnDecls (e : es) = getFnDecls es

getFnDefs :: [Element] -> [FnDef]
getFnDefs [] = []
getFnDefs (EFnDef d : es) = d : getFnDefs es
getFnDefs (e : es) = getFnDefs es

getTestDefs :: [Element] -> [TestDef]
getTestDefs [] = []
getTestDefs (ETestDef d : es) = d : getTestDefs es
getTestDefs (e : es) = getTestDefs es

tryAddElements :: Env -> [Element] -> ExceptT ElementError IO Env
tryAddElements env elems = do
  (env1, elems1) <- recursiveInclude env "" elems
  env2 <- liftEither (mapLeft DataDefElementError (tryAddDataDefs env1 (getDataDefs elems1)))
  env3 <- liftEither (mapLeft FnDeclElementError (tryAddFnDecls env2 (getFnDecls elems1)))
  env4 <- liftEither (mapLeft FnDefElementError (tryAddFnDefs env3 (getFnDefs elems1)))
  liftEither (mapLeft TestDefElementError (tryAddTestDefs env4 (getTestDefs elems1)))
  where
    recursiveInclude :: Env -> URIRef -> [Element] -> ExceptT ElementError IO (Env, [Element])
    recursiveInclude env uriRefDir [] = return (env, [])
    recursiveInclude env@Env {includes} uriRefDir (EInclude (Include uriRef) : es) = do
      let combinedUriRef =
            if null uriRefDir || "/" `isPrefixOf` uriRef
              then uriRef
              else uriRefDir ++ "/" ++ uriRef
      if combinedUriRef `Set.member` includes
        then recursiveInclude env uriRefDir es
        else do
          es' <- ExceptT (fmap (first IncludeElementError) (parseElementsFromFile combinedUriRef))
          let combinedUriRefSegments = splitOn "/" combinedUriRef
          let uriRefDir' = intercalate "/" (init combinedUriRefSegments)
          let env1 = env {includes = Set.insert combinedUriRef includes}
          (env2, elems2) <- recursiveInclude env1 uriRefDir' es'
          (env3, elems3) <- recursiveInclude env2 uriRefDir es
          return (env3, elems2 ++ elems3)
    recursiveInclude env uriRefDir (e : es) = return (env, e : es)
