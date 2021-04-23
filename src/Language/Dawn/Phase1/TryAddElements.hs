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
tryAddElements env@Env {includes} elems = do
  elems' <- recursiveInclude includes "" elems
  env1 <- liftEither (mapLeft DataDefElementError (tryAddDataDefs env (getDataDefs elems')))
  env2 <- liftEither (mapLeft FnDeclElementError (tryAddFnDecls env1 (getFnDecls elems')))
  env3 <- liftEither (mapLeft FnDefElementError (tryAddFnDefs env2 (getFnDefs elems')))
  liftEither (mapLeft TestDefElementError (tryAddTestDefs env3 (getTestDefs elems')))
  where
    recursiveInclude :: Set.Set URIRef -> URIRef -> [Element] -> ExceptT ElementError IO [Element]
    recursiveInclude includes uriRefDir [] = return []
    recursiveInclude includes uriRefDir (EInclude (Include uriRef) : es) = do
      let combinedUriRef =
            if null uriRefDir || "/" `isPrefixOf` uriRef
              then uriRef
              else uriRefDir ++ "/" ++ uriRef
      if combinedUriRef `Set.member` includes
        then recursiveInclude includes uriRefDir es
        else do
          es' <- ExceptT (fmap (first IncludeElementError) (parseElementsFromFile combinedUriRef))
          let combinedUriRefSegments = splitOn "/" combinedUriRef
          let uriRefDir' = intercalate "/" (init combinedUriRefSegments)
          let includes' = Set.insert combinedUriRef includes
          elems' <- recursiveInclude includes' uriRefDir' es'
          elems <- recursiveInclude includes' uriRefDir es
          return (elems' ++ elems)
    recursiveInclude includes uriRefDir (e : es) = return (e : es)
