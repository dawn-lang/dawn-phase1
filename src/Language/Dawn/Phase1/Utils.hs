-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Utils
  ( fromExprSeq,
    inferNormType',
    inferType',
    polymorphicRank,
    renameTypeVar,
    toExprSeq,
    unusedQuantifiers,
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core

toExprSeq :: Expr -> [Expr]
toExprSeq (ECompose es) = es
toExprSeq e = [e]

fromExprSeq :: [Expr] -> Expr
fromExprSeq [] = ECompose []
fromExprSeq [e] = e
fromExprSeq es = ECompose es

inferType' :: Expr -> Either TypeError Type
inferType' = inferType Map.empty ["$"]

inferNormType' :: Expr -> Either TypeError Type
inferNormType' = inferNormType Map.empty ["$"]

---------------------
-- Type Validation --
---------------------

unusedQuantifiers :: Type -> TypeVars
unusedQuantifiers (TVar _) = Set.empty
unusedQuantifiers (TProd l r) =
  unusedQuantifiers l `Set.union` unusedQuantifiers r
unusedQuantifiers (TFn qs mio) =
  let unused = qs `Set.difference` ftv mio
      folder s (i, o) =
        s `Set.union` unusedQuantifiers i `Set.union` unusedQuantifiers o
   in unused `Set.union` foldl folder Set.empty mio
unusedQuantifiers (TCons _) = Set.empty

----------------------
-- Polymorphic Rank --
----------------------

polymorphicRank :: Type -> Int
polymorphicRank (TVar _) = 0
polymorphicRank (TProd l r) = max (polymorphicRank l) (polymorphicRank r)
polymorphicRank (TFn qs mio) =
  if null qs
    then
      let iter (i, o) = max (polymorphicRank i) (polymorphicRank o)
       in maximum (map iter (Map.elems mio))
    else
      let iter (i, o) = max (polymorphicRank i) (polymorphicRank o - 1)
       in 1 + maximum (map iter (Map.elems mio))
polymorphicRank (TCons _) = 0
