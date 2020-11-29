-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Utils
  ( inferNormType,
    normalizeType,
    polymorphicRank,
    renameTypeVar,
    unusedQuantifiers,
  )
where

import qualified Data.Set as Set
import Language.Dawn.Phase1.Core

------------------------
-- Type Normalization --
------------------------

normalizeType :: Type -> Type
normalizeType t =
  if not $ null $ ftv t
    then error "unexpected free type variables"
    else
      let (t', _) = instantiate t Set.empty
          maxId = maximum $ map (\(TypeVar id) -> id) (atv t')
          (t'', _) = instantiate t' (Set.fromList (map TypeVar [0 .. maxId]))
          (t''', _) = replaceTypeVars (atv t'') t'' Set.empty
       in t'''

inferNormType :: Expr -> Result Type
inferNormType e = do
  t <- inferType e
  return (normalizeType t)

---------------------
-- Type Validation --
---------------------

unusedQuantifiers :: Type -> TypeVars
unusedQuantifiers (TVar _) = Set.empty
unusedQuantifiers (TProd l r) =
  unusedQuantifiers l `Set.union` unusedQuantifiers r
unusedQuantifiers (TFn qs (i, o)) =
  let unused = qs `Set.difference` ftv (i, o)
   in unused `Set.union` unusedQuantifiers i `Set.union` unusedQuantifiers o

----------------------
-- Polymorphic Rank --
----------------------

polymorphicRank :: Type -> Int
polymorphicRank (TVar _) = 0
polymorphicRank (TProd l r) = max (polymorphicRank l) (polymorphicRank r)
polymorphicRank (TFn qs (i, o)) =
  if null qs
    then max (polymorphicRank i) (polymorphicRank o)
    else 1 + max (polymorphicRank i) (polymorphicRank o - 1)
