-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Utils
  ( inferNormType,
    inferNormType',
    normalizeType,
    polymorphicRank,
    removeTrivialStacks,
    renameTypeVar,
    unusedQuantifiers,
  )
where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core

------------------------
-- Type Normalization --
------------------------

normalizeType :: Type -> Type
normalizeType = normalizeTypeVars . removeTrivialStacks

removeTrivialStacks :: Type -> Type
removeTrivialStacks t@(TVar _) = t
removeTrivialStacks (TProd l r) = TProd (removeTrivialStacks l) (removeTrivialStacks r)
removeTrivialStacks (TFn qs mio) =
  let trivialMIO = Map.filter (isTrivial qs) mio
      mio' = mio `Map.difference` trivialMIO
   in if null mio'
        then
          let v = TVar (Set.findMin qs)
           in forall' [v] (v --> v)
        else
          let ftvs = ftv trivialMIO
              qs' =
                if any (`elem` atv mio') (Set.elems ftvs)
                  then error "invalid reuse of trivial stack variable"
                  else qs `Set.difference` ftvs
              iter (i, o) = (removeTrivialStacks i, removeTrivialStacks o)
           in TFn qs' (Map.map iter mio')
  where
    isTrivial qs (TVar i, TVar o) | i == o && i `elem` qs = True
    isTrivial _ _ = False
removeTrivialStacks t@(TCons _) = t

normalizeTypeVars :: Type -> Type
normalizeTypeVars t =
  if not $ null $ ftv t
    then error "unexpected free type variables"
    else
      let (t', _) = instantiate t Set.empty
          maxId = maximum $ map (\(TypeVar id) -> id) (atv t')
          (t'', _) = instantiate t' (Set.fromList (map TypeVar [0 .. maxId]))
          (t''', _) = replaceTypeVars (atv t'') t'' Set.empty
       in t'''

inferNormType :: Context -> Expr -> Result Type
inferNormType ctx e = do
  t <- inferType ctx e
  return (normalizeType t)

inferNormType' :: Expr -> Result Type
inferNormType' = inferNormType ["$"]

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
