-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Display (Display (..)) where

import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core

class Display t where
  display :: t -> String

instance Display Expr where
  display (EIntrinsic intr) = display intr
  display (EQuote e) = "[" ++ display e ++ "]"
  display (ECompose []) = "()"
  display (ECompose es) = unwords (displayedExprs es)

displayedExprs :: [Expr] -> [String]
displayedExprs [] = []
displayedExprs (ECompose es : es') = case displayedExprs es of
  [] -> "()" : displayedExprs es'
  [de] -> de : displayedExprs es'
  (de : des) -> ["(" ++ de] ++ init des ++ [last des ++ ")"] ++ displayedExprs es'
displayedExprs (e : es) = display e : displayedExprs es

instance Display Intrinsic where
  display IClone = "clone"
  display IDrop = "drop"
  display ISwap = "swap"
  display IQuote = "quote"
  display ICompose = "compose"
  display IApply = "apply"

instance Display Type where
  display (TVar tv) = display tv
  display (TProd t t') = display t ++ " * " ++ display t'
  display (TFn qs (i, o)) =
    "("
      ++ ( if null qs
             then ""
             else unwords $ map (\tv -> "∀" ++ display tv) (Set.toAscList qs)
         )
      ++ (if null qs then "" else " . ")
      ++ display i
      ++ " -> "
      ++ display o
      ++ ")"

instance Display TypeVar where
  display (TypeVar n) = "v" ++ show n

instance Display Subst where
  display (Subst m) =
    concatMap
      ( \(tv, t) -> "\n    " ++ display tv ++ " +-> " ++ display t
      )
      (Map.toAscList m)

instance Display UnificationError where
  display (DoesNotUnify t t') =
    display t ++ " does not unify with " ++ display t'
  display (OccursIn tv t) = display tv ++ " occurs in " ++ display t

instance Display a => Display [a] where
  display l = "[" ++ intercalate ", " (map display l) ++ "]"

instance (Display a, Display b) => Display (a, b) where
  display (a, b) = "(" ++ display a ++ ", " ++ display b ++ ")"
