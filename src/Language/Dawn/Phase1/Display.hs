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
  display (EContext s (EIntrinsic IPush)) = s ++ "<-"
  display (EContext s (EIntrinsic IPop)) = s ++ "->"
  display (EContext s e) = "(" ++ s ++ ": " ++ display e ++ ")"
  display (ELit (LU32 i)) = show i

displayedExprs :: [Expr] -> [String]
displayedExprs [] = []
displayedExprs (ECompose es : es') = case displayedExprs es of
  [] -> "()" : displayedExprs es'
  [de] -> de : displayedExprs es'
  (de : des) -> ["(" ++ de] ++ init des ++ [last des ++ ")"] ++ displayedExprs es'
displayedExprs (e : es) = display e : displayedExprs es

instance Display Intrinsic where
  display IPush = "push"
  display IPop = "pop"
  display IClone = "clone"
  display IDrop = "drop"
  display IQuote = "quote"
  display ICompose = "compose"
  display IApply = "apply"
  display IEqz = "eqz"
  display IAdd = "add"
  display ISub = "sub"
  display IBitAnd = "bit_and"
  display IBitOr = "bit_or"
  display IBitXor = "bit_xor"
  display IShl = "shl"
  display IShr = "shr"

instance Display Type where
  display (TVar tv) = display tv
  display (TProd t t') = display t ++ " * " ++ display t'
  display (TFn qs mio) =
    "("
      ++ ( if null qs
             then ""
             else "∀ " ++ unwords (map display (Set.toAscList qs))
         )
      ++ (if null qs then "" else " . ")
      ++ displayMultiIO mio
      ++ ")"
  display (TCons tc) = display tc

displayMultiIO mio
  | Map.keys mio == [""] =
    let [("", (i, o))] = Map.toList mio
     in display i ++ " -> " ++ display o
  | otherwise = intercalate " . " (map iter (Map.toAscList mio))
  where
    iter (sid, (i, o)) = sid ++ ": " ++ display i ++ " -> " ++ display o

instance Display TypeCons where
  display (TypeCons s) = s

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
