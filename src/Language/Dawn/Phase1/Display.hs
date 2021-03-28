-- Copyright (c) 2020 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.Display (Display (..)) where

import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Eval

class Display t where
  display :: t -> String

instance Display Expr where
  display (EIntrinsic intr) = display intr
  display (EQuote e) = "[" ++ display e ++ "]"
  display (ECompose []) = "()"
  display (ECompose es) = unwords (displayedExprs es)
  display (EContext s (EIntrinsic IPush)) = s ++ "<-"
  display (EContext s (EIntrinsic IPop)) = s ++ "->"
  display (EContext s e) = "{" ++ s ++ " " ++ display e ++ "}"
  display (ELit (LBool b)) = show b
  display (ELit (LU32 i)) = show i
  display (EMatch cases) = "{match " ++ unwords (map displayCase cases) ++ "}"
  display (ECons cid) = cid
  display (ECall fid) = fid

displayedExprs :: [Expr] -> [String]
displayedExprs [] = []
displayedExprs (ECompose es : es') = case displayedExprs es of
  [] -> "()" : displayedExprs es'
  [de] -> de : displayedExprs es'
  (de : des) -> ["(" ++ de] ++ init des ++ [last des ++ ")"] ++ displayedExprs es'
displayedExprs (e : es) = display e : displayedExprs es

displayCase (p, e) = "{case " ++ display p ++ " => " ++ display e ++ "}"

instance Display Pattern where
  display PEmpty = ""
  display (PProd l r) = unwords [display l, display r]
  display (PLit (LBool b)) = show b
  display (PLit (LU32 i)) = show i

instance Display Intrinsic where
  display = intrinsicFnId

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
  display (TCons args cid) = unwords (map display args ++ [cid])

displayMultiIO mio
  | Map.keys mio == ["$"] =
    let [("$", (i, o))] = Map.toList mio
     in display i ++ " -> " ++ display o
  | otherwise = unwords (map iter (Map.toAscList mio))
  where
    iter (sid, (i, o)) = "{" ++ sid ++ " " ++ display i ++ " -> " ++ display o ++ "}"

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

instance Display TypeError where
  display (UnificationError err) = "unification error: " ++ display err
  display (UndefinedFn fid) = "undefined function: " ++ fid

instance Display DataDefError where
  display (TypeConsArityMismatch tcid t) =
    unwords ["TypeConsArityMismatch", tcid, "(" ++ display t ++ ")"]
  display err = show err

instance Display MultiStack where
  display (MultiStack m) = "{" ++ unwords (map iter (Map.toAscList m)) ++ "}"
    where
      iter (sid, vs) = sid ++ ": " ++ unwords (map display (reverse vs))

instance Display Val where
  display (VCons [] cid) = cid
  display (VCons args cid) = "(" ++ unwords (map display args ++ [cid]) ++ ")"
  display v = display (fromVal v)
