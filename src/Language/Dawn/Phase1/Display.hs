-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Language.Dawn.Phase1.Display (Display (..)) where

import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Eval
import Language.Dawn.Phase1.TryAddElements

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
  display (PCons Empty cid) = cid
  display (PCons args cid) = "(" ++ display args ++ " " ++ cid ++ ")"
  display PWild = "_"

instance Display Intrinsic where
  display IPush = "push"
  display IPop = "pop"
  display IClone = "clone"
  display IDrop = "drop"
  display IQuote = "quote"
  display ICompose = "compose"
  display IApply = "apply"

instance Display Type where
  display (TVar tv) = display tv
  display (TProd t t') = display t ++ " " ++ display t'
  display (TFn qs mio) =
    "("
      ++ ( if null qs
             then ""
             else "∀ " ++ unwords (map display (Set.toAscList qs))
         )
      ++ (if null qs then "" else " . ")
      ++ displayMultiIO mio
      ++ ")"
  display (TCons [] cid) = cid
  display (TCons args cid) = "(" ++ unwords (map display args ++ [cid]) ++ ")"

displayMultiIO mio
  | Map.keys mio == ["$"] =
    let [("$", (i, o))] = Map.toList mio
     in display i ++ " -> " ++ display o
  | otherwise = unwords (map mapper (Map.toAscList mio))
  where
    mapper (sid, (i, o)) =
      "{" ++ sid ++ " " ++ display i ++ " -> " ++ display o ++ "}"

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

instance Display MatchError where
  display (DoesNotMatch t t') =
    display t ++ " does not match " ++ display t'

instance Display TypeError where
  display (UnificationError err) = "unification error: " ++ display err
  display (MatchError matchError) = "match error: " ++ display matchError
  display (UndefinedCons cid) = "undefined constructor: " ++ cid
  display (UndefinedFn fid) = "undefined function: " ++ fid

instance Display FnDeclError where
  display err@(FnAlreadyDeclared fid) = show err

instance Display FnDefError where
  display err@(FnAlreadyDefined fid) = show err
  display (FnTypeError fid err) = "type error: " ++ display err
  display (FnStackError fid sids) =
    let s = intercalate ", " (Set.toList sids)
     in "exposed temporary stacks: " ++ s

instance Display DataDefError where
  display (TypeConsArityMismatch tcid t) =
    unwords ["TypeConsArityMismatch", tcid, display t]
  display err = show err

instance Display ElementError where
  display (IncludeElementError e) = show e
  display (DataDefElementError e) = display e
  display (FnDeclElementError e) = display e
  display (FnDefElementError e) = display e

instance Display Val where
  display (VCons Empty cid) = cid
  display (VCons args cid) = "(" ++ display args ++ " " ++ cid ++ ")"
  display v = display (fromVal v)

instance (Display a) => Display (Stack a) where
  display Empty = ""
  display (Empty :*: v) = display v
  display (s :*: v) = display s ++ " " ++ display v

instance (Display a) => Display (MultiStack a) where
  display (MultiStack m) =
    "{" ++ unwords (map mapper (Map.toAscList m)) ++ "}"
    where
      mapper (sid, vs) = sid ++ " " ++ display vs
