-- Copyright (c) 2021 Scott J Maddox
--
-- Licensed under either the Apache License, Version 2.0 (see LICENSE-APACHE),
-- or the ZLib license (see LICENSE-ZLIB), at your option.

module Language.Dawn.Phase1.PartialEval
  ( partialEval,
  )
where

import Control.Monad
import Control.Monad.Except
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Dawn.Phase1.Core hiding ((*))

partialEval :: Expr -> Expr
partialEval e@(EIntrinsic _) = e
partialEval (EQuote e) = EQuote (partialEval e)
partialEval (ECompose es) = case iter [] es of
  [e] -> e
  es -> ECompose es
  where
    iter es' [] = es'
    iter
      es'
      ( e@(EQuote (ECompose (EIntrinsic IClone : EIntrinsic IApply : _)))
          : EIntrinsic IClone
          : EIntrinsic IApply
          : es
        ) =
        iter (es' ++ [e, EIntrinsic IClone, EIntrinsic IApply]) es
    iter es' (EQuote e : EIntrinsic IClone : es) =
      iter es' (EQuote e : EQuote e : es)
    iter es' (EQuote _ : EIntrinsic IDrop : es) =
      iter es' es
    iter es' (EQuote e1 : EQuote e2 : EIntrinsic ISwap : es) =
      iter es' (EQuote e2 : EQuote e1 : es)
    iter es' (EQuote e : EIntrinsic IQuote : es) =
      iter es' (EQuote (EQuote e) : es)
    iter es' (EQuote e1 : EQuote e2 : EIntrinsic ICompose : es) =
      case (e1, e2) of
        (ECompose es1, ECompose es2) -> iter es' (EQuote (ECompose (es1 ++ es2)) : es)
        (ECompose es1, _) -> iter es' (EQuote (ECompose (es1 ++ [e2])) : es)
        (_, ECompose es2) -> iter es' (EQuote (ECompose (e1 : es2)) : es)
        (_, _) -> iter es' (EQuote (ECompose [e1, e2]) : es)
    iter es' (EQuote e : EIntrinsic IApply : es) =
      if null es'
        then iter [] (e : es)
        else iter (init es') (last es' : e : es)
    iter [] ((ECompose es'') : es) = iter [] (es'' ++ es)
    iter es' ((ECompose es'') : es) = iter (init es') (last es' : es'' ++ es)
    iter es' (e : es) = iter (es' ++ [e]) es
