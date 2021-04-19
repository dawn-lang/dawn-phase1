-- Copyright (c) 2021 Scott J Maddox
--
-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at https://mozilla.org/MPL/2.0/.

module Language.Dawn.Phase1.Prelude (preludeEnv) where

import Language.Dawn.Phase1.Core
import Language.Dawn.Phase1.Parse

(Right preludeEnv) =
  let bitSrc = "{data Bit {cons B0} {cons B1}}"
      byteSrc = "{data Byte {cons Bit Bit Bit Bit Bit Bit Bit Bit Byte}}"
      (Right bitDef) = parseDataDef bitSrc
      (Right byteDef) = parseDataDef byteSrc
   in tryAddDataDefs emptyEnv [bitDef, byteDef]
