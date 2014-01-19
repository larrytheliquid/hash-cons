{-# OPTIONS --type-in-type #-}
module Desc.Concat where
open import Desc
import Desc.Examples

----------------------------------------------------------------------

Concat : Set
Concat = {!!}

----------------------------------------------------------------------

concat : Desc.Examples.Induction.Concat
concat = {!!}

----------------------------------------------------------------------

test-Concat : Concat ≡ Desc.Examples.Induction.Concat
test-Concat = {!!}

test-concat : concat ≡ Desc.Examples.Induction.concat
test-concat = {!!}

----------------------------------------------------------------------
