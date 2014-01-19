{-# OPTIONS --type-in-type #-}
module Desc.Append where
open import Desc
import Desc.Examples

----------------------------------------------------------------------

Append : Set
Append = {!!}

----------------------------------------------------------------------

append : Desc.Examples.Induction.Append
append = {!!}

----------------------------------------------------------------------

test-Append : Append ≡ Desc.Examples.Induction.Append
test-Append = {!!}

test-append : append ≡ Desc.Examples.Induction.append
test-append = {!!}

----------------------------------------------------------------------
