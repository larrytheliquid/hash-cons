{-# OPTIONS --type-in-type #-}
module Desc.Two where
open import Desc
import Desc.Examples

----------------------------------------------------------------------

Two : Set
Two =
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)))) tt)

----------------------------------------------------------------------

two : Desc.Examples.Two
two =
  (con ((pair (there here))
  ((pair (con ((pair (there here))
  ((pair (con ((pair here) refl)))
  refl)))) refl)))

----------------------------------------------------------------------

test-Two : Two ≡ Desc.Examples.Two
test-Two = refl

test-two : two ≡ Desc.Examples.two
test-two = refl

----------------------------------------------------------------------
