{-# OPTIONS --type-in-type #-}
module Desc.Add where
open import Desc
import Desc.Examples

----------------------------------------------------------------------

Add : Set
Add =
  ((_ : (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)))) tt)) → ((_ : (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t)))) tt))
  → (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)))) tt)))

----------------------------------------------------------------------

add : Desc.Examples.Induction.Add
add =
  (((((ind ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)))) (λ _ → (λ _ → ((_ :
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)))) tt)) → (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t))))
  tt))))) (λ u → (λ t,c →
  (((((case ((cons "zero") ((cons
  "suc") nil))) (λ t → ((c :
  ((((El ⊤) ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)) ((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₁ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁))))) u)) → ((_ :
  ((((((All ⊤) ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)) ((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₁ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁))))) (λ u₁ → (λ n → ((_
  : (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) u₁)) → (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₁ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₁))))
  u₁))))) u) c)) → ((_ : (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₁ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₁)))) u))
  → (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) u)))))) ((pair (λ q
  → (λ ih → (λ n → n)))) ((pair (λ
  m,q → (λ ih,tt → (λ n → (con
  ((pair (there here)) ((pair
  ((proj₁ ih,tt) n)) refl)))))))
  tt))) (proj₁ t,c)) (proj₂
  t,c))))) tt)

----------------------------------------------------------------------

test-Add : Add ≡ Desc.Examples.Induction.Add
test-Add = refl

test-add : add ≡ Desc.Examples.Induction.add
test-add = refl

----------------------------------------------------------------------
