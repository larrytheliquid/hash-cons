{-# OPTIONS --type-in-type #-}
module Desc.Mult where
open import Desc
import Desc.Examples

----------------------------------------------------------------------

Mult : Set
Mult =
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

mult : Desc.Examples.Induction.Mult
mult =
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
  → (λ ih → (λ n → (con ((pair
  here) refl)))))) ((pair (λ m,q →
  (λ ih,tt → (λ n → (((((((ind ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t)))) (λ _
  → (λ _ → ((_ : (((μ ⊤) ((`Arg
  (Tag ((cons "zero") ((cons
  "suc") nil)))) (λ t → ((((case
  ((cons "zero") ((cons "suc")
  nil))) (λ _ → (Desc ⊤))) ((pair
  (`End tt)) ((pair ((`Rec tt)
  (`End tt))) tt))) t)))) tt)) →
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)))) tt))))) (λ u₁ → (λ
  t,c₁ → (((((case ((cons "zero")
  ((cons "suc") nil))) (λ t → ((c
  : ((((El ⊤) ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)) ((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₁ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁))))) u₁)) → ((_ :
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
  tt))) t₁))))) (λ u₂ → (λ n₁ →
  ((_ : (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) u₂)) → (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₁ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₁))))
  u₂))))) u₁) c)) → ((_ : (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₁ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₁))))
  u₁)) → (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₁ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) u₁)))))) ((pair (λ
  q → (λ ih → (λ n₁ → n₁))))
  ((pair (λ m,q₁ → (λ ih,tt₁ → (λ
  n₁ → (con ((pair (there here))
  ((pair ((proj₁ ih,tt₁) n₁))
  refl))))))) tt))) (proj₁ t,c₁))
  (proj₂ t,c₁))))) tt) n) ((proj₁
  ih,tt) n)))))) tt))) (proj₁
  t,c)) (proj₂ t,c))))) tt)

----------------------------------------------------------------------

test-Mult : Mult ≡ Desc.Examples.Induction.Mult
test-Mult = refl

test-mult : mult ≡ Desc.Examples.Induction.mult
test-mult = refl

----------------------------------------------------------------------
