{-# OPTIONS --type-in-type #-}
module Desc.Concat where
open import Desc
import Desc.Examples

----------------------------------------------------------------------

Concat : Set
Concat =
  ((A : Set) → ((m : (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t)))) tt))
  → ((n : (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)))) tt)) → ((_ : (((μ
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t)))) tt)) ((`Arg (Tag
  ((cons "vnil") ((cons "vcons")
  nil)))) (λ t → ((((case ((cons
  "vnil") ((cons "vcons") nil)))
  (λ _ → (Desc (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₁ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)))) ((pair (`End
  (con ((pair here) refl))))
  ((pair ((`Arg (((μ ⊤) ((`Arg
  (Tag ((cons "zero") ((cons
  "suc") nil)))) (λ t₁ → ((((case
  ((cons "zero") ((cons "suc")
  nil))) (λ _ → (Desc ⊤))) ((pair
  (`End tt)) ((pair ((`Rec tt)
  (`End tt))) tt))) t₁)))) tt)) (λ
  n₁ → ((`Arg (((μ (((μ ⊤) ((`Arg
  (Tag ((cons "zero") ((cons
  "suc") nil)))) (λ t₁ → ((((case
  ((cons "zero") ((cons "suc")
  nil))) (λ _ → (Desc ⊤))) ((pair
  (`End tt)) ((pair ((`Rec tt)
  (`End tt))) tt))) t₁)))) tt))
  ((`Arg (Tag ((cons "vnil")
  ((cons "vcons") nil)))) (λ t₁ →
  ((((case ((cons "vnil") ((cons
  "vcons") nil))) (λ _ → (Desc
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₂ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₂)))) tt)))) ((pair (`End
  (con ((pair here) refl))))
  ((pair ((`Arg (((μ ⊤) ((`Arg
  (Tag ((cons "zero") ((cons
  "suc") nil)))) (λ t₂ → ((((case
  ((cons "zero") ((cons "suc")
  nil))) (λ _ → (Desc ⊤))) ((pair
  (`End tt)) ((pair ((`Rec tt)
  (`End tt))) tt))) t₂)))) tt)) (λ
  n₂ → ((`Arg A) (λ _ → ((`Rec n₂)
  (`End (con ((pair (there here))
  ((pair n₂) refl)))))))))) tt)))
  t₁)))) m)) (λ _ → ((`Rec n₁)
  (`End (con ((pair (there here))
  ((pair n₁) refl)))))))))) tt)))
  t)))) n)) → (((μ (((μ ⊤) ((`Arg
  (Tag ((cons "zero") ((cons
  "suc") nil)))) (λ t → ((((case
  ((cons "zero") ((cons "suc")
  nil))) (λ _ → (Desc ⊤))) ((pair
  (`End tt)) ((pair ((`Rec tt)
  (`End tt))) tt))) t)))) tt))
  ((`Arg (Tag ((cons "vnil")
  ((cons "vcons") nil)))) (λ t →
  ((((case ((cons "vnil") ((cons
  "vcons") nil))) (λ _ → (Desc
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)))) ((pair (`End
  (con ((pair here) refl))))
  ((pair ((`Arg (((μ ⊤) ((`Arg
  (Tag ((cons "zero") ((cons
  "suc") nil)))) (λ t₁ → ((((case
  ((cons "zero") ((cons "suc")
  nil))) (λ _ → (Desc ⊤))) ((pair
  (`End tt)) ((pair ((`Rec tt)
  (`End tt))) tt))) t₁)))) tt)) (λ
  n₁ → ((`Arg A) (λ _ → ((`Rec n₁)
  (`End (con ((pair (there here))
  ((pair n₁) refl)))))))))) tt)))
  t)))) (((((((ind ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
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
  tt))) t₁))))) (λ u₁ → (λ n₁ →
  ((_ : (((μ ⊤) ((`Arg (Tag ((cons
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
  → (λ ih → (λ n₁ → (con ((pair
  here) refl)))))) ((pair (λ m,q →
  (λ ih,tt → (λ n₁ → (((((((ind ⊤)
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
  tt))) t₁))))) (λ u₂ → (λ n₂ →
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
  q → (λ ih → (λ n₂ → n₂))))
  ((pair (λ m,q₁ → (λ ih,tt₁ → (λ
  n₂ → (con ((pair (there here))
  ((pair ((proj₁ ih,tt₁) n₂))
  refl))))))) tt))) (proj₁ t,c₁))
  (proj₂ t,c₁))))) tt) n₁) ((proj₁
  ih,tt) n₁)))))) tt))) (proj₁
  t,c)) (proj₂ t,c))))) tt) n)
  m))))))

----------------------------------------------------------------------

concat : Desc.Examples.Induction.Concat
concat = {!!}

----------------------------------------------------------------------

test-Concat : Concat ≡ Desc.Examples.Induction.Concat
test-Concat = refl

test-concat : concat ≡ Desc.Examples.Induction.concat
test-concat = {!!}

----------------------------------------------------------------------
