{-# OPTIONS --type-in-type #-}
module Desc.Append where
open import Desc
import Desc.Examples

----------------------------------------------------------------------

Append : Set
Append =
  ((A : Set) → ((m : (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t)))) tt))
  → ((_ : (((μ (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
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
  n → ((`Arg A) (λ _ → ((`Rec n)
  (`End (con ((pair (there here))
  ((pair n) refl)))))))))) tt)))
  t)))) m)) → ((n : (((μ ⊤) ((`Arg
  (Tag ((cons "zero") ((cons
  "suc") nil)))) (λ t → ((((case
  ((cons "zero") ((cons "suc")
  nil))) (λ _ → (Desc ⊤))) ((pair
  (`End tt)) ((pair ((`Rec tt)
  (`End tt))) tt))) t)))) tt)) →
  ((_ : (((μ (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
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
  n₁ → ((`Arg A) (λ _ → ((`Rec n₁)
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
  → (λ ih → (λ n₁ → n₁)))) ((pair
  (λ m,q → (λ ih,tt → (λ n₁ → (con
  ((pair (there here)) ((pair
  ((proj₁ ih,tt) n₁)) refl)))))))
  tt))) (proj₁ t,c)) (proj₂
  t,c))))) tt) m) n)))))))

----------------------------------------------------------------------

append : Desc.Examples.Induction.Append
append =
  (λ A → ((((ind (((μ ⊤) ((`Arg
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
  n → ((`Arg A) (λ _ → ((`Rec n)
  (`End (con ((pair (there here))
  ((pair n) refl)))))))))) tt)))
  t)))) (λ m → (λ xs → ((n : (((μ
  ⊤) ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t)))) tt))
  → ((_ : (((μ (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
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
  n₁ → ((`Arg A) (λ _ → ((`Rec n₁)
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
  → (λ ih → (λ n₁ → n₁)))) ((pair
  (λ m,q → (λ ih,tt → (λ n₁ → (con
  ((pair (there here)) ((pair
  ((proj₁ ih,tt) n₁)) refl)))))))
  tt))) (proj₁ t,c)) (proj₂
  t,c))))) tt) m) n))))))) (λ m →
  (λ t,c → (((((case ((cons
  "vnil") ((cons "vcons") nil)))
  (λ t → ((c : ((((El (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₁ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₁))))
  tt)) ((((case ((cons "vnil")
  ((cons "vcons") nil))) (λ _ →
  (Desc (((μ ⊤) ((`Arg (Tag ((cons
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
  n → ((`Arg A) (λ _ → ((`Rec n)
  (`End (con ((pair (there here))
  ((pair n) refl)))))))))) tt)))
  t)) (λ n → (((μ (((μ ⊤) ((`Arg
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
  n₁ → ((`Arg A) (λ _ → ((`Rec n₁)
  (`End (con ((pair (there here))
  ((pair n₁) refl)))))))))) tt)))
  t₁)))) n))) m)) → ((_ :
  ((((((All (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₁ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)) ((((case
  ((cons "vnil") ((cons "vcons")
  nil))) (λ _ → (Desc (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₁ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₁))))
  tt)))) ((pair (`End (con ((pair
  here) refl)))) ((pair ((`Arg
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)) (λ n → ((`Arg
  A) (λ _ → ((`Rec n) (`End (con
  ((pair (there here)) ((pair n)
  refl)))))))))) tt))) t)) (λ n →
  (((μ (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)) ((`Arg (Tag
  ((cons "vnil") ((cons "vcons")
  nil)))) (λ t₁ → ((((case ((cons
  "vnil") ((cons "vcons") nil)))
  (λ _ → (Desc (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₂ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
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
  n₁ → ((`Arg A) (λ _ → ((`Rec n₁)
  (`End (con ((pair (there here))
  ((pair n₁) refl)))))))))) tt)))
  t₁)))) n))) (λ m₁ → (λ xs → ((n
  : (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)) → ((_ : (((μ
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)) ((`Arg (Tag
  ((cons "vnil") ((cons "vcons")
  nil)))) (λ t₁ → ((((case ((cons
  "vnil") ((cons "vcons") nil)))
  (λ _ → (Desc (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₂ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
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
  n₁ → ((`Arg A) (λ _ → ((`Rec n₁)
  (`End (con ((pair (there here))
  ((pair n₁) refl)))))))))) tt)))
  t₁)))) n)) → (((μ (((μ ⊤) ((`Arg
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
  n₁ → ((`Arg A) (λ _ → ((`Rec n₁)
  (`End (con ((pair (there here))
  ((pair n₁) refl)))))))))) tt)))
  t₁)))) (((((((ind ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₁ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) (λ _ → (λ _ → ((_ :
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)) → (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₁ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₁))))
  tt))))) (λ u → (λ t,c₁ →
  (((((case ((cons "zero") ((cons
  "suc") nil))) (λ t₁ → ((c₁ :
  ((((El ⊤) ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)) ((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₂ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₂))))) u)) → ((_ :
  ((((((All ⊤) ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)) ((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₂ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₂))))) (λ u₁ → (λ n₁ →
  ((_ : (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₂ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₂)))) u₁)) → (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₂ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₂))))
  u₁))))) u) c₁)) → ((_ : (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₂ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₂)))) u))
  → (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₂ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₂)))) u)))))) ((pair (λ q
  → (λ ih → (λ n₁ → n₁)))) ((pair
  (λ m,q → (λ ih,tt → (λ n₁ → (con
  ((pair (there here)) ((pair
  ((proj₁ ih,tt) n₁)) refl)))))))
  tt))) (proj₁ t,c₁)) (proj₂
  t,c₁))))) tt) m₁) n))))))) m)
  c)) → ((n : (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₁ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)) → ((_ : (((μ
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)) ((`Arg (Tag
  ((cons "vnil") ((cons "vcons")
  nil)))) (λ t₁ → ((((case ((cons
  "vnil") ((cons "vcons") nil)))
  (λ _ → (Desc (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₂ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
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
  n₁ → ((`Arg A) (λ _ → ((`Rec n₁)
  (`End (con ((pair (there here))
  ((pair n₁) refl)))))))))) tt)))
  t₁)))) n)) → (((μ (((μ ⊤) ((`Arg
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
  n₁ → ((`Arg A) (λ _ → ((`Rec n₁)
  (`End (con ((pair (there here))
  ((pair n₁) refl)))))))))) tt)))
  t₁)))) (((((((ind ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₁ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) (λ _ → (λ _ → ((_ :
  (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₁ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)))) tt)) → (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₁ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₁))))
  tt))))) (λ u → (λ t,c₁ →
  (((((case ((cons "zero") ((cons
  "suc") nil))) (λ t₁ → ((c₁ :
  ((((El ⊤) ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)) ((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₂ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₂))))) u)) → ((_ :
  ((((((All ⊤) ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₁)) ((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t₂ → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₂))))) (λ u₁ → (λ n₁ →
  ((_ : (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₂ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₂)))) u₁)) → (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₂ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₂))))
  u₁))))) u) c₁)) → ((_ : (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t₂ →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t₂)))) u))
  → (((μ ⊤) ((`Arg (Tag ((cons
  "zero") ((cons "suc") nil)))) (λ
  t₂ → ((((case ((cons "zero")
  ((cons "suc") nil))) (λ _ →
  (Desc ⊤))) ((pair (`End tt))
  ((pair ((`Rec tt) (`End tt)))
  tt))) t₂)))) u)))))) ((pair (λ q
  → (λ ih → (λ n₁ → n₁)))) ((pair
  (λ m,q → (λ ih,tt → (λ n₁ → (con
  ((pair (there here)) ((pair
  ((proj₁ ih,tt) n₁)) refl)))))))
  tt))) (proj₁ t,c₁)) (proj₂
  t,c₁))))) tt) m) n))))))))
  ((pair (λ q → (λ ih → (λ n →
  ((subst (λ m₁ → (((μ (((μ ⊤)
  ((`Arg (Tag ((cons "zero")
  ((cons "suc") nil)))) (λ t →
  ((((case ((cons "zero") ((cons
  "suc") nil))) (λ _ → (Desc ⊤)))
  ((pair (`End tt)) ((pair ((`Rec
  tt) (`End tt))) tt))) t)))) tt))
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
  tt))))) (λ u → (λ t,c₁ →
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
  tt))) t₁)))) u)))))) ((pair (λ
  q₁ → (λ ih₁ → (λ n₁ → n₁))))
  ((pair (λ m,q → (λ ih,tt → (λ n₁
  → (con ((pair (there here))
  ((pair ((proj₁ ih,tt) n₁))
  refl))))))) tt))) (proj₁ t,c₁))
  (proj₂ t,c₁))))) tt) m₁) n))))
  q))))) ((pair (λ m',x,xs,q → (λ
  ih,tt → (λ n → (λ ys → (((subst
  (λ m₁ → (((μ (((μ ⊤) ((`Arg (Tag
  ((cons "zero") ((cons "suc")
  nil)))) (λ t → ((((case ((cons
  "zero") ((cons "suc") nil))) (λ
  _ → (Desc ⊤))) ((pair (`End tt))
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
  tt))))) (λ u → (λ t,c₁ →
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
  → (λ ih → (λ n₁ → n₁)))) ((pair
  (λ m,q → (λ ih,tt₁ → (λ n₁ →
  (con ((pair (there here)) ((pair
  ((proj₁ ih,tt₁) n₁)) refl)))))))
  tt))) (proj₁ t,c₁)) (proj₂
  t,c₁))))) tt) m₁) n)))) (proj₂
  (proj₂ (proj₂ m',x,xs,q)))) (con
  ((pair (there here)) ((pair
  (((((((ind ⊤) ((`Arg (Tag ((cons
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
  tt))))) (λ u → (λ t,c₁ →
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
  → (λ ih → (λ n₁ → n₁)))) ((pair
  (λ m,q → (λ ih,tt₁ → (λ n₁ →
  (con ((pair (there here)) ((pair
  ((proj₁ ih,tt₁) n₁)) refl)))))))
  tt))) (proj₁ t,c₁)) (proj₂
  t,c₁))))) tt) (proj₁ m',x,xs,q))
  n)) ((pair (proj₁ (proj₂
  m',x,xs,q))) ((pair (((proj₁
  ih,tt) n) ys)) refl)))))))))))
  tt))) (proj₁ t,c)) (proj₂
  t,c))))))

----------------------------------------------------------------------

test-Append : Append ≡ Desc.Examples.Induction.Append
test-Append = refl

test-append : append ≡ Desc.Examples.Induction.append
test-append = refl

----------------------------------------------------------------------
