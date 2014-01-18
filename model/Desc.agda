{-# OPTIONS --type-in-type #-}
module Desc where
open import Data.Unit public
  using ( ⊤ ; tt )
open import Data.Product public
  using ( Σ ; _×_ ; proj₁ ; proj₂ )
  renaming (_,_ to pair)
open import Data.List public
  using ( List )
  renaming ([] to nil ; _∷_ to cons)
open import Data.String public
  using ( String )
open import Relation.Binary.PropositionalEquality public
  using ( _≡_ ; refl ; subst )

----------------------------------------------------------------------

elimEq : (A : Set) (x : A) (P : (y : A) → x ≡ y → Set)
  → P x refl
  → (y : A) (p : x ≡ y) → P y p
elimEq A .x P prefl x refl = prefl

----------------------------------------------------------------------

Label : Set
Label = String

Enum : Set
Enum = List Label

data Tag : Enum → Set where
  here : ∀{l E} → Tag (cons l E)
  there : ∀{l E} → Tag E → Tag (cons l E)

Cases : (E : Enum) (P : Tag E → Set) → Set
Cases nil P = ⊤
Cases (cons l E) P = P here × Cases E λ t → P (there t)

case : (E : Enum) (P : Tag E → Set) (cs : Cases E P) (t : Tag E) → P t
case (cons l E) P (pair c cs) here = c
case (cons l E) P (pair c cs) (there t) = case E (λ t → P (there t)) cs t

----------------------------------------------------------------------

data Desc (I : Set) : Set₁ where
  `End : (i : I) → Desc I
  `Rec : (i : I) (D : Desc I) → Desc I
  `Arg : (A : Set) (B : A → Desc I) → Desc I
  `RecFun : (A : Set) (B : A → I) (D : Desc I) → Desc I

ISet : Set → Set₁
ISet I = I → Set

El : (I : Set) (D : Desc I) (X : ISet I) → ISet I
El I (`End j) X i = j ≡ i
El I (`Rec j D) X i = X j × El I D X i
El I (`Arg A B) X i = Σ A (λ a → El I (B a) X i)
El I (`RecFun A B D) X i = ((a : A) → X (B a)) × El I D X i

data μ (I : Set) (D : Desc I) (i : I) : Set where
  con : El I D (μ I D) i → μ I D i

All : (I : Set) (D : Desc I) (X : ISet I) (P : (i : I) → X i → Set) (i : I) (xs : El I D X i) → Set
All I (`End j) X P i q = ⊤
All I (`Rec j D) X P i (pair x xs) = P j x × All I D X P i xs
All I (`Arg A B) X P i (pair a b) = All I (B a) X P i b
All I (`RecFun A B D) X P i (pair f xs) = ((a : A) → P (B a) (f a)) × All I D X P i xs

caseD : (E : Enum) (I : Set) (cs : Cases E (λ _ → Desc I)) (t : Tag E) → Desc I
caseD E I cs t = case E (λ _ → Desc I) cs t

----------------------------------------------------------------------

ind :
  (I : Set)
  (D : Desc I)
  (P : (i : I) → μ I D i → Set)
  (pcon : (i : I) (xs : El I D (μ I D) i) → All I D (μ I D) P i xs → P i (con xs))
  (i : I)
  (x : μ I D i)
  → P i x

hyps :
  (I : Set)
  (D₁ : Desc I)
  (P : (i : I) → μ I D₁ i → Set)
  (pcon : (i : I) (xs : El I D₁ (μ I D₁) i) → All I D₁ (μ I D₁) P i xs → P i (con xs))
  (D₂ : Desc I)
  (i : I)
  (xs : El I D₂ (μ I D₁) i)
  → All I D₂ (μ I D₁) P i xs

ind I D P pcon i (con xs) = pcon i xs (hyps I D P pcon D i xs)

hyps I D P pcon (`End j) i q = tt
hyps I D P pcon (`Rec j A) i (pair x xs) = pair (ind I D P pcon j x) (hyps I D P pcon A i xs)
hyps I D P pcon (`Arg A B) i (pair a b) = hyps I D P pcon (B a) i b
hyps I D P pcon (`RecFun A B E) i (pair f xs) = pair (λ a → ind I D P pcon (B a) (f a)) (hyps I D P pcon E i xs)

----------------------------------------------------------------------

