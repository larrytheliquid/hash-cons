{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product
  renaming (_,_ to pair)
open import Data.List
  hiding ( concat )
   renaming ([] to nil ; _∷_ to cons)
open import Data.String
open import Relation.Binary.PropositionalEquality
module PropositionalDesc where

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

ℕT : Enum
ℕT = cons "zero" (cons "suc" nil)

VecT : Enum
VecT = cons "vnil" (cons "vcons" nil)

ℕC : Tag ℕT → Desc ⊤
ℕC = caseD ℕT ⊤
  ( pair (`End tt)
   (pair (`Rec tt (`End tt))
   tt)
  )

ℕD : Desc ⊤
ℕD = `Arg (Tag ℕT) ℕC

ℕ : ⊤ → Set
ℕ = μ ⊤ ℕD

zero : ℕ tt
zero = con (pair here refl)

suc : ℕ tt → ℕ tt
suc n = con (pair (there here) (pair n refl))

one : ℕ tt
one = suc zero

two : ℕ tt
two = suc one

VecC : (A : Set) → Tag VecT → Desc (ℕ tt)
VecC A = caseD VecT (ℕ tt)
  ( pair (`End zero)
   (pair (`Arg (ℕ tt) (λ n → `Arg A λ _ → `Rec n (`End (suc n))))
    tt)
  )

VecD : (A : Set) → Desc (ℕ tt)
VecD A = `Arg (Tag VecT) (VecC A)

Vec : (A : Set) (n : ℕ tt) → Set
Vec A n = μ (ℕ tt) (VecD A) n

vnil : (A : Set) → Vec A zero
vnil A = con (pair here refl)

vcons : (A : Set) (n : ℕ tt) (x : A) (xs : Vec A n) → Vec A (suc n)
vcons A n x xs = con (pair (there here) (pair n (pair x (pair xs refl))))
 
----------------------------------------------------------------------

module Induction where

  add : ℕ tt → ℕ tt → ℕ tt
  add = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
    (λ u t,c → case ℕT
      (λ t → (c : El ⊤ (ℕC t) ℕ u)
             (ih : All ⊤ ℕD ℕ (λ u n → ℕ u → ℕ u) u (pair t c))
             → ℕ u → ℕ u
      )
      ( pair (λ q ih n → n)
       (pair (λ m,q ih,tt n → suc (proj₁ ih,tt n))
        tt)
      )
      (proj₁ t,c)
      (proj₂ t,c)
    )
    tt
  
  mult : ℕ tt → ℕ tt → ℕ tt
  mult = ind ⊤ ℕD (λ _ _ → ℕ tt → ℕ tt)
    (λ u t,c → case ℕT
      (λ t → (c : El ⊤ (ℕC t) ℕ u)
             (ih : All ⊤ ℕD ℕ (λ u n → ℕ u → ℕ u) u (pair t c))
             → ℕ u → ℕ u
      )
      ( pair (λ q ih n → zero)
       (pair (λ m,q ih,tt n → add n (proj₁ ih,tt n))
        tt)
      )
      (proj₁ t,c)
      (proj₂ t,c)
    )
    tt
  
  append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
  append A = ind (ℕ tt) (VecD A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
    (λ m t,c → case VecT
      (λ t → (c : El (ℕ tt) (VecC A t) (Vec A) m)
             (ih : All (ℕ tt) (VecD A) (Vec A) (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)) m (pair t c))
             (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
      )
      ( pair (λ q ih n ys → subst (λ m → Vec A (add m n)) q ys)
       (pair (λ m',x,xs,q ih,tt n ys →
          let m' = proj₁ m',x,xs,q
              x = proj₁ (proj₂ m',x,xs,q)
              q = proj₂ (proj₂ (proj₂ m',x,xs,q))
              ih = proj₁ ih,tt
          in
          subst (λ m → Vec A (add m n)) q (vcons A (add m' n) x (ih n ys))
        )
       tt)
      )
      (proj₁ t,c)
      (proj₂ t,c)
    )
  
  concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  concat A m = ind (ℕ tt) (VecD (Vec A m)) (λ n xss → Vec A (mult n m))
    (λ n t,c → case VecT
      (λ t → (c : El (ℕ tt) (VecC (Vec A m) t) (Vec (Vec A m)) n)
             (ih : All (ℕ tt) (VecD (Vec A m)) (Vec (Vec A m)) (λ n xss → Vec A (mult n m)) n (pair t c))
             → Vec A (mult n m)
      )
      ( pair (λ q ih → subst (λ n → Vec A (mult n m)) q (vnil A))
       (pair (λ n',xs,xss,q ih,tt →
          let n' = proj₁ n',xs,xss,q
              xs = proj₁ (proj₂ n',xs,xss,q)
              q = proj₂ (proj₂ (proj₂ n',xs,xss,q))
              ih = proj₁ ih,tt
          in
          subst (λ n → Vec A (mult n m)) q (append A m xs (mult n' m) ih)
        )
        tt)
      )
      (proj₁ t,c)
      (proj₂ t,c)
    )

----------------------------------------------------------------------

module Eliminator where

  elimℕ : (P : (ℕ tt) → Set)
    (pzero : P zero)
    (psuc : (m : ℕ tt) → P m → P (suc m))
    (n : ℕ tt)
    → P n
  elimℕ P pzero psuc = ind ⊤ ℕD (λ u n → P n)
    (λ u t,c → case ℕT
      (λ t → (c : El ⊤ (ℕC t) ℕ u)
             (ih : All ⊤ ℕD ℕ (λ u n → P n) u (pair t c))
             → P (con (pair t c))
      )
      ( pair (λ q ih →
          elimEq ⊤ tt (λ u q → P (con (pair here q)))
            pzero
            u q
        )
        (pair (λ n,q ih,tt →
          elimEq ⊤ tt (λ u q → P (con (pair (there here) (pair (proj₁ n,q) q))))
            (psuc (proj₁ n,q) (proj₁ ih,tt))
            u (proj₂ n,q)
        )
        tt)
      )
      (proj₁ t,c)
      (proj₂ t,c)
    )
    tt

  elimVec : (A : Set) (P : (n : ℕ tt) → Vec A n → Set)
    (pvnil : P zero (vnil A))
    (pvcons : (n : ℕ tt) (a : A) (xs : Vec A n) → P n xs → P (suc n) (vcons A n a xs))
    (n : ℕ tt)
    (xs : Vec A n)
    → P n xs
  elimVec A P pvnil pvcons = ind (ℕ tt) (VecD A) (λ n xs → P n xs)
    (λ n t,c → case VecT
      (λ t → (c : El (ℕ tt) (VecC A t) (Vec A) n)
             (ih : All (ℕ tt) (VecD A) (Vec A) (λ n xs → P n xs) n (pair t c))
             → P n (con (pair t c))
      )
      ( pair (λ q ih →
          elimEq (ℕ tt) zero (λ n q → P n (con (pair here q)))
            pvnil
            n q
        )
        (pair (λ n',x,xs,q ih,tt →
          let n' = proj₁ n',x,xs,q
              x = proj₁ (proj₂ n',x,xs,q)
              xs = proj₁ (proj₂ (proj₂ n',x,xs,q))
              q = proj₂ (proj₂ (proj₂ n',x,xs,q))
              ih = proj₁ ih,tt
          in
          elimEq (ℕ tt) (suc n') (λ n q → P n (con (pair (there here) (pair n' (pair x (pair xs q))))))
            (pvcons n' x xs ih )
            n q
        )
        tt)
      )
      (proj₁ t,c)
      (proj₂ t,c)
    )

----------------------------------------------------------------------

  add : ℕ tt → ℕ tt → ℕ tt
  add = elimℕ (λ _ → ℕ tt → ℕ tt)
    (λ n → n)
    (λ m ih n → suc (ih n))

  mult : ℕ tt → ℕ tt → ℕ tt
  mult = elimℕ (λ _ → ℕ tt → ℕ tt)
    (λ n → zero)
    (λ m ih n → add n (ih n))

  append : (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n)
  append A = elimVec A (λ m xs → (n : ℕ tt) (ys : Vec A n) → Vec A (add m n))
    (λ n ys → ys)
    (λ m x xs ih n ys → vcons A (add m n) x (ih n ys))

  concat : (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  concat A m = elimVec (Vec A m) (λ n xss → Vec A (mult n m))
    (vnil A)
    (λ n xs xss ih → append A m xs (mult n m) ih)
    
----------------------------------------------------------------------
