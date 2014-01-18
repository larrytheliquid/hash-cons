{-# OPTIONS --type-in-type #-}
module Desc.Examples where
open import Desc

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

Two : Set
Two = ℕ tt

two : Two
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

  Add : Set
  Add = ℕ tt → ℕ tt → ℕ tt

  add : Add
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
  
  Mult : Set
  Mult = Add

  mult : Mult
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

  Append : Set
  Append = (A : Set) (m : ℕ tt) (xs : Vec A m) (n : ℕ tt) (ys : Vec A n) → Vec A (add m n) 
  
  append : Append
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

  Concat : Set
  Concat = (A : Set) (m n : ℕ tt) (xss : Vec (Vec A m) n) → Vec A (mult n m)
  
  concat : Concat
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
