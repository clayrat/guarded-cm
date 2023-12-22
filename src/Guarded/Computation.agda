{-# OPTIONS --guarded #-}
module Guarded.Computation where

open import Prelude
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Bool

open import LaterG

private variable
  ℓ : Level
  A B : 𝒰 ℓ

-- Megacz's computation monad aka trampoline

data Comp (A : 𝒰 ℓ) : 𝒰 (ℓsuc ℓ) where
  ret  : A → Comp A
  bind : ∀ {B : 𝒰 ℓ}
       → (B → ▹ Comp A) → ▹ Comp B → Comp A

call : ▹ Comp A → Comp A
call = bind (next ∘ ret)

δᶜ : Comp A → Comp A
δᶜ = call ∘ next

callω : Comp A
callω = fix call

thunk : ▹ Comp A → Comp A
thunk c▹ = bind (λ _ → c▹) (next (ret (lift tt)))

thunkω : Comp A
thunkω = fix thunk

callWith : ∀ {A B : 𝒰 ℓ}
         → (A → B) → ▹ Comp A → Comp B
callWith f = bind (next ∘ ret ∘ f)

mapᶜ : ∀ {A B : 𝒰 ℓ}
     → (A → B) → Comp A → Comp B
mapᶜ f = callWith f ∘ next

apᶜ : ∀ {A B : 𝒰 ℓ}
    → Comp (A → B) → Comp A → Comp B
apᶜ cf ca = bind (λ f → next (mapᶜ f ca)) (next cf)    

_>>=ᶜ_ : ∀ {A B : 𝒰 ℓ}
       → Comp A → (A → Comp B) → Comp B
c >>=ᶜ f = bind (next ∘ f) (next c)

-- examples

-- TODO upstream

odd : ℕ → Bool
odd  zero   = false
odd (suc n) = not (odd n)

even : ℕ → Bool
even = not ∘ odd

mutual
 _÷2 : ℕ → ℕ
 zero ÷2    = zero
 (suc n) ÷2 = n ÷2↑

 _÷2↑ : ℕ → ℕ
 zero ÷2↑   = zero
 (suc n) ÷2↑ = suc (n ÷2)

pow2 : ℕ → Comp ℕ
pow2 = fix λ p▹ → λ where
  zero    → ret 1
  (suc n) → if even n
              then callWith (2 ·_) (p▹ ⊛ next n)
              else callWith (λ x → x · x) (p▹ ⊛ next (n ÷2↑) )

gcd : ℕ → ℕ → Comp ℕ
gcd = fix λ g▹ → λ where
  zero     m      → ret m
  (suc n)  zero   → ret (suc n)
  (suc n) (suc m) → if n ≤ᵇ m
                      then call (g▹ ⊛ next (suc n) ⊛ next (m ∸ n))
                      else call (g▹ ⊛ next (n ∸ m) ⊛ next (suc m)) 

mccarthy : ℕ → Comp ℕ
mccarthy = fix λ m▹ n →
  if n ≤ᵇ 100
    then bind (λ m → m▹ ⊛ next m) (m▹ ⊛ next (11 + n))
    else ret (n ∸ 10)
