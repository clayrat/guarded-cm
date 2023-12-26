{-# OPTIONS --guarded #-}
module Guarded.Computation1 where

open import Prelude
open import Data.Empty
open import Data.Nat
open import Data.Nat.Two
open import Data.Nat.Order.Base
open import Data.Bool

open import LaterG

private variable
  ℓ : Level
  A : 𝒰 ℓ

-- Megacz's computation monad aka trampoline (homogeneous version)

data Comp (A : 𝒰 ℓ) : 𝒰 ℓ where
  ret  : A → Comp A
  bind : (A → ▹ Comp A) → ▹ Comp A → Comp A

module Comp-code where

  Code-body : ▹ (Comp A → Comp A → 𝒰 (level-of-type A))
            → Comp A → Comp A → 𝒰 (level-of-type A)
  Code-body C▹ (ret x)      (ret y)      = x ＝ y
  Code-body C▹ (ret _)      (bind _ _)   = Lift _ ⊥
  Code-body C▹ (bind _ _)   (ret _)      = Lift _ ⊥
  Code-body C▹ (bind kx x▹) (bind ky y▹) = ▸ (C▹ ⊛ x▹ ⊛ y▹) × (∀ a → ▸ (C▹ ⊛ kx a ⊛ ky a))

  Code : Comp A → Comp A → 𝒰 (level-of-type A)
  Code = fix Code-body

  Code-bb-eq : {kx ky : A → ▹ Comp A} {x▹ y▹ : ▹ Comp A}
             → Code (bind kx x▹) (bind ky y▹) ＝ (▸ (▹map Code x▹ ⊛ y▹)) × (∀ a → ▸ (▹map Code (kx a) ⊛ ky a))
  Code-bb-eq {kx} {ky} {x▹} {y▹} i = (▹[ α ] pfix Code-body i α (x▹ α) (y▹ α))
                                   × (∀ a → ▹[ α ] pfix Code-body i α (kx a α) (ky a α))

  Code-bb⇉ : {kx ky : A → ▹ Comp A} {x▹ y▹ : ▹ Comp A}
           → Code (bind kx x▹) (bind ky y▹)
           → (▸ (▹map Code x▹ ⊛ y▹)) × (∀ a → ▸ (▹map Code (kx a) ⊛ ky a))
  Code-bb⇉ = transport Code-bb-eq

  ⇉Code-bb : {kx ky : A → ▹ Comp A} {x▹ y▹ : ▹ Comp A}
           → (▸ (▹map Code x▹ ⊛ y▹)) × (∀ a → ▸ (▹map Code (kx a) ⊛ ky a))
           → Code (bind kx x▹) (bind ky y▹)
  ⇉Code-bb = transport (sym Code-bb-eq)

  Code-refl-body : ▹ ((c : Comp A) → Code c c) → (c : Comp A) → Code c c
  Code-refl-body C▹ (ret x)      = refl
  Code-refl-body C▹ (bind kx x▹) = ⇉Code-bb ((C▹ ⊛ x▹) , λ a → C▹ ⊛ kx a)

  Code-refl : (c : Comp A) → Code c c
  Code-refl = fix Code-refl-body

  encode : {p q : Comp A} → p ＝ q → Code p q
  encode {p} {q} e = subst (Code p) e (Code-refl p)

  decode : ∀ (p q : Comp A) → Code p q → p ＝ q
  decode (ret x)      (ret y)      c = ap ret c
  decode (bind kx x▹) (bind ky y▹) c =
    let (ex , ek) = Code-bb⇉ c in
    ap² bind
      (fun-ext λ a → ▹-ext λ α → decode (kx a α) (ky a α) (ek a α))
      (▹-ext λ α → decode (x▹ α) (y▹ α) (ex α))

ret-inj : {x y : A}
        → ret x ＝ ret y → x ＝ y
ret-inj = Comp-code.encode

bind-inj : {kx ky : A → ▹ Comp A} {x▹ y▹ : ▹ Comp A}
         → bind kx x▹ ＝ bind ky y▹ → (x▹ ＝ y▹) × (kx ＝ ky)
bind-inj {kx} {ky} {x▹} {y▹} e =
  let (cx , ck) = Comp-code.Code-bb⇉ (Comp-code.encode e) in
    (▹-ext λ α → Comp-code.decode (x▹ α) (y▹ α) (cx α))
  , (fun-ext λ a → ▹-ext λ α → Comp-code.decode (kx a α) (ky a α) (ck a α))

call : ▹ Comp A → Comp A
call = bind (next ∘ ret)

δᶜ : Comp A → Comp A
δᶜ = call ∘ next

callω : Comp A
callω = fix call

callWith : (A → A) → ▹ Comp A → Comp A
callWith f = bind (next ∘ ret ∘ f)

-- examples

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
