{-# OPTIONS --guarded #-}
module Clocked.Computation1 where

open import Prelude
open import Data.Empty
open import Data.Nat
open import Data.Nat.Two
open import Data.Nat.Order.Base
open import Data.Nat.Order.Inductive.Base using (_≤ᵇ_)
open import Data.Bool

open import Later

private variable
  ℓ : Level
  A : 𝒰 ℓ
  k : Cl

-- Megacz's computation monad aka trampoline (homogeneous version)

data gComp (k : Cl) (A : 𝒰 ℓ) : 𝒰 ℓ where
  retᵏ  : A → gComp k A
  bindᵏ : (A → ▹ k (gComp k A)) → ▹ k (gComp k A) → gComp k A

module gComp-code where

  Code-body : ▹ k (gComp k A → gComp k A → 𝒰 (level-of-type A))
            → gComp k A → gComp k A → 𝒰 (level-of-type A)
  Code-body     C▹ (retᵏ x)      (retᵏ y)      = x ＝ y
  Code-body     C▹ (retᵏ _)      (bindᵏ _ _)   = Lift _ ⊥
  Code-body     C▹ (bindᵏ _ _)   (retᵏ _)      = Lift _ ⊥
  Code-body {k} C▹ (bindᵏ kx x▹) (bindᵏ ky y▹) = ▸ k (C▹ ⊛ x▹ ⊛ y▹) × (∀ a → ▸ k (C▹ ⊛ kx a ⊛ ky a))

  Code : gComp k A → gComp k A → 𝒰 (level-of-type A)
  Code = fix Code-body

  Code-bb-eq : {kx ky : A → ▹ k (gComp k A)} {x▹ y▹ : ▹ k (gComp k A)}
             → Code (bindᵏ kx x▹) (bindᵏ ky y▹) ＝ (▸ k (Code ⍉ x▹ ⊛ y▹)) × (∀ a → ▸ k (Code ⍉ (kx a) ⊛ ky a))
  Code-bb-eq {k} {kx} {ky} {x▹} {y▹} i = (▹[ α ∶ k ] pfix Code-body i α (x▹ α) (y▹ α))
                                   × (∀ a → ▹[ α ∶ k ] pfix Code-body i α (kx a α) (ky a α))

  Code-bb⇉ : {kx ky : A → ▹ k (gComp k A)} {x▹ y▹ : ▹ k (gComp k A)}
           → Code (bindᵏ kx x▹) (bindᵏ ky y▹)
           → (▸ k (Code ⍉ x▹ ⊛ y▹)) × (∀ a → ▸ k (Code ⍉ (kx a) ⊛ ky a))
  Code-bb⇉ = transport Code-bb-eq

  ⇉Code-bb : {kx ky : A → ▹ k (gComp k A)} {x▹ y▹ : ▹ k (gComp k A)}
           → (▸ k (Code ⍉ x▹ ⊛ y▹)) × (∀ a → ▸ k (Code ⍉ (kx a) ⊛ ky a))
           → Code (bindᵏ kx x▹) (bindᵏ ky y▹)
  ⇉Code-bb = transport (sym Code-bb-eq)

  Code-refl-body : ▹ k ((c : gComp k A) → Code c c) → (c : gComp k A) → Code c c
  Code-refl-body C▹ (retᵏ x)      = refl
  Code-refl-body C▹ (bindᵏ kx x▹) = ⇉Code-bb ((C▹ ⊛ x▹) , λ a → C▹ ⊛ kx a)

  Code-refl : (c : gComp k A) → Code c c
  Code-refl = fix Code-refl-body

  encode : {p q : gComp k A} → p ＝ q → Code p q
  encode {p} {q} e = subst (Code p) e (Code-refl p)

  decode : ∀ (p q : gComp k A) → Code p q → p ＝ q
  decode (retᵏ x)      (retᵏ y)      c = ap retᵏ c
  decode (bindᵏ kx x▹) (bindᵏ ky y▹) c =
    let (ex , ek) = Code-bb⇉ c in
    ap² bindᵏ
      (fun-ext λ a → ▹-ext λ α → decode (kx a α) (ky a α) (ek a α))
      (▹-ext λ α → decode (x▹ α) (y▹ α) (ex α))

retᵏ≠bindᵏ : {x : A} {ky : A → ▹ k (gComp k A)} {y▹ : ▹ k (gComp k A)}
           → retᵏ x ≠ bindᵏ ky y▹
retᵏ≠bindᵏ = lower ∘ gComp-code.encode

retᵏ-inj : {x y : A}
         → retᵏ {k = k} x ＝ retᵏ y → x ＝ y
retᵏ-inj = gComp-code.encode

bindᵏ-inj : {kx ky : A → ▹ k (gComp k A)} {x▹ y▹ : ▹ k (gComp k A)}
          → bindᵏ kx x▹ ＝ bindᵏ ky y▹ → (x▹ ＝ y▹) × (kx ＝ ky)
bindᵏ-inj {kx} {ky} {x▹} {y▹} e =
  let (cx , ck) = gComp-code.Code-bb⇉ (gComp-code.encode e) in
    (▹-ext λ α → gComp-code.decode (x▹ α) (y▹ α) (cx α))
  , (fun-ext λ a → ▹-ext λ α → gComp-code.decode (kx a α) (ky a α) (ck a α))

callᵏ : ▹ k (gComp k A) → gComp k A
callᵏ = bindᵏ (next ∘ retᵏ)

δᵏ : gComp k A → gComp k A
δᵏ = callᵏ ∘ next

callω : gComp k A
callω = fix callᵏ

callWithᵏ : (A → A) → ▹ k (gComp k A) → gComp k A
callWithᵏ f = bindᵏ (next ∘ retᵏ ∘ f)

Comp : 𝒰 ℓ → 𝒰 ℓ
Comp A = ∀ k → gComp k A

ret  : A → Comp A
ret a k = retᵏ a

bind : (A → Comp A) → Comp A → Comp A
bind f c k = bindᵏ (λ b → next (f b k)) (next (c k))

ret≠bind : {x : A} {ky : A → Comp A} {y : Comp A}
         → ret x ≠ bind ky y
ret≠bind e = retᵏ≠bindᵏ (happly e k0)

ret-inj : {x y : A}
         → ret x ＝ ret y → x ＝ y
ret-inj e = retᵏ-inj (happly e k0)

bind-inj : {kx ky : A → Comp A} {x y : Comp A}
         → bind kx x ＝ bind ky y
         → (x ＝ y) × (kx ＝ ky)
bind-inj e =
    (fun-ext (force (λ k → ▹-ap (bindᵏ-inj (happly e k) .fst))))
  , fun-ext λ a → fun-ext (force λ k → ▹-ap (happly (bindᵏ-inj (happly e k) .snd) a))

-- examples

pow2ᵏ : ℕ → gComp k ℕ
pow2ᵏ = fix λ p▹ → λ where
  zero    → retᵏ 1
  (suc n) → if even n
              then callWithᵏ (2 ·_) (p▹ ⊛ next n)
              else callWithᵏ (λ x → x · x) (p▹ ⊛ next (n ÷2↑))

pow2 : ℕ → Comp ℕ
pow2 n k = pow2ᵏ n

gcdᵏ : ℕ → ℕ → gComp k ℕ
gcdᵏ = fix λ g▹ → λ where
  zero     m      → retᵏ m
  (suc n)  zero   → retᵏ (suc n)
  (suc n) (suc m) → if n ≤ᵇ m
                      then callᵏ (g▹ ⊛ next (suc n) ⊛ next (m ∸ n))
                      else callᵏ (g▹ ⊛ next (n ∸ m) ⊛ next (suc m))

gcd : ℕ → ℕ → Comp ℕ
gcd n m k = gcdᵏ n m

mccarthyᵏ : ℕ → gComp k ℕ
mccarthyᵏ = fix λ m▹ n →
  if n ≤ᵇ 100
    then bindᵏ (λ m → m▹ ⊛ next m) (m▹ ⊛ next (11 + n))
    else retᵏ (n ∸ 10)

mccarthy : ℕ → Comp ℕ
mccarthy n k = mccarthyᵏ n

