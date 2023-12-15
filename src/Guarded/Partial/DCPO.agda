{-# OPTIONS --guarded #-}
module Guarded.Partial.DCPO where

open import Prelude
open import Data.Empty

open import LaterG
open import Guarded.Partial

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

-- TODO "weak convergence"? what's the domain-theoretic name for this?

data _⊑ᵖ_ {ℓ} {A : 𝒰 ℓ} : Part A → A → 𝒰 ℓ where
  n⊑ᵖ : ∀ {x y}
      → x ＝ y
      → now x ⊑ᵖ y
  l⊑ᵖ : ∀ {m▹ y}
      → ▹[ α ] (m▹ α ⊑ᵖ y)
      → later m▹ ⊑ᵖ y

-- TODO general hlevel?
⊑-prop : is-set A
       → (a : A) → (p : Part A)
       → is-prop (p ⊑ᵖ a)
⊑-prop sA a = fix λ ih▹ → λ where
  (now x)    → is-prop-η λ where (n⊑ᵖ e₁)  (n⊑ᵖ e₂)  → ap n⊑ᵖ (is-set-β sA x a e₁ e₂)
  (later p▹) → is-prop-η λ where (l⊑ᵖ p▹₁) (l⊑ᵖ p▹₂) → ap l⊑ᵖ (is-prop-β (▹is-prop (ih▹ ⊛ p▹)) p▹₁ p▹₂)

never⊑ : (a : A) → never ⊑ᵖ a
never⊑ a = fix λ ih▹ → l⊑ᵖ λ α → transport (λ i → pfix later (~ i) α ⊑ᵖ a) (ih▹ α)

-- partial order

data _≤ᵖ_ {ℓ} {A : 𝒰 ℓ} : Part A → Part A → 𝒰 ℓ where
  ≤ᵖn  : ∀ {p x}
       → p ⊑ᵖ x
       → p ≤ᵖ now x
  l≤ᵖl : ∀ {m▹ n▹}
       → ▹[ α ] (m▹ α ≤ᵖ n▹ α)
       → later m▹ ≤ᵖ later n▹

¬now≤later : {x : A} {p▹ : ▹ Part A}
           → ¬ (now x ≤ᵖ later p▹)
¬now≤later ()

-- TODO general hlevel?
≤-prop : is-set A
       → (p q : Part A)
       → is-prop (p ≤ᵖ q)
≤-prop sA = fix λ ih▹ → λ where
  p          (now y)    → is-prop-η λ where (≤ᵖn py₁)   (≤ᵖn py₂)   → ap ≤ᵖn (is-prop-β (⊑-prop sA y p) py₁ py₂)
  (now x)    (later q▹) → is-prop-η λ xq₁ → absurd (¬now≤later xq₁)
  (later p▹) (later q▹) → is-prop-η λ where (l≤ᵖl pq▹₁) (l≤ᵖl pq▹₂) → ap l≤ᵖl (is-prop-β (▹is-prop (ih▹ ⊛′ p▹ ⊛′ q▹)) pq▹₁ pq▹₂)

refl≤ : (p : Part A) → p ≤ᵖ p
refl≤ = fix λ ih▹ → λ where
  (now x) → ≤ᵖn (n⊑ᵖ refl)
  (later p▹) → l≤ᵖl (ih▹ ⊛ p▹)

≤-contra-⊑ : (a : A) → (p q : Part A)
           → p ≤ᵖ q → q ⊑ᵖ a → p ⊑ᵖ a
≤-contra-⊑ a = fix λ ih▹ → λ where
  p           .(now x)    (≤ᵖn px)                       (n⊑ᵖ {x} e) → subst (p ⊑ᵖ_) e px
  .(later p▹) .(later q▹) (l≤ᵖl {m▹ = p▹} {n▹ = q▹} pq▹) (l⊑ᵖ qa▹)   → l⊑ᵖ (ih▹ ⊛′ p▹ ⊛′ q▹ ⊛′ pq▹ ⊛′ qa▹)

trans≤ : (p q r : Part A)
       → p ≤ᵖ q → q ≤ᵖ r → p ≤ᵖ r
trans≤ = fix λ ih▹ → λ where
  p           q           (now z)    pq                   (≤ᵖn qz)             → ≤ᵖn (≤-contra-⊑ z p q pq qz)
  .(later p▹) .(later q▹) (later r▹) (l≤ᵖl {m▹ = p▹} pq▹) (l≤ᵖl {m▹ = q▹} qr▹) → l≤ᵖl (ih▹ ⊛′ p▹ ⊛′ q▹ ⊛′ r▹ ⊛′ pq▹ ⊛′ qr▹)

antisym≤ : (p q : Part A)
         → p ≤ᵖ q → q ≤ᵖ p → p ＝ q
antisym≤ = fix λ ih▹ → λ where
  .(now _)    .(now _)    (≤ᵖn (n⊑ᵖ exy))                (≤ᵖn _)    → ap now exy
  .(later p▹) .(later q▹) (l≤ᵖl {m▹ = p▹} {n▹ = q▹} pq▹) (l≤ᵖl qp▹) → ap later (▹-ext (ih▹ ⊛′ p▹ ⊛′ q▹  ⊛′ pq▹ ⊛′ qp▹))

-- TODO directed-complete laws

never≤ : (p : Part A) → never ≤ᵖ p
never≤ = fix λ ih▹ → λ where
  (now x)    → ≤ᵖn (never⊑ x)
  (later p▹) → l≤ᵖl λ α → transport (λ i → pfix later (~ i) α ≤ᵖ p▹ α) ((ih▹ ⊛ p▹) α)
