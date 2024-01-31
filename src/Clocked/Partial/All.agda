{-# OPTIONS --guarded #-}
module Clocked.Partial.All where

open import Prelude

open import Later
open import Clocked.Partial

private variable
  ℓ ℓ′ ℓ″ : Level
  A B : 𝒰 ℓ
  κ : Cl

-- predicate on a partiality monad

data gAllᵖ (κ : Cl) (P : A → 𝒰 ℓ′) : gPart κ A → 𝒰 (level-of-type A ⊔ ℓ′) where
  gAll-now   : ∀ {a}
             → P a → gAllᵖ κ P (now a)
  gAll-later : ∀ {p▹}
             → ▸ κ (gAllᵖ κ P ⍉ p▹)
             → gAllᵖ κ P (later p▹)

Allᵖ : (A → 𝒰 ℓ′) → Part A → 𝒰 (level-of-type A ⊔ ℓ′)
Allᵖ P p = ∀ κ → gAllᵖ κ P (p κ)

all-δᵏ : ∀ {P : A → 𝒰 ℓ′} {p : gPart κ A}
       → gAllᵖ κ P p → gAllᵖ κ P (δᵏ p)
all-δᵏ = gAll-later ∘ next

all-δ : ∀ {P : A → 𝒰 ℓ′} {p : Part A}
      → Allᵖ P p → Allᵖ P (δᵖ p)
all-δ a κ = all-δᵏ (a κ)

all->>=ᵏ : ∀ {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″}
            {p : gPart κ A} {f : A → gPart κ B}
         → gAllᵖ κ P p → (∀ {x} → P x → gAllᵖ κ Q (f x))
         → gAllᵖ κ Q (p >>=ᵏ f)
all->>=ᵏ (gAll-now ap)    af = af ap
all->>=ᵏ (gAll-later ap▹) af = gAll-later (λ α → all->>=ᵏ (ap▹ α) af)  -- need combinators for (m)apping over indexed+guarded types

all->>= : ∀ {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″}
            {p : Part A} {f : A → Part B}
         → Allᵖ P p → (∀ {x} → P x → Allᵖ Q (f x))
         → Allᵖ Q (p >>=ᵖ f)
all->>= ap af κ = all->>=ᵏ (ap κ) (λ {x} px → af px κ)
