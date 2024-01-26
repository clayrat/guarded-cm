{-# OPTIONS --guarded #-}
module Guarded.Partial.All where

open import Prelude

open import LaterG
open import Guarded.Partial

private variable
  ℓ ℓ′ ℓ″ : Level
  A B : 𝒰 ℓ

-- predicate on a partiality monad

data Allᵖ (P : A → 𝒰 ℓ′) : Part A → 𝒰 (level-of-type A ⊔ ℓ′) where
  All-now   : ∀ {a}
           → P a → Allᵖ P (now a)
  All-later : ∀ {p▹}
           → ▸ (Allᵖ P ⍉ p▹)
           → Allᵖ P (later p▹)

all-δ : ∀ {P : A → 𝒰 ℓ′} {p : Part A}
      → Allᵖ P p → Allᵖ P (δᵖ p)
all-δ = All-later ∘ next

all->>= : ∀ {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″}
            {p : Part A} {f : A → Part B}
         → Allᵖ P p → (∀ {x} → P x → Allᵖ Q (f x))
         → Allᵖ Q (p >>=ᵖ f)
all->>= (All-now ap)     af = af ap
all->>= (All-later ap▹) af = All-later (λ α → all->>= (ap▹ α) af)  -- need combinators for (m)apping over indexed+guarded types
