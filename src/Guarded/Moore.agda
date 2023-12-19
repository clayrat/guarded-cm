{-# OPTIONS --guarded #-}
module Guarded.Moore where

open import Prelude

open import LaterG

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

-- Moore machine

-- A = input, B = output
data Moore (A : 𝒰 ℓ) (B : 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  M : B → (A → ▹ Moore A B) → Moore A B

-- functor

mapᵐ-body : (B → C)
          → ▹ (Moore A B → Moore A C)
          → Moore A B → Moore A C
mapᵐ-body f m▹ (M b tr) = M (f b) λ a → m▹ ⊛ tr a

mapᵐ : (B → C)
     → Moore A B → Moore A C
mapᵐ f = fix (mapᵐ-body f)

-- comonad

extractᵐ : Moore A B → B
extractᵐ (M b _) = b

duplicateᵐ-body : ▹ (Moore A B -> Moore A (Moore A B))
                →  Moore A B -> Moore A (Moore A B)
duplicateᵐ-body d▹ m@(M _ tr) = M m λ a → d▹ ⊛ tr a

duplicateᵐ : Moore A B -> Moore A (Moore A B)
duplicateᵐ = fix duplicateᵐ-body

extendᵐ-body : (Moore A B → C)
             → ▹ (Moore A B → Moore A C)
             → Moore A B → Moore A C
extendᵐ-body f e▹ m@(M b tr) = M (f m) λ a → e▹ ⊛ tr a

extendᵐ : (Moore A B → C) -> Moore A B -> Moore A C
extendᵐ f = fix (extendᵐ-body f)

-- left fold

moorel-body : (B → A → ▹ B)
            → ▹ (B → Moore A B)
            → B → Moore A B
moorel-body f m▹ b = M b λ a → m▹ ⊛ f b a

moorel : (B → A → ▹ B) → B → Moore A B
moorel f = fix (moorel-body f)

moorel1-body : (▹ B → A → B)
            → ▹ (B → Moore A B)
            → B → Moore A B
moorel1-body f m▹ b = M b λ a → m▹ ⊛ ?
