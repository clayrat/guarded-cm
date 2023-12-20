{-# OPTIONS --guarded #-}
module Guarded.Moore where

open import Prelude

open import LaterG

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  D : 𝒰 ℓ‴

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

-- profunctor

dimapᵐ-body : (D → A) → (B → C)
            → ▹ (Moore A B → Moore D C)
            → Moore A B → Moore D C
dimapᵐ-body f g d▹ (M b tr) = M (g b) λ d → d▹ ⊛ tr (f d)

dimapᵐ : (D → A) → (B → C)
       → Moore A B → Moore D C
dimapᵐ f g = fix (dimapᵐ-body f g)

-- applicative

pureᵐ-body : B → ▹ Moore A B → Moore A B
pureᵐ-body b p▹ = M b λ _ → p▹

pureᵐ : B → Moore A B
pureᵐ b = fix (pureᵐ-body b)

apᵐ-body : ▹ (Moore A (B → C) → Moore A B → Moore A C)
         → Moore A (B → C) → Moore A B → Moore A C
apᵐ-body a▹ (M f trf) (M b trb) = M (f b) λ a → a▹ ⊛ trf a ⊛ trb a

apᵐ : Moore A (B → C) → Moore A B → Moore A C
apᵐ = fix apᵐ-body

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

-- TODO mfix ?
