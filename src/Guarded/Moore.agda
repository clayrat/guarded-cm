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
  Mre : B → (A → ▹ Moore A B) → Moore A B

-- functor

mapᵐ-body : (B → C)
          → ▹ (Moore A B → Moore A C)
          → Moore A B → Moore A C
mapᵐ-body f m▹ (Mre b tr) = Mre (f b) λ a → m▹ ⊛ tr a

mapᵐ : (B → C)
     → Moore A B → Moore A C
mapᵐ f = fix (mapᵐ-body f)

-- profunctor

dimapᵐ-body : (D → A) → (B → C)
            → ▹ (Moore A B → Moore D C)
            → Moore A B → Moore D C
dimapᵐ-body f g d▹ (Mre b tr) = Mre (g b) λ d → d▹ ⊛ tr (f d)

dimapᵐ : (D → A) → (B → C)
       → Moore A B → Moore D C
dimapᵐ f g = fix (dimapᵐ-body f g)

-- applicative

pureᵐ-body : B → ▹ Moore A B → Moore A B
pureᵐ-body b p▹ = Mre b λ _ → p▹

pureᵐ : B → Moore A B
pureᵐ b = fix (pureᵐ-body b)

apᵐ-body : ▹ (Moore A (B → C) → Moore A B → Moore A C)
         → Moore A (B → C) → Moore A B → Moore A C
apᵐ-body a▹ (Mre f trf) (Mre b trb) = Mre (f b) λ a → a▹ ⊛ trf a ⊛ trb a

apᵐ : Moore A (B → C) → Moore A B → Moore A C
apᵐ = fix apᵐ-body

-- comonad

extractᵐ : Moore A B → B
extractᵐ (Mre b _) = b

duplicateᵐ-body : ▹ (Moore A B -> Moore A (Moore A B))
                →  Moore A B -> Moore A (Moore A B)
duplicateᵐ-body d▹ m@(Mre _ tr) = Mre m λ a → d▹ ⊛ tr a

duplicateᵐ : Moore A B -> Moore A (Moore A B)
duplicateᵐ = fix duplicateᵐ-body

extendᵐ-body : (Moore A B → C)
             → ▹ (Moore A B → Moore A C)
             → Moore A B → Moore A C
extendᵐ-body f e▹ m@(Mre b tr) = Mre (f m) λ a → e▹ ⊛ tr a

extendᵐ : (Moore A B → C) -> Moore A B -> Moore A C
extendᵐ f = fix (extendᵐ-body f)

-- left fold

moorel-body : (B → A → ▹ B)
            → ▹ (B → Moore A B)
            → B → Moore A B
moorel-body f m▹ b = Mre b λ a → m▹ ⊛ f b a

moorel : (B → A → ▹ B) → B → Moore A B
moorel f = fix (moorel-body f)

-- composition (cascade product?)

catᵐ-body : ▹ (Moore A B → Moore B C → Moore A C)
          → Moore A B → Moore B C → Moore A C
catᵐ-body m▹ (Mre b tra) (Mre c trb) = Mre c λ a → m▹ ⊛ tra a ⊛ trb b

catᵐ : Moore A B → Moore B C → Moore A C
catᵐ = fix catᵐ-body

-- TODO mfix ?
