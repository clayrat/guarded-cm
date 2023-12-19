{-# OPTIONS --guarded #-}
module Guarded.Mealy where

open import Prelude

open import LaterG

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  D : 𝒰 ℓ‴

-- Mealy machine

-- A = input, B = output
data Mealy (A : 𝒰 ℓ) (B : 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  My : (A → B × ▹ Mealy A B) → Mealy A B

-- functor

mapᵐ-body : (B → C)
          → ▹ (Mealy A B → Mealy A C)
          → Mealy A B → Mealy A C
mapᵐ-body f m▹ (My tr) = My λ a → let btr' = tr a in
                            f (btr' .fst) , (m▹ ⊛ btr' .snd)

mapᵐ : (B → C)
     → Mealy A B → Mealy A C
mapᵐ f = fix (mapᵐ-body f)

-- profunctor

dimapᵐ-body : (D → A) → (B → C)
            → ▹ (Mealy A B → Mealy D C)
            → Mealy A B → Mealy D C
dimapᵐ-body f g d▹ (My tr) = My λ d → let btr' = tr (f d) in
                                g (btr' .fst) , (d▹ ⊛ btr' .snd)

dimapᵐ : (D → A) → (B → C)
       → Mealy A B → Mealy D C
dimapᵐ f g = fix (dimapᵐ-body f g)
