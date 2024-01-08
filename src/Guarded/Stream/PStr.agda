{-# OPTIONS --guarded #-}
module Guarded.Stream.PStr where

open import Prelude

open import LaterG
open import Guarded.Conat

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- guarded partial streams (after Basold)
-- indexed by a conat length

data PStream (A : 𝒰 ℓ) : ℕ∞ → 𝒰 ℓ where
  pcons : ∀ {n▹ : ▹ ℕ∞}
        → A → ▹[ α ] (PStream A (n▹ α)) → PStream A (cosu n▹)

repeatᵖ : A → PStream A infty
repeatᵖ {A} a = fix λ s▹ → pcons a (transport (λ i → ▹[ α ] (PStream A (pfix cosu (~ i) α))) s▹)

mapᵖ-body : (A → B) → ▹ ((n : ℕ∞) → PStream A n → PStream B n)
                    → (n : ℕ∞) → PStream A n → PStream B n
mapᵖ-body f m▹ .(cosu n▹) (pcons {n▹} a s▹) = pcons (f a) (m▹ ⊛ n▹ ⊛′ s▹)

mapᵖ : ∀ {n} → (A → B) → PStream A n → PStream B n
mapᵖ {n} f = fix (mapᵖ-body f) n
