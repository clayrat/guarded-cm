{-# OPTIONS --guarded #-}

module ClIrr where

open import Prelude
open import Later

-- whenever t : ∀κ.A and κ is not in A, then evaluating t at different clocks give the same result
postulate
  clock-irr : {ℓ : Level} {A : 𝒰 ℓ} {κ₁ κ₂ : Cl}
            → (x : Cl → A) → x κ₁ ＝ x κ₂
  clock-pirr : {ℓ : Level} {A : 𝒰 ℓ} {κ₁ κ₂ : Cl}
             → (x : A) → clock-irr {κ₁ = κ₁} {κ₂ = κ₂} (λ κ → x) ＝ refl
