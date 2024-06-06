{-# OPTIONS --guarded #-}
module Guarded.Conat.Partial where

open import Prelude
open import Data.Empty

open import LaterG
open import Guarded.Conat
open import Guarded.Partial

fromℕ-inj : (x y : ℕ) → fromℕᶜ x ＝ fromℕᶜ y → Part (x ＝ y)
fromℕ-inj  zero    zero   prf = now refl
fromℕ-inj  zero   (suc y) prf = absurd (cosu≠coze (sym prf))
fromℕ-inj (suc x)  zero   prf = absurd (cosu≠coze prf)
fromℕ-inj (suc x) (suc y) prf =
  later ((mapᵖ (ap suc) ∘ fromℕ-inj x y) ⍉ (▹-ap $ cosu-inj prf))

-- subtraction

∸ᶜ-body : ▹ (ℕ∞ → ℕ∞ → Part ℕ∞) → ℕ∞ → ℕ∞ → Part ℕ∞
∸ᶜ-body s▹  coze      _        = now coze
∸ᶜ-body s▹ (cosu x▹)   coze    = now (cosu x▹)
∸ᶜ-body s▹ (cosu x▹) (cosu y▹) = later (s▹ ⊛ x▹ ⊛ y▹)

_∸ᶜ_ : ℕ∞ → ℕ∞ → Part ℕ∞
_∸ᶜ_ = fix ∸ᶜ-body

∸ᶜ-zerol : (x : ℕ∞) → coze ∸ᶜ x ＝ now coze
∸ᶜ-zerol x = refl

∸ᶜ-zeror : (x : ℕ∞) → x ∸ᶜ coze ＝ now x
∸ᶜ-zeror  coze     = refl
∸ᶜ-zeror (cosu x▹) = refl

∸ᶜ-infty : infty ∸ᶜ infty ＝ never*
∸ᶜ-infty = fix λ prf▹ →
  later (dfix ∸ᶜ-body ⊛ (dfix cosu) ⊛ (dfix cosu))
    ~⟨ ap (λ q → later (dfix ∸ᶜ-body ⊛ (dfix cosu) ⊛ q)) (pfix cosu) ⟩
  later (dfix ∸ᶜ-body ⊛ dfix cosu ⊛ (next infty))
    ~⟨ ap (λ q → later (dfix ∸ᶜ-body ⊛ q ⊛ (next infty))) (pfix cosu) ⟩
  later (dfix ∸ᶜ-body ⊛ (next infty) ⊛ next infty)
    ~⟨ ap (λ q → later (q ⊛ (next infty) ⊛ next infty)) (pfix ∸ᶜ-body) ⟩
  later ((next _∸ᶜ_) ⊛ next infty ⊛ next infty)
    ~⟨⟩
  later (next (infty ∸ᶜ infty))
    ~⟨ ap later (▹-ext prf▹) ⟩
  later (next never*)
    ~⟨ fix-path later ⁻¹ ⟩
  never*
    ∎
