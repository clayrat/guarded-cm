{-# OPTIONS --guarded #-}
module Clocked.Conat.Partial where

open import Prelude
open import Data.Empty

open import Later
open import Clocked.Conat
open import Clocked.Partial

private variable
  k : Cl

fromℕ-inj : (x y : ℕ) → fromℕᵏ {k = k} x ＝ fromℕᵏ y → gPart k (x ＝ y)
fromℕ-inj  zero    zero   prf = now refl
fromℕ-inj  zero   (suc y) prf = absurd (cosu≠coze (sym prf))
fromℕ-inj (suc x)  zero   prf = absurd (cosu≠coze prf)
fromℕ-inj (suc x) (suc y) prf =
  later (▹map (mapᵏ (ap suc) ∘ fromℕ-inj x y) (▹-ap $ cosu-inj prf))

-- subtraction

∸ᵏ-body : ▹ k (ℕ∞ᵏ k → ℕ∞ᵏ k → gPart k (ℕ∞ᵏ k)) → ℕ∞ᵏ k → ℕ∞ᵏ k → gPart k (ℕ∞ᵏ k)
∸ᵏ-body s▹  coze      _        = now coze
∸ᵏ-body s▹ (cosu x▹)   coze    = now (cosu x▹)
∸ᵏ-body s▹ (cosu x▹) (cosu y▹) = later (s▹ ⊛ x▹ ⊛ y▹)

_∸ᵏ_ : ℕ∞ᵏ k → ℕ∞ᵏ k → gPart k (ℕ∞ᵏ k)
_∸ᵏ_ = fix ∸ᵏ-body

∸ᵏ-zerol : (x : ℕ∞ᵏ k) → coze ∸ᵏ x ＝ now coze
∸ᵏ-zerol x = refl

∸ᵏ-zeror : (x : ℕ∞ᵏ k) → x ∸ᵏ coze ＝ now x
∸ᵏ-zeror  coze     = refl
∸ᵏ-zeror (cosu x▹) = refl

∸ᵏ-infty : (inftyᵏ {k = k}) ∸ᵏ inftyᵏ ＝ neverᵏ
∸ᵏ-infty = fix λ prf▹ →
  later (dfix ∸ᵏ-body ⊛ (dfix cosu) ⊛ (dfix cosu))
    ＝⟨ ap (λ q → later (dfix ∸ᵏ-body ⊛ (dfix cosu) ⊛ q)) (pfix cosu) ⟩
  later (dfix ∸ᵏ-body ⊛ dfix cosu ⊛ (next inftyᵏ))
    ＝⟨ ap (λ q → later (dfix ∸ᵏ-body ⊛ q ⊛ (next inftyᵏ))) (pfix cosu) ⟩
  later (dfix ∸ᵏ-body ⊛ (next inftyᵏ) ⊛ next inftyᵏ)
    ＝⟨ ap (λ q → later (q ⊛ (next inftyᵏ) ⊛ next inftyᵏ)) (pfix ∸ᵏ-body) ⟩
  later ((next _∸ᵏ_) ⊛ next inftyᵏ ⊛ next inftyᵏ)
    ＝⟨ ap later (▹-ext prf▹) ⟩
  later (next neverᵏ)
    ＝⟨ sym $ fix-path later ⟩
  neverᵏ
    ∎
