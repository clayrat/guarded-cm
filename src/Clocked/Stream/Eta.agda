{-# OPTIONS --guarded #-}
module Clocked.Stream.Eta where

open import Prelude

open import Later
open import ClIrr
open import Clocked.Stream

private variable
  ℓ : Level
  A : 𝒰 ℓ

uncons-eqˢ : (s : Stream A) → s ＝ consˢ (headˢ s) (tailˢ s)
uncons-eqˢ s =
  fun-ext λ k →
    uncons-eqᵏ (s k) ∙ ap² cons (clock-irr {κ₁ = k} {κ₂ = k0} (headᵏ ∘ s)) (tail-eq s k)

