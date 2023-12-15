{-# OPTIONS --guarded #-}
module Guarded.Partial.Converges where

open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.Sum
open import LaterG

open import Guarded.Partial

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

-- convergence (propositional)

_⇓ᵖ_ : Part A → A → 𝒰 (level-of-type A)
_⇓ᵖ_ {A} p x = ∃[ n ꞉ ℕ ] (p ＝ delay-by n x)

map⇓ : {p : Part A} {a : A}
     → (f : A → B)
     → p ⇓ᵖ a
     → mapᵖ f p ⇓ᵖ f a
map⇓ {a} f =
  ∥-∥₁.map λ where (n , e) → n , ap (mapᵖ f) e ∙ delay-by-mapᵖ a n

ap⇓ : {p : Part A} {g : A → B} {a : A}
    → (f : Part (A → B))
    → f ⇓ᵖ g
    → p ⇓ᵖ a
    → (apᵖ f p) ⇓ᵖ g a
ap⇓ {g} {a} f fg pa =
  ∥-∥₁.rec! (λ where
    (n , eᶠ) → ∥-∥₁.map (λ where
      (m , e) → max n m , ap² apᵖ eᶠ e
                        ∙ delay-by-apᵖ g n a m) pa) fg

bind⇓ : {p : Part A} {a : A} {b : B}
      → (f : A → Part B)
      → p ⇓ᵖ a
      → f a ⇓ᵖ b
      → (p >>=ᵖ f) ⇓ᵖ b
bind⇓ {a} {b} f pa fab =
  ∥-∥₁.rec! (λ where
    (n , e) → ∥-∥₁.map (λ where
      (m , eᶠ) → (n + m , ap (_>>=ᵖ f) e
                        ∙ delay-by-bindᵖ f a n
                        ∙ ap (iter n δᵖ) eᶠ
                        ∙ sym (iter-add n m δᵖ (now b)))) fab) pa
