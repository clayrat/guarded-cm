{-# OPTIONS --guarded #-}
module Guarded.Conat.WLPO where

open import Prelude
open import Data.Empty
open import Data.Sum
open import Data.Dec

open import LaterG
open import Guarded.Conat
open import Guarded.Conat.Arith

-- morally false, as it's equivalent to the halting problem
WLPO : 𝒰
WLPO = (n : ℕ∞) → (n ＝ infty) ⊎ (n ≠ infty)

ℕ∞-discrete→WLPO : is-discrete ℕ∞ → WLPO
ℕ∞-discrete→WLPO d n =
  (dec-as-sum ∙ₑ ⊎-comm) .fst (is-discrete-β d n infty)

WLPO→ℕ∞-discrete : WLPO → is-discrete ℕ∞
WLPO→ℕ∞-discrete w = is-discrete-η go
  where
  go : Dec on-paths-of ℕ∞
  go m n with (w (closenessᶜ m n))
  ... | inl e  = yes (close∞→equal m n e)
  ... | inr ne = no λ e → ne (ap (closenessᶜ m) (sym e) ∙ closenessᶜ-refl m)
