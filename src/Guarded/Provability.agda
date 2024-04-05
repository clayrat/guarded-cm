{-# OPTIONS --guarded #-}
module Guarded.Provability where

open import Prelude
open import Data.Empty

open import LaterG

private variable
  ℓ : Level
  A : 𝒰 ℓ

-- ▹ originally meant "provable in PA"
-- and the classical Loeb axiom is weak
WLoeb : ▹ (▹ A → A) → ▹ A
WLoeb = fix ⍉_

-- which immediately implies Goedel's 2nd theorem
Goedel : ¬ (▹ ⊥) → ¬ (▹ (¬ (▹ ⊥)))
Goedel cst = cst ∘ WLoeb

-- also works backwards
Goedel← : ¬ (▹ (¬ (▹ ⊥))) → ¬ (▹ ⊥)
Goedel← unp x = unp ((λ a → absurd a) ⍉ x)

◇ : 𝒰 ℓ → 𝒰 ℓ
◇ A = ¬ ▹ (¬ A)

-- however the strong axiom is "not not inconsistence"
nnv : ¬ ¬ (▹ ⊥)
nnv = fix
