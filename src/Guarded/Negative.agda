{-# OPTIONS --cubical --guarded #-}
module Guarded.Negative where

open import Prelude
open import Data.Empty
open import LaterG

{-
data Neg : 𝒰 where
  MkNeg : ℕ → (▹ Neg → ⊥) → Neg
-}

Neg-body : ▹ 𝒰 → 𝒰
Neg-body N▹ = ℕ × (▸ N▹ → ⊥)

Neg : 𝒰
Neg = fix Neg-body

-- we can move forward in time ...
contra : ¬ Neg
contra ev = transport (fix-path Neg-body) ev .snd (next ev)

Neg-empty : Neg ≃ ⊥
Neg-empty = ¬-extₑ contra id

-- ... but not backwards
evidence : ℕ → Neg
evidence n =
  n , λ neg▸ →
    let neg▹ = the (▹ Neg) (subst (λ q → ▸ q) (pfix Neg-body) neg▸) in
    contra {!!}

bot : ⊥
bot = contra (evidence 42)
