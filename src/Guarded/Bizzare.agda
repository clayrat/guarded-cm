{-# OPTIONS --guarded #-}
module Guarded.Bizzare where

open import Prelude
open import Data.Unit
open import Data.Sum
open import LaterG

private variable
  A : 𝒰

-- non-trivial negative recursive type

{-
data Bizzare : 𝒰 → 𝒰 where
  pt     : Bizzare A
  pierce : ((((▹ Bizzare A → A) → ▹ Bizzare A) → ▹ Bizzare A) → ▹ Bizzare A) → Bizzare A
-}

Bizzare-pierce : 𝒰 → ▹ 𝒰 → 𝒰
Bizzare-pierce A b▹ = (((▸ b▹ → A) → ▸ b▹) → ▸ b▹) → ▸ b▹

Bizzare-body : 𝒰 → ▹ 𝒰 → 𝒰
Bizzare-body A b▹ = ⊤ ⊎ Bizzare-pierce A b▹

Bizzare : 𝒰 → 𝒰
Bizzare A = fix (Bizzare-body A)

pt : Bizzare A
pt = inl tt

pierce : ((((▹ Bizzare A → A) → ▹ Bizzare A) → ▹ Bizzare A) → ▹ Bizzare A) → Bizzare A
pierce {A} f = inr (subst (Bizzare-pierce A) (sym $ pfix (Bizzare-body A)) f)
