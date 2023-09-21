{-# OPTIONS --cubical --guarded #-}
module Guarded.NegativeU where

open import Prelude
open import Data.Unit
open import LaterG

{-
data NegU : 𝒰 where
  MkNegU : (▹ Neg → ⊤) → Neg
-}

NegU-body : ▹ 𝒰 → 𝒰
NegU-body N▹ = ▸ N▹ → ⊤

NegU : 𝒰
NegU = fix NegU-body

pt : NegU
pt _ = tt

NegU-inh : NegU ≃ ⊤
NegU-inh =
  is-contr→equiv-⊤ (is-contr-η (pt , λ n → fun-ext (λ q → refl)))
