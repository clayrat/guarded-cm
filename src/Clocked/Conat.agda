{-# OPTIONS --cubical --guarded #-}
module Clocked.Conat where

open import Prelude
open import Data.Maybe
open import Later

private variable
  A B C : 𝒰
  k : Cl

-- co-naturals

data gConat (k : Cl) : 𝒰 where
  coze : gConat k
  cosu : ▹ k (gConat k) → gConat k

inftyᵏ : gConat k
inftyᵏ = fix cosu

Conat : 𝒰
Conat = ∀ k → gConat k

addᵏ-body : gConat k → ▹ k (gConat k → gConat k) → gConat k → gConat k
addᵏ-body x ax▹  coze    = x
addᵏ-body x ax▹ (cosu y) = cosu (ax▹ ⊛ y)

addᵏ : gConat k → gConat k → gConat k
addᵏ x = fix (addᵏ-body x)

addᶜ : Conat → Conat → Conat
addᶜ x y k = addᵏ (x k) (y k)

predᵏ : gConat k → Maybe (▹ k (gConat k))
predᵏ  coze    = nothing
predᵏ (cosu x) = just x
