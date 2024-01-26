{-# OPTIONS --guarded #-}
module Guarded.RoseTree.Conat where

open import Prelude
open import Data.List as List

open import LaterG
open import Guarded.RoseTree
open import Guarded.Conat
open import Guarded.Conat.Arith

private variable
  ℓ : Level
  A B : 𝒰 ℓ

depthʳ-body : ▹ (RTree A → ℕ∞) → RTree A → ℕ∞
depthʳ-body d▹ (rnode a ts) = cosu (List.rec (next coze) (λ r▹ n▹ → maxᶜ ⍉ (d▹ ⊛ r▹) ⊛ n▹) ts)

depthʳ : RTree A → ℕ∞
depthʳ = fix depthʳ-body
