{-# OPTIONS --cubical --guarded #-}
module Hofmann where

open import Prelude
open import Data.Nat
open import Data.List
open import Data.Sum
open import LaterG

private variable
  ℓ ℓ′  : Level

data Tree : 𝒰 where
  Leaf : ℕ → Tree
  Br : Tree → ℕ → Tree → Tree

{-
data Rou : 𝒰 where
  overR : Rou
  nextR : ((▹ Rou → List ℕ) → List ℕ) → Rou
-}

Rou : 𝒰
Rou = fix (λ rou▹ → ⊤ ⊎ ((▸ rou▹ → List ℕ) → List ℕ))
