{-# OPTIONS --guarded #-}
module Clocked.ReplaceMin where

open import Prelude
open import Data.Nat
open import Later

private variable
  ℓ : Level

-- Bird's algorithm

data Tree (A : 𝒰 ℓ) : 𝒰 ℓ where
  Leaf : A → Tree A
  Br   : Tree A → Tree A → Tree A

replaceMinBody : Tree ℕ → ∀ {k} → ▹ k ℕ → ▹ k (Tree ℕ) × ℕ
replaceMinBody (Leaf x) n▹ = ▹map Leaf n▹ , x
replaceMinBody (Br l r) n▹ =
  let (l▹ , nl) = replaceMinBody l n▹
      (r▹ , nr) = replaceMinBody r n▹
    in
  (▹map Br l▹ ⊛ r▹) , min nl nr

replaceMin : Tree ℕ → Tree ℕ
replaceMin t =
  force (λ k → feedback {B = λ k′ → ▹ k′ (Tree ℕ)} (replaceMinBody t {k = k})) k0
