{-# OPTIONS --guarded #-}
module Clocked.ReplaceMin where

open import Prelude
open import Data.Nat
open import Later

private variable
  ℓ ℓ′  : Level

data Tree (A : 𝒰 ℓ) : 𝒰 ℓ where
  Leaf : A → Tree A
  Br   : Tree A → Tree A → Tree A

feedback : {A : 𝒰 ℓ} {B : Cl → 𝒰 ℓ′} {k : Cl}
         → (▹ k A → B k × A) → B k
feedback f = fst (fix (f ∘ ▹map snd))

replaceMinBody : Tree ℕ → {k : Cl} → ▹ k ℕ → ▹ k (Tree ℕ) × ℕ
replaceMinBody (Leaf x) n▹ = (next Leaf ⊛ n▹) , x
replaceMinBody (Br l r) n▹ =
  let (l▹ , nl) = replaceMinBody l n▹
      (r▹ , nr) = replaceMinBody r n▹
    in
  (next Br ⊛ l▹ ⊛ r▹) , min nl nr

replaceMin : Tree ℕ → Tree ℕ
replaceMin t =
  force (λ k → feedback {B = λ k′ → ▹ k′ (Tree ℕ)} {k} (replaceMinBody t)) k0
