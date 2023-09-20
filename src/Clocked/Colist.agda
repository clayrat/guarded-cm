{-# OPTIONS --cubical --guarded #-}
module Clocked.Colist where

open import Prelude
open import Data.Nat
open import Data.List
open import Later

private variable
  A B C : 𝒰
  k : Cl

-- clocked colists

data gColist (k : Cl) (A : 𝒰) : 𝒰 where
  cnil  : gColist k A
  ccons : (x : A) (xs : ▹ k (gColist k A)) → gColist k A

appendᵏ : gColist k A → gColist k A → gColist k A
appendᵏ {k} = fix {k = k} λ ap▹ → λ where
  cnil t → t
  (ccons x s) t → ccons x ((ap▹ ⊛ s) ⊛ next t)

Colist : 𝒰 → 𝒰
Colist A = ∀ k → gColist k A

appendˡ : Colist A → Colist A → Colist A
appendˡ s t k = appendᵏ (s k) (t k)
