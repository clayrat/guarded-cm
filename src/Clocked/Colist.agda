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

Colist : 𝒰 → 𝒰
Colist A = ∀ k → gColist k A

-- append

appendᵏ-body : ▹ k (gColist k A → gColist k A → gColist k A) → gColist k A → gColist k A → gColist k A
appendᵏ-body ap▹  cnil         t = t
appendᵏ-body ap▹ (ccons x xs▹) t = ccons x ((ap▹ ⊛ xs▹) ⊛ next t)

appendᵏ : gColist k A → gColist k A → gColist k A
appendᵏ = fix appendᵏ-body

appendˡ : Colist A → Colist A → Colist A
appendˡ s t k = appendᵏ (s k) (t k)

-- map

mapᵏ-body : (A → B) → ▹ k (gColist k A → gColist k B) → gColist k A → gColist k B
mapᵏ-body f map▹  cnil         = cnil
mapᵏ-body f map▹ (ccons x xs▹) = ccons (f x) (λ α → map▹ α (xs▹ α))

mapᵏ : (A → B) → gColist k A → gColist k B
mapᵏ f = fix (mapᵏ-body f)

mapˡ : (A → B) → Colist A → Colist B
mapˡ f s k = mapᵏ f (s k)
