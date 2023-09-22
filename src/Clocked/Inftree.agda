{-# OPTIONS --cubical --guarded #-}
module Clocked.Inftree where

open import Prelude
open import Data.Nat
open import Data.List
open import Later
open import Clocked.Colist

private variable
  A B C : 𝒰
  k : Cl

-- clocked infinite binary trees

data gTree∞ (k : Cl) (A : 𝒰) : 𝒰 where
  node : (x : A) (l r : ▹ k (gTree∞ k A)) → gTree∞ k A

Tree∞ : 𝒰 → 𝒰
Tree∞ A = ∀ k → gTree∞ k A

labelᵏ : gTree∞ k A → A
labelᵏ (node n l▹ r▹) = n

sonl▹ᵏ : gTree∞ k A → ▹ k (gTree∞ k A)
sonl▹ᵏ (node n l▹ r▹) = l▹

sonr▹ᵏ : gTree∞ k A → ▹ k (gTree∞ k A)
sonr▹ᵏ (node n l▹ r▹) = r▹

labelᵗ : Tree∞ A → A
labelᵗ t = labelᵏ (t k0)

sonlᵗ : Tree∞ A → Tree∞ A
sonlᵗ t = force λ k → sonl▹ᵏ (t k)

sonrᵗ : Tree∞ A → Tree∞ A
sonrᵗ t = force λ k → sonr▹ᵏ (t k)

-- breadth-first traversal via forests

bftauxᵏ-body : ▹ k (gColist k (gTree∞ k A) → gColist k A) → gColist k (gTree∞ k A) → gColist k A
bftauxᵏ-body b▹  cnil        = cnil
bftauxᵏ-body b▹ (ccons x xs) =
  ccons (labelᵏ x)
        (b▹ ⊛ (next (appendᵏ) ⊛ xs ⊛ (next ccons ⊛ sonl▹ᵏ x ⊛ next (next ccons ⊛ sonl▹ᵏ x ⊛ next (next cnil)))))

bftauxᵏ : gColist k (gTree∞ k A) → gColist k A
bftauxᵏ = fix bftauxᵏ-body

bftᵏ : gTree∞ k A → gColist k A
bftᵏ t = bftauxᵏ (ccons t (next cnil))

bft : Tree∞ A → Colist A
bft t k = bftᵏ (t k)

