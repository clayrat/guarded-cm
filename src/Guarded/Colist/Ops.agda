{-# OPTIONS --guarded #-}
module Guarded.Colist.Ops where

open import Prelude
open import Data.Maybe
open import Data.Nat
open import Data.List

open import LaterG
open import Guarded.Colist
open import Guarded.Partial
open import Guarded.Conat
open import Guarded.Conat.Arith

private variable
  A B C : 𝒰

-- foldl
-- is necessarily partial

foldlˡ-body : (B → A → B) → ▹ (B → Colist A → Part B) → B → Colist A → Part B
foldlˡ-body f f▹ z  cnil         = now z
foldlˡ-body f f▹ z (ccons x xs▹) = later (f▹ ⊛ next (f z x) ⊛ xs▹)

foldlˡ : (B → A → B) → B → Colist A → Part B
foldlˡ f = fix (foldlˡ-body f)

-- sums

suml : Colist ℕ → Part ℕ
suml c = foldlˡ _+_ zero c

sum∞l : Colist ℕ∞ → Part ℕ∞
sum∞l c = foldlˡ _+ᶜ_ coze c

sumr : Colist ℕ → Part ℕ
sumr c = foldrˡ (λ x → later ∘ ▹map (mapᵖ (x +_))) c (now zero)

sum∞r : Colist ℕ∞ → Part ℕ∞
sum∞r c = foldrˡ (λ x → later ∘ ▹map (mapᵖ (x +ᶜ_))) c (now coze)

-- size

sizeˡ-body : ▹ (Colist A → ℕ∞) → Colist A → ℕ∞
sizeˡ-body s▹  cnil        = coze
sizeˡ-body s▹ (ccons _ t▹) = cosu (s▹ ⊛ t▹)

sizeˡ : Colist A → ℕ∞
sizeˡ = fix sizeˡ-body

