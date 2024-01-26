{-# OPTIONS --guarded #-}
module Guarded.RoseTree where

open import Prelude
open import Data.List

open import LaterG

private variable
  ℓ : Level
  A B : 𝒰 ℓ

data RTree (A : 𝒰 ℓ) : 𝒰 ℓ where
  rnode : A → List (▹ RTree A) → RTree A

mapʳ-body : (A → B) → ▹ (RTree A → RTree B) → RTree A → RTree B
mapʳ-body f m▹ (rnode a ts) = rnode (f a) (map (m▹ ⊛_) ts)

mapʳ : (A → B) → RTree A → RTree B
mapʳ f = fix (mapʳ-body f)

-- TODO put somewhere?
List▹ : (A → ▹ B) → List A → ▹ (List B)
List▹ f []      = next []
List▹ f (h ∷ t) = (_∷_) ⍉ f h ⊛ List▹ f t

foldrʳ-body : (A → ▹ List B → B) → ▹ (RTree A → B) → RTree A → B
foldrʳ-body f f▹ (rnode a ts) = f a (List▹ (f▹ ⊛_) ts)

foldrʳ : (A → ▹ List B → B) → RTree A → B
foldrʳ f = fix (foldrʳ-body f)

mirrorʳ-body : ▹ (RTree A → RTree A) → RTree A → RTree A
mirrorʳ-body m▹ (rnode a ts) = rnode a (map (m▹ ⊛_) (reverse ts))

mirrorʳ : RTree A → RTree A
mirrorʳ = fix mirrorʳ-body
