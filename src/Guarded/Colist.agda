{-# OPTIONS --guarded #-}
module Guarded.Colist where

open import Prelude
open import Data.Nat
open import Data.List
open import LaterG

private variable
  A B C : 𝒰

-- guarded colists

data Colist (A : 𝒰) : 𝒰 where
  cnil  : Colist A
  ccons : A → ▹ (Colist A) → Colist A

-- append

appendˡ-body : ▹ (Colist A → Colist A → Colist A) → Colist A → Colist A → Colist A
appendˡ-body ap▹  cnil         t = t
appendˡ-body ap▹ (ccons x xs▹) t = ccons x ((ap▹ ⊛ xs▹) ⊛ next t)

appendˡ : Colist A → Colist A → Colist A
appendˡ = fix appendˡ-body

-- map

mapˡ-body : (A → B) → ▹ (Colist A → Colist B) → Colist A → Colist B
mapˡ-body f map▹  cnil         = cnil
mapˡ-body f map▹ (ccons x xs▹) = ccons (f x) (map▹ ⊛ xs▹)

mapˡ : (A → B) → Colist A → Colist B
mapˡ f = fix (mapˡ-body f)
