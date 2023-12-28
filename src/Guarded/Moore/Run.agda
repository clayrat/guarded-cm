{-# OPTIONS --guarded #-}
module Guarded.Moore.Run where

open import Prelude
open import Data.Maybe
open import Data.List

open import LaterG
open import Guarded.Moore
open import Guarded.Stream
open import Guarded.Colist
open import Guarded.Partial
open import Guarded.Partial.Converges

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

runListLast-body : ▹ (Moore A B → List A → Part B)
                 → Moore A B → List A → Part B
runListLast-body r▹ (Mre b _) []      = now b
runListLast-body r▹ (Mre _ k) (x ∷ l) = later $ r▹ ⊛ k x ⊛ next l

runListLast : Moore A B → List A → Part B
runListLast = fix runListLast
