{-# OPTIONS --guarded #-}
module Guarded.Mealy.Moore where

open import Prelude

open import LaterG
open import Guarded.Mealy
open import Guarded.Moore

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- a Moore machine is a special case of a Mealy machine

moore→mealy-body : ▹ (Moore A B → Mealy A B)
                 → Moore A B → Mealy A B
moore→mealy-body m▹ (Mre b tr) = Mly λ a → b , (m▹ ⊛ tr a)

moore→mealy : Moore A B → Mealy A B
moore→mealy = fix moore→mealy-body
