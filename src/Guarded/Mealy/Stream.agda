{-# OPTIONS --guarded #-}
module Guarded.Mealy.Stream where

open import Prelude

open import LaterG
open import Guarded.Mealy
open import Guarded.Stream

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- Mealy machine corresponds to a causal stream function

mstr-body : ▹ (Mealy A B → Stream A → Stream B)
          → Mealy A B → Stream A → Stream B
mstr-body m▹ (Mly tr) (cons a as▹) = let btr = tr a in
                                     cons (btr .fst) (m▹ ⊛ btr .snd ⊛ as▹)

mstr : Mealy A B → Stream A → Stream B
mstr = fix mstr-body

-- the other direction seems to require clocks
