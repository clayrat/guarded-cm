{-# OPTIONS --guarded #-}
module Guarded.Partial.Stream where

open import Prelude
open import Data.Maybe

open import LaterG
open import Guarded.Partial
open import Guarded.Stream

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

to-streamᵖ-body : ▹ (Part A → Stream (Maybe A)) → Part A → Stream (Maybe A)
to-streamᵖ-body ts▹ (now a)    = repeatˢ (just a)
to-streamᵖ-body ts▹ (later p▹) = cons nothing (ts▹ ⊛ p▹)

to-streamᵖ : Part A → Stream (Maybe A)
to-streamᵖ = fix to-streamᵖ-body

raceωᵖ-body : ▹ (Stream (Part A) → Part A) → Stream (Part A) → Part A
raceωᵖ-body r▹ (cons p ps▹) = raceᵖ p (later (r▹ ⊛ ps▹))

raceωᵖ : Stream (Part A) → Part A
raceωᵖ = fix raceωᵖ-body
