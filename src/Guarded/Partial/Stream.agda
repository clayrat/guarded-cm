{-# OPTIONS --guarded #-}
module Guarded.Partial.Stream where

open import Prelude
open import Data.Maybe

open import LaterG
open import Guarded.Partial
open import Guarded.Stream
open import Guarded.Stream.Quantifiers

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

data Maybe-inc {A : 𝒰 ℓ} : Maybe A → Maybe A → 𝒰 ℓ where
  nothing-inc : ∀ {m}
              → Maybe-inc nothing m
  just-inc    : ∀ {a b}
              → a ＝ b → Maybe-inc (just a) (just b)

Maybe-inc-refl : (m : Maybe A) → Maybe-inc m m
Maybe-inc-refl nothing  = nothing-inc
Maybe-inc-refl (just a) = just-inc refl

increasing : Stream (Maybe A) → 𝒰 (level-of-type A)
increasing = Adjˢ Maybe-inc

to-streamᵖ-increasing : (p : Part A) → increasing (to-streamᵖ p)
to-streamᵖ-increasing =
  fix λ ih▹ → λ where
    (now x)    → repeat-adj Maybe-inc-refl (just x)
    (later p▹) → Adj-cons (λ α → nothing-inc)
                   λ α →  transport (λ i → increasing (pfix to-streamᵖ-body (~ i) α (p▹ α))) ((ih▹ ⊛ p▹) α)
