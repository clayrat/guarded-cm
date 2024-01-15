{-# OPTIONS --guarded #-}
module Clocked.Partial.Stream where

open import Prelude
open import Data.Maybe

open import Later
open import Clocked.Partial
open import Clocked.Stream

private variable
  A B : 𝒰
  k : Cl

to-streamᵏ-body : ▹ k (gPart k A → gStream k (Maybe A)) → gPart k A → gStream k (Maybe A)
to-streamᵏ-body ts▹ (now a)    = repeatᵏ (just a)
to-streamᵏ-body ts▹ (later p▹) = cons nothing (ts▹ ⊛ p▹)

to-streamᵏ : gPart k A → gStream k (Maybe A)
to-streamᵏ = fix to-streamᵏ-body

to-streamᵖ : Part A → Stream (Maybe A)
to-streamᵖ c k = to-streamᵏ (c k)

timeout : Part A → ℕ → Maybe A
timeout p n = nthˢ n (to-streamᵖ p)

raceωᵏ-body : ▹ k (gStream k (gPart k A) → gPart k A) → gStream k (gPart k A) → gPart k A
raceωᵏ-body r▹ (cons p ps) = raceᵏ p (later (r▹ ⊛ ps))

raceωᵏ : gStream k (gPart k A) → gPart k A
raceωᵏ = fix raceωᵏ-body

raceωᵖ : Stream (Part A) → Part A
raceωᵖ s k = raceωᵏ (mapˢ (λ p → p k) s k)
