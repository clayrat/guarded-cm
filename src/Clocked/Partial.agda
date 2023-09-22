{-# OPTIONS --cubical --guarded #-}
module Clocked.Partial where

open import Prelude
open import Later

private variable
  A B : 𝒰
  k : Cl

-- partiality monad aka Lift

data gPart (k : Cl) (A : 𝒰) : 𝒰 where
  now   : A → gPart k A
  later : ▹ k (gPart k A) → gPart k A

_>>=ᵏ_ : gPart k A → (A → gPart k B) → gPart k B
now x   >>=ᵏ f = f x
later x >>=ᵏ f = later λ α → x α >>=ᵏ f

Part : 𝒰 → 𝒰
Part A = ∀ k → gPart k A

pureᵖ : A → Part A
pureᵖ a k = now a

_>>=ᵖ_ : Part A → (A → Part B) → Part B
_>>=ᵖ_ p f k = p k >>=ᵏ λ a → f a k

-- TODO needs modulus
-- collatz : ℕ → Part ⊤
-- collatz n k = ?
