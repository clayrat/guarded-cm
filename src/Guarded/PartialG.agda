{-# OPTIONS --cubical --guarded #-}
module Guarded.PartialG where

open import Prelude
open import Data.Maybe
open import LaterG

private variable
  A B : 𝒰

-- guarded partiality monad aka Lift aka Event

data Part (A : 𝒰) : 𝒰 where
  now   : A → Part A
  later : ▹ Part A → Part A

_>>=ᵖ_ : Part A → (A → Part B) → Part B
now x   >>=ᵖ f = f x
later x >>=ᵖ f = later λ α → x α >>=ᵖ f
