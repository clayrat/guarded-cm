{-# OPTIONS --cubical --guarded #-}
module Clocked.FairStream where

open import Prelude
open import Data.Bool
open import Data.Sum
open import Later
open import Clocked.Stream
open import Clocked.Conat

private variable
  A B : 𝒰
  k : Cl

fbᵏ : gConat k → gConat k → gStream k Bool
fbᵏ = fix λ fb▹ → λ where
  coze     m → cons false (fb▹ ⊛ next m ⊛ next (cosu (next m)))
  (cosu n) m → cons true (fb▹ ⊛ n ⊛ next m)

fb : Conat → Conat → Stream Bool
fb c m k = fbᵏ (c k) (m k)

schedᵏ-body : ▹ k (gStream k Bool → gStream k A → gStream k B → gStream k (A ⊎ B)) → gStream k Bool → gStream k A → gStream k B → gStream k (A ⊎ B)
schedᵏ-body s▹ b s t with (headᵏ b)
... | true  = cons (inl (headᵏ s)) (s▹ ⊛ tail▹ᵏ b ⊛ tail▹ᵏ s ⊛ tail▹ᵏ t)
... | false = cons (inr (headᵏ t)) (s▹ ⊛ tail▹ᵏ b ⊛ tail▹ᵏ s ⊛ tail▹ᵏ t)

schedᵏ : gStream k Bool → gStream k A → gStream k B → gStream k (A ⊎ B)
schedᵏ = fix schedᵏ-body

sched : Stream Bool → Stream A → Stream B → Stream (A ⊎ B)
sched b s t k = schedᵏ (b k) (s k) (t k)

