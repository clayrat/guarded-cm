{-# OPTIONS --cubical --guarded #-}
module Clocked.Hofmann where

open import Prelude
open import Data.Nat
open import Data.Sum
open import Later
open import Clocked.Colist

private variable
  ℓ ℓ′  : Level
  k : Cl

data Tree : 𝒰 where
  Leaf : ℕ → Tree
  Br : Tree → ℕ → Tree → Tree

{-
data Rou : 𝒰 where
  overR : Rou
  nextR : ((▹ Rou → ▹ Colist ℕ) → Colist ℕ) → Rou
-}

Rou-next : ▹ k 𝒰 → 𝒰
Rou-next {k} rou▹ = (▸ k rou▹ → ▹ k (gColist k ℕ)) → gColist k ℕ

Rou-body : ▹ k 𝒰 → 𝒰
Rou-body rou▹ = ⊤ ⊎ Rou-next rou▹

Rou : Cl → 𝒰
Rou k = fix {k = k} Rou-body

overR : Rou k
overR = inl tt

nextR : ((▹ k (Rou k) → ▹ k (gColist k ℕ)) → gColist k ℕ) → Rou k
nextR {k} f = inr (subst Rou-next (sym $ pfix Rou-body) f)

unfold : Rou k → (▹ k (Rou k) → ▹ k (gColist k ℕ)) → ▹ k (gColist k ℕ)
unfold (inl tt) kf = kf (next overR)
unfold (inr f)  kf = next (subst Rou-next (pfix Rou-body) f kf)

br : Tree → Rou k → Rou k
br (Leaf n)   c = nextR (λ kf → ccons n (unfold c kf))
br (Br l n r) c = nextR (λ kf → ccons n (unfold c λ r▹ → kf (▹map (λ c′ → br l (br r c′)) r▹)))

ex : Rou k → gColist k ℕ
ex {k} = fix {k = k} λ ex▹ → λ where
  (inl tt) → cnil
  (inr f)  → subst Rou-next (pfix Rou-body) f (ex▹ ⊛_)

breadthfirst : Tree → Colist ℕ
breadthfirst t k = ex {k = k} (br t overR)
