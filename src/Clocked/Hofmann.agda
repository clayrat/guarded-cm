{-# OPTIONS --cubical --guarded #-}
module Clocked.Hofmann where

open import Prelude
open import Data.Sum
open import Later
open import Clocked.Colist

private variable
  A : 𝒰
  k : Cl

-- can be extended to Tree∞

data Tree (A : 𝒰) : 𝒰 where
  Leaf : A → Tree A
  Br   : Tree A → A → Tree A → Tree A

{-
data Rou (A : 𝒰) : 𝒰 where
  overR : Rou A
  nextR : ((▹ Rou A → ▹ Colist A) → Colist A) → Rou A
-}

Rou-next : 𝒰 → ▹ k 𝒰 → 𝒰
Rou-next {k} A rou▹ = (▸ k rou▹ → ▹ k (gColist k A)) → gColist k A

Rou-body : 𝒰 → ▹ k 𝒰 → 𝒰
Rou-body A rou▹ = ⊤ ⊎ (Rou-next A rou▹)

Rou : Cl → 𝒰 → 𝒰
Rou k A = fix {k = k} (Rou-body A)

overR : Rou k A
overR = inl tt

nextR : ((▹ k (Rou k A) → ▹ k (gColist k A)) → gColist k A) → Rou k A
nextR {k} {A} f = inr (subst (Rou-next A) (sym $ pfix (Rou-body A)) f)

unfold : Rou k A → (▹ k (Rou k A) → ▹ k (gColist k A)) → ▹ k (gColist k A)
unfold     (inl tt) kf = kf (next overR)
unfold {A} (inr f)  kf = next (subst (Rou-next A) (pfix (Rou-body A)) f kf)

br : Tree A → Rou k A → Rou k A
br (Leaf a)   c = nextR (λ kf → ccons a (unfold c kf))
br (Br l a r) c = nextR (λ kf → ccons a (unfold c λ r▹ → kf (▹map (λ c′ → br l (br r c′)) r▹)))

ex : Rou k A → gColist k A
ex {k} {A} = fix {k = k} λ ex▹ → λ where
  (inl tt) → cnil
  (inr f)  → subst (Rou-next A) (pfix (Rou-body A)) f (ex▹ ⊛_)

breadthfirst : Tree A → Colist A
breadthfirst t k = ex {k = k} (br t overR)
