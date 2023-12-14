{-# OPTIONS --guarded #-}
module Clocked.Hofmann where

open import Prelude
open import Data.Sum
open import Later
open import Clocked.Colist

private variable
  A B : 𝒰
  k : Cl

-- can be extended to Tree∞

data Tree (A : 𝒰) : 𝒰 where
  Leaf : A → Tree A
  Br   : Tree A → A → Tree A → Tree A

-- Rou

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

nextR⇉ : Rou-next A (dfix (Rou-body A))
       → (▹ k (Rou k A) → ▹ k (gColist k A)) → gColist k A
nextR⇉ {A} = subst (Rou-next A) (pfix (Rou-body A))

⇉nextR : ((▹ k (Rou k A) → ▹ k (gColist k A)) → gColist k A)
       → Rou-next A (dfix (Rou-body A))
⇉nextR {A} = subst (Rou-next A) (sym $ pfix (Rou-body A))

-- constructors & recursor

overR : Rou k A
overR = inl tt

nextR : ((▹ k (Rou k A) → ▹ k (gColist k A)) → gColist k A) → Rou k A
nextR = inr ∘ ⇉nextR

rec : B → (((▹ k (Rou k A) → ▹ k (gColist k A)) → gColist k A) → B)
    → Rou k A → B
rec o _  (inl tt) = o
rec _ nf (inr f)  = nf (nextR⇉ f)

-- the algorithm

unfold : (▹ k (Rou k A) → ▹ k (gColist k A)) → Rou k A → ▹ k (gColist k A)
unfold kf =
  rec (kf (next overR))
      (λ f → next (f kf))

br : Tree A → Rou k A → Rou k A
br (Leaf a)   c = nextR (λ kf → ccons a (unfold kf c))
br (Br l a r) c = nextR (λ kf → ccons a (unfold (kf ∘ ▹map (br l ∘ br r)) c))

ex : Rou k A → gColist k A
ex {k} = fix {k = k} λ ex▹ →
  rec cnil
      (λ f → f (ex▹ ⊛_))

breadthfirst : Tree A → Colist A
breadthfirst t k = ex {k = k} $ br t overR
