{-# OPTIONS --guarded #-}
module Guarded.Hofmann where

open import Prelude
open import Data.Sum
open import LaterG
open import Guarded.Colist

private variable
  A : 𝒰

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

Rou-next : 𝒰 → ▹ 𝒰 → 𝒰
Rou-next A rou▹ = (▸ rou▹ → ▹ (Colist A)) → Colist A

Rou-body : 𝒰 → ▹ 𝒰 → 𝒰
Rou-body A rou▹ = ⊤ ⊎ (Rou-next A rou▹)

Rou : 𝒰 → 𝒰
Rou A = fix (Rou-body A)

nextR⇉ : Rou-next A (dfix (Rou-body A))
       → ((▹ Rou A → ▹ Colist A) → Colist A)
nextR⇉ {A} = subst (Rou-next A) (pfix (Rou-body A))

⇉nextR : ((▹ Rou A → ▹ Colist A) → Colist A)
       → Rou-next A (dfix (Rou-body A))
⇉nextR {A} = subst (Rou-next A) (sym $ pfix (Rou-body A))

overR : Rou A
overR = inl tt

nextR : ((▹ (Rou A) → ▹ (Colist A)) → Colist A) → Rou A
nextR {A} f = inr (⇉nextR f)

-- the algorithm

unfold : Rou A → (▹ (Rou A) → ▹ (Colist A)) → ▹ (Colist A)
unfold     (inl tt) kf = kf (next overR)
unfold {A} (inr f)  kf = next (nextR⇉ f kf)

br : Tree A → Rou A → Rou A
br (Leaf a)   c = nextR (λ kf → ccons a (unfold c  kf))
br (Br l a r) c = nextR (λ kf → ccons a (unfold c (kf ∘ ▹map (br l ∘ br r))))

ex : Rou A → Colist A
ex {A} = fix λ ex▹ → λ where
  (inl tt) → cnil
  (inr f)  → nextR⇉ f (ex▹ ⊛_)

breadthfirst : Tree A → Colist A
breadthfirst t = ex $ br t overR
