{-# OPTIONS --guarded #-}
module Guarded.Hofmann where

open import Prelude
open import Data.Sum
open import LaterG
open import Guarded.Colist

private variable
  A B : 𝒰

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

data RouF (A : 𝒰) (R▹ : ▹ 𝒰) : 𝒰 where
  overRF : RouF A R▹
  nextRF : ((▸ R▹ → ▹ Colist A) → Colist A) → RouF A R▹

Rou : 𝒰 → 𝒰
Rou A = fix (RouF A)

Rou⇉ : Rou A
     → RouF A (next (Rou A))
Rou⇉ {A} = transport (fix-path (RouF A))

⇉Rou : RouF A (next (Rou A))
     → Rou A
⇉Rou {A} = transport (sym $ fix-path (RouF A))

{-
Rou-next : 𝒰 → ▹ 𝒰 → 𝒰
Rou-next A rou▹ = (▸ rou▹ → ▹ Colist A) → Colist A

Rou-body : 𝒰 → ▹ 𝒰 → 𝒰
Rou-body A rou▹ = ⊤ ⊎ (Rou-next A rou▹)

Rou : 𝒰 → 𝒰
Rou A = fix (Rou-body A)

nextR⇉ : Rou-next A (dfix (Rou-body A))
       → (▹ Rou A → ▹ Colist A) → Colist A
nextR⇉ {A} = subst (Rou-next A) (pfix (Rou-body A))

⇉nextR : ((▹ Rou A → ▹ Colist A) → Colist A)
       → Rou-next A (dfix (Rou-body A))
⇉nextR {A} = subst (Rou-next A) (sym $ pfix (Rou-body A))
-}
-- constructors & recursor

overR : Rou A
overR = ⇉Rou overRF

nextR : ((▹ Rou A → ▹ Colist A) → Colist A) → Rou A
nextR = ⇉Rou ∘ nextRF

rec : B → (((▹ Rou A → ▹ Colist A) → Colist A) → B)
    → Rou A → B
rec b nf r with Rou⇉ r
... | overRF   = b
... | nextRF f = nf f

-- the algorithm

unfold : (▹ Rou A → ▹ Colist A) → Rou A → ▹ Colist A
unfold kf =
  rec (kf (next overR))
      (λ f → next (f kf))

br : Tree A → Rou A → Rou A
br (Leaf a)   c = nextR (λ kf → ccons a (unfold kf c))
br (Br l a r) c = nextR (λ kf → ccons a (unfold (kf ∘ ((br l ∘ br r) ⍉_)) c))

ex : Rou A → Colist A
ex {A} = fix λ ex▹ →
  rec cnil
      (λ f → f (ex▹ ⊛_))

breadthfirst : Tree A → Colist A
breadthfirst t = ex $ br t overR

