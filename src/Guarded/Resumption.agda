{-# OPTIONS --guarded #-}
module Guarded.Resumption where

open import Prelude
open import Data.Unit
open import LaterG

-- can be viewed as a variation on a Mealy machine
-- or a combination of a partiality and (generalized) state monad

private variable
  ℐ O A B : 𝒰

data Res (ℐ O A : 𝒰) : 𝒰 where
 ret  : A → Res ℐ O A
 cont : (ℐ → O × ▹ Res ℐ O A) → Res ℐ O A

>>=ʳ-body : (A → Res ℐ O B)
          → ▹ (Res ℐ O A → Res ℐ O B)
          → Res ℐ O A → Res ℐ O B
>>=ʳ-body f b▹ (ret a)   = f a
>>=ʳ-body f b▹ (cont tr) = cont λ 𝒾 → let (o , tr▹) = tr 𝒾 in
                                      o , (b▹ ⊛ tr▹)

_>>=ʳ_ : Res ℐ O A → (A → Res ℐ O B) → Res ℐ O B
_>>=ʳ_ p f = fix (>>=ʳ-body f) p

step : (ℐ → O × A) → Res ℐ O A
step f = cont λ 𝒾 → let (o , a) = f 𝒾 in
                    o , next (ret a)

tick : Res ℐ ℐ ⊤
tick = cont λ 𝒾 → 𝒾 , next (ret tt)

-- interleaving scheduler

sched-body : ▹ (Res ℐ O A → Res ℐ O A → Res ℐ O A)
           → Res ℐ O A → Res ℐ O A → Res ℐ O A
sched-body s▹ (ret a)  q = ret a
sched-body s▹ (cont c) q = cont λ 𝒾 → let (o , t) = c 𝒾 in
                                       (o , (s▹ ⊛ next q ⊛ t))

sched : Res ℐ O A → Res ℐ O A → Res ℐ O A
sched = fix sched-body

