{-# OPTIONS --guarded #-}
module Guarded.Mealy.Resumption where

open import Prelude
open import LaterG

-- https://www.cl.cam.ac.uk/~nk480/simple-frp.pdf
-- Krishnaswami, [2013] "Higher-Order Functional Reactive Programming without Spacetime Leaks"

-- a variation on a Mealy machine

private variable
  ℐ O A : 𝒰

data Res (ℐ O A : 𝒰) : 𝒰 where
 ret  : A → Res ℐ O A
 cont : (ℐ → O × ▹ Res ℐ O A) → Res ℐ O A

-- interleaving scheduler

sched-body : ▹ (Res ℐ O A → Res ℐ O A → Res ℐ O A)
           → Res ℐ O A → Res ℐ O A → Res ℐ O A
sched-body s▹ (ret a)  q = ret a
sched-body s▹ (cont c) q = cont λ 𝒾 → let (o , t) = c 𝒾 in
                                       (o , (s▹ ⊛ next q ⊛ t))

sched : Res ℐ O A → Res ℐ O A → Res ℐ O A
sched = fix sched-body

