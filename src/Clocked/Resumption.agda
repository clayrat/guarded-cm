{-# OPTIONS --guarded #-}
module Clocked.Resumption where

open import Prelude
open import Later

-- https://www.cl.cam.ac.uk/~nk480/simple-frp.pdf
-- Krishnaswami, [2013] "Higher-Order Functional Reactive Programming without Spacetime Leaks"

-- a variation on a Mealy machine

private variable
  ℐ O A : 𝒰
  k : Cl

data gRes (k : Cl) (ℐ O A : 𝒰) : 𝒰 where
 ret  : A → gRes k ℐ O A
 cont : (ℐ → O × ▹ k (gRes k ℐ O A)) → gRes k ℐ O A

Res : 𝒰 → 𝒰 → 𝒰 → 𝒰
Res ℐ O A = ∀ k → gRes k ℐ O A

schedᵏ-body : ▹ k (gRes k ℐ O A → gRes k ℐ O A → gRes k ℐ O A)
            → gRes k ℐ O A → gRes k ℐ O A → gRes k ℐ O A
schedᵏ-body s▹ (ret a)  q = ret a
schedᵏ-body s▹ (cont c) q = cont λ 𝒾 → let (o , t) = c 𝒾 in
                                       (o , (s▹ ⊛ next q ⊛ t))

schedᵏ : gRes k ℐ O A → gRes k ℐ O A → gRes k ℐ O A
schedᵏ = fix schedᵏ-body

sched : Res ℐ O A → Res ℐ O A → Res ℐ O A
sched p q k = schedᵏ (p k) (q k)

