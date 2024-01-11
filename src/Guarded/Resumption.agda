{-# OPTIONS --guarded #-}
module Guarded.Resumption where

open import Prelude
open import Data.Empty
open import Data.Unit
open import LaterG

-- can be viewed as a variation on a Mealy machine
-- or a combination of a partiality and (generalized) state monad

private variable
  ℐ 𝒪 A B : 𝒰

data Res (ℐ 𝒪 A : 𝒰) : 𝒰 where
  ret  : A → Res ℐ 𝒪 A
  cont : (ℐ → 𝒪 × ▹ Res ℐ 𝒪 A) → Res ℐ 𝒪 A

module Res-code where
  Code-body : ▹ (Res ℐ 𝒪 A → Res ℐ 𝒪 A → 𝒰 (level-of-type A))
            → Res ℐ 𝒪 A → Res ℐ 𝒪 A → 𝒰 (level-of-type A)
  Code-body C▹ (ret x)   (ret y)   = x ＝ y
  Code-body C▹ (ret _)   (cont _)  = Lift _ ⊥
  Code-body C▹ (cont _)  (ret _)   = Lift _ ⊥
  Code-body C▹ (cont kx) (cont ky) = ∀ a → (kx a .fst ＝ ky a .fst) × ▸ (C▹ ⊛ kx a .snd ⊛ ky a .snd)

  Code : Res ℐ 𝒪 A → Res ℐ 𝒪 A → 𝒰 (level-of-type A)
  Code = fix Code-body

  Code-cc-eq : {kx ky : ℐ → 𝒪 × ▹ Res ℐ 𝒪 A}
             → Code (cont kx) (cont ky) ＝ ∀ a → (kx a .fst ＝ ky a .fst) × ▸ (Code ⍉ (kx a .snd) ⊛ ky a .snd)
  Code-cc-eq {ℐ} {kx} {ky} i = (𝒾 : ℐ) → ((kx 𝒾 .fst ＝ ky 𝒾 .fst) × (▹[ α ] pfix Code-body i α (kx 𝒾 .snd α) (ky 𝒾 .snd α)))

  Code-cc⇉ : {kx ky : ℐ → 𝒪 × ▹ Res ℐ 𝒪 A}
           → Code (cont kx) (cont ky)
           → ∀ a → (kx a .fst ＝ ky a .fst) × ▸ (Code ⍉ (kx a .snd) ⊛ ky a .snd)
  Code-cc⇉ = transport Code-cc-eq

  ⇉Code-cc : {kx ky : ℐ → 𝒪 × ▹ Res ℐ 𝒪 A}
           → (∀ a → (kx a .fst ＝ ky a .fst) × ▸ (Code ⍉ (kx a .snd) ⊛ ky a .snd))
           → Code (cont kx) (cont ky)
  ⇉Code-cc = transport (sym Code-cc-eq)

  Code-refl-body : ▹ ((r : Res ℐ 𝒪 A) → Code r r)
                 → (r : Res ℐ 𝒪 A) → Code r r
  Code-refl-body C▹ (ret a)  = refl
  Code-refl-body C▹ (cont k) = ⇉Code-cc λ 𝒾 → refl , (C▹ ⊛ k 𝒾 .snd)

  Code-refl : (r : Res ℐ 𝒪 A) → Code r r
  Code-refl = fix Code-refl-body

  encode : {p q : Res ℐ 𝒪 A} → p ＝ q → Code p q
  encode {p} {q} e = subst (Code p) e (Code-refl p)

  decode : (p q : Res ℐ 𝒪 A) → Code p q → p ＝ q
  decode (ret x)   (ret y)   c = ap ret c
  decode (cont kx) (cont ky) c =
    let ke = Code-cc⇉ c in
    ap cont (fun-ext λ 𝒾 → ×-path (ke 𝒾 .fst) (▹-ext λ α → decode (kx 𝒾 .snd α) (ky 𝒾 .snd α) (ke 𝒾 .snd α)))

ret-inj : {x y : A}
        → ret {ℐ} {𝒪} x ＝ ret y → x ＝ y
ret-inj = Res-code.encode

cont-inj : {kx ky : ℐ → 𝒪 × ▹ Res ℐ 𝒪 A}
         → cont kx ＝ cont ky → kx ＝ ky
cont-inj {kx} {ky} e =
  let ke = Res-code.Code-cc⇉ (Res-code.encode e) in
  fun-ext λ 𝒾 → ×-path (ke 𝒾 .fst) (▹-ext λ α → Res-code.decode (kx 𝒾 .snd α) (ky 𝒾 .snd α) (ke 𝒾 .snd α))

>>=ʳ-body : (A → Res ℐ 𝒪 B)
          → ▹ (Res ℐ 𝒪 A → Res ℐ 𝒪 B)
          → Res ℐ 𝒪 A → Res ℐ 𝒪 B
>>=ʳ-body f b▹ (ret a)   = f a
>>=ʳ-body f b▹ (cont tr) = cont λ 𝒾 → let (o , tr▹) = tr 𝒾 in
                                      o , (b▹ ⊛ tr▹)

_>>=ʳ_ : Res ℐ 𝒪 A → (A → Res ℐ 𝒪 B) → Res ℐ 𝒪 B
_>>=ʳ_ p f = fix (>>=ʳ-body f) p

step : (ℐ → 𝒪 × A) → Res ℐ 𝒪 A
step f = cont λ 𝒾 → let (o , a) = f 𝒾 in
                    o , next (ret a)

tick : Res ℐ ℐ ⊤
tick = cont λ 𝒾 → 𝒾 , next (ret tt)

-- interleaving scheduler

sched-body : ▹ (Res ℐ 𝒪 A → Res ℐ 𝒪 A → Res ℐ 𝒪 A)
           → Res ℐ 𝒪 A → Res ℐ 𝒪 A → Res ℐ 𝒪 A
sched-body s▹ (ret a)  q = ret a
sched-body s▹ (cont c) q = cont λ 𝒾 → let (o , t) = c 𝒾 in
                                       (o , (s▹ ⊛ next q ⊛ t))

sched : Res ℐ 𝒪 A → Res ℐ 𝒪 A → Res ℐ 𝒪 A
sched = fix sched-body
