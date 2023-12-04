{-# OPTIONS --guarded #-}
module Guarded.Partial.Fin where

open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.Sum
open import LaterG

open import Guarded.Partial

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

-- finiteness

is-finiteᵖ : Part A → 𝒰 (level-of-type A)
is-finiteᵖ {A} p = ∃[ n ꞉ ℕ ] (Σ[ x ꞉ A ] (p ＝ delay-by n x))

record FinPart (A : 𝒰 ℓ) : 𝒰 ℓ where
  constructor mkFinPart
  field
    pt : Part A
    isFin : is-finiteᵖ pt

open FinPart

nowᶠ : A → FinPart A
nowᶠ x = mkFinPart (now x) ∣ 0 , x , refl ∣₁

δᶠ : FinPart A → FinPart A
δᶠ (mkFinPart pt if) =
  mkFinPart (δᵖ pt)
    (∥-∥₁.map (λ where
                   (n , x , e) → suc n , x , ap later (▹-ext (next e)))
               if)

mapᶠ : (A → B) → FinPart A → FinPart B
mapᶠ f (mkFinPart pt if) =
  mkFinPart (mapᵖ f pt)
   (∥-∥₁.map (λ where
                 (n , x , e) → n , f x , ap (mapᵖ f) e ∙ delay-by-mapᵖ x n) if)

apᶠ : FinPart (A → B) → FinPart A → FinPart B
apᶠ (mkFinPart ptf iff) (mkFinPart pta ifa) =
  mkFinPart (apᵖ ptf pta)
    (∥-∥₁.rec²!
        (λ where
            (nf , xf , ef) (na , xa , ea) → ∣ max nf na , xf xa , ap² apᵖ ef ea ∙ delay-by-apᵖ xf nf xa na ∣₁)
          iff ifa)

_>>=ᶠ_ : FinPart A → (A → FinPart B) → FinPart B
(mkFinPart p if) >>=ᶠ f =
  mkFinPart (p >>=ᵖ (pt ∘ f))
    (∥-∥₁.rec!
       (λ where
           (n , x , e) →
              ∥-∥₁.map (λ where
                           (m , y , e1) → n + m , y , ap (_>>=ᵖ (pt ∘ f)) e ∙ delay-by-bindᵖ (pt ∘ f) x n ∙ ap (iter n δᵖ) e1 ∙ sym (iter-add n m δᵖ (now y)))
                       (f x .isFin))
       if)
