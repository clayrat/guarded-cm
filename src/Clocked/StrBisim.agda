{-# OPTIONS --guarded #-}
module Clocked.StrBisim where

open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.List

open import Later
open import Clocked.Stream

private variable
  A B C : 𝒰
  k : Cl

data _[_≋ᵏ_] (k : Cl) : Stream A → Stream A → 𝒰 (ℓsuc 0ℓ) where
  bcons : ∀ {s1 s2 : Stream A}
        → headˢ s1 ＝ headˢ s2
        → ▹ k (k [ tailˢ s1 ≋ᵏ tailˢ s2 ])
        → k [ s1 ≋ᵏ s2 ]

_≋_ : Stream A → Stream A → 𝒰 (ℓsuc 0ℓ)
s1 ≋ s2 = ∀ k → k [ s1 ≋ᵏ s2 ]

-- properties

≋-reflᵏ : (s : Stream A) → k [ s ≋ᵏ s ]
≋-reflᵏ {k} = fix {k = k} λ b▹ s → bcons refl (b▹ ⊛ next (tailˢ s))

≋-refl : (s : Stream A) → s ≋ s
≋-refl s k = ≋-reflᵏ s

eq-≋ᵏ : ∀ {s1 s2 : Stream A} → s1 ＝ s2 → k [ s1 ≋ᵏ s2 ]
eq-≋ᵏ {k} {s1} {s2} eq = subst (λ q → k [ q ≋ᵏ s2 ]) (sym eq) (≋-reflᵏ s2)

eq-≋ : {s1 s2 : Stream A} → s1 ＝ s2 → s1 ≋ s2
eq-≋ {s1} {s2} eq = subst (_≋ s2) (sym eq) (≋-refl s2)

≋-eq-head : {s1 s2 : Stream A} → s1 ≋ s2 → headˢ s1 ＝ headˢ s2
≋-eq-head b with (b k0)
... | bcons eq eq1 = eq

≋-transᵏ-e : (s1 s2 s3 : Stream A) → k [ s1 ≋ᵏ s2 ] → k [ s2 ≋ᵏ s3 ] → k [ s1 ≋ᵏ s3 ]
≋-transᵏ-e {k = k} =
  fix λ t▹ s1 s2 s3 → λ where
    (bcons e12 b12) (bcons e23 b23) →
      bcons (e12 ∙ e23) (t▹ ⊛ (next $ tailˢ s1) ⊛ (next $ tailˢ s2) ⊛ (next $ tailˢ s3) ⊛ b12 ⊛ b23)

≋-transᵏ : {s1 s2 s3 : Stream A} → k [ s1 ≋ᵏ s2 ] → k [ s2 ≋ᵏ s3 ] → k [ s1 ≋ᵏ s3 ]
≋-transᵏ {s1} {s2} {s3} b1 b2 = ≋-transᵏ-e s1 s2 s3 b1 b2

≋-trans : {s1 s2 s3 : Stream A} → s1 ≋ s2 → s2 ≋ s3 → s1 ≋ s3
≋-trans b1 b2 k = ≋-transᵏ-e _ _ _ (b1 k) (b2 k)

≋-symᵏ : (s1 s2 : Stream A) → k [ s1 ≋ᵏ s2 ] → k [ s2 ≋ᵏ s1 ]
≋-symᵏ {k = k} =
  fix λ t▹ s1 s2 → λ where
    (bcons e12 b12)  →
      bcons (sym e12) (t▹ ⊛ (next $ tailˢ s1) ⊛ (next $ tailˢ s2) ⊛ b12)

≋-sym : (s1 s2 : Stream A) → s1 ≋ s2 → s2 ≋ s1
≋-sym s1 s2 b k = ≋-symᵏ s1 s2 (b k)

-- examples

uncons-≋ᵏ : (s : Stream A) → k [ consˢ (headˢ s) (tailˢ s) ≋ᵏ s ]
uncons-≋ᵏ {k} s =
  bcons refl (next (subst (λ q → k [ q ≋ᵏ tailˢ s ]) (sym $ tail-consˢ (headˢ s) (tailˢ s)) (≋-reflᵏ (tailˢ s))))

uncons-≋ : (s : Stream A) → consˢ (headˢ s) (tailˢ s) ≋ s
uncons-≋ s k = uncons-≋ᵏ s

even-odd-≋ᵏ : (s : Stream A)
            → k [ interleaveˢ (eo s) (evens s) ≋ᵏ s ]
even-odd-≋ᵏ {k} =
  fix {k = k} λ prf▹ s →
    bcons refl $ next $
    subst (λ q → k [ q ≋ᵏ tailˢ s ])
          (sym $ tail-interleaveˢ (eo s) (evens s)) $
    bcons refl $
    subst (λ q → ▹ k (k [ q ≋ᵏ tailˢ (tailˢ s) ]))
          (  ap (interleaveˢ (eo (tailˢ (tailˢ s)))) (sym (tail-evens s))
           ∙ ap (λ q → interleaveˢ q (tailˢ (evens s))) (sym (tail-eoˢ s))
           ∙ sym (tail-interleaveˢ (evens s) (tailˢ (eo s)))) $
    prf▹ ⊛ next (tailˢ (tailˢ s))

even-odd-≋ : (s : Stream A)
           → interleaveˢ (eo s) (evens s) ≋ s
even-odd-≋ s k = even-odd-≋ᵏ s
