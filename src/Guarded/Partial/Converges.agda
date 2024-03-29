{-# OPTIONS --guarded #-}
module Guarded.Partial.Converges where

open import Prelude
open import Data.Empty
open import Data.Nat

open import LaterG
open import Guarded.Partial

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- convergence (propositional)

_⇓ᵖ_ : Part A → A → 𝒰 (level-of-type A)
_⇓ᵖ_ {A} p x = ∃[ n ꞉ ℕ ] (p ＝ delay-by n x)

_⇓ : Part A → 𝒰 (level-of-type A)
_⇓ {A} p = Σ[ a ꞉ A ] p ⇓ᵖ a

now⇓ : {x : A}
     → now x ⇓ᵖ x
now⇓ = ∣ 0 , refl ∣₁

δ⇓ : {p : Part A} {x : A}
   → p ⇓ᵖ x → δᵖ p ⇓ᵖ x
δ⇓ = map λ where (n , e) → suc n , ap later (▹-ext λ α → e)

spin⇓ : {p : Part A} {x : A}
      → ∀ n → p ⇓ᵖ x → spin n p ⇓ᵖ x
spin⇓  zero   = id
spin⇓ (suc n) = δ⇓ ∘ spin⇓ n

-- we cannot go in the other direction however

map⇓ : {p : Part A} {a : A}
     → (f : A → B)
     → p ⇓ᵖ a
     → mapᵖ f p ⇓ᵖ f a
map⇓ {a} f =
  map λ where (n , e) → n , ap (mapᵖ f) e ∙ delay-by-mapᵖ a n

ap⇓ : {p : Part A} {g : A → B} {a : A}
    → (f : Part (A → B))
    → f ⇓ᵖ g
    → p ⇓ᵖ a
    → (apᵖ f p) ⇓ᵖ g a
ap⇓ {g} {a} f fg pa =
  ∥-∥₁.rec! (λ where
    (n , eᶠ) → map (λ where
      (m , e) → max n m , ap² apᵖ eᶠ e
                        ∙ delay-by-apᵖ g n a m) pa) fg

bind⇓ : {p : Part A} {a : A} {b : B}
      → (f : A → Part B)
      → p ⇓ᵖ a
      → f a ⇓ᵖ b
      → (p >>=ᵖ f) ⇓ᵖ b
bind⇓ {a} {b} f pa fab =
  ∥-∥₁.rec! (λ where
    (n , e) → map (λ where
      (m , eᶠ) → (n + m , ap (_>>=ᵖ f) e
                        ∙ delay-by-bindᵖ f a n
                        ∙ ap (iter n δᵖ) eᶠ
                        ∙ sym (iter-add n m δᵖ (now b)))) fab) pa

-- weak bisimilarity

_＝⇓_ : Part A → Part A → 𝒰 (level-of-type A)
_＝⇓_ p q = ∀ x → (p ⇓ᵖ x → q ⇓ᵖ x) × (q ⇓ᵖ x → p ⇓ᵖ x)

＝⇓-refl : {p : Part A}
         → p ＝⇓ p
＝⇓-refl x = id , id

＝⇓-sym : {p q : Part A}
         → p ＝⇓ q → q ＝⇓ p
＝⇓-sym pq x = (pq x .snd) , (pq x .fst)

＝⇓-trans : {p q r : Part A}
          → p ＝⇓ q → q ＝⇓ r → p ＝⇓ r
＝⇓-trans pq qr x = qr x .fst ∘ pq x .fst , pq x .snd ∘ qr x .snd
