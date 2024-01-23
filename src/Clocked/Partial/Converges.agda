{-# OPTIONS --guarded #-}
module Clocked.Partial.Converges where

open import Prelude
open import Data.Empty
open import Data.Nat

open import Later
open import Clocked.Partial

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  κ : Cl

-- convergence (propositional)

_⇓ᵏᵖ_ : gPart κ A → A → 𝒰 (level-of-type A)
_⇓ᵏᵖ_ {A} p x = ∃[ n ꞉ ℕ ] (p ＝ delay-byᵏ n x)

_⇓ᵏ : gPart κ A → 𝒰 (level-of-type A)
_⇓ᵏ {A} p = Σ[ a ꞉ A ] p ⇓ᵏᵖ a

_⇓ᵖ_ : Part A → A → 𝒰 (level-of-type A)
_⇓ᵖ_ {A} p x = ∃[ n ꞉ ℕ ] (p ＝ delay-by n x)

_⇓ : Part A → 𝒰 (level-of-type A)
_⇓ {A} p = Σ[ a ꞉ A ] p ⇓ᵖ a

pure⇓ : {x : A}
     → pureᵖ x ⇓ᵖ x
pure⇓ = ∣ 0 , refl ∣₁

δ⇓ : {p : Part A} {x : A}
   → p ⇓ᵖ x → δᵖ p ⇓ᵖ x
δ⇓ = map λ where (n , e) → suc n , fun-ext λ k → ap later (▹-ext (next (happly e k)))

spin⇓ : {p : Part A} {x : A}
      → ∀ n → p ⇓ᵖ x → spin n p ⇓ᵖ x
spin⇓  zero   = id
spin⇓ (suc n) = δ⇓ ∘ spin⇓ n

unδ⇓ : {p : Part A} {x : A}
   → δᵖ p ⇓ᵖ x → p ⇓ᵖ x
unδ⇓ = map λ where
               (zero  , e) → absurd (now≠later (sym $ happly e k0))
               (suc n , e) → n , fun-ext (force (λ k₁ → ▹-ap (later-inj (happly e k₁))))

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

map²⇓ : {p : Part A} {a : A} {q : Part B} {b : B}
      → (f : A → B → C)
      → p ⇓ᵖ a
      → q ⇓ᵖ b
      → map²ᵖ f p q ⇓ᵖ f a b
map²⇓ {p} f = ap⇓ (mapᵏ f ∘ p) ∘ map⇓ f

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
                        ∙ ap (spin n) eᶠ
                        ∙ fun-ext (λ k → sym (iter-add n m δᵏ (now b)))))
                 fab) pa

-- weak bisimilarity (both converge to same value modulo the number of steps)

_＝⇓_ : Part A → Part A → 𝒰 (level-of-type A)
p ＝⇓ q = ∀ x → (p ⇓ᵖ x → q ⇓ᵖ x) × (q ⇓ᵖ x → p ⇓ᵖ x)

＝⇓-refl : {p : Part A}
         → p ＝⇓ p
＝⇓-refl x = id , id

＝→＝⇓ : {p q : Part A}
      → p ＝ q → p ＝⇓ q
＝→＝⇓ {p} e = subst (p ＝⇓_) e ＝⇓-refl

＝⇓-sym : {p q : Part A}
         → p ＝⇓ q → q ＝⇓ p
＝⇓-sym pq x = pq x .snd , pq x .fst

＝⇓-trans : {p q r : Part A}
          → p ＝⇓ q → q ＝⇓ r → p ＝⇓ r
＝⇓-trans pq qr x = qr x .fst ∘ pq x .fst , pq x .snd ∘ qr x .snd

＝⇓-δ : {p : Part A}
     → p ＝⇓ δᵖ p
＝⇓-δ x = δ⇓ , unδ⇓
