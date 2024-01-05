{-# OPTIONS --guarded #-}
module Guarded.Conat.Stream where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Dec

open import LaterG
open import Guarded.Conat
open import Guarded.Conat.Arith
open import Guarded.Stream
open import Guarded.Stream.Quantifiers

private variable
  ℓ : Level
  A : 𝒰 ℓ

-- stream interaction

to-streamᶜ-body : ▹ (ℕ∞ → Stream Bool) → ℕ∞ → Stream Bool
to-streamᶜ-body ts▹  coze     = repeatˢ false
to-streamᶜ-body ts▹ (cosu n▹) = cons true (ts▹ ⊛ n▹)

-- Escardo's ι
to-streamᶜ : ℕ∞ → Stream Bool
to-streamᶜ = fix to-streamᶜ-body

infty-stream : to-streamᶜ infty ＝ repeatˢ true
infty-stream = fix λ prf▹ →
  to-streamᶜ infty
    ＝⟨ ap (_$ infty) (fix-path to-streamᶜ-body) ⟩
  to-streamᶜ-body (next to-streamᶜ) ⌜ infty ⌝
    ＝⟨ ap! (fix-path cosu) ⟩
  to-streamᶜ-body (next to-streamᶜ) (cosu (next infty))
    ＝⟨⟩
  cons true ⌜ next (to-streamᶜ infty) ⌝
    ＝⟨ ap! (▹-ext prf▹) ⟩
  cons true (next (repeatˢ true))
    ＝˘⟨ fix-path (cons true) ⟩
  repeatˢ true
    ∎

to-streamᶜ-inj : (n m : ℕ∞) → to-streamᶜ n ＝ to-streamᶜ m → n ＝ m
to-streamᶜ-inj = fix λ prf▹ →
  λ where
      coze       coze     e → refl
      coze      (cosu _)  e → absurd (false≠true (cons-inj e .fst))
      (cosu _)   coze     e → absurd (true≠false (cons-inj e .fst))
      (cosu n▹) (cosu m▹) e →
        ap cosu (▹-ext λ α → prf▹ α (n▹ α) (m▹ α)
                                  ((λ i → pfix to-streamᶜ-body (~ i) α (n▹ α))
                                   ∙ ▹-ap (cons-inj e .snd) α
                                   ∙ λ i → pfix to-streamᶜ-body i α (m▹ α)))

-- TODO stream hlevel
--to-streamᶜ-emb : is-embedding to-streamᶜ
--to-streamᶜ-emb = set-injective→is-embedding {!!} λ {x} {y} → to-streamᶜ-inj x y

decreasing : Stream Bool → 𝒰
decreasing = Adjˢ (λ p q → p or (not q) ＝ true)

-- TODO upstream
or-neg : (a : Bool) → a or not a ＝ true
or-neg true  = refl
or-neg false = refl

to-streamᶜ-decreasing : (n : ℕ∞) → decreasing (to-streamᶜ n)
to-streamᶜ-decreasing =
  fix λ ih▹ → λ where
    coze      → repeat-adj or-neg false
    (cosu n▹) →
      Adj-cons (next refl) λ α → transport (λ i → decreasing (pfix to-streamᶜ-body (~ i) α (n▹ α))) ((ih▹ ⊛ n▹) α)

-- Cantor encoding (single bit)

to-Cantorᶜ-body : ▹ (ℕ∞ → Stream Bool) → ℕ∞ → Stream Bool
to-Cantorᶜ-body ts▹  coze     = cons-δ true (repeatˢ false)
to-Cantorᶜ-body ts▹ (cosu n▹) = cons false (ts▹ ⊛ n▹)

to-Cantorᶜ : ℕ∞ → Stream Bool
to-Cantorᶜ = fix to-Cantorᶜ-body

Cantor-infty : to-Cantorᶜ infty ＝ repeatˢ false
Cantor-infty =
  fix λ ih▹ →
    ap (cons false) (▹-ext λ α → (λ i → dfix to-Cantorᶜ-body α (pfix cosu i α))
                               ∙ (λ i → pfix to-Cantorᶜ-body i α infty)
                               ∙ ih▹ α
                               ∙ (λ i → pfix (cons false) (~ i) α))

-- stream closeness

closenessˢ-body : is-discrete A
                → ▹ (Stream A → Stream A → ℕ∞) → Stream A → Stream A → ℕ∞
closenessˢ-body d c▹ (cons h₁ t▹₁) (cons h₂ t▹₂) with (is-discrete-β d h₁ h₂)
... | yes e   = cosu (c▹ ⊛ t▹₁ ⊛ t▹₂)
... | no ctra = coze

closenessˢ : is-discrete A
           → Stream A → Stream A → ℕ∞
closenessˢ d = fix (closenessˢ-body d)

closenessˢ-refl : (d : is-discrete A)
                → (s : Stream A) → closenessˢ d s s ＝ infty
closenessˢ-refl d = fix (go d)
  where
  go : ∀ {A} → (d : is-discrete A)
     → ▹ ((s : Stream A) → closenessˢ d s s ＝ infty)
     → (s : Stream A) → closenessˢ d s s ＝ infty
  go d ih▹ (cons h t▹) with (is-discrete-β d h h)
  ... | yes e = ap cosu (▹-ext λ α → (λ i → pfix (closenessˢ-body d) i α (t▹ α) (t▹ α))
                                   ∙ ih▹ α (t▹ α)
                                   ∙ ▹-ap (sym $ pfix cosu) α)
  ... | no ctra = absurd (ctra refl)

close∞→equalˢ : (d : is-discrete A)
             → (s t : Stream A)
             → closenessˢ d s t ＝ infty → s ＝ t
close∞→equalˢ d = fix (go d)
  where
  go : ∀ {A} → (d : is-discrete A)
     → ▹ ((s t : Stream A) → closenessˢ d s t ＝ infty → s ＝ t)
     → (s t : Stream A) → closenessˢ d s t ＝ infty → s ＝ t
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) e with (is-discrete-β d h₁ h₂)
  ... | yes eh = ap² cons eh (▹-ext λ α → ih▹ α (t▹₁ α) (t▹₂ α)
                                             ((λ i → pfix (closenessˢ-body d) (~ i) α (t▹₁ α) (t▹₂ α))
                                              ∙ ▹-ap (cosu-inj e ∙ pfix cosu) α))
  ... | no ctra = absurd (cosu≠coze (sym e))

closenessˢ-comm : (d : is-discrete A)
                → (s t : Stream A) → closenessˢ d s t ＝ closenessˢ d t s
closenessˢ-comm d = fix (go d)
  where
  go : ∀ {A} → (d : is-discrete A) →
     ▹ ((s t : Stream A) → closenessˢ d s t ＝ closenessˢ d t s) →
       (s t : Stream A) → closenessˢ d s t ＝ closenessˢ d t s
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) with (is-discrete-β d h₁ h₂)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | yes eh with (is-discrete-β d h₂ h₁) -- AARGH
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | yes eh | yes eh′ =
    ap cosu (▹-ext λ α → (λ i → pfix (closenessˢ-body d) i α (t▹₁ α) (t▹₂ α))
                       ∙ ih▹ α (t▹₁ α) (t▹₂ α)
                       ∙ λ i → pfix (closenessˢ-body d) (~ i) α (t▹₂ α) (t▹₁ α) )
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | yes eh | no ctra′ = absurd (ctra′ (sym eh))
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | no ctra with (is-discrete-β d h₂ h₁) -- AARGH
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | no ctra | yes eh′ = absurd (ctra (sym eh′))
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | no ctra | no ctra′ = refl

closenessˢ-ultra : (d : is-discrete A)
                 → (x y z : Stream A)
                 → minᶜ (closenessˢ d x y) (closenessˢ d y z) ≤ᶜ closenessˢ d x z
closenessˢ-ultra d = fix (go d)
  where
  go : ∀ {A} → (d : is-discrete A)
     → ▹ ((x y z : Stream A) → minᶜ (closenessˢ d x y) (closenessˢ d y z) ≤ᶜ closenessˢ d x z)
     → (x y z : Stream A) → minᶜ (closenessˢ d x y) (closenessˢ d y z) ≤ᶜ closenessˢ d x z
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) with (is-discrete-β d h₁ h₂)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ with (is-discrete-β d h₂ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | yes e₂₃ with (is-discrete-β d h₁ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | yes e₂₃ | yes e₁₃ =
    s≤ᶜs λ α →
      transport (λ i → pfix minᶜ-body (~ i) α (dfix (closenessˢ-body d) α (t▹₁ α) (t▹₂ α))
                                              (dfix (closenessˢ-body d) α (t▹₂ α) (t▹₃ α))
                                            ≤ᶜ dfix (closenessˢ-body d) α (t▹₁ α) (t▹₃ α)) $
      transport (λ i → minᶜ (pfix (closenessˢ-body d) (~ i) α (t▹₁ α) (t▹₂ α))
                            (pfix (closenessˢ-body d) (~ i) α (t▹₂ α) (t▹₃ α))
                          ≤ᶜ pfix (closenessˢ-body d) (~ i) α (t▹₁ α) (t▹₃ α)) $
      ih▹ α (t▹₁ α) (t▹₂ α) (t▹₃ α)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | yes e₂₃ | no ne₁₃ =
    absurd (ne₁₃ (e₁₂ ∙ e₂₃))
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | no ne₂₃ with (is-discrete-β d h₁ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | no ne₂₃ | yes e₁₃ =
    absurd (ne₂₃ (sym e₁₂ ∙ e₁₃))
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | no ne₂₃ | no ne₁₃ =
    z≤ᶜn
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ with (is-discrete-β d h₂ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | yes e₂₃ with (is-discrete-β d h₁ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | yes e₂₃ | yes e₁₃ =
    absurd (ne₁₂ (e₁₃ ∙ sym e₂₃))
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | yes e₂₃ | no ne₁₃ =
    z≤ᶜn
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | no ne₂₃ with (is-discrete-β d h₁ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | no ne₂₃ | yes e₁₃ =
    z≤ᶜn
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | no ne₂₃ | no ne₁₃ =
    z≤ᶜn
