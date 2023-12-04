{-# OPTIONS --guarded #-}
module Guarded.Conat.Stream where

open import Prelude
open import Data.Empty
open import Data.Bool

open import LaterG
open import Guarded.Conat
open import Guarded.Stream

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
  to-streamᶜ-body (next to-streamᶜ) infty
    ＝⟨ ap (to-streamᶜ-body (next to-streamᶜ)) (fix-path cosu) ⟩
  to-streamᶜ-body (next to-streamᶜ) (cosu (next infty))
    ＝⟨⟩
  cons true (next (to-streamᶜ infty))
    ＝⟨ ap (cons true) (▹-ext prf▹) ⟩
  cons true (next (repeatˢ true))
    ＝⟨ sym $ fix-path (cons true) ⟩
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
