{-# OPTIONS --guarded #-}
module Guarded.Loeb where

open import Prelude
open import Data.Empty
open import Data.Nat
open import Data.Maybe
open import Data.List

open import LaterG
open import Guarded.Partial

private variable
  ℓᵃ : Level
  A : 𝒰 ℓᵃ

loeb-body : {F : Effect} ⦃ t : Map F ⦄
     → (let module F = Effect F)
     → F.₀ (▹ F.₀ A → A)
     → ▹ F.₀ A → F.₀ A
loeb-body fs as▹ = map (_$ as▹) fs

loeb : {F : Effect} ⦃ t : Map F ⦄
     → (let module F = Effect F)
     → F.₀ (▹ F.₀ A → A) → F.₀ A
loeb fs = fix (loeb-body fs)

-- example from http://blog.sigfpe.com/2006/11/from-l-theorem-to-spreadsheet.html

len▹ : ▹ List (Part ℕ) → Part ℕ
len▹ xs▹ = later (now ∘ length ⍉ xs▹)

-- hang if undefined
probe : Maybe (Part A) → Part A
probe nothing = mapᵖ (λ v → absurd v) never
probe (just p) = p

at0▹ : ▹ List (Part ℕ) → Part ℕ
at0▹ xs▹ = later ((λ xs → probe (mnth xs 0)) ⍉ xs▹)

test : List (▹ List (Part ℕ) → Part ℕ)
test = len▹ ∷ at0▹ ∷ []

test-exec : loeb test ＝ delay-by 1 2 ∷ delay-by 2 2 ∷ []
test-exec =
  loeb test
    ＝⟨ fix-path (loeb-body test) ⟩
  len▹ (next (loeb test)) ∷ at0▹ (next (loeb test)) ∷ []
    ＝⟨⟩
  delay-by 1 (length (loeb test)) ∷ δᵖ (probe (mnth (loeb test) 0)) ∷ []
    ＝⟨ ap (λ q → δᵖ (now (length q)) ∷ δᵖ (probe (mnth q 0)) ∷ []) (fix-path (loeb-body test)) ⟩
  delay-by 1 2 ∷ delay-by 2 (length (loeb test)) ∷ []
    ＝⟨ ap (λ q → delay-by 1 2 ∷ delay-by 2 (length q) ∷ []) (fix-path (loeb-body test)) ⟩
  delay-by 1 2 ∷ delay-by 2 2 ∷ []
    ∎
