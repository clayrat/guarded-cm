{-# OPTIONS --guarded #-}
module Guarded.Bush where

open import Prelude
open import Data.List

open import LaterG
open import Guarded.Partial

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- http://www.cs.nott.ac.uk/~psztxa/publ/tlca01a.pdf

data Bush (A : 𝒰 ℓ) : 𝒰 ℓ  where
  bsh : A → ▹ Bush (Bush A) → Bush A

mapᵇ-body : ▹ (∀ {A : 𝒰 ℓ} {B : 𝒰 ℓ′} → (A → B) → Bush A → Bush B)
          → ∀ {A : 𝒰 ℓ} {B : 𝒰 ℓ′} → (A → B) → Bush A → Bush B
mapᵇ-body m▹ f (bsh a b▹) = bsh (f a) λ α → m▹ α (m▹ α f) (b▹ α)

mapᵇ : (A → B) → Bush A → Bush B
mapᵇ {A} {B} f = fix mapᵇ-body {A} {B} f

mapᵇ-id : (A : 𝒰 ℓ)
        → (b : Bush A)
        → mapᵇ id b ＝ b
mapᵇ-id = fix λ ih▹ A → λ where
  b@(bsh a b▹) →
      mapᵇ id b
        ＝⟨ ap (λ q → q id b) (fix-path mapᵇ-body) ⟩
      mapᵇ-body (next (λ {A} {B} → mapᵇ)) id b
        ＝⟨ ap (bsh a) (▹-ext λ α → ap (λ q → mapᵇ q (b▹ α)) (fun-ext λ b′ → ih▹ α A b′)
                                 ∙ ih▹ α (Bush A) (b▹ α)) ⟩
      b
        ∎

-- constant bush

pureᵇ-body : ▹ (∀ {A : 𝒰 ℓ} → A → Bush A)
           → ∀ {A : 𝒰 ℓ} → A → Bush A
pureᵇ-body b▹ a = bsh a λ α → b▹ α (b▹ α a)

pureᵇ : ∀ {A : 𝒰 ℓ} → A → Bush A
pureᵇ = fix pureᵇ-body

data BT : 𝒰 where
  L : BT
  Sp : BT → BT → BT

lamBT-body : ▹ (∀ {A : 𝒰 ℓ} → (BT → A) → Bush A)
           → ∀ {A : 𝒰 ℓ} → (BT → A) → Bush A
lamBT-body l▹ {A} f = bsh (f L) λ α → l▹ α λ t → l▹ α λ u → f (Sp t u)

lamBT : (BT → A) → Bush A
lamBT {A} = fix lamBT-body {A}

appBT-body : ▹ (∀ {A : 𝒰 ℓ} → Bush A → BT → Part A)
           → ∀ {A : 𝒰 ℓ} → Bush A → BT → Part A
appBT-body a▹     (bsh a f)  L       = now a
appBT-body a▹ {A} (bsh a f) (Sp l r) = later λ α → a▹ α (f α) l >>=ᵖ λ b → a▹ α b r

appBT : Bush A → BT → Part A
appBT {A} = fix appBT-body {A}

