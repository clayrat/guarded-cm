{-# OPTIONS --guarded #-}
module Guarded.Bush where

open import Prelude
open import Data.List

open import LaterG
open import Guarded.Partial

private variable
  ℓ : Level    -- TODO generalize levels?
  A B C : 𝒰 ℓ

-- http://www.cs.nott.ac.uk/~psztxa/publ/tlca01a.pdf

data Bush (A : 𝒰 ℓ) : 𝒰 ℓ where
  bsh : A → ▹ Bush (Bush A) → Bush A

-- constant bush

-- TODO need an implicit version of ⊛
pureᵇ-body : ▹ ({A : 𝒰 ℓ} → A → Bush A)
           →    {A : 𝒰 ℓ} → A → Bush A
pureᵇ-body b▹ a = bsh a λ α → b▹ α (b▹ α a)

pureᵇ : ∀ {A : 𝒰 ℓ} → A → Bush A
pureᵇ = fix pureᵇ-body

-- map

mapᵇ-body : ▹ ({A B : 𝒰 ℓ} → (A → B) → Bush A → Bush B)
          →    {A B : 𝒰 ℓ} → (A → B) → Bush A → Bush B
mapᵇ-body m▹ f (bsh a b▹) = bsh (f a) λ α → m▹ α (m▹ α f) (b▹ α)

mapᵇ : {A B : 𝒰 ℓ} → (A → B) → Bush A → Bush B
mapᵇ {A} {B} f = fix mapᵇ-body {A} {B} f

mapᵇ-id : (A : 𝒰 ℓ)
        → (b : Bush A)
        → mapᵇ id b ＝ b
mapᵇ-id = fix λ ih▹ A → λ where
  b@(bsh a b▹) →
      mapᵇ id b
        =⟨ ap (λ q → q id b) (fix-path mapᵇ-body) ⟩
      mapᵇ-body (next λ {A} {B} → mapᵇ) id b
        =⟨ ap (bsh a) (▹-ext λ α → ap (λ q → mapᵇ q (b▹ α)) (fun-ext λ b′ → ih▹ α A b′)
                                 ∙ ih▹ α (Bush A) (b▹ α)) ⟩
      b
        ∎

mapᵇ-comp : (A B C : 𝒰 ℓ) (f : A → B) (g : B → C)
          → (b : Bush A)
          → mapᵇ g (mapᵇ f b) ＝ mapᵇ (g ∘ f) b
mapᵇ-comp {ℓ} = fix λ ih▹ A B C f g → λ where
  b@(bsh a b▹) →
      mapᵇ g (mapᵇ f b)
        =⟨ ap (λ q → mapᵇ g (q f b)) (fix-path mapᵇ-body) ⟩
      mapᵇ g (mapᵇ-body (next λ {A} {B} → mapᵇ) f b)
        =⟨ ap (λ q → q g (mapᵇ-body (next λ {A} {B} → mapᵇ) f b)) (fix-path mapᵇ-body) ⟩
      mapᵇ-body (next λ {A} {B} → mapᵇ) g (mapᵇ-body (next (λ {A} {B} → mapᵇ)) f b)
        =⟨ ap (bsh (g (f a))) (▹-ext λ α → ih▹ α (Bush A) (Bush B) (Bush C)
                                                  ((λ {A B : 𝒰 ℓ} → mapᵇ {ℓ} {A} {B}) f)
                                                  ((λ {A B : 𝒰 ℓ} → mapᵇ {ℓ} {A} {B}) g)
                                                  (b▹ α)
                                         ∙ ap (λ q → mapᵇ q (b▹ α)) (fun-ext λ b′ → ih▹ α A B C f g b′)) ⟩
      mapᵇ-body (next λ {A} {B} → mapᵇ) (g ∘ f) b
        =⟨ ap (λ q → q (g ∘ f) b) (fix-path mapᵇ-body) ⟨
      mapᵇ (g ∘ f) b
        ∎

data BT : 𝒰 where
  L  : BT
  Sp : BT → BT → BT

lamBT-body : ▹ ({A : 𝒰 ℓ} → (BT → A) → Bush A)
           →    {A : 𝒰 ℓ} → (BT → A) → Bush A
lamBT-body l▹ {A} f = bsh (f L) λ α → l▹ α λ t → l▹ α λ u → f (Sp t u)

lamBT : (BT → A) → Bush A
lamBT {A} = fix lamBT-body {A}

appBT-body : ▹ ({A : 𝒰 ℓ} → Bush A → BT → Part A)
           →    {A : 𝒰 ℓ} → Bush A → BT → Part A
appBT-body _  (bsh a _)  L       = now a
appBT-body a▹ (bsh _ f) (Sp l r) = later λ α → a▹ α (f α) l >>=ᵖ λ b → a▹ α b r

appBT : Bush A → BT → Part A
appBT {A} = fix appBT-body {A}

{-
app-retr-lam : {A : 𝒰 ℓ} {f : BT → A} {t : BT}
             → Σ[ n ꞉ ℕ ] (appBT (lamBT f) t ＝ delay-by n (f t))
app-retr-lam = {!!}
-}
