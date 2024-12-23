{-# OPTIONS --guarded #-}
module Guarded.BushA where

open import Prelude

open import LaterG
open import Guarded.Partial

private variable
  ℓ : Level    -- TODO generalize levels?
  Aⁿ Aˡ B : 𝒰 ℓ

-- guarded (top-down?) binary tree automaton (with data in nodes and leaves)
-- based on http://www.cs.nott.ac.uk/~psztxa/publ/tlca01a.pdf

data Bush (Aⁿ Aˡ B : 𝒰 ℓ) : 𝒰 ℓ where
  bsh : (Aˡ → B) → (Aⁿ → ▹ Bush Aⁿ Aˡ (Bush Aⁿ Aˡ B)) → Bush Aⁿ Aˡ B

mapᵇ-body : ▹ ({B C : 𝒰 ℓ} → (B → C) → Bush Aⁿ Aˡ B → Bush Aⁿ Aˡ C)
          →    {B C : 𝒰 ℓ} → (B → C) → Bush Aⁿ Aˡ B → Bush Aⁿ Aˡ C
mapᵇ-body m▹ f (bsh fb b▹) = bsh (f ∘ fb) λ a α → m▹ α (m▹ α f) (b▹ a α)

mapᵇ : {B C : 𝒰 ℓ} → (B → C) → Bush Aⁿ Aˡ B → Bush Aⁿ Aˡ C
mapᵇ {B} {C} f = fix mapᵇ-body {B} {C} f

mapᵇ-id : (B : 𝒰 ℓ)
        → (b : Bush Aⁿ Aˡ B)
        → mapᵇ id b ＝ b
mapᵇ-id {Aⁿ} {Aˡ} =
  fix λ ih▹ B → λ where
    b@(bsh a b▹) →
        mapᵇ id b
          =⟨ ap (λ q → q id b) (fix-path mapᵇ-body) ⟩
        mapᵇ-body (next λ {A} {B} → mapᵇ) id b
          =⟨ ap (bsh a) (fun-ext λ a → ▹-ext λ α →
                             ap (λ q → mapᵇ q (b▹ a α)) (fun-ext λ b′ → ih▹ α B b′)
                           ∙ ih▹ α (Bush Aⁿ Aˡ B) (b▹ a α)) ⟩
        b
          ∎

mapᵇ-comp : (B C D : 𝒰 ℓ) (f : B → C) (g : C → D)
          → (b : Bush Aⁿ Aˡ B)
          → mapᵇ g (mapᵇ f b) ＝ mapᵇ (g ∘ f) b
mapᵇ-comp {ℓ} {Aⁿ} {Aˡ} =
  fix λ ih▹ B C D f g → λ where
    b@(bsh fx b▹) →
        mapᵇ g (mapᵇ f b)
          =⟨ ap (λ q → mapᵇ g (q f b)) (fix-path mapᵇ-body) ⟩
        mapᵇ g (mapᵇ-body (next λ {B} {C} → mapᵇ) f b)
          =⟨ ap (λ q → q g (mapᵇ-body (next λ {B} {C} → mapᵇ) f b)) (fix-path mapᵇ-body) ⟩
        mapᵇ-body (next λ {B} {C} → mapᵇ) g (mapᵇ-body (next (λ {B} {C} → mapᵇ)) f b)
          =⟨ ap (bsh (g ∘ f ∘ fx)) (fun-ext λ a → ▹-ext λ α →
                                      ih▹ α (Bush Aⁿ Aˡ B) (Bush Aⁿ Aˡ C) (Bush Aⁿ Aˡ D)
                                            ((λ {B C : 𝒰 ℓ} → mapᵇ {ℓ} {B} {C}) f)
                                            ((λ {B C : 𝒰 ℓ} → mapᵇ {ℓ} {B} {C}) g)
                                            (b▹ a α)
                                    ∙ ap (λ q → mapᵇ q (b▹ a α)) (fun-ext λ b′ → ih▹ α B C D f g b′)) ⟩
        mapᵇ-body (next λ {B} {C} → mapᵇ) (g ∘ f) b
          =⟨ ap (λ q → q (g ∘ f) b) (fix-path mapᵇ-body) ⟨
        mapᵇ (g ∘ f) b
          ∎

-- constant bush

pureᵇ-body : ▹ ({B : 𝒰 ℓ} → B → Bush Aⁿ Aˡ B)
           →    {B : 𝒰 ℓ} → B → Bush Aⁿ Aˡ B
pureᵇ-body p▹ b = bsh (λ _ → b) λ _ α → p▹ α (p▹ α b)

pureᵇ : ∀ {B : 𝒰 ℓ} → B → Bush Aⁿ Aˡ B
pureᵇ = fix pureᵇ-body

data BT (Aⁿ Aˡ : 𝒰 ℓ) : 𝒰 ℓ where
  L  : Aˡ → BT Aⁿ Aˡ
  Sp : BT Aⁿ Aˡ → Aⁿ → BT Aⁿ Aˡ → BT Aⁿ Aˡ

lamBT-body : ▹ ({B : 𝒰 ℓ} → (BT Aⁿ Aˡ → B) → Bush Aⁿ Aˡ B)
           →    {B : 𝒰 ℓ} → (BT Aⁿ Aˡ → B) → Bush Aⁿ Aˡ B
lamBT-body l▹ {B} f = bsh (f ∘ L) λ a α → l▹ α λ t → l▹ α λ u → f (Sp t a u)

lamBT : (BT Aⁿ Aˡ → B) → Bush Aⁿ Aˡ B
lamBT {B} = fix lamBT-body {B}

appBT-body : ▹ ({B : 𝒰 ℓ} → Bush Aⁿ Aˡ B → BT Aⁿ Aˡ → Part B)
           →    {B : 𝒰 ℓ} → Bush Aⁿ Aˡ B → BT Aⁿ Aˡ → Part B
appBT-body a▹ (bsh fb _ ) (L b)      = now (fb b)
appBT-body a▹ (bsh _  f▹) (Sp l a r) = later λ α → a▹ α (f▹ a α) l >>=ᵖ λ x → a▹ α x r

appBT : Bush Aⁿ Aˡ B → BT Aⁿ Aˡ → Part B
appBT {B} = fix appBT-body {B}

-- example: evaluating a numerical expression

open import Data.Nat

data Op : 𝒰 where
  Plus Mul : Op

eval : Bush Op ℕ ℕ
eval = fix λ e▹ → bsh id (go e▹)
  where
  go : ▹ Bush Op ℕ ℕ → Op → ▹ Bush Op ℕ (Bush Op ℕ ℕ)
  go e▹ Plus = (λ l r → mapᵇ (λ a → mapᵇ (λ b → a + b) r) l) ⍉ e▹ ⊛ e▹
  go e▹ Mul  = (λ l r → mapᵇ (λ a → mapᵇ (λ b → a · b) r) l) ⍉ e▹ ⊛ e▹
