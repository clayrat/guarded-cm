{-# OPTIONS --guarded #-}
module Guarded.BushAFix where

open import Prelude
open import Data.List

open import LaterG
open import Guarded.Partial

private variable
  ℓ : Level    -- TODO generalize levels?
  A B X Y : 𝒰 ℓ

-- binary tree automaton via fixpoint in the universe

BushF : 𝒰 ℓ → 𝒰 ℓ → ▹ (𝒰 ℓ → 𝒰 ℓ) → 𝒰 ℓ → 𝒰 ℓ
BushF A B F▹ X = (A → X) × (B → ▸ (F▹ ⊛ (F▹ ⊛ next X)))

Bush : 𝒰 ℓ → 𝒰 ℓ → 𝒰 ℓ → 𝒰 ℓ
Bush A B = fix (BushF A B)

opaque
  Bush-path : Bush A B X ＝ BushF A B (next (Bush A B)) X
  Bush-path {A} {B} {X} = happly (fix-path (BushF A B)) X

  Bush⇉ : Bush A B X → BushF A B (next (Bush A B)) X
  Bush⇉ = transport Bush-path

  ⇉Bush : BushF A B (next (Bush A B)) X → Bush A B X
  ⇉Bush = transport (Bush-path ⁻¹)

consᵇ : (A → X) → (B → ▹ Bush A B (Bush A B X)) → Bush A B X
consᵇ af bf▹ = ⇉Bush (af , bf▹)

unconsᵇ : Bush A B X → (A → X) × (B → ▹ Bush A B (Bush A B X))
unconsᵇ = Bush⇉

headᵇ : Bush A B X → (A → X)
headᵇ = fst ∘ unconsᵇ

tail▹ᵇ : Bush A B X → B → ▹ Bush A B (Bush A B X)
tail▹ᵇ = snd ∘ unconsᵇ

opaque
  unfolding Bush⇉ ⇉Bush

  uncons-eq : (b : Bush A B X) → b ＝ consᵇ (headᵇ b) (tail▹ᵇ b)
  uncons-eq {A} s = transport⁻-transport Bush-path s ⁻¹

  head-cons : (af : A → X) (bf▹ : B → ▹ Bush A B (Bush A B X)) → headᵇ (consᵇ af bf▹) ＝ af
  head-cons {A} a as▹ = transport⁻-transport refl a

  tail-cons : {A B X : 𝒰 ℓ} (af : A → X) (bf▹ : B → ▹ Bush A B (Bush A B X)) → tail▹ᵇ (consᵇ af bf▹) ＝ bf▹
  tail-cons {A} {B} {X} a as▹ =
    transport⁻-transport
      (λ i → B → ▹[ α ] (pfix (BushF A B) (~ i) α (pfix (BushF A B) (~ i) α X)))
      as▹

-- constant bush

pureᵇ-body : ▹ ({X : 𝒰 ℓ} → X → Bush A B X)
           →    {X : 𝒰 ℓ} → X → Bush A B X
pureᵇ-body p▹ x = consᵇ (λ _ → x) λ _ α → p▹ α (p▹ α x)

pureᵇ : X → Bush A B X
pureᵇ = fix pureᵇ-body

-- map

mapᵇ-body : ▹ ({X Y : 𝒰 ℓ} → (X → Y) → Bush A B X → Bush A B Y)
          →    {X Y : 𝒰 ℓ} → (X → Y) → Bush A B X → Bush A B Y
mapᵇ-body m▹ f b =
  consᵇ (f ∘ headᵇ b) λ a α → m▹ α (m▹ α f) (tail▹ᵇ b a α)

mapᵇ : (X → Y) → Bush A B X → Bush A B Y
mapᵇ f = fix mapᵇ-body f

mapᵇ-id : (X : 𝒰 ℓ)
        → (b : Bush A B X)
        → mapᵇ id b ＝ b
mapᵇ-id {A} {B} =
  fix λ ih▹ X b →
    mapᵇ id b
      =⟨ ap (λ q → q id b) (fix-path mapᵇ-body) ⟩
    mapᵇ-body (next (λ {A} {B} → mapᵇ)) id b
      =⟨⟩
    consᵇ (headᵇ b) (λ a α → mapᵇ (mapᵇ id) (tail▹ᵇ b a α))
      =⟨ ap (consᵇ (headᵇ b)) (fun-ext λ a → ▹-ext λ α →
                                    ap (λ q → mapᵇ q (tail▹ᵇ b a α)) (fun-ext (ih▹ α X))
                                  ∙ ih▹ α (Bush A B X) (tail▹ᵇ b a α)) ⟩
    consᵇ (headᵇ b) (tail▹ᵇ b)
      =⟨ uncons-eq b ⁻¹ ⟩
    b
      ∎

mapᵇ-comp : {A B : 𝒰 ℓ} (X Y Z : 𝒰 ℓ) (f : X → Y) (g : Y → Z)
          → (b : Bush A B X)
          → mapᵇ g (mapᵇ f b) ＝ mapᵇ (g ∘ f) b
mapᵇ-comp {A} {B} = fix λ ih▹ X Y Z f g b →
      mapᵇ g (mapᵇ f b)
        =⟨ ap (λ q → mapᵇ g (q f b)) (fix-path mapᵇ-body) ⟩
      mapᵇ g (mapᵇ-body (next λ {A} {B} → mapᵇ) f b)
        =⟨ ap (λ q → q g (mapᵇ-body (next λ {A} {B} → mapᵇ) f b)) (fix-path mapᵇ-body) ⟩
      mapᵇ-body (next λ {A} {B} → mapᵇ) g (mapᵇ-body (next (λ {A} {B} → mapᵇ)) f b)
        =⟨⟩
      consᵇ (g ∘ headᵇ (consᵇ (f ∘ headᵇ b) (λ a α → mapᵇ (mapᵇ f) (tail▹ᵇ b a α))))
            (λ a α → mapᵇ (mapᵇ g) (tail▹ᵇ (consᵇ (f ∘ headᵇ b) (λ a′ α′ → mapᵇ (mapᵇ f) (tail▹ᵇ b a′ α′))) a α))
        =⟨ ap (λ q → consᵇ (g ∘ q)
                           (λ a α → mapᵇ (mapᵇ g) (tail▹ᵇ (consᵇ (f ∘ headᵇ b)
                                                                 (λ a′ α′ → mapᵇ (mapᵇ f) (tail▹ᵇ b a′ α′))) a α)))
             (head-cons (f ∘ headᵇ b) (λ a α → mapᵇ (mapᵇ f) (tail▹ᵇ b a α))) ⟩
      consᵇ (g ∘ f ∘ headᵇ b)
            (λ a α → mapᵇ (mapᵇ g) (tail▹ᵇ (consᵇ (f ∘ headᵇ b) (λ a′ α′ → mapᵇ (mapᵇ f) (tail▹ᵇ b a′ α′))) a α))
        =⟨ ap (consᵇ (g ∘ f ∘ headᵇ b))
              (fun-ext λ a → ▹-ext λ α →
                  ap (mapᵇ (mapᵇ g)) (▹-ap (happly (tail-cons (f ∘ headᵇ b) λ a′ α′ → mapᵇ (mapᵇ f) (tail▹ᵇ b a′ α′)) a) α)
                ∙ ih▹ α (Bush A B X) (Bush A B Y) (Bush A B Z)
                        (mapᵇ f) (mapᵇ g)
                        (tail▹ᵇ b a α)
                ∙ ap (λ q → mapᵇ q (tail▹ᵇ b a α)) (fun-ext (ih▹ α X Y Z f g))
                ) ⟩
      consᵇ (g ∘ f ∘ headᵇ b) (λ a α → mapᵇ (mapᵇ (g ∘ f)) (tail▹ᵇ b a α))
        =⟨⟩
      mapᵇ-body (next λ {A} {B} → mapᵇ) (g ∘ f) b
        =⟨ ap (λ q → q (g ∘ f) b) (fix-path mapᵇ-body) ⟨
      mapᵇ (g ∘ f) b
        ∎


data BT (A B : 𝒰 ℓ) : 𝒰 ℓ where
  L  : A → BT A B
  Sp : BT A B → B → BT A B → BT A B

lamBT-body : ▹ ({X : 𝒰 ℓ} → (BT A B → X) → Bush A B X)
           →    {X : 𝒰 ℓ} → (BT A B → X) → Bush A B X
lamBT-body l▹ f = consᵇ (f ∘ L) λ a α → l▹ α λ t → l▹ α λ u → f (Sp t a u)

lamBT : (BT A B → X) → Bush A B X
lamBT = fix lamBT-body

appBT-body : ▹ ({X : 𝒰 ℓ} → Bush A B X → BT A B → Part X)
           →    {X : 𝒰 ℓ} → Bush A B X → BT A B → Part X
appBT-body _  bh (L a)      = now (headᵇ bh a)
appBT-body a▹ bh (Sp l a r) = later λ α → a▹ α (tail▹ᵇ bh a α) l >>=ᵖ λ x → a▹ α x r

appBT : Bush A B X → BT A B → Part X
appBT = fix appBT-body

-- example: evaluating a numerical expression

open import Data.Nat

data Op : 𝒰 where
  Plus Mul : Op

eval : Bush ℕ Op ℕ
eval = fix λ e▹ → consᵇ id (go e▹)
  where
  go : ▹ Bush ℕ Op ℕ → Op → ▹ Bush ℕ Op (Bush ℕ Op ℕ)
  go e▹ Plus = (λ l r → mapᵇ (λ a → mapᵇ (λ b → a + b) r) l) ⍉ e▹ ⊛ e▹
  go e▹ Mul  = (λ l r → mapᵇ (λ a → mapᵇ (λ b → a · b) r) l) ⍉ e▹ ⊛ e▹
