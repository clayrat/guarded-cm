{-# OPTIONS --guarded #-}
module Guarded.BushFix where

open import Prelude
open import Data.List

open import LaterG
open import Guarded.Partial

private variable
  ℓ : Level    -- TODO generalize levels?
  A B C : 𝒰 ℓ

-- bushes via fixpoint in the universe

BushF : ▹ (𝒰 ℓ → 𝒰 ℓ) → 𝒰 ℓ → 𝒰 ℓ
BushF B▹ A = A × ▸ (B▹ ⊛ (B▹ ⊛ next A))

Bush : 𝒰 ℓ → 𝒰 ℓ
Bush = fix BushF

opaque
  Bush-path : Bush A ＝ BushF (next Bush) A
  Bush-path {A} = happly (fix-path BushF) A

  Bush⇉ : Bush A → BushF (next Bush) A
  Bush⇉ = transport Bush-path

  ⇉Bush : BushF (next Bush) A → Bush A
  ⇉Bush = transport (Bush-path ⁻¹)

consᵇ : A → ▹ Bush (Bush A) → Bush A
consᵇ x xs▹ = ⇉Bush (x , xs▹)

unconsᵇ : Bush A → A × ▹ Bush (Bush A)
unconsᵇ = Bush⇉

headᵇ : Bush A → A
headᵇ = fst ∘ unconsᵇ

tail▹ᵇ : Bush A → ▹ Bush (Bush A)
tail▹ᵇ = snd ∘ unconsᵇ

opaque
  unfolding Bush⇉ ⇉Bush

  uncons-eq : (b : Bush A) → b ＝ consᵇ (headᵇ b) (tail▹ᵇ b)
  uncons-eq {A} s = transport⁻-transport Bush-path s ⁻¹

  head-cons : (a : A) (as▹ : ▹ Bush (Bush A)) → headᵇ (consᵇ a as▹) ＝ a
  head-cons {A} a as▹ = transport⁻-transport refl a

  tail-cons : (a : A) (as▹ : ▹ Bush (Bush A)) → tail▹ᵇ (consᵇ a as▹) ＝ as▹
  tail-cons {A} a as▹ =
    transport⁻-transport
      (λ i → ▹[ α ] (pfix BushF (~ i) α (pfix BushF (~ i) α A)))
      as▹

-- constant bush

pureᵇ-body : ▹ ({A : 𝒰 ℓ} → A → Bush A)
           →    {A : 𝒰 ℓ} → A → Bush A
pureᵇ-body p▹ a = consᵇ a λ α → p▹ α (p▹ α a)

pureᵇ : {A : 𝒰 ℓ} → A → Bush A
pureᵇ = fix pureᵇ-body

-- map

mapᵇ-body : ▹ ({A B : 𝒰 ℓ} → (A → B) → Bush A → Bush B)
          →    {A B : 𝒰 ℓ} → (A → B) → Bush A → Bush B
mapᵇ-body m▹ f b =
  consᵇ (f (headᵇ b)) λ α → m▹ α (m▹ α f) (tail▹ᵇ b α)

mapᵇ : {A B : 𝒰 ℓ} → (A → B) → Bush A → Bush B
mapᵇ {A} {B} f = fix mapᵇ-body {A} {B} f

mapᵇ-id : (A : 𝒰 ℓ)
        → (b : Bush A)
        → mapᵇ id b ＝ b
mapᵇ-id =
  fix λ ih▹ A b →
    mapᵇ id b
      =⟨ ap (λ q → q id b) (fix-path mapᵇ-body) ⟩
    mapᵇ-body (next (λ {A} {B} → mapᵇ)) id b
      =⟨⟩
    consᵇ (headᵇ b) (λ α → next mapᵇ α (next mapᵇ α id) (tail▹ᵇ b α))
      =⟨ ap (consᵇ (headᵇ b)) (▹-ext λ α →   ap (λ q → mapᵇ q (tail▹ᵇ b α)) (fun-ext (ih▹ α A))
                                           ∙ ih▹ α (Bush A) (tail▹ᵇ b α)) ⟩
    consᵇ (headᵇ b) (tail▹ᵇ b)
      =⟨ uncons-eq b ⁻¹ ⟩
    b
      ∎

mapᵇ-comp : (A B C : 𝒰 ℓ) (f : A → B) (g : B → C)
          → (b : Bush A)
          → mapᵇ g (mapᵇ f b) ＝ mapᵇ (g ∘ f) b
mapᵇ-comp {ℓ} = fix λ ih▹ A B C f g b →
      mapᵇ g (mapᵇ f b)
        =⟨ ap (λ q → mapᵇ g (q f b)) (fix-path mapᵇ-body) ⟩
      mapᵇ g (mapᵇ-body (next λ {A} {B} → mapᵇ) f b)
        =⟨ ap (λ q → q g (mapᵇ-body (next λ {A} {B} → mapᵇ) f b)) (fix-path mapᵇ-body) ⟩
      mapᵇ-body (next λ {A} {B} → mapᵇ) g (mapᵇ-body (next (λ {A} {B} → mapᵇ)) f b)
        =⟨⟩
      consᵇ (g (headᵇ (consᵇ (f (headᵇ b)) (λ α → mapᵇ (mapᵇ f) (tail▹ᵇ b α)))))
            (λ α → mapᵇ (mapᵇ g) (tail▹ᵇ (consᵇ (f (headᵇ b)) (λ α → mapᵇ (mapᵇ f) (tail▹ᵇ b α))) α))
        =⟨ ap (λ q → consᵇ (g q) (λ α → mapᵇ (mapᵇ g) (tail▹ᵇ (consᵇ (f (headᵇ b)) (λ α → mapᵇ (mapᵇ f) (tail▹ᵇ b α))) α)))
             (head-cons (f (headᵇ b)) (λ α → mapᵇ (mapᵇ f) (tail▹ᵇ b α))) ⟩
      consᵇ (g (f (headᵇ b)))
            (λ α → mapᵇ (mapᵇ g) (tail▹ᵇ (consᵇ (f (headᵇ b)) (λ α → mapᵇ (mapᵇ f) (tail▹ᵇ b α))) α))
        =⟨ ap (consᵇ (g (f (headᵇ b))))
              (▹-ext λ α → ap (mapᵇ (mapᵇ g)) (▹-ap (tail-cons (f (headᵇ b)) λ α′ → mapᵇ (mapᵇ f) (tail▹ᵇ b α′)) α)
                         ∙ ih▹ α (Bush A) (Bush B) (Bush C)
                                                  ((λ {A B : 𝒰 ℓ} → mapᵇ {ℓ} {A} {B}) f)
                                                  ((λ {A B : 𝒰 ℓ} → mapᵇ {ℓ} {A} {B}) g)
                                                  (tail▹ᵇ b α)
                         ∙ ap (λ q → mapᵇ q (tail▹ᵇ b α)) (fun-ext (ih▹ α A B C f g))) ⟩
      consᵇ (g (f (headᵇ b))) (λ α → mapᵇ (mapᵇ (g ∘ f)) (tail▹ᵇ b α))
        =⟨⟩
      mapᵇ-body (next λ {A} {B} → mapᵇ) (g ∘ f) b
        =⟨ ap (λ q → q (g ∘ f) b) (fix-path mapᵇ-body) ⟨
      mapᵇ (g ∘ f) b
        ∎

data BT : 𝒰 where
  L  : BT
  Sp : BT → BT → BT

lamBT-body : ▹ ({A : 𝒰 ℓ} → (BT → A) → Bush A)
           →    {A : 𝒰 ℓ} → (BT → A) → Bush A
lamBT-body l▹ {A} f = consᵇ (f L) λ α → l▹ α λ t → l▹ α λ u → f (Sp t u)

lamBT : (BT → A) → Bush A
lamBT = fix lamBT-body

appBT-body : ▹ ({A : 𝒰 ℓ} → Bush A → BT → Part A)
           →    {A : 𝒰 ℓ} → Bush A → BT → Part A
appBT-body _  b  L       = now (headᵇ b)
appBT-body a▹ b (Sp l r) = later λ α → a▹ α (tail▹ᵇ b α) l >>=ᵖ λ b → a▹ α b r

appBT : Bush A → BT → Part A
appBT = fix appBT-body
