{-# OPTIONS --guarded #-}
module Guarded.Conat where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Structures.IdentitySystem

open import LaterG
open import Guarded.Stream

private variable
  A B C : 𝒰

-- guarded co-naturals

data ℕ∞ : 𝒰 where
  coze : ℕ∞
  cosu : ▹ ℕ∞ → ℕ∞

Code-body : ▹ (ℕ∞ → ℕ∞ → 𝒰) → ℕ∞ → ℕ∞ → 𝒰
Code-body C▹  coze     coze    = ⊤
Code-body C▹  coze    (cosu _) = ⊥
Code-body C▹ (cosu _)  coze    = ⊥
Code-body C▹ (cosu x) (cosu y) = ▸ (C▹ ⊛ x ⊛ y)

Code : ℕ∞ → ℕ∞ → 𝒰
Code = fix Code-body

Code-refl-body : ▹ ((c′ : ℕ∞) → Code c′ c′) → (c : ℕ∞) → Code c c
Code-refl-body C▹  coze    = tt
Code-refl-body C▹ (cosu c) =
  λ α → transport (λ i → (sym $ pfix Code-body) i α (c α) (c α)) ((C▹ ⊛ c) α)

Code-refl : (c : ℕ∞) → Code c c
Code-refl = fix Code-refl-body

decode : ∀ m n → Code m n → m ＝ n
decode  coze     coze    c = refl
decode (cosu x) (cosu y) c =
  ap cosu (▹-ext (λ α → decode (x α) (y α) (transport (λ i → (pfix Code-body) i α (x α) (y α)) (c α))))

Code-is-prop : ∀ m n → is-prop (Code m n)
Code-is-prop coze      coze    = hlevel!
Code-is-prop coze     (cosu _) = hlevel!
Code-is-prop (cosu _)  coze    = hlevel!
Code-is-prop (cosu x) (cosu y) =
  ▹isProp→isProp▹ (λ α → transport (λ i → is-prop ((sym $ pfix Code-body) i α (x α) (y α))) (Code-is-prop (x α) (y α)))

ℕ∞-identity-system : is-identity-system Code Code-refl
ℕ∞-identity-system = set-identity-system Code-is-prop (λ {x} {y} → decode x y)

instance
  ℕ∞-is-set : is-set ℕ∞
  ℕ∞-is-set = identity-system→is-of-hlevel 1 ℕ∞-identity-system Code-is-prop

encode : {c1 c2 : ℕ∞} → c1 ＝ c2 → Code c1 c2
encode {c1} {c2} eq = subst (Code c1) eq (Code-refl c1)

cosu≠coze : {c : ▹ ℕ∞} → cosu c ≠ coze
cosu≠coze {c} = encode

cosu-inj : {c1 c2 : ▹ ℕ∞} → cosu c1 ＝ cosu c2 → c1 ＝ c2
cosu-inj {c1} {c2} eq =
  ▹-ext (λ α → decode (c1 α) (c2 α) (transport (λ i → pfix Code-body i α (c1 α) (c2 α)) (encode eq α)))

infty : ℕ∞
infty = fix cosu

incᶜ : ℕ∞ → ℕ∞
incᶜ = cosu ∘ next

inc-inftyᶜ : incᶜ infty ＝ infty
inc-inftyᶜ = ap cosu (sym (pfix cosu))

-- doesn't seem to scale to coinductive definition
predᶜ : ℕ∞ → Maybe (▹ ℕ∞)
predᶜ  coze     = nothing
predᶜ (cosu c▹) = just c▹

is-zeroᶜ : ℕ∞ → Bool
is-zeroᶜ  coze    = true
is-zeroᶜ (cosu _) = false

pred0ᶜ : ℕ∞ → ▹ ℕ∞
pred0ᶜ  coze     = next coze
pred0ᶜ (cosu c▹) = c▹

pred-sucᶜ : {c▹ : ▹ ℕ∞} → pred0ᶜ (cosu c▹) ＝ c▹
pred-sucᶜ = refl

pred-infᶜ : pred0ᶜ infty ＝ next infty
pred-infᶜ = pfix cosu

-- unfolding

unfoldᶜ-body : (A → Maybe A) → ▹ (A → ℕ∞) → A → ℕ∞
unfoldᶜ-body f u▹ b with (f b)
... | nothing = coze
... | just a  = cosu (u▹ ⊛ next a)

unfoldᶜ : (A → Maybe A) → A → ℕ∞
unfoldᶜ f = fix (unfoldᶜ-body f)

-- ℕ interaction

fromℕᶜ : ℕ → ℕ∞
fromℕᶜ  zero   = coze
fromℕᶜ (suc n) = incᶜ (fromℕᶜ n)

is-finiteᶜ : ℕ∞ → 𝒰
is-finiteᶜ c = Σ[ n ꞉ ℕ ] (fromℕᶜ n ＝ c)

finite-size : {x : ℕ∞} → is-finiteᶜ x → ℕ
finite-size (n , _) = n

is-finite-downᶜ′ : (x▹ : ▹ ℕ∞) → is-finiteᶜ (cosu x▹) → ▸ (▹map is-finiteᶜ x▹)
is-finite-downᶜ′ x▹ (zero  , e) = λ _ → absurd (cosu≠coze (sym e))
is-finite-downᶜ′ x▹ (suc n , e) = λ α → n , ▹-ap (cosu-inj e) α

is-finite-downᶜ : (x : ℕ∞) → is-finiteᶜ (incᶜ x) → ▹ (is-finiteᶜ x)
is-finite-downᶜ x = is-finite-downᶜ′ (next x)

is-finite-upᶜ : (x : ℕ∞) → is-finiteᶜ x → is-finiteᶜ (incᶜ x)
is-finite-upᶜ x (n , e) = suc n , ap cosu (▹-ext (next e))

-- stream interaction

to-streamᶜ-body : ▹ (ℕ∞ → Stream Bool) → ℕ∞ → Stream Bool
to-streamᶜ-body ts▹  coze     = repeatˢ false
to-streamᶜ-body ts▹ (cosu n▹) = cons true (ts▹ ⊛ n▹)

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
