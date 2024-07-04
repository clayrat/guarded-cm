{-# OPTIONS --guarded #-}
module Clocked.Conat where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Maybe
open import Data.Nat

open import Later

private variable
  A B C : 𝒰
  k : Cl

-- clocked co-naturals

data ℕ∞ᵏ (k : Cl) : 𝒰 where
  coze : ℕ∞ᵏ k
  cosu : ▹ k (ℕ∞ᵏ k) → ℕ∞ᵏ k

Code-body : ▹ k (ℕ∞ᵏ k → ℕ∞ᵏ k → 𝒰) → ℕ∞ᵏ k → ℕ∞ᵏ k → 𝒰
Code-body     C▹  coze     coze    = ⊤
Code-body     C▹  coze    (cosu _) = ⊥
Code-body     C▹ (cosu _)  coze    = ⊥
Code-body {k} C▹ (cosu x) (cosu y) = ▸ k (C▹ ⊛ x ⊛ y)

Code : ℕ∞ᵏ k → ℕ∞ᵏ k → 𝒰
Code = fix Code-body

Code-refl-body : ▹ k ((c′ : ℕ∞ᵏ k) → Code c′ c′) → (c : ℕ∞ᵏ k) → Code c c
Code-refl-body C▹  coze    = tt
Code-refl-body C▹ (cosu c) =
  λ α → transport (λ i → (sym $ pfix Code-body) i α (c α) (c α)) ((C▹ ⊛ c) α)

Code-refl : (c : ℕ∞ᵏ k) → Code c c
Code-refl = fix Code-refl-body

decode : ∀ m n → Code {k} m n → m ＝ n
decode  coze     coze    c = refl
decode (cosu x) (cosu y) c =
  ap cosu (▹-ext λ α → decode (x α) (y α) (transport (λ i → (pfix Code-body) i α (x α) (y α)) (c α)))

Code-is-prop : ∀ m n → is-prop (Code {k} m n)
Code-is-prop coze      coze    = hlevel!
Code-is-prop coze     (cosu _) = hlevel!
Code-is-prop (cosu _)  coze    = hlevel!
Code-is-prop (cosu x) (cosu y) =
  ▹is-prop λ α → transport (λ i → is-prop ((sym $ pfix Code-body) i α (x α) (y α))) (Code-is-prop (x α) (y α))

ℕ∞ᵏ-identity-system : is-identity-system (Code {k}) Code-refl
ℕ∞ᵏ-identity-system = set-identity-system Code-is-prop (λ {x} {y} → decode x y)

ℕ∞ᵏ-is-set : is-set (ℕ∞ᵏ k)
ℕ∞ᵏ-is-set = identity-system→is-of-hlevel 1 ℕ∞ᵏ-identity-system Code-is-prop

encode : {c1 c2 : ℕ∞ᵏ k} → c1 ＝ c2 → Code c1 c2
encode {c1} {c2} e = subst (Code c1) e (Code-refl c1)

cosu≠coze : {c : ▹ k (ℕ∞ᵏ k)} → cosu c ≠ coze
cosu≠coze {c} = encode

cosu-inj : {c1 c2 : ▹ k (ℕ∞ᵏ k)} → cosu c1 ＝ cosu c2 → c1 ＝ c2
cosu-inj {c1} {c2} e =
  ▹-ext λ α → decode (c1 α) (c2 α) (transport (λ i → pfix Code-body i α (c1 α) (c2 α)) (encode e α))

inftyᵏ : ℕ∞ᵏ k
inftyᵏ = fix cosu

incᵏ : ℕ∞ᵏ k → ℕ∞ᵏ k
incᵏ = cosu ∘ next

inc-inftyᵏ : incᵏ {k} inftyᵏ ＝ inftyᵏ
inc-inftyᵏ = ap cosu (sym (pfix cosu))

-- doesn't seem to scale to coinductive definition
predᵏ : ℕ∞ᵏ k → Maybe (▹ k (ℕ∞ᵏ k))
predᵏ  coze     = nothing
predᵏ (cosu c▹) = just c▹

is-zeroᵏ : ℕ∞ᵏ k → Bool
is-zeroᵏ  coze    = true
is-zeroᵏ (cosu _) = false

pred0ᵏ : ℕ∞ᵏ k → ▹ k (ℕ∞ᵏ k)
pred0ᵏ  coze     = next coze
pred0ᵏ (cosu c▹) = c▹

pred-sucᵏ : {c▹ : ▹ k (ℕ∞ᵏ k)} → pred0ᵏ {k} (cosu c▹) ＝ c▹
pred-sucᵏ = refl

pred-infᵏ : pred0ᵏ {k} inftyᵏ ＝ next inftyᵏ
pred-infᵏ = pfix cosu

-- coinductive co-naturals

ℕ∞ : 𝒰
ℕ∞ = ∀ k → ℕ∞ᵏ k

zeᶜ : ℕ∞
zeᶜ k = coze

suᶜ : ℕ∞ → ℕ∞
suᶜ s k = incᵏ (s k)

ℕ∞-is-set : is-set ℕ∞
ℕ∞-is-set = Π-is-of-hlevel 2 λ k → ℕ∞ᵏ-is-set

inftyᶜ : ℕ∞
inftyᶜ k = inftyᵏ

su-inftyᶜ : suᶜ inftyᶜ ＝ inftyᶜ
su-inftyᶜ = fun-ext (λ k → inc-inftyᵏ)

is-zeroᶜ : ℕ∞ → Bool
is-zeroᶜ c = is-zeroᵏ (c k0)

pred0ᶜ : ℕ∞ → ℕ∞
pred0ᶜ c = force λ k → pred0ᵏ (c k)

pred-zero : pred0ᶜ zeᶜ ＝ zeᶜ
pred-zero = fun-ext (delay-force (λ _ → coze))

pred-suc : {c : ℕ∞} → pred0ᶜ (suᶜ c) ＝ c
pred-suc {c} = fun-ext (delay-force c)

suᶜ≠zeᶜ : {c : ℕ∞} → suᶜ c ≠ zeᶜ
suᶜ≠zeᶜ e = cosu≠coze (happly e k0)

inftyᶜ≠zeᶜ : inftyᶜ ≠ zeᶜ
inftyᶜ≠zeᶜ e = cosu≠coze (happly e k0)

suᶜ-inj : (c1 c2 : ℕ∞) → suᶜ c1 ＝ suᶜ c2 → c1 ＝ c2
suᶜ-inj c1 c2 e = sym (pred-suc {c = c1}) ∙ ap pred0ᶜ e ∙ pred-suc {c = c2}

pred-inf : pred0ᶜ inftyᶜ ＝ inftyᶜ
pred-inf = fun-ext λ k →
  pred0ᶜ inftyᶜ k
    ~⟨⟩
  force (λ k′ → pred0ᵏ inftyᵏ) k
    ~⟨ ap (λ q → force q k) (fun-ext (λ k′ → pred-infᵏ)) ⟩
  force (λ k′ → next inftyᵏ) k
    ~⟨⟩
  force (λ k′ α → inftyᵏ) k
    ~⟨ delay-force (λ k′ → inftyᵏ) k ⟩
  inftyᶜ k
    ∎

-- unfolding

unfoldᵏ-body : (A → Maybe A) → ▹ k (A → ℕ∞ᵏ k) → A → ℕ∞ᵏ k
unfoldᵏ-body f u▹ b with (f b)
... | nothing = coze
... | just a  = cosu (u▹ ⊛ next a)

unfoldᵏ : (A → Maybe A) → A → ℕ∞ᵏ k
unfoldᵏ f = fix (unfoldᵏ-body f)

unfoldᶜ : (A → Maybe A) → A → ℕ∞
unfoldᶜ f a k = unfoldᵏ f a

-- ℕ interaction

fromℕᵏ : ℕ → ℕ∞ᵏ k
fromℕᵏ  zero   = coze
fromℕᵏ (suc n) = incᵏ (fromℕᵏ n)

fromℕᶜ : ℕ → ℕ∞
fromℕᶜ n k = fromℕᵏ n

is-finiteᵏ : ℕ∞ᵏ k → 𝒰
is-finiteᵏ c = Σ[ n ꞉ ℕ ] (fromℕᵏ n ＝ c)

finite-sizeᵏ : {x : ℕ∞ᵏ k} → is-finiteᵏ x → ℕ
finite-sizeᵏ (n , _) = n

is-finite-downᵏ′ : (x▹ : ▹ k (ℕ∞ᵏ k)) → is-finiteᵏ (cosu x▹) → ▸ k (is-finiteᵏ ⍉ x▹)
is-finite-downᵏ′ x▹ (zero  , e) = λ _ → absurd (cosu≠coze (sym e))
is-finite-downᵏ′ x▹ (suc n , e) = λ α → n , ▹-ap (cosu-inj e) α

is-finite-downᵏ : (x : ℕ∞ᵏ k) → is-finiteᵏ (incᵏ x) → ▹ k (is-finiteᵏ x)
is-finite-downᵏ x = is-finite-downᵏ′ (next x)

is-finite-upᵏ : (x : ℕ∞ᵏ k) → is-finiteᵏ x → is-finiteᵏ (incᵏ x)
is-finite-upᵏ x (n , e) = suc n , ap cosu (▹-ext (next e))

infty-not-finite′ : (n : ℕ) → inftyᶜ ≠ fromℕᶜ n
infty-not-finite′  zero   e = cosu≠coze $ happly e k0
infty-not-finite′ (suc n) e = infty-not-finite′ n (suᶜ-inj inftyᶜ (fromℕᶜ n) (su-inftyᶜ ∙ e))

is-finiteᶜ : ℕ∞ → 𝒰
is-finiteᶜ c = Σ[ n ꞉ ℕ ] (fromℕᶜ n ＝ c)

finite-sizeᶜ : {x : ℕ∞} → is-finiteᶜ x → ℕ
finite-sizeᶜ (n , _) = n

infty-not-finite : ¬ is-finiteᶜ inftyᶜ
infty-not-finite (n , e) = infty-not-finite′ n (sym e)
