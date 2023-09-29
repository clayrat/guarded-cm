{-# OPTIONS --cubical --guarded #-}
module Clocked.Conat where

open import Prelude
open import Data.Bool
open import Data.Maybe
open import Later
open import Clocked.Stream

private variable
  A B C : 𝒰
  k : Cl

-- clocked co-naturals

data gConat (k : Cl) : 𝒰 where
  coze : gConat k
  cosu : ▹ k (gConat k) → gConat k

inftyᵏ : gConat k
inftyᵏ = fix cosu

incᵏ : gConat k → gConat k
incᵏ = cosu ∘ next

inc-inftyᵏ : incᵏ {k} inftyᵏ ＝ inftyᵏ
inc-inftyᵏ = ap cosu (sym (pfix cosu))

Conat : 𝒰
Conat = ∀ k → gConat k

zeᶜ : Conat
zeᶜ k = coze

suᶜ : Conat → Conat
suᶜ s k = incᵏ (s k)

inftyᶜ : Conat
inftyᶜ k = inftyᵏ

su-inftyᶜ : suᶜ inftyᶜ ＝ inftyᶜ
su-inftyᶜ = fun-ext (λ k → inc-inftyᵏ)

unfoldᵏ-body : (A → Maybe A) → ▹ k (A → gConat k) → A → gConat k
unfoldᵏ-body f u▹ b with (f b)
... | nothing = coze
... | just a  = cosu (u▹ ⊛ next a)

unfoldᵏ : (A → Maybe A) → A → gConat k
unfoldᵏ f = fix (unfoldᵏ-body f)

unfoldᶜ : (A → Maybe A) → A → Conat
unfoldᶜ f a k = unfoldᵏ f a

fromℕᵏ : ℕ → gConat k
fromℕᵏ  zero   = coze
fromℕᵏ (suc n) = incᵏ (fromℕᵏ n)

fromℕᶜ : ℕ → Conat
fromℕᶜ n k = fromℕᵏ n

is-finiteᵏ : gConat k → 𝒰
is-finiteᵏ c = Σ[ n ꞉ ℕ ] (fromℕᵏ n ＝ c)

is-finiteᶜ : Conat → 𝒰
is-finiteᶜ c = Σ[ n ꞉ ℕ ] (fromℕᶜ n ＝ c)

to-streamᵏ-body : ▹ k (gConat k → gStream k Bool) → gConat k → gStream k Bool
to-streamᵏ-body ts▹  coze     = repeatᵏ false
to-streamᵏ-body ts▹ (cosu n▹) = cons true (ts▹ ⊛ n▹)

to-streamᵏ : gConat k → gStream k Bool
to-streamᵏ = fix to-streamᵏ-body

to-streamᶜ : Conat → Stream Bool
to-streamᶜ c k = to-streamᵏ (c k)

_<ℕ_ : Conat → ℕ → Bool
c <ℕ n = nthˢ n (to-streamᶜ c)

-- concatenation style
addᵏ-body : gConat k → ▹ k (gConat k → gConat k) → gConat k → gConat k
addᵏ-body x ax▹  coze    = x
addᵏ-body x ax▹ (cosu y) = cosu (ax▹ ⊛ y)

addᵏ : gConat k → gConat k → gConat k
addᵏ x = fix (addᵏ-body x)

addᶜ : Conat → Conat → Conat
addᶜ x y k = addᵏ (x k) (y k)

-- interleaving style
addᵏ′-body : ▹ k (gConat k → gConat k → gConat k) → gConat k → gConat k → gConat k
addᵏ′-body a▹  coze     coze    = coze
addᵏ′-body a▹ (cosu x)  coze    = cosu x
addᵏ′-body a▹  coze    (cosu y) = cosu y
addᵏ′-body a▹ (cosu x) (cosu y) = cosu (next (cosu (a▹ ⊛ x ⊛ y)))

addᵏ′ : gConat k → gConat k → gConat k
addᵏ′ = fix addᵏ′-body

addᶜ′ : Conat → Conat → Conat
addᶜ′ x y k = addᵏ′ (x k) (y k)

-- TODO https://proofassistants.stackexchange.com/questions/1545/how-to-prove-that-addition-is-commutative-for-conatural-numbers-in-coq

predᵏ : gConat k → Maybe (▹ k (gConat k))
predᵏ  coze    = nothing
predᵏ (cosu x) = just x
