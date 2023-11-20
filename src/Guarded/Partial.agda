{-# OPTIONS --guarded #-}
module Guarded.Partial where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.Sum
open import LaterG

private variable
  A B C : 𝒰

-- guarded partiality monad aka Delay/Lift/Event

data Part (A : 𝒰) : 𝒰 where
  now   : A → Part A
  later : ▹ Part A → Part A

module Part-code where
  Code-body : ▹ (Part A → Part A → 𝒰) → Part A → Part A → 𝒰
  Code-body C▹ (now a)    (now b)    = a ＝ b
  Code-body C▹ (now _)    (later _)  = ⊥
  Code-body C▹ (later _)  (now _)    = ⊥
  Code-body C▹ (later a▹) (later b▹) = ▸ (C▹ ⊛ a▹ ⊛ b▹)

  Code : Part A → Part A → 𝒰
  Code = fix Code-body

  Code-refl-body : ▹ ((p : Part A) → Code p p) → (p : Part A) → Code p p
  Code-refl-body C▹ (now a)    = refl
  Code-refl-body C▹ (later p▹) =
    λ α → transport (λ i → (sym $ pfix Code-body) i α (p▹ α) (p▹ α)) ((C▹ ⊛ p▹) α)

  Code-refl : (p : Part A) → Code p p
  Code-refl = fix Code-refl-body

  encode : ∀ {p q} → p ＝ q → Code {A} p q
  encode {p} {q} e = subst (Code p) e (Code-refl p)

  decode : ∀ p q → Code {A} p q → p ＝ q
  decode (now a)    (now b)    c = ap now c
  decode (later a▹) (later b▹) c = ap later (▹-ext λ α → decode (a▹ α) (b▹ α) (transport (λ i → (pfix Code-body) i α (a▹ α) (b▹ α)) (c α)))

  -- TODO hlevel

now-inj : ∀ {A} {a b : A}
        → now a ＝ now b → a ＝ b
now-inj = Part-code.encode

later-inj : ∀ {A} {a▹ b▹ : ▹ Part A}
          → later a▹ ＝ later b▹ → a▹ ＝ b▹
later-inj {a▹} {b▹} eq =
  ▹-ext λ α → Part-code.decode (a▹ α) (b▹ α) (transport (λ i → pfix Part-code.Code-body i α (a▹ α) (b▹ α)) (Part-code.encode eq α))

now≠later : ∀ {A} {a : A} {p▹ : ▹ Part A}
          → now a ≠ later p▹
now≠later = Part-code.encode

never : Part A
never = fix later

δᵖ : Part A → Part A
δᵖ = later ∘ next

δᵖ-inj : ∀ {A} {a b : Part A}
       → δᵖ a ＝ δᵖ b → ▹ (a ＝ b)
δᵖ-inj = ▹-ap ∘ later-inj

delay-by : ℕ → A → Part A
delay-by k a = iter k δᵖ (now a)

_>>=ᵖ_ : Part A → (A → Part B) → Part B
now x   >>=ᵖ f = f x
later x >>=ᵖ f = later λ α → x α >>=ᵖ f

mapᵖ : (A → B) → Part A → Part B
mapᵖ f (now a)   = now (f a)
mapᵖ f (later p) = later λ α → mapᵖ f (p α)
-- mapᵖ f p = p >>=ᵖ (now ∘ f)

mapᵖ-id : (p : Part A)
        → mapᵖ id p ＝ p
mapᵖ-id (now x)    = refl
mapᵖ-id (later p▹) = ap later (▹-ext λ α → mapᵖ-id (p▹ α))

mapᵖ-comp : {f : A → B} {g : B → C}
          → (p : Part A)
          → mapᵖ g (mapᵖ f p) ＝ mapᵖ (g ∘ f) p
mapᵖ-comp (now x)    = refl
mapᵖ-comp (later p▹) = ap later (▹-ext λ α → mapᵖ-comp (p▹ α))

δᵖ-mapᵖ : {f : A → B}
        → (p : Part A)
        → δᵖ (mapᵖ f p) ＝ mapᵖ f (δᵖ p)
δᵖ-mapᵖ p = refl

-- should be derivable?
mapᵖ-bind : {f : A → B} {g : B → Part C}
          → (p : Part A)
          → mapᵖ f p >>=ᵖ g ＝ p >>=ᵖ (g ∘ f)
mapᵖ-bind (now x)    = refl
mapᵖ-bind (later p▹) = ap later (▹-ext λ α → mapᵖ-bind (p▹ α))

apᵖ : Part (A → B) → Part A → Part B
apᵖ (now f)     (now a)     = now (f a)
apᵖ (now f)     (later pa▹) = later λ α → apᵖ (now f) (pa▹ α)
apᵖ (later pf▹) (now a)     = later λ α → apᵖ (pf▹ α) (now a)
apᵖ (later pf▹) (later pa▹) = later λ α → apᵖ (pf▹ α) (pa▹ α)
-- apᵖ pf pa = pf >>=ᵖ λ f → pa >>=ᵖ (now ∘ f)

map²ᵖ : (A → B → C) → Part A → Part B → Part C
map²ᵖ f = apᵖ ∘ mapᵖ f

unfoldᵖ-body : (B → A ⊎ B) → ▹ (B → Part A) → B → Part A
unfoldᵖ-body f u▹ b with (f b)
... | inl a  = now a
... | inr b′ = later (u▹ ⊛ next b′)

unfoldᵖ : (B → A ⊎ B) → B → Part A
unfoldᵖ f = fix (unfoldᵖ-body f)

-- try successive natural numbers until a `just` is obtained
try-moreᵖ : (ℕ → Maybe A) → Part A
try-moreᵖ {A} f = unfoldᵖ try 0
  where
  try : ℕ → A ⊎ ℕ
  try n with f n
  ... | just a = inl a
  ... | nothing = inr (suc n)

minimizeᵖ : (ℕ → Bool) → Part ℕ
minimizeᵖ test = try-moreᵖ λ n → if test n then just n else nothing

raceᵖ-body : ▹ (Part A → Part A → Part A) → Part A → Part A → Part A
raceᵖ-body r▹ (now a)     _         = now a
raceᵖ-body r▹ (later _)  (now a)    = now a
raceᵖ-body r▹ (later p1) (later p2) = later (r▹ ⊛ p1 ⊛ p2)

raceᵖ : Part A → Part A → Part A
raceᵖ = fix raceᵖ-body

bothᵖ : Part A → Part B → Part (A × B)
bothᵖ = map²ᵖ _,_

Part▹-body : (A → ▹ B) → ▹ (Part A  → ▹ Part B) → Part A → ▹ Part B
Part▹-body f P▹ (now a)    = ▹map now (f a)
Part▹-body f P▹ (later p▹) = ▹map later (P▹ ⊛ p▹)

Part▹ : (A → ▹ B) → Part A → ▹ Part B
Part▹ f = fix (Part▹-body f)

-- adds an extra step
▹Part+ : ▹ Part A → Part (▹ A)
▹Part+ = later ∘ ▹map (mapᵖ next)
