{-# OPTIONS --guarded #-}
module Guarded.PartialG where

open import Prelude
open import Data.Bool
open import Data.Maybe
open import Data.Sum
open import LaterG

private variable
  A B C : 𝒰

-- guarded partiality monad aka Lift aka Event

data Part (A : 𝒰) : 𝒰 where
  now   : A → Part A
  later : ▹ (Part A) → Part A

never : Part A
never = fix later

stall : Part A → Part A
stall = later ∘ next

_>>=ᵖ_ : Part A → (A → Part B) → Part B
now x   >>=ᵖ f = f x
later x >>=ᵖ f = later λ α → x α >>=ᵖ f

mapᵖ : (A → B) → Part A → Part B
mapᵖ f (now a)   = now (f a)
mapᵖ f (later p) = later (λ α → mapᵖ f (p α))
-- mapᵖ f p = p >>=ᵖ (now ∘ f)

apᵖ : Part (A → B) → Part A → Part B
apᵖ (now f)    (now a)    = now (f a)
apᵖ (now f)    (later pa) = later (λ α → apᵖ (now f) (pa α))
apᵖ (later pf) (now a)    = later (λ α → apᵖ (pf α) (now a))
apᵖ (later pf) (later pa) = later (λ α → later (λ α₁ → apᵖ (pf α) (pa α₁)))
-- apᵖ pf pa = pf >>=ᵖ λ f → pa >>=ᵖ (now ∘ f)

map²ᵖ : (A → B → C) → Part A → Part B → Part C
map²ᵖ f = apᵖ ∘ mapᵖ f

unfoldᵖ-body : (B → A ⊎ B) → ▹ (B → Part A) → B → Part A
unfoldᵖ-body f u▹ b with (f b)
... | inl a  = now a
... | inr b′ = later (u▹ ⊛ next b′)

unfoldᵖ : (B → A ⊎ B) → B → Part A
unfoldᵖ f = fix (unfoldᵖ-body f)

try-moreᵖ : (ℕ → Maybe A) → Part A
try-moreᵖ {A} f = unfoldᵖ try 0
  where
  try : ℕ → A ⊎ ℕ
  try n with f n
  ... | just a = inl a
  ... | nothing = inr (suc n)

minimizeᵖ : (ℕ → Bool) → Part ℕ
minimizeᵖ test = try-moreᵖ (λ n → if test n then just n else nothing)

raceᵖ-body : ▹ (Part A → Part A → Part A) → Part A → Part A → Part A
raceᵖ-body r▹ (now a)     _         = now a
raceᵖ-body r▹ (later _)  (now a)    = now a
raceᵖ-body r▹ (later p1) (later p2) = later (r▹ ⊛ p1 ⊛ p2)

raceᵖ : Part A → Part A → Part A
raceᵖ = fix raceᵖ-body

bothᵖ : Part A → Part B → Part (A × B)
bothᵖ pa pb = apᵖ (mapᵖ (_,_) pa) pb

Part▹-body : (A → ▹ B) → ▹ (Part A  → ▹ (Part B)) → Part A → ▹ (Part B)
Part▹-body f P▹ (now a)    = ▹map now (f a)
Part▹-body f P▹ (later p▹) = ▹map later (P▹ ⊛ p▹)

Part▹ : (A → ▹ B) → Part A → ▹ (Part B)
Part▹ f = fix (Part▹-body f)

-- adds an extra step
▹Part : ▹ (Part A) → Part (▹ A)
▹Part x = later (▹map (mapᵖ next) x)
