{-# OPTIONS --guarded #-}
module Clocked.Partial where

open import Prelude
open import Data.Bool
open import Data.Maybe
open import Data.Sum
open import Later
open import Clocked.Stream using (gStream ; cons ; repeatᵏ ; Stream ; mapˢ ; nthˢ)

private variable
  A B : 𝒰
  k : Cl

-- clocked partiality monad aka Lift aka Event

data gPart (k : Cl) (A : 𝒰) : 𝒰 where
  now   : A → gPart k A
  later : ▹ k (gPart k A) → gPart k A

neverᵏ : gPart k A
neverᵏ = fix later

stallᵏ : gPart k A → gPart k A
stallᵏ = later ∘ next

_>>=ᵏ_ : gPart k A → (A → gPart k B) → gPart k B
now x   >>=ᵏ f = f x
later x >>=ᵏ f = later λ α → x α >>=ᵏ f

mapᵏ : (A → B) → gPart k A → gPart k B
mapᵏ f (now a)   = now (f a)
mapᵏ f (later p) = later λ α → mapᵏ f (p α)
-- mapᵏ f p = p >>=ᵏ (now ∘ f)

apᵏ : gPart k (A → B) → gPart k A → gPart k B
apᵏ (now f)     (now a)     = now (f a)
apᵏ (now f)     (later pa▹) = later λ α → apᵏ (now f) (pa▹ α)
apᵏ (later pf▹) (now a)     = later λ α → apᵏ (pf▹ α) (now a)
apᵏ (later pf▹) (later pa▹) = later λ α → apᵏ (pf▹ α) (pa▹ α)
-- apᵏ pf pa = pf >>=ᵏ λ f → pa >>=ᵏ (now ∘ f)

Part : 𝒰 → 𝒰
Part A = ∀ k → gPart k A

neverᵖ : Part A
neverᵖ k = neverᵏ

stallᵖ : Part A → Part A
stallᵖ p k = stallᵏ (p k)

pureᵖ : A → Part A
pureᵖ a k = now a

_>>=ᵖ_ : Part A → (A → Part B) → Part B
_>>=ᵖ_ p f k = p k >>=ᵏ λ a → f a k

mapᵖ : (A → B) → Part A → Part B
mapᵖ f p k = mapᵏ f (p k)

apᵖ : Part (A → B) → Part A → Part B
apᵖ pf p k = apᵏ (pf k) (p k)

unfoldᵏ-body : (B → A ⊎ B) → ▹ k (B → gPart k A) → B → gPart k A
unfoldᵏ-body f u▹ b with (f b)
... | inl a  = now a
... | inr b′ = later (u▹ ⊛ next b′)

unfoldᵏ : (B → A ⊎ B) → B → gPart k A
unfoldᵏ f = fix (unfoldᵏ-body f)

unfoldᵖ : (B → A ⊎ B) → B → Part A
unfoldᵖ f b k = unfoldᵏ f b

to-streamᵏ-body : ▹ k (gPart k A → gStream k (Maybe A)) → gPart k A → gStream k (Maybe A)
to-streamᵏ-body ts▹ (now a)    = repeatᵏ (just a)
to-streamᵏ-body ts▹ (later p▹) = cons nothing (ts▹ ⊛ p▹)

to-streamᵏ : gPart k A → gStream k (Maybe A)
to-streamᵏ = fix to-streamᵏ-body

to-streamᵖ : Part A → Stream (Maybe A)
to-streamᵖ c k = to-streamᵏ (c k)

timeout : Part A → ℕ → Maybe A
timeout p n = nthˢ n (to-streamᵖ p)

try-moreᵏ : (ℕ → Maybe A) → gPart k A
try-moreᵏ {A} f = unfoldᵏ try 0
  where
  try : ℕ → A ⊎ ℕ
  try n with f n
  ... | just a = inl a
  ... | nothing = inr (suc n)

minimizeᵏ : (ℕ → Bool) → gPart k ℕ
minimizeᵏ test = try-moreᵏ (λ n → if test n then just n else nothing)

minimizeᵖ : (ℕ → Bool) → Part ℕ
minimizeᵖ test k = minimizeᵏ test

raceᵏ-body : ▹ k (gPart k A → gPart k A → gPart k A) → gPart k A → gPart k A → gPart k A
raceᵏ-body r▹ (now a)     _         = now a
raceᵏ-body r▹ (later _)  (now a)    = now a
raceᵏ-body r▹ (later p1) (later p2) = later (r▹ ⊛ p1 ⊛ p2)

raceᵏ : gPart k A → gPart k A → gPart k A
raceᵏ = fix raceᵏ-body

raceωᵏ-body : ▹ k (gStream k (gPart k A) → gPart k A) → gStream k (gPart k A) → gPart k A
raceωᵏ-body r▹ (cons p ps) = raceᵏ p (later (r▹ ⊛ ps))

raceωᵏ : gStream k (gPart k A) → gPart k A
raceωᵏ = fix raceωᵏ-body

bothᵏ : gPart k A → gPart k B → gPart k (A × B)
bothᵏ pa pb = apᵏ (mapᵏ (_,_) pa) pb

raceᵖ : Part A → Part A → Part A
raceᵖ p1 p2 k = raceᵏ (p1 k) (p2 k)

raceωᵖ : Stream (Part A) → Part A
raceωᵖ s k = raceωᵏ (mapˢ (λ p → p k) s k)

bothᵖ : Part A → Part B → Part (A × B)
bothᵖ pa pb k = bothᵏ (pa k) (pb k)

-- TODO needs modulus
-- collatz : ℕ → Part ⊤
-- collatz n k = ?
