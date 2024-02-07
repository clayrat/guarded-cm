{-# OPTIONS --guarded #-}
module Clocked.Partial where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Maybe
open import Data.Sum
open import Data.Nat
open import Later

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  k : Cl

-- clocked partiality monad aka Lift aka Event

data gPart (k : Cl) (A : 𝒰 ℓ) : 𝒰 ℓ where
  now   : A → gPart k A
  later : ▹ k (gPart k A) → gPart k A

module gPart-code where
  Code-body : ▹ k (gPart k A → gPart k A → 𝒰 (level-of-type A))
            → gPart k A → gPart k A → 𝒰 (level-of-type A)
  Code-body     C▹ (now a)    (now b)    = a ＝ b
  Code-body     C▹ (now _)    (later _)  = Lift _ ⊥
  Code-body     C▹ (later _)  (now _)    = Lift _ ⊥
  Code-body {k} C▹ (later a▹) (later b▹) = ▸ k (C▹ ⊛ a▹ ⊛ b▹)

  Code : gPart k A → gPart k A → 𝒰 (level-of-type A)
  Code = fix Code-body

  Code-ll-eq : {a▹ b▹ : ▹ k (gPart k A)} → Code (later a▹) (later b▹) ＝ ▸ k (Code ⍉ a▹ ⊛ b▹)
  Code-ll-eq {k} {a▹} {b▹} i = ▹[ α ∶ k ] (pfix Code-body i α (a▹ α) (b▹ α))

  Code-ll⇉ : {a▹ b▹ : ▹ k (gPart k A)} → Code (later a▹) (later b▹) → ▸ k (Code ⍉ a▹ ⊛ b▹)
  Code-ll⇉ = transport Code-ll-eq

  ⇉Code-ll : {a▹ b▹ : ▹ k (gPart k A)} → ▸ k (Code ⍉ a▹ ⊛ b▹) → Code (later a▹) (later b▹)
  ⇉Code-ll = transport (sym Code-ll-eq)

  ⇉Code-ll⇉ : {a▹ b▹ : ▹ k (gPart k A)} {c : Code (later a▹) (later b▹)}
            → ⇉Code-ll (Code-ll⇉ c) ＝ c
  ⇉Code-ll⇉ {c} = transport⁻-transport Code-ll-eq c

  Code-refl-body : ▹ k ((p : gPart k A) → Code p p) → (p : gPart k A) → Code p p
  Code-refl-body C▹ (now a)    = refl
  Code-refl-body C▹ (later p▹) = ⇉Code-ll (C▹ ⊛ p▹)

  Code-refl : (p : gPart k A) → Code p p
  Code-refl = fix Code-refl-body

  encode : {p q : gPart k A} → p ＝ q → Code p q
  encode {p} {q} e = subst (Code p) e (Code-refl p)

  decode : ∀ (p q : gPart k A) → Code p q → p ＝ q
  decode (now a)    (now b)    c = ap now c
  decode (later a▹) (later b▹) c = ap later (▹-ext λ α → decode (a▹ α) (b▹ α) (Code-ll⇉ c α))

now-inj : ∀ {a b : A}
        → now {k = k} a ＝ now b → a ＝ b
now-inj = gPart-code.encode

later-inj : ∀ {a▹ b▹ : ▹ k (gPart k A)}
          → later a▹ ＝ later b▹ → a▹ ＝ b▹
later-inj {a▹} {b▹} e =
  ▹-ext λ α → gPart-code.decode (a▹ α) (b▹ α) (gPart-code.Code-ll⇉ (gPart-code.encode e) α)

now≠later : ∀ {a : A} {p▹ : ▹ k (gPart k A)}
          → now a ≠ later p▹
now≠later = lower ∘ gPart-code.encode

neverᵏ : gPart k A
neverᵏ = fix later

δᵏ : gPart k A → gPart k A
δᵏ = later ∘ next

spinᵏ : ℕ → gPart k A → gPart k A
spinᵏ k = iter k δᵏ

delay-byᵏ : ℕ → A → gPart k A
delay-byᵏ k a = spinᵏ k (now a)

_>>=ᵏ_ : gPart k A → (A → gPart k B) → gPart k B
now x   >>=ᵏ f = f x
later x >>=ᵏ f = later λ α → x α >>=ᵏ f

-- sugar
_=<<ᵏ_ : (A → gPart k B) → gPart k A → gPart k B
f =<<ᵏ p = p >>=ᵏ f

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

mapᵏ-id : (p : gPart k A)
        → mapᵏ id p ＝ p
mapᵏ-id (now a)   = refl
mapᵏ-id (later p) = ap later (▹-ext λ α → mapᵏ-id (p α))

delay-by-mapᵏ : {f : A → B}
              → (x : A) (n : ℕ)
              → mapᵏ {k = k} f (delay-byᵏ n x) ＝ delay-byᵏ n (f x)
delay-by-mapᵏ x  zero   = refl
delay-by-mapᵏ x (suc n) = ap later (▹-ext λ _ → delay-by-mapᵏ x n)

apᵏ-nowf : (f : A → B) (p : gPart k A)
         → apᵏ (now f) p ＝ mapᵏ f p
apᵏ-nowf f (now x)    = refl
apᵏ-nowf f (later p▹) = ap later (▹-ext λ α → apᵏ-nowf f (p▹ α))

apᵏ-nowx : (f : gPart k (A → B)) (x : A)
         → apᵏ f (now x) ＝ mapᵏ (_$ x) f
apᵏ-nowx (now f)    x = refl
apᵏ-nowx (later f▹) x = ap later (▹-ext λ α → apᵏ-nowx (f▹ α) x)

delay-by-apᵏ : (f : A → B) (nf : ℕ) (x : A) (nx : ℕ)
             → apᵏ {k = k} (delay-byᵏ nf f) (delay-byᵏ nx x) ＝ delay-byᵏ (max nf nx) (f x)
delay-by-apᵏ f  zero    x  zero    = refl
delay-by-apᵏ f  zero    x (suc nx) = ap later (▹-ext λ α → apᵏ-nowf f (delay-byᵏ nx x) ∙ delay-by-mapᵏ x nx)
delay-by-apᵏ f (suc nf) x  zero    = ap later (▹-ext λ α → apᵏ-nowx (delay-byᵏ nf f) x ∙ delay-by-mapᵏ f nf)
delay-by-apᵏ f (suc nf) x (suc nx) = ap later (▹-ext λ α → delay-by-apᵏ f nf x nx)

delay-by-bindᵏ : (f : A → gPart k B) (x : A) (n : ℕ)
               → (delay-byᵏ n x) >>=ᵏ f ＝ spinᵏ n (f x)
delay-by-bindᵏ f x  zero   = refl
delay-by-bindᵏ f x (suc n) = ap δᵏ (delay-by-bindᵏ f x n)

Part : 𝒰 ℓ → 𝒰 ℓ
Part A = ∀ k → gPart k A

pureᵖ : A → Part A
pureᵖ a k = now a

neverᵖ : Part A
neverᵖ k = neverᵏ

δᵖ : Part A → Part A
δᵖ p k = δᵏ (p k)

spin : ℕ → Part A → Part A
spin n p k = spinᵏ n (p k)

delay-by : ℕ → A → Part A
delay-by n a k = delay-byᵏ n a

_>>=ᵖ_ : Part A → (A → Part B) → Part B
_>>=ᵖ_ p f k = p k >>=ᵏ λ a → f a k

_=<<ᵖ_ : Part A → (A → Part B) → Part B
_=<<ᵖ_ p f k = (λ a → f a k) =<<ᵏ p k

mapᵖ : (A → B) → Part A → Part B
mapᵖ f p k = mapᵏ f (p k)

apᵖ : Part (A → B) → Part A → Part B
apᵖ pf p k = apᵏ (pf k) (p k)

delay-by-mapᵖ : {f : A → B}
              → (x : A) (n : ℕ)
              → mapᵖ f (delay-by n x) ＝ delay-by n (f x)
delay-by-mapᵖ x n = fun-ext λ k → delay-by-mapᵏ x n

delay-by-apᵖ : (f : A → B) (nf : ℕ) (x : A) (nx : ℕ)
             → apᵖ (delay-by nf f) (delay-by nx x) ＝ delay-by (max nf nx) (f x)
delay-by-apᵖ f nf x nx = fun-ext λ k → delay-by-apᵏ f nf x nx

delay-by-bindᵖ : (f : A → Part B) (x : A) (n : ℕ)
               → (delay-by n x) >>=ᵖ f ＝ spin n (f x)
delay-by-bindᵖ f x n = fun-ext λ k → delay-by-bindᵏ (λ a → f a k) x n

unfoldᵏ-body : (B → A ⊎ B) → ▹ k (B → gPart k A) → B → gPart k A
unfoldᵏ-body f u▹ b with (f b)
... | inl a  = now a
... | inr b′ = later (u▹ ⊛ next b′)

unfoldᵏ : (B → A ⊎ B) → B → gPart k A
unfoldᵏ f = fix (unfoldᵏ-body f)

unfoldᵖ : (B → A ⊎ B) → B → Part A
unfoldᵖ f b k = unfoldᵏ f b

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

map²ᵏ : (A → B → C) → gPart k A → gPart k B → gPart k C
map²ᵏ f = apᵏ ∘ mapᵏ f

bothᵏ : gPart k A → gPart k B → gPart k (A × B)
bothᵏ = map²ᵏ (_,_)

raceᵖ : Part A → Part A → Part A
raceᵖ p1 p2 k = raceᵏ (p1 k) (p2 k)

map²ᵖ : (A → B → C) → Part A → Part B → Part C
map²ᵖ f pa pb k = map²ᵏ f (pa k) (pb k)

bothᵖ : Part A → Part B → Part (A × B)
bothᵖ pa pb k = bothᵏ (pa k) (pb k)

gPart▹-body : (A → ▹ k B) → ▹ k (gPart k A → ▹ k (gPart k B)) → gPart k A → ▹ k (gPart k B)
gPart▹-body f P▹ (now a)    = now ⍉ (f a)
gPart▹-body f P▹ (later p▹) = later ⍉ (P▹ ⊛ p▹)

gPart▹ : (A → ▹ k B) → gPart k A → ▹ k (gPart k B)
gPart▹ f = fix (gPart▹-body f)

