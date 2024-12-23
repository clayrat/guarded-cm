{-# OPTIONS --guarded #-}
module Guarded.Partial where

open import Prelude
open import Foundations.Transport
open import Data.Bool
open import Data.Nat
open import Order.Constructions.Nat
open import Order.Constructions.Minmax
open import Data.Maybe
open import Data.Sum hiding (code-is-of-hlevel)

open import LaterG

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

-- guarded partiality monad aka Delay/Lift/Event

data Part (A : 𝒰 ℓ) : 𝒰 ℓ where
  now   : A → Part A
  later : ▹ Part A → Part A

module Part-code where
  Code-body : ▹ (Part A → Part A → 𝒰 (level-of-type A)) → Part A → Part A → 𝒰 (level-of-type A)
  Code-body C▹ (now a)    (now b)    = a ＝ b
  Code-body C▹ (now _)    (later _)  = Lift _ ⊥
  Code-body C▹ (later _)  (now _)    = Lift _ ⊥
  Code-body C▹ (later a▹) (later b▹) = ▸ (C▹ ⊛ a▹ ⊛ b▹)

  Code : Part A → Part A → 𝒰 (level-of-type A)
  Code = fix Code-body

  Code-ll-eq : {a▹ b▹ : ▹ Part A} → Code (later a▹) (later b▹) ＝ ▸ (Code ⍉ a▹ ⊛ b▹)
  Code-ll-eq {a▹} {b▹} i = ▹[ α ] (pfix Code-body i α (a▹ α) (b▹ α))

  Code-ll⇉ : {a▹ b▹ : ▹ Part A} → Code (later a▹) (later b▹) → ▸ (Code ⍉ a▹ ⊛ b▹)
  Code-ll⇉ = transport Code-ll-eq

  ⇉Code-ll : {a▹ b▹ : ▹ Part A} → ▸ (Code ⍉ a▹ ⊛ b▹) → Code (later a▹) (later b▹)
  ⇉Code-ll = transport (sym Code-ll-eq)

  ⇉Code-ll⇉ : {a▹ b▹ : ▹ Part A} {c : Code (later a▹) (later b▹)}
            → ⇉Code-ll (Code-ll⇉ c) ＝ c
  ⇉Code-ll⇉ {c} = transport⁻-transport Code-ll-eq c

  Code-refl-body : ▹ ((p : Part A) → Code p p) → (p : Part A) → Code p p
  Code-refl-body C▹ (now a)    = refl
  Code-refl-body C▹ (later p▹) = ⇉Code-ll (C▹ ⊛ p▹)

  Code-refl : (p : Part A) → Code p p
  Code-refl = fix Code-refl-body

  encode : {p q : Part A} → p ＝ q → Code p q
  encode {p} {q} e = subst (Code p) e (Code-refl p)

  decode : ∀ (p q : Part A) → Code p q → p ＝ q
  decode (now a)    (now b)    c = ap now c
  decode (later a▹) (later b▹) c = ap later (▹-ext λ α → decode (a▹ α) (b▹ α) (Code-ll⇉ c α))

  Code-refl-l-eq : {a▹ : ▹ Part A} → Code-refl (later a▹) ＝ ⇉Code-ll (Code-refl ⍉ a▹)
  Code-refl-l-eq {a▹} i = ⇉Code-ll λ α → pfix Code-refl-body i α (a▹ α)

  Code-refl-pathP : (p q : Part A) → (c : Code p q) → ＜ Code-refl p ／ (λ i → Code p (decode p q c i)) ＼ c ＞
  Code-refl-pathP = fix λ ih▹ → λ where
    (now x)    (now y)    c → λ i j → c (i ∧ j)
    (later p▹) (later q▹) c →
       let ihP : ＜ (Code-refl ⍉ p▹) ／ (λ i → ▹[ α ] Code (p▹ α) (decode (p▹ α) (q▹ α) (Code-ll⇉ c α) i)) ＼ (Code-ll⇉ c) ＞
           ihP = ▹-extP λ α → ih▹ α (p▹ α) (q▹ α) (Code-ll⇉ c α)
         in
        to-pathᴾ⁻ (Code-refl-l-eq ∙ transport-flip {A = λ i → Code-ll-eq {a▹ = p▹} (~ i)} (from-pathᴾ⁻ ihP ∙ go))
     where
     go : {p▹ q▹ : ▹ Part A} {c : Code (later p▹) (later q▹)} →
          transport (λ i → ▹[ α ] Code (p▹ α) (decode (p▹ α) (q▹ α) (Code-ll⇉ c α) (~ i))) (Code-ll⇉ c)
           ＝
          Code-ll⇉ (transport (λ i → Code (later p▹) (decode (later p▹) (later q▹) c (~ i))) c)
     go {p▹} {q▹} {c} =
         sym (transport-comp Code-ll-eq (λ i → ▹[ α ] Code (p▹ α) (decode (p▹ α) (q▹ α) (Code-ll⇉ c α) (~ i))) c)
       ∙ ap (λ q → transport q c)
            (square→commutes λ j i →
              ▹[ α ] pfix Code-body j α (p▹ α) (decode (p▹ α) (q▹ α) (Code-ll⇉ c α) (~ i)))
       ∙ transport-comp (λ i → Code (later p▹) (decode (later p▹) (later q▹) c (~ i))) Code-ll-eq c

  identity-system : is-identity-system {A = Part A} Code Code-refl
  identity-system .to-path      {a} {b} = decode a b
  identity-system .to-path-over {a} {b} = Code-refl-pathP a b

  code-is-of-hlevel : (p q : Part A) → (n : HLevel) → is-of-hlevel (2 + n) A → is-of-hlevel (1 + n) (Code p q)
  code-is-of-hlevel = fix λ ih▹ → λ where
    (now x)    (now y)    n al → path-is-of-hlevel (1 + n) al x y
    (now x)    (later q▹) n al → Lift-is-of-hlevel (suc n) (hlevel (suc n))
    (later p▹) (now y)    n al → Lift-is-of-hlevel (suc n) (hlevel (suc n))
    (later p▹) (later q▹) n al →
      ▹is-of-hlevel λ α → transport (λ i → is-of-hlevel (suc n) (pfix Code-body (~ i) α (p▹ α) (q▹ α)))
                                    (ih▹ α (p▹ α) (q▹ α) n al)

Part-is-of-hlevel : (n : HLevel)
                  → is-of-hlevel (2 + n) A
                  → is-of-hlevel (2 + n) (Part A)
Part-is-of-hlevel n A-hl _ _ =
  ≃→is-of-hlevel (1 + n)
                 (identity-system-gives-path Part-code.identity-system ⁻¹)
                 (Part-code.code-is-of-hlevel _ _ n A-hl)

now-inj : ∀ {a b : A}
        → now a ＝ now b → a ＝ b
now-inj = Part-code.encode

later-inj : ∀ {a▹ b▹ : ▹ Part A}
          → later a▹ ＝ later b▹ → a▹ ＝ b▹
later-inj {a▹} {b▹} e =
  ▹-ext λ α → Part-code.decode (a▹ α) (b▹ α) (Part-code.Code-ll⇉ (Part-code.encode e) α)

now≠later : ∀ {a : A} {p▹ : ▹ Part A}
          → now a ≠ later p▹
now≠later = lower ∘ Part-code.encode

never : Part ⊥
never = fix later

never* : Part A
never* = fix later

δᵖ : Part A → Part A
δᵖ = later ∘ next

δᵖ-inj : ∀ {a b : Part A}
       → δᵖ a ＝ δᵖ b → ▹ (a ＝ b)
δᵖ-inj = ▹-ap ∘ later-inj

spin : ℕ → Part A → Part A
spin k = iter k δᵖ

delay-by : ℕ → A → Part A
delay-by k a = spin k (now a)

_>>=ᵖ_ : Part A → (A → Part B) → Part B
now x   >>=ᵖ f = f x
later x >>=ᵖ f = later λ α → x α >>=ᵖ f

delay-by-bindᵖ : (f : A → Part B) (x : A) (n : ℕ)
               → (delay-by n x) >>=ᵖ f ＝ iter n δᵖ (f x)
delay-by-bindᵖ f x  zero   = refl
delay-by-bindᵖ f x (suc n) = ap later (▹-ext λ α → delay-by-bindᵖ f x n)

bind-δᵖ : {f : A → Part B}
        → (p : Part A)
        → p >>=ᵖ (δᵖ ∘ f) ＝ δᵖ (p >>=ᵖ f)
bind-δᵖ     (now x)    = refl
bind-δᵖ {f} (later p▹) =
  ap later (▹-ext λ α → bind-δᵖ (p▹ α) ∙ ap later (▹-ext λ α₁ → ap (_>>=ᵖ f) (tick-irr p▹ α α₁)))

mapᵖ : (A → B) → Part A → Part B
mapᵖ f (now a)   = now (f a)
mapᵖ f (later p) = later λ α → mapᵖ f (p α)

-- functor laws

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

delay-by-mapᵖ : {f : A → B}
              → (x : A) (n : ℕ)
              → mapᵖ f (delay-by n x) ＝ delay-by n (f x)
delay-by-mapᵖ x  zero   = refl
delay-by-mapᵖ x (suc n) = ap later (▹-ext λ _ → delay-by-mapᵖ x n)

apᵖ : Part (A → B) → Part A → Part B
apᵖ (now f)     (now a)     = now (f a)
apᵖ (now f)     (later pa▹) = later λ α → apᵖ (now f) (pa▹ α)
apᵖ (later pf▹) (now a)     = later λ α → apᵖ (pf▹ α) (now a)
apᵖ (later pf▹) (later pa▹) = later λ α → apᵖ (pf▹ α) (pa▹ α)
-- apᵖ pf pa = pf >>=ᵖ λ f → mapᵖ f pa

-- TODO applicative laws

-- monad laws

bind-left-id : {a : A} {f : A → Part B}
              → now a >>=ᵖ f ＝ f a
bind-left-id = refl

bind-right-id : (p : Part A)
               → p >>=ᵖ now ＝ p
bind-right-id = fix λ ih▹ → λ where
  (now x)    → refl
  (later p▹) → ap later (▹-ext (ih▹ ⊛ p▹))

bind-assoc : {f : A → Part B} {g : B → Part C}
            → (p : Part A)
            → (p >>=ᵖ f) >>=ᵖ g ＝ p >>=ᵖ λ x → f x >>=ᵖ g
bind-assoc = fix λ ih▹ → λ where
  (now x)    → refl
  (later p▹) → ap later (▹-ext (ih▹ ⊛ p▹))

bind-map : {f : A → B}
         → (p : Part A)
         → p >>=ᵖ (now ∘ f) ＝ mapᵖ f p
bind-map = fix λ ih▹ → λ where
  (now x)    → refl
  (later p▹) → ap later (▹-ext (ih▹ ⊛ p▹))

mapᵖ-bind : {f : A → B} {g : B → Part C}
          → (p : Part A)
          → mapᵖ f p >>=ᵖ g ＝ p >>=ᵖ (g ∘ f)
mapᵖ-bind {f} {g} p = ap (_>>=ᵖ g) (bind-map p) ⁻¹ ∙ bind-assoc p

apᵖ-nowf : (f : A → B) (p : Part A)
         → apᵖ (now f) p ＝ mapᵖ f p
apᵖ-nowf f (now x)    = refl
apᵖ-nowf f (later p▹) = ap later (▹-ext λ α → apᵖ-nowf f (p▹ α))

apᵖ-nowx : (f : Part (A → B)) (x : A)
         → apᵖ f (now x) ＝ mapᵖ (_$ x) f
apᵖ-nowx (now f)    x = refl
apᵖ-nowx (later f▹) x = ap later (▹-ext λ α → apᵖ-nowx (f▹ α) x)

open decminmax ℕ-dec-total
open decminmaxprops ℕ-dec-total ℕ-dec-total

delay-by-apᵖ : (f : A → B) (nf : ℕ) (x : A) (nx : ℕ)
             → apᵖ (delay-by nf f) (delay-by nx x) ＝ delay-by (max nf nx) (f x)
delay-by-apᵖ f  zero    x  zero    = refl
delay-by-apᵖ f  zero    x (suc nx) =
  ap later (▹-ext λ α → apᵖ-nowf f (delay-by nx x) ∙ delay-by-mapᵖ x nx)
delay-by-apᵖ f (suc nf) x  zero    =
  ap later (▹-ext λ α → apᵖ-nowx (delay-by nf f) x ∙ delay-by-mapᵖ f nf)
delay-by-apᵖ f (suc nf) x (suc nx) =
    ap later (▹-ext λ α → delay-by-apᵖ f nf x nx)
  ∙ ap (λ q → delay-by q (f x)) (max-ap Suc nf nx)

map²ᵖ : (A → B → C) → Part A → Part B → Part C
map²ᵖ f = apᵖ ∘ mapᵖ f

-- via fix

map′ᵖ-body : (A → B)
           → ▹ (Part A → Part B)
           →    Part A → Part B
map′ᵖ-body f m▹ (now a)   = now (f a)
map′ᵖ-body f m▹ (later p) = later (m▹ ⊛ p)

map′ᵖ : (A → B) → Part A → Part B
map′ᵖ f = fix (map′ᵖ-body f)

ap′ᵖ-body : ▹ (Part (A → B) → Part A → Part B)
          →    Part (A → B) → Part A → Part B
ap′ᵖ-body a▹ (now f)    (now x)    = now (f x)
ap′ᵖ-body a▹ (now f)    (later x▹) = later (a▹ ⊛ next (now f) ⊛ x▹)
ap′ᵖ-body a▹ (later f▹) (now x)    = later (a▹ ⊛ f▹ ⊛ next (now x))
ap′ᵖ-body a▹ (later f▹) (later x▹) = later (a▹ ⊛ f▹ ⊛ x▹)

ap′ᵖ : Part (A → B) → Part A → Part B
ap′ᵖ = fix ap′ᵖ-body

flatten′ᵖ-body : ▹ (Part (Part A) → Part A) → Part (Part A) → Part A
flatten′ᵖ-body f▹ (now p)    = p
flatten′ᵖ-body f▹ (later p▹) = later (f▹ ⊛ p▹)

flatten′ᵖ : Part (Part A) → Part A
flatten′ᵖ = fix flatten′ᵖ-body

-- unfold

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
Part▹-body f P▹ (now a)    = now ⍉ (f a)
Part▹-body f P▹ (later p▹) = later ⍉ (P▹ ⊛ p▹)

Part▹ : (A → ▹ B) → Part A → ▹ Part B
Part▹ f = fix (Part▹-body f)

-- adds an extra step
▹Part+ : ▹ Part A → Part (▹ A)
▹Part+ = later ∘ (mapᵖ next ⍉_)
