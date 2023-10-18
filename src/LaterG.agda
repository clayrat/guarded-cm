{-# OPTIONS --guarded #-}
module LaterG where

open import Agda.Primitive.Cubical using ( primHComp ; primComp )
open import Prelude
open import Foundations.Cubes
open import Prim

private
  variable
    ℓ ℓ′ ℓ″ : Level
    A : 𝒰 ℓ
    B : A → 𝒰 ℓ′

infixl 4 _⊛_
infixr -2 ▹-syntax

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : 𝒰 ℓ → 𝒰 ℓ
▹_ A = (@tick α : Tick) -> A

▸_ : ▹ 𝒰 ℓ → 𝒰 ℓ
▸ A▹ = (@tick α : Tick) → A▹ α

▹-syntax : ▹ 𝒰 ℓ → 𝒰 ℓ
▹-syntax A▹ = (@tick α : Tick) → A▹ α

syntax ▹-syntax (λ α → e) = ▹[ α ] e

next : A → ▹ A
next x _ = x

▸-next : ▸ (next A) ＝ ▹ A
▸-next = refl

_⊛_ : ▹ ((a : A) → B a)
     → (a : ▹ A) → ▹[ α ] B (a α)
(f ⊛ x) α = f α (x α)

▹map : ((a : A) → B a)
     → (a : ▹ A) → ▹[ α ] B (a α)
▹map f x α = f (x α)

▹map-id : {x : ▹ A}
        → ▹map id x ＝ x
▹map-id = refl

▹map-comp : {B C : 𝒰 ℓ} {f : A → B} {g : B -> C} {x : ▹ A}
          → ▹map g (▹map f x) ＝ ▹map (g ∘ f) x
▹map-comp = refl

-- TODO simplified
▹map² : {B C : 𝒰 ℓ} → (f : A → B → C) → ▹ A → ▹ B → ▹ C
▹map² f x y α = f (x α) (y α)

▹-ext : ∀ {A : 𝒰} → {f g : ▹ A} → (▸ λ α → f α ＝ g α) → f ＝ g
▹-ext eq i α = eq α i

▹-ap : ∀ {A : 𝒰} → {f g : ▹ A} → f ＝ g → ▸ λ α → f α ＝ g α
▹-ap eq α i = eq i α

-- These will compute only on diamond ticks.
postulate
  dfix : (▹ A → A) → ▹ A
  pfix : (f : ▹ A → A) → dfix f ＝ λ _ → f (dfix f)

pfix-ext : (f : ▹ A → A) → ▸ λ α → dfix f α ＝ f (dfix f)
pfix-ext f α i = pfix f i α

fix : (▹ A → A) → A
fix f = f (dfix f)

fix-path : (f : ▹ A → A) → fix f ＝ f (next (fix f))
fix-path f i = f (pfix f i)

▹isContr→isContr▹ : {A : ▹ 𝒰 ℓ}
  → ▹[ α ] is-contr (A α)
  → is-contr (▹[ α ] (A α))
▹isContr→isContr▹ p = is-contr-η $ (λ α → is-contr-β (p α) .fst) , λ y i α → is-contr-β (p α) .snd (y α) i

▹isProp→isProp▹ : {A : ▹ 𝒰 ℓ}
  → ▹[ α ] is-prop (A α)
  → is-prop (▹[ α ] (A α))
▹isProp→isProp▹ p = is-prop-η λ x y i α → is-prop-β (p α) (x α) (y α) i

▹isSet→isSet▹ : {A : ▹ 𝒰 ℓ}
  → ▹[ α ] is-set (A α)
  → is-set (▹[ α ] (A α))
▹isSet→isSet▹ hyp = is-set-η λ x y p q i j α →
  is-set-β (hyp α) (x α) (y α) (λ j → p j α) (λ j → q j α) i j

▹isSet□→isSet□▹ : {A : ▹ 𝒰 ℓ}
  → ▹[ α ] is-set-□ (A α)
  → is-set-□ (▹[ α ] (A α))
▹isSet□→isSet□▹ hyp p q r s i j α = hyp α
  (λ i → p i α) (λ i → q i α) (λ j → r j α) (λ j → s j α) i j

▹x=▹y→▹x=y : (x y : ▹ A)
  → (x ＝ y)
    -------------------------
  → ▹[ α ] x α ＝ y α
▹x=▹y→▹x=y x y eq α i = eq i α

▹x=y→▹x=▹y : (x y : ▹ A)
  → ▹[ α ] x α ＝ y α
    -------------------------
  → x ＝ y
▹x=y→▹x=▹y x y eq i α = eq α i
