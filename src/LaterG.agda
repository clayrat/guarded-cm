{-# OPTIONS --cubical --guarded #-}
module LaterG where

open import Agda.Primitive.Cubical using ( primHComp ; primComp )
open import Prelude
open import Foundations.Cubes
open import Prim

private
  variable
    l : Level
    A B : 𝒰 l

infixl 4 _⊛_

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : ∀ {l} → 𝒰 l → 𝒰 l
▹_ A = (@tick x : Tick) -> A

▸_ : ∀ {l} → ▹ 𝒰 l → 𝒰 l
▸ A = (@tick x : Tick) → A x

▸-eq : {A : 𝒰 l} → ▸ (λ _ → A) ＝ ▹ A
▸-eq = refl

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)

▹map : (f : A → B) → ▹ A → ▹ B
▹map f x α = f (x α)

▹-ext : ∀ {A : 𝒰} → {f g : ▹ A} → (▸ λ α → f α ＝ g α) → f ＝ g
▹-ext eq i α = eq α i

▹-ap : ∀ {A : 𝒰} → {f g : ▹ A} → f ＝ g → ▸ λ α → f α ＝ g α
▹-ap eq α i = eq i α

-- These will compute only on diamond ticks.
postulate
  dfix : ∀ {l} {A : 𝒰 l} → (▹ A → A) → ▹ A
  pfix : ∀ {l} {A : 𝒰 l} (f : ▹ A → A) → dfix f ＝ λ _ → f (dfix f)

pfix-ext : ∀ {l} {A : 𝒰 l} (f : ▹ A → A) → ▸ λ α → dfix f α ＝ f (dfix f)
pfix-ext f α i = pfix f i α

fix : ∀ {l} {A : 𝒰 l} → (▹ A → A) → A
fix f = f (dfix f)

fix-path : (f : ▹ A → A) → fix f ＝ f (next (fix f))
fix-path f i = f (pfix f i)



