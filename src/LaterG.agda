{-# OPTIONS --cubical --guarded #-}
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



