{-# OPTIONS --guarded #-}
module Guarded.Moore where

open import Prelude
open import Data.List

open import LaterG

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  D : 𝒰 ℓ‴

-- Moore machine

-- A = input, B = output
data Moore (A : 𝒰 ℓ) (B : 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  Mre : B → (A → ▹ Moore A B) → Moore A B

module Moore-code where
  Code-body : ▹ (Moore A B → Moore A B → 𝒰 (level-of-type A ⊔ level-of-type B))
            → Moore A B → Moore A B → 𝒰 (level-of-type A ⊔ level-of-type B)
  Code-body C▹ (Mre bx kx) (Mre by ky) = (bx ＝ by) × (∀ a → ▸ (C▹ ⊛ kx a ⊛ ky a))

  Code : Moore A B → Moore A B → 𝒰 (level-of-type A ⊔ level-of-type B)
  Code = fix Code-body

  Code-mm-eq : {bx by : B} {kx ky : A → ▹ Moore A B}
             → Code (Mre bx kx) (Mre by ky) ＝ (bx ＝ by) × (∀ a → ▸ (▹map Code (kx a) ⊛ ky a))
  Code-mm-eq {A} {bx} {by} {kx} {ky} i = (bx ＝ by) × ((a : A) → ▹[ α ] pfix Code-body i α (kx a α) (ky a α))

  Code-mm⇉ : {bx by : B} {kx ky : A → ▹ Moore A B}
            → Code (Mre bx kx) (Mre by ky)
            → (bx ＝ by) × (∀ a → ▸ (▹map Code (kx a) ⊛ ky a))
  Code-mm⇉ = transport Code-mm-eq

  ⇉Code-mm : {bx by : B} {kx ky : A → ▹ Moore A B}
            → (bx ＝ by) × (∀ a → ▸ (▹map Code (kx a) ⊛ ky a))
            → Code (Mre bx kx) (Mre by ky)
  ⇉Code-mm = transport (sym Code-mm-eq)

  Code-refl-body : ▹ ((m : Moore A B) → Code m m)
                 → (m : Moore A B) → Code m m
  Code-refl-body C▹ (Mre b k) = ⇉Code-mm (refl , λ a → C▹ ⊛ k a)

  Code-refl : (m : Moore A B) → Code m m
  Code-refl = fix Code-refl-body

  encode : {p q : Moore A B} → p ＝ q → Code p q
  encode {p} {q} e = subst (Code p) e (Code-refl p)

  decode : ∀ (p q : Moore A B) → Code p q → p ＝ q
  decode (Mre bx kx) (Mre by ky) c =
    let (be , ke) = Code-mm⇉ c in
    ap² Mre be (fun-ext λ a → ▹-ext λ α → decode (kx a α) (ky a α) (ke a α))

Mre-inj : {bx by : B} {kx ky : A → ▹ Moore A B}
        → Mre bx kx ＝ Mre by ky → (bx ＝ by) × (kx ＝ ky)
Mre-inj {kx} {ky} e =
  let (be , ke) = Moore-code.Code-mm⇉ (Moore-code.encode e) in
  be , fun-ext λ a → ▹-ext λ α → Moore-code.decode (kx a α) (ky a α) (ke a α)

ν : Moore A B → B
ν (Mre b _) = b

δ : Moore A B → A → ▹ Moore A B
δ (Mre _ k) = k

unfoldᵐ-body : (C → B × (A → C))
             → ▹ (C → Moore A B)
             → C → Moore A B
unfoldᵐ-body f u▹ c =
  let (b , g) = f c in
    Mre b λ a → u▹ ⊛ next (g a)

unfoldᵐ : (C → B × (A → C)) → C → Moore A B
unfoldᵐ f = fix (unfoldᵐ-body f)

unfoldListᵐ : (List A → B) → Moore A B
unfoldListᵐ = unfoldᵐ (λ f → f [] , λ a as → f (a ∷ as))

-- functor

mapᵐ-body : (B → C)
          → ▹ (Moore A B → Moore A C)
          → Moore A B → Moore A C
mapᵐ-body f m▹ (Mre b tr) = Mre (f b) λ a → m▹ ⊛ tr a

mapᵐ : (B → C)
     → Moore A B → Moore A C
mapᵐ f = fix (mapᵐ-body f)

-- profunctor

dimapᵐ-body : (D → A) → (B → C)
            → ▹ (Moore A B → Moore D C)
            → Moore A B → Moore D C
dimapᵐ-body f g d▹ (Mre b tr) = Mre (g b) λ d → d▹ ⊛ tr (f d)

dimapᵐ : (D → A) → (B → C)
       → Moore A B → Moore D C
dimapᵐ f g = fix (dimapᵐ-body f g)

-- applicative

pureᵐ-body : B → ▹ Moore A B → Moore A B
pureᵐ-body b p▹ = Mre b λ _ → p▹

pureᵐ : B → Moore A B
pureᵐ b = fix (pureᵐ-body b)

apᵐ-body : ▹ (Moore A (B → C) → Moore A B → Moore A C)
         → Moore A (B → C) → Moore A B → Moore A C
apᵐ-body a▹ (Mre f trf) (Mre b trb) = Mre (f b) λ a → a▹ ⊛ trf a ⊛ trb a

apᵐ : Moore A (B → C) → Moore A B → Moore A C
apᵐ = fix apᵐ-body

-- comonad

extractᵐ : Moore A B → B
extractᵐ (Mre b _) = b

duplicateᵐ-body : ▹ (Moore A B -> Moore A (Moore A B))
                →  Moore A B -> Moore A (Moore A B)
duplicateᵐ-body d▹ m@(Mre _ tr) = Mre m λ a → d▹ ⊛ tr a

duplicateᵐ : Moore A B -> Moore A (Moore A B)
duplicateᵐ = fix duplicateᵐ-body

extendᵐ-body : (Moore A B → C)
             → ▹ (Moore A B → Moore A C)
             → Moore A B → Moore A C
extendᵐ-body f e▹ m@(Mre b tr) = Mre (f m) λ a → e▹ ⊛ tr a

extendᵐ : (Moore A B → C) -> Moore A B -> Moore A C
extendᵐ f = fix (extendᵐ-body f)

-- left fold

moorel-body : (B → A → ▹ B)
            → ▹ (B → Moore A B)
            → B → Moore A B
moorel-body f m▹ b = Mre b λ a → m▹ ⊛ f b a

moorel : (B → A → ▹ B) → B → Moore A B
moorel f = fix (moorel-body f)

-- composition (cascade product?)

catᵐ-body : ▹ (Moore A B → Moore B C → Moore A C)
          → Moore A B → Moore B C → Moore A C
catᵐ-body m▹ (Mre b tra) (Mre c trb) = Mre c λ a → m▹ ⊛ tra a ⊛ trb b

catᵐ : Moore A B → Moore B C → Moore A C
catᵐ = fix catᵐ-body

-- TODO mfix ?
