{-# OPTIONS --guarded #-}
module Clocked.Moore where

open import Prelude

open import Later

open import Data.List

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  D : 𝒰 ℓ‴
  k : Cl

-- Moore machine

-- A = input, B = output
data gMoore (k : Cl) (A : 𝒰 ℓ) (B : 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  Mreᵏ : B → (A → ▹ k (gMoore k A B)) → gMoore k A B

module gMoore-code where
  Code-body : ▹ k (gMoore k A B → gMoore k A B → 𝒰 (level-of-type A ⊔ level-of-type B))
            → gMoore k A B → gMoore k A B → 𝒰 (level-of-type A ⊔ level-of-type B)
  Code-body {k} C▹ (Mreᵏ bx kx) (Mreᵏ by ky) = (bx ＝ by) × (∀ a → ▸ k (C▹ ⊛ kx a ⊛ ky a))

  Code : gMoore k A B → gMoore k A B → 𝒰 (level-of-type A ⊔ level-of-type B)
  Code = fix Code-body

  Code-mm-eq : {bx by : B} {kx ky : A → ▹ k (gMoore k A B)}
             → Code (Mreᵏ bx kx) (Mreᵏ by ky) ＝ (bx ＝ by) × (∀ a → ▸ k (▹map Code (kx a) ⊛ ky a))
  Code-mm-eq {A} {k} {bx} {by} {kx} {ky} i = (bx ＝ by) × ((a : A) → ▹[ α ∶ k ] pfix Code-body i α (kx a α) (ky a α))

  Code-mm⇉ : {bx by : B} {kx ky : A → ▹ k (gMoore k A B)}
            → Code (Mreᵏ bx kx) (Mreᵏ by ky)
            → (bx ＝ by) × (∀ a → ▸ k (▹map Code (kx a) ⊛ ky a))
  Code-mm⇉ = transport Code-mm-eq

  ⇉Code-mm : {bx by : B} {kx ky : A → ▹ k (gMoore k A B)}
            → (bx ＝ by) × (∀ a → ▸ k (▹map Code (kx a) ⊛ ky a))
            → Code (Mreᵏ bx kx) (Mreᵏ by ky)
  ⇉Code-mm = transport (sym Code-mm-eq)

  Code-refl-body : ▹ k ((m : gMoore k A B) → Code m m)
                 → (m : gMoore k A B) → Code m m
  Code-refl-body C▹ (Mreᵏ b k) = ⇉Code-mm (refl , λ a → C▹ ⊛ k a)

  Code-refl : (m : gMoore k A B) → Code m m
  Code-refl = fix Code-refl-body

  encode : {p q : gMoore k A B} → p ＝ q → Code p q
  encode {p} {q} e = subst (Code p) e (Code-refl p)

  decode : ∀ (p q : gMoore k A B) → Code p q → p ＝ q
  decode (Mreᵏ bx kx) (Mreᵏ by ky) c =
    let (be , ke) = Code-mm⇉ c in
    ap² Mreᵏ be (fun-ext λ a → ▹-ext λ α → decode (kx a α) (ky a α) (ke a α))

νᵏ : gMoore k A B → B
νᵏ (Mreᵏ b _) = b

δᵏ : gMoore k A B → A → ▹ k (gMoore k A B)
δᵏ (Mreᵏ _ k) = k

Moore : 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)
Moore A B = ∀ k → gMoore k A B

Mre : B → (A → Moore A B) → Moore A B
Mre b f k = Mreᵏ b λ a → next (f a k)

ν : Moore A B → B
ν m = νᵏ (m k0)

δ : Moore A B → A → Moore A B
δ m a = force λ k → δᵏ (m k) a

Mreᵏ-inj : {bx by : B} {kx ky : A → ▹ k (gMoore k A B)}
        → Mreᵏ bx kx ＝ Mreᵏ by ky → (bx ＝ by) × (kx ＝ ky)
Mreᵏ-inj {kx} {ky} e =
  let (be , ke) = gMoore-code.Code-mm⇉ (gMoore-code.encode e) in
  be , fun-ext λ a → ▹-ext λ α → gMoore-code.decode (kx a α) (ky a α) (ke a α)

Mre-inj : {bx by : B} {kx ky : A → Moore A B}
        → Mre bx kx ＝ Mre by ky → (bx ＝ by) × (kx ＝ ky)
Mre-inj e = Mreᵏ-inj (happly e k0) .fst
          , fun-ext λ a → fun-ext (force (λ k → ▹-ap (happly (Mreᵏ-inj (happly e k) .snd) a)))

unfoldᵏ-body : (C → B × (A → C))
             → ▹ k (C → gMoore k A B)
             → C → gMoore k A B
unfoldᵏ-body f u▹ c =
  let (b , g) = f c in
    Mreᵏ b λ a → u▹ ⊛ next (g a)

unfoldᵏ : (C → B × (A → C)) → C → gMoore k A B
unfoldᵏ f = fix (unfoldᵏ-body f)

unfoldListᵏ-body : ▹ k ((List A → B) → gMoore k A B)
                 → (List A → B) → gMoore k A B
unfoldListᵏ-body u▹ f = Mreᵏ (f []) (λ a → u▹ ⊛ next (λ as → f (a ∷ as)))

unfoldListᵏ : (List A → B) → gMoore k A B
unfoldListᵏ = fix unfoldListᵏ-body

unfoldList : (List A → B) → Moore A B
unfoldList f k = unfoldListᵏ f

-- functor

mapᵏ-body : (B → C)
          → ▹ k (gMoore k A B → gMoore k A C)
          → gMoore k A B → gMoore k A C
mapᵏ-body f m▹ (Mreᵏ b tr) = Mreᵏ (f b) λ a → m▹ ⊛ tr a

mapᵏ : (B → C)
     → gMoore k A B → gMoore k A C
mapᵏ f = fix (mapᵏ-body f)

-- profunctor

dimapᵏ-body : (D → A) → (B → C)
            → ▹ k (gMoore k A B → gMoore k D C)
            → gMoore k A B → gMoore k D C
dimapᵏ-body f g d▹ (Mreᵏ b tr) = Mreᵏ (g b) λ d → d▹ ⊛ tr (f d)

dimapᵏ : (D → A) → (B → C)
       → gMoore k A B → gMoore k D C
dimapᵏ f g = fix (dimapᵏ-body f g)

-- applicative

pureᵏ-body : B → ▹ k (gMoore k A B) → gMoore k A B
pureᵏ-body b p▹ = Mreᵏ b λ _ → p▹

pureᵏ : B → gMoore k A B
pureᵏ b = fix (pureᵏ-body b)

apᵏ-body : ▹ k (gMoore k A (B → C) → gMoore k A B → gMoore k A C)
         → gMoore k A (B → C) → gMoore k A B → gMoore k A C
apᵏ-body a▹ (Mreᵏ f trf) (Mreᵏ b trb) = Mreᵏ (f b) λ a → a▹ ⊛ trf a ⊛ trb a

apᵏ : gMoore k A (B → C) → gMoore k A B → gMoore k A C
apᵏ = fix apᵏ-body

-- comonad

extractᵏ : gMoore k A B → B
extractᵏ (Mreᵏ b _) = b

duplicateᵏ-body : ▹ k (gMoore k A B -> gMoore k A (gMoore k A B))
                →  gMoore k A B -> gMoore k A (gMoore k A B)
duplicateᵏ-body d▹ m@(Mreᵏ _ tr) = Mreᵏ m λ a → d▹ ⊛ tr a

duplicateᵏ : gMoore k A B -> gMoore k A (gMoore k A B)
duplicateᵏ = fix duplicateᵏ-body

extendᵏ-body : (gMoore k A B → C)
             → ▹ k (gMoore k A B → gMoore k A C)
             → gMoore k A B → gMoore k A C
extendᵏ-body f e▹ m@(Mreᵏ b tr) = Mreᵏ (f m) λ a → e▹ ⊛ tr a

extendᵏ : (gMoore k A B → C) -> gMoore k A B -> gMoore k A C
extendᵏ f = fix (extendᵏ-body f)

-- left fold

moorel-body : (B → A → ▹ k B)
            → ▹ k (B → gMoore k A B)
            → B → gMoore k A B
moorel-body f m▹ b = Mreᵏ b λ a → m▹ ⊛ f b a

moorel : (B → A → ▹ k B) → B → gMoore k A B
moorel f = fix (moorel-body f)

-- composition (cascade product?)

catᵏ-body : ▹ k (gMoore k A B → gMoore k B C → gMoore k A C)
          → gMoore k A B → gMoore k B C → gMoore k A C
catᵏ-body m▹ (Mreᵏ b tra) (Mreᵏ c trb) = Mreᵏ c λ a → m▹ ⊛ tra a ⊛ trb b

catᵏ : gMoore k A B → gMoore k B C → gMoore k A C
catᵏ = fix catᵏ-body

-- TODO mfix ?
