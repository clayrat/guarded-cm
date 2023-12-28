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

-- functor laws

mapᵐ-id : (m : Moore A B)
        → mapᵐ id m ＝ m
mapᵐ-id = fix λ ih▹ → λ where
  m@(Mre b tr) →
      happly (fix-path (mapᵐ-body id)) m
    ∙ ap (Mre b) (fun-ext λ a → ▹-ext (ih▹ ⊛ tr a))

mapᵐ-comp : {f : B → C} {g : C → D}
          → (m : Moore A B)
          → mapᵐ g (mapᵐ f m) ＝ mapᵐ (g ∘ f) m
mapᵐ-comp {f} {g} = fix λ ih▹ → λ where
 m@(Mre b tr) →
     ap (mapᵐ g) (happly (fix-path (mapᵐ-body f)) m)
   ∙ happly (fix-path (mapᵐ-body g)) (mapᵐ-body f (next (mapᵐ f)) m)
   ∙ ap (Mre (g (f b))) (fun-ext λ a → ▹-ext (ih▹ ⊛ tr a))
   ∙ sym (happly (fix-path (mapᵐ-body (g ∘ f))) m)


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

-- applicative laws

apᵐ-id : (m : Moore A B)
       → apᵐ (pureᵐ id) m ＝ m
apᵐ-id = fix λ ih▹ → λ where
  m@(Mre b tr) →
      ap (λ q → apᵐ q m) (fix-path (pureᵐ-body id))
    ∙ ap (λ q → q (pureᵐ-body id (next (pureᵐ id))) m) (fix-path apᵐ-body)
    ∙ ap (Mre b) (fun-ext λ a → ▹-ext (ih▹ ⊛ tr a))

apᵐ-comp : (mf : Moore A (B → C))
         → (mg : Moore A (C → D))
         → (m : Moore A B)
         → apᵐ (apᵐ (apᵐ (pureᵐ λ g → g ∘_) mg) mf) m ＝ apᵐ mg (apᵐ mf m)
apᵐ-comp = fix λ ih▹ → λ where
  mf@(Mre bf trf) mg@(Mre bg trg) m@(Mre b tr) →
     ap (λ q → apᵐ (apᵐ (apᵐ q mg) mf) m) (fix-path (pureᵐ-body (λ g → g ∘_)))
   ∙ ap (λ q → apᵐ (apᵐ (q (pureᵐ-body (λ g → g ∘_) (next (pureᵐ (λ g → g ∘_)))) mg) mf) m)
        (fix-path apᵐ-body)
   ∙ ap (λ q → apᵐ (q (apᵐ-body (next apᵐ) (pureᵐ-body (λ g → g ∘_) (next (pureᵐ (λ g → g ∘_)))) mg) mf) m)
        (fix-path apᵐ-body)
   ∙ ap (λ q → q (apᵐ-body (next apᵐ) (apᵐ-body (next apᵐ) (pureᵐ-body (λ g → g ∘_) (next (pureᵐ (λ g → g ∘_)))) mg) mf) m)
        (fix-path apᵐ-body)
   ∙ ap (Mre (bg (bf b))) (fun-ext λ a → ▹-ext (ih▹ ⊛ trf a ⊛′ trg a ⊛′ tr a))
   ∙ ap (λ q → q mg (apᵐ-body (next apᵐ) mf m)) (sym (fix-path apᵐ-body))
   ∙ ap (λ q → apᵐ mg (q mf m)) (sym (fix-path apᵐ-body))

apᵐ-homo : {f : B → C} {x : B}
         → apᵐ {A = A} (pureᵐ f) (pureᵐ x) ＝ pureᵐ (f x)
apᵐ-homo {f} {x} = fix λ ih▹ →
    ap (apᵐ (pureᵐ f)) (fix-path (pureᵐ-body x))
  ∙ ap (λ q → apᵐ q (pureᵐ-body x (next (pureᵐ x)))) (fix-path (pureᵐ-body f))
  ∙ ap (λ q → q (pureᵐ-body f (next (pureᵐ f))) (pureᵐ-body x (next (pureᵐ x)))) (fix-path apᵐ-body)
  ∙ ap (Mre (f x)) (fun-ext λ a → ▹-ext ih▹)
  ∙ sym (fix-path (pureᵐ-body (f x)))

apᵐ-inter : {x : B}
          → (mf : Moore A (B → C))
          → apᵐ mf (pureᵐ x) ＝ apᵐ (pureᵐ (_$ x)) mf
apᵐ-inter {x} = fix λ ih▹ → λ where
  mf@(Mre bf trf) →
     ap (apᵐ mf) (fix-path (pureᵐ-body x))
   ∙ ap (λ q → q mf (pureᵐ-body x (next (pureᵐ x)))) (fix-path apᵐ-body)
   ∙ ap (Mre (bf x)) (fun-ext (λ a → ▹-ext (ih▹ ⊛ trf a)))
   ∙ ap (λ q → q (pureᵐ-body (_$ x) (next (pureᵐ (_$ x)))) mf) (sym $ fix-path apᵐ-body)
   ∙ ap (λ q → apᵐ q mf) (sym $ fix-path (pureᵐ-body (_$ x)))

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
