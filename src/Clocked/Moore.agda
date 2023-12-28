{-# OPTIONS --guarded #-}
module Clocked.Moore where

open import Prelude
open import Data.List

open import Later

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

νᵐ : Moore A B → B
νᵐ m = νᵏ (m k0)

δᵐ : Moore A B → A → Moore A B
δᵐ m a = force λ k → δᵏ (m k) a

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

-- coiteration

unfoldᵏ : (C → B × (A → C)) → C → gMoore k A B
unfoldᵏ f = fix (unfoldᵏ-body f)

unfoldᵐ : (C → B × (A → C)) → C → Moore A B
unfoldᵐ f c k = unfoldᵏ f c

unfoldListᵏ : (List A → B) → gMoore k A B
unfoldListᵏ = unfoldᵏ (λ f → f [] , λ a as → f (a ∷ as))

unfoldListᵐ : (List A → B) → Moore A B
unfoldListᵐ f k = unfoldListᵏ f

-- functor

mapᵏ-body : (B → C)
          → ▹ k (gMoore k A B → gMoore k A C)
          → gMoore k A B → gMoore k A C
mapᵏ-body f m▹ (Mreᵏ b tr) = Mreᵏ (f b) λ a → m▹ ⊛ tr a

mapᵏ : (B → C)
     → gMoore k A B → gMoore k A C
mapᵏ f = fix (mapᵏ-body f)

mapᵐ : (B → C)
     → Moore A B → Moore A C
mapᵐ f m k = mapᵏ f (m k)

-- functor laws

mapᵏ-id : (m : gMoore k A B)
        → mapᵏ id m ＝ m
mapᵏ-id {k} = fix {k} λ ih▹ → λ where
  m@(Mreᵏ b tr) →
      happly (fix-path (mapᵏ-body id)) m
    ∙ ap (Mreᵏ b) (fun-ext λ a → ▹-ext (ih▹ ⊛ tr a))

mapᵐ-id : (m : Moore A B)
        → mapᵐ id m ＝ m
mapᵐ-id m = fun-ext (mapᵏ-id ∘ m)

mapᵏ-comp : {f : B → C} {g : C → D}
          → (m : gMoore k A B)
          → mapᵏ g (mapᵏ f m) ＝ mapᵏ (g ∘ f) m
mapᵏ-comp {k} {f} {g} = fix {k} λ ih▹ → λ where
 m@(Mreᵏ b tr) →
     ap (mapᵏ g) (happly (fix-path (mapᵏ-body f)) m)
   ∙ happly (fix-path (mapᵏ-body g)) (mapᵏ-body f (next (mapᵏ f)) m)
   ∙ ap (Mreᵏ (g (f b))) (fun-ext λ a → ▹-ext (ih▹ ⊛ tr a))
   ∙ sym (happly (fix-path (mapᵏ-body (g ∘ f))) m)

mapᵐ-comp : {f : B → C} {g : C → D}
          → (m : Moore A B)
          → mapᵐ g (mapᵐ f m) ＝ mapᵐ (g ∘ f) m
mapᵐ-comp m = fun-ext (mapᵏ-comp ∘ m)

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

pureᵐ : B → Moore A B
pureᵐ b k = pureᵏ b

apᵏ-body : ▹ k (gMoore k A (B → C) → gMoore k A B → gMoore k A C)
         → gMoore k A (B → C) → gMoore k A B → gMoore k A C
apᵏ-body a▹ (Mreᵏ f trf) (Mreᵏ b trb) = Mreᵏ (f b) λ a → a▹ ⊛ trf a ⊛ trb a

apᵏ : gMoore k A (B → C) → gMoore k A B → gMoore k A C
apᵏ = fix apᵏ-body

apᵐ : Moore A (B → C) → Moore A B → Moore A C
apᵐ mf ma k = apᵏ (mf k) (ma k)

-- applicative laws

apᵏ-id : (m : gMoore k A B)
       → apᵏ (pureᵏ id) m ＝ m
apᵏ-id {k} = fix {k} λ ih▹ → λ where
  m@(Mreᵏ b tr) →
      ap (λ q → apᵏ q m) (fix-path (pureᵏ-body id))
    ∙ ap (λ q → q (pureᵏ-body id (next (pureᵏ id))) m) (fix-path apᵏ-body)
    ∙ ap (Mreᵏ b) (fun-ext λ a → ▹-ext (ih▹ ⊛ tr a))

apᵐ-id : (m : Moore A B)
       → apᵐ (pureᵐ id) m ＝ m
apᵐ-id m = fun-ext (apᵏ-id ∘ m)

apᵏ-comp : (mf : gMoore k A (B → C))
         → (mg : gMoore k A (C → D))
         → (m : gMoore k A B)
         → apᵏ (apᵏ (apᵏ (pureᵏ λ g → g ∘_) mg) mf) m ＝ apᵏ mg (apᵏ mf m)
apᵏ-comp {k} = fix {k} λ ih▹ → λ where
  mf@(Mreᵏ bf trf) mg@(Mreᵏ bg trg) m@(Mreᵏ b tr) →
     ap (λ q → apᵏ (apᵏ (apᵏ q mg) mf) m) (fix-path (pureᵏ-body (λ g → g ∘_)))
   ∙ ap (λ q → apᵏ (apᵏ (q (pureᵏ-body (λ g → g ∘_) (next (pureᵏ (λ g → g ∘_)))) mg) mf) m)
        (fix-path apᵏ-body)
   ∙ ap (λ q → apᵏ (q (apᵏ-body (next apᵏ) (pureᵏ-body (λ g → g ∘_) (next (pureᵏ (λ g → g ∘_)))) mg) mf) m)
        (fix-path apᵏ-body)
   ∙ ap (λ q → q (apᵏ-body (next apᵏ) (apᵏ-body (next apᵏ) (pureᵏ-body (λ g → g ∘_) (next (pureᵏ (λ g → g ∘_)))) mg) mf) m)
        (fix-path apᵏ-body)
   ∙ ap (Mreᵏ (bg (bf b))) (fun-ext λ a → ▹-ext (ih▹ ⊛ trf a ⊛′ trg a ⊛′ tr a))
   ∙ ap (λ q → q mg (apᵏ-body (next apᵏ) mf m)) (sym (fix-path apᵏ-body))
   ∙ ap (λ q → apᵏ mg (q mf m)) (sym (fix-path apᵏ-body))

apᵐ-comp : (mf : Moore A (B → C))
         → (mg : Moore A (C → D))
         → (m : Moore A B)
         → apᵐ (apᵐ (apᵐ (pureᵐ λ g → g ∘_) mg) mf) m ＝ apᵐ mg (apᵐ mf m)
apᵐ-comp mf mg m = fun-ext (λ k → apᵏ-comp (mf k) (mg k) (m k))

apᵏ-homo : {f : B → C} {x : B}
         → apᵏ {k} {A = A} (pureᵏ f) (pureᵏ x) ＝ pureᵏ (f x)
apᵏ-homo {k} {f} {x} = fix {k} λ ih▹ →
    ap (apᵏ (pureᵏ f)) (fix-path (pureᵏ-body x))
  ∙ ap (λ q → apᵏ q (pureᵏ-body x (next (pureᵏ x)))) (fix-path (pureᵏ-body f))
  ∙ ap (λ q → q (pureᵏ-body f (next (pureᵏ f))) (pureᵏ-body x (next (pureᵏ x)))) (fix-path apᵏ-body)
  ∙ ap (Mreᵏ (f x)) (fun-ext λ a → ▹-ext ih▹)
  ∙ sym (fix-path (pureᵏ-body (f x)))

apᵐ-homo : {f : B → C} {x : B}
         → apᵐ {A = A} (pureᵐ f) (pureᵐ x) ＝ pureᵐ (f x)
apᵐ-homo = fun-ext λ k → apᵏ-homo

apᵏ-inter : {x : B}
          → (mf : gMoore k A (B → C))
          → apᵏ mf (pureᵏ x) ＝ apᵏ (pureᵏ (_$ x)) mf
apᵏ-inter {k} {x} = fix {k} λ ih▹ → λ where
  mf@(Mreᵏ bf trf) →
     ap (apᵏ mf) (fix-path (pureᵏ-body x))
   ∙ ap (λ q → q mf (pureᵏ-body x (next (pureᵏ x)))) (fix-path apᵏ-body)
   ∙ ap (Mreᵏ (bf x)) (fun-ext (λ a → ▹-ext (ih▹ ⊛ trf a)))
   ∙ ap (λ q → q (pureᵏ-body (_$ x) (next (pureᵏ (_$ x)))) mf) (sym $ fix-path apᵏ-body)
   ∙ ap (λ q → apᵏ q mf) (sym $ fix-path (pureᵏ-body (_$ x)))

apᵐ-inter : {x : B}
          → (mf : Moore A (B → C))
          → apᵐ mf (pureᵐ x) ＝ apᵐ (pureᵐ (_$ x)) mf
apᵐ-inter mf = fun-ext (apᵏ-inter ∘ mf)

-- zipWith

zipWithᵏ : (B → C → D) → gMoore k A B → gMoore k A C → gMoore k A D
zipWithᵏ f mb mc = apᵏ (mapᵏ f mb) mc

zipWithᵐ : (B → C → D) → Moore A B → Moore A C → Moore A D
zipWithᵐ f mb mc = apᵐ (mapᵐ f mb) mc

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

