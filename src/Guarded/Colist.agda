{-# OPTIONS --guarded #-}
module Guarded.Colist where

open import Prelude
open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Data.List

open import LaterG

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

-- guarded colists

data Colist (A : 𝒰 ℓ) : 𝒰 ℓ where
  cnil  : Colist A
  ccons : A → ▹ Colist A → Colist A

module Colist-code where
  Code-body : ▹ (Colist A → Colist A → 𝒰 (level-of-type A)) → Colist A → Colist A → 𝒰 (level-of-type A)
  Code-body C▹  cnil          cnil         = Lift _ ⊤
  Code-body C▹  cnil         (ccons _ _)   = Lift _ ⊥
  Code-body C▹ (ccons _ _)    cnil         = Lift _ ⊥
  Code-body C▹ (ccons x cx▹) (ccons y cy▹) = (x ＝ y) × (▸ (C▹ ⊛ cx▹ ⊛ cy▹))

  Code : Colist A → Colist A → 𝒰 (level-of-type A)
  Code = fix Code-body

  Code-cc-eq : {x y : A} {cx▹ cy▹ : ▹ Colist A}
             → Code (ccons x cx▹) (ccons y cy▹) ＝ (x ＝ y) × ▸ (Code ⍉ cx▹ ⊛ cy▹)
  Code-cc-eq {x} {y} {cx▹} {cy▹} i = (x ＝ y) × (▹[ α ] pfix Code-body i α (cx▹ α) (cy▹ α))

  Code-cc⇉ : {x y : A} {cx▹ cy▹ : ▹ Colist A}
           → Code (ccons x cx▹) (ccons y cy▹)
           → (x ＝ y) × ▸ (Code ⍉ cx▹ ⊛ cy▹)
  Code-cc⇉ = transport Code-cc-eq

  ⇉Code-cc : {x y : A} {cx▹ cy▹ : ▹ Colist A}
           → (x ＝ y) × ▸ (Code ⍉ cx▹ ⊛ cy▹)
           → Code (ccons x cx▹) (ccons y cy▹)
  ⇉Code-cc = transport (sym Code-cc-eq)

  Code-refl-body : ▹ ((c : Colist A) → Code c c) → (c : Colist A) → Code c c
  Code-refl-body C▹  cnil        = lift tt
  Code-refl-body C▹ (ccons x c▹) = ⇉Code-cc (refl , (C▹ ⊛ c▹))

  Code-refl : (c : Colist A) → Code c c
  Code-refl = fix Code-refl-body

  encode : {c1 c2 : Colist A} → c1 ＝ c2 → Code c1 c2
  encode {c1} {c2} e = subst (Code c1) e (Code-refl c1)

  decode : (m n : Colist A) → Code m n → m ＝ n
  decode  cnil          cnil          c = refl
  decode (ccons x cx▹) (ccons y cy▹)  c =
    let (ex , ec) = Code-cc⇉ c in
    ap² ccons ex (▹-ext λ α → decode (cx▹ α) (cy▹ α) (ec α))

cnil≠ccons : {x : A} {c▹ : ▹ Colist A} → cnil ≠ ccons x c▹
cnil≠ccons = lower ∘ Colist-code.encode

ccons-inj : {x y : A} {cx▹ cy▹ : ▹ Colist A}
          → ccons x cx▹ ＝ ccons y cy▹ → (x ＝ y) × (cx▹ ＝ cy▹)
ccons-inj {x} {y} {cx▹} {cy▹} e =
  let (ex , ec) = Colist-code.Code-cc⇉ (Colist-code.encode e) in
  ex , ▹-ext (Colist-code.decode ⍉ cx▹ ⊛▹ cy▹ ⊛▹ ec)

prepend : A → Colist A → Colist A
prepend a = ccons a ∘ next

-- singleton

singletonˡ : A → Colist A
singletonˡ a = prepend a cnil

-- repeat

repeatˡ : A → Colist A
repeatˡ = fix ∘ ccons

-- uncons

unconsˡ : Colist A -> Maybe (A × ▹ Colist A)
unconsˡ  cnil         = nothing
unconsˡ (ccons a as▹) = just (a , as▹)

-- fromList

fromList : List A → Colist A
fromList []      = cnil
fromList (x ∷ l) = prepend x (fromList l)

-- catList

catList : List A → Colist A → Colist A
catList []      c = c
catList (x ∷ l) c = prepend x (catList l c)

catFromList : (as bs : List A)
            → fromList (as ++ bs) ＝ catList as (fromList bs)
catFromList []       bs = refl
catFromList (a ∷ as) bs = ap (prepend a) (catFromList as bs)

-- append

appendˡ-body : ▹ (Colist A → Colist A → Colist A) → Colist A → Colist A → Colist A
appendˡ-body ap▹  cnil         t = t
appendˡ-body ap▹ (ccons x xs▹) t = ccons x ((ap▹ ⊛ xs▹) ⊛ next t)

appendˡ : Colist A → Colist A → Colist A
appendˡ = fix appendˡ-body

-- map

mapˡ-body : (A → B) → ▹ (Colist A → Colist B) → Colist A → Colist B
mapˡ-body f mp▹  cnil         = cnil
mapˡ-body f mp▹ (ccons x xs▹) = ccons (f x) (mp▹ ⊛ xs▹)

mapˡ : (A → B) → Colist A → Colist B
mapˡ f = fix (mapˡ-body f)

map-catList : ∀ {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
            → (f : A → B) → (l : List A) → (c : Colist A)
            → mapˡ f (catList l c) ＝ catList (map f l) (mapˡ f c)
map-catList f []      c = refl
map-catList f (x ∷ l) c = ap (ccons (f x)) (▹-ext λ α → (λ i → pfix (mapˡ-body f) i α (catList l c))
                                                             ∙ map-catList f l c)

-- zipWith

zipWithˡ-body : (A → B → C) → ▹ (Colist A → Colist B → Colist C) → Colist A → Colist B → Colist C
zipWithˡ-body f zw▹  cnil          cnil         = cnil
zipWithˡ-body f zw▹  cnil         (ccons _ _  ) = cnil
zipWithˡ-body f zw▹ (ccons _ _  )  cnil         = cnil
zipWithˡ-body f zw▹ (ccons a as▹) (ccons b bs▹) = ccons (f a b) (zw▹ ⊛ as▹ ⊛ bs▹)

zipWithˡ : (A → B → C) → Colist A → Colist B → Colist C
zipWithˡ f = fix (zipWithˡ-body f)

-- intersperse

prepend-to-allˡ-body : A → ▹ (Colist A → Colist A) → Colist A → Colist A
prepend-to-allˡ-body sep p▹  cnil         = cnil
prepend-to-allˡ-body sep p▹ (ccons x xs▹) = prepend sep (ccons x (p▹ ⊛ xs▹))

prepend-to-allˡ : A → Colist A → Colist A
prepend-to-allˡ sep = fix (prepend-to-allˡ-body sep)

intersperseˡ : A → Colist A → Colist A
intersperseˡ sep  cnil         = cnil
intersperseˡ sep (ccons x xs▹) = ccons x ((prepend-to-allˡ sep) ⍉ xs▹)

-- foldr

foldrˡ-body : (A → ▹ B → B) → B → ▹ (Colist A → B) → Colist A → B
foldrˡ-body f z f▹  cnil         = z
foldrˡ-body f z f▹ (ccons x xs▹) = f x (f▹ ⊛ xs▹)

foldrˡ : (A → ▹ B → B) → Colist A → B → B
foldrˡ f c z = fix (foldrˡ-body f z) c

-- finiteness

is-finiteˡ : Colist A → 𝒰 (level-of-type A)
is-finiteˡ = fibre fromList

is-finite-uncons : (x : A) (c▹ : ▹ Colist A) → is-finiteˡ (ccons x c▹) → ▸ (is-finiteˡ ⍉ c▹)
is-finite-uncons x c▹ ([]    , e) = absurd (cnil≠ccons e)
is-finite-uncons x c▹ (y ∷ l , e) = λ α → l , (▹-ap (ccons-inj e .snd) α)

is-finite-downˡ : (x : A) (c : Colist A) → is-finiteˡ (prepend x c) → ▹ (is-finiteˡ c)
is-finite-downˡ x c = is-finite-uncons x (next c)

is-finite-upˡ : (x : A) (c : Colist A) → is-finiteˡ c → is-finiteˡ (prepend x c)
is-finite-upˡ x c (l , e) = (x ∷ l) , ap (prepend x) e

-- propositional version

is-finite-pˡ : Colist A → 𝒰 (level-of-type A)
is-finite-pˡ = ∥_∥₁ ∘ is-finiteˡ

is-finite-uncons-p : (x : A) (c▹ : ▹ Colist A) → is-finite-pˡ (ccons x c▹) → ▸ (is-finite-pˡ ⍉ c▹)
is-finite-uncons-p x c▹ p = ▹trunc₁ id (map (is-finite-uncons x c▹) p)

is-finite-down-pˡ : (x : A) (c : Colist A) → is-finite-pˡ (prepend x c) → ▹ (is-finite-pˡ c)
is-finite-down-pˡ x c = is-finite-uncons-p x (next c)

is-finite-up-pˡ : (x : A) (c : Colist A) → is-finite-pˡ c → is-finite-pˡ (prepend x c)
is-finite-up-pˡ x c = map (is-finite-upˡ x c)
