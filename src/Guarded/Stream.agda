{-# OPTIONS --guarded #-}
module Guarded.Stream where

open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.List
open import LaterG

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

-- guarded streams

data Stream (A : 𝒰 ℓ) : 𝒰 ℓ where
  cons : A → ▹ Stream A → Stream A

Code-body : ▹ (Stream A → Stream A → 𝒰 (level-of-type A)) → Stream A → Stream A → 𝒰 (level-of-type A)
Code-body C▹ (cons h₁ t▹₁) (cons h₂ t▹₂) = (h₁ ＝ h₂) × ▸ (C▹ ⊛ t▹₁ ⊛ t▹₂)

Code : Stream A → Stream A → 𝒰 (level-of-type A)
Code = fix Code-body

Code-cc-eq : {h₁ h₂ : A} {t▹₁ t▹₂ : ▹ Stream A} → Code (cons h₁ t▹₁) (cons h₂ t▹₂) ＝ (h₁ ＝ h₂) × ▸ (Code ⍉ t▹₁ ⊛ t▹₂)
Code-cc-eq {h₁} {h₂} {t▹₁} {t▹₂} i = (h₁ ＝ h₂) × (▹[ α ] (pfix Code-body i α (t▹₁ α) (t▹₂ α)))

Code-cc⇉ : {h₁ h₂ : A} {t▹₁ t▹₂ : ▹ Stream A} → Code (cons h₁ t▹₁) (cons h₂ t▹₂) → (h₁ ＝ h₂) × ▸ (Code ⍉ t▹₁ ⊛ t▹₂)
Code-cc⇉ = transport Code-cc-eq

⇉Code-cc : {h₁ h₂ : A} {t▹₁ t▹₂ : ▹ Stream A} → (h₁ ＝ h₂) × ▸ (Code ⍉ t▹₁ ⊛ t▹₂) → Code (cons h₁ t▹₁) (cons h₂ t▹₂)
⇉Code-cc = transport (sym Code-cc-eq)

Code-refl-body : ▹ ((s : Stream A) → Code s s) → (s : Stream A) → Code s s
Code-refl-body C▹ (cons h t▹) = ⇉Code-cc (refl , (C▹ ⊛ t▹))

Code-refl : (s : Stream A) → Code s s
Code-refl = fix Code-refl-body

decode : (s t : Stream A) → Code s t → s ＝ t
decode (cons h₁ t▹₁) (cons h₂ t▹₂) c =
  let (eh , et) = Code-cc⇉ c in
  ap² cons eh (▹-ext λ α → decode (t▹₁ α) (t▹₂ α) (et α))

encode : {c1 c2 : Stream A} → c1 ＝ c2 → Code c1 c2
encode {c1} {c2} e = subst (Code c1) e (Code-refl c1)

-- TODO hlevel

cons-inj : {h₁ h₂ : A} {t▹₁ t▹₂ : ▹ Stream A}
         → cons h₁ t▹₁ ＝ cons h₂ t▹₂
         → (h₁ ＝ h₂) × (t▹₁ ＝ t▹₂)
cons-inj {t▹₁} {t▹₂} e =
  let (e1 , e2) = Code-cc⇉ (encode e) in
  e1 , ▹-ext (decode ⍉ t▹₁ ⊛▹ t▹₂ ⊛▹ e2)

cons-δ : A → Stream A → Stream A
cons-δ a = cons a ∘ next

headˢ : Stream A → A
headˢ (cons x _) = x

tail▹ˢ : Stream A → ▹ Stream A
tail▹ˢ (cons _ xs▹) = xs▹

stream-eq-coind : (R : Stream A → Stream A → 𝒰 ℓ′)
                → (∀ s1 s2 → R s1 s2 → headˢ s1 ＝ headˢ s2)
                → (∀ s1 s2 → R s1 s2 → ▸ (R ⍉ (tail▹ˢ s1) ⊛ (tail▹ˢ s2)))
                → ∀ s1 s2 → R s1 s2 → s1 ＝ s2
stream-eq-coind R hh ht = fix λ ih▹ → λ where
  (cons h1 t1▹) (cons h2 t2▹) r →
     ap² cons (hh (cons h1 t1▹) (cons h2 t2▹) r)
              (▹-ext (ih▹ ⊛ t1▹ ⊛▹ t2▹ ⊛▹ (ht (cons h1 t1▹) (cons h2 t2▹) r)))

uncons-eq : (s : Stream A) → s ＝ cons (headˢ s) (tail▹ˢ s)
uncons-eq (cons x xs▹) = refl

-- repeat aka constant stream

repeatˢ : A → Stream A
repeatˢ a = fix (cons a)

repeatˢ-eq : (a : A) → repeatˢ a ＝ cons-δ a (repeatˢ a)
repeatˢ-eq a = fix-path (cons a)

-- map

mapˢ-body : (A → B) → ▹ (Stream A → Stream B) → Stream A → Stream B
mapˢ-body f m▹ as = cons (f (headˢ as)) (m▹ ⊛ (tail▹ˢ as))

mapˢ : (A → B) → Stream A → Stream B
mapˢ f = fix (mapˢ-body f)

mapˢ-eq : (f : A → B)
        → ∀ a as▹
        → mapˢ f (cons a as▹) ＝ cons (f a) ((mapˢ f) ⍉ as▹)
mapˢ-eq f a as▹ = happly (fix-path (mapˢ-body f)) (cons a as▹)

mapˢ-head : (f : A → B) → (s : Stream A)
          → headˢ (mapˢ f s) ＝ f (headˢ s)
mapˢ-head f s = refl

mapˢ-tail : (f : A → B) → (s : Stream A)
          → tail▹ˢ (mapˢ f s) ＝ (mapˢ f) ⍉ (tail▹ˢ s)
mapˢ-tail f (cons a as▹) = ap tail▹ˢ (mapˢ-eq f a as▹)

mapˢ-fusion : (f : A → B) → (g : B → C) → (s : Stream A)
            → mapˢ g (mapˢ f s) ＝ mapˢ (g ∘ f) s
mapˢ-fusion f g =
  fix λ ih▹ → λ where
    s@(cons a as▹) →
      mapˢ g ⌜ mapˢ f s ⌝
        ＝⟨ ap! (mapˢ-eq f a as▹) ⟩
      mapˢ g (cons (f a) ((mapˢ f) ⍉ as▹))
        ＝⟨ mapˢ-eq g (f a) ((mapˢ f) ⍉ as▹) ⟩
      cons (g (f a)) ⌜ (mapˢ g) ⍉ ((mapˢ f) ⍉ as▹) ⌝
        ＝⟨ ap! (▹-ext (ih▹ ⊛ as▹)) ⟩
      cons (g (f a)) ((mapˢ (g ∘ f)) ⍉ as▹)
        ＝˘⟨ mapˢ-eq (g ∘ f) a as▹ ⟩
      mapˢ (g ∘ f) s
        ∎

mapˢ-repeat : (a : A) → (f : A → B) → mapˢ f (repeatˢ a) ＝ repeatˢ (f a)
mapˢ-repeat a f = fix λ prf▹ →
  mapˢ f ⌜ repeatˢ a ⌝
    ＝⟨ ap! (repeatˢ-eq a)  ⟩
  mapˢ f (cons a (next $ repeatˢ a))
    ＝⟨ mapˢ-eq f a (next $ repeatˢ a) ⟩
  cons (f a) ⌜ next $ mapˢ f (repeatˢ a) ⌝
    ＝⟨ ap! (▹-ext prf▹) ⟩
  cons (f a) (next $ repeatˢ (f a))
    ＝˘⟨ repeatˢ-eq (f a) ⟩
  repeatˢ (f a)
    ∎

-- duplicate vs every-other

dup : Stream A → Stream A
dup = fix λ d▹ s → cons (headˢ s) (next (cons (headˢ s) (d▹ ⊛ tail▹ˢ s)))

-- impossible

--eo : Stream A → Stream A
--eo = fix λ e▹ s → cons (headˢ s) (e▹ ⊛ tail▹ˢ (tail▹ˢ s {!!}))

eo-causal : Stream A → Stream (Maybe A)
eo-causal = fix (λ e▹ s → cons (just (headˢ s)) λ α → cons nothing (e▹ ⊛ (tail▹ˢ (tail▹ˢ s α))))

-- folding

foldrˢ-body : (A → ▹ B → B) → ▹ (Stream A → B) → Stream A → B
foldrˢ-body f f▹ s = f (headˢ s) (f▹ ⊛ tail▹ˢ s)

foldrˢ : (A → ▹ B → B) → Stream A → B
foldrˢ f = fix (foldrˢ-body f)

scanl1ˢ : (A → A → A) → Stream A → Stream A
scanl1ˢ f = fix λ sc▹ s → cons (headˢ s) ((mapˢ (f (headˢ s))) ⍉ (sc▹ ⊛ tail▹ˢ s))

-- iterate

iterateˢ-body : ▹ (A → A) → ▹ (A → Stream A) → A → Stream A
iterateˢ-body f i▹ a = cons a (i▹ ⊛ (f ⊛ next a))

iterateˢ : ▹ (A → A) → A → Stream A
iterateˢ f = fix (iterateˢ-body f)

tail-iterateˢ : (f▹ : ▹ (A → A)) → (x : A)
              → tail▹ˢ (iterateˢ f▹ x) ＝ (iterateˢ f▹) ⍉ (f▹ ⊛ next x)
tail-iterateˢ f x = ap (_⊛ (f ⊛ next x)) (pfix (iterateˢ-body f))

-- interleave

interleaveˢ : Stream A → ▹ Stream A → Stream A
interleaveˢ = fix λ i▹ s t▹ → cons (headˢ s) (i▹ ⊛ t▹ ⊛ next (tail▹ˢ s))

-- zipping

zipWithˢ-body : (A → B → C)
              → ▹ (Stream A → Stream B → Stream C)
              → Stream A → Stream B → Stream C
zipWithˢ-body f zw▹ sa sb = cons (f (headˢ sa) (headˢ sb)) (zw▹ ⊛ tail▹ˢ sa ⊛ tail▹ˢ sb)

zipWithˢ : (A → B → C) → Stream A → Stream B → Stream C
zipWithˢ f = fix (zipWithˢ-body f)

zipWithˢ-eq : (f : A → B → C)
            → ∀ a as▹ b bs▹
            → zipWithˢ f (cons a as▹) (cons b bs▹) ＝ cons (f a b) ((zipWithˢ f) ⍉ as▹ ⊛ bs▹)
zipWithˢ-eq f a as▹ b bs▹ =
  happly (happly (fix-path (zipWithˢ-body f)) (cons a as▹)) (cons b bs▹)

zipWithˢ-comm : (f : A → A → B)
              → (∀ a b → f a b ＝ f b a)
              → ∀ s t → zipWithˢ f s t ＝ zipWithˢ f t s
zipWithˢ-comm f fc = fix λ ih▹ → λ where
  (cons x s▹) (cons y t▹) → zipWithˢ-eq f x s▹ y t▹
                          ∙ ap² cons (fc x y) (▹-ext (ih▹ ⊛ s▹ ⊛▹ t▹))
                          ∙ sym (zipWithˢ-eq f y t▹ x s▹)

zipˢ : Stream A → Stream B → Stream (A × B)
zipˢ = zipWithˢ (_,_)

-- natural numbers

natsˢ-body : ▹ Stream ℕ → Stream ℕ
natsˢ-body = cons 0 ∘ (mapˢ suc ⍉_)

natsˢ : Stream ℕ
natsˢ = fix natsˢ-body

natsˢ-tail : tail▹ˢ natsˢ ＝ next (mapˢ suc natsˢ)
natsˢ-tail = ap tail▹ˢ (fix-path natsˢ-body)

-- Fibonacci numbers

fibˢ-body : ▹ Stream ℕ → Stream ℕ
fibˢ-body = cons 0 ∘ ((λ s → cons 1 $ (zipWithˢ _+_ s) ⍉ (tail▹ˢ s)) ⍉_)

fibˢ : Stream ℕ
fibˢ = fix fibˢ-body

-- prime numbers

-- TODO fuse
primesˢ-body : ▹ Stream ℕ → Stream ℕ
primesˢ-body = cons 2 ∘ ((mapˢ suc ∘ scanl1ˢ _·_) ⍉_)

primesˢ : Stream ℕ
primesˢ = fix primesˢ-body

-- paperfolding / dragon curve sequence

toggleˢ-body : ▹ Stream Bool → Stream Bool
toggleˢ-body = cons-δ true ∘ cons false

toggleˢ : Stream Bool
toggleˢ = fix toggleˢ-body

paperfoldsˢ : Stream Bool
paperfoldsˢ = fix (interleaveˢ toggleˢ)

-- Thue-Morse sequence

hˢ-body : ▹ (Stream Bool → Stream Bool) → Stream Bool → Stream Bool
hˢ-body h▹ s with headˢ s
... | false = cons-δ false (cons true  (h▹ ⊛ tail▹ˢ s))
... | true  = cons-δ true  (cons false (h▹ ⊛ tail▹ˢ s))

hˢ : Stream Bool → Stream Bool
hˢ = fix hˢ-body

thuemorseˢ : Stream Bool
thuemorseˢ = fix $ cons false ∘ ((λ tm → cons true (hˢ ⍉ (tail▹ˢ (hˢ tm)))) ⍉_)

-- Pascal coefficients

pascal-nextˢ : Stream ℕ → Stream ℕ
pascal-nextˢ xs = fix λ p▹ → cons 1 ((zipWithˢ _+_) ⍉ (tail▹ˢ xs) ⊛ p▹)

pascalˢ : Stream (Stream ℕ)
pascalˢ = fix $ cons (repeatˢ 1) ∘ ((mapˢ pascal-nextˢ) ⍉_)
