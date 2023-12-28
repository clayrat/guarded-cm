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

Code-refl-body : ▹ ((s : Stream A) → Code s s) → (s : Stream A) → Code s s
Code-refl-body C▹ (cons h t▹) =
  refl , λ α → transport (λ i → pfix Code-body (~ i) α (t▹ α) (t▹ α)) ((C▹ ⊛ t▹) α)

Code-refl : (s : Stream A) → Code s s
Code-refl = fix Code-refl-body

decode : (s t : Stream A) → Code s t → s ＝ t
decode (cons h₁ t▹₁) (cons h₂ t▹₂) (e , c) =
  ap² cons e (▹-ext λ α → decode (t▹₁ α) (t▹₂ α) (transport (λ i → pfix Code-body i α (t▹₁ α) (t▹₂ α)) (c α)))

encode : {c1 c2 : Stream A} → c1 ＝ c2 → Code c1 c2
encode {c1} {c2} e = subst (Code c1) e (Code-refl c1)

-- TODO hlevel

cons-inj : {h₁ h₂ : A} {t▹₁ t▹₂ : ▹ Stream A}
         → cons h₁ t▹₁ ＝ cons h₂ t▹₂
         → (h₁ ＝ h₂) × (t▹₁ ＝ t▹₂)
cons-inj {t▹₁} {t▹₂} e =
  let ee = encode e in
  ee .fst , ▹-ext λ α → decode (t▹₁ α) (t▹₂ α) (transport (λ i → pfix Code-body i α (t▹₁ α) (t▹₂ α)) (ee .snd α))

cons-δ : A → Stream A → Stream A
cons-δ a s = cons a (next s)

headˢ : Stream A → A
headˢ (cons x _) = x

tail▹ˢ : Stream A → ▹ Stream A
tail▹ˢ (cons _ xs▹) = xs▹

stream-eq-coind : (R : Stream A → Stream A → 𝒰 ℓ′)
                → (∀ s1 s2 → R s1 s2 → headˢ s1 ＝ headˢ s2)
                → (∀ s1 s2 → R s1 s2 → ▸ (▹map R (tail▹ˢ s1) ⊛ (tail▹ˢ s2)))
                → ∀ s1 s2 → R s1 s2 → s1 ＝ s2
stream-eq-coind R hh ht = fix λ ih▹ → λ where
  (cons h1 t1▹) (cons h2 t2▹) r →
     ap² cons (hh (cons h1 t1▹) (cons h2 t2▹) r)
              (▹-ext (ih▹ ⊛ t1▹ ⊛′ t2▹ ⊛′ (ht (cons h1 t1▹) (cons h2 t2▹) r)))

uncons-eq : (s : Stream A) → s ＝ cons (headˢ s) (tail▹ˢ s)
uncons-eq (cons x xs▹) = refl

-- repeat aka constant stream

repeatˢ : A → Stream A
repeatˢ a = fix (cons a)

repeatˢ-eq : (a : A) → repeatˢ a ＝ cons a (next $ repeatˢ a)
repeatˢ-eq a = fix-path (cons a)

-- map

mapˢ-body : (A → B) → ▹ (Stream A → Stream B) → Stream A → Stream B
mapˢ-body f m▹ as = cons (f (headˢ as)) (m▹ ⊛ (tail▹ˢ as))

mapˢ : (A → B) → Stream A → Stream B
mapˢ f = fix (mapˢ-body f)

mapˢ-eq : (f : A → B)
        → ∀ a as▹
        → mapˢ f (cons a as▹) ＝ cons (f a) (▹map (mapˢ f) as▹)
mapˢ-eq f a as▹ = happly (fix-path (mapˢ-body f)) (cons a as▹)

mapˢ-head : (f : A → B) → (s : Stream A)
          → headˢ (mapˢ f s) ＝ f (headˢ s)
mapˢ-head f s = refl

mapˢ-tail : (f : A → B) → (s : Stream A)
          → tail▹ˢ (mapˢ f s) ＝ ▹map (mapˢ f) (tail▹ˢ s)
mapˢ-tail f (cons a as▹) = ap tail▹ˢ (mapˢ-eq f a as▹)

mapˢ-fusion : (f : A → B) → (g : B → C) → (s : Stream A)
            → mapˢ g (mapˢ f s) ＝ mapˢ (g ∘ f) s
mapˢ-fusion f g =
  fix λ ih▹ → λ where
    (cons a as▹) →
      mapˢ g (mapˢ f (cons a as▹))
        ＝⟨ ap (mapˢ g) (mapˢ-eq f a as▹) ⟩
      mapˢ g (cons (f a) (▹map (mapˢ f) as▹))
        ＝⟨ mapˢ-eq g (f a) (▹map (mapˢ f) as▹) ⟩
      cons (g (f a)) (▹map (mapˢ g) (▹map (mapˢ f) as▹))
        ＝⟨ ap (cons (g (f a))) (▹-ext (ih▹ ⊛ as▹)) ⟩
      cons (g (f a)) (▹map (mapˢ (g ∘ f)) as▹)
        ＝⟨ sym (mapˢ-eq (g ∘ f) a as▹) ⟩
      mapˢ (g ∘ f) (cons a as▹)
        ∎

mapˢ-repeat : (a : A) → (f : A → B) → mapˢ f (repeatˢ a) ＝ repeatˢ (f a)
mapˢ-repeat a f = fix λ prf▹ →
  mapˢ f (repeatˢ a)
    ＝⟨ ap (mapˢ f) (repeatˢ-eq a)  ⟩
  mapˢ f (cons a (next $ repeatˢ a))
    ＝⟨ mapˢ-eq f a (λ x → cons a (dfix (cons a))) ⟩
  cons (f a) (next $ mapˢ f (repeatˢ a))
    ＝⟨ ap (cons (f a)) (▹-ext prf▹) ⟩
  cons (f a) (next $ repeatˢ (f a))
    ＝⟨ ap (cons (f a)) (▹-ext λ α → sym $ pfix-ext (cons (f a)) α) ⟩
  cons (f a) (dfix (cons (f a)))
    ＝⟨⟩
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
scanl1ˢ f = fix λ sc▹ s → cons (headˢ s) (▹map (mapˢ (f (headˢ s))) (sc▹ ⊛ tail▹ˢ s))

-- iterate

iterateˢ-body : ▹ (A → A) → ▹ (A → Stream A) → A → Stream A
iterateˢ-body f i▹ a = cons a (i▹ ⊛ (f ⊛ next a))

iterateˢ : ▹ (A → A) → A → Stream A
iterateˢ f = fix (iterateˢ-body f)

tail-iterateˢ : (f▹ : ▹ (A → A)) → (x : A)
              → tail▹ˢ (iterateˢ f▹ x) ＝ ▹map (iterateˢ f▹) (f▹ ⊛ next x)
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
            → zipWithˢ f (cons a as▹) (cons b bs▹) ＝ cons (f a b) (▹map (zipWithˢ f) as▹ ⊛ bs▹)
zipWithˢ-eq f a as▹ b bs▹ =
  happly (happly (fix-path (zipWithˢ-body f)) (cons a as▹)) (cons b bs▹)

zipWithˢ-comm : (f : A → A → B)
              → (∀ a b → f a b ＝ f b a)
              → ∀ s t → zipWithˢ f s t ＝ zipWithˢ f t s
zipWithˢ-comm f fc = fix λ ih▹ → λ where
  (cons x s▹) (cons y t▹) → zipWithˢ-eq f x s▹ y t▹
                          ∙ ap² cons (fc x y) (▹-ext λ α → ih▹ α (s▹ α) (t▹ α))
                          ∙ sym (zipWithˢ-eq f y t▹ x s▹)

zipˢ : Stream A → Stream B → Stream (A × B)
zipˢ = zipWithˢ (_,_)

-- natural numbers

natsˢ : Stream ℕ
natsˢ = fix λ nats▹ → cons 0 (▹map (mapˢ suc) nats▹)

natsˢ-tail : tail▹ˢ natsˢ ＝ next (mapˢ suc natsˢ)
natsˢ-tail = ap tail▹ˢ (fix-path (λ nats▹ → cons 0 (λ α → mapˢ suc (nats▹ α))))

-- Fibonacci numbers

fibˢ : Stream ℕ
fibˢ = fix $ cons 0 ∘ ▹map (λ s → cons 1 $ ▹map (zipWithˢ _+_ s) (tail▹ˢ s))

-- prime numbers

-- TODO fuse
primesˢ : Stream ℕ
primesˢ = fix λ pr▹ → cons 2 (▹map (mapˢ suc ∘ scanl1ˢ _·_) pr▹)

-- paperfolding / dragon curve sequence

toggleˢ : Stream Bool
toggleˢ = fix λ t▹ → cons true (next (cons false t▹))

paperfoldsˢ : Stream Bool
paperfoldsˢ = fix (interleaveˢ toggleˢ)

-- Thue-Morse sequence

hˢ-body : ▹ (Stream Bool → Stream Bool) → Stream Bool → Stream Bool
hˢ-body h▹ s with (headˢ s)
... | false = cons false (next (cons true  (h▹ ⊛ tail▹ˢ s)))
... | true  = cons true  (next (cons false (h▹ ⊛ tail▹ˢ s)))

hˢ : Stream Bool → Stream Bool
hˢ = fix hˢ-body

thuemorseˢ : Stream Bool
thuemorseˢ = fix λ t▹ → cons false (▹map (λ tm → cons true (▹map hˢ (tail▹ˢ (hˢ tm)))) t▹)

-- Pascal coefficients

pascal-nextˢ : Stream ℕ → Stream ℕ
pascal-nextˢ xs = fix λ p▹ → cons 1 (▹map (zipWithˢ _+_) (tail▹ˢ xs) ⊛ p▹)

pascalˢ : Stream (Stream ℕ)
pascalˢ = fix λ p▹ → cons (repeatˢ 1) (▹map (mapˢ pascal-nextˢ) p▹)
