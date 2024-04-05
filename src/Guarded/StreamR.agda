{-# OPTIONS --guarded #-}
module Guarded.StreamR where

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

-- guarded streams as records

record Stream (A : 𝒰 ℓ) : 𝒰 ℓ where
  -- we're forced to use this combination:
  -- 1. inductive - we need recursive records which don't clash with guard use
  -- 2. no-eta-equality - we need members of the record be structurally smaller than the record
  -- 3. pattern - we still need some form of eta for proofs (this precludes using copatterns though)
  inductive ; no-eta-equality ; pattern
  constructor cons
  field
    hd  : A
    tl▹ : ▹ Stream A

open Stream

Code-body : ▹ (Stream A → Stream A → 𝒰 (level-of-type A)) → Stream A → Stream A → 𝒰 (level-of-type A)
Code-body C▹ s₁ s₂ = (s₁ .hd ＝ s₂ .hd) × ▸ (C▹ ⊛ s₁ .tl▹ ⊛ s₂ .tl▹)

Code : Stream A → Stream A → 𝒰 (level-of-type A)
Code = fix Code-body

Code-cc-eq : {s₁ s₂ : Stream A} → Code s₁ s₂ ＝ (s₁ .hd ＝ s₂ .hd) × ▸ (Code ⍉ s₁ .tl▹ ⊛ s₂ .tl▹)
Code-cc-eq {s₁} {s₂} i = (s₁ .hd ＝ s₂ .hd) × (▹[ α ] (pfix Code-body i α (s₁ .tl▹ α) (s₂ .tl▹ α)))

Code-cc⇉ : {s₁ s₂ : Stream A} → Code s₁ s₂ → (s₁ .hd ＝ s₂ .hd) × ▸ (Code ⍉ s₁ .tl▹ ⊛ s₂ .tl▹)
Code-cc⇉ {s₁} {s₂} = transport (Code-cc-eq {s₁ = s₁} {s₂})

⇉Code-cc : {s₁ s₂ : Stream A} → (s₁ .hd ＝ s₂ .hd) × ▸ (Code ⍉ s₁ .tl▹ ⊛ s₂ .tl▹) → Code s₁ s₂
⇉Code-cc {s₁} {s₂} = transport (sym (Code-cc-eq {s₁ = s₁} {s₂}))

Code-refl-body : ▹ ((s : Stream A) → Code s s) → (s : Stream A) → Code s s
Code-refl-body C▹ s = ⇉Code-cc {s₁ = s} {s₂ = s} (refl , (C▹ ⊛ s .tl▹))

Code-refl : (s : Stream A) → Code s s
Code-refl = fix Code-refl-body

uncons-eq : (s : Stream A) → s ＝ cons (s .hd) (s .tl▹)
uncons-eq (cons x xs▹) = refl

-- can't use uncons-eq here because of termination issues
decode : (s t : Stream A) → Code s t → s ＝ t
decode s₁@(cons h₁ t▹₁) s₂@(cons h₂ t▹₂) c =
  let (eh , et) = Code-cc⇉ {s₁ = s₁} {s₂} c in
  ap² cons eh (▹-ext λ α → decode (t▹₁ α) (t▹₂ α) (et α))

encode : {c1 c2 : Stream A} → c1 ＝ c2 → Code c1 c2
encode {c1} {c2} e = subst (Code c1) e (Code-refl c1)

-- TODO hlevel

cons-inj : {s₁ s₂ : Stream A}
         → s₁ ＝ s₂
         → (s₁ .hd ＝ s₂ .hd) × (s₁ .tl▹ ＝ s₂ .tl▹)
cons-inj {s₁} {s₂} e =
  let (e1 , e2) = Code-cc⇉ {s₁ = s₁} {s₂} (encode e) in
  e1 , ▹-ext (decode ⍉ s₁ .tl▹ ⊛▹ s₂ .tl▹ ⊛▹ e2)

cons-δ : A → Stream A → Stream A
cons-δ a s = cons a (next s)

stream-eq-coind : (R : Stream A → Stream A → 𝒰 ℓ′)
                → (∀ s1 s2 → R s1 s2 → s1 .hd ＝ s2 .hd)
                → (∀ s1 s2 → R s1 s2 → ▸ (R ⍉ (s1 .tl▹) ⊛ (s2 .tl▹)))
                → ∀ s1 s2 → R s1 s2 → s1 ＝ s2
stream-eq-coind R hh ht = fix λ ih▹ → λ where
  s1 s2 r →
       uncons-eq s1
     ∙ ap² cons (hh s1 s2 r)
                (▹-ext (ih▹ ⊛ s1 .tl▹ ⊛▹ s2 .tl▹ ⊛▹ (ht s1 s2 r)))
     ∙ sym (uncons-eq s2)

-- repeat aka constant stream

repeatˢ : A → Stream A
repeatˢ a = fix (cons a)

repeatˢ-eq : (a : A) → repeatˢ a ＝ cons-δ a (repeatˢ a)
repeatˢ-eq a = fix-path (cons a)

-- map

mapˢ-body : (A → B) → ▹ (Stream A → Stream B) → Stream A → Stream B
mapˢ-body f m▹ as = cons (f (as .hd)) (m▹ ⊛ (as .tl▹))

mapˢ : (A → B) → Stream A → Stream B
mapˢ f = fix (mapˢ-body f)

mapˢ-eq : (f : A → B)
        → ∀ s
        → mapˢ f s ＝ cons (f (s .hd)) ((mapˢ f) ⍉ (s .tl▹))
mapˢ-eq f = happly (fix-path (mapˢ-body f))

mapˢ-head : (f : A → B) → (s : Stream A)
          → (mapˢ f s) .hd ＝ f (s .hd)
mapˢ-head f s = refl

mapˢ-tail : (f : A → B) → (s : Stream A)
          → (mapˢ f s) .tl▹ ＝ (mapˢ f) ⍉ (s .tl▹)
mapˢ-tail f s = ap tl▹ (mapˢ-eq f s)

mapˢ-fusion : (f : A → B) → (g : B → C) → (s : Stream A)
            → mapˢ g (mapˢ f s) ＝ mapˢ (g ∘ f) s
mapˢ-fusion f g =
  fix λ ih▹ → λ where
    s →
      mapˢ g ⌜ mapˢ f s ⌝
        ＝⟨ ap! (mapˢ-eq f s) ⟩
      mapˢ g (cons (f (s .hd)) ((mapˢ f) ⍉ (s .tl▹)))
        ＝⟨ mapˢ-eq g (cons (f (s .hd)) ((mapˢ f) ⍉ (s .tl▹))) ⟩
      cons (g (f (s .hd))) ⌜ mapˢ g ⍉ (mapˢ f ⍉ s .tl▹) ⌝
        ＝⟨ ap! (▹-ext (ih▹ ⊛ s .tl▹)) ⟩
      cons (g (f (s .hd))) ((mapˢ (g ∘ f)) ⍉ (s .tl▹))
        ＝˘⟨ mapˢ-eq (g ∘ f) s ⟩
      mapˢ (g ∘ f) s
        ∎

mapˢ-repeat : (a : A) → (f : A → B) → mapˢ f (repeatˢ a) ＝ repeatˢ (f a)
mapˢ-repeat a f = fix λ prf▹ →
  mapˢ f ⌜ repeatˢ a ⌝
    ＝⟨ ap! (repeatˢ-eq a)  ⟩
  mapˢ f (cons-δ a (repeatˢ a))
    ＝⟨ mapˢ-eq f (cons-δ a (repeatˢ a)) ⟩
  cons (f a) ⌜ next $ mapˢ f (repeatˢ a) ⌝
    ＝⟨ ap! (▹-ext prf▹) ⟩
  cons-δ (f a) (repeatˢ (f a))
    ＝˘⟨ repeatˢ-eq (f a) ⟩
  repeatˢ (f a)
    ∎

-- duplicate vs every-other

dup : Stream A → Stream A
dup = fix λ d▹ s → cons-δ (s .hd) (cons (s .hd) (d▹ ⊛ s .tl▹))

-- impossible

--eo : Stream A → Stream A
--eo = fix λ e▹ s → cons (s .hd) (e▹ ⊛ s .tl▹ {!!} .tl▹)

eo-causal : Stream A → Stream (Maybe A)
eo-causal = fix λ e▹ s → cons (just (s .hd)) λ α → cons nothing (e▹ ⊛ (s .tl▹ α .tl▹))

-- folding

foldrˢ-body : (A → ▹ B → B) → ▹ (Stream A → B) → Stream A → B
foldrˢ-body f f▹ s = f (s .hd) (f▹ ⊛ s .tl▹)

foldrˢ : (A → ▹ B → B) → Stream A → B
foldrˢ f = fix (foldrˢ-body f)

scanl1ˢ : (A → A → A) → Stream A → Stream A
scanl1ˢ f = fix λ sc▹ s → cons (s .hd) ((mapˢ (f (s .hd))) ⍉ (sc▹ ⊛ s .tl▹))

-- iterate

iterateˢ-body : ▹ (A → A) → ▹ (A → Stream A) → A → Stream A
iterateˢ-body f i▹ a = cons a (i▹ ⊛ (f ⊛ next a))

iterateˢ : ▹ (A → A) → A → Stream A
iterateˢ f = fix (iterateˢ-body f)

tail-iterateˢ : (f▹ : ▹ (A → A)) → (x : A)
              → (iterateˢ f▹ x) .tl▹ ＝ (iterateˢ f▹) ⍉ (f▹ ⊛ next x)
tail-iterateˢ f x = ap (_⊛ (f ⊛ next x)) (pfix (iterateˢ-body f))

-- interleave

interleaveˢ : Stream A → ▹ Stream A → Stream A
interleaveˢ = fix λ i▹ s t▹ → cons (s .hd) (i▹ ⊛ t▹ ⊛ next (s .tl▹))

-- zipping

zipWithˢ-body : (A → B → C)
              → ▹ (Stream A → Stream B → Stream C)
              → Stream A → Stream B → Stream C
zipWithˢ-body f zw▹ sa sb = cons (f (sa .hd) (sb .hd)) (zw▹ ⊛ sa .tl▹ ⊛ sb .tl▹)

zipWithˢ : (A → B → C) → Stream A → Stream B → Stream C
zipWithˢ f = fix (zipWithˢ-body f)

zipWithˢ-eq : (f : A → B → C)
            → ∀ as bs
            → zipWithˢ f as bs ＝ cons (f (as .hd) (bs .hd)) ((zipWithˢ f) ⍉ as .tl▹ ⊛ bs .tl▹)
zipWithˢ-eq f as bs =
  happly (happly (fix-path (zipWithˢ-body f)) as) bs

zipWithˢ-comm : (f : A → A → B)
              → (∀ a b → f a b ＝ f b a)
              → ∀ s t → zipWithˢ f s t ＝ zipWithˢ f t s
zipWithˢ-comm f fc = fix λ ih▹ → λ where
  xs ys →
      zipWithˢ-eq f xs ys
    ∙ ap² cons (fc (xs .hd) (ys .hd)) (▹-ext (ih▹ ⊛ xs .tl▹ ⊛▹ ys .tl▹))
    ∙ sym (zipWithˢ-eq f ys xs)

zipˢ : Stream A → Stream B → Stream (A × B)
zipˢ = zipWithˢ _,_

-- comonad structure

extractˢ : Stream A → A
extractˢ = hd

-- aka tails
duplicateˢ-body : ▹ (Stream A → Stream (Stream A)) → Stream A → Stream (Stream A)
duplicateˢ-body d▹ s = cons s (d▹ ⊛ s .tl▹)

duplicateˢ : Stream A → Stream (Stream A)
duplicateˢ = fix duplicateˢ-body

extendˢ-body : (Stream A → B) → ▹ (Stream A → Stream B) → Stream A → Stream B
extendˢ-body f e▹ s = cons (f s) (e▹ ⊛ s .tl▹)

extendˢ : (Stream A → B) → Stream A → Stream B
extendˢ f = fix (extendˢ-body f)

extract-duplicate : (s : Stream A) → extractˢ (duplicateˢ s) ＝ s
extract-duplicate s =
    extractˢ (duplicateˢ s)
      ＝⟨ ap (λ q → extractˢ (q s)) (fix-path duplicateˢ-body) ⟩
    extractˢ (duplicateˢ-body (next duplicateˢ) s)
      ＝⟨⟩
    s
      ∎

map-extract-duplicate : (s : Stream A) → mapˢ extractˢ (duplicateˢ s) ＝ s
map-extract-duplicate = fix λ ih▹ → λ where
  s →
    mapˢ extractˢ (duplicateˢ s)
      ＝⟨ ap (λ q → mapˢ extractˢ (q s)) (fix-path duplicateˢ-body) ⟩
    mapˢ extractˢ (duplicateˢ-body (next duplicateˢ) s)
      ＝⟨ mapˢ-eq extractˢ (duplicateˢ-body (next duplicateˢ) s) ⟩
    cons (s .hd) (mapˢ extractˢ ⍉ (duplicateˢ ⍉ s .tl▹))
      ＝⟨ ap (cons (s .hd)) (▹-ext (ih▹ ⊛ s .tl▹)) ⟩
    cons (s .hd) (s .tl▹)
      ＝˘⟨ uncons-eq s ⟩
    s
      ∎

duplicate-duplicate : (s : Stream A) → duplicateˢ (duplicateˢ s) ＝ mapˢ duplicateˢ (duplicateˢ s)
duplicate-duplicate = fix λ ih▹ → λ where
  s →
    duplicateˢ (duplicateˢ s)
      ＝⟨ ap (λ q → duplicateˢ (q s)) (fix-path duplicateˢ-body) ⟩
    duplicateˢ (duplicateˢ-body (next duplicateˢ) s)
      ＝⟨ ap (λ q → q (duplicateˢ-body (next duplicateˢ) s)) (fix-path duplicateˢ-body) ⟩
    duplicateˢ-body (next duplicateˢ) (duplicateˢ-body (next duplicateˢ) s)
      ＝⟨⟩
    cons (cons s (duplicateˢ ⍉ s .tl▹)) (duplicateˢ ⍉ (duplicateˢ ⍉ s .tl▹))
      ＝⟨ ap (cons (cons s (duplicateˢ ⍉ s .tl▹))) (▹-ext λ α → ih▹ α (s .tl▹ α) ∙ ap (λ q → mapˢ q (duplicateˢ (s .tl▹ α))) (fix-path duplicateˢ-body)) ⟩
    cons (cons s (duplicateˢ ⍉ s .tl▹)) (mapˢ (duplicateˢ-body (next duplicateˢ)) ⍉ (duplicateˢ ⍉ s .tl▹))
      ＝˘⟨ mapˢ-eq (duplicateˢ-body (next duplicateˢ)) (cons s (duplicateˢ ⍉ s .tl▹)) ⟩
    mapˢ (duplicateˢ-body (next duplicateˢ)) (cons s (duplicateˢ ⍉ s .tl▹))
      ＝⟨⟩
    mapˢ (duplicateˢ-body (next duplicateˢ)) (duplicateˢ-body (next duplicateˢ) s)
      ＝˘⟨ ap (λ q → mapˢ q (duplicateˢ-body (next duplicateˢ) s)) (fix-path duplicateˢ-body) ⟩
    mapˢ duplicateˢ (duplicateˢ-body (next duplicateˢ) s)
      ＝˘⟨ ap (λ q → mapˢ duplicateˢ (q s)) (fix-path duplicateˢ-body) ⟩
    mapˢ duplicateˢ (duplicateˢ s)
      ∎

-- natural numbers

natsˢ-body : ▹ Stream ℕ → Stream ℕ
natsˢ-body = cons 0 ∘ (mapˢ suc ⍉_)

natsˢ : Stream ℕ
natsˢ = fix natsˢ-body

natsˢ-tail : natsˢ .tl▹ ＝ next (mapˢ suc natsˢ)
natsˢ-tail = ap tl▹ (fix-path natsˢ-body)

-- Fibonacci numbers

fibˢ-body : ▹ Stream ℕ → Stream ℕ
fibˢ-body = cons 0 ∘ ((λ s → cons 1 $ (zipWithˢ _+_ s) ⍉ (s .tl▹)) ⍉_)

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
toggleˢ-body = cons true ∘ next ∘ cons false

toggleˢ : Stream Bool
toggleˢ = fix toggleˢ-body

paperfoldsˢ : Stream Bool
paperfoldsˢ = fix (interleaveˢ toggleˢ)

-- Thue-Morse sequence

hˢ-body : ▹ (Stream Bool → Stream Bool) → Stream Bool → Stream Bool
hˢ-body h▹ s with s .hd
... | false = cons false (next (cons true  (h▹ ⊛ s .tl▹)))
... | true  = cons true  (next (cons false (h▹ ⊛ s .tl▹)))

hˢ : Stream Bool → Stream Bool
hˢ = fix hˢ-body

thuemorseˢ : Stream Bool
thuemorseˢ = fix $ cons false ∘ ((λ tm → cons true (hˢ ⍉ (hˢ tm .tl▹))) ⍉_)

-- Pascal coefficients

pascal-nextˢ : Stream ℕ → Stream ℕ
pascal-nextˢ xs = fix λ p▹ → cons 1 ((zipWithˢ _+_) ⍉ xs .tl▹ ⊛ p▹)

pascalˢ : Stream (Stream ℕ)
pascalˢ = fix $ cons (repeatˢ 1) ∘ ((mapˢ pascal-nextˢ) ⍉_)
