{-# OPTIONS --guarded #-}
module Clocked.Stream where

open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.List
open import Later

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  k : Cl

-- clocked streams

data gStream (k : Cl) (A : 𝒰 ℓ) : 𝒰 ℓ where
  cons : A → ▹ k (gStream k A) → gStream k A

Code-body : ▹ k (gStream k A → gStream k A → 𝒰 (level-of-type A))
               → gStream k A → gStream k A → 𝒰 (level-of-type A)
Code-body {k} C▹ (cons h₁ t▹₁) (cons h₂ t▹₂) = (h₁ ＝ h₂) × ▸ k (C▹ ⊛ t▹₁ ⊛ t▹₂)

Code : gStream k A → gStream k A → 𝒰 (level-of-type A)
Code = fix Code-body

Code-refl-body : ▹ k ((s : gStream k A) → Code s s) → (s : gStream k A) → Code s s
Code-refl-body C▹ (cons h t▹) =
  refl , λ α → transport (λ i → pfix Code-body (~ i) α (t▹ α) (t▹ α)) ((C▹ ⊛ t▹) α)

Code-refl : (s : gStream k A) → Code s s
Code-refl = fix Code-refl-body

decode : (s t : gStream k A) → Code s t → s ＝ t
decode (cons h₁ t▹₁) (cons h₂ t▹₂) (e , c) =
  ap² cons e (▹-ext λ α → decode (t▹₁ α) (t▹₂ α) (transport (λ i → pfix Code-body i α (t▹₁ α) (t▹₂ α)) (c α)))

encode : {c1 c2 : gStream k A} → c1 ＝ c2 → Code c1 c2
encode {c1} {c2} e = subst (Code c1) e (Code-refl c1)

-- TODO hlevel

cons-inj : {h₁ h₂ : A} {t▹₁ t▹₂ : ▹ k (gStream k A)}
         → cons h₁ t▹₁ ＝ cons h₂ t▹₂
         → (h₁ ＝ h₂) × (t▹₁ ＝ t▹₂)
cons-inj {t▹₁} {t▹₂} e =
  let ee = encode e in
  ee .fst , ▹-ext λ α → decode (t▹₁ α) (t▹₂ α) (transport (λ i → pfix Code-body i α (t▹₁ α) (t▹₂ α)) (ee .snd α))

cons-δ : A → gStream k A → gStream k A
cons-δ a s = cons a (next s)

headᵏ : gStream k A → A
headᵏ (cons x xs) = x

tail▹ᵏ : gStream k A → ▹ k (gStream k A)
tail▹ᵏ (cons x xs) = xs

stream-eq-coindᵏ : (R : gStream k A → gStream k A → 𝒰 ℓ′)
                 → (∀ s1 s2 → R s1 s2 → headᵏ s1 ＝ headᵏ s2)
                 → (∀ s1 s2 → R s1 s2 → ▸ k (R ⍉ (tail▹ᵏ s1) ⊛ (tail▹ᵏ s2)))
                 → ∀ s1 s2 → R s1 s2 → s1 ＝ s2
stream-eq-coindᵏ R hh ht = fix λ ih▹ → λ where
  (cons h1 t1▹) (cons h2 t2▹) r →
     ap² cons (hh (cons h1 t1▹) (cons h2 t2▹) r)
              (▹-ext (ih▹ ⊛ t1▹ ⊛▹ t2▹ ⊛▹ (ht (cons h1 t1▹) (cons h2 t2▹) r)))

uncons-eqᵏ : (s : gStream k A) → s ＝ cons (headᵏ s) (tail▹ᵏ s)
uncons-eqᵏ (cons x xs) = refl

-- coinductive streams

Stream : 𝒰 ℓ → 𝒰 ℓ
Stream A = ∀ k → gStream k A

consˢ : A → Stream A → Stream A
consˢ a s k = cons-δ a (s k)

headˢ : Stream A → A
headˢ s = headᵏ (s k0)

tailˢ : Stream A → Stream A
tailˢ s = force (tail▹ᵏ ∘ s)

head-consˢ : (a : A) → (as : Stream A)
           → headˢ (consˢ a as) ＝ a
head-consˢ a as = refl

tail-consˢ : (a : A) → (as : Stream A)
           → tailˢ (consˢ a as) ＝ as
tail-consˢ a as = fun-ext (delay-force as)

tail-eq : (s : Stream A) → ∀ k → tail▹ᵏ (s k) ＝ next (tailˢ s k)
tail-eq s k = sym $ ▹-ext (force-delay (tail▹ᵏ ∘ s) k)

consˢ-inj : {h₁ h₂ : A} {t₁ t₂ : Stream A}
          → consˢ h₁ t₁ ＝ consˢ h₂ t₂
          → (h₁ ＝ h₂) × (t₁ ＝ t₂)
consˢ-inj e =
  (cons-inj (happly e k0) .fst , fun-ext (force λ k → ▹-ap (cons-inj (happly e k) .snd)))

-- repeat

repeatᵏ : A → gStream k A
repeatᵏ a = fix (cons a)

repeatᵏ-eq : (a : A) → repeatᵏ {k = k} a ＝ cons a (next $ repeatᵏ a)
repeatᵏ-eq a = ap (cons a) (pfix (cons a))

repeatˢ : A → Stream A
repeatˢ a k = repeatᵏ a

repeatˢ-eq : (a : A) → repeatˢ a ＝ consˢ a (repeatˢ a)
repeatˢ-eq a = fun-ext λ k → repeatᵏ-eq a

-- map

mapᵏ-body : (A → B) → ▹ k (gStream k A → gStream k B) → gStream k A → gStream k B
mapᵏ-body f m▹ as = cons (f (headᵏ as)) (m▹ ⊛ (tail▹ᵏ as))

mapᵏ : (A → B) → gStream k A → gStream k B
mapᵏ f = fix (mapᵏ-body f)

mapᵏ-eq : (f : A → B) → (a : A) → (as▹ : ▹ k (gStream k A))
        → mapᵏ {k = k} f (cons a as▹) ＝ cons (f a) ((mapᵏ f) ⍉ as▹)
mapᵏ-eq f a as▹ =
  ap (cons (f a))
     (▹-ext (λ α → happly (pfix-ext (mapᵏ-body f) α) (as▹ α)))

mapᵏ-head : (f : A → B) → (s : gStream k A)
          → headᵏ (mapᵏ {k = k} f s) ＝ f (headᵏ s)
mapᵏ-head f s = refl

mapᵏ-tail : (f : A → B) → (s : gStream k A)
          → tail▹ᵏ (mapᵏ {k = k} f s) ＝ (mapᵏ f) ⍉ (tail▹ᵏ s)
mapᵏ-tail f (cons a as▹) = ap tail▹ᵏ (mapᵏ-eq f a as▹)

mapᵏ-fusion : (f : A → B) → (g : B → C) → (s : gStream k A)
            → mapᵏ g (mapᵏ f s) ＝ mapᵏ (g ∘ f) s
mapᵏ-fusion f g =
  fix λ prf▹ → λ where
    (cons a as▹) →
      mapᵏ g (mapᵏ f (cons a as▹))
        ＝⟨ ap (mapᵏ g) (mapᵏ-eq f a as▹) ⟩
      mapᵏ g (cons (f a) ((mapᵏ f) ⍉ as▹))
        ＝⟨ mapᵏ-eq g (f a) ((mapᵏ f) ⍉ as▹) ⟩
      cons (g (f a)) ((mapᵏ g) ⍉ ((mapᵏ f) ⍉ as▹))
        ＝⟨ ap (cons (g (f a))) (▹-ext (prf▹ ⊛ as▹)) ⟩
      cons (g (f a)) ((mapᵏ (g ∘ f)) ⍉ as▹)
        ＝⟨ sym (mapᵏ-eq (g ∘ f) a as▹) ⟩
      mapᵏ (g ∘ f) (cons a as▹)
        ∎

mapᵏ-repeat : (a : A) → (f : A → B) → mapᵏ {k = k} f (repeatᵏ a) ＝ repeatᵏ (f a)
mapᵏ-repeat a f = fix λ prf▹ →
  mapᵏ f (repeatᵏ a)
    ＝⟨ ap (mapᵏ f) (repeatᵏ-eq a)  ⟩
  mapᵏ f (cons a (λ α → repeatᵏ a))
    ＝⟨ mapᵏ-eq f a (λ x → cons a (dfix (cons a))) ⟩
  cons (f a) (λ α → mapᵏ f (repeatᵏ a))
    ＝⟨ ap (cons (f a)) (▹-ext prf▹) ⟩
  cons (f a) (λ α → repeatᵏ (f a))
    ＝⟨ ap (cons (f a)) (▹-ext λ α → sym (pfix-ext (cons (f a)) α)) ⟩
  cons (f a) (dfix (cons (f a)))
    ＝⟨⟩
  repeatᵏ (f a)
    ∎

mapˢ : (A → B) → Stream A → Stream B
mapˢ f s k = mapᵏ f (s k)

mapˢ-eq : (f : A → B)
        → (a : A) → (as : Stream A)
        → mapˢ f (consˢ a as) ＝ consˢ (f a) (mapˢ f as)
mapˢ-eq f a as = fun-ext λ k → mapᵏ-eq f a (next (as k))

mapˢ-head : (f : A → B) → (s : Stream A)
          → headˢ (mapˢ f s) ＝ f (headˢ s)
mapˢ-head f s = refl

mapˢ-fusion : (f : A → B) → (g : B → C) → (s : Stream A)
            → mapˢ g (mapˢ f s) ＝ mapˢ (g ∘ f) s
mapˢ-fusion f g s = fun-ext (mapᵏ-fusion f g ∘ s)

mapˢ-repeat : (a : A) → (f : A → B) → mapˢ f (repeatˢ a) ＝ repeatˢ (f a)
mapˢ-repeat a f = fun-ext λ k → mapᵏ-repeat a f

-- folding

foldrᵏ-body : (A → ▹ k B → B) → ▹ k (gStream k A → B) → gStream k A → B
foldrᵏ-body f f▹ s = f (headᵏ s) (f▹ ⊛ tail▹ᵏ s)

foldrᵏ : (A → ▹ k B → B) → gStream k A → B
foldrᵏ f = fix (foldrᵏ-body f)

scanl1ᵏ : (A → A → A) → gStream k A → gStream k A
scanl1ᵏ f = fix λ sc▹ s → cons (headᵏ s) ((mapᵏ (f (headᵏ s))) ⍉ (sc▹ ⊛ tail▹ᵏ s))

-- iterate

iterateᵏ-body : ▹ k (A → A) → ▹ k (A → gStream k A) → A → gStream k A
iterateᵏ-body f i▹ a = cons a (i▹ ⊛ (f ⊛ next a))

iterateᵏ : ▹ k (A → A) → A → gStream k A
iterateᵏ f = fix (iterateᵏ-body f)

tail-iterateᵏ : (f▹ : ▹ k (A → A)) → (x : A)
             → tail▹ᵏ (iterateᵏ f▹ x) ＝ (iterateᵏ f▹) ⍉ (f▹ ⊛ next x)
tail-iterateᵏ f x = ap (_⊛ (f ⊛ next x)) (pfix (iterateᵏ-body f))

iterateˢ : (A → A) → A → Stream A
iterateˢ f a k = iterateᵏ (next f) a

tail-iterate : (f : A → A) → (x : A)
             → tailˢ (iterateˢ f x) ＝ iterateˢ f (f x)
tail-iterate f x =
  fun-ext λ k →
    tailˢ (iterateˢ f x) k
      ＝⟨⟩
    force (λ k′ → tail▹ᵏ {k = k′} (iterateᵏ (next f) x)) k
      ＝⟨ ap (λ q → force q k) (fun-ext (λ k₁ → tail-iterateᵏ (next f) x)) ⟩
    force (λ k′ → next (iterateᵏ {k = k′} (next f) (f x))) k
      ＝⟨ delay-force (λ k′ → iterateᵏ {k = k′} (next f) (f x)) k ⟩
    iterateᵏ {k = k} (next f) (f x)
      ＝⟨⟩
    iterateˢ f (f x) k
      ∎

-- interleave

interleaveᵏ-body : ▹ k (gStream k A → ▹ k (gStream k A) → gStream k A) → gStream k A → ▹ k (gStream k A) → gStream k A
interleaveᵏ-body i▹ s t▹ = cons (headᵏ s) (i▹ ⊛ t▹ ⊛ next (tail▹ᵏ s))

interleaveᵏ : gStream k A → ▹ k (gStream k A) → gStream k A
interleaveᵏ = fix interleaveᵏ-body

interleaveˢ : Stream A → Stream A → Stream A
interleaveˢ s t k = interleaveᵏ (s k) (next (t k))

tail-interleaveᵏ : (s1 : gStream k A) → (s2▹ : ▹ k (gStream k A))
                 → tail▹ᵏ (interleaveᵏ s1 s2▹) ＝ (interleaveᵏ ⍉ s2▹ ⊛ next (tail▹ᵏ s1))
tail-interleaveᵏ s1 s2▹ = ap (λ q → q ⊛ s2▹ ⊛ next (tail▹ᵏ s1)) (pfix interleaveᵏ-body)

tail-interleaveˢ : (s1 s2 : Stream A)
                 → tailˢ (interleaveˢ s1 s2) ＝ interleaveˢ s2 (tailˢ s1)
tail-interleaveˢ s1 s2 =
  fun-ext λ k →
    tailˢ (interleaveˢ s1 s2) k
      ＝⟨⟩
    force (λ k₁ → tail▹ᵏ (interleaveᵏ (s1 k₁) (next (s2 k₁)))) k
      ＝⟨ ap (λ q → force q k) (fun-ext (λ k₁ → tail-interleaveᵏ (s1 k₁) (next (s2 k₁)))) ⟩
    force (λ k₁ → next (interleaveᵏ (s2 k₁) (tail▹ᵏ (s1 k₁)))) k
      ＝⟨ delay-force (λ k₁ → interleaveᵏ (s2 k₁) (tail▹ᵏ (s1 k₁))) k ⟩
    interleaveᵏ (s2 k) (tail▹ᵏ (s1 k))
      ＝⟨ ap (interleaveᵏ (s2 k)) (▹-ext (λ α → sym $ force-delay (λ k₁ → tail▹ᵏ (s1 k₁)) k α)) ⟩
    interleaveᵏ (s2 k) (next (tailˢ s1 k))
      ＝⟨⟩
    interleaveˢ s2 (tailˢ s1) k
      ∎

-- zipping

zipWithᵏ-body : (A → B → C)
              → ▹ k (gStream k A → gStream k B → gStream k C)
              → gStream k A → gStream k B → gStream k C
zipWithᵏ-body f zw▹ sa sb = cons (f (headᵏ sa) (headᵏ sb)) (zw▹ ⊛ tail▹ᵏ sa ⊛ tail▹ᵏ sb)

zipWithᵏ : (A → B → C) → gStream k A → gStream k B → gStream k C
zipWithᵏ f = fix (zipWithᵏ-body f)

zipWithᵏ-eq : (f : A → B → C)
            → ∀ a as▹ b bs▹
            → zipWithᵏ {k = k} f (cons a as▹) (cons b bs▹) ＝ cons (f a b) ((zipWithᵏ f) ⍉ as▹ ⊛ bs▹)
zipWithᵏ-eq f a as▹ b bs▹ =
  happly (happly (fix-path (zipWithᵏ-body f)) (cons a as▹)) (cons b bs▹)

zipWithᵏ-comm : (f : A → A → B)
              → (∀ a b → f a b ＝ f b a)
              → ∀ s t → zipWithᵏ {k = k} f s t ＝ zipWithᵏ f t s
zipWithᵏ-comm f fc = fix λ ih▹ → λ where
  (cons x s▹) (cons y t▹) → zipWithᵏ-eq f x s▹ y t▹
                          ∙ ap² cons (fc x y) (▹-ext λ α → ih▹ α (s▹ α) (t▹ α))
                          ∙ sym (zipWithᵏ-eq f y t▹ x s▹)

zipᵏ : gStream k A → gStream k B → gStream k (A × B)
zipᵏ = zipWithᵏ (_,_)

zipWithˢ : (A → B → C) → Stream A → Stream B → Stream C
zipWithˢ f sa sb k = zipWithᵏ f (sa k) (sb k)

zipWithˢ-comm : (f : A → A → B)
              → (∀ a b → f a b ＝ f b a)
              → ∀ s t → zipWithˢ f s t ＝ zipWithˢ f t s
zipWithˢ-comm f fc s t = fun-ext λ k → zipWithᵏ-comm f fc (s k) (t k)

zipˢ : Stream A → Stream B → Stream (A × B)
zipˢ = zipWithˢ (_,_)

-- indexing

nthˢ : ℕ → Stream A → A
nthˢ  zero   s = headˢ s
nthˢ (suc n) s = nthˢ n (tailˢ s)

takeˢ : ℕ → Stream A → List A
takeˢ  zero   s = []
takeˢ (suc n) s = headˢ s ∷ takeˢ n (tailˢ s)

dropˢ : ℕ → Stream A → Stream A
dropˢ zero    s = s
dropˢ (suc n) s = dropˢ n (tailˢ s)

-- "every other" function aka odds

eoᵏ-body : ▹ k (Stream A → gStream k A) → Stream A → gStream k A
eoᵏ-body eo▹ s = cons (headˢ s) (eo▹ ⊛ next (tailˢ (tailˢ s)))

eoᵏ : Stream A → gStream k A
eoᵏ = fix eoᵏ-body

eo : Stream A → Stream A
eo s k = eoᵏ s

eoᵏ-iterate : (f : A → A) → (x : A)
            → eoᵏ {k = k} (iterateˢ f x) ＝ iterateᵏ (next (f ∘ f)) x
eoᵏ-iterate {k} f =
  fix {k = k} λ prf▹ x →
    eoᵏ {k = k} (iterateˢ f x)
      ＝⟨⟩
    cons x (dfix eoᵏ-body ⊛ next (tailˢ (tailˢ (iterateˢ f x))))
      ＝⟨ ap (λ q → cons x (q ⊛ next (tailˢ (tailˢ (iterateˢ f x))))) (pfix eoᵏ-body) ⟩
    cons x (next (eoᵏ (tailˢ (tailˢ (iterateˢ f x)))))
      ＝⟨ ap (λ q → cons x (next (eoᵏ (tailˢ q)))) (tail-iterate f x) ⟩
    cons x (next (eoᵏ (tailˢ (iterateˢ f (f x)))))
      ＝⟨ ap (λ q → cons x (next (eoᵏ q))) (tail-iterate f (f x)) ⟩
    cons x (next (eoᵏ (iterateˢ f (f (f x)))))
      ＝⟨ ap (cons x) (▹-ext (prf▹ ⊛ (next (f (f x))))) ⟩
    cons x (next (iterateᵏ (next (f ∘ f)) (f (f x))))
      ＝⟨ ap (λ q → cons x (q ⊛ next (f (f x)))) (sym $ pfix (iterateᵏ-body (next (f ∘ f)))) ⟩
    cons x (dfix (iterateᵏ-body (next (f ∘ f))) ⊛ (next (f (f x))))
      ＝⟨⟩
    iterateᵏ (next (f ∘ f)) x
      ∎

eo-iterate : (f : A → A) → (x : A)
           → eo (iterateˢ f x) ＝ iterateˢ (f ∘ f) x
eo-iterate f x = fun-ext λ k → eoᵏ-iterate f x

head-eoᵏ : (s : Stream A)
         → headᵏ {k = k} (eoᵏ s) ＝ headˢ s
head-eoᵏ s = refl

tail-eoᵏ : (s : Stream A)
         → tail▹ᵏ {k = k} (eoᵏ s) ＝ next (eoᵏ (tailˢ (tailˢ s)))
tail-eoᵏ {k} s = ap (_⊛ next (tailˢ (tailˢ s))) (pfix eoᵏ-body)

head-eoˢ : (s : Stream A)
         → headˢ (eo s) ＝ headˢ s
head-eoˢ s = refl

tail-eoˢ : (s : Stream A)
         → tailˢ (eo s) ＝ eo (tailˢ (tailˢ s))
tail-eoˢ s = fun-ext λ k →
  tailˢ (eo s) k
    ＝⟨⟩
  force (λ k₁ → tail▹ᵏ (eoᵏ {k = k₁} s)) k
    ＝⟨ ap (λ q → force q k) (fun-ext (λ k₁ → tail-eoᵏ s)) ⟩
  force (λ k₁ → next (eoᵏ {k = k₁} (tailˢ (tailˢ s)))) k
    ＝⟨ delay-force (λ k₁ → eoᵏ {k = k₁} (tailˢ (tailˢ s))) k  ⟩
  eoᵏ {k = k} (tailˢ (tailˢ s))
    ＝⟨⟩
  eo (tailˢ (tailˢ s)) k
    ∎

evens : Stream A → Stream A
evens s = eo (tailˢ s)

head-evens : (s : Stream A)
           → headˢ (evens s) ＝ headˢ (tailˢ s)
head-evens s = refl

tail-evens : (s : Stream A)
           → tailˢ (evens s) ＝ evens (tailˢ (tailˢ s))
tail-evens s = tail-eoˢ (tailˢ s)

-- diagonal function

diagauxᵏ : (Stream A → Stream A) → gStream k (Stream A) → gStream k A
diagauxᵏ = fix (λ d▹ f s → cons ((headˢ ∘ f) (headᵏ s)) (d▹ ⊛ next (f ∘ tailˢ) ⊛ tail▹ᵏ s))

diagᵏ : gStream k (Stream A) → gStream k A
diagᵏ = diagauxᵏ id

diag : Stream (Stream A) → Stream A
diag x k = diagᵏ (x k)

-- natural numbers

natsᵏ-body : ▹ k (gStream k ℕ) → gStream k ℕ
natsᵏ-body nats▹ = cons 0 ((mapᵏ suc) ⍉ nats▹)

natsᵏ : gStream k ℕ
natsᵏ = fix natsᵏ-body

natsᵏ-tail : tail▹ᵏ {k = k} natsᵏ ＝ next (mapᵏ suc natsᵏ)
natsᵏ-tail = ap tail▹ᵏ (fix-path natsᵏ-body)

nats : Stream ℕ
nats k = natsᵏ

nats-tail : tailˢ nats ＝ mapˢ suc nats
nats-tail = fun-ext λ k →
  tailˢ nats k
    ＝⟨⟩
  force (λ k′ → tail▹ᵏ natsᵏ) k
    ＝⟨ ap (λ q → force q k) (fun-ext (λ k′ → natsᵏ-tail)) ⟩
  force (λ k′ α → mapᵏ {k = k′} suc natsᵏ) k
    ＝⟨ delay-force (λ k′ → mapᵏ suc natsᵏ) k ⟩
  mapᵏ suc natsᵏ
    ＝⟨⟩
  mapˢ suc nats k
    ∎

nats-1 : headˢ (tailˢ nats) ＝ 1
nats-1 = ap headˢ nats-tail

-- Fibonacci numbers

fibᵏ : gStream k ℕ
fibᵏ = fix λ fib▹ → cons 0 ((λ s → cons 1 ((zipWithᵏ _+_ s) ⍉ (tail▹ᵏ s))) ⍉ fib▹)

fibˢ : Stream ℕ
fibˢ k = fibᵏ

-- prime numbers

primesᵏ : gStream k ℕ
primesᵏ = fix λ pr▹ → cons 2 ((mapᵏ suc ∘ scanl1ᵏ _·_) ⍉ pr▹)

primesˢ : Stream ℕ
primesˢ k = primesᵏ

-- paperfolding / dragon curve sequence

toggleᵏ : gStream k Bool
toggleᵏ = fix λ t▹ → cons true (next (cons false t▹))

toggleˢ : Stream Bool
toggleˢ k = toggleᵏ

paperfoldsᵏ : gStream k Bool
paperfoldsᵏ = fix (interleaveᵏ toggleᵏ)

paperfoldsˢ : Stream Bool
paperfoldsˢ k = paperfoldsᵏ

-- Thue-Morse sequence

hᵏ-body : ▹ k (gStream k Bool → gStream k Bool) → gStream k Bool → gStream k Bool
hᵏ-body h▹ s with (headᵏ s)
... | false = cons false (next (cons true  (h▹ ⊛ tail▹ᵏ s)))
... | true  = cons true  (next (cons false (h▹ ⊛ tail▹ᵏ s)))

hᵏ : gStream k Bool → gStream k Bool
hᵏ = fix hᵏ-body

thuemorseᵏ : gStream k Bool
thuemorseᵏ = fix λ t▹ → cons false ((λ tm → cons true (hᵏ ⍉ (tail▹ᵏ (hᵏ tm)))) ⍉ t▹)

thuemorseˢ : Stream Bool
thuemorseˢ k = thuemorseᵏ

-- Pascal coefficients

pascal-nextᵏ : gStream k ℕ → gStream k ℕ
pascal-nextᵏ xs = fix λ p▹ → cons 1 ((zipWithᵏ _+_) ⍉ (tail▹ᵏ xs) ⊛ p▹)

pascal-nextˢ : Stream ℕ → Stream ℕ
pascal-nextˢ s k = pascal-nextᵏ (s k)

pascalᵏ : gStream k (Stream ℕ)
pascalᵏ = fix λ p▹ → cons (repeatˢ 1) ((mapᵏ pascal-nextˢ) ⍉ p▹)

pascalˢ : Stream (Stream ℕ)
pascalˢ k = pascalᵏ
