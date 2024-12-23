{-# OPTIONS --guarded #-}
module Guarded.StreamFix where

open import Prelude
open import Foundations.Transport
open import Data.Bool
open import Data.Nat
open import Data.List

open import LaterG

private variable
  A B C : 𝒰

-- guarded streams via fixpoint in the universe

StreamF : 𝒰 → ▹ 𝒰 → 𝒰
StreamF A S▹ = A × ▸ S▹

Stream : 𝒰 → 𝒰
Stream A = fix (StreamF A)

opaque
  Stream-path : Stream A ＝ StreamF A (next (Stream A))
  Stream-path {A} = fix-path (StreamF A)

  Stream⇉ : Stream A
           → StreamF A (next (Stream A))
  Stream⇉ = transport Stream-path

  ⇉Stream : StreamF A (next (Stream A))
           → Stream A
  ⇉Stream = transport (Stream-path ⁻¹)

consˢ : A → ▹ Stream A → Stream A
consˢ x xs▹ = ⇉Stream (x , xs▹)

unconsˢ : Stream A → A × ▹ Stream A
unconsˢ = Stream⇉

headˢ : Stream A → A
headˢ = fst ∘ unconsˢ

tail▹ˢ : Stream A → ▹ Stream A
tail▹ˢ = snd ∘ unconsˢ

opaque
  unfolding Stream⇉ ⇉Stream
  
  uncons-eq : (s : Stream A) → s ＝ consˢ (headˢ s) (tail▹ˢ s)
  uncons-eq {A} s = transport⁻-transport Stream-path s ⁻¹

  head-cons : (a : A) (as▹ : ▹ Stream A) → headˢ (consˢ a as▹) ＝ a
  head-cons {A} a as▹ = transport⁻-transport refl a 

  tail-cons : (a : A) (as▹ : ▹ Stream A) → tail▹ˢ (consˢ a as▹) ＝ as▹
  tail-cons {A} a as▹ = transport⁻-transport (λ i → ▸ pfix (StreamF A) (~ i)) as▹

-- repeat

repeatˢ : A → Stream A
repeatˢ a = fix (consˢ a)

repeatˢ-eq : (a : A) → repeatˢ a ＝ consˢ a (λ α → repeatˢ a)
repeatˢ-eq a = ap (consˢ a) (pfix (consˢ a))

-- map

mapˢ-body : (A → B) → ▹ (Stream A → Stream B) → Stream A → Stream B
mapˢ-body f m▹ as = consˢ (f (headˢ as)) (m▹ ⊛ (tail▹ˢ as))

mapˢ : (A → B) → Stream A → Stream B
mapˢ f = fix (mapˢ-body f)

mapˢ-eq : (f : A → B) → (a : A) → (as▹ : ▹ Stream A)
        → mapˢ f (consˢ a as▹) ＝ consˢ (f a) ((mapˢ f) ⍉ as▹)
mapˢ-eq {A} f a as▹ =
    happly (fix-path (mapˢ-body f)) (consˢ a as▹)
  ∙ ap² consˢ
      (ap f (head-cons a as▹))
      (ap (mapˢ f ⍉_) (tail-cons a as▹))

mapˢ-head : (f : A → B) → (s : Stream A)
          → headˢ (mapˢ f s) ＝ f (headˢ s)
mapˢ-head f s =
    ap headˢ (happly (fix-path (mapˢ-body f)) s) 
  ∙ head-cons (f (headˢ s)) ((mapˢ f) ⍉ (tail▹ˢ s))

mapˢ-tail : (f : A → B) → (s : Stream A)
          → tail▹ˢ (mapˢ f s) ＝ (mapˢ f) ⍉ (tail▹ˢ s)
mapˢ-tail f s =
    ap (λ q → tail▹ˢ (mapˢ f q)) (uncons-eq s)
  ∙ ap tail▹ˢ (mapˢ-eq f (headˢ s) (tail▹ˢ s))
  ∙ tail-cons (f (headˢ s)) ((mapˢ f) ⍉ (tail▹ˢ s))

mapˢ-fusion : (f : A → B) → (g : B → C) → (s : Stream A)
            → mapˢ g (mapˢ f s) ＝ mapˢ (g ∘ f) s
mapˢ-fusion f g =
  fix λ prf▹ s → let (a , as▹) = unconsˢ s in
    mapˢ g (mapˢ f s)
      =⟨ ap (mapˢ g ∘ mapˢ f) (uncons-eq s) ⟩
    mapˢ g (mapˢ f (consˢ a as▹))
      =⟨ ap (mapˢ g) (mapˢ-eq f a as▹) ⟩
    mapˢ g (consˢ (f a) ((mapˢ f) ⍉ as▹))
      =⟨ mapˢ-eq g (f a) ((mapˢ f) ⍉ as▹) ⟩
    consˢ (g (f a)) ((mapˢ g) ⍉ ((mapˢ f) ⍉ as▹))
      =⟨ ap (consˢ (g (f a))) (▹-ext (prf▹ ⊛ as▹)) ⟩
    consˢ (g (f a)) ((mapˢ (g ∘ f)) ⍉ as▹)
      =⟨ sym (mapˢ-eq (g ∘ f) a as▹) ⟩
    mapˢ (g ∘ f) (consˢ a as▹)
      =⟨ ap (mapˢ (g ∘ f)) (sym (uncons-eq s)) ⟩
    mapˢ (g ∘ f) s
      ∎

mapˢ-repeat : (a : A) → (f : A → B) → mapˢ f (repeatˢ a) ＝ repeatˢ (f a)
mapˢ-repeat a f = fix λ prf▹ →
  mapˢ f (repeatˢ a)
    =⟨ ap (mapˢ f) (repeatˢ-eq a)  ⟩
  mapˢ f (consˢ a (λ α → repeatˢ a))
    =⟨ mapˢ-eq f a (λ x → consˢ a (dfix (consˢ a))) ⟩
  consˢ (f a) (λ α → mapˢ f (repeatˢ a))
    =⟨ ap (consˢ (f a)) (▹-ext prf▹) ⟩
  consˢ (f a) (λ α → repeatˢ (f a))
    =⟨ ap (consˢ (f a)) (▹-ext λ α → sym (pfix-ext (consˢ (f a)) α)) ⟩
  consˢ (f a) (λ α → dfix (consˢ (f a)) α)
    =⟨⟩
  repeatˢ (f a)
    ∎

-- lift a predicate to a stream

Allˢ-body : (A → 𝒰) → ▹ (Stream A → 𝒰) → Stream A → 𝒰
Allˢ-body P P▹ s = P (headˢ s) × ▸ (P▹ ⊛ (tail▹ˢ s))

Allˢ : (A → 𝒰) → Stream A → 𝒰
Allˢ P = fix (Allˢ-body P)

Allˢ-cons : ∀ {a as▹} {P : A → 𝒰} → P a → ▹[ α ] (Allˢ P (as▹ α)) → Allˢ P (consˢ a as▹)
Allˢ-cons {a} {as▹} {P} pa ps▹ =
    subst P (head-cons a as▹ ⁻¹) pa
  , (subst (λ q → ▸ (dfix (Allˢ-body P) ⊛ q)) ((tail-cons a as▹) ⁻¹) $
     subst (λ q → ▸ (q ⊛ as▹)) ((pfix (Allˢ-body P)) ⁻¹) $
     ps▹)

Allˢ-match : ∀ {a as▹} {P : A → 𝒰} → Allˢ P (consˢ a as▹) → P a × (▹[ α ] (Allˢ P (as▹ α)))
Allˢ-match {a} {as▹} {P} (pa , ps▸) =
    subst P (head-cons a as▹) pa
  , (subst (λ q → ▸ (q ⊛ as▹)) (pfix (Allˢ-body P)) $
     subst (λ q → ▸ (dfix (Allˢ-body P) ⊛ q)) (tail-cons a as▹) $
     ps▸)

Allˢ-map : {P Q : A → 𝒰} {f : A → A}
         → ({x : A} → P x → Q (f x))
         → (s : Stream A) → Allˢ P s → Allˢ Q (mapˢ f s)
Allˢ-map {P} {Q} {f} pq =
  fix λ prf▹ s ps →
    let pa , pas▹ = Allˢ-match {P = P} (subst (Allˢ P) (uncons-eq s) ps) in
    subst (Allˢ Q ∘ mapˢ f) ((uncons-eq s) ⁻¹) $
    subst (Allˢ Q) ((mapˢ-eq f (headˢ s) (tail▹ˢ s)) ⁻¹) $
    Allˢ-cons {P = Q} (pq pa) ((λ α → prf▹ α (tail▹ˢ s α) (pas▹ α)))
  
-- folding

foldrˢ-body : (A → ▹ B → B) → ▹ (Stream A → B) → Stream A → B
foldrˢ-body f f▹ s = f (headˢ s) (f▹ ⊛ tail▹ˢ s)

foldrˢ : (A → ▹ B → B) → Stream A → B
foldrˢ f = fix (foldrˢ-body f)

scanl1ˢ-body : (A → A → A) → ▹ (Stream A → Stream A) → Stream A → Stream A
scanl1ˢ-body f sc▹ s = consˢ (headˢ s) ((mapˢ (f (headˢ s))) ⍉ (sc▹ ⊛ tail▹ˢ s))

scanl1ˢ : (A → A → A) → Stream A → Stream A
scanl1ˢ f = fix (scanl1ˢ-body f)

-- iterate

iterateˢ-body : ▹ (A → A) → ▹ (A → Stream A) → A → Stream A
iterateˢ-body f i▹ a = consˢ a (i▹ ⊛ (f ⊛ next a))

iterateˢ : ▹ (A → A) → A → Stream A
iterateˢ f = fix (iterateˢ-body f)

tail-iterateˢ : (f▹ : ▹ (A → A)) → (x : A)
              → tail▹ˢ (iterateˢ f▹ x) ＝ (iterateˢ f▹) ⍉ (f▹ ⊛ next x)
tail-iterateˢ f x =
  tail-cons x (dfix (iterateˢ-body f) ⊛ (f ⊛ next x))
  ∙ ap (_⊛ (f ⊛ next x)) (pfix (iterateˢ-body f))

-- interleave

interleaveˢ : Stream A → ▹ Stream A → Stream A
interleaveˢ = fix λ i▹ s t▹ → consˢ (headˢ s) (i▹ ⊛ t▹ ⊛ next (tail▹ˢ s))

-- zipping

zipWithˢ-body : (A → B → C) → ▹ (Stream A → Stream B → Stream C) → Stream A → Stream B → Stream C
zipWithˢ-body f zw▹ sa sb = consˢ (f (headˢ sa) (headˢ sb)) (zw▹ ⊛ tail▹ˢ sa ⊛ tail▹ˢ sb)

zipWithˢ : (A → B → C) → Stream A → Stream B → Stream C
zipWithˢ f = fix (zipWithˢ-body f)

-- comonad structure

extractˢ : Stream A → A
extractˢ = headˢ

-- aka tails
duplicateˢ-body : ▹ (Stream A → Stream (Stream A)) → Stream A → Stream (Stream A)
duplicateˢ-body d▹ s = consˢ s (d▹ ⊛ tail▹ˢ s)

duplicateˢ : Stream A → Stream (Stream A)
duplicateˢ = fix duplicateˢ-body

extendˢ-body : (Stream A → B) → ▹ (Stream A → Stream B) → Stream A → Stream B
extendˢ-body f e▹ s = consˢ (f s) (e▹ ⊛ tail▹ˢ s)

extendˢ : (Stream A → B) → Stream A → Stream B
extendˢ f = fix (extendˢ-body f)

extract-duplicate : (s : Stream A) → extractˢ (duplicateˢ s) ＝ s
extract-duplicate s =
  extractˢ (duplicateˢ s)
    =⟨ ap (λ q → extractˢ (q s)) (fix-path duplicateˢ-body) ⟩
  extractˢ (duplicateˢ-body (next duplicateˢ) s)
    =⟨ head-cons s (duplicateˢ ⍉ tail▹ˢ s) ⟩
  s
    ∎

map-extract-duplicate : (s : Stream A) → mapˢ extractˢ (duplicateˢ s) ＝ s
map-extract-duplicate = fix λ ih▹ → λ where
  s →
    mapˢ extractˢ (duplicateˢ s)
      =⟨ ap (λ q → mapˢ extractˢ (q s)) (fix-path duplicateˢ-body) ⟩
    mapˢ extractˢ (duplicateˢ-body (next duplicateˢ) s)
      =⟨ mapˢ-eq extractˢ s (duplicateˢ ⍉ tail▹ˢ s) ⟩
    consˢ (headˢ s) (mapˢ extractˢ ⍉ (duplicateˢ ⍉ tail▹ˢ s))
      =⟨ ap (consˢ (headˢ s)) (▹-ext (ih▹ ⊛ tail▹ˢ s)) ⟩
    consˢ (headˢ s) (tail▹ˢ s)
      =⟨ uncons-eq s ⟨
    s
      ∎

duplicate-duplicate : (s : Stream A) → duplicateˢ (duplicateˢ s) ＝ mapˢ duplicateˢ (duplicateˢ s)
duplicate-duplicate = fix λ ih▹ → λ where
  s →
    duplicateˢ (duplicateˢ s)
      =⟨ ap (λ q → duplicateˢ (q s)) (fix-path duplicateˢ-body) ⟩
    duplicateˢ (duplicateˢ-body (next duplicateˢ) s)
      =⟨ ap (λ q → q (duplicateˢ-body (next duplicateˢ) s)) (fix-path duplicateˢ-body) ⟩
    duplicateˢ-body (next duplicateˢ) (duplicateˢ-body (next duplicateˢ) s)
      =⟨⟩
    consˢ (consˢ s (duplicateˢ ⍉ tail▹ˢ s)) (duplicateˢ ⍉ ⌜ tail▹ˢ (consˢ s (duplicateˢ ⍉ tail▹ˢ s)) ⌝)
      =⟨ ap! (tail-cons s (duplicateˢ ⍉ tail▹ˢ s)) ⟩
    consˢ (consˢ s (duplicateˢ ⍉ tail▹ˢ s)) (duplicateˢ ⍉ (duplicateˢ ⍉ tail▹ˢ s))
      =⟨ ap (consˢ (consˢ s (duplicateˢ ⍉ tail▹ˢ s))) (▹-ext λ α → ih▹ α (tail▹ˢ s α) ∙ ap (λ q → mapˢ q (duplicateˢ (tail▹ˢ s α))) (fix-path duplicateˢ-body)) ⟩
    consˢ (consˢ s (duplicateˢ ⍉ tail▹ˢ s)) (mapˢ (duplicateˢ-body (next duplicateˢ)) ⍉ (duplicateˢ ⍉ tail▹ˢ s))
      =⟨ mapˢ-eq (duplicateˢ-body (next duplicateˢ)) s (duplicateˢ ⍉ tail▹ˢ s) ⟨
    mapˢ (duplicateˢ-body (next duplicateˢ)) (consˢ s (duplicateˢ ⍉ tail▹ˢ s))
      =⟨⟩
    mapˢ (duplicateˢ-body (next duplicateˢ)) (duplicateˢ-body (next duplicateˢ) s)
      =⟨ ap (λ q → mapˢ q (duplicateˢ-body (next duplicateˢ) s)) (fix-path duplicateˢ-body) ⟨
    mapˢ duplicateˢ (duplicateˢ-body (next duplicateˢ) s)
      =⟨ ap (λ q → mapˢ duplicateˢ (q s)) (fix-path duplicateˢ-body) ⟨
    mapˢ duplicateˢ (duplicateˢ s)
      ∎

-- natural numbers

natsˢ-body : ▹ Stream ℕ → Stream ℕ
natsˢ-body nats▹ = consˢ 0 ((mapˢ suc) ⍉ nats▹)

natsˢ : Stream ℕ
natsˢ = fix natsˢ-body

natsˢ-tail : tail▹ˢ natsˢ ＝ next (mapˢ suc natsˢ)
natsˢ-tail =
  ap tail▹ˢ (fix-path natsˢ-body)
  ∙ tail-cons 0 (λ α → mapˢ suc (next (fix natsˢ-body) α))

-- Fibonacci numbers

fibˢ-body : ▹ Stream ℕ → Stream ℕ
fibˢ-body fib▹ = consˢ 0 ((λ s → consˢ 1 ((zipWithˢ _+_ s) ⍉ (tail▹ˢ s))) ⍉ fib▹)

fibˢ : Stream ℕ
fibˢ = fix fibˢ-body

-- prime numbers

primesˢ-body : ▹ Stream ℕ → Stream ℕ
primesˢ-body pr▹ = consˢ 2 ((mapˢ suc ∘ scanl1ˢ _·_) ⍉ pr▹)

primesˢ : Stream ℕ
primesˢ = fix primesˢ-body

-- paperfolding / dragon curve sequence

toggleˢ : Stream Bool
toggleˢ = fix λ t▹ → consˢ true (next (consˢ false t▹))

paperfoldsˢ : Stream Bool
paperfoldsˢ = fix (interleaveˢ toggleˢ)

-- Thue-Morse sequence

hˢ-body : ▹ (Stream Bool → Stream Bool) → Stream Bool → Stream Bool
hˢ-body h▹ s with (headˢ s)
... | false = consˢ false (next (consˢ true  (h▹ ⊛ tail▹ˢ s)))
... | true  = consˢ true  (next (consˢ false (h▹ ⊛ tail▹ˢ s)))

hˢ : Stream Bool → Stream Bool
hˢ = fix hˢ-body

thuemorseˢ : Stream Bool
thuemorseˢ = fix λ t▹ → consˢ false ((λ tm → consˢ true (hˢ ⍉ (tail▹ˢ (hˢ tm)))) ⍉ t▹)

-- Pascal coefficients

pascal-nextˢ : Stream ℕ → Stream ℕ
pascal-nextˢ xs = fix λ p▹ → consˢ 1 ((zipWithˢ _+_) ⍉ (tail▹ˢ xs) ⊛ p▹)

pascalˢ : Stream (Stream ℕ)
pascalˢ = fix λ p▹ → consˢ (repeatˢ 1) ((mapˢ pascal-nextˢ) ⍉ p▹)
