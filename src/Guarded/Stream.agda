{-# OPTIONS --guarded #-}
module Guarded.Stream where

open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.List
open import LaterG

private variable
  A B C : 𝒰

-- guarded streams

data Stream (A : 𝒰) : 𝒰 where
  cons : (x : A) (xs : ▹ Stream A) → Stream A

headˢ : Stream A → A
headˢ (cons x xs) = x

tail▹ˢ : Stream A → ▹ Stream A
tail▹ˢ (cons x xs) = xs

uncons-eq : (s : Stream A) → s ＝ cons (headˢ s) (tail▹ˢ s)
uncons-eq (cons x xs) = refl

-- repeat

repeatˢ : A → Stream A
repeatˢ a = fix (cons a)

repeatˢ-eq : (a : A) → repeatˢ a ＝ cons a (λ α → repeatˢ a)
repeatˢ-eq a = ap (cons a) (pfix (cons a))

-- map

mapˢ-body : (A → B) → ▹ (Stream A → Stream B) → Stream A → Stream B
mapˢ-body f m▹ as = cons (f (headˢ as)) (m▹ ⊛ (tail▹ˢ as))

mapˢ : (A → B) → Stream A → Stream B
mapˢ f = fix (mapˢ-body f)

mapˢ-eq : (f : A → B)
        → ∀ a as → mapˢ f (cons a as) ＝ cons (f a) (λ α → mapˢ f (as α))
mapˢ-eq f a as =
  ap (cons (f a))
     (▹-ext (λ α → happly (pfix-ext (mapˢ-body f) α) (as α)))

mapˢ-head : (f : A → B) → (s : Stream A)
          → headˢ (mapˢ f s) ＝ f (headˢ s)
mapˢ-head f s = refl

mapˢ-tail : (f : A → B) → (s : Stream A)
          → tail▹ˢ (mapˢ f s) ＝ ▹map (mapˢ f) (tail▹ˢ s)
mapˢ-tail f (cons a as▹) = ap tail▹ˢ (mapˢ-eq f a as▹)

mapˢ-repeat : (a : A) → (f : A → B) → mapˢ f (repeatˢ a) ＝ repeatˢ (f a)
mapˢ-repeat a f = fix λ prf▹ →
  mapˢ f (repeatˢ a)
    ＝⟨ ap (mapˢ f) (repeatˢ-eq a)  ⟩
  mapˢ f (cons a (λ α → repeatˢ a))
    ＝⟨ mapˢ-eq f a (λ x → cons a (dfix (cons a))) ⟩
  cons (f a) (λ α → mapˢ f (repeatˢ a))
    ＝⟨ ap (cons (f a)) (▹-ext prf▹) ⟩
  cons (f a) (λ α → repeatˢ (f a))
    ＝⟨ ap (cons (f a)) (▹-ext λ α → sym (pfix-ext (cons (f a)) α)) ⟩
  cons (f a) (λ α → dfix (cons (f a)) α)
    ＝⟨⟩
  repeatˢ (f a)
    ∎

-- folding

foldrˢ-body : (A → ▹ B → B) → ▹ (Stream A → B) → Stream A → B
foldrˢ-body f f▹ s = f (headˢ s) (f▹ ⊛ tail▹ˢ s)

foldrˢ : (A → ▹ B → B) → Stream A → B
foldrˢ f = fix (foldrˢ-body f)

scanl1ˢ : (A → A → A) → Stream A → Stream A
scanl1ˢ f = fix λ sc▹ s → cons (headˢ s) (▹map (mapˢ (f (headˢ s))) (sc▹ ⊛ tail▹ˢ s))

-- iterate

iterateˢ : ▹ (A → A) → A → Stream A
iterateˢ f = fix λ i▹ a → cons a (i▹ ⊛ (f ⊛ next a))

-- interleave

interleaveˢ : Stream A → ▹ Stream A → Stream A
interleaveˢ = fix λ i▹ s t▹ → cons (headˢ s) (i▹ ⊛ t▹ ⊛ next (tail▹ˢ s))

-- zipping

zipWithˢ : (A → B → C) → Stream A → Stream B → Stream C
zipWithˢ f = fix (λ zw▹ sa sb → cons (f (headˢ sa) (headˢ sb)) (zw▹ ⊛ tail▹ˢ sa ⊛ tail▹ˢ sb))

-- natural numbers

natsˢ : Stream ℕ
natsˢ = fix (λ nats▹ → cons 0 (▹map (mapˢ suc) nats▹))

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
pascal-nextˢ xs = fix λ p▹ → cons 1 (next (zipWithˢ _+_) ⊛ tail▹ˢ xs ⊛ p▹)

pascalˢ : Stream (Stream ℕ)
pascalˢ = fix λ p▹ → cons (repeatˢ 1) (▹map (mapˢ pascal-nextˢ) p▹)
