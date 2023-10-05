{-# OPTIONS --guarded #-}
module Clocked.Stream where

open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.List
open import Later

private variable
  A B C : 𝒰
  k : Cl

-- clocked streams

data gStream (k : Cl) (A : 𝒰) : 𝒰 where
  cons : (x : A) (xs : ▹ k (gStream k A)) → gStream k A

headᵏ : gStream k A → A
headᵏ (cons x xs) = x

tail▹ᵏ : gStream k A → ▹ k (gStream k A)
tail▹ᵏ (cons x xs) = xs

uncons-eqᵏ : (s : gStream k A) → s ＝ cons (headᵏ s) (tail▹ᵏ s)
uncons-eqᵏ (cons x xs) = refl

Stream : 𝒰 → 𝒰
Stream A = ∀ k → gStream k A

consˢ : A → Stream A → Stream A
consˢ a str k = cons a (next (str k))

headˢ : Stream A → A
headˢ str = headᵏ (str k0)

tailˢ : Stream A → Stream A
tailˢ str = force λ k → tail▹ᵏ (str k)

head-consˢ : (a : A) → (as : Stream A)
           → headˢ (consˢ a as) ＝ a
head-consˢ a as = refl

tail-consˢ : (a : A) → (as : Stream A)
           → tailˢ (consˢ a as) ＝ as
tail-consˢ a as = fun-ext (delay-force as)

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
        → mapᵏ {k = k} f (cons a as▹) ＝ cons (f a) (λ α → mapᵏ f (as▹ α))
mapᵏ-eq f a as▹ =
  ap (cons (f a))
     (▹-ext (λ α → happly (pfix-ext (mapᵏ-body f) α) (as▹ α)))

mapᵏ-head : (f : A → B) → (s : gStream k A)
          → headᵏ (mapᵏ {k = k} f s) ＝ f (headᵏ s)
mapᵏ-head f s = refl

mapᵏ-tail : (f : A → B) → (s : gStream k A)
          → tail▹ᵏ (mapᵏ {k = k} f s) ＝ ▹map (mapᵏ f) (tail▹ᵏ s)
mapᵏ-tail f (cons a as▹) = ap tail▹ᵏ (mapᵏ-eq f a as▹)

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
  cons (f a) (λ α → dfix (cons (f a)) α)
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

mapˢ-repeat : (a : A) → (f : A → B) → mapˢ f (repeatˢ a) ＝ repeatˢ (f a)
mapˢ-repeat a f = fun-ext (λ k → mapᵏ-repeat a f)

-- folding

foldrᵏ-body : (A → ▹ k B → B) → ▹ k (gStream k A → B) → gStream k A → B
foldrᵏ-body f f▹ s = f (headᵏ s) (f▹ ⊛ tail▹ᵏ s)

foldrᵏ : (A → ▹ k B → B) → gStream k A → B
foldrᵏ f = fix (foldrᵏ-body f)

scanl1ᵏ : (A → A → A) → gStream k A → gStream k A
scanl1ᵏ f = fix λ sc▹ s → cons (headᵏ s) (▹map (mapᵏ (f (headᵏ s))) (sc▹ ⊛ tail▹ᵏ s))

-- iterate

iterateᵏ : ▹ k (A → A) → A → gStream k A
iterateᵏ f = fix λ i▹ a → cons a (i▹ ⊛ (f ⊛ next a))

iterateˢ : (A → A) → A → Stream A
iterateˢ f a k = iterateᵏ (next f) a

-- interleave

interleaveᵏ : gStream k A → ▹ k (gStream k A) → gStream k A
interleaveᵏ = fix λ i▹ s t▹ → cons (headᵏ s) (i▹ ⊛ t▹ ⊛ next (tail▹ᵏ s))

interleaveˢ : Stream A → Stream A → Stream A
interleaveˢ s t k = interleaveᵏ (s k) (next (t k))

-- zipping

zipWithᵏ : (A → B → C) → gStream k A → gStream k B → gStream k C
zipWithᵏ f = fix (λ zw▹ sa sb → cons (f (headᵏ sa) (headᵏ sb)) (zw▹ ⊛ tail▹ᵏ sa ⊛ tail▹ᵏ sb))

zipWithˢ : (A → B → C) → Stream A → Stream B → Stream C
zipWithˢ f sa sb k = zipWithᵏ f (sa k) (sb k)

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

-- "every other" function

eoᵏ : Stream A → gStream k A
eoᵏ = fix λ eo▹ s → cons (headˢ s) λ α → eo▹ α (tailˢ (tailˢ s))

eo : Stream A → Stream A
eo s k = eoᵏ s

-- diagonal function

diagauxᵏ : (Stream A → Stream A) → gStream k (Stream A) → gStream k A
diagauxᵏ = fix (λ d▹ f s → cons ((headˢ ∘ f) (headᵏ s)) (d▹ ⊛ next (f ∘ tailˢ) ⊛ tail▹ᵏ s))

diagᵏ : gStream k (Stream A) → gStream k A
diagᵏ = diagauxᵏ id

diag : Stream (Stream A) → Stream A
diag x k = diagᵏ (x k)

-- natural numbers

natsᵏ-body : ▹ k (gStream k ℕ) → gStream k ℕ
natsᵏ-body nats▹ = cons 0 (▹map (mapᵏ suc) nats▹)

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
fibᵏ = fix λ fib▹ → cons 0 (▹map (λ s → cons 1 (▹map (zipWithᵏ _+_ s) (tail▹ᵏ s))) fib▹)

fibˢ : Stream ℕ
fibˢ k = fibᵏ

-- prime numbers

primesᵏ : gStream k ℕ
primesᵏ = fix λ pr▹ → cons 2 (▹map (mapᵏ suc ∘ scanl1ᵏ _·_) pr▹)

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
thuemorseᵏ = fix λ t▹ → cons false (▹map (λ tm → cons true (▹map hᵏ (tail▹ᵏ (hᵏ tm)))) t▹)

thuemorseˢ : Stream Bool
thuemorseˢ k = thuemorseᵏ

-- Pascal coefficients

pascal-nextᵏ : gStream k ℕ → gStream k ℕ
pascal-nextᵏ xs = fix λ p▹ → cons 1 (next (zipWithᵏ _+_) ⊛ tail▹ᵏ xs ⊛ p▹)

pascal-nextˢ : Stream ℕ → Stream ℕ
pascal-nextˢ s k = pascal-nextᵏ (s k)

pascalᵏ : gStream k (Stream ℕ)
pascalᵏ = fix λ p▹ → cons (repeatˢ 1) (▹map (mapᵏ pascal-nextˢ) p▹)

pascalˢ : Stream (Stream ℕ)
pascalˢ k = pascalᵏ
