{-# OPTIONS --guarded #-}
module Clocked.StreamFix where

open import Prelude
open import Foundations.Transport
open import Data.Bool
open import Data.Nat
open import Data.List
open import Later

private variable
  A B C : 𝒰
  k : Cl

-- clocked streams via fixpoint in the universe

gStream-body : (k : Cl) → 𝒰 → ▹ k 𝒰 → 𝒰
gStream-body k A S▹ = A × ▸ k S▹

gStream : Cl → 𝒰 → 𝒰
gStream k A = fix (gStream-body k A)

consᵏ : A → ▹ k (gStream k A) → gStream k A
consᵏ {A} {k} x xs▹ = (x , subst (▸ k) (sym (pfix (gStream-body k A))) xs▹)

headᵏ : gStream k A → A
headᵏ (x , xs▹) = x

tail▹ᵏ : gStream k A → ▹ k (gStream k A)
tail▹ᵏ {k} {A} (x , xs▹) = subst (▸ k) (pfix (gStream-body k A)) xs▹

uncons-eqᵏ : (s : gStream k A) → s ＝ consᵏ (headᵏ s) (tail▹ᵏ s)
uncons-eqᵏ {k} {A} (a , as▹) =
  ap (λ q → (a , q)) $ sym $ transport⁻-transport (λ i → ▸ k (pfix (gStream-body k A) i)) as▹

head-consᵏ : (a : A) → (as▹ : ▹ k (gStream k A))
           → headᵏ (consᵏ a as▹) ＝ a
head-consᵏ a as▹ = refl

tail-consᵏ : (a : A) → (as▹ : ▹ k (gStream k A))
           → tail▹ᵏ (consᵏ a as▹) ＝ as▹
tail-consᵏ {A} {k} a as▹ = transport⁻-transport (λ i → ▸ k (pfix (gStream-body k A) (~ i))) as▹

Stream : 𝒰 → 𝒰
Stream A = ∀ k → gStream k A

consˢ : A → Stream A → Stream A
consˢ a str k = consᵏ a (next (str k))

headˢ : Stream A → A
headˢ str = headᵏ (str k0)

tailˢ : Stream A → Stream A
tailˢ str = force λ k → tail▹ᵏ (str k)

head-consˢ : (a : A) → (as : Stream A)
           → headˢ (consˢ a as) ＝ a
head-consˢ a as = refl

tail-consˢ : (a : A) → (as : Stream A)
           → tailˢ (consˢ a as) ＝ as
tail-consˢ a as =
  fun-ext (λ k → ap (λ q → force q k) (fun-ext (λ k₁ → tail-consᵏ a (next (as k₁))))
                 ∙ delay-force as k)

-- repeat

repeatᵏ : A → gStream k A
repeatᵏ a = fix (consᵏ a)

repeatᵏ-eq : (a : A) → repeatᵏ {k = k} a ＝ consᵏ a (λ α → repeatᵏ a)
repeatᵏ-eq a = ap (consᵏ a) (pfix (consᵏ a))

repeatˢ : A → Stream A
repeatˢ a k = repeatᵏ a

repeatˢ-eq : (a : A) → repeatˢ a ＝ consˢ a (repeatˢ a)
repeatˢ-eq a = fun-ext λ k → repeatᵏ-eq a

-- map

mapᵏ-body : (A → B) → ▹ k (gStream k A → gStream k B) → gStream k A → gStream k B
mapᵏ-body f m▹ as = consᵏ (f (headᵏ as)) (m▹ ⊛ (tail▹ᵏ as))

mapᵏ : (A → B) → gStream k A → gStream k B
mapᵏ f = fix (mapᵏ-body f)

mapᵏ-eq : (f : A → B) → (a : A) → (as▹ : ▹ k (gStream k A))
        → mapᵏ {k = k} f (consᵏ a as▹) ＝ consᵏ (f a) (λ α → mapᵏ f (as▹ α))
mapᵏ-eq f a as▹ =
  ap (consᵏ (f a))
     (▹-ext (λ α → happly (pfix-ext (mapᵏ-body f) α) (tail▹ᵏ (consᵏ a as▹) α)
                   ∙ ap (mapᵏ f) (▹-ap (tail-consᵏ a as▹) α)))

mapᵏ-head : (f : A → B) → (s : gStream k A)
          → headᵏ (mapᵏ {k = k} f s) ＝ f (headᵏ s)
mapᵏ-head f s = refl

mapᵏ-repeat : (a : A) → (f : A → B) → mapᵏ {k = k} f (repeatᵏ a) ＝ repeatᵏ (f a)
mapᵏ-repeat a f = fix λ prf▹ →
  mapᵏ f (repeatᵏ a)
    ＝⟨ ap (mapᵏ f) (repeatᵏ-eq a)  ⟩
  mapᵏ f (consᵏ a (λ α → repeatᵏ a))
    ＝⟨ mapᵏ-eq f a (λ x → consᵏ a (dfix (consᵏ a))) ⟩
  consᵏ (f a) (λ α → mapᵏ f (repeatᵏ a))
    ＝⟨ ap (consᵏ (f a)) (▹-ext prf▹) ⟩
  consᵏ (f a) (λ α → repeatᵏ (f a))
    ＝⟨ ap (consᵏ (f a)) (▹-ext λ α → sym (pfix-ext (consᵏ (f a)) α)) ⟩
  consᵏ (f a) (λ α → dfix (consᵏ (f a)) α)
    ＝⟨⟩
  repeatᵏ (f a)
    ∎

mapˢ : (A → B) → Stream A → Stream B
mapˢ f s k = mapᵏ f (s k)

mapˢ-eq : (f : A → B)
        → (a : A) → (as : Stream A)
        → mapˢ f (consˢ a as) ＝ consˢ (f a) (mapˢ f as)
mapˢ-eq f a as = fun-ext λ k → mapᵏ-eq f a (next (as k))

mapˢ-repeat : (a : A) → (f : A → B) → mapˢ f (repeatˢ a) ＝ repeatˢ (f a)
mapˢ-repeat a f = fun-ext (λ k → mapᵏ-repeat a f)

-- folding

foldrᵏ-body : (A → ▹ k B → B) → ▹ k (gStream k A → B) → gStream k A → B
foldrᵏ-body f f▹ s = f (headᵏ s) (f▹ ⊛ tail▹ᵏ s)

foldrᵏ : (A → ▹ k B → B) → gStream k A → B
foldrᵏ f = fix (foldrᵏ-body f)

scanl1ᵏ : (f : A → A → A) → gStream k A → gStream k A
scanl1ᵏ f = fix λ sc▹ s → consᵏ (headᵏ s) (▹map (mapᵏ (f (headᵏ s))) (sc▹ ⊛ tail▹ᵏ s))

-- iterate

iterateᵏ : ▹ k (A → A) → A → gStream k A
iterateᵏ f = fix λ i▹ a → consᵏ a (i▹ ⊛ (f ⊛ next a))

iterateˢ : (A → A) → A → Stream A
iterateˢ f a k = iterateᵏ (next f) a

-- interleave

interleaveᵏ : gStream k A → ▹ k (gStream k A) → gStream k A
interleaveᵏ = fix λ i▹ s t▹ → consᵏ (headᵏ s) (i▹ ⊛ t▹ ⊛ next (tail▹ᵏ s))

interleaveˢ : Stream A → Stream A → Stream A
interleaveˢ s t k = interleaveᵏ (s k) (next (t k))

-- zipping

zipWithᵏ : (f : A → B → C) → gStream k A → gStream k B → gStream k C
zipWithᵏ f = fix (λ zw▹ sa sb → consᵏ (f (headᵏ sa) (headᵏ sb)) (zw▹ ⊛ tail▹ᵏ sa ⊛ tail▹ᵏ sb))

zipWithˢ : (f : A → B → C) → Stream A → Stream B → Stream C
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
eoᵏ = fix (λ eo▹ s → consᵏ (headˢ s) λ α → eo▹ α (tailˢ (tailˢ s)))

eo : Stream A → Stream A
eo s k = eoᵏ s

-- diagonal function

diagauxᵏ : (Stream A → Stream A) → gStream k (Stream A) → gStream k A
diagauxᵏ = fix (λ d▹ f s → consᵏ ((headˢ ∘ f) (headᵏ s)) (d▹ ⊛ next (f ∘ tailˢ) ⊛ tail▹ᵏ s))

diagᵏ : gStream k (Stream A) → gStream k A
diagᵏ = diagauxᵏ id

diag : Stream (Stream A) → Stream A
diag x k = diagᵏ (x k)

-- natural numbers

natsᵏ-body : ▹ k (gStream k ℕ) → gStream k ℕ
natsᵏ-body nats▹ = consᵏ 0 (▹map (mapᵏ suc) nats▹)

natsᵏ : gStream k ℕ
natsᵏ = fix natsᵏ-body

natsᵏ-tail : tail▹ᵏ {k = k} natsᵏ ＝ next (mapᵏ suc natsᵏ)
natsᵏ-tail = ap tail▹ᵏ (fix-path natsᵏ-body) ∙ tail-consᵏ 0 (next (mapᵏ suc natsᵏ))

natsˢ : Stream ℕ
natsˢ k = natsᵏ

nats-tailˢ : tailˢ natsˢ ＝ mapˢ suc natsˢ
nats-tailˢ = fun-ext λ k →
  tailˢ natsˢ k
    ＝⟨⟩
  force (λ k′ → tail▹ᵏ natsᵏ) k
    ＝⟨ ap (λ q → force q k) (fun-ext (λ k′ → natsᵏ-tail)) ⟩
  force (λ k′ α → mapᵏ {k = k′} suc natsᵏ) k
    ＝⟨ delay-force (λ k′ → mapᵏ suc natsᵏ) k ⟩
  mapᵏ suc natsᵏ
    ＝⟨⟩
  mapˢ suc natsˢ k
    ∎

nats-1 : headˢ (tailˢ natsˢ) ＝ 1
nats-1 = ap headˢ nats-tailˢ

-- Fibonacci numbers

fibᵏ : gStream k ℕ
fibᵏ = fix λ fib▹ → consᵏ 0 (▹map (λ s → consᵏ 1 (▹map (zipWithᵏ _+_ s) (tail▹ᵏ s))) fib▹)

fibˢ : Stream ℕ
fibˢ k = fibᵏ

-- prime numbers

primesᵏ : gStream k ℕ
primesᵏ = fix λ pr▹ → consᵏ 2 (▹map (mapᵏ suc ∘ scanl1ᵏ _·_) pr▹)

primesˢ : Stream ℕ
primesˢ k = primesᵏ

-- paperfolding / dragon curve sequence

toggleᵏ : gStream k Bool
toggleᵏ = fix λ t▹ → consᵏ true (next (consᵏ false t▹))

toggleˢ : Stream Bool
toggleˢ k = toggleᵏ

paperfoldsᵏ : gStream k Bool
paperfoldsᵏ = fix (interleaveᵏ toggleᵏ)

paperfoldsˢ : Stream Bool
paperfoldsˢ k = paperfoldsᵏ

-- Thue-Morse sequence

hᵏ-body : ▹ k (gStream k Bool → gStream k Bool) → gStream k Bool → gStream k Bool
hᵏ-body h▹ s with (headᵏ s)
... | false = consᵏ false (next (consᵏ true  (h▹ ⊛ tail▹ᵏ s)))
... | true  = consᵏ true  (next (consᵏ false (h▹ ⊛ tail▹ᵏ s)))

hᵏ : gStream k Bool → gStream k Bool
hᵏ = fix hᵏ-body

thuemorseᵏ : gStream k Bool
thuemorseᵏ = fix λ t▹ → consᵏ false (▹map (λ tm → consᵏ true (▹map hᵏ (tail▹ᵏ (hᵏ tm)))) t▹)

thuemorseˢ : Stream Bool
thuemorseˢ k = thuemorseᵏ

-- Pascal coefficients

pascal-nextᵏ : gStream k ℕ → gStream k ℕ
pascal-nextᵏ xs = fix λ p▹ → consᵏ 1 (▹map (zipWithᵏ _+_) (tail▹ᵏ xs) ⊛ p▹)

pascal-nextˢ : Stream ℕ → Stream ℕ
pascal-nextˢ s k = pascal-nextᵏ (s k)

pascalᵏ : gStream k (Stream ℕ)
pascalᵏ = fix λ p▹ → consᵏ (repeatˢ 1) (▹map (mapᵏ pascal-nextˢ) p▹)

pascalˢ : Stream (Stream ℕ)
pascalˢ k = pascalᵏ
