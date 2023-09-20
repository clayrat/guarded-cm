{-# OPTIONS --cubical --guarded #-}
module Clocked.Stream where

open import Prelude
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

repeatᵏ : A → gStream k A
repeatᵏ a = fix (cons a)

repeatᵏ-eq : (a : A) → repeatᵏ {k = k} a ＝ cons a (λ α → repeatᵏ a)
repeatᵏ-eq a = ap (cons a) (pfix (cons a))

repeatˢ : A → Stream A
repeatˢ a k = repeatᵏ a

repeatˢ-eq : (a : A) → repeatˢ a ＝ consˢ a (repeatˢ a)
repeatˢ-eq a = fun-ext λ k → repeatᵏ-eq a

mapᵏ : (A → B) → gStream k A → gStream k B
mapᵏ f = fix λ map▹ as → cons (f (headᵏ as)) λ α → map▹ α (tail▹ᵏ as α)

mapᵏ-eq : (f : A → B) → (a : A) → (as▹ : ▹ k (gStream k A))
        → mapᵏ {k = k} f (cons a as▹) ＝ cons (f a) (λ α → mapᵏ f (as▹ α))
mapᵏ-eq f a as▹ =
  ap (cons (f a))
     (▹-ext (λ α → happly (pfix-ext (λ map▹ as′ → cons (f (headᵏ as′))
                                                       (λ x → map▹ x (tail▹ᵏ as′ x))) α)
                          (as▹ α)))

mapᵏ-head : (f : A → B) → (s : gStream k A)
          → headᵏ (mapᵏ {k = k} f s) ＝ f (headᵏ s)
mapᵏ-head f s = refl

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

mapˢ-repeat : (a : A) → (f : A → B) → mapˢ f (repeatˢ a) ＝ repeatˢ (f a)
mapˢ-repeat a f = fun-ext (λ k → mapᵏ-repeat a f)

natsᵏ : gStream k ℕ
natsᵏ = fix (λ nats▹ → cons 0 (λ α → mapᵏ suc (nats▹ α)))

natsᵏ-tail : tail▹ᵏ {k = k} natsᵏ ＝ next (mapᵏ suc natsᵏ)
natsᵏ-tail = ap tail▹ᵏ (fix-path (λ nats▹ → cons 0 (λ α → mapᵏ suc (nats▹ α))))

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
nats-1 = ap headˢ  nats-tail

zipWithᵏ : (f : A → B → C) → gStream k A → gStream k B → gStream k C
zipWithᵏ f = fix (λ zw▹ sa sb → cons (f (headᵏ sa) (headᵏ sb)) (zw▹ ⊛ tail▹ᵏ sa ⊛ tail▹ᵏ sb))

zipWithˢ : (f : A → B → C) → Stream A → Stream B → Stream C
zipWithˢ f sa sb k = zipWithᵏ f (sa k) (sb k)

fibᵏ : gStream k ℕ
fibᵏ = fix λ fib▹ → cons 0 (▹map (λ s → cons 1 (▹map (zipWithᵏ _+_ s) (tail▹ᵏ s))) fib▹)

fibˢ : Stream ℕ
fibˢ k = fibᵏ

scanl1ᵏ : (f : A → A → A) → gStream k A → gStream k A
scanl1ᵏ f = fix λ sc▹ s → cons (headᵏ s) (▹map (mapᵏ (f (headᵏ s))) (sc▹ ⊛ tail▹ᵏ s))

primesᵏ : gStream k ℕ
primesᵏ = fix λ pr▹ → cons 2 (▹map (mapᵏ suc) (▹map (scanl1ᵏ _·_) pr▹))

primesˢ : Stream ℕ
primesˢ k = primesᵏ

nthˢ : ℕ → Stream A → A
nthˢ  zero   s = headˢ s
nthˢ (suc n) s = nthˢ n (tailˢ s)

takeˢ : ℕ → Stream A → List A
takeˢ  zero   s = []
takeˢ (suc n) s = headˢ s ∷ takeˢ n (tailˢ s)

eoᵏ : Stream A → gStream k A
eoᵏ = fix (λ eo▹ s → cons (headˢ s) λ α → eo▹ α (tailˢ (tailˢ s)))

eo : Stream A → Stream A
eo s k = eoᵏ s
