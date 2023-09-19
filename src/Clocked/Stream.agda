{-# OPTIONS --cubical --guarded #-}
module Clocked.Stream where

open import Prelude
open import Data.Nat
open import Data.List
open import Later

-- clocked streams

data gStream (k : Cl) (A : 𝒰) : 𝒰 where
  cons : (x : A) (xs : ▹ k (gStream k A)) → gStream k A

headᵏ : {A : 𝒰} {k : Cl} → gStream k A → A
headᵏ (cons x xs) = x

tail▹ᵏ : {A : 𝒰} {k : Cl} → gStream k A → ▹ k (gStream k A)
tail▹ᵏ (cons x xs) = xs

Stream : 𝒰 → 𝒰
Stream A = ∀ k → gStream k A

consᶠ : {A : 𝒰} → A → Stream A → Stream A
consᶠ a str k = str k

headᶠ : {A : 𝒰} → Stream A → A
headᶠ str = headᵏ (str k0)

tailᶠ : {A : 𝒰} → Stream A → Stream A
tailᶠ str = force λ k → tail▹ᵏ (str k)

repeatᵏ : {A : 𝒰} {k : Cl} → A → gStream k A
repeatᵏ a = fix (cons a)

repeatᵏ-eq : {A : 𝒰} {k : Cl} (a : A) → repeatᵏ {k = k} a ＝ cons a (λ α → repeatᵏ a)
repeatᵏ-eq a = ap (cons a) (pfix (cons a))

repeatᶠ : {A : 𝒰} → A → Stream A
repeatᶠ a k = repeatᵏ a

repeatᶠ-eq : {A : 𝒰} (a : A) → repeatᶠ a ＝ consᶠ a (repeatᶠ a)
repeatᶠ-eq a = refl

mapᵏ : {A B : 𝒰} {k : Cl} → (A → B) → gStream k A → gStream k B
mapᵏ f = fix λ map▹ as → cons (f (headᵏ as)) λ α → map▹ α (tail▹ᵏ as α)

mapᵏ-eq : {A B : 𝒰} {k : Cl}
        → (f : A → B)
        → ∀ a as → mapᵏ {k = k} f (cons a as) ＝ cons (f a) (λ α → mapᵏ f (as α))
mapᵏ-eq f a as =
  ap (cons (f a))
     (▹-ext (λ α → happly (pfix-ext (λ map▹ as′ → cons (f (headᵏ as′))
                                                       (λ x → map▹ x (tail▹ᵏ as′ x))) α)
                          (as α)))

mapᵏ-head : {A B : 𝒰} {k : Cl}
          → (f : A → B)
          → ∀ s → headᵏ (mapᵏ {k = k} f s) ＝ f (headᵏ s)
mapᵏ-head f s = refl

mapᵏ-repeat : {A B : 𝒰} {k : Cl} → (a : A) → (f : A → B) → mapᵏ {k = k} f (repeatᵏ a) ＝ repeatᵏ (f a)
mapᵏ-repeat {k} a f = fix λ prf▹ →
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

mapᶠ : ∀ {A B : 𝒰} → (A → B) → Stream A → Stream B
mapᶠ f s k = mapᵏ f (s k)

mapᶠ-eq : {A B : 𝒰}
        → (f : A → B)
        → ∀ a as → mapᶠ f (consᶠ a as) ＝ consᶠ (f a) (mapᶠ f as)
mapᶠ-eq f a as = refl

mapᶠ-repeat : {A B : 𝒰} → (a : A) → (f : A → B) → mapᶠ f (repeatᶠ a) ＝ repeatᶠ (f a)
mapᶠ-repeat a f = fun-ext (λ k → mapᵏ-repeat a f)

natsᵏ : {k : Cl} → gStream k ℕ
natsᵏ = fix (λ nats▹ → cons 0 (λ α → mapᵏ suc (nats▹ α)))

natsᵏ-tail : {k : Cl} → tail▹ᵏ {k = k} natsᵏ ＝ next (mapᵏ suc natsᵏ)
natsᵏ-tail = ap tail▹ᵏ (fix-path (λ nats▹ → cons 0 (λ α → mapᵏ suc (nats▹ α))))

nats : Stream ℕ
nats k = natsᵏ

nats-tail : tailᶠ nats ＝ mapᶠ suc nats
nats-tail = fun-ext λ k →
  tailᶠ nats k
    ＝⟨⟩
  force (λ k′ → tail▹ᵏ natsᵏ) k
    ＝⟨ ap (λ q → force q k) (fun-ext (λ k′ → natsᵏ-tail)) ⟩
  force (λ k′ α → mapᵏ {k = k′} suc natsᵏ) k
    ＝⟨ delay-force (λ k′ → mapᵏ suc natsᵏ) k ⟩
  mapᵏ suc natsᵏ
    ＝⟨⟩
  mapᶠ suc nats k
    ∎

nats-1 : headᶠ (tailᶠ nats) ＝ 1
nats-1 = ap headᶠ nats-tail

zipWithᵏ : {A B C : 𝒰} {k : Cl} → (f : A → B → C) → gStream k A → gStream k B → gStream k C
zipWithᵏ f = fix (λ zw▹ sa sb → cons (f (headᵏ sa) (headᵏ sb)) (zw▹ ⊛ tail▹ᵏ sa ⊛ tail▹ᵏ sb))

zipWithˢ : {A B C : 𝒰} → (f : A → B → C) → Stream A → Stream B → Stream C
zipWithˢ f sa sb k = zipWithᵏ f (sa k) (sb k)

fibᵏ : {k : Cl} → gStream k ℕ
fibᵏ = fix λ fib▹ → cons 0 (▹map (λ s → cons 1 (▹map (zipWithᵏ _+_ s) (tail▹ᵏ s))) fib▹)

fibˢ : Stream ℕ
fibˢ k = fibᵏ

scanl1ᵏ : {A : 𝒰} {k : Cl} → (f : A → A → A) → gStream k A → gStream k A
scanl1ᵏ f = fix λ sc▹ s → cons (headᵏ s) (▹map (mapᵏ (f (headᵏ s))) (sc▹ ⊛ tail▹ᵏ s))

primesᵏ : {k : Cl} → gStream k ℕ
primesᵏ = fix λ pr▹ → cons 2 (▹map (mapᵏ suc) (▹map (scanl1ᵏ _·_) pr▹))

primesˢ : Stream ℕ
primesˢ k = primesᵏ

nthᶠ : {A : 𝒰} → ℕ → Stream A → A
nthᶠ  zero   s = headᶠ s
nthᶠ (suc n) s = nthᶠ n (tailᶠ s)

takeᶠ : {A : 𝒰} → ℕ → Stream A → List A
takeᶠ  zero   s = []
takeᶠ (suc n) s = headᶠ s ∷ takeᶠ n (tailᶠ s)

eoᵏ : {A : 𝒰} {k : Cl} → Stream A → gStream k A
eoᵏ = fix (λ eo▹ s → cons (headᶠ s) λ α → eo▹ α (tailᶠ (tailᶠ s)))

eo : {A : 𝒰} → Stream A → Stream A
eo s k = eoᵏ s
