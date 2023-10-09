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

Stream-body : 𝒰 → ▹ 𝒰 → 𝒰
Stream-body A S▹ = A × ▸ S▹

Stream : 𝒰 → 𝒰
Stream A = fix (Stream-body A)

consˢ : A → ▹ Stream A → Stream A
consˢ {A} x xs▹ = (x , subst ▸_ (sym $ pfix (Stream-body A)) xs▹)

unconsˢ : Stream A → A × ▹ Stream A
unconsˢ {A} (x , xs▹) = x , subst ▸_ (pfix (Stream-body A)) xs▹

headˢ : Stream A → A
headˢ = fst ∘ unconsˢ

tail▹ˢ : Stream A → ▹ Stream A
tail▹ˢ = snd ∘ unconsˢ

uncons-eq : (s : Stream A) → s ＝ consˢ (headˢ s) (tail▹ˢ s)
uncons-eq {A} (a , as▹) =
  ap (λ q → (a , q)) $ sym $ transport⁻-transport (λ i → ▸ pfix (Stream-body A) i) as▹

head-cons : (a : A) → (as▹ : ▹ Stream A) → headˢ (consˢ a as▹) ＝ a
head-cons a as▹ = refl

tail-cons : (a : A) → (as▹ : ▹ Stream A) → tail▹ˢ (consˢ a as▹) ＝ as▹
tail-cons {A} a as▹ = transport⁻-transport (λ i → ▸ pfix (Stream-body A) (~ i)) as▹

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
        → mapˢ f (consˢ a as▹) ＝ consˢ (f a) (λ α → mapˢ f (as▹ α))
mapˢ-eq {A} f a as▹ =
  ap (consˢ (f a)) (▹-ext λ α →
    ap (dfix (mapˢ-body f) α) (▹-ap (tail-cons a as▹) α)
    ∙ happly (pfix-ext (mapˢ-body f) α) (as▹ α))

mapˢ-head : (f : A → B) → (s : Stream A)
          → headˢ (mapˢ f s) ＝ f (headˢ s)
mapˢ-head f s = refl

mapˢ-tail : (f : A → B) → (s : Stream A)
          → tail▹ˢ (mapˢ f s) ＝ ▹map (mapˢ f) (tail▹ˢ s)
mapˢ-tail f s =
  ap (λ q → tail▹ˢ (mapˢ f q)) (uncons-eq s)
  ∙ ap tail▹ˢ (mapˢ-eq f (headˢ s) (tail▹ˢ s))
  ∙ tail-cons (f (headˢ s)) (▹map (mapˢ f) (tail▹ˢ s))

mapˢ-fusion : (f : A → B) → (g : B → C) → (s : Stream A)
            → mapˢ g (mapˢ f s) ＝ mapˢ (g ∘ f) s
mapˢ-fusion f g =
  fix λ prf▹ s → let (a , as▹) = unconsˢ s in
    mapˢ g (mapˢ f s)
      ＝⟨ ap (mapˢ g ∘ mapˢ f) (uncons-eq s) ⟩
    mapˢ g (mapˢ f (consˢ a as▹))
      ＝⟨ ap (mapˢ g) (mapˢ-eq f a as▹) ⟩
    mapˢ g (consˢ (f a) (▹map (mapˢ f) as▹))
      ＝⟨ mapˢ-eq g (f a) (▹map (mapˢ f) as▹) ⟩
    consˢ (g (f a)) (▹map (mapˢ g) (▹map (mapˢ f) as▹))
      ＝⟨ ap (consˢ (g (f a))) (▹-ext (prf▹ ⊛ as▹)) ⟩
    consˢ (g (f a)) (▹map (mapˢ (g ∘ f)) as▹)
      ＝⟨ sym (mapˢ-eq (g ∘ f) a as▹) ⟩
    mapˢ (g ∘ f) (consˢ a as▹)
      ＝⟨ ap (mapˢ (g ∘ f)) (sym $ uncons-eq s) ⟩
    mapˢ (g ∘ f) s
      ∎

mapˢ-repeat : (a : A) → (f : A → B) → mapˢ f (repeatˢ a) ＝ repeatˢ (f a)
mapˢ-repeat a f = fix λ prf▹ →
  mapˢ f (repeatˢ a)
    ＝⟨ ap (mapˢ f) (repeatˢ-eq a)  ⟩
  mapˢ f (consˢ a (λ α → repeatˢ a))
    ＝⟨ mapˢ-eq f a (λ x → consˢ a (dfix (consˢ a))) ⟩
  consˢ (f a) (λ α → mapˢ f (repeatˢ a))
    ＝⟨ ap (consˢ (f a)) (▹-ext prf▹) ⟩
  consˢ (f a) (λ α → repeatˢ (f a))
    ＝⟨ ap (consˢ (f a)) (▹-ext λ α → sym (pfix-ext (consˢ (f a)) α)) ⟩
  consˢ (f a) (λ α → dfix (consˢ (f a)) α)
    ＝⟨⟩
  repeatˢ (f a)
    ∎

-- lift a predicate to a stream

PStr-body : (A → 𝒰) → ▹ (Stream A → 𝒰) → Stream A → 𝒰
PStr-body P P▹ s = P (headˢ s) × ▸ (P▹ ⊛ (tail▹ˢ s))

PStr : (A → 𝒰) → Stream A → 𝒰
PStr P = fix (PStr-body P)

Pcons : ∀ {a as▹} {P : A → 𝒰} → P a → ▹[ α ] (PStr P (as▹ α)) → PStr P (consˢ a as▹)
Pcons {a} {as▹} {P} pa ps▹ =
    pa
  , (subst (λ q → ▸ (dfix (PStr-body P) ⊛ q)) (sym $ tail-cons a as▹) $
     subst (λ q → ▸ (q ⊛ as▹)) (sym $ pfix (PStr-body P)) $
     ps▹)

P-match : ∀ {a as▹} {P : A → 𝒰} → PStr P (consˢ a as▹) → P a × ▹[ α ] (PStr P (as▹ α))
P-match {a} {as▹} {P} (pa , ps▸) =
    pa
  , (subst (λ q → ▸ (q ⊛ as▹)) (pfix (PStr-body P)) $
     subst (λ q → ▸ (dfix (PStr-body P) ⊛ q)) (tail-cons a as▹) $
     ps▸)

PStr-map : {P Q : A → 𝒰} {f : A → A}
         → ({x : A} → P x → Q (f x))
         → (s : Stream A) → PStr P s → PStr Q (mapˢ f s)
PStr-map {P} {Q} {f} pq =
  fix λ prf▹ s ps →
    let pa , pas▹ = P-match (subst (PStr P) (uncons-eq s) ps) in
    subst (PStr Q ∘ mapˢ f) (sym $ uncons-eq s) $
    subst (PStr Q) (sym $ mapˢ-eq f (headˢ s) (tail▹ˢ s)) $
    Pcons (pq pa) ((λ α → prf▹ α (tail▹ˢ s α) (pas▹ α)))

-- folding

foldrˢ-body : (A → ▹ B → B) → ▹ (Stream A → B) → Stream A → B
foldrˢ-body f f▹ s = f (headˢ s) (f▹ ⊛ tail▹ˢ s)

foldrˢ : (A → ▹ B → B) → Stream A → B
foldrˢ f = fix (foldrˢ-body f)

scanl1ˢ-body : (A → A → A) → ▹ (Stream A → Stream A) → Stream A → Stream A
scanl1ˢ-body f sc▹ s = consˢ (headˢ s) (▹map (mapˢ (f (headˢ s))) (sc▹ ⊛ tail▹ˢ s))

scanl1ˢ : (A → A → A) → Stream A → Stream A
scanl1ˢ f = fix (scanl1ˢ-body f)

-- iterate

iterateˢ-body : ▹ (A → A) → ▹ (A → Stream A) → A → Stream A
iterateˢ-body f i▹ a = consˢ a (i▹ ⊛ (f ⊛ next a))

iterateˢ : ▹ (A → A) → A → Stream A
iterateˢ f = fix (iterateˢ-body f)

tail-iterateˢ : (f▹ : ▹ (A → A)) → (x : A)
              → tail▹ˢ (iterateˢ f▹ x) ＝ ▹map (iterateˢ f▹) (f▹ ⊛ next x)
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

-- natural numbers

natsˢ-body : ▹ Stream ℕ → Stream ℕ
natsˢ-body nats▹ = consˢ 0 (▹map (mapˢ suc) nats▹)

natsˢ : Stream ℕ
natsˢ = fix natsˢ-body

natsˢ-tail : tail▹ˢ natsˢ ＝ next (mapˢ suc natsˢ)
natsˢ-tail =
  ap tail▹ˢ (fix-path natsˢ-body)
  ∙ tail-cons 0 (λ α → mapˢ suc (next (fix natsˢ-body) α))

-- Fibonacci numbers

fibˢ-body : ▹ Stream ℕ → Stream ℕ
fibˢ-body fib▹ = consˢ 0 (▹map (λ s → consˢ 1 (▹map (zipWithˢ _+_ s) (tail▹ˢ s))) fib▹)

fibˢ : Stream ℕ
fibˢ = fix fibˢ-body

-- prime numbers

primesˢ-body : ▹ Stream ℕ → Stream ℕ
primesˢ-body pr▹ = consˢ 2 (▹map (mapˢ suc ∘ scanl1ˢ _·_) pr▹)

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
thuemorseˢ = fix λ t▹ → consˢ false (▹map (λ tm → consˢ true (▹map hˢ (tail▹ˢ (hˢ tm)))) t▹)

-- Pascal coefficients

pascal-nextˢ : Stream ℕ → Stream ℕ
pascal-nextˢ xs = fix λ p▹ → consˢ 1 (▹map (zipWithˢ _+_) (tail▹ˢ xs) ⊛ p▹)

pascalˢ : Stream (Stream ℕ)
pascalˢ = fix λ p▹ → consˢ (repeatˢ 1) (▹map (mapˢ pascal-nextˢ) p▹)
