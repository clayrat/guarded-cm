{-# OPTIONS --guarded #-}
module Guarded.Partial.Fin where

open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.Sum
open import LaterG

private variable
  A B C : 𝒰

-- Delay monad indexed by exact finite number of steps

data Delayed (A : 𝒰) : ℕ → 𝒰 where
  nowD   : A → Delayed A zero
  laterD : ∀ {n} → ▹ (Delayed A n) → Delayed A (suc n)

stallᵈ : ∀ {n} → Delayed A n → Delayed A (suc n)
stallᵈ = laterD ∘ next

delay-by : (n : ℕ) → A → Delayed A n
delay-by  zero   a = nowD a
delay-by (suc n) a = stallᵈ (delay-by n a)

mapᵈ : ∀ {n} → (A → B) → Delayed A n → Delayed B n
mapᵈ f (nowD a)   = nowD (f a)
mapᵈ f (laterD p) = laterD λ α → mapᵈ f (p α)

apᵈ : ∀ {m n} → Delayed (A → B) m → Delayed A n → Delayed B (max m n)
apᵈ     (nowD f)             (nowD a)         = nowD (f a)
apᵈ {B} (nowD f)             (laterD {n} pa▹) = laterD (λ α → subst (Delayed B)
                                                                    (max-id-l n)
                                                                    (apᵈ (nowD f) (pa▹ α)))
apᵈ {B} (laterD {n = m} pf▹) (nowD a)         = laterD (λ α → subst (Delayed B)
                                                                    (max-id-r m)
                                                                    (apᵈ (pf▹ α) (nowD a)))
apᵈ     (laterD         pf▹) (laterD     pa▹) = laterD (λ α → apᵈ (pf▹ α) (pa▹ α))

_>>=ᵈ_ : ∀ {m n} → Delayed A m → (A → Delayed B n) → Delayed B (m + n)
nowD x    >>=ᵈ f = f x
laterD d▹ >>=ᵈ f = laterD (λ α → d▹ α >>=ᵈ f)

map²ᵈ : ∀ {m n} → (A → B → C) → Delayed A m → Delayed B n → Delayed C (max m n)
map²ᵈ f = apᵈ ∘ mapᵈ f

bothᵈ : ∀ {m n} → Delayed A m → Delayed B n → Delayed (A × B) (max m n)
bothᵈ = map²ᵈ (_,_)

raceᵈ-body : ▹ ((m n : ℕ) → Delayed A m → Delayed A n → Delayed A (min m n)) → (m n : ℕ) → Delayed A m → Delayed A n → Delayed A (min m n)
raceᵈ-body {A} r▹ .0        n       (nowD a)              _               = subst (Delayed A)
                                                                                  (sym $ min-absorb-l n)
                                                                                  (nowD a)
raceᵈ-body     r▹ .(suc m) .0       (laterD {n = m} _)   (nowD a)         = nowD a
raceᵈ-body     r▹ .(suc m) .(suc n) (laterD {n = m} p1▹) (laterD {n} p2▹) = laterD (r▹ ⊛ next m ⊛ next n ⊛ p1▹ ⊛ p2▹)

raceᵈ : ∀ {m n} → Delayed A m → Delayed A n → Delayed A (min m n)
raceᵈ {m} {n} = fix raceᵈ-body m n

travᵈ-body : (A → ▹ B) → ▹ ((n : ℕ) → Delayed A n → ▹ Delayed B n) → (n : ℕ) → Delayed A n → ▹ Delayed B n
travᵈ-body f P▹ .zero    (nowD a)            = ▹map nowD (f a)
travᵈ-body f P▹ .(suc n) (laterD {n = n} p▹) = ▹map laterD (P▹ ⊛ next n ⊛ p▹)

travᵈ : ∀ {n} → (A → ▹ B) → Delayed A n → ▹ Delayed B n
travᵈ {n} f = fix (travᵈ-body f) n

-- adds an extra step
▹Delayed+ : ∀ {n} → ▹ Delayed A n → Delayed (▹ A) (suc n)
▹Delayed+ = laterD ∘ ▹map (mapᵈ next)
