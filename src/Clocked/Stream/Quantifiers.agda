{-# OPTIONS --guarded #-}
module Clocked.Stream.Quantifiers where

open import Prelude
open import Data.Empty

open import Later
open import Clocked.Stream

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ′ ℓ″ ℓ‴ : Level
  A : 𝒰 ℓ₁
  B : 𝒰 ℓ₂
  C : 𝒰 ℓ₃
  k : Cl

-- predicates on a stream

-- indexed existential

data gAt (k : Cl) (P : A → 𝒰 ℓ′) : ℕ → gStream k A → 𝒰 (level-of-type A ⊔ ℓ′) where
  gAt-here  : ∀ {a s▹}
            → P a → gAt k P 0 (cons a s▹)
  gAt-there : ∀ {a s▹ n}
            → ▹[ α ∶ k ] (gAt k P n (s▹ α))
            → gAt k P (suc n) (cons a s▹)

At : (A → 𝒰 ℓ′) → ℕ → Stream A → 𝒰 (level-of-type A ⊔ ℓ′)
At P n s = ∀ k → gAt k P n (s k)

At-here : {P : A → 𝒰} {a : A} {s : Stream A}
        → P a → At P 0 (consˢ a s)
At-here pa k = gAt-here pa

At-there : {P : A → 𝒰} {n : ℕ} {a : A} {s : Stream A}
         → At P n s → At P (suc n) (consˢ a s)
At-there at k = gAt-there (next (at k))

At-tail : {P : A → 𝒰} {n : ℕ} {s : Stream A}
        → At P (suc n) s → At P n (tailˢ s)
At-tail {P} {n} {s} a = force go
  where
  go : ∀ κ → ▹ κ (gAt κ P n (tailˢ s κ))
  go κ with s κ | recall s κ | a κ
  ... | cons h t▹ | ⟪ e ⟫ | gAt-there a▹ =
    λ α → subst (gAt κ P n) (sym ((force-delay (tail▹ᵏ ∘ s) κ α) ∙ λ i → tail▹ᵏ (e i) α)) (a▹ α)


gAt-map : {P : A → 𝒰} {Q : B → 𝒰} {f : A → B}
        → (∀ {x} → P x → Q (f x))
        → (n : ℕ) → (s : gStream k A)
        → gAt k P n s → gAt k Q n (mapᵏ f s)
gAt-map {k} {Q} {f} pq =
  fix λ prf▹ → λ where
    .zero    .(cons a s▹) (gAt-here {a} {s▹} p)   → gAt-here (pq p)
    .(suc n) .(cons a s▹) (gAt-there {a} {s▹} {n} a▹) →
       subst (gAt k Q (suc n)) (sym $ mapᵏ-eq f a s▹) $
       gAt-there {a = f a} (prf▹ ⊛ next n ⊛▹ s▹ ⊛▹ a▹)

At-map : {P : A → 𝒰} {Q : B → 𝒰} {f : A → B}
       → (∀ {x} → P x → Q (f x))
       → (n : ℕ) → (s : Stream A)
       → At P n s → At Q n (mapˢ f s)
At-map pq n s a k = gAt-map pq n (s k) (a k)

-- universal

data gAll (k : Cl) (P : A → 𝒰 ℓ′) : gStream k A → 𝒰 (level-of-type A ⊔ ℓ′) where
  gAll-cons : ∀ {a s▹}
            → P a → ▹[ α ∶ k ] (gAll k P (s▹ α))
            → gAll k P (cons a s▹)

gAll-repeat : {P : A → 𝒰 ℓ′}
            → ∀ a → P a → gAll k P (repeatᵏ a)
gAll-repeat {k} {P} a Pa =
  fix {k = k} λ ih▹ →
    gAll-cons Pa λ α → transport (λ i → gAll k P (pfix (cons a) (~ i) α)) (ih▹ α)

gAll-map : {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″} {f : A → B}
          → ({x : A} → P x → Q (f x))
          → (s : gStream k A) → gAll k P s → gAll k Q (mapᵏ f s)
gAll-map {k} {Q} {f} pq =
  fix {k = k} λ prf▹ → λ where
    .(cons a s▹) (gAll-cons {a} {s▹} pa pas▹) →
       subst (gAll k Q) (sym $ mapᵏ-eq f a s▹) $
       gAll-cons (pq pa) (λ α → prf▹ α (s▹ α) (pas▹ α))

gAll-zipWith : {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″} {R : C → 𝒰 ℓ‴} {f : A → B → C}
             → (∀ {x y} → P x → Q y → R (f x y))
             → (s : gStream k A) → (t : gStream k B)
             → gAll k P s → gAll k Q t → gAll k R (zipWithᵏ f s t)
gAll-zipWith {k} {R} {f} pqr = fix λ prf▹ → λ where
  .(cons a s▹) .(cons b t▹) (gAll-cons {a} {s▹} pa as▹) (gAll-cons {a = b} {s▹ = t▹} qb at▹) →
     subst (gAll k R) (sym $ zipWithᵏ-eq f a s▹ b t▹) $
     gAll-cons (pqr pa qb) λ α → prf▹ α (s▹ α) (t▹ α) (as▹ α) (at▹ α)

All : (A → 𝒰 ℓ′) → Stream A → 𝒰 (level-of-type A ⊔ ℓ′)
All P s = ∀ k → gAll k P (s k)

All-repeat : {P : A → 𝒰 ℓ′}
           → ∀ a → P a → All P (repeatˢ a)
All-repeat a Pa k = gAll-repeat a Pa

All-map : {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″} {f : A → B}
         → ({x : A} → P x → Q (f x))
         → (s : Stream A) → All P s → All Q (mapˢ f s)
All-map pq s ps k = gAll-map pq (s k) (ps k)

All-zipWith : {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″} {R : C → 𝒰 ℓ‴} {f : A → B → C}
            → (∀ {x y} → P x → Q y → R (f x y))
            → (s : Stream A) → (t : Stream B)
            → All P s → All Q t → All R (zipWithˢ f s t)
All-zipWith pqr s t ps pt k = gAll-zipWith pqr (s k) (t k) (ps k) (pt k)

-- prefix versions

data gAny≤ (k : Cl) (P : A → 𝒰 ℓ′) : ℕ → gStream k A → 𝒰 (level-of-type A ⊔ ℓ′) where
  gAny≤-here  : ∀ {a s▹ n}
              → P a → gAny≤ k P n (cons a s▹)
  gAny≤-there : ∀ {a s▹ n}
              → ▹[ α ∶ k ] (gAny≤ k P n (s▹ α))
              → gAny≤ k P (suc n) (cons a s▹)

gAny≤-map : {P : A → 𝒰} {Q : B → 𝒰} {f : A → B}
          → (∀ {x} → P x → Q (f x))
          → (n : ℕ) → (s : gStream k A)
          → gAny≤ k P n s → gAny≤ k Q n (mapᵏ f s)
gAny≤-map {k} {Q} {f} pq =
  fix λ prf▹ → λ where
    n        .(cons a s▹) (gAny≤-here {a} {s▹} pa)      → gAny≤-here (pq pa)
    .(suc n) .(cons a s▹) (gAny≤-there {a} {s▹} {n} a▹) →
       subst (gAny≤ k Q (suc n)) (sym $ mapᵏ-eq f a s▹) $
       gAny≤-there (prf▹ ⊛ (next n) ⊛▹ s▹ ⊛▹ a▹)

Any≤ : (A → 𝒰 ℓ′) → ℕ → Stream A → 𝒰 (level-of-type A ⊔ ℓ′)
Any≤ P n s = ∀ k → gAny≤ k P n (s k)

Any≤-map : {P : A → 𝒰} {Q : B → 𝒰} {f : A → B}
         → (∀ {x} → P x → Q (f x))
         → (n : ℕ) → (s : Stream A)
         → Any≤ P n s → Any≤ Q n (mapˢ f s)
Any≤-map pq n s a k = gAny≤-map pq n (s k) (a k)

data gAll≤ (k : Cl) (P : A → 𝒰 ℓ′) : ℕ → gStream k A → 𝒰 (level-of-type A ⊔ ℓ′) where
  gAll≤-nil  : ∀ {a s▹}
             → P a
             → gAll≤ k P zero (cons a s▹)
  gAll≤-cons : ∀ {a s▹ n}
             → P a → ▹[ α ∶ k ] (gAll≤ k P n (s▹ α))
             → gAll≤ k P (suc n) (cons a s▹)

All≤ : (A → 𝒰 ℓ′) → ℕ → Stream A → 𝒰 (level-of-type A ⊔ ℓ′)
All≤ P n s = ∀ k → gAll≤ k P n (s k)

All≤-nil : ∀ {P : A → 𝒰 ℓ′} {a s}
         → P a → All≤ P zero (consˢ a s)
All≤-nil p k = gAll≤-nil p

All≤-cons : ∀ {P : A → 𝒰 ℓ′} {a s n}
          → P a → All≤ P n s  -- guard?
          → All≤ P (suc n) (consˢ a s)
All≤-cons p a k = gAll≤-cons p (next (a k))

-- adjacent elements

data gAdj (k : Cl) (P : A → A → 𝒰 ℓ′) : gStream k A → 𝒰 (level-of-type A ⊔ ℓ′) where
  gAdj-cons : ∀ {a s▹}
            → ▹[ α ∶ k ] P a (headᵏ (s▹ α))
            → ▹[ α ∶ k ] (gAdj k P (s▹ α))
            → gAdj k P (cons a s▹)

repeat-gadj : {P : A → A → 𝒰 ℓ′}
            → ∀ a → P a a → gAdj k P (repeatᵏ a)
repeat-gadj {k} {P} a Pr =
  fix λ ih▹ → gAdj-cons (λ α → transport (λ i → P a (headᵏ (pfix (cons a) (~ i) α))) Pr)
                        (λ α → transport (λ i → gAdj k P (pfix (cons a) (~ i) α)) (ih▹ α))

Adj : (A → A → 𝒰 ℓ′) → Stream A → 𝒰 (level-of-type A ⊔ ℓ′)
Adj P s = ∀ k → gAdj k P (s k)

repeat-adj : {P : A → A → 𝒰 ℓ′}
           → ∀ a → P a a → Adj P (repeatˢ a)
repeat-adj a Pr k = repeat-gadj a Pr
