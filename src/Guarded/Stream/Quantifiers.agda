{-# OPTIONS --guarded #-}
module Guarded.Stream.Quantifiers where

open import Prelude
open import Data.Empty

open import LaterG
open import Guarded.Stream

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ′ ℓ″ ℓ‴ : Level
  A : 𝒰 ℓ₁
  B : 𝒰 ℓ₂
  C : 𝒰 ℓ₃

-- predicates on a stream

data Atˢ (P : A → 𝒰 ℓ′) : ℕ → Stream A → 𝒰 (level-of-type A ⊔ ℓ′) where
  At-here  : ∀ {a s▹}
           → P a → Atˢ P 0 (cons a s▹)
  At-there : ∀ {a s▹ n}
           → ▸ (Atˢ P n ⍉ s▹)
           → Atˢ P (suc n) (cons a s▹)

Atˢ-map : {P : A → 𝒰} {Q : B → 𝒰} {f : A → B}
        → (∀ {x} → P x → Q (f x))
        → (n : ℕ) → (s : Stream A)
        → Atˢ P n s → Atˢ Q n (mapˢ f s)
Atˢ-map {Q} {f} pq =
  fix λ prf▹ → λ where
    .zero    .(cons a s▹) (At-here {a} {s▹} p)   → At-here (pq p)
    .(suc n) .(cons a s▹) (At-there {a} {s▹} {n} a▹) →
       subst (Atˢ Q (suc n)) (sym $ mapˢ-eq f a s▹) $
       At-there {a = f a} (prf▹ ⊛ next n ⊛▹ s▹ ⊛▹ a▹)

data Allˢ (P : A → 𝒰 ℓ′) : Stream A → 𝒰 (level-of-type A ⊔ ℓ′) where
  All-cons : ∀ {a s▹}
           → P a → ▸ (Allˢ P ⍉ s▹)
           → Allˢ P (cons a s▹)

Allˢ-repeat : {P : A → 𝒰 ℓ′}
            → ∀ x → P x → Allˢ P (repeatˢ x)
Allˢ-repeat {P} x px =
  fix λ ih▹ →
    All-cons px λ α → transport (λ i →  Allˢ P (pfix (cons x) (~ i) α)) (ih▹ α)

Allˢ-map : {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″} {f : A → B}
         → (∀ {x} → P x → Q (f x))
         → (s : Stream A)
         → Allˢ P s → Allˢ Q (mapˢ f s)
Allˢ-map {Q} {f} pq =
  fix λ prf▹ → λ where
    .(cons a s▹) (All-cons {a} {s▹} pa ps▹) →
       subst (Allˢ Q) (sym $ mapˢ-eq f a s▹) $
       All-cons (pq pa) (prf▹ ⊛ s▹ ⊛▹ ps▹)

Allˢ-zipWith : {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″} {R : C → 𝒰 ℓ‴} {f : A → B → C}
             → (∀ {x y} → P x → Q y → R (f x y))
             → (s : Stream A) → (t : Stream B)
             → Allˢ P s → Allˢ Q t → Allˢ R (zipWithˢ f s t)
Allˢ-zipWith {R} {f} pqr = fix λ prf▹ → λ where
  .(cons a s▹) .(cons b t▹) (All-cons {a} {s▹} pa as▹) (All-cons {a = b} {s▹ = t▹} qb at▹) →
     subst (Allˢ R) (sym $ zipWithˢ-eq f a s▹ b t▹) $
     All-cons (pqr pa qb) (prf▹ ⊛ s▹ ⊛▹ t▹ ⊛▹ as▹ ⊛▹ at▹)

¬Any→All¬ : ∀ {P : A → 𝒰 ℓ′}
          → (s : Stream A)
          → ¬ (Σ[ n ꞉ ℕ ] Atˢ P n s) → Allˢ (¬_ ∘ P) s
¬Any→All¬ {P} = fix λ prf▹ → λ where
  (cons h t▹) na →
    All-cons (λ ph → na (0 , At-here ph))
             (prf▹ ⊛▹ t▹ ⊛▹ λ α → λ where
                (n , a) → na (suc n , At-there λ β → subst (Atˢ P n) (tick-irr t▹ α β) a))

-- prefix versions

data Any≤ˢ (P : A → 𝒰 ℓ′) : ℕ → Stream A → 𝒰 (level-of-type A ⊔ ℓ′) where
  Any≤-here  : ∀ {a s▹ n}
            → P a → Any≤ˢ P n (cons a s▹)
  Any≤-there : ∀ {a s▹ n}
            → ▸ (Any≤ˢ P n ⍉ s▹)
            → Any≤ˢ P (suc n) (cons a s▹)

Any≤ˢ-map : {P : A → 𝒰} {Q : B → 𝒰} {f : A → B}
         → (∀ {x} → P x → Q (f x))
         → (n : ℕ) → (s : Stream A)
         → Any≤ˢ P n s → Any≤ˢ Q n (mapˢ f s)
Any≤ˢ-map {Q} {f} pq =
  fix λ prf▹ → λ where
    n        .(cons a s▹) (Any≤-here {a} {s▹} pa)      → Any≤-here (pq pa)
    .(suc n) .(cons a s▹) (Any≤-there {a} {s▹} {n} a▹) →
       subst (Any≤ˢ Q (suc n)) (sym $ mapˢ-eq f a s▹) $
       Any≤-there (prf▹ ⊛ next n ⊛▹ s▹ ⊛▹ a▹)

data All≤ˢ (P : A → 𝒰 ℓ′) : ℕ → Stream A → 𝒰 (level-of-type A ⊔ ℓ′) where
  All≤-nil  : ∀ {a s▹}
             → P a
             → All≤ˢ P zero (cons a s▹)
  All≤-cons : ∀ {a s▹ n}
             → P a → ▸ (All≤ˢ P n ⍉ s▹)
             → All≤ˢ P (suc n) (cons a s▹)

All≤ˢ-zipWith : {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″} {R : C → 𝒰 ℓ‴} {f : A → B → C}
             → (∀ {x y} → P x → Q y → R (f x y))
             → (n : ℕ) → (s : Stream A) → (t : Stream B)
             → All≤ˢ P n s → All≤ˢ Q n t → All≤ˢ R n (zipWithˢ f s t)
All≤ˢ-zipWith {R} {f} pqr = fix λ prf▹ → λ where
  .zero    .(cons _ _) .(cons _ _) (All≤-nil pa)                   (All≤-nil qb)                        →
     All≤-nil (pqr pa qb)
  .(suc n) .(cons _ _) .(cons _ _) (All≤-cons {a} {s▹} {n} pa as▹) (All≤-cons {a = b} {s▹ = t▹} qb at▹) →
     subst (All≤ˢ R (suc n)) (sym $ zipWithˢ-eq f a s▹ b t▹) $
     All≤-cons (pqr pa qb) (prf▹ ⊛ next n ⊛ s▹ ⊛▹ t▹ ⊛▹ as▹ ⊛▹ at▹)

-- adjacent elements

data Adjˢ (P : A → A → 𝒰 ℓ′) : Stream A → 𝒰 (level-of-type A ⊔ ℓ′) where
  Adj-cons : ∀ {a s▹}
           → ▸ ((P a ∘ headˢ) ⍉ s▹)
           → ▸ (Adjˢ P ⍉ s▹)
           → Adjˢ P (cons a s▹)

repeat-adj : {P : A → A → 𝒰 ℓ′}
           → (∀ a → P a a)
           → ∀ a → Adjˢ P (repeatˢ a)
repeat-adj {P} Pr a =
  fix λ ih▹ → Adj-cons (λ α → transport (λ i → P a (headˢ (pfix (cons a) (~ i) α))) (Pr a))
                       (λ α → transport (λ i → Adjˢ P (pfix (cons a) (~ i) α)) (ih▹ α))
