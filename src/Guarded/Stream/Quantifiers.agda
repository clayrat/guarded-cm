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

data Anyˢ (P : A → 𝒰 ℓ′) : Stream A → 𝒰 (level-of-type A ⊔ ℓ′) where
  Any-here  : ∀ {a s▹}
            → P a → Anyˢ P (cons a s▹)
  Any-there : ∀ {a s▹}
            → ▹[ α ] (Anyˢ P (s▹ α))
            → Anyˢ P (cons a s▹)

Anyˢ-map : {P : A → 𝒰} {Q : B → 𝒰} {f : A → B}
         → (∀ {x} → P x → Q (f x))
         → (s : Stream A)
         → Anyˢ P s → Anyˢ Q (mapˢ f s)
Anyˢ-map {Q} {f} pq =
  fix λ prf▹ → λ where
    .(cons a s▹) (Any-here {a} {s▹} p)   → Any-here (pq p)
    .(cons a s▹) (Any-there {a} {s▹} a▹) →
       subst (Anyˢ Q) (sym $ mapˢ-eq f a s▹) $
       Any-there {a = f a} λ α → prf▹ α (s▹ α) (a▹ α)

data Allˢ (P : A → 𝒰 ℓ′) : Stream A → 𝒰 (level-of-type A ⊔ ℓ′) where
  All-cons : ∀ {a s▹}
           → P a → ▹[ α ] (Allˢ P (s▹ α))
           → Allˢ P (cons a s▹)

Allˢ-map : {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″} {f : A → B}
         → (∀ {x} → P x → Q (f x))
         → (s : Stream A)
         → Allˢ P s → Allˢ Q (mapˢ f s)
Allˢ-map {Q} {f} pq =
  fix λ prf▹ → λ where
    .(cons a s▹) (All-cons {a} {s▹} pa ps▹) →
       subst (Allˢ Q) (sym $ mapˢ-eq f a s▹) $
       All-cons (pq pa) (λ α → prf▹ α (s▹ α) (ps▹ α))

Allˢ-zipWith : {P : A → 𝒰 ℓ′} {Q : B → 𝒰 ℓ″} {R : C → 𝒰 ℓ‴} {f : A → B → C}
             → (∀ {x y} → P x → Q y → R (f x y))
             → (s : Stream A) → (t : Stream B)
             → Allˢ P s → Allˢ Q t → Allˢ R (zipWithˢ f s t)
Allˢ-zipWith {R} {f} pqr = fix λ prf▹ → λ where
  .(cons a s▹) .(cons b t▹) (All-cons {a} {s▹} pa as▹) (All-cons {a = b} {s▹ = t▹} qb at▹) →
     subst (Allˢ R) (sym $ zipWithˢ-eq f a s▹ b t▹) $
     All-cons (pqr pa qb) λ α → prf▹ α (s▹ α) (t▹ α) (as▹ α) (at▹ α)

¬Any→All¬ : ∀ {P : A → 𝒰 ℓ′}
          → (s : Stream A) → ¬ (Anyˢ P s) → Allˢ (¬_ ∘ P) s
¬Any→All¬ {P} = fix λ prf▹ → λ where
  (cons h t▹) n →
    All-cons (n ∘ Any-here)
             (λ α → prf▹ α (t▹ α) (λ a → n (Any-there (λ β → subst (Anyˢ P) (tick-irr t▹ α β) a))))

-- other directions seem impossible ?

-- prefix versions

data Any≤ˢ (P : A → 𝒰 ℓ′) : ℕ → Stream A → 𝒰 (level-of-type A ⊔ ℓ′) where
  Any≤-here  : ∀ {a s▹ n}
            → P a → Any≤ˢ P n (cons a s▹)
  Any≤-there : ∀ {a s▹ n}
            → ▹[ α ] (Any≤ˢ P n (s▹ α))
            → Any≤ˢ P (suc n) (cons a s▹)

data All≤ˢ (P : A → 𝒰 ℓ′) : ℕ → Stream A → 𝒰 (level-of-type A ⊔ ℓ′) where
  All≤-nil  : ∀ {a s▹}
             → P a
             → All≤ˢ P zero (cons a s▹)
  All≤-cons : ∀ {a s▹ n}
             → P a → ▹[ α ] (All≤ˢ P n (s▹ α))
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
     All≤-cons (pqr pa qb) (λ α → prf▹ α n (s▹ α) (t▹ α) (as▹ α) (at▹ α))

-- adjacent elements

data Adjˢ (P : A → A → 𝒰 ℓ′) : Stream A → 𝒰 (level-of-type A ⊔ ℓ′) where
  Adj-cons : ∀ {a s▹}
           → ▹[ α ] P a (headˢ (s▹ α)) → ▹[ α ] (Adjˢ P (s▹ α))
           → Adjˢ P (cons a s▹)

repeat-adj : {P : A → A → 𝒰 ℓ′}
           → (∀ a → P a a)
           → ∀ a → Adjˢ P (repeatˢ a)
repeat-adj {P} Pr a =
  fix λ ih▹ → Adj-cons (λ α → transport (λ i → P a (headˢ (pfix (cons a) (~ i) α))) (Pr a))
                       (λ α → transport (λ i → Adjˢ P (pfix (cons a) (~ i) α)) (ih▹ α))
