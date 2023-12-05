{-# OPTIONS --guarded #-}
module Guarded.Stream.Quantifiers where

open import Prelude
open import Data.Empty

open import LaterG
open import Guarded.Stream

private variable
  A B C : 𝒰

-- predicates on a stream

data Anyˢ (P : A → 𝒰) : Stream A → 𝒰 where
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

data Allˢ (P : A → 𝒰) : Stream A → 𝒰 where
  All-cons : ∀ {a s▹}
           → P a → ▹[ α ] (Allˢ P (s▹ α))
           → Allˢ P (cons a s▹)

Allˢ-map : {P : A → 𝒰} {Q : B → 𝒰} {f : A → B}
         → (∀ {x} → P x → Q (f x))
         → (s : Stream A)
         → Allˢ P s → Allˢ Q (mapˢ f s)
Allˢ-map {Q} {f} pq =
  fix λ prf▹ → λ where
    .(cons a s▹) (All-cons {a} {s▹} pa ps▹) →
       subst (Allˢ Q) (sym $ mapˢ-eq f a s▹) $
       All-cons (pq pa) (λ α → prf▹ α (s▹ α) (ps▹ α))

¬Any→All¬ : ∀ {P : A → 𝒰}
          → (s : Stream A) → ¬ (Anyˢ P s) → Allˢ (¬_ ∘ P) s
¬Any→All¬ {P} = fix λ prf▹ → λ where
  (cons h t▹) n →
    All-cons (n ∘ Any-here)
             (λ α → prf▹ α (t▹ α) (λ a → n (Any-there (λ β → subst (Anyˢ P) (tick-irr t▹ α β) a))))

-- other directions seem impossible ?

data Adjˢ (P : A → A → 𝒰) : Stream A → 𝒰 where
  Adj-cons : ∀ {a s▹}
           → ▹[ α ] P a (headˢ (s▹ α)) → ▹[ α ] (Adjˢ P (s▹ α))
           → Adjˢ P (cons a s▹)

repeat-adj : {P : A → A → 𝒰}
           → (∀ a → P a a)
           → ∀ a → Adjˢ P (repeatˢ a)
repeat-adj {P} Pr a =
  fix λ ih▹ → Adj-cons (λ α → transport (λ i → P a (headˢ (pfix (cons a) (~ i) α))) (Pr a))
                       (λ α → transport (λ i → Adjˢ P (pfix (cons a) (~ i) α)) (ih▹ α))
