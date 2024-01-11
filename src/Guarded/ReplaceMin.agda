{-# OPTIONS --guarded #-}
module Guarded.ReplaceMin where

open import Prelude
open import Data.Bool hiding (_==_)
open import Data.Dec
open import Data.Nat
open import Data.List
open import LaterG

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

feedback : (▹ A → B × A) → B
feedback f = fst (fix (f ∘ (snd ⍉_)))

-- Bird's algorithm

data Tree (A : 𝒰 ℓ) : 𝒰 ℓ where
  Leaf : A → Tree A
  Br   : Tree A → Tree A → Tree A

-- body

replaceMinBody : Tree ℕ → ▹ ℕ → ▹ (Tree ℕ) × ℕ
replaceMinBody (Leaf x) n▹ = Leaf ⍉ n▹ , x
replaceMinBody (Br l r) n▹ =
  let (l▹ , nl) = replaceMinBody l n▹
      (r▹ , nr) = replaceMinBody r n▹
    in
  (Br ⍉ l▹ ⊛ r▹) , min nl nr

-- main function

replaceMin : Tree ℕ → ▹ Tree ℕ
replaceMin t = feedback (replaceMinBody t)

-- specification

-- map-reduce
fold-tree : (A → B) → (B → B → B) → Tree A → B
fold-tree fl fn (Leaf x) = fl x
fold-tree fl fn (Br l r) = fn (fold-tree fl fn l) (fold-tree fl fn r)

shape : Tree A → Tree ⊤
shape = fold-tree (λ _ → Leaf tt) Br

allt : (A → Bool) → Tree A → Bool
allt p = fold-tree p _and_

min-tree : Tree ℕ → ℕ
min-tree = fold-tree id min

-- output ▹tree has the same shape
rmb-shape : (t : Tree ℕ) → (n▹ : ▹ ℕ)
          → shape ⍉ fst (replaceMinBody t n▹) ＝ next (shape t)
rmb-shape (Leaf x) n▹ = ▹-ext (next refl)
rmb-shape (Br l r) n▹ = ▹-ext λ α →
  ap² Br (▹-ap (rmb-shape l n▹) α)
         (▹-ap (rmb-shape r n▹) α)

-- all data in the output ▹tree is replaced by second parameter
rmb-all : (t : Tree ℕ) → (n▹ : ▹ ℕ)
        → ((allt ∘ _==_) ⍉ n▹ ⊛ fst (replaceMinBody t n▹)) ＝ next true
rmb-all (Leaf x) n▹ = ▹-ext λ α →
  Reflects′.reflects-true (==-reflects (n▹ α) (n▹ α)) refl
rmb-all (Br l r) n▹ = ▹-ext λ α →
  ap² _and_ (▹-ap (rmb-all l n▹) α)
            (▹-ap (rmb-all r n▹) α)

-- resulting number is the minimum
rmb-min : (t : Tree ℕ) → (n▹ : ▹ ℕ)
        → snd (replaceMinBody t n▹) ＝ min-tree t
rmb-min (Leaf x) n▹ = refl
rmb-min (Br l r) n▹ = ap² min (rmb-min l n▹) (rmb-min r n▹)

-- main properties

rm-shape : (t : Tree ℕ)
         → shape ⍉ (replaceMin t) ＝ next (shape t)
rm-shape t =
  let fx : ▹ (▹ (Tree ℕ) × ℕ) → ▹ (Tree ℕ) × ℕ
      fx x = replaceMinBody t (snd ⍉ x)
      nx = snd (fix fx)
    in
  ▹-ext λ α →
    (shape ⍉ (replaceMin t)) α
      ＝⟨⟩
    shape (fst (fix fx) α)
      ＝⟨ ap shape (▹-ap (ap fst (fix-path fx)) α) ⟩
    shape (fst (replaceMinBody t (next nx)) α)
      ＝⟨ ▹-ap (rmb-shape t (next nx)) α ⟩
    shape t
      ∎

rm-min : (t : Tree ℕ)
       → (allt (min-tree t ==_)) ⍉ (replaceMin t) ＝ next true
rm-min t =
  let fx : ▹ (▹ (Tree ℕ) × ℕ) → ▹ (Tree ℕ) × ℕ
      fx x = replaceMinBody t (snd ⍉ x)
      nx = snd (fix fx)
    in
  ▹-ext λ α →
    ((allt (min-tree t ==_)) ⍉ (replaceMin t)) α
      ＝⟨⟩
    allt (min-tree t ==_) (fst (fix fx) α)
      ＝⟨ ap (allt (min-tree t ==_)) (▹-ap (ap fst (fix-path fx)) α) ⟩
    allt (min-tree t ==_) (fst (replaceMinBody t (next nx)) α)
      ＝⟨ ap (λ q → allt (q ==_) (fst (replaceMinBody t (next nx)) α)) (sym $ rmb-min t _) ⟩
    allt (nx ==_) (fst (replaceMinBody t (next nx)) α)
      ＝⟨ ▹-ap (rmb-all t (next nx)) α ⟩
    true
      ∎

-- non-empty list version

replaceMinListBody : ℕ → List ℕ → ▹ ℕ → ▹ (List ℕ) × ℕ
replaceMinListBody x []       n▹ = [_] ⍉ n▹ , x
replaceMinListBody x (y ∷ ys) n▹ =
  let (l▹ , nl) = replaceMinListBody y ys n▹
    in
  (_∷_ ⍉ n▹ ⊛ l▹) , min x nl

replaceMinList : ℕ → List ℕ → ▹ List ℕ
replaceMinList x l = feedback (replaceMinListBody x l)

