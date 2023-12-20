{-# OPTIONS --guarded #-}
module Guarded.Mealy where

open import Prelude

open import LaterG

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  D : 𝒰 ℓ‴

-- Mealy machine

-- A = input, B = output
data Mealy (A : 𝒰 ℓ) (B : 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  Mly : (A → B × ▹ Mealy A B) → Mealy A B

-- functor

mapᵐ-body : (B → C)
          → ▹ (Mealy A B → Mealy A C)
          → Mealy A B → Mealy A C
mapᵐ-body f m▹ (Mly tr) = Mly λ a → let btr' = tr a in
                            f (btr' .fst) , (m▹ ⊛ btr' .snd)

mapᵐ : (B → C)
     → Mealy A B → Mealy A C
mapᵐ f = fix (mapᵐ-body f)

-- profunctor / arrow

dimapᵐ-body : (D → A) → (B → C)
            → ▹ (Mealy A B → Mealy D C)
            → Mealy A B → Mealy D C
dimapᵐ-body f g d▹ (Mly tr) = Mly λ d → let btr' = tr (f d) in
                                g (btr' .fst) , (d▹ ⊛ btr' .snd)

dimapᵐ : (D → A) → (B → C)
       → Mealy A B → Mealy D C
dimapᵐ f g = fix (dimapᵐ-body f g)

firstᵐ-body : ▹ (Mealy A B → Mealy (A × C) (B × C))
            → Mealy A B → Mealy (A × C) (B × C)
firstᵐ-body f▹ (Mly tr) = Mly λ where (a , c) → let btr' = tr a in
                                       (btr' .fst , c) , (f▹ ⊛ btr' .snd)

firstᵐ : Mealy A B → Mealy (A × C) (B × C)
firstᵐ = fix firstᵐ-body

arrᵐ-body : (A → B) → ▹ Mealy A B → Mealy A B
arrᵐ-body f a▹ = Mly λ a → f a , a▹

arrᵐ : (A → B) → Mealy A B
arrᵐ f = fix (arrᵐ-body f)

-- TODO ArrowChoice / ArrowApply

-- applicative

pureᵐ-body : B → ▹ Mealy A B → Mealy A B
pureᵐ-body b p▹ = Mly λ _ → b , p▹

pureᵐ : B → Mealy A B
pureᵐ b = fix (pureᵐ-body b)

apᵐ-body : ▹ (Mealy A (B → C) → Mealy A B → Mealy A C)
         → Mealy A (B → C) → Mealy A B → Mealy A C
apᵐ-body a▹ (Mly trf) (Mly tra) =
  Mly λ a → let ftr = trf a
                btr = tra a
             in
            ftr .fst (btr .fst) , (a▹ ⊛ ftr .snd ⊛ btr .snd)

apᵐ : Mealy A (B → C) → Mealy A B → Mealy A C
apᵐ = fix apᵐ-body

-- category

idᵐ-body : ▹ Mealy A A → Mealy A A
idᵐ-body i▹ = Mly λ a → a , i▹

idᵐ : Mealy A A
idᵐ = fix idᵐ-body

-- aka cascade product
catᵐ-body : ▹ (Mealy A B → Mealy B C → Mealy A C)
          → Mealy A B → Mealy B C → Mealy A C
catᵐ-body c▹ (Mly tra) (Mly trb) =
  Mly λ a → let btr' = tra a
                ctr″ = trb (btr' .fst)
             in
            ctr″ .fst , (c▹ ⊛ btr' .snd ⊛ ctr″ .snd)

catᵐ : Mealy A B → Mealy B C → Mealy A C
catᵐ = fix catᵐ-body

-- aka direct product
prodᵐ-body : ▹ (Mealy A B → Mealy C D → Mealy (A × C) (B × D))
           → Mealy A B → Mealy C D → Mealy (A × C) (B × D)
prodᵐ-body p▹ (Mly tra) (Mly trc) =
  Mly λ where (a , c) →
                let btr = tra a
                    dtr = trc c
                 in
                (btr .fst , dtr .fst) , (p▹ ⊛ btr .snd ⊛ dtr .snd)

prodᵐ : Mealy A B → Mealy C D → Mealy (A × C) (B × D)
prodᵐ = fix prodᵐ-body

-- TODO monotone + trace ?
