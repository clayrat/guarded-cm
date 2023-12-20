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
  My : (A → B × ▹ Mealy A B) → Mealy A B

-- functor

mapᵐ-body : (B → C)
          → ▹ (Mealy A B → Mealy A C)
          → Mealy A B → Mealy A C
mapᵐ-body f m▹ (My tr) = My λ a → let btr' = tr a in
                            f (btr' .fst) , (m▹ ⊛ btr' .snd)

mapᵐ : (B → C)
     → Mealy A B → Mealy A C
mapᵐ f = fix (mapᵐ-body f)

-- profunctor / arrow

dimapᵐ-body : (D → A) → (B → C)
            → ▹ (Mealy A B → Mealy D C)
            → Mealy A B → Mealy D C
dimapᵐ-body f g d▹ (My tr) = My λ d → let btr' = tr (f d) in
                                g (btr' .fst) , (d▹ ⊛ btr' .snd)

dimapᵐ : (D → A) → (B → C)
       → Mealy A B → Mealy D C
dimapᵐ f g = fix (dimapᵐ-body f g)

firstᵐ-body : ▹ (Mealy A B → Mealy (A × C) (B × C))
            → Mealy A B → Mealy (A × C) (B × C)
firstᵐ-body f▹ (My tr) = My λ where (a , c) → let btr' = tr a in
                                      (btr' .fst , c) , (f▹ ⊛ btr' .snd)

firstᵐ : Mealy A B → Mealy (A × C) (B × C)
firstᵐ = fix firstᵐ-body

arrᵐ-body : (A → B) → ▹ Mealy A B → Mealy A B
arrᵐ-body f a▹ = My λ a → f a , a▹

arrᵐ : (A → B) → Mealy A B
arrᵐ f = fix (arrᵐ-body f)

-- TODO ArrowChoice / ArrowApply

-- applicative

pureᵐ-body : B → ▹ Mealy A B → Mealy A B
pureᵐ-body b p▹ = My λ _ → b , p▹

pureᵐ : B → Mealy A B
pureᵐ b = fix (pureᵐ-body b)

apᵐ-body : ▹ (Mealy A (B → C) → Mealy A B → Mealy A C)
         → Mealy A (B → C) → Mealy A B → Mealy A C
apᵐ-body a▹ (My trf) (My tra) = My λ a → let ftr = trf a
                                             btr = tra a
                                          in
                                         ftr .fst (btr .fst) , (a▹ ⊛ ftr .snd ⊛ btr .snd)

apᵐ : Mealy A (B → C) → Mealy A B → Mealy A C
apᵐ = fix apᵐ-body

-- category

idᵐ-body : ▹ Mealy A A → Mealy A A
idᵐ-body i▹ = My λ a → a , i▹

idᵐ : Mealy A A
idᵐ = fix idᵐ-body

-- aka cascade product
catᵐ-body : ▹ (Mealy A B → Mealy B C → Mealy A C)
          → Mealy A B → Mealy B C → Mealy A C
catᵐ-body c▹ (My tra) (My trb) = My λ a → let btr' = tra a
                                              ctr″ = trb (btr' .fst)
                                           in ctr″ .fst , (c▹ ⊛ btr' .snd ⊛ ctr″ .snd)

catᵐ : Mealy A B → Mealy B C → Mealy A C
catᵐ = fix catᵐ-body

-- aka direct product
prodᵐ-body : ▹ (Mealy A B → Mealy C D → Mealy (A × C) (B × D))
           → Mealy A B → Mealy C D → Mealy (A × C) (B × D)
prodᵐ-body p▹ (My tra) (My trc) = My λ where (a , c) →
                                               let btr = tra a
                                                   dtr = trc c
                                                 in
                                               (btr .fst , dtr .fst) , (p▹ ⊛ btr .snd ⊛ dtr .snd)

prodᵐ : Mealy A B → Mealy C D → Mealy (A × C) (B × D)
prodᵐ = fix prodᵐ-body

-- TODO monotone + trace ?
