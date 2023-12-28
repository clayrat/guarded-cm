{-# OPTIONS --guarded #-}
module Guarded.Mealy.Run where

open import Prelude
open import Data.Maybe
open import Data.List

open import LaterG
open import Guarded.Mealy
open import Guarded.Stream
open import Guarded.Colist
open import Guarded.Partial

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- Mealy machine corresponds to a causal stream function

runStream-body : ▹ (Mealy A B → Stream A → Stream B)
               → Mealy A B → Stream A → Stream B
runStream-body r▹ (Mly tr) (cons a as▹) = let (b , t▹) = tr a in
                                          cons b (r▹ ⊛ t▹ ⊛ as▹)

runStream : Mealy A B → Stream A → Stream B
runStream = fix runStream-body

runColist-body : ▹ (Mealy A B → Colist A → Colist B)
               → Mealy A B → Colist A → Colist B
runColist-body r▹  m       cnil        = cnil
runColist-body r▹ (Mly f) (ccons a c▹) = let (b , t▹) = f a in
                                         ccons b (r▹ ⊛ t▹ ⊛ c▹)

runColist : Mealy A B → Colist A → Colist B
runColist = fix runColist-body

runList-body : ▹ (Mealy A B → List A → Part (List B))
             → Mealy A B → List A → Part (List B)
runList-body r▹  m      []      = now []
runList-body r▹ (Mly f) (a ∷ l) = let (b , t▹) = f a in
                                  later (▹map (mapᵖ (b ∷_)) (r▹ ⊛ t▹ ⊛ next l))

runList : Mealy A B → List A → Part (List B)
runList = fix runList-body

