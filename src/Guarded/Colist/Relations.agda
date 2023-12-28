{-# OPTIONS --guarded #-}
module Guarded.Colist.Relations where

open import Prelude
open import Data.Empty
open import Data.List

open import LaterG
open import Guarded.Colist

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

data SubColist {A : 𝒰 ℓ} : Colist A → Colist A → 𝒰 ℓ where
  sub-cnil  : ∀ {bs}
            → SubColist cnil bs
  sub-ccons : ∀ {a as▹ bs▹} l
            → ▹[ α ] (SubColist (as▹ α) (bs▹ α))
            → SubColist (ccons a as▹) (catList l (ccons a bs▹))

SubColist-refl : (as : Colist A)
               → SubColist as as
SubColist-refl = fix λ ih▹ → λ where
   cnil          → sub-cnil
   (ccons a as▹) → sub-ccons [] (ih▹ ⊛ as▹)

SubColist-map : {f : A → B}
              → (as bs : Colist A)
              → SubColist as bs
              → SubColist (mapˡ f as) (mapˡ f bs)
SubColist-map {f} = fix λ ih▹ → λ where
  .cnil           bs                         sub-cnil                        → sub-cnil
  .(ccons a as▹) .(catList l (ccons a bs▹)) (sub-ccons {a} {as▹} {bs▹} l s▹) →
    subst (SubColist (mapˡ f (ccons a as▹))) (sym $ map-catList f l (ccons a bs▹)) $
    transport (λ i → SubColist (ccons (f a) (λ α → pfix (mapˡ-body f) (~ i) α (as▹ α)))
                               (catList (map f l) (ccons (f a) (λ α → pfix (mapˡ-body f) (~ i) α (bs▹ α))))) $
    sub-ccons (map f l) (ih▹ ⊛ as▹ ⊛′ bs▹ ⊛′ s▹)
