{-# OPTIONS --guarded #-}
module Guarded.Colist where

open import Prelude
open import Data.Maybe
open import Data.Nat
open import Data.List

open import LaterG

private variable
  A B C : 𝒰

-- guarded colists

data Colist (A : 𝒰) : 𝒰 where
  cnil  : Colist A
  ccons : A → ▹ Colist A → Colist A

-- singleton

singletonˡ : A → Colist A
singletonˡ a = ccons a (next cnil)

-- repeat

repeatˡ : A → Colist A
repeatˡ a = fix (ccons a)

-- uncons

unconsˡ : Colist A -> Maybe (A × ▹ Colist A)
unconsˡ  cnil         = nothing
unconsˡ (ccons a as▹) = just (a , as▹)

-- fromList

fromList : List A → Colist A
fromList []      = cnil
fromList (x ∷ l) = ccons x (next (fromList l))

-- append

appendˡ-body : ▹ (Colist A → Colist A → Colist A) → Colist A → Colist A → Colist A
appendˡ-body ap▹  cnil         t = t
appendˡ-body ap▹ (ccons x xs▹) t = ccons x ((ap▹ ⊛ xs▹) ⊛ next t)

appendˡ : Colist A → Colist A → Colist A
appendˡ = fix appendˡ-body

-- map

mapˡ-body : (A → B) → ▹ (Colist A → Colist B) → Colist A → Colist B
mapˡ-body f mp▹  cnil         = cnil
mapˡ-body f mp▹ (ccons x xs▹) = ccons (f x) (mp▹ ⊛ xs▹)

mapˡ : (A → B) → Colist A → Colist B
mapˡ f = fix (mapˡ-body f)

-- zipWith

zipWithˡ-body : (A → B → C) → ▹ (Colist A → Colist B → Colist C) → Colist A → Colist B → Colist C
zipWithˡ-body f zw▹  cnil          cnil         = cnil
zipWithˡ-body f zw▹  cnil         (ccons _ _  ) = cnil
zipWithˡ-body f zw▹ (ccons _ _  )  cnil         = cnil
zipWithˡ-body f zw▹ (ccons a as▹) (ccons b bs▹) = ccons (f a b) (zw▹ ⊛ as▹ ⊛ bs▹)

zipWithˡ : (A → B → C) → Colist A → Colist B → Colist C
zipWithˡ f = fix (zipWithˡ-body f)

-- intersperse

prepend-to-allˡ-body : A → ▹ (Colist A → Colist A) → Colist A → Colist A
prepend-to-allˡ-body sep p▹  cnil         = cnil
prepend-to-allˡ-body sep p▹ (ccons x xs▹) = ccons sep (next (ccons x (p▹ ⊛ xs▹)))

prepend-to-allˡ : A → Colist A → Colist A
prepend-to-allˡ sep = fix (prepend-to-allˡ-body sep)

intersperseˡ : A → Colist A → Colist A
intersperseˡ sep  cnil         = cnil
intersperseˡ sep (ccons x xs▹) = ccons x (▹map (prepend-to-allˡ sep) xs▹)

-- foldr

foldrˡ-body : (A → ▹ B → B) → B → ▹ (Colist A → B) → Colist A → B
foldrˡ-body f z f▹  cnil         = z
foldrˡ-body f z f▹ (ccons x xs▹) = f x (f▹ ⊛ xs▹)

foldrˡ : (A → ▹ B → B) → Colist A → B → B
foldrˡ f c z = fix (foldrˡ-body f z) c


