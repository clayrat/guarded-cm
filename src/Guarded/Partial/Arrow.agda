{-# OPTIONS --guarded #-}
module Guarded.Partial.Arrow where

open import Prelude
open import Data.Empty

open import LaterG
open import Guarded.Partial

private variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″
  D : 𝒰 ℓ‴

KPart : 𝒰 ℓ → 𝒰 ℓ′ → 𝒰 (ℓ ⊔ ℓ′)
KPart A B = A → Part B

dimapᵏᵖ : (C → A) → (B → D) → KPart A B → KPart C D
dimapᵏᵖ ca bd kp c = mapᵖ bd (kp (ca c))

pureᵏᵖ : (A → B) → KPart A B
pureᵏᵖ f = now ∘ f

compᵏᵖ : KPart A B → KPart B C → KPart A C
compᵏᵖ ab bc a = ab a >>=ᵖ bc
