{-# OPTIONS --guarded #-}
module Guarded.Domain where

open import Prelude
open import LaterG
open import Guarded.PartialG

private variable
  A B : 𝒰

-- guarded domains

D-body : ▹ 𝒰 → 𝒰
D-body D▹ = Part (▸ (λ α → D▹ α → D▹ α))

D : 𝒰
D = fix D-body

inD : Part (▹ (D → D)) → D
inD = transport (sym (fix-path D-body))

outD : D → Part (▹ (D → D))
outD = transport (fix-path D-body)

δ : Part D → D
δ d = inD (d >>=ᵖ outD)

App : D → D → D
App d1 d2 = δ (outD d1 >>=ᵖ (λ f▹ → later (λ α → now (f▹ α d2))))

Lam : (D → D) → D
Lam f = inD (now (next f))
