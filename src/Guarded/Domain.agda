{-# OPTIONS --guarded #-}
module Guarded.Domain where

open import Prelude

open import LaterG
open import Guarded.Partial

-- guarded domains

D-body : ▹ 𝒰 → 𝒰
D-body D▹ = Part (▹[ α ] (D▹ α → D▹ α))

D : 𝒰
D = fix D-body

⇉D : Part (▹ (D → D)) → D
⇉D = transport (sym $ fix-path D-body)

D⇉ : D → Part (▹ (D → D))
D⇉ = transport (fix-path D-body)

δ : Part D → D
δ d = ⇉D (d >>=ᵖ D⇉)

App : D → D → D
App d1 d2 = δ (D⇉ d1 >>=ᵖ λ f▹ → later (▹map now (f▹ ⊛ next d2)))

Lam : (D → D) → D
Lam = ⇉D ∘ now ∘ next
