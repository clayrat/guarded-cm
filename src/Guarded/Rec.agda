{-# OPTIONS --guarded #-}
module Guarded.Rec where

open import Prelude
open import Data.Empty
open import Data.Unit
open import LaterG

{-
data Rec : 𝒰 → 𝒰 where
  MkRec : (▹ Rec A → A) → Rec A
-}

Rec-body : 𝒰 → ▹ 𝒰 → 𝒰
Rec-body A N▹ = ▸ N▹ → A

Rec : 𝒰 → 𝒰
Rec A = fix (Rec-body A)

Neg : 𝒰
Neg = Rec ⊥

-- we can move forward in time ...
contra : ¬ Neg
contra ev = transport (fix-path (Rec-body ⊥)) ev (next ev)

Neg≃⊥ : Neg ≃ ⊥
Neg≃⊥ = ¬-extₑ contra id

{-
-- ... but not backwards
evidence : Neg
evidence =
  λ neg▸ →
    let neg▹ = the (▹ Neg) (subst (λ q → ▸ q) (pfix (Rec-body ⊥)) neg▸) in
    contra {!!}

bot : ⊥
bot = contra evidence
-}

NegU : 𝒰
NegU = Rec ⊤

pt : NegU
pt _ = tt

NegU≃⊤ : NegU ≃ ⊤
NegU≃⊤ =
  is-contr→equiv-⊤ (is-contr-η (pt , λ n → fun-ext (λ q → refl)))

