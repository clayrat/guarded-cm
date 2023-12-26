{-# OPTIONS --guarded #-}
module Clocked.Computation1.Termination where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Nat

open import Later
open import Clocked.Computation1

private variable
  ℓ  : Level
  A : 𝒰 ℓ

data TmWith {A : 𝒰 ℓ} : Comp A → A → 𝒰 ℓ where
  tmret : ∀ {c : Comp A} {a}
        → c ＝ ret a
        → TmWith c a
  tmbind : ∀ {c : Comp A} {a b} {k : A → Comp A} {x : Comp A}
         → c ＝ bind k x
         → TmWith x a
         → TmWith (k a) b
         → TmWith c b

TmWith-det : ∀ {c : Comp A} {x y : A}
           → TmWith c x → TmWith c y → x ＝ y
TmWith-det (tmret ex)                                     (tmret ey)                                     = ret-inj (sym ex ∙ ey)
TmWith-det (tmret ex)                                     (tmbind ey tya tyb)                            = absurd (ret≠bind (sym ex ∙ ey))
TmWith-det (tmbind ex txa txb)                            (tmret ey)                                     = absurd (ret≠bind (sym ey ∙ ex))
TmWith-det (tmbind {a = ax} {b = bx} {k = kx} ex txa txb) (tmbind {a = ay} {b = by} {k = ky} ey tya tyb) =
  let (ex , ek) = bind-inj (sym ex ∙ ey)
      ea = TmWith-det txa (subst (λ q → TmWith q ay) (sym ex) tya)
    in
  TmWith-det txb (subst (λ q → TmWith q by) (sym (happly ek ax)) $
                  subst (λ q → TmWith (ky q) by) (sym ea) tyb)

Tm : Comp A → 𝒰 (level-of-type A)
Tm {A} c = Σ[ a ꞉ A ] TmWith c a  -- TODO truncate?

data InvokedBy {A : 𝒰 ℓ} : Comp A → Comp A → 𝒰 ℓ where
  iprev : ∀ {c : Comp A} {k : A → Comp A} {x : Comp A}
        → c ＝ bind k x
        → InvokedBy x c
  ifun : ∀ {c : Comp A} {k : A → Comp A} {x : Comp A} {a : A}
       → c ＝ bind k x
       → TmWith x a
       → InvokedBy (k a) c

notInvRet : {c : Comp A} {a : A} → ¬ (InvokedBy c (ret a))
notInvRet (iprev e)  = absurd (ret≠bind e)
notInvRet (ifun e _) = absurd (ret≠bind e)

data Safe {A : 𝒰 ℓ} : Comp A → 𝒰 ℓ where
  sf : ∀ {c : Comp A}
     → (∀ {d : Comp A} → InvokedBy d c → Safe d)
     → Safe c

Safe-is-prop : (c : Comp A) → is-prop (Safe c)
Safe-is-prop c = is-prop-η (go c)
  where
  go : (c : Comp A) (p q : Safe c) → p ＝ q
  go c (sf sp) (sf sq) = ap sf (fun-ext-implicit λ {d} → fun-ext λ inv → go d (sp inv) (sq inv))
