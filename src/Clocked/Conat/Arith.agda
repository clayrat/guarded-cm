{-# OPTIONS --guarded #-}
module Clocked.Conat.Arith where

open import Prelude
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.Maybe
open import Structures.IdentitySystem

open import Later
open import Clocked.Conat

private variable
  k : Cl

data _≤ᵏ_ : ℕ∞ᵏ k → ℕ∞ᵏ k → 𝒰 where
  z≤ᵏn : ∀ {k n}                              → coze {k} ≤ᵏ n
  s≤ᵏs : ∀ {m▹ n▹} → ▹[ α ∶ k ] (m▹ α ≤ᵏ n▹ α) → cosu m▹ ≤ᵏ cosu n▹

¬s≤ᵏz : (x▹ : ▹ k (ℕ∞ᵏ k)) → ¬ (cosu x▹ ≤ᵏ coze)
¬s≤ᵏz x▹ ()

≤ᵏ-refl : (x : ℕ∞ᵏ k) → x ≤ᵏ x
≤ᵏ-refl {k} = fix {k = k} λ prf▹ → λ where
  coze      → z≤ᵏn
  (cosu x▹) → s≤ᵏs (prf▹ ⊛ x▹)

≤ᵏ-trans : (x y z : ℕ∞ᵏ k) → x ≤ᵏ y → y ≤ᵏ z → x ≤ᵏ z
≤ᵏ-trans {k} = fix {k = k} λ prf▹ → λ where
  .coze       y          z          z≤ᵏn                           _                             →
    z≤ᵏn
  .(cosu x▹) .(cosu y▹) .(cosu z▹) (s≤ᵏs {m▹ = x▹} {n▹ = y▹} xy▹) (s≤ᵏs {m▹ = y▹} {n▹ = z▹} yz▹) →
    s≤ᵏs λ α → prf▹ α (x▹ α) (y▹ α) (z▹ α) (xy▹ α) (yz▹ α)

≤ᵏ-antisym : (x y : ℕ∞ᵏ k) → x ≤ᵏ y → y ≤ᵏ x → x ＝ y
≤ᵏ-antisym {k} = fix {k = k} λ prf▹ → λ where
  .coze      .coze       z≤ᵏn                           z≤ᵏn                          →
    refl
  .(cosu x▹) .(cosu y▹) (s≤ᵏs {m▹ = x▹} {n▹ = y▹} xy▹) (s≤ᵏs {m▹ = y▹} {n▹ = x▹} yx▹) →
    ap cosu (▹-ext (λ α → prf▹ α (x▹ α) (y▹ α) (xy▹ α) (yx▹ α)))

≤ᵏ-infty : (x : ℕ∞ᵏ k) → x ≤ᵏ inftyᵏ
≤ᵏ-infty {k} = fix {k = k} λ prf▹ → λ where
  coze      → z≤ᵏn
  (cosu x▹) → s≤ᵏs (subst (λ q → ▹[ α ∶ k ] (x▹ α ≤ᵏ q α))
                          (sym $ pfix cosu)
                          (prf▹ ⊛ x▹))

-- interleaving style

-- minimum

minᵏ-body : ▹ k (ℕ∞ᵏ k → ℕ∞ᵏ k → ℕ∞ᵏ k) → ℕ∞ᵏ k → ℕ∞ᵏ k → ℕ∞ᵏ k
minᵏ-body m▹  coze      _        = coze
minᵏ-body m▹ (cosu _)   coze     = coze
minᵏ-body m▹ (cosu x▹) (cosu y▹) = cosu (m▹ ⊛ x▹ ⊛ y▹)

minᵏ : ℕ∞ᵏ k → ℕ∞ᵏ k → ℕ∞ᵏ k
minᵏ = fix minᵏ-body

minᵏ-zerol : (x : ℕ∞ᵏ k) → minᵏ coze x ＝ coze
minᵏ-zerol x = refl

minᵏ-zeror : (x : ℕ∞ᵏ k) → minᵏ x coze ＝ coze
minᵏ-zeror  coze     = refl
minᵏ-zeror (cosu x▹) = refl

minᵏ-idemp : (x : ℕ∞ᵏ k) → minᵏ x x ＝ x
minᵏ-idemp {k} = fix {k = k} λ prf▹ → λ where
  coze      → refl
  (cosu x▹) → ap (λ q → cosu (q ⊛ x▹ ⊛ x▹)) (pfix minᵏ-body)
            ∙ ap cosu (▹-ext (prf▹ ⊛ x▹))

minᵏ-comm : (x y : ℕ∞ᵏ k) → minᵏ x y ＝ minᵏ y x
minᵏ-comm {k} = fix {k = k} λ prf▹ → λ where
  coze       y        → sym (minᵏ-zeror y)
  (cosu x▹)  coze     → refl
  (cosu x▹) (cosu y▹) → ap (λ q → cosu (q ⊛ x▹ ⊛ y▹)) (pfix minᵏ-body)
                      ∙ ap cosu (▹-ext λ α → prf▹ α (x▹ α) (y▹ α))
                      ∙ ap (λ q → cosu (q ⊛ y▹ ⊛ x▹)) (sym $ pfix minᵏ-body)

minᵏ-assoc : (x y z : ℕ∞ᵏ k) → minᵏ x (minᵏ y z) ＝ minᵏ (minᵏ x y) z
minᵏ-assoc {k} = fix {k = k} λ prf▹ → λ where
  coze      y         z         → refl
  (cosu x▹) coze      z         → refl
  (cosu x▹) (cosu y▹) coze      → refl
  (cosu x▹) (cosu y▹) (cosu z▹) →
      ap (λ q → cosu ((dfix minᵏ-body) ⊛ x▹ ⊛ (q ⊛ y▹ ⊛ z▹))) (pfix minᵏ-body)
    ∙ ap (λ q → cosu (q ⊛ x▹ ⊛ ((next minᵏ) ⊛ y▹ ⊛ z▹))) (pfix minᵏ-body)
    ∙ ap cosu (▹-ext (λ α → prf▹ α (x▹ α) (y▹ α) (z▹ α)))
    ∙ ap (λ q → cosu (q ⊛ ((next minᵏ) ⊛ x▹ ⊛ y▹) ⊛ z▹)) (sym $ pfix minᵏ-body)
    ∙ ap (λ q → cosu ((dfix minᵏ-body) ⊛ (q ⊛ x▹ ⊛ y▹) ⊛ z▹)) (sym $ pfix minᵏ-body)

minᵏ-inftyl : (x : ℕ∞ᵏ k) → minᵏ inftyᵏ x ＝ x
minᵏ-inftyl {k} = fix {k = k} λ prf▹ → λ where
  coze      → refl
  (cosu x▹) → ap (λ q → minᵏ q (cosu x▹)) (fix-path cosu)
            ∙ ap (λ q → cosu (q ⊛ (next inftyᵏ) ⊛ x▹)) (pfix minᵏ-body)
            ∙ ap cosu (▹-ext (prf▹ ⊛ x▹))

minᵏ-inftyr : (x : ℕ∞ᵏ k) → minᵏ x inftyᵏ ＝ x
minᵏ-inftyr x = minᵏ-comm x inftyᵏ ∙ minᵏ-inftyl x

≤ᵏ-min-l : (x y : ℕ∞ᵏ k) → minᵏ x y ≤ᵏ x
≤ᵏ-min-l {k} = fix {k = k} λ prf▹ → λ where
  coze      y         → z≤ᵏn
  (cosu x▹) coze      → z≤ᵏn
  (cosu x▹) (cosu y▹) → s≤ᵏs (subst (λ q → ▹[ α ∶ k ] ((q ⊛ x▹ ⊛ y▹) α ≤ᵏ x▹ α))
                                    (sym $ pfix minᵏ-body)
                                    (λ α → prf▹ α (x▹ α) (y▹ α)))

≤ᵏ-min-r : (x y : ℕ∞ᵏ k) → minᵏ x y ≤ᵏ y
≤ᵏ-min-r x y = subst (_≤ᵏ y) (minᵏ-comm y x) (≤ᵏ-min-l y x)

-- maximum

maxᵏ-body : ▹ k (ℕ∞ᵏ k → ℕ∞ᵏ k → ℕ∞ᵏ k) → ℕ∞ᵏ k → ℕ∞ᵏ k → ℕ∞ᵏ k
maxᵏ-body m▹  coze      y        = y
maxᵏ-body m▹ (cosu x▹)  coze     = cosu x▹
maxᵏ-body m▹ (cosu x▹) (cosu y▹) = cosu (m▹ ⊛ x▹ ⊛ y▹)

maxᵏ : ℕ∞ᵏ k → ℕ∞ᵏ k → ℕ∞ᵏ k
maxᵏ = fix maxᵏ-body

maxᵏ-zerol : (x : ℕ∞ᵏ k) → maxᵏ coze x ＝ x
maxᵏ-zerol x = refl

maxᵏ-zeror : (x : ℕ∞ᵏ k) → maxᵏ x coze ＝ x
maxᵏ-zeror  coze     = refl
maxᵏ-zeror (cosu x▹) = refl

maxᵏ-idemp : (x : ℕ∞ᵏ k) → maxᵏ x x ＝ x
maxᵏ-idemp {k} = fix {k = k} λ prf▹ → λ where
  coze      → refl
  (cosu x▹) → ap (λ q → cosu (q ⊛ x▹ ⊛ x▹)) (pfix maxᵏ-body)
            ∙ ap cosu (▹-ext (prf▹ ⊛ x▹))

maxᵏ-comm : (x y : ℕ∞ᵏ k) → maxᵏ x y ＝ maxᵏ y x
maxᵏ-comm {k} = fix {k = k} λ prf▹ → λ where
  coze       y        → sym (maxᵏ-zeror y)
  (cosu x▹)  coze     → refl
  (cosu x▹) (cosu y▹) → ap (λ q → cosu (q ⊛ x▹ ⊛ y▹)) (pfix maxᵏ-body)
                      ∙ ap cosu (▹-ext λ α → prf▹ α (x▹ α) (y▹ α))
                      ∙ ap (λ q → cosu (q ⊛ y▹ ⊛ x▹)) (sym $ pfix maxᵏ-body)

maxᵏ-assoc : (x y z : ℕ∞ᵏ k) → maxᵏ x (maxᵏ y z) ＝ maxᵏ (maxᵏ x y) z
maxᵏ-assoc {k} = fix {k = k} λ prf▹ → λ where
  coze      y         z         → refl
  (cosu x▹) coze      z         → refl
  (cosu x▹) (cosu y▹) coze      → refl
  (cosu x▹) (cosu y▹) (cosu z▹) →
      ap (λ q → cosu ((dfix maxᵏ-body) ⊛ x▹ ⊛ (q ⊛ y▹ ⊛ z▹))) (pfix maxᵏ-body)
    ∙ ap (λ q → cosu (q ⊛ x▹ ⊛ ((next maxᵏ) ⊛ y▹ ⊛ z▹))) (pfix maxᵏ-body)
    ∙ ap cosu (▹-ext (λ α → prf▹ α (x▹ α) (y▹ α) (z▹ α)))
    ∙ ap (λ q → cosu (q ⊛ ((next maxᵏ) ⊛ x▹ ⊛ y▹) ⊛ z▹)) (sym $ pfix maxᵏ-body)
    ∙ ap (λ q → cosu ((dfix maxᵏ-body) ⊛ (q ⊛ x▹ ⊛ y▹) ⊛ z▹)) (sym $ pfix maxᵏ-body)

maxᵏ-inftyl : (x : ℕ∞ᵏ k) → maxᵏ inftyᵏ x ＝ inftyᵏ
maxᵏ-inftyl {k} = fix {k = k} λ prf▹ → λ where
  coze      → refl
  (cosu x▹) → ap (λ q → maxᵏ q (cosu x▹)) (fix-path cosu)
            ∙ ap (λ q → cosu (q ⊛ (next inftyᵏ) ⊛ x▹)) (pfix maxᵏ-body)
            ∙ ap cosu (▹-ext (prf▹ ⊛ x▹))
            ∙ sym (fix-path cosu)

maxᵏ-inftyr : (x : ℕ∞ᵏ k) → maxᵏ x inftyᵏ ＝ inftyᵏ
maxᵏ-inftyr x = maxᵏ-comm x inftyᵏ ∙ maxᵏ-inftyl x

≤ᵏ-max-l : (x y : ℕ∞ᵏ k) → x ≤ᵏ maxᵏ x y
≤ᵏ-max-l {k} = fix {k = k} λ prf▹ → λ where
  coze      y         → z≤ᵏn
  (cosu x▹) coze      → ≤ᵏ-refl (cosu x▹)
  (cosu x▹) (cosu y▹) → s≤ᵏs (subst (λ q → ▹[ α ∶ k ] (x▹ α ≤ᵏ (q ⊛ x▹ ⊛ y▹) α))
                                    (sym $ pfix maxᵏ-body)
                                    (λ α → prf▹ α (x▹ α) (y▹ α)))

≤ᵏ-max-r : (x y : ℕ∞ᵏ k) → y ≤ᵏ maxᵏ x y
≤ᵏ-max-r x y = subst (y ≤ᵏ_) (maxᵏ-comm y x) (≤ᵏ-max-l y x)

-- addition

+ᵏ-body : ▹ k (ℕ∞ᵏ k → ℕ∞ᵏ k → ℕ∞ᵏ k) → ℕ∞ᵏ k → ℕ∞ᵏ k → ℕ∞ᵏ k
+ᵏ-body a▹  coze      coze     = coze
+ᵏ-body a▹ (cosu x▹)  coze     = cosu x▹
+ᵏ-body a▹  coze     (cosu y▹) = cosu y▹
+ᵏ-body a▹ (cosu x▹) (cosu y▹) = cosu (next (cosu (a▹ ⊛ x▹ ⊛ y▹)))

_+ᵏ_ : ℕ∞ᵏ k → ℕ∞ᵏ k → ℕ∞ᵏ k
_+ᵏ_ = fix +ᵏ-body

+ᵏ-zerol : (x : ℕ∞ᵏ k) → coze +ᵏ x ＝ x
+ᵏ-zerol  coze     = refl
+ᵏ-zerol (cosu x▹) = refl

+ᵏ-zeror : (x : ℕ∞ᵏ k) → x +ᵏ coze ＝ x
+ᵏ-zeror  coze     = refl
+ᵏ-zeror (cosu x▹) = refl

+ᵏ-comm : (x y : ℕ∞ᵏ k) → x +ᵏ y ＝ y +ᵏ x
+ᵏ-comm {k} = fix {k = k} λ prf▹ → λ where
  coze       coze      → refl
  coze      (cosu x▹)  → refl
  (cosu x▹)  coze      → refl
  (cosu x▹) (cosu y▹)  →
    (cosu x▹ +ᵏ cosu y▹)
      ＝⟨⟩
    cosu (next (cosu (dfix +ᵏ-body ⊛ x▹ ⊛ y▹)))
      ＝⟨ ap (λ q → cosu (next (cosu (q ⊛ x▹ ⊛ y▹)))) (pfix +ᵏ-body) ⟩
    cosu (next (cosu ((next _+ᵏ_) ⊛ x▹ ⊛ y▹)))
      ＝⟨ ap cosu (▹-ext (next (ap cosu (▹-ext λ α → prf▹ α (x▹ α) (y▹ α))))) ⟩
    cosu (next (cosu ((next _+ᵏ_) ⊛ y▹ ⊛ x▹)))
      ＝⟨ ap (λ q → cosu (next (cosu (q ⊛ y▹ ⊛ x▹)))) (sym $ pfix +ᵏ-body) ⟩
    cosu (next (cosu (dfix +ᵏ-body ⊛ y▹ ⊛ x▹)))
      ＝⟨⟩
    (cosu y▹ +ᵏ cosu x▹)
      ∎

+ᵏ-inftyl : (x : ℕ∞ᵏ k) → inftyᵏ +ᵏ x ＝ inftyᵏ
+ᵏ-inftyl {k} = fix {k = k} λ prf▹ → λ where
  coze      → refl
  (cosu x▹) →
     inftyᵏ +ᵏ cosu x▹
       ＝⟨ ap (_+ᵏ cosu x▹) (fix-path cosu) ⟩
     cosu (next (cosu ((dfix +ᵏ-body) ⊛ (next inftyᵏ) ⊛ x▹)))
       ＝⟨ ap (λ q → cosu (next (cosu (q ⊛ (next inftyᵏ) ⊛ x▹)))) (pfix +ᵏ-body) ⟩
     cosu (next (cosu ((next _+ᵏ_) ⊛ next inftyᵏ ⊛ x▹)))
       ＝⟨ ap cosu (▹-ext (λ _ → ap cosu (▹-ext (prf▹ ⊛ x▹)))) ⟩
     cosu (next (cosu (next (fix cosu))))
       ＝⟨ ap cosu (▹-ext (λ _ → sym $ fix-path cosu)) ⟩
     cosu (next inftyᵏ)
       ＝⟨ sym $ fix-path cosu ⟩
     inftyᵏ
       ∎

+ᵏ-inftyr : (x : ℕ∞ᵏ k) → x +ᵏ inftyᵏ ＝ inftyᵏ
+ᵏ-inftyr x = +ᵏ-comm x inftyᵏ ∙ +ᵏ-inftyl x

_+ᶜ_ : ℕ∞ → ℕ∞ → ℕ∞
_+ᶜ_ x y k = (x k) +ᵏ (y k)

+ᶜ-comm : (x y : ℕ∞) → x +ᶜ y ＝ y +ᶜ x
+ᶜ-comm x y = fun-ext λ k → +ᵏ-comm (x k) (y k)

-- concatenation style
+:ᵏ-body : ℕ∞ᵏ k → ▹ k (ℕ∞ᵏ k → ℕ∞ᵏ k) → ℕ∞ᵏ k → ℕ∞ᵏ k
+:ᵏ-body x ax▹  coze    = x
+:ᵏ-body x ax▹ (cosu y) = cosu (ax▹ ⊛ y)

_+:ᵏ_ : ℕ∞ᵏ k → ℕ∞ᵏ k → ℕ∞ᵏ k
_+:ᵏ_ x = fix (+:ᵏ-body x)

+:ᵏ-zerol : (x : ℕ∞ᵏ k) → coze +:ᵏ x ＝ x
+:ᵏ-zerol {k} = fix {k = k} λ prf▹ → λ where
  coze     → refl
  (cosu x) → cosu (dfix (+:ᵏ-body coze) ⊛ x)
               ＝⟨ ap (λ q → cosu (q ⊛ x)) (pfix (+:ᵏ-body coze) ) ⟩
             cosu (▹map (coze +:ᵏ_) x)
               ＝⟨ ap cosu (▹-ext (prf▹ ⊛ x)) ⟩
             cosu x
               ∎

+:ᵏ-zeror : (x : ℕ∞ᵏ k) → x +ᵏ coze ＝ x
+:ᵏ-zeror  coze     = refl
+:ᵏ-zeror (cosu x▹) = refl

-- +ᵏ-sucl doesn't seem to be provable easily

+:ᵏ-sucr : (x : ℕ∞ᵏ k) → (y▹ : ▹ k (ℕ∞ᵏ k))
        → x +:ᵏ (cosu y▹) ＝ cosu (▹map (x +:ᵏ_) y▹)
+:ᵏ-sucr x y▹ = ap (_$ (cosu y▹)) (fix-path (+:ᵏ-body x))

-- TODO https://proofassistants.stackexchange.com/questions/1545/how-to-prove-that-addition-is-commutative-for-conatural-numbers-in-coq
