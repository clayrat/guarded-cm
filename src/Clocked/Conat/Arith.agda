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

-- partial order

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

≤ᵏ-inc : (x : ℕ∞ᵏ k) → x ≤ᵏ incᵏ x
≤ᵏ-inc {k} = fix {k = k} λ prf▹ → λ where
  coze      → z≤ᵏn
  (cosu x▹) → s≤ᵏs (transport▹ (λ i α → x▹ α ≤ᵏ cosu (λ α₁ → tick-irr x▹ α α₁ i))
                               (prf▹ ⊛ x▹))

≤ᵏ-infty : (x : ℕ∞ᵏ k) → x ≤ᵏ inftyᵏ
≤ᵏ-infty {k} = fix {k = k} λ prf▹ → λ where
  coze      → z≤ᵏn
  (cosu x▹) → s≤ᵏs (subst (λ q → ▹[ α ∶ k ] (x▹ α ≤ᵏ q α))
                          (sym $ pfix cosu)
                          (prf▹ ⊛ x▹))

_≤ᶜ_ : ℕ∞ → ℕ∞ → 𝒰
x ≤ᶜ y = ∀ k → x k ≤ᵏ y k

¬s≤ᶜz : (x : ℕ∞) → ¬ (suᶜ x ≤ᶜ zeᶜ)
¬s≤ᶜz x prf = ¬s≤ᵏz (next (x k0)) (prf k0)

≤ᶜ-refl : (x : ℕ∞) → x ≤ᶜ x
≤ᶜ-refl x k = ≤ᵏ-refl (x k)

≤ᶜ-trans : (x y z : ℕ∞) → x ≤ᶜ y → y ≤ᶜ z → x ≤ᶜ z
≤ᶜ-trans x y z xy yz k = ≤ᵏ-trans (x k) (y k) (z k) (xy k) (yz k)

≤ᶜ-antisym : (x y : ℕ∞) → x ≤ᶜ y → y ≤ᶜ x → x ＝ y
≤ᶜ-antisym x y xy yx = fun-ext λ k → ≤ᵏ-antisym (x k) (y k) (xy k) (yx k)

≤ᶜ-inc : (x : ℕ∞) → x ≤ᶜ suᶜ x
≤ᶜ-inc x k = ≤ᵏ-inc (x k)

≤ᶜ-infty : (x : ℕ∞) → x ≤ᶜ inftyᶜ
≤ᶜ-infty x k = ≤ᵏ-infty (x k)

-- strict(?) order

_<ᵏ_ : ℕ∞ᵏ k → ℕ∞ᵏ k → 𝒰
x <ᵏ y = is-finiteᵏ x × incᵏ x ≤ᵏ y

<ᵏ-trans : (x y z : ℕ∞ᵏ k) → x <ᵏ y → y <ᵏ z → x <ᵏ z
<ᵏ-trans x y z (fx , ix≤y) (_ , iy≤z) =
  fx , ≤ᵏ-trans (incᵏ x) (incᵏ y) z
                (≤ᵏ-trans (incᵏ x) y (incᵏ y) ix≤y (≤ᵏ-inc y))
                iy≤z

<ᵏ-weaken : {x y : ℕ∞ᵏ k} → x <ᵏ y → x ≤ᵏ y
<ᵏ-weaken {x} {y} (_ , ix≤y) = ≤ᵏ-trans x (incᵏ x) y (≤ᵏ-inc x) ix≤y

≺ᵏ-inc : {x : ℕ∞ᵏ k} → is-finiteᵏ x → x <ᵏ incᵏ x
≺ᵏ-inc {x} fx = fx , ≤ᵏ-refl (incᵏ x)

_<ᶜ_ : ℕ∞ → ℕ∞ → 𝒰
x <ᶜ y = ∀ k → x k <ᵏ y k

<ᶜ-trans : (x y z : ℕ∞) → x <ᶜ y → y <ᶜ z → x <ᶜ z
<ᶜ-trans x y z xy yz k = <ᵏ-trans (x k) (y k) (z k) (xy k) (yz k)

<ᶜ-weaken : {x y : ℕ∞} → x <ᶜ y → x ≤ᶜ y
<ᶜ-weaken xy k = <ᵏ-weaken (xy k)

≺ᶜ-inc : {x : ℕ∞} → is-finiteᶜ x → x <ᶜ suᶜ x
≺ᶜ-inc {x} (n , e) k = ≺ᵏ-inc (n , happly e k)

-- interleaving style operations

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

minᶜ : ℕ∞ → ℕ∞ → ℕ∞
minᶜ x y k = minᵏ (x k) (y k)

minᶜ-zerol : (x : ℕ∞) → minᶜ zeᶜ x ＝ zeᶜ
minᶜ-zerol x = refl

minᶜ-zeror : (x : ℕ∞) → minᶜ x zeᶜ ＝ zeᶜ
minᶜ-zeror x = fun-ext λ k → minᵏ-zeror (x k)

minᶜ-idemp : (x : ℕ∞) → minᶜ x x ＝ x
minᶜ-idemp x = fun-ext λ k → minᵏ-idemp (x k)

minᶜ-comm : (x y : ℕ∞) → minᶜ x y ＝ minᶜ y x
minᶜ-comm x y = fun-ext λ k → minᵏ-comm (x k) (y k)

minᶜ-assoc : (x y z : ℕ∞) → minᶜ x (minᶜ y z) ＝ minᶜ (minᶜ x y) z
minᶜ-assoc x y z = fun-ext λ k → minᵏ-assoc (x k) (y k) (z k)

minᶜ-inftyl : (x : ℕ∞) → minᶜ inftyᶜ x ＝ x
minᶜ-inftyl x = fun-ext λ k → minᵏ-inftyl (x k)

minᶜ-inftyr : (x : ℕ∞) → minᶜ x inftyᶜ ＝ x
minᶜ-inftyr x = fun-ext λ k → minᵏ-inftyr (x k)

≤ᶜ-min-l : (x y : ℕ∞) → minᶜ x y ≤ᶜ x
≤ᶜ-min-l x y k = ≤ᵏ-min-l (x k) (y k)

≤ᶜ-min-r : (x y : ℕ∞) → minᶜ x y ≤ᶜ y
≤ᶜ-min-r x y k = ≤ᵏ-min-r (x k) (y k)

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
