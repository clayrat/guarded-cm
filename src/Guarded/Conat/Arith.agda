{-# OPTIONS --guarded #-}
module Guarded.Conat.Arith where

open import Prelude
open import Data.Empty
open import Data.Sum

open import LaterG
open import Guarded.Conat

-- partial order

data _≤ᶜ_ : ℕ∞ → ℕ∞ → 𝒰 where
  z≤ᶜn : ∀ {n}                             → coze ≤ᶜ n
  s≤ᶜs : ∀ {m▹ n▹} → ▹[ α ] (m▹ α ≤ᶜ n▹ α) → cosu m▹ ≤ᶜ cosu n▹

¬s≤ᶜz : (x▹ : ▹ ℕ∞) → ¬ (cosu x▹ ≤ᶜ coze)
¬s≤ᶜz x▹ ()

≤ᶜ-refl : (x : ℕ∞) → x ≤ᶜ x
≤ᶜ-refl = fix λ prf▹ → λ where
  coze      → z≤ᶜn
  (cosu x▹) → s≤ᶜs (prf▹ ⊛ x▹)

≤ᶜ-trans : (x y z : ℕ∞) → x ≤ᶜ y → y ≤ᶜ z → x ≤ᶜ z
≤ᶜ-trans = fix λ prf▹ → λ where
  .coze       y          z          z≤ᶜn                           _                             →
    z≤ᶜn
  .(cosu x▹) .(cosu y▹) .(cosu z▹) (s≤ᶜs {m▹ = x▹} {n▹ = y▹} xy▹) (s≤ᶜs {m▹ = y▹} {n▹ = z▹} yz▹) →
    s≤ᶜs λ α → prf▹ α (x▹ α) (y▹ α) (z▹ α) (xy▹ α) (yz▹ α)

≤ᶜ-antisym : (x y : ℕ∞) → x ≤ᶜ y → y ≤ᶜ x → x ＝ y
≤ᶜ-antisym = fix λ prf▹ → λ where
  .coze      .coze       z≤ᶜn                           z≤ᶜn                          →
    refl
  .(cosu x▹) .(cosu y▹) (s≤ᶜs {m▹ = x▹} {n▹ = y▹} xy▹) (s≤ᶜs {m▹ = y▹} {n▹ = x▹} yx▹) →
    ap cosu (▹-ext (λ α → prf▹ α (x▹ α) (y▹ α) (xy▹ α) (yx▹ α)))

≤ᶜ-inc : (x : ℕ∞) → x ≤ᶜ incᶜ x
≤ᶜ-inc = fix λ prf▹ → λ where
  coze      → z≤ᶜn
  (cosu x▹) → s≤ᶜs (transport▹ (λ i α → x▹ α ≤ᶜ cosu (λ α₁ → tick-irr x▹ α α₁ i))
                               (prf▹ ⊛ x▹))

≤ᶜ-infty : (x : ℕ∞) → x ≤ᶜ infty
≤ᶜ-infty = fix λ prf▹ → λ where
  coze      → z≤ᶜn
  (cosu x▹) → s≤ᶜs (subst (λ q → ▹[ α ] (x▹ α ≤ᶜ q α))
                          (sym $ pfix cosu)
                          (prf▹ ⊛ x▹))

≤ᶜ-mono : (x y : ℕ∞) → x ≤ᶜ y → incᶜ x ≤ᶜ incᶜ y
≤ᶜ-mono x y l = s≤ᶜs (next l)

≤ᶜ-loc : (x y : ℕ∞) → incᶜ x ≤ᶜ incᶜ y → ▹ (x ≤ᶜ y)
≤ᶜ-loc x y (s≤ᶜs l▹) = l▹

≤ᶜ-prop : (x y : ℕ∞) → is-prop (x ≤ᶜ y)
≤ᶜ-prop x y = is-prop-η go
  where
  go : ∀ {x y} → (p₁ p₂ : x ≤ᶜ y) → p₁ ＝ p₂
  go {.coze}                    z≤ᶜn                 z≤ᶜn      = refl
  go {.(cosu m▹)} {.(cosu n▹)} (s≤ᶜs {m▹} {n▹} l₁▹) (s≤ᶜs l₂▹) = ap s≤ᶜs (▹-extP λ α → go (l₁▹ α) (l₂▹ α))

-- ≤ᶜ-finite looks impossible

-- strict(?) order

_<ᶜ_ : ℕ∞ → ℕ∞ → 𝒰
x <ᶜ y = is-finite-pᶜ x × incᶜ x ≤ᶜ y

<ᶜ-trans : (x y z : ℕ∞) → x <ᶜ y → y <ᶜ z → x <ᶜ z
<ᶜ-trans x y z (fx , ix≤y) (_ , iy≤z) =
  fx , ≤ᶜ-trans (incᶜ x) (incᶜ y) z
                (≤ᶜ-trans (incᶜ x) y (incᶜ y) ix≤y (≤ᶜ-inc y))
                iy≤z

<ᶜ-weaken : {x y : ℕ∞} → x <ᶜ y → x ≤ᶜ y
<ᶜ-weaken {x} {y} (_ , ix≤y) = ≤ᶜ-trans x (incᶜ x) y (≤ᶜ-inc x) ix≤y

≺ᶜ-inc : {x : ℕ∞} → is-finite-pᶜ x → x <ᶜ incᶜ x
≺ᶜ-inc {x} fx = fx , ≤ᶜ-refl (incᶜ x)

<ᶜ-mono : (x y : ℕ∞) → x <ᶜ y → incᶜ x <ᶜ incᶜ y
<ᶜ-mono x y (fx , ix≤y) = is-finite-p-upᶜ x fx , ≤ᶜ-mono (incᶜ x) y ix≤y

<ᶜ-loc : (x y : ℕ∞) → incᶜ x <ᶜ incᶜ y → ▹ (x <ᶜ y)
<ᶜ-loc x y (fx , ix≤y) = ▹map² _,_ (is-finite-down-pᶜ x fx) (≤ᶜ-loc (incᶜ x) y ix≤y)

<ᶜ-prop : (x y : ℕ∞) → is-prop (x <ᶜ y)
<ᶜ-prop x y = ×-is-of-hlevel 1 hlevel! (≤ᶜ-prop (incᶜ x) y)

-- interleaving style operations

-- minimum

minᶜ-body : ▹ (ℕ∞ → ℕ∞ → ℕ∞) → ℕ∞ → ℕ∞ → ℕ∞
minᶜ-body m▹  coze      _        = coze
minᶜ-body m▹ (cosu _)   coze     = coze
minᶜ-body m▹ (cosu x▹) (cosu y▹) = cosu (m▹ ⊛ x▹ ⊛ y▹)

minᶜ : ℕ∞ → ℕ∞ → ℕ∞
minᶜ = fix minᶜ-body

minᶜ-zerol : (x : ℕ∞) → minᶜ coze x ＝ coze
minᶜ-zerol x = refl

minᶜ-zeror : (x : ℕ∞) → minᶜ x coze ＝ coze
minᶜ-zeror  coze     = refl
minᶜ-zeror (cosu x▹) = refl

minᶜ-zero-inv : (m n : ℕ∞) → minᶜ m n ＝ coze → (m ＝ coze) ⊎ (n ＝ coze)
minᶜ-zero-inv  coze      n        e = inl refl
minᶜ-zero-inv (cosu m▹)  coze     e = inr refl
minᶜ-zero-inv (cosu m▹) (cosu n▹) e = absurd (cosu≠coze e)

minᶜ-idemp : (x : ℕ∞) → minᶜ x x ＝ x
minᶜ-idemp = fix λ prf▹ → λ where
  coze      → refl
  (cosu x▹) → ap (λ q → cosu (q ⊛ x▹ ⊛ x▹)) (pfix minᶜ-body)
            ∙ ap cosu (▹-ext (prf▹ ⊛ x▹))

minᶜ-comm : (x y : ℕ∞) → minᶜ x y ＝ minᶜ y x
minᶜ-comm = fix λ prf▹ → λ where
  coze       y        → sym (minᶜ-zeror y)
  (cosu x▹)  coze     → refl
  (cosu x▹) (cosu y▹) → ap (λ q → cosu (q ⊛ x▹ ⊛ y▹)) (pfix minᶜ-body)
                      ∙ ap cosu (▹-ext λ α → prf▹ α (x▹ α) (y▹ α))
                      ∙ ap (λ q → cosu (q ⊛ y▹ ⊛ x▹)) (sym $ pfix minᶜ-body)

minᶜ-assoc : (x y z : ℕ∞) → minᶜ x (minᶜ y z) ＝ minᶜ (minᶜ x y) z
minᶜ-assoc = fix λ prf▹ → λ where
  coze      y         z         → refl
  (cosu x▹) coze      z         → refl
  (cosu x▹) (cosu y▹) coze      → refl
  (cosu x▹) (cosu y▹) (cosu z▹) →
      ap (λ q → cosu ((dfix minᶜ-body) ⊛ x▹ ⊛ (q ⊛ y▹ ⊛ z▹))) (pfix minᶜ-body)
    ∙ ap (λ q → cosu (q ⊛ x▹ ⊛ ((next minᶜ) ⊛ y▹ ⊛ z▹))) (pfix minᶜ-body)
    ∙ ap cosu (▹-ext (λ α → prf▹ α (x▹ α) (y▹ α) (z▹ α)))
    ∙ ap (λ q → cosu (q ⊛ ((next minᶜ) ⊛ x▹ ⊛ y▹) ⊛ z▹)) (sym $ pfix minᶜ-body)
    ∙ ap (λ q → cosu ((dfix minᶜ-body) ⊛ (q ⊛ x▹ ⊛ y▹) ⊛ z▹)) (sym $ pfix minᶜ-body)

minᶜ-inftyl : (x : ℕ∞) → minᶜ infty x ＝ x
minᶜ-inftyl = fix λ prf▹ → λ where
  coze      → refl
  (cosu x▹) → ap (λ q → minᶜ q (cosu x▹)) (fix-path cosu)
            ∙ ap (λ q → cosu (q ⊛ (next infty) ⊛ x▹)) (pfix minᶜ-body)
            ∙ ap cosu (▹-ext (prf▹ ⊛ x▹))

minᶜ-inftyr : (x : ℕ∞) → minᶜ x infty ＝ x
minᶜ-inftyr x = minᶜ-comm x infty ∙ minᶜ-inftyl x

≤ᶜ-min-l : (x y : ℕ∞) → minᶜ x y ≤ᶜ x
≤ᶜ-min-l = fix λ prf▹ → λ where
  coze      y         → z≤ᶜn
  (cosu x▹) coze      → z≤ᶜn
  (cosu x▹) (cosu y▹) → s≤ᶜs (subst (λ q → ▹[ α ] ((q ⊛ x▹ ⊛ y▹) α ≤ᶜ x▹ α))
                                    (sym $ pfix minᶜ-body)
                                    (λ α → prf▹ α (x▹ α) (y▹ α)))

≤ᶜ-min-r : (x y : ℕ∞) → minᶜ x y ≤ᶜ y
≤ᶜ-min-r x y = subst (_≤ᶜ y) (minᶜ-comm y x) (≤ᶜ-min-l y x)

-- maximum

maxᶜ-body : ▹ (ℕ∞ → ℕ∞ → ℕ∞) → ℕ∞ → ℕ∞ → ℕ∞
maxᶜ-body m▹  coze      y        = y
maxᶜ-body m▹ (cosu x▹)  coze     = cosu x▹
maxᶜ-body m▹ (cosu x▹) (cosu y▹) = cosu (m▹ ⊛ x▹ ⊛ y▹)

maxᶜ : ℕ∞ → ℕ∞ → ℕ∞
maxᶜ = fix maxᶜ-body

maxᶜ-zerol : (x : ℕ∞) → maxᶜ coze x ＝ x
maxᶜ-zerol x = refl

maxᶜ-zeror : (x : ℕ∞) → maxᶜ x coze ＝ x
maxᶜ-zeror  coze     = refl
maxᶜ-zeror (cosu x▹) = refl

maxᶜ-idemp : (x : ℕ∞) → maxᶜ x x ＝ x
maxᶜ-idemp = fix λ prf▹ → λ where
  coze      → refl
  (cosu x▹) → ap (λ q → cosu (q ⊛ x▹ ⊛ x▹)) (pfix maxᶜ-body)
            ∙ ap cosu (▹-ext (prf▹ ⊛ x▹))

maxᶜ-comm : (x y : ℕ∞) → maxᶜ x y ＝ maxᶜ y x
maxᶜ-comm = fix λ prf▹ → λ where
  coze       y        → sym (maxᶜ-zeror y)
  (cosu x▹)  coze     → refl
  (cosu x▹) (cosu y▹) → ap (λ q → cosu (q ⊛ x▹ ⊛ y▹)) (pfix maxᶜ-body)
                      ∙ ap cosu (▹-ext λ α → prf▹ α (x▹ α) (y▹ α))
                      ∙ ap (λ q → cosu (q ⊛ y▹ ⊛ x▹)) (sym $ pfix maxᶜ-body)

maxᶜ-assoc : (x y z : ℕ∞) → maxᶜ x (maxᶜ y z) ＝ maxᶜ (maxᶜ x y) z
maxᶜ-assoc = fix λ prf▹ → λ where
  coze      y         z         → refl
  (cosu x▹) coze      z         → refl
  (cosu x▹) (cosu y▹) coze      → refl
  (cosu x▹) (cosu y▹) (cosu z▹) →
      ap (λ q → cosu ((dfix maxᶜ-body) ⊛ x▹ ⊛ (q ⊛ y▹ ⊛ z▹))) (pfix maxᶜ-body)
    ∙ ap (λ q → cosu (q ⊛ x▹ ⊛ ((next maxᶜ) ⊛ y▹ ⊛ z▹))) (pfix maxᶜ-body)
    ∙ ap cosu (▹-ext (λ α → prf▹ α (x▹ α) (y▹ α) (z▹ α)))
    ∙ ap (λ q → cosu (q ⊛ ((next maxᶜ) ⊛ x▹ ⊛ y▹) ⊛ z▹)) (sym $ pfix maxᶜ-body)
    ∙ ap (λ q → cosu ((dfix maxᶜ-body) ⊛ (q ⊛ x▹ ⊛ y▹) ⊛ z▹)) (sym $ pfix maxᶜ-body)

maxᶜ-inftyl : (x : ℕ∞) → maxᶜ infty x ＝ infty
maxᶜ-inftyl = fix λ prf▹ → λ where
  coze      → refl
  (cosu x▹) → ap (λ q → maxᶜ q (cosu x▹)) (fix-path cosu)
            ∙ ap (λ q → cosu (q ⊛ (next infty) ⊛ x▹)) (pfix maxᶜ-body)
            ∙ ap cosu (▹-ext (prf▹ ⊛ x▹))
            ∙ sym (fix-path cosu)

maxᶜ-inftyr : (x : ℕ∞) → maxᶜ x infty ＝ infty
maxᶜ-inftyr x = maxᶜ-comm x infty ∙ maxᶜ-inftyl x

≤ᶜ-max-l : (x y : ℕ∞) → x ≤ᶜ maxᶜ x y
≤ᶜ-max-l = fix λ prf▹ → λ where
  coze      y         → z≤ᶜn
  (cosu x▹) coze      → ≤ᶜ-refl (cosu x▹)
  (cosu x▹) (cosu y▹) → s≤ᶜs (subst (λ q → ▹[ α ] (x▹ α ≤ᶜ (q ⊛ x▹ ⊛ y▹) α))
                                    (sym $ pfix maxᶜ-body)
                                    (λ α → prf▹ α (x▹ α) (y▹ α)))

≤ᶜ-max-r : (x y : ℕ∞) → y ≤ᶜ maxᶜ x y
≤ᶜ-max-r x y = subst (y ≤ᶜ_) (maxᶜ-comm y x) (≤ᶜ-max-l y x)

-- closeness

closenessᶜ-body : ▹ (ℕ∞ → ℕ∞ → ℕ∞) → ℕ∞ → ℕ∞ → ℕ∞
closenessᶜ-body c▹  coze      coze     = infty
closenessᶜ-body c▹  coze     (cosu _)  = coze
closenessᶜ-body c▹ (cosu _)   coze     = coze
closenessᶜ-body c▹ (cosu m▹) (cosu n▹) = cosu (c▹ ⊛ m▹ ⊛ n▹)

closenessᶜ : ℕ∞ → ℕ∞ → ℕ∞
closenessᶜ = fix closenessᶜ-body

closenessᶜ-refl : (n : ℕ∞) → closenessᶜ n n ＝ infty
closenessᶜ-refl = fix λ ih▹ → λ where
  coze      → refl
  (cosu n▹) → ap cosu (▹-ext λ α → (λ i → pfix closenessᶜ-body i α (n▹ α) (n▹ α))
                                 ∙ ih▹ α (n▹ α)
                                 ∙ ▹-ap (sym $ pfix cosu) α)

close∞→equal : (m n : ℕ∞) → closenessᶜ m n ＝ infty → m ＝ n
close∞→equal = fix λ ih▹ → λ where
  coze       coze     e → refl
  coze      (cosu _)  e → absurd (cosu≠coze (sym e))
  (cosu _)   coze     e → absurd (cosu≠coze (sym e))
  (cosu m▹) (cosu n▹) e →
    ap cosu (▹-ext λ α → ih▹ α (m▹ α) (n▹ α) ((λ i → pfix closenessᶜ-body (~ i) α (m▹ α) (n▹ α))
                                              ∙ ▹-ap (cosu-inj e ∙ pfix cosu) α))

closenessᶜ-comm : (m n : ℕ∞) → closenessᶜ m n ＝ closenessᶜ n m
closenessᶜ-comm = fix λ ih▹ → λ where
  coze       coze     → refl
  coze      (cosu _)  → refl
  (cosu _)   coze     → refl
  (cosu m▹) (cosu n▹) → ap cosu (▹-ext λ α → (λ i → pfix closenessᶜ-body i α (m▹ α) (n▹ α))
                                           ∙ ih▹ α (m▹ α) (n▹ α)
                                           ∙ (λ i → pfix closenessᶜ-body (~ i) α (n▹ α) (m▹ α)))

closenessᶜ-ultra : (x y z : ℕ∞)
                 → minᶜ (closenessᶜ x y) (closenessᶜ y z) ≤ᶜ closenessᶜ x z
closenessᶜ-ultra = fix λ ih▹ → λ where
  coze       coze      coze     → ≤ᶜ-infty (minᶜ infty infty)
  coze       coze     (cosu z▹) → z≤ᶜn
  coze      (cosu y▹)  coze     → z≤ᶜn
  coze      (cosu y▹) (cosu z▹) → z≤ᶜn
  (cosu x▹)  coze      coze     → z≤ᶜn
  (cosu x▹)  coze     (cosu z▹) → z≤ᶜn
  (cosu x▹) (cosu y▹)  coze     → z≤ᶜn
  (cosu x▹) (cosu y▹) (cosu z▹) →
    s≤ᶜs λ α →
      transport (λ i → pfix minᶜ-body (~ i) α (dfix closenessᶜ-body α (x▹ α) (y▹ α))
                                              (dfix closenessᶜ-body α (y▹ α) (z▹ α))
                                            ≤ᶜ dfix closenessᶜ-body α (x▹ α) (z▹ α)) $
      transport (λ i → minᶜ (pfix closenessᶜ-body (~ i) α (x▹ α) (y▹ α))
                            (pfix closenessᶜ-body (~ i) α (y▹ α) (z▹ α))
                          ≤ᶜ pfix closenessᶜ-body (~ i) α (x▹ α) (z▹ α)) $
      ih▹ α (x▹ α) (y▹ α) (z▹ α)

-- addition

+ᶜ-body : ▹ (ℕ∞ → ℕ∞ → ℕ∞) → ℕ∞ → ℕ∞ → ℕ∞
+ᶜ-body a▹  coze      coze     = coze
+ᶜ-body a▹ (cosu x▹)  coze     = cosu x▹
+ᶜ-body a▹  coze     (cosu y▹) = cosu y▹
+ᶜ-body a▹ (cosu x▹) (cosu y▹) = cosu (next (cosu (a▹ ⊛ x▹ ⊛ y▹)))

_+ᶜ_ : ℕ∞ → ℕ∞ → ℕ∞
_+ᶜ_ = fix +ᶜ-body

+ᶜ-zerol : (x : ℕ∞) → coze +ᶜ x ＝ x
+ᶜ-zerol  coze     = refl
+ᶜ-zerol (cosu x▹) = refl

+ᶜ-zeror : (x : ℕ∞) → x +ᶜ coze ＝ x
+ᶜ-zeror  coze     = refl
+ᶜ-zeror (cosu x▹) = refl

+ᶜ-comm : (x y : ℕ∞) → x +ᶜ y ＝ y +ᶜ x
+ᶜ-comm = fix λ prf▹ → λ where
  coze       coze      → refl
  coze      (cosu x▹)  → refl
  (cosu x▹)  coze      → refl
  (cosu x▹) (cosu y▹)  →
    (cosu x▹ +ᶜ cosu y▹)
      ＝⟨⟩
    cosu (next (cosu (dfix +ᶜ-body ⊛ x▹ ⊛ y▹)))
      ＝⟨ ap (λ q → cosu (next (cosu (q ⊛ x▹ ⊛ y▹)))) (pfix +ᶜ-body) ⟩
    cosu (next (cosu ((next _+ᶜ_) ⊛ x▹ ⊛ y▹)))
      ＝⟨ ap cosu (▹-ext (next (ap cosu (▹-ext λ α → prf▹ α (x▹ α) (y▹ α))))) ⟩
    cosu (next (cosu ((next _+ᶜ_) ⊛ y▹ ⊛ x▹)))
      ＝⟨ ap (λ q → cosu (next (cosu (q ⊛ y▹ ⊛ x▹)))) (sym $ pfix +ᶜ-body) ⟩
    cosu (next (cosu (dfix +ᶜ-body ⊛ y▹ ⊛ x▹)))
      ＝⟨⟩
    (cosu y▹ +ᶜ cosu x▹)
      ∎

+ᶜ-inftyl : (x : ℕ∞) → infty +ᶜ x ＝ infty
+ᶜ-inftyl = fix λ prf▹ → λ where
  coze      → refl
  (cosu x▹) →
     infty +ᶜ cosu x▹
       ＝⟨ ap (_+ᶜ cosu x▹) (fix-path cosu) ⟩
     cosu (next (cosu ((dfix +ᶜ-body) ⊛ (next infty) ⊛ x▹)))
       ＝⟨ ap (λ q → cosu (next (cosu (q ⊛ (next infty) ⊛ x▹)))) (pfix +ᶜ-body) ⟩
     cosu (next (cosu ((next _+ᶜ_) ⊛ next infty ⊛ x▹)))
       ＝⟨ ap cosu (▹-ext (λ _ → ap cosu (▹-ext (prf▹ ⊛ x▹)))) ⟩
     cosu (next (cosu (next (fix cosu))))
       ＝⟨ ap cosu (▹-ext (λ _ → sym $ fix-path cosu)) ⟩
     cosu (next infty)
       ＝⟨ sym $ fix-path cosu ⟩
     infty
       ∎

+ᶜ-inftyr : (x : ℕ∞) → x +ᶜ infty ＝ infty
+ᶜ-inftyr x = +ᶜ-comm x infty ∙ +ᶜ-inftyl x

-- concatenation style
+:ᶜ-body : ℕ∞ → ▹ (ℕ∞ → ℕ∞) → ℕ∞ → ℕ∞
+:ᶜ-body x ax▹  coze    = x
+:ᶜ-body x ax▹ (cosu y) = cosu (ax▹ ⊛ y)

_+:ᶜ_ : ℕ∞ → ℕ∞ → ℕ∞
_+:ᶜ_ x = fix (+:ᶜ-body x)

+:ᶜ-zerol : (x : ℕ∞) → coze +:ᶜ x ＝ x
+:ᶜ-zerol = fix λ prf▹ → λ where
  coze     → refl
  (cosu x) → cosu (dfix (+:ᶜ-body coze) ⊛ x)
               ＝⟨ ap (λ q → cosu (q ⊛ x)) (pfix (+:ᶜ-body coze) ) ⟩
             cosu (▹map (coze +:ᶜ_) x)
               ＝⟨ ap cosu (▹-ext (prf▹ ⊛ x)) ⟩
             cosu x
               ∎

+:ᶜ-zeror : (x : ℕ∞) → x +ᶜ coze ＝ x
+:ᶜ-zeror  coze     = refl
+:ᶜ-zeror (cosu x▹) = refl

-- +ᶜ-sucl doesn't seem to be provable easily

+:ᶜ-sucr : (x : ℕ∞) → (y▹ : ▹ ℕ∞)
        → x +:ᶜ (cosu y▹) ＝ cosu (▹map (x +:ᶜ_) y▹)
+:ᶜ-sucr x y▹ = ap (_$ (cosu y▹)) (fix-path (+:ᶜ-body x))

-- TODO https://proofassistants.stackexchange.com/questions/1545/how-to-prove-that-addition-is-commutative-for-conatural-numbers-in-coq
