{-# OPTIONS --guarded #-}
module Clocked.Conat.Stream where

open import Prelude
open import Data.Empty
open import Data.Bool
open import Data.Dec

open import Later
open import Clocked.Conat
open import Clocked.Conat.Arith
open import Clocked.Stream
open import Clocked.Stream.Quantifiers

private variable
  ℓ : Level
  A : 𝒰 ℓ
  k : Cl

-- stream interaction

to-streamᵏ-body : ▹ k (ℕ∞ᵏ k → gStream k Bool) → ℕ∞ᵏ k → gStream k Bool
to-streamᵏ-body ts▹  coze     = repeatᵏ false
to-streamᵏ-body ts▹ (cosu n▹) = cons true (ts▹ ⊛ n▹)

-- Escardo's ι
to-streamᵏ : ℕ∞ᵏ k → gStream k Bool
to-streamᵏ = fix to-streamᵏ-body

infty-stream : to-streamᵏ {k = k} inftyᵏ ＝ repeatᵏ true
infty-stream {k} = fix {k = k} λ prf▹ →
  to-streamᵏ inftyᵏ
    ＝⟨ ap (_$ inftyᵏ) (fix-path to-streamᵏ-body) ⟩
  to-streamᵏ-body (next to-streamᵏ) inftyᵏ
    ＝⟨ ap (to-streamᵏ-body (next to-streamᵏ)) (fix-path cosu) ⟩
  to-streamᵏ-body (next to-streamᵏ) (cosu (next inftyᵏ))
    ＝⟨⟩
  cons true (next (to-streamᵏ inftyᵏ))
    ＝⟨ ap (cons true) (▹-ext prf▹) ⟩
  cons true (next (repeatᵏ true))
    ＝⟨ sym $ fix-path (cons true) ⟩
  repeatᵏ true
    ∎

to-streamᶜ : ℕ∞ → Stream Bool
to-streamᶜ c k = to-streamᵏ (c k)

-- TODO should be possible to express without streams
_>ℕ_ : ℕ∞ → ℕ → Bool
c >ℕ n = nthˢ n (to-streamᶜ c)

to-streamᵏ-inj : (n m : ℕ∞ᵏ k) → to-streamᵏ n ＝ to-streamᵏ m → n ＝ m
to-streamᵏ-inj = fix λ prf▹ →
  λ where
      coze       coze     e → refl
      coze      (cosu _)  e → absurd (false≠true (cons-inj e .fst))
      (cosu _)   coze     e → absurd (true≠false (cons-inj e .fst))
      (cosu n▹) (cosu m▹) e →
        ap cosu (▹-ext λ α → prf▹ α (n▹ α) (m▹ α)
                                  ((λ i → pfix to-streamᵏ-body (~ i) α (n▹ α))
                                   ∙ ▹-ap (cons-inj e .snd) α
                                   ∙ λ i → pfix to-streamᵏ-body i α (m▹ α)))

to-streamᶜ-inj : (n m : ℕ∞) → to-streamᶜ n ＝ to-streamᶜ m → n ＝ m
to-streamᶜ-inj n m e = fun-ext λ k → to-streamᵏ-inj (n k) (m k) (happly e k)

-- TODO (g)stream hlevel
--to-streamᵏ-emb : is-embedding to-streamᵏ
--to-streamᵏ-emb = set-injective→is-embedding {!!} λ {x} {y} → to-streamᵏ-inj x y

decreasingᵏ : gStream k Bool → 𝒰
decreasingᵏ {k} = gAdj k (λ p q → p or (not q) ＝ true)

decreasingˢ : Stream Bool → 𝒰
decreasingˢ = Adj (λ p q → p or (not q) ＝ true)

to-streamᵏ-decreasing : (n : ℕ∞ᵏ k) → decreasingᵏ (to-streamᵏ n)
to-streamᵏ-decreasing =
  fix λ ih▹ → λ where
    coze      → repeat-gadj or-compl false
    (cosu n▹) →
      gAdj-cons (next refl) λ α → transport (λ i → decreasingᵏ (pfix to-streamᵏ-body (~ i) α (n▹ α))) ((ih▹ ⊛ n▹) α)

to-streamˢ-decreasing : (n : ℕ∞) → decreasingˢ (to-streamᶜ n)
to-streamˢ-decreasing n k = to-streamᵏ-decreasing (n k)

-- Cantor encoding (single bit)

to-Cantorᵏ-body : ▹ k (ℕ∞ᵏ k → gStream k Bool) → ℕ∞ᵏ k → gStream k Bool
to-Cantorᵏ-body ts▹  coze     = cons-δ true (repeatᵏ false)
to-Cantorᵏ-body ts▹ (cosu n▹) = cons false (ts▹ ⊛ n▹)

to-Cantorᵏ : ℕ∞ᵏ k → gStream k Bool
to-Cantorᵏ = fix to-Cantorᵏ-body

to-Cantorᶜ : ℕ∞ → Stream Bool
to-Cantorᶜ n k = to-Cantorᵏ (n k)

Cantorᵏ-infty : to-Cantorᵏ {k = k} inftyᵏ ＝ repeatᵏ false
Cantorᵏ-infty =
  fix λ ih▹ →
    ap (cons false) (▹-ext λ α → (λ i → dfix to-Cantorᵏ-body α (pfix cosu i α))
                               ∙ (λ i → pfix to-Cantorᵏ-body i α inftyᵏ)
                               ∙ ih▹ α
                               ∙ (λ i → pfix (cons false) (~ i) α))

Cantorᶜ-infty : to-Cantorᶜ inftyᶜ ＝ repeatˢ false
Cantorᶜ-infty = fun-ext λ k → Cantorᵏ-infty

-- stream closeness

closenessᵏˢ-body : is-discrete A
                → ▹ k (gStream k A → gStream k A → ℕ∞ᵏ k) → gStream k A → gStream k A → ℕ∞ᵏ k
closenessᵏˢ-body d c▹ (cons h₁ t▹₁) (cons h₂ t▹₂) with (is-discrete-β d h₁ h₂)
... | yes e   = cosu (c▹ ⊛ t▹₁ ⊛ t▹₂)
... | no ctra = coze

closenessᵏˢ : is-discrete A
            → gStream k A → gStream k A → ℕ∞ᵏ k
closenessᵏˢ d = fix (closenessᵏˢ-body d)

closenessᵏˢ-refl : (d : is-discrete A)
                 → (s : gStream k A) → closenessᵏˢ d s s ＝ inftyᵏ
closenessᵏˢ-refl d = fix (go d)
  where
  go : ∀ {A} → (d : is-discrete A)
     → ▹ k ((s : gStream k A) → closenessᵏˢ d s s ＝ inftyᵏ)
     →      (s : gStream k A) → closenessᵏˢ d s s ＝ inftyᵏ
  go d ih▹ (cons h t▹) with (is-discrete-β d h h)
  ... | yes e = ap cosu (▹-ext λ α → (λ i → pfix (closenessᵏˢ-body d) i α (t▹ α) (t▹ α))
                                   ∙ ih▹ α (t▹ α)
                                   ∙ ▹-ap (sym $ pfix cosu) α)
  ... | no ctra = absurd (ctra refl)

close∞→equalᵏˢ : (d : is-discrete A)
               → (s t : gStream k A)
               → closenessᵏˢ d s t ＝ inftyᵏ → s ＝ t
close∞→equalᵏˢ d = fix (go d)
  where
  go : ∀ {A} → (d : is-discrete A)
     → ▹ k ((s t : gStream k A) → closenessᵏˢ d s t ＝ inftyᵏ → s ＝ t)
     →      (s t : gStream k A) → closenessᵏˢ d s t ＝ inftyᵏ → s ＝ t
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) e with (is-discrete-β d h₁ h₂)
  ... | yes eh = ap² cons eh (▹-ext λ α → ih▹ α (t▹₁ α) (t▹₂ α)
                                             ((λ i → pfix (closenessᵏˢ-body d) (~ i) α (t▹₁ α) (t▹₂ α))
                                              ∙ ▹-ap (cosu-inj e ∙ pfix cosu) α))
  ... | no ctra = absurd (cosu≠coze (sym e))

closenessᵏˢ-comm : (d : is-discrete A)
                 → (s t : gStream k A)
                 → closenessᵏˢ d s t ＝ closenessᵏˢ d t s
closenessᵏˢ-comm d = fix (go d)
  where
  go : ∀ {A} → (d : is-discrete A)
     → ▹ k ((s t : gStream k A) → closenessᵏˢ d s t ＝ closenessᵏˢ d t s) →
            (s t : gStream k A) → closenessᵏˢ d s t ＝ closenessᵏˢ d t s
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) with (is-discrete-β d h₁ h₂)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | yes eh with (is-discrete-β d h₂ h₁) -- AARGH
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | yes eh | yes eh′ =
    ap cosu (▹-ext λ α → (λ i → pfix (closenessᵏˢ-body d) i α (t▹₁ α) (t▹₂ α))
                       ∙ ih▹ α (t▹₁ α) (t▹₂ α)
                       ∙ λ i → pfix (closenessᵏˢ-body d) (~ i) α (t▹₂ α) (t▹₁ α) )
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | yes eh | no ctra′ = absurd (ctra′ (sym eh))
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | no ctra with (is-discrete-β d h₂ h₁) -- AARGH
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | no ctra | yes eh′ = absurd (ctra (sym eh′))
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) | no ctra | no ctra′ = refl

closenessᵏˢ-ultra : (d : is-discrete A)
                 → (x y z : gStream k A)
                 → minᵏ (closenessᵏˢ d x y) (closenessᵏˢ d y z) ≤ᵏ closenessᵏˢ d x z
closenessᵏˢ-ultra d = fix (go d)
  where
  go : ∀ {A} → (d : is-discrete A)
     → ▹ k ((x y z : gStream k A) → minᵏ (closenessᵏˢ d x y) (closenessᵏˢ d y z) ≤ᵏ closenessᵏˢ d x z)
     →      (x y z : gStream k A) → minᵏ (closenessᵏˢ d x y) (closenessᵏˢ d y z) ≤ᵏ closenessᵏˢ d x z
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) with (is-discrete-β d h₁ h₂)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ with (is-discrete-β d h₂ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | yes e₂₃ with (is-discrete-β d h₁ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | yes e₂₃ | yes e₁₃ =
    s≤ᵏs λ α →
      transport (λ i → pfix minᵏ-body (~ i) α (dfix (closenessᵏˢ-body d) α (t▹₁ α) (t▹₂ α))
                                              (dfix (closenessᵏˢ-body d) α (t▹₂ α) (t▹₃ α))
                                            ≤ᵏ dfix (closenessᵏˢ-body d) α (t▹₁ α) (t▹₃ α)) $
      transport (λ i → minᵏ (pfix (closenessᵏˢ-body d) (~ i) α (t▹₁ α) (t▹₂ α))
                            (pfix (closenessᵏˢ-body d) (~ i) α (t▹₂ α) (t▹₃ α))
                          ≤ᵏ pfix (closenessᵏˢ-body d) (~ i) α (t▹₁ α) (t▹₃ α)) $
      ih▹ α (t▹₁ α) (t▹₂ α) (t▹₃ α)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | yes e₂₃ | no ne₁₃ =
    absurd (ne₁₃ (e₁₂ ∙ e₂₃))
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | no ne₂₃ with (is-discrete-β d h₁ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | no ne₂₃ | yes e₁₃ =
    absurd (ne₂₃ (sym e₁₂ ∙ e₁₃))
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | yes e₁₂ | no ne₂₃ | no ne₁₃ =
    z≤ᵏn
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ with (is-discrete-β d h₂ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | yes e₂₃ with (is-discrete-β d h₁ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | yes e₂₃ | yes e₁₃ =
    absurd (ne₁₂ (e₁₃ ∙ sym e₂₃))
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | yes e₂₃ | no ne₁₃ =
    z≤ᵏn
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | no ne₂₃ with (is-discrete-β d h₁ h₃)
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | no ne₂₃ | yes e₁₃ =
    z≤ᵏn
  go d ih▹ (cons h₁ t▹₁) (cons h₂ t▹₂) (cons h₃ t▹₃) | no ne₁₂ | no ne₂₃ | no ne₁₃ =
    z≤ᵏn

closenessˢ : is-discrete A
           → Stream A → Stream A → ℕ∞
closenessˢ ds s t k = closenessᵏˢ ds (s k) (t k)

closenessˢ-refl : (d : is-discrete A)
                → (s : Stream A) → closenessˢ d s s ＝ inftyᶜ
closenessˢ-refl d s = fun-ext λ k → closenessᵏˢ-refl d (s k)

close∞→equalˢ : (d : is-discrete A)
              → (s t : Stream A)
              → closenessˢ d s t ＝ inftyᶜ → s ＝ t
close∞→equalˢ d s t e = fun-ext λ k → close∞→equalᵏˢ d (s k) (t k) (happly e k)

closenessˢ-comm : (d : is-discrete A)
                → (s t : Stream A) → closenessˢ d s t ＝ closenessˢ d t s
closenessˢ-comm d s t = fun-ext λ k → closenessᵏˢ-comm d (s k) (t k)

closenessˢ-ultra : (d : is-discrete A)
                 → (x y z : Stream A)
                 → minᶜ (closenessˢ d x y) (closenessˢ d y z) ≤ᶜ closenessˢ d x z
closenessˢ-ultra d x y z k = closenessᵏˢ-ultra d (x k) (y k) (z k)
