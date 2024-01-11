{-# OPTIONS --guarded #-}

module Later where

open import Agda.Primitive.Cubical using ( primHComp ; primComp )
open import Prelude
open import Foundations.Cubes
open import Prim

infixl 5 _⍉_
infixl 4 _⊛_
infixl 4 _⊛′_
infixr -2 ▹-syntax

postulate
  Cl   : 𝒰
  k0   : Cl
  Tick : Cl → LockU

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : A → 𝒰 ℓ′
  k : Cl

▹ : Cl → 𝒰 ℓ → 𝒰 ℓ
▹ k A = (@tick α : Tick k) → A

▸ : (k : Cl) → ▹ k (𝒰 ℓ) → 𝒰 ℓ
▸ k A▹ = (@tick α : Tick k) → A▹ α

▹-syntax : (k : Cl) → ▹ k (𝒰 ℓ) → 𝒰 ℓ
▹-syntax k A▹ = (@tick α : Tick k) → A▹ α

syntax ▹-syntax k (λ α → e) = ▹[ α ∶ k ] e

postulate
  tick-irr : {k : Cl} (x : ▹ k A) → ▹[ α ∶ k ] ▹[ β ∶ k ] x α ＝ x β

  dfix : (▹ k A → A) → ▹ k A
  pfix : (f : ▹ k A → A) → dfix f ＝ λ _ → f (dfix f)

  force       : {A : Cl → 𝒰 ℓ}        → (∀ k → ▹ k (A k)) → ∀ k → A k
  force-delay : {A : Cl → 𝒰 ℓ}        → (f : ∀ k → ▹ k (A k)) → ∀ k → ▹[ α ∶ k ] force f k ＝ f k α
  delay-force : {A : Cl → 𝒰 ℓ}        → (f : ∀ k → A k)       → ∀ k → force (λ k′ α → f k′) k ＝ f k
  force^      : {A : ∀ k → ▹ k (𝒰 ℓ)} → (∀ k → ▸ k (A k))     → ∀ k → force A k
-- No more postulates after this line.

transport▹ : (A : I → ▹ k (𝒰 ℓ)) → ▸ k (A i0) → ▸ k (A i1)
transport▹ {k = k} A = transp (λ i → ▸ k (A i)) i0

hcomp▹ : (A : ▹ k (𝒰 ℓ)) (φ : I) (u : I → Partial φ (▸ k A))
  → (u0 : ▸ k A [ φ ↦ u i0 ]) → ▸ k A
hcomp▹ A φ u u0 a = primHComp (λ { i (φ = i1) → u i 1=1 a }) (outS u0 a)

-- aka pure
next : A → ▹ k A
next x α = x

▸-next : ▸ k (next A) ＝ ▹ k A
▸-next = refl

_⊛_ : ▹ k ((a : A) → B a)
  → (a : ▹ k A) → ▹[ α ∶ k ] B (a α)
(f ⊛ x) α = f α (x α)

_⊛′_ : ∀ {A : ▹ k (𝒰 ℓ)} {B : ▹[ α ∶ k ] (A α → 𝒰 ℓ′)}
     → ▹[ α ∶ k ] ((a : A α) → B α a)
     → (a : ▹[ α ∶ k ] A α)
     → ▹[ α ∶ k ] B α (a α)
(f ⊛′ x) α = f α (x α)

-- map
_⍉_ : ((a : A) → B a)
     → (a : ▹ k A) → ▹[ α ∶ k ] B (a α)
_⍉_ f x α = f (x α)

-- functor laws

▹map-id : {x : ▹ k A}
        → id ⍉ x ＝ x
▹map-id = refl

▹map-comp : {B C : 𝒰 ℓ} {f : A → B} {g : B -> C} {x : ▹ k A}
          → g ⍉ (f ⍉ x) ＝ (g ∘ f) ⍉ x
▹map-comp = refl

-- applicative laws

ap-id : {B : 𝒰}
      → (x▹ : ▹ k A)
      → (next id ⊛ x▹) ＝ x▹
ap-id x▹ = refl

ap-comp : {B C : 𝒰}
        → (f▹ : ▹ k (A → B))
        → (g▹ : ▹ k (B → C))
        → (x▹ : ▹ k A)
        → ((next λ g f → g ∘ f) ⊛ g▹ ⊛ f▹ ⊛ x▹) ＝ (g▹ ⊛ (f▹ ⊛ x▹))
ap-comp f▹ g▹ x▹ = refl

ap-homo : {B : 𝒰}
        → (f : A → B)
        → (x : A)
        → (next {k = k} f ⊛ next x) ＝ next (f x)
ap-homo f x = refl

ap-inter : {B : 𝒰}
         → (f▹ : ▹ k (A → B))
         → (x : A)
         → (f▹ ⊛ next x) ＝ ((next (_$ x)) ⊛ f▹)
ap-inter f▹ x = refl

-- path interaction

▹-ext : {A : I → 𝒰 ℓ} {x▹ : ▹ k (A i0)} {y▹ : ▹ k (A i1)}
      → ▹[ α ∶ k ] ＜ (x▹ α) ／ (λ i → A i) ＼ (y▹ α) ＞
      → ＜ x▹ ／ (λ i → ▹ k (A i)) ＼ y▹ ＞
▹-ext p i α = p α i

▹-ap : {A : I → 𝒰 ℓ} {x▹ : ▹ k (A i0)} {y▹ : ▹ k (A i1)}
     → ＜ x▹ ／ (λ i → ▹ k (A i)) ＼ y▹ ＞
     → ▹[ α ∶ k ] ＜ (x▹ α) ／ (λ i → A i) ＼ (y▹ α) ＞
▹-ap p α i = p i α

▹-extP : {A : I → ▹ k (𝒰 ℓ)} {x▹ : ▹[ α ∶ k ] A i0 α} {y▹ : ▹[ α ∶ k ] A i1 α}
     → (▹[ α ∶ k ] ＜ (x▹ α) ／ (λ i → A i α) ＼ (y▹ α) ＞)
     → ＜ x▹ ／ (λ i → ▹[ α ∶ k ] A i α) ＼ y▹ ＞
▹-extP e i α = e α i

▹-apP : {A : I → ▹ k (𝒰 ℓ)} {x▹ : ▹[ α ∶ k ] A i0 α} {y▹ : ▹[ α ∶ k ] A i1 α}
     → ＜ x▹ ／ (λ i → ▹[ α ∶ k ] A i α) ＼ y▹ ＞
     → (▹[ α ∶ k ] ＜ (x▹ α) ／ (λ i → A i α) ＼ (y▹ α) ＞)
▹-apP e α i = e i α

-- fixpoint

fix : (▹ k A → A) → A
fix f = f (dfix f)

pfix-ext : ∀ {l} {A : 𝒰 l} (f : ▹ k A → A) → ▸ k (λ α → dfix f α ＝ f (dfix f))
pfix-ext f α i = pfix f i α

fix-path : (f : ▹ k A → A) → fix f ＝ f (next (fix f))
fix-path f i = f (pfix f i)

-- sigma interaction

Σ▹ : Σ[ x ꞉ ▹ k A ] (▹[ α ∶ k ] B (x α))
   → ▹ k (Σ[ a ꞉ A ] B a)
Σ▹ (x , y) α = (x α) , (y α)

▹Σ : ▹[ α ∶ k ]     Σ[ a ꞉ A ] B a
   → Σ[ x ꞉ ▹ k A ] (▹[ α ∶ k ] B (x α))
▹Σ f = (λ α → fst (f α)) , λ α → snd (f α)

▹Σ≃Σ▹ : Iso (▹[ α ∶ k ] Σ[ a ꞉ A ] B a) (Σ[ x ꞉ ▹ k A ] (▹[ α ∶ k ] B (x α)))
▹Σ≃Σ▹ = ▹Σ , iso Σ▹
               (λ { (x , y) i → x , y } )
               λ x i α → x α .fst , x α .snd

@0 ▹Σ≡Σ▹ : (k : Cl) (A : 𝒰 ℓ) (B : A → 𝒰 ℓ′)
  → (▹[ α ∶ k ] Σ[ a ꞉ A ] B a) ＝ (Σ[ x ꞉ ▹ k A ] (▹[ α ∶ k ] B (x α)))
▹Σ≡Σ▹ k A B = iso→path ▹Σ≃Σ▹

@0 dfixΣ : (Σ[ x ꞉ ▹ k A ] (▹[ α ∶ k ] B (x α)) → Σ[ a ꞉ A ] B a)
         →  Σ[ x ꞉ ▹ k A ] (▹[ α ∶ k ] B (x α))
dfixΣ {k} {A} {B} = transport
  (λ i → (▹Σ≡Σ▹ k A B i → Σ[ a ꞉ A ] B a) → ▹Σ≡Σ▹ k A B i) dfix

@0 fixΣ : (Σ[ x ꞉ ▹ k A ] (▹[ α ∶ k ] B (x α)) → Σ[ a ꞉ A ] B a)
         → Σ[ x ꞉ A ] B x
fixΣ f = f (dfixΣ f)
{-
pfixΣ : {k : Cl} {A : 𝒰 l} {B : A → 𝒰 ℓ′}
  → (f : Σ[ x ∶ ▹ k A ] ▹[ α ∶ k ] B (x α) → Σ[ a ∶ A ] B a)
  → dfixΣ f ≡ (next (f (dfixΣ f) .fst) , next (f (dfixΣ f) .snd))
pfixΣ f = {!!}
-}
{-
  force (λ _ _ → f x) k ---------------------> force (λ _ _ → g x) k
        |                                        |
        |                                        |
        |                                        |
        V                                        v
       f x -----------------------------------> g x
-}

-- delay and force

delay : {A : Cl → 𝒰 ℓ} → (∀ k → A k) → ∀ k → ▹ k (A k)
delay a k _ = a k

▹x=▹y→x=y : {x y : A}
  → ((k : Cl) → next {k = k} x ＝ next y)
  → (k : Cl) → x ＝ y
▹x=▹y→x=y {A = A} {x} {y} ▹x=▹y k i = primComp (λ _ → A) (λ j → λ
  { (i = i0) → delay-force (λ _ → x) k j
  ; (i = i1) → delay-force (λ _ → y) k j
  })
  (force (λ k → ▹x=▹y k i) k )

▹-is-faithful : {A B : 𝒰 ℓ} → (f g : A → B)
  → (∀ k → Path (▹ k A → ▹ k B) (f ⍉_) (g ⍉_))
  → ∀ k → f ＝ g
▹-is-faithful {A} {B} f g p k i x = primComp (λ _ → B) sq (force (λ k α → p k i (next x) α) k)
  where
    sq : I → Partial (~ i ∨ i) B
    sq j (i = i0) = delay-force (λ _ → f x) k j
    sq j (i = i1) = delay-force (λ _ → g x) k j

-- feedback combinator

feedback : (▹ k A → B k × A) → B k
feedback f = fst (fix (f ∘ (snd ⍉_)))

-- fixed point uniqueness

dfix-unique : ∀ {f▹ : ▹ k A → A} {x : ▹ k A}
            → x ＝ next (f▹ x)
            → x ＝ dfix f▹
dfix-unique {f▹} e = fix λ ih▹ → e ∙ ▹-ext ((ap f▹) ⍉ ih▹) ∙ sym (pfix f▹)

fix-unique : ∀ {f▹ : ▹ k A → A} {x : A}
           → x ＝ f▹ (next x)
           → x ＝ fix f▹
fix-unique {f▹} e = fix λ ih▹ → e ∙ ap f▹ (▹-ext ih▹) ∙ sym (fix-path f▹)

▹Alg : ∀ {k} → 𝒰 ℓ → 𝒰 ℓ
▹Alg {k} A = ▹ k A → A

-- hlevel interaction

▹is-contr : {A : ▹ k (𝒰 ℓ)}
  → ▹[ α ∶ k ] is-contr (A α)
  → is-contr (▹[ α ∶ k ] (A α))
▹is-contr p = is-contr-η $ (λ α → is-contr-β (p α) .fst) , λ y i α → is-contr-β (p α) .snd (y α) i

▹is-prop : {A : ▹ k (𝒰 ℓ)}
  → ▹[ α ∶ k ] is-prop (A α)
  → is-prop (▹[ α ∶ k ] (A α))
▹is-prop p = is-prop-η λ x y i α → is-prop-β (p α) (x α) (y α) i

▹is-of-hlevel : {A : ▹ k (𝒰 ℓ)} {n : HLevel}
  → ▹[ α ∶ k ] is-of-hlevel n (A α)
  → is-of-hlevel n (▹[ α ∶ k ] (A α))
▹is-of-hlevel {n = zero}          = ▹is-contr
▹is-of-hlevel {n = suc zero}      = ▹is-prop
▹is-of-hlevel {n = suc (suc n)} a =
  is-of-hlevel-η n λ p q →
    retract→is-of-hlevel (suc n) ▹-extP ▹-apP (λ _ → refl)
    (▹is-of-hlevel λ α → is-of-hlevel-β n (a α) (p α) (q α))

▹is-set-□ : {A : ▹ k (𝒰 ℓ)}
  → ▹[ α ∶ k ] is-set-□ (A α)
  → is-set-□ (▹[ α ∶ k ] (A α))
▹is-set-□ hyp p q r s i j α = hyp α
  (λ i → p i α) (λ i → q i α) (λ j → r j α) (λ j → s j α) i j

-- prop truncation interaction

▹trunc : ∀ {B : ▹ k (𝒰 ℓ′)}
       → (A → ▹[ α ∶ k ] B α)
       → ∥ A ∥₁ → ▹[ α ∶ k ] ∥ B α ∥₁
▹trunc f = ∥-∥₁.rec (▹is-prop (λ α → hlevel!)) (λ x α → ∣ f x α ∣₁)
