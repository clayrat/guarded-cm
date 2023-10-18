{-# OPTIONS --guarded #-}

module Later where

open import Agda.Primitive.Cubical using ( primHComp ; primComp )
open import Prelude
open import Foundations.Cubes
open import Prim

infixl 4 _⊛_
infixr -2 ▹-syntax

postulate
  Cl   : 𝒰
  k0   : Cl
  Tick : Cl → LockU

private
  variable
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

postulate
  dfix : (▹ k A → A) → ▹ k A
  pfix : (f : ▹ k A → A) → dfix f ＝ λ _ → f (dfix f)

postulate
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

--next-inj : {x y : A} → next {k = k} x ＝ next y → ▹ k (x ＝ y)
--next-inj eq α i = eq i α

_⊛_ : ▹ k ((a : A) → B a)
  → (a : ▹ k A) → ▹[ α ∶ k ] B (a α)
(f ⊛ x) k = f k (x k)

▹map : ((a : A) → B a)
  → (a : ▹ k A) → ▹[ α ∶ k ] B (a α)
▹map f x k = f (x k)

▹map-id : {x : ▹ k A}
        → ▹map id x ＝ x
▹map-id = refl

▹map-comp : {B C : 𝒰 ℓ} {f : A → B} {g : B -> C} {x : ▹ k A}
          → ▹map g (▹map f x) ＝ ▹map (g ∘ f) x
▹map-comp = refl

Σ▹
  : Σ[ x ꞉ ▹ k A ] (▹[ α ∶ k ] B (x α))
  → ▹ k (Σ[ a ꞉ A ] B a)
Σ▹ (x , y) α = (x α) , (y α)

▹Σ
  : ▹[ α ∶ k ]     Σ[ a ꞉ A ] B a
  → Σ[ x ꞉ ▹ k A ] (▹[ α ∶ k ] B (x α))
▹Σ f = (λ α → fst (f α)) , λ α → snd (f α)

▹-ext : {A : I → 𝒰 ℓ} {x : ▹ k (A i0)} {y : ▹ k (A i1)}
  → ▹[ α ∶ k ] PathP A (x α) (y α) → PathP (λ i → ▹ k (A i)) x y
▹-ext p i α = p α i

▹-ap : {A : I → 𝒰 ℓ} {x : ▹ k (A i0)} {y : ▹ k (A i1)}
  → PathP (λ i → ▹ k (A i)) x y → ▹[ α ∶ k ] PathP A (x α) (y α)
▹-ap eq α i = eq i α

fix : (▹ k A → A) → A
fix f = f (dfix f)

pfix-ext : ∀ {l} {A : 𝒰 l} (f : ▹ k A → A) → ▸ k (λ α → dfix f α ＝ f (dfix f))
pfix-ext f α i = pfix f i α

fix-path : (f : ▹ k A → A) → fix f ＝ f (next (fix f))
fix-path f i = f (pfix f i)

delay : {A : Cl → 𝒰 ℓ} → (∀ k → A k) → ∀ k → ▹ k (A k)
delay a k _ = a k

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

▹x=▹y→x=y : {x y : A}
  → ((k : Cl) → next {k = k} x ＝ next y)
  → (k : Cl) → x ＝ y
▹x=▹y→x=y {A = A} {x} {y} ▹x=▹y k i = primComp (λ _ → A) (λ j → λ
  { (i = i0) → delay-force (λ _ → x) k j
  ; (i = i1) → delay-force (λ _ → y) k j
  })
  (force (λ k → ▹x=▹y k i) k )

▹-is-faithful : {A B : 𝒰 ℓ} → (f g : A → B)
  → (p : ∀ k → Path (▹ k A → ▹ k B) (▹map f) (▹map g))
  → (k : Cl) → f ＝ g
▹-is-faithful {A} {B} f g p k i x = primComp (λ _ → B) sq (force (λ k α → p k i (next x) α) k)
  where
    sq : I → Partial (~ i ∨ i) B
    sq j (i = i0) = delay-force (λ _ → f x) k j
    sq j (i = i1) = delay-force (λ _ → g x) k j

▹isContr→isContr▹ : {A : ▹ k (𝒰 ℓ)}
  → ▹[ α ∶ k ] is-contr (A α)
  → is-contr (▹[ α ∶ k ] (A α))
▹isContr→isContr▹ p = is-contr-η $ (λ α → is-contr-β (p α) .fst) , λ y i α → is-contr-β (p α) .snd (y α) i

▹isProp→isProp▹ : {A : ▹ k (𝒰 ℓ)}
  → ▹[ α ∶ k ] is-prop (A α)
  → is-prop (▹[ α ∶ k ] (A α))
▹isProp→isProp▹ p = is-prop-η λ x y i α → is-prop-β (p α) (x α) (y α) i

▹isSet→isSet▹ : {A : ▹ k (𝒰 ℓ)}
  → ▹[ α ∶ k ] is-set (A α)
  → is-set (▹[ α ∶ k ] (A α))
▹isSet→isSet▹ hyp = is-set-η λ x y p q i j α →
  is-set-β (hyp α) (x α) (y α) (λ j → p j α) (λ j → q j α) i j

▹isSet□→isSet□▹ : {A : ▹ k (𝒰 ℓ)}
  → ▹[ α ∶ k ] is-set-□ (A α)
  → is-set-□ (▹[ α ∶ k ] (A α))
▹isSet□→isSet□▹ hyp p q r s i j α = hyp α
  (λ i → p i α) (λ i → q i α) (λ j → r j α) (λ j → s j α) i j

▹x=▹y→▹x=y : (x y : ▹ k A)
  → (x ＝ y)
    -------------------------
  → ▹[ α ∶ k ] x α ＝ y α
▹x=▹y→▹x=y x y eq α i = eq i α

▹x=y→▹x=▹y : (x y : ▹ k A)
  → ▹[ α ∶ k ] x α ＝ y α
    -------------------------
  → x ＝ y
▹x=y→▹x=▹y x y eq i α = eq α i
