{-# OPTIONS --guarded #-}
module Guarded.Hofmann where

open import Prelude
open import Data.Empty
open import Data.Sum
open import Data.List as List

open import LaterG
open import Guarded.Colist

private variable
  A B : 𝒰

-- can be extended to Tree∞

data Tree (A : 𝒰) : 𝒰 where
  Leaf :           A           → Tree A
  Br   : Tree A → A → Tree A → Tree A

-- Rou

{-
data Rou (A : 𝒰) : 𝒰 where
  overR : Rou A
  nextR : ((▹ Rou A → ▹ Colist A) → Colist A) → Rou A
-}

data RouF (A : 𝒰) (R▹ : ▹ 𝒰) : 𝒰 where
  overRF : RouF A R▹
  nextRF : ((▸ R▹ → ▹ Colist A) → Colist A) → RouF A R▹

module RouF-code where
  Code : {A : 𝒰} {R▹ : ▹ 𝒰} → RouF A R▹ → RouF A R▹ → 𝒰
  Code           overRF      overRF     = ⊤
  Code           overRF     (nextRF _)  = ⊥
  Code          (nextRF _)   overRF     = ⊥
  Code {A} {R▹} (nextRF k₁) (nextRF k₂) = (f : ▸ R▹ → ▹ Colist A) → k₁ f ＝ k₂ f

  Code-refl : {A : 𝒰} {R▹ : ▹ 𝒰} → (r : RouF A R▹) → Code r r
  Code-refl  overRF    = tt
  Code-refl (nextRF k) = λ f → refl

  encode : {A : 𝒰} {R▹ : ▹ 𝒰} {r1 r2 : RouF A R▹} → r1 ＝ r2 → Code r1 r2
  encode {r1} e = subst (Code r1) e (Code-refl r1)

  decode : {A : 𝒰} {R▹ : ▹ 𝒰} (r1 r2 : RouF A R▹) → Code r1 r2 → r1 ＝ r2
  decode  overRF      overRF     _ = refl
  decode (nextRF k₁) (nextRF k₂) c = ap nextRF (fun-ext c)

nextRF-inj : {A : 𝒰} {R▹ : ▹ 𝒰}
           → (k1 k2 : (▸ R▹ → ▹ Colist A) → Colist A)
           → nextRF k1 ＝ nextRF k2
           → k1 ＝ k2
nextRF-inj k1 k2 = fun-ext ∘ RouF-code.encode

Rou : 𝒰 → 𝒰
Rou A = fix (RouF A)

Rou⇉ : Rou A
     → RouF A (next (Rou A))
Rou⇉ {A} = transport (fix-path (RouF A))

⇉Rou : RouF A (next (Rou A))
     → Rou A
⇉Rou {A} = transport ((fix-path (RouF A)) ⁻¹)

{-
Rou-next : 𝒰 → ▹ 𝒰 → 𝒰
Rou-next A rou▹ = (▸ rou▹ → ▹ Colist A) → Colist A

Rou-body : 𝒰 → ▹ 𝒰 → 𝒰
Rou-body A rou▹ = ⊤ ⊎ (Rou-next A rou▹)

Rou : 𝒰 → 𝒰
Rou A = fix (Rou-body A)

nextR⇉ : Rou-next A (dfix (Rou-body A))
       → (▹ Rou A → ▹ Colist A) → Colist A
nextR⇉ {A} = subst (Rou-next A) (pfix (Rou-body A))

⇉nextR : ((▹ Rou A → ▹ Colist A) → Colist A)
       → Rou-next A (dfix (Rou-body A))
⇉nextR {A} = subst (Rou-next A) (sym $ pfix (Rou-body A))
-}

-- constructors & recursor

overR : Rou A
overR = overRF

nextR : ((▹ Rou A → ▹ Colist A) → Colist A) → Rou A
nextR = ⇉Rou ∘ nextRF

recR : B → (((▹ Rou A → ▹ Colist A) → Colist A) → B)
    → Rou A → B
recR b nf r with Rou⇉ r
... | overRF   = b
... | nextRF f = nf f

recR-overR : (b : B) → (f : ((▹ Rou A → ▹ Colist A) → Colist A) → B)
           → recR b f overR ＝ b
recR-overR b f = refl

recR-nextR : (b : B) → (f : ((▹ Rou A → ▹ Colist A) → Colist A) → B)
           → (k : (▹ Rou A → ▹ Colist A) → Colist A)
           → recR b f (nextR k) ＝ f k
recR-nextR {A} b f k = ap f (nextRF-inj _ k (transport⁻-transport ((fix-path (RouF A)) ⁻¹) (nextRF k)))

-- the algorithm

unfold : (▹ Rou A → ▹ Colist A) → Rou A → ▹ Colist A
unfold kf =
  recR (kf (next overR))
       (λ f → next (f kf))

br : Tree A → Rou A → Rou A
br (Leaf a)   c = nextR (λ kf → ccons a (unfold kf c))
br (Br l a r) c = nextR (λ kf → ccons a (unfold (kf ∘ ((br l ∘ br r) ⍉_)) c))

ex-body : ▹ (Rou A → Colist A) → Rou A → Colist A
ex-body ex▹ = recR cnil (λ f → f (ex▹ ⊛_))

ex : Rou A → Colist A
ex = fix ex-body

breadthfirst : Tree A → Colist A
breadthfirst t = ex $ br t overR

-------- correctness + termination

-- non-empty lists (TODO move?)

record List1 (A : 𝒰) : 𝒰 where
  constructor _∷₁_
  field
    hd1 : A
    tl1 : List A

toList : List1 A → List A
toList (h ∷₁ t) = h ∷ t

infixr 5 _++₁_
_++₁_ : List1 A → List1 A → List1 A
(ha ∷₁ ta) ++₁ bs = ha ∷₁ (ta ++ toList bs)

++₁-assoc : (xs ys zs : List1 A) → (xs ++₁ ys) ++₁ zs ＝ xs ++₁ ys ++₁ zs
++₁-assoc (x ∷₁ xs) ys zs = ap (x ∷₁_) (++-assoc xs (toList ys) (toList zs))

concat₁ : List (List1 A) → List A
concat₁ = List.rec [] λ l → (toList l) ++_

catl₁ : List1 A → ▹ Colist A → Colist A
catl₁ (h ∷₁ t) c▹ = ccons h (catList t ⍉ c▹)

catl₁-next : (l1 : List1 A) → (c : Colist A)
           → catl₁ l1 (next c) ＝ catList (toList l1) c
catl₁-next (h ∷₁ t) c = refl

-- BFS spec

zip2 : List (List1 A) → List (List1 A) → List (List1 A)
zip2 []         bs        = bs
zip2 as@(_ ∷ _) []        = as
zip2 (al ∷ as)  (bl ∷ bs) = (al ++₁ bl) ∷ zip2 as bs

zip2-nil : (as : List (List1 A)) → zip2 as [] ＝ as
zip2-nil []        = refl
zip2-nil (al ∷ as) = refl

zip2-assoc : (as bs cs : List (List1 A)) → zip2 as (zip2 bs cs) ＝ zip2 (zip2 as bs) cs
zip2-assoc []        bs        cs        = refl
zip2-assoc (al ∷ as) []        cs        = refl
zip2-assoc (al ∷ as) (bl ∷ bs) []        = refl
zip2-assoc (al ∷ as) (bl ∷ bs) (cl ∷ cs) =
    ap ((al ++₁ bl ++₁ cl) ∷_) (zip2-assoc as bs cs)
  ∙ ap (_∷ zip2 (zip2 as bs) cs) (++₁-assoc al bl cl ⁻¹)

niv : Tree A → List (List1 A)
niv (Leaf x)   = (x ∷₁ []) ∷ []
niv (Br l x r) = (x ∷₁ []) ∷ zip2 (niv l) (niv r)

bfs-spec : Tree A → List A
bfs-spec = concat₁ ∘ niv

-- routine transformer

γ : List (List1 A) → Rou A → Rou A
γ []       r = r
γ (l ∷ ls) r = nextR (λ k▹ → catl₁ l (unfold (λ r▹ → k▹ (γ ls ⍉ r▹)) r))

-- lemmas

γ-ex : (ls : List (List1 A)) → ex (γ ls overR) ＝ fromList (concat₁ ls)
γ-ex []       = refl
γ-ex (l ∷ ls) =
  ex (γ (l ∷ ls) overR)
    ~⟨ ap (λ q → q (nextR (λ k▹ → catl₁ l (unfold (λ r▹ → k▹ (γ ls ⍉ r▹)) overR)))) (fix-path ex-body) ⟩
  recR cnil ((λ f → f (ex ⍉_))) (nextR (λ k▹ → catl₁ l (unfold (λ r▹ → k▹ (γ ls ⍉ r▹)) overR)))
    ~⟨ recR-nextR cnil ((λ f → f (ex ⍉_))) (λ k▹ → catl₁ l (unfold (λ r▹ → k▹ (γ ls ⍉ r▹)) overR)) ⟩
  catl₁ l (next (ex (γ ls overR)))
    ~⟨ ap (catl₁ l) (▹-ext (next (γ-ex ls))) ⟩
  catl₁ l (next (fromList (concat₁ ls)))
    ~⟨ catl₁-next l (fromList (concat₁ ls)) ⟩
  catList (toList l) (fromList (concat₁ ls))
    ~⟨ (catFromList (toList l) (concat₁ ls)) ⟨
  fromList (concat₁ (l ∷ ls))
    ∎
