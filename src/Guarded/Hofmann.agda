{-# OPTIONS --guarded --lossy-unification #-}
module Guarded.Hofmann where

open import Prelude
open import Data.Empty
open import Data.Sum
open import Data.List as List

open import LaterG
open import Guarded.Colist

private variable
  ℓ   : Level
  A B : 𝒰 ℓ

-- It is crucial for the algorithm that the tree is non-empty on each level.

-- The algorithm can also be extended to Tree∞.

data Tree (A : 𝒰 ℓ) : 𝒰 ℓ where
  Leaf :          A          → Tree A
  Br   : Tree A → A → Tree A → Tree A

-- Rou

{-
data Rou (A : 𝒰) : 𝒰 where
  overR : Rou A
  nextR : ((▹ Rou A → ▹ Colist A) → Colist A) → Rou A
-}

data RouF (A : 𝒰 ℓ) (R▹ : ▹ 𝒰 ℓ) : 𝒰 ℓ where
  overRF : RouF A R▹
  nextRF : ((▸ R▹ → ▹ Colist A) → Colist A) → RouF A R▹

module RouF-code where
  Code : {A : 𝒰 ℓ} {R▹ : ▹ 𝒰 ℓ} → RouF A R▹ → RouF A R▹ → 𝒰 ℓ
  Code           overRF      overRF     = Lift _ ⊤
  Code           overRF     (nextRF _)  = Lift _ ⊥
  Code          (nextRF _)   overRF     = Lift _ ⊥
  Code {A} {R▹} (nextRF k₁) (nextRF k₂) = (f : ▸ R▹ → ▹ Colist A) → k₁ f ＝ k₂ f

  Code-refl : {A : 𝒰 ℓ} {R▹ : ▹ 𝒰 ℓ}
            → (r : RouF A R▹) → Code r r
  Code-refl  overRF    = lift tt
  Code-refl (nextRF k) = λ f → refl

  encode : {A : 𝒰 ℓ} {R▹ : ▹ 𝒰 ℓ} {r1 r2 : RouF A R▹} → r1 ＝ r2 → Code r1 r2
  encode {r1} e = subst (Code r1) e (Code-refl r1)

  decode : {A : 𝒰 ℓ} {R▹ : ▹ 𝒰 ℓ} (r1 r2 : RouF A R▹) → Code r1 r2 → r1 ＝ r2
  decode  overRF      overRF     _ = refl
  decode (nextRF k₁) (nextRF k₂) c = ap nextRF (fun-ext c)

nextRF-inj : {A : 𝒰 ℓ} {R▹ : ▹ 𝒰 ℓ}
           → {k1 k2 : (▸ R▹ → ▹ Colist A) → Colist A}
           → nextRF k1 ＝ nextRF k2
           → k1 ＝ k2
nextRF-inj = fun-ext ∘ RouF-code.encode

Rou : 𝒰 ℓ → 𝒰 ℓ
Rou A = fix (RouF A)

Rou-path : Rou A ＝ RouF A (next (Rou A))
Rou-path {A} = fix-path (RouF A)

Rou⇉ : Rou A
     → RouF A (next (Rou A))
Rou⇉ = transport Rou-path

⇉Rou : RouF A (next (Rou A))
     → Rou A
⇉Rou = transport (Rou-path ⁻¹)

-- constructors & pattern matching

overR : Rou A
overR = overRF

nextR : ((▹ Rou A → ▹ Colist A) → Colist A) → Rou A
nextR = ⇉Rou ∘ nextRF

matchR : B → (((▹ Rou A → ▹ Colist A) → Colist A) → B)
       → Rou A → B
matchR b nf r with Rou⇉ r
... | overRF   = b
... | nextRF f = nf f

matchR-overR : {b : B} {f : ((▹ Rou A → ▹ Colist A) → Colist A) → B}
             → matchR b f overR ＝ b
matchR-overR = refl

matchR-nextR : {b : B}
             → {f : ((▹ Rou A → ▹ Colist A) → Colist A) → B}
             → {k : (▹ Rou A → ▹ Colist A) → Colist A}
             → matchR b f (nextR k) ＝ f k
matchR-nextR {f} {k} = ap f (nextRF-inj (transport⁻-transport (Rou-path ⁻¹) (nextRF k)))

-- the algorithm

unfold : (▹ Rou A → ▹ Colist A) → Rou A → ▹ Colist A
unfold kf = matchR (kf (next overR)) λ f → next (f kf)

br : Tree A → Rou A → Rou A
br (Leaf a)   c = nextR λ kf → ccons a (unfold kf c)
br (Br l a r) c = nextR λ kf → ccons a (unfold (kf ∘ ((br l ∘ br r) ⍉_)) c)

ex-body : ▹ (Rou A → Colist A) → Rou A → Colist A
ex-body ex▹ = matchR cnil λ f → f (ex▹ ⊛_)

ex : Rou A → Colist A
ex = fix ex-body

breadthfirst : Tree A → Colist A
breadthfirst t = ex $ br t overR

-------- correctness + termination

-- non-empty lists (TODO move?)

record List1 (A : 𝒰 ℓ) : 𝒰 ℓ where
  constructor _∷₁_
  field
    hd1 : A
    tl1 : List A

open List1

[_]₁ : A → List1 A
[ a ]₁ = a ∷₁ []

toList : List1 A → List A
toList (h ∷₁ t) = h ∷ t

infixr 5 _++₁_
_++₁_ : List1 A → List1 A → List1 A
(ha ∷₁ ta) ++₁ bs = ha ∷₁ (ta ++ toList bs)

++₁-assoc : {xs ys zs : List1 A} → (xs ++₁ ys) ++₁ zs ＝ xs ++₁ ys ++₁ zs
++₁-assoc {xs = x ∷₁ xs} {ys} {zs} = ap (x ∷₁_) (++-assoc xs (toList ys) (toList zs))

concat₁ : List (List1 A) → List A
concat₁ = List.rec [] λ l → toList l ++_

catl₁ : List1 A → ▹ Colist A → Colist A
catl₁ (h ∷₁ t) c▹ = ccons h (catList t ⍉ c▹)

catl₁-next : {c : Colist A} → (l1 : List1 A)
           → catl₁ l1 (next c) ＝ catList (toList l1) c
catl₁-next (h ∷₁ t) = refl

-- TODO adhoc
catList-catl₁-aux : {c▹ : ▹ Colist A} → (l : List A) → (l1 : List1 A)
                  → ▹[ α ] (catList l (catl₁ l1 c▹) ＝ catList (l ++ toList l1) (c▹ α))
catList-catl₁-aux {c▹} []      l1 α =
  ap (ccons (l1 .hd1)) (▹-ext λ β → ap (catList (l1 .tl1)) (tick-irr c▹ α β ⁻¹))
catList-catl₁-aux {c▹} (h ∷ t) l1 α =
  ap (ccons h) (▹-ext λ β → catList-catl₁-aux t l1 α)

catList-catl₁ : {c▹ : ▹ Colist A} → (l1 l2 : List1 A)
              → catList (toList l1) (catl₁ l2 c▹) ＝ catl₁ (l1 ++₁ l2) c▹
catList-catl₁ (h1 ∷₁ t1) l2 = ap (ccons h1) (▹-ext (catList-catl₁-aux t1 l2))

-- BFS spec

zip2 : List (List1 A) → List (List1 A) → List (List1 A)
zip2    []         bs       = bs
zip2 as@(_ ∷ _)    []       = as
zip2    (al ∷ as) (bl ∷ bs) = (al ++₁ bl) ∷ zip2 as bs

zip2-nil : (as : List (List1 A)) → zip2 as [] ＝ as
zip2-nil []        = refl
zip2-nil (al ∷ as) = refl

zip2-assoc : (as bs cs : List (List1 A))
           → zip2 as (zip2 bs cs) ＝ zip2 (zip2 as bs) cs
zip2-assoc []        bs        cs        = refl
zip2-assoc (al ∷ as) []        cs        = refl
zip2-assoc (al ∷ as) (bl ∷ bs) []        = refl
zip2-assoc (al ∷ as) (bl ∷ bs) (cl ∷ cs) =
    ap ((al ++₁ bl ++₁ cl) ∷_) (zip2-assoc as bs cs)
  ∙ ap (_∷ zip2 (zip2 as bs) cs) (++₁-assoc ⁻¹)

niv : Tree A → List (List1 A)
niv (Leaf x)   = [ x ]₁ ∷ []
niv (Br l x r) = [ x ]₁ ∷ zip2 (niv l) (niv r)

bfs-spec : Tree A → List A
bfs-spec = concat₁ ∘ niv

-- routine transformer

γ : List (List1 A) → Rou A → Rou A
γ []       r = r
γ (l ∷ ls) r = nextR λ k▹ → catl₁ l (unfold (λ r▹ → k▹ (γ ls ⍉ r▹)) r)

-- lemmas

γ-ex : (ls : List (List1 A)) → ex (γ ls overR) ＝ fromList (concat₁ ls)
γ-ex []       = refl
γ-ex (l ∷ ls) =
  ex (γ (l ∷ ls) overR)
    ~⟨ ap (λ q → q (nextR (λ k▹ → catl₁ l (unfold (λ r▹ → k▹ (γ ls ⍉ r▹)) overR))))
          (fix-path ex-body) ⟩
  matchR cnil ((λ f → f (ex ⍉_)))
         (nextR (λ k▹ → catl₁ l (unfold (λ r▹ → k▹ (γ ls ⍉ r▹)) overR)))
    ~⟨ matchR-nextR ⟩
  catl₁ l (next (ex (γ ls overR)))
    ~⟨ ap (catl₁ l) (▹-ext (next (γ-ex ls))) ⟩
  catl₁ l (next (fromList (concat₁ ls)))
    ~⟨ catl₁-next l ⟩
  catList (toList l) (fromList (concat₁ ls))
    ~⟨ catFromList (toList l) (concat₁ ls) ⟨
  fromList (concat₁ (l ∷ ls))
    ∎

γ-comp : (ls ls1 : List (List1 A)) → γ ls ∘ γ ls1 ＝ γ (zip2 ls ls1)
γ-comp []       ls1        = refl
γ-comp (l ∷ ls) []         = refl
γ-comp (l ∷ ls) (l1 ∷ ls1) = fun-ext λ c →
  γ (l ∷ ls) (γ (l1 ∷ ls1) c)
    ~⟨⟩
  γ (l ∷ ls) (nextR (λ k▹ → catl₁ l1 (unfold (λ r▹ → k▹ (γ ls1 ⍉ r▹)) c)))
    ~⟨⟩
  nextR (λ k▹ → catl₁ l (unfold (λ r▹ → k▹ (γ ls ⍉ r▹))
                                (nextR (λ k▹ → catl₁ l1 (unfold (λ r▹ → k▹ (γ ls1 ⍉ r▹)) c)))))
    ~⟨⟩
  nextR (λ k▹ → catl₁ l (matchR (k▹ (next (γ ls overR))) (λ f → next (f (λ r▹ → k▹ (γ ls ⍉ r▹))))
                                (nextR (λ k▹ → catl₁ l1 (unfold (λ r▹ → k▹ (γ ls1 ⍉ r▹)) c)))))
    ~⟨ ap nextR (fun-ext λ k▹ → ap (catl₁ l) matchR-nextR) ⟩
  nextR (λ k▹ → catl₁ l (next (catl₁ l1 (unfold (λ r▹ → k▹ (γ ls ⍉ (γ ls1 ⍉ r▹))) c))))
    ~⟨ ap nextR (fun-ext λ k▹ → catl₁-next l ∙ catList-catl₁ l l1) ⟩
  nextR (λ k▹ → catl₁ (l ++₁ l1) (unfold (λ r▹ → k▹ (γ ls ⍉ (γ ls1 ⍉ r▹))) c))
    ~⟨ ap nextR (fun-ext λ k▹ → ap (λ q → catl₁ (l ++₁ l1) (unfold q c))
                                   (fun-ext λ r▹ → ap k▹ (▹-ext λ α → happly (γ-comp ls ls1) (r▹ α)))) ⟩
  nextR (λ k▹ → catl₁ (l ++₁ l1) (unfold (λ r▹ → k▹ (γ (zip2 ls ls1) ⍉ r▹)) c))
    ~⟨⟩
  γ ((l ++₁ l1) ∷ zip2 ls ls1) c
    ~⟨⟩
  γ (zip2 (l ∷ ls) (l1 ∷ ls1)) c
    ∎

γ-niv : (t : Tree A) → (c : Rou A) → br t c ＝ γ (niv t) c
γ-niv (Leaf x)   c = refl
γ-niv (Br l x r) c =
  br (Br l x r) c
    ~⟨⟩
  nextR (λ k▹ → ccons x (unfold (λ r▹ → k▹ ((br l ∘ br r) ⍉ r▹)) c))
    ~⟨ ap nextR (fun-ext λ k▹ →
         ap (λ q → ccons x (unfold q c))
            (fun-ext λ r▹ → ap k▹ (▹-ext λ α →
                happly (  fun-ext (λ z → ap (br l) (γ-niv r z) ∙ γ-niv l (γ (niv r) z))
                        ∙ γ-comp (niv l) (niv r))
                       (r▹ α)))) ⟩
  nextR (λ k▹ → ccons x (unfold (λ r▹ → k▹ (γ (zip2 (niv l) (niv r)) ⍉ r▹)) c))
    ~⟨⟩
  γ ([ x ]₁ ∷ zip2 (niv l) (niv r)) c
    ~⟨⟩
  γ (niv (Br l x r)) c
    ∎

bfs-correct : (t : Tree A) → breadthfirst t ＝ fromList (bfs-spec t)
bfs-correct t =
  breadthfirst t             ~⟨⟩
  ex (br t overR)            ~⟨ ap ex (γ-niv t overR) ⟩
  ex (γ (niv t) overR)       ~⟨ γ-ex (niv t) ⟩
  fromList (concat₁ (niv t)) ~⟨⟩
  fromList (bfs-spec t)      ∎

bfs-terminates : (t : Tree A) → is-finiteˡ (breadthfirst t)
bfs-terminates t = bfs-spec t , (bfs-correct t ⁻¹)
