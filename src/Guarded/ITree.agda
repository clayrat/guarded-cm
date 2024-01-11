{-# OPTIONS --guarded #-}
module Guarded.ITree where

open import Prelude
open import Data.Maybe

open import LaterG

-- guarded interaction tree (Frumin-Timany-Birkedal'23)

{-
data ITree (S : 𝒰) (I O : S → 𝒰 → 𝒰) (A : 𝒰) : 𝒰 where
  ret : A → ITree S I O A
  fun : ▹ (ITree S I O A → ITree S I O A) → ITree S I O A
  err : ITree S I O A
  tau : ▹ ITree S I O A → ITree S I O A
  vis : (s : S) → I s (▹ ITree S I O A) → (O s (▹ ITree S I O A) → ▹ ITree S I O A) → ITree S I O A
-}

data ITreeF (S : 𝒰) (I O : S → 𝒰 → 𝒰) (A : 𝒰) (T▹ : ▹ 𝒰) : 𝒰 where
  retF : A → ITreeF S I O A T▹
  funF : ▹[ α ] (T▹ α → T▹ α)
       → ITreeF S I O A T▹
  errF : ITreeF S I O A T▹
  tauF : ▸ T▹
       → ITreeF S I O A T▹
  visF : (s : S)
       → I s (▸ T▹)
       → (O s (▸ T▹) → ▸ T▹)
       → ITreeF S I O A T▹

ITree : (S : 𝒰) (I O : S → 𝒰 → 𝒰) (A : 𝒰) → 𝒰
ITree S I O A = fix (ITreeF S I O A)

ITree⇉ : ∀ {S I O A}
         → ITree S I O A
         → ITreeF S I O A (next (ITree S I O A))
ITree⇉ {S} {I} {O} {A} = transport (fix-path (ITreeF S I O A))

⇉ITree : ∀ {S I O A}
         → ITreeF S I O A (next (ITree S I O A))
         → ITree S I O A
⇉ITree {S} {I} {O} {A} = transport (sym $ fix-path (ITreeF S I O A))

-- constructors

ret : ∀ {S I O A}
    → A → ITree S I O A
ret = ⇉ITree ∘ retF

fun : ∀ {S I O A}
    → ▹ (ITree S I O A → ITree S I O A) → ITree S I O A
fun = ⇉ITree ∘ funF

err : ∀ {S I O A}
    → ITree S I O A
err = ⇉ITree errF

tau : ∀ {S I O A}
    → ▹ ITree S I O A → ITree S I O A
tau = ⇉ITree ∘ tauF

vis : ∀ {S I O A}
    → (s : S)
    → I s (▹ ITree S I O A)
    → (O s (▹ ITree S I O A)
    → ▹ ITree S I O A) → ITree S I O A
vis s i o = ⇉ITree (visF s i o)

-- bottom

bottom : ∀ {S I O A}
       → ITree S I O A
bottom = fix tau

-- IO

data SigIO : 𝒰 where
  input output : SigIO

InsIO : SigIO → 𝒰 → 𝒰
InsIO input  _ = ⊤
InsIO output _ = ℕ

OutsIO : SigIO → 𝒰 → 𝒰
OutsIO input  _ = ℕ
OutsIO output _ = ⊤

IOℕ : 𝒰
IOℕ = ITree SigIO InsIO OutsIO (Maybe ℕ)

Input : IOℕ
Input = vis input tt λ n →
        next (ret (just n))

Output : ℕ → IOℕ
Output n = vis output n λ _ →
           next (ret nothing)

-- higher-order store

data SigST : 𝒰 where
  alloc read write dealloc : SigST

-- nats = pointers
InsST : SigST → 𝒰 → 𝒰
InsST alloc   X = X
InsST read    _ = ℕ
InsST write   X = ℕ × X
InsST dealloc _ = ℕ

OutsST : SigST → 𝒰 → 𝒰
OutsST alloc   _ = ℕ
OutsST read    X = X
OutsST write   _ = ⊤
OutsST dealloc _ = ⊤

IOS : 𝒰 → 𝒰
IOS = ITree SigST InsST OutsST

Alloc : {A : 𝒰}
      → IOS A → (ℕ → IOS A) → IOS A
Alloc a k = vis alloc (next a) (next ∘ k)

Read : {A : 𝒰}
     → ℕ → IOS A
Read l = vis read l id

Write : {A : 𝒰}
      → ℕ → IOS (Maybe A) → IOS (Maybe A)
Write l a = vis write (l , next a) λ _ →
            next (ret nothing)

Dealloc : {A : 𝒰}
        → ℕ → IOS (Maybe A)
Dealloc l = vis dealloc l λ _ →
            next (ret nothing)
