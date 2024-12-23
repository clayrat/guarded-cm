{-# OPTIONS --guarded #-}
module Guarded.BushNFix where

open import Prelude
open import Data.List

open import LaterG
open import Guarded.Partial

private variable
  ℓ : Level
  X : 𝒰 ℓ

-- n-ary tree automaton via fixpoint in the universe

BushG : ▹ (𝒰 ℓ → 𝒰 ℓ) → ▹ (𝒰 ℓ → 𝒰 ℓ) → 𝒰 ℓ → 𝒰 ℓ
BushG F▹ G▹ X = X × (▸ (F▹ ⊛ (G▹ ⊛ next X)))

BushF : ▹ (𝒰 ℓ → 𝒰 ℓ) → 𝒰 ℓ → 𝒰 ℓ
BushF = fix ∘ BushG

Bush : 𝒰 ℓ → 𝒰 ℓ
Bush = fix BushF

opaque 
  BushG-path′ : (F▹ : ▹ (𝒰 ℓ → 𝒰 ℓ)) → BushF F▹ ＝ BushG F▹ (next (BushF F▹))
  BushG-path′ F▹ = fix-path (BushG F▹)

  BushG-path : (F▹ : ▹ (𝒰 ℓ → 𝒰 ℓ)) → BushF F▹ X ＝ BushG F▹ (next (BushF F▹)) X
  BushG-path {X} F▹ = happly (fix-path (BushG F▹)) X

  BushG⇉ : (F▹ : ▹ (𝒰 ℓ → 𝒰 ℓ)) → BushF F▹ X → BushG F▹ (next (BushF F▹)) X
  BushG⇉ F▹ = transport (BushG-path F▹)

  ⇉BushG : (F▹ : ▹ (𝒰 ℓ → 𝒰 ℓ)) → BushG F▹ (next (BushF F▹)) X → BushF F▹ X
  ⇉BushG F▹ = transport (BushG-path F▹ ⁻¹)

  Bush-path′ : Bush {ℓ} ＝ BushF (next Bush)
  Bush-path′ = fix-path BushF

  Bush-path : Bush X ＝ BushF (next Bush) X
  Bush-path {X} = happly (fix-path BushF) X

  Bush1⇉ : Bush X → BushF (next Bush) X
  Bush1⇉ = transport Bush-path

  ⇉Bush1 : BushF (next Bush) X → Bush X
  ⇉Bush1 = transport (Bush-path ⁻¹)

  Bush-path2 : Bush X ＝ BushG (next Bush) (next (BushF (next Bush))) X
  Bush-path2 {X} = Bush-path ∙ BushG-path (next Bush)

  Bush2⇉ : Bush X → BushG (next Bush) (next (BushF (next Bush))) X
  Bush2⇉ = transport Bush-path2

  ⇉Bush2 : BushG (next Bush) (next (BushF (next Bush))) X → Bush X
  ⇉Bush2 = transport (Bush-path2 ⁻¹)

  Bush-path3 : Bush X ＝ BushG (next Bush) (next Bush) X
  Bush-path3 {X} =
       Bush-path
     ∙ BushG-path (next Bush)
     ∙ ap (λ q → BushG (next Bush) q X) (▹-ext λ _ → Bush-path′ ⁻¹)

  Bush3⇉ : Bush X → BushG (next Bush) (next Bush) X
  Bush3⇉ = transport Bush-path3

  ⇉Bush3 : BushG (next Bush) (next Bush) X → Bush X
  ⇉Bush3 = transport (Bush-path3 ⁻¹)

consᵇ : X → ▹ (Bush (Bush X)) → Bush X
consᵇ x xs▹ = ⇉Bush3 (x , xs▹)

unconsᵇ : Bush X → X × ▹ (Bush (Bush X))
unconsᵇ = Bush3⇉

headᵇ : Bush X → X
headᵇ = fst ∘ unconsᵇ

tail▹ᵇ : Bush X → ▹ (Bush (Bush X))
tail▹ᵇ = snd ∘ unconsᵇ

-- finitary tree

record FT : 𝒰 where
  inductive
  constructor nd
  field
    ch : List FT

open FT

lamFT-body : ▹ ({X : 𝒰 ℓ} → (FT → X) → Bush X)
           →    {X : 𝒰 ℓ} → (FT → X) → Bush X
lamFT-body l▹ {X} f =
  consᵇ (f (nd [])) λ α → l▹ α λ t → l▹ α λ u → f (nd (u .ch ++ t .ch))  -- ?

lamFT : (FT → X) → Bush X
lamFT = fix lamFT-body

mutual
  appFT-body : ▹ ({X : 𝒰 ℓ} → Bush X → FT → Part X)
             →    {X : 𝒰 ℓ} → Bush X → FT → Part X
  appFT-body a▹ b f = appFT-list a▹ b (f .ch)

  appFT-list : ▹ ({X : 𝒰 ℓ} → Bush X → FT → Part X)
             →    {X : 𝒰 ℓ} → Bush X → List FT → Part X
  appFT-list a▹ b []       = now (headᵇ b)
  appFT-list a▹ b (x ∷ xs) = later λ α → a▹ α (tail▹ᵇ b α) x >>=ᵖ λ b → appFT-list a▹ b xs

appBT : Bush X → FT → Part X
appBT = fix appFT-body
