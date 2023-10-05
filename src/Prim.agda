{-# OPTIONS --guarded #-}
module Prim where

open import Prelude

module Prims where
  primitive
    primLockUniv : 𝒰₁

open Prims renaming (primLockUniv to LockU) public
