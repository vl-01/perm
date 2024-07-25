{-# OPTIONS --safe #-}

module PermutationTable.Components.Inverse where

open import Data.Fin using (Fin)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ)

open import PermutationTable.Components.Base
open import PermutationTable.Components.Properties
open import Function.Bundles using (_↔_; mk↔ₛ′)

private
  variable
    n : ℕ

transpose↔ : ∀ (i j : Fin n) → Vec (Fin n) n ↔ Vec (Fin n) n
transpose↔ i j = mk↔ₛ′ swp swp inv inv
  where
  swp = transpose i j
  inv = transpose-involutive i j
