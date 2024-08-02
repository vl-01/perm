{-# OPTIONS --safe #-}

module PermutationTable where

open import Level using (Level)

open import Function using (_∘_)

open import Data.Nat using (ℕ)
private
  variable
    A : Set
    n m k : ℕ
    ℓ : Level

open import PermutationTable.Base public
