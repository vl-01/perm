{-# OPTIONS --safe #-}

module PermutationTable.Components.Base where

open import Data.Fin using (Fin)
open import Data.Vec using (Vec; lookup; _[_]≔_)
open import Data.Nat using (ℕ)

private
  variable
    A : Set
    n : ℕ

transpose : ∀ (i j : Fin n) → Vec A n → Vec A n
transpose i j xs = xs [ i ]≔ lookup xs j [ j ]≔ lookup xs i
