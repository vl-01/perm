{-# OPTIONS --safe #-}

module PermutationTable.Permutation.Base where

open import Function using (_∘_)

open import Data.Fin using (Fin)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; tabulate; map; lookup)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Relation.Unary.Any using (index)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PermutationTable.Base
open import PermutationTable.Properties

private
  variable
    A : Set
    n : ℕ

permute : PermutationTable n → Vec A n → Vec A n
permute σ xs = map (lookup xs) (table σ)

permute′ : PermutationTable n → Vec A n → Vec A n
permute′ σ xs = tabulate (lookup xs ∘ lookup (table σ))

permute-empty : (σ : PermutationTable 0) → (xs : Vec A 0) → permute σ xs ≡ xs
permute-empty ([] , _) [] = refl
