{-# OPTIONS --safe #-}

module PermutationTable.TranspositionList where

open import Data.Nat using (ℕ)
open import Data.Fin.Permutation.Transposition.List using (TranspositionList)
open import PermutationTable
open import Data.List using (_∷_; [])
open import Data.Product using (_,_)

private
  variable
    n : ℕ

eval : TranspositionList n → PermutationTable n
eval [] = PermutationTable.id _
eval ((i , j) ∷ idxs) = transpose i j (eval idxs)

