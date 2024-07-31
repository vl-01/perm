{-# OPTIONS --safe #-}

module PermutationTable.Transposition where

open import PermutationTable.Base
open import PermutationTable.Components.Base public

transpose : ∀ (i j : Fin n) → PermutationTable n → PermutationTable n
transpose i j = dmap (transpose′ i j) (transpose-unique i j)

transpose↔ : ∀ (i j : Fin n) → PermutationTable n ↔ PermutationTable n
transpose↔ i j = mk↔ₛ′ swp swp inv inv
  where
  swp = transpose i j
  inv : (xs : PermutationTable _) → swp (swp xs) ≡ xs
  inv (xs , _) = Σ-≡,≡→≡ (transpose-involutive i j xs , unique-irrelevant _ _)
