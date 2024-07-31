{-# OPTIONS --safe #-}

module PermutationTable.Base where

open import Level using (Level)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (∃; _,_)
open import Data.Vec using (Vec; []; allFin)
open import Data.Fin using (Fin)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique; [])
open import PermutationTable.Properties.Unique

private
  variable
    n m k : ℕ
    ℓ : Level

PermutationTable′ : ℕ → ℕ  → Set
PermutationTable′ n m = ∃ (λ (xs : Vec (Fin n) m) → Unique xs)

PermutationTable : ℕ → Set
PermutationTable n = PermutationTable′ n n

table : ∀ {n} → PermutationTable n → Vec (Fin n) n
table {n} (xs , _) = xs

id : (n : ℕ) → PermutationTable n
id n = allFin n , allFin-Unique

empty : PermutationTable 0
empty = [] , []
