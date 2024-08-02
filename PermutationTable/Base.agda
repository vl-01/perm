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
    n m : ℕ
    ℓ : Level

PermutationTable : ℕ → Set
PermutationTable n = ∃ (λ (xs : Vec (Fin n) n) → Unique xs)

table : ∀ {n} → PermutationTable n → Vec (Fin n) n
table {n} (xs , _) = xs

id : (n : ℕ) → PermutationTable n
id n = allFin n , allFin-Unique

empty : PermutationTable 0
empty = [] , []

open import Relation.Binary.PropositionalEquality using (_≡_; subst)

cast : m ≡ n → PermutationTable m → PermutationTable n
cast eq = subst PermutationTable eq
