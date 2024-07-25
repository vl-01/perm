{-# OPTIONS --safe #-}

module PermutationTable.Base where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (∃; _,_)
open import Data.Vec using (Vec; allFin)
open import Data.Fin using (Fin)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
open import PermutationTable.Properties.Unique

private
  variable
    n : ℕ

PermutationTable : ℕ → Set
PermutationTable n = ∃ (λ (xs : Vec (Fin n) n) → Unique xs)

table : ∀ {n} → PermutationTable n → Vec (Fin n) n
table {n} (xs , _) = xs

id : (n : ℕ) → PermutationTable n
id n = allFin n , allFin-Unique

open Data.Product using (dmap)
open import PermutationTable.Components.Properties
open import PermutationTable.Components renaming (transpose to transpose′)
open Data.Product using (dmap)

transpose : ∀ (i j : Fin n) → PermutationTable n → PermutationTable n
transpose i j = dmap (transpose′ i j) (transpose-unique i j)

open import Function.Bundles using (_↔_; mk↔ₛ′)
open Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product.Properties using (Σ-≡,≡→≡)

transpose↔ : ∀ (i j : Fin n) → PermutationTable n ↔ PermutationTable n
transpose↔ i j = mk↔ₛ′ swp swp inv inv
  where
  swp = transpose i j
  inv : (xs : Σ (Vec (Fin _) _) Unique) → swp (swp xs) ≡ xs
  inv (xs , _) = Σ-≡,≡→≡ (transpose-involutive i j xs , unique-irrelevant _ _)
