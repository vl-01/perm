{-# OPTIONS --safe #-}

module PermutationTable.Permutation.Base where

open import Function using (_∘_)

open import Data.Fin using (Fin)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; tabulate; map; lookup)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Relation.Unary.Any using (index)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (tabulate⁺)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import PermutationTable.Base
open import PermutationTable.Properties

private
  variable
    A : Set
    n m : ℕ

module _ where
  private module _ where
    open import Data.Vec.Relation.Unary.Any using (index; here; there)
    open import Data.Fin.Properties using (suc-injective)
    open import Data.Vec.Membership.Propositional using (_∈_)

    lemma : {i j : Fin n} → {xs : Vec (Fin n) m}
          → (∃i : i ∈ xs) → (∃j : j ∈ xs) → index ∃i ≡ index ∃j → i ≡ j
    lemma (here i=x) (here j=x) _ = trans i=x (sym j=x)
    lemma (there ∃i) (there ∃j) x = lemma ∃i ∃j (suc-injective x)

  _⁻¹ : PermutationTable n → PermutationTable n
  (σ , !σ)⁻¹ = (σ⁻¹ , !σ⁻¹)
    where
    σ⁻¹ : Vec (Fin _) _
    σ⁻¹ = tabulate (index ∘ all-Fin-∈ !σ)
    !σ⁻¹ : Unique σ⁻¹
    !σ⁻¹ = tabulate⁺ (lemma (all-Fin-∈ !σ _) (all-Fin-∈ !σ _))

permute : PermutationTable n → Vec A n → Vec A n
permute σ xs = map (lookup xs) (table σ)

permute′ : PermutationTable n → Vec A n → Vec A n
permute′ σ xs = tabulate (lookup xs ∘ lookup (table σ))

permute-empty : (σ : PermutationTable 0) → (xs : Vec A 0) → permute σ xs ≡ xs
permute-empty ([] , _) [] = refl
