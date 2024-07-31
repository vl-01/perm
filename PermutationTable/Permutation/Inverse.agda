{-# OPTIONS --safe #-}

module PermutationTable.Permutation.Inverse where

open import Function using (_∘_)

open import PermutationTable.Base
open import PermutationTable.Properties
open import PermutationTable.Permutation.Base

open import Data.Vec using (Vec; allFin; map; lookup; tabulate)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; _≗_; module ≡-Reasoning; trans)

open import Data.Fin using (_≟_)
open import Relation.Nullary using (yes; no; contradiction)

open import Data.Vec.Relation.Unary.Any using (index)
open import Data.Vec.Relation.Unary.Any.Properties using (lookup-index)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (lookup-injective; tabulate⁺)

open import Data.Vec.Properties using (tabulate-∘; tabulate∘lookup; tabulate-cong; lookup-map; map-cong; map-∘; map-lookup-allFin; lookup∘tabulate)

private
  variable
    A : Set
    n m : ℕ

open ≡-Reasoning

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


permute-inverse-id : ∀ {n} (σ : PermutationTable n) → (xs : Vec A n) → permute (σ ⁻¹) (table σ) ≡ allFin n
permute-inverse-id σ@(π , !π) xs = begin
  map (lookup π) (tabulate (index ∘ all-Fin-∈ !π))
    ≡⟨ sym (tabulate-∘ _ _) ⟩
  tabulate (lookup π ∘ index ∘ all-Fin-∈ !π)
    ≡⟨ tabulate-cong (sym ∘ lookup-index ∘ all-Fin-∈ !π) ⟩
  tabulate Function.id
  ∎

permute-inverse-map : ((π , !π) : PermutationTable n) → (f : Fin n → A)
    → lookup (map f π) ∘ index ∘ all-Fin-∈ !π ≗ f
permute-inverse-map (π , !π) f i = begin
  lookup (map f π) ((index ∘ all-Fin-∈ !π) i)
    ≡⟨ lookup-map _ f π ⟩
  f (lookup π (index (all-Fin-∈ !π i)))
    ≡⟨ cong f (sym (lookup-index (all-Fin-∈ !π i))) ⟩
  f i
  ∎

permute-inverseʳ : ∀ {n} (σ : PermutationTable n) → (xs : Vec A n) → permute (σ ⁻¹) (permute σ xs) ≡ xs
permute-inverseʳ σ@(π , !π) xs = begin
  permute (σ ⁻¹) (permute σ xs)
    ≡⟨⟩
  map (lookup (map (lookup xs) π)) (tabulate (index ∘ all-Fin-∈ !π))
    ≡⟨ sym (tabulate-∘ _ _) ⟩
  tabulate (lookup (map (lookup xs) π) ∘ index ∘ all-Fin-∈ !π)
    ≡⟨ tabulate-cong (permute-inverse-map σ (lookup xs)) ⟩
  tabulate (lookup xs)
    ≡⟨ tabulate∘lookup xs ⟩
  xs
  ∎


index-lookup : ((π , !π) : PermutationTable n) → index ∘ all-Fin-∈ !π ∘ lookup π ≗ Function.id
index-lookup (π , !π) i = lookup-injective !π _ _ (sym (lookup-index (all-Fin-∈ !π (lookup π i))))

map-index : ((π , !π) : PermutationTable n) → map (index ∘ all-Fin-∈ !π) π ≡ allFin n
map-index σ@(π , !π) = begin
  map (index ∘ all-Fin-∈ !π) π
    ≡⟨ cong (map (index ∘ all-Fin-∈ !π)) (sym (tabulate∘lookup _)) ⟩
  map (index ∘ all-Fin-∈ !π) (tabulate (lookup π))
    ≡⟨ sym (tabulate-∘ _ _) ⟩
  tabulate (index ∘ all-Fin-∈ !π ∘ lookup π)
    ≡⟨ tabulate-cong (index-lookup σ) ⟩
  tabulate Function.id
  ∎
    
permute-inverseˡ : ∀ {n} (σ : PermutationTable n) → (xs : Vec A n) → permute σ (permute (σ ⁻¹) xs) ≡ xs
permute-inverseˡ σ@(π , !π) xs = begin
  map (lookup (permute (σ ⁻¹) xs)) π
    ≡⟨⟩
  map (lookup (map (lookup xs) (table (σ ⁻¹)))) π
    ≡⟨⟩
  map (lookup (map (lookup xs) (tabulate (index ∘ all-Fin-∈ !π)))) π
    ≡⟨ map-cong (λ i → lookup-map i (lookup xs) (tabulate (index ∘ all-Fin-∈ !π))) π ⟩
  map (lookup xs ∘ lookup (tabulate (index ∘ all-Fin-∈ !π))) π
    ≡⟨ map-cong (cong (lookup xs) ∘ (lookup∘tabulate (index ∘ all-Fin-∈ !π))) π ⟩
  map (lookup xs ∘ index ∘ all-Fin-∈ !π) π
    ≡⟨ map-∘ _ _ _ ⟩
  map (lookup xs) (map (index ∘ all-Fin-∈ !π) π)
    ≡⟨ cong (map (lookup xs)) (map-index σ) ⟩
  map (lookup xs) (allFin _)
    ≡⟨ map-lookup-allFin _ ⟩
  xs
  ∎

