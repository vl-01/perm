{-# OPTIONS --safe #-}

module PermutationTable.Permutation where

open import Function using (_∘_)
open import Function.Bundles using (_↔_; mk↔ₛ′; Inverse)
open import Function.Construct.Composition using (_↔-∘_)

open import Data.Vec using (Vec; map; lookup)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)

open import Data.Vec.Properties using (map-cong; map-∘; lookup-map)

open import PermutationTable.Base
open import PermutationTable.Permutation.Base
open import PermutationTable.Permutation.Inverse
open import PermutationTable.Permutation.Properties

open import Relation.Binary.PropositionalEquality using (sym; _≗_; module ≡-Reasoning)

open ≡-Reasoning

private
  variable
    A : Set
    n : ℕ

permutation : ∀ {n} (σ : PermutationTable n) → Vec A n ↔ Vec A n
permutation σ = mk↔ₛ′ (permute σ) (permute (σ ⁻¹)) (permute-inverseˡ σ) (permute-inverseʳ σ)

_∘ₚ_ : PermutationTable n → PermutationTable n → PermutationTable n
σ ∘ₚ (π , !π) = (permute σ π , permute-unique σ !π)

∘ₚ-composes : ∀ {n} (σ τ : PermutationTable n) → Inverse.to (permutation {A = A} (σ ∘ₚ τ)) ≗ Inverse.to (permutation σ ↔-∘ permutation τ)
∘ₚ-composes {n = n} σ@(π , !π) τ@(ρ , !ρ) xs = begin
  map (lookup xs) (map (lookup ρ) π)
    ≡⟨ sym (map-∘ _ _ _) ⟩
  map (lookup xs ∘ lookup ρ) π
    ≡⟨ map-cong (λ i → sym (lookup-map i (lookup xs) ρ)) π ⟩
  map (lookup (permute τ xs)) π
  ∎
