{-# OPTIONS --safe #-}

module PermutationTable.TranspositionList.Properties where

open import Relation.Nullary.Decidable.Core using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; sym; cong; module ≡-Reasoning)

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec using (lookup)
open import Data.List using (_∷_; [])
open import Data.Fin using (_≟_)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Permutation.Components renaming (transpose to transpose-⊙)
open import Data.Fin.Permutation.Transposition.List using (TranspositionList) renaming (eval to evalᴾ)
open import Data.Sum using (inj₂)

open import PermutationTable.Base
open import PermutationTable.TranspositionList renaming (eval to evalᵀ)

open import PermutationTable.Components.Properties
open import Supplementary.Data.Fin.Permutation.Components.Properties

import Data.Vec.Properties as Vecₚ

open ≡-Reasoning

private
  variable
    n : ℕ

index-computable : (σ : TranspositionList n) → evalᴾ σ ⟨$⟩ʳ_ ≗ lookup (table (evalᵀ σ))
index-computable [] _ = sym (Vecₚ.lookup-allFin _)
index-computable ((i , j) ∷ σ) k = h (k ≟ i) (k ≟ j)
  where
  π = evalᵀ σ
  h : Dec (k ≡ i) → Dec (k ≡ j) → evalᴾ ((i , j) ∷ σ) ⟨$⟩ʳ k ≡ lookup (table (evalᵀ ((i , j) ∷ σ))) k
  h (yes k≡i) _ = begin
    evalᴾ ((i , j) ∷ σ) ⟨$⟩ʳ k
      ≡⟨ cong _ k≡i ⟩
    evalᴾ ((i , j) ∷ σ) ⟨$⟩ʳ i
      ≡⟨⟩
    evalᴾ σ ⟨$⟩ʳ (transpose-⊙ i j i)
      ≡⟨ cong (evalᴾ σ ⟨$⟩ʳ_) (transpose-i-j-i i j) ⟩
    evalᴾ σ ⟨$⟩ʳ j
      ≡⟨ index-computable σ j ⟩
    lookup (table π) j
      ≡⟨ sym (lookup-transposeˡ i j (table π)) ⟩
    lookup (table (transpose i j π)) i
      ≡⟨ cong _ (sym k≡i) ⟩
    lookup (table (transpose i j π)) k
    ∎
  h (no _) (yes k≡j) = begin
    evalᴾ ((i , j) ∷ σ) ⟨$⟩ʳ k
      ≡⟨ cong _ k≡j ⟩
    evalᴾ ((i , j) ∷ σ) ⟨$⟩ʳ j
      ≡⟨⟩
    evalᴾ σ ⟨$⟩ʳ (transpose-⊙ i j j)
      ≡⟨ cong (evalᴾ σ ⟨$⟩ʳ_) (transpose-i-j-j i j) ⟩
    evalᴾ σ ⟨$⟩ʳ i
      ≡⟨ index-computable σ i ⟩
    lookup (table π) i
      ≡⟨ sym (lookup-transposeʳ i j (table π)) ⟩
    lookup (table (transpose i j π)) j
      ≡⟨ cong _ (sym k≡j) ⟩
    lookup (table (transpose i j π)) k
    ∎
  h (no k≢i) (no  k≢j) = begin
    evalᴾ ((i , j) ∷ σ) ⟨$⟩ʳ k
      ≡⟨⟩
    evalᴾ σ ⟨$⟩ʳ (transpose-⊙ i j k)
      ≡⟨ cong (evalᴾ σ ⟨$⟩ʳ_) (transpose-i-j-k i j k k≢i k≢j) ⟩
    evalᴾ σ ⟨$⟩ʳ k
      ≡⟨ index-computable σ k ⟩
    lookup (table π) k
      ≡⟨ sym (transpose-minimal i j k (table π) (inj₂ (k≢i , k≢j))) ⟩
    lookup (table (transpose i j π)) k
    ∎
