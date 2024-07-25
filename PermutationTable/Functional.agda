{-# OPTIONS --safe #-}

module PermutationTable.Functional where

open import Data.Product using (_,_)
open import Data.Nat.Base using (ℕ)
open import Data.Vec using (Vec; allFin; lookup)
open import Data.Fin using (Fin)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; module ≡-Reasoning)

import Data.Vec.Properties as Vecₚ
open import PermutationTable.Components.Properties
open import PermutationTable.Components using () renaming (transpose to transposeᵀ)

open ≡-Reasoning

private
  variable
    A : Set
    n : ℕ

toVector : ∀ (f : Vec (Fin n) n → Vec A n) → Fin n → A
toVector f = lookup (f (allFin _))

transpose : ∀ (i j : Fin n) → Fin n → Fin n
transpose {n = n} i j = toVector (transposeᵀ i j)

open import Data.Sum using (inj₂)
open import Relation.Nullary.Decidable.Core using (yes; no; Dec)

transpose-lemmaˡ : ∀ (i j k : Fin n) → k ≡ i → transpose i j k ≡ j
transpose-lemmaˡ i j k k≡i = begin
  lookup (transposeᵀ i j (allFin _)) k
    ≡⟨ cong (lookup (transposeᵀ i j (allFin _))) k≡i ⟩
  lookup (transposeᵀ i j (allFin _)) i
    ≡⟨ lookup-transposeˡ i j (allFin _) ⟩
  lookup (allFin _) j
    ≡⟨ Vecₚ.lookup-allFin _ ⟩
  j
  ∎
transpose-lemmaʳ : (i j k : Fin n) → k ≡ j → transpose i j k ≡ i
transpose-lemmaʳ i j k k≡j = begin
  lookup (transposeᵀ i j (allFin _)) k
    ≡⟨ cong (lookup (transposeᵀ i j (allFin _))) k≡j ⟩
  lookup (transposeᵀ i j (allFin _)) j
    ≡⟨ lookup-transposeʳ i j (allFin _) ⟩
  lookup (allFin _) i
    ≡⟨ Vecₚ.lookup-allFin _ ⟩
  i
  ∎
transpose-lemmaᵐⁱⁿ : (i j k : Fin n) → k ≢ i → k ≢ j → transpose i j k ≡ k
transpose-lemmaᵐⁱⁿ i j k k≢i k≢j = begin
  lookup (transposeᵀ i j (allFin _)) k
    ≡⟨ transpose-minimal _ _ _ (allFin _) (inj₂ (k≢i , k≢j)) ⟩
  lookup (allFin _) k
    ≡⟨ Vecₚ.lookup-allFin _ ⟩
  k
  ∎

