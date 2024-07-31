{-# OPTIONS --safe #-}

module Utils.Data.Fin.Permutation.Components.Properties where

open import Data.Fin.Permutation.Components
open import Data.Fin using (Fin; _≟_)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (yes; no)

private
  variable
    n : ℕ

transpose-i-j-i : ∀ (i j : Fin n) → transpose i j i ≡ j
transpose-i-j-i i j with i ≟ i
... | yes _  = refl
... | no i≢i = contradiction refl i≢i

transpose-i-j-j : ∀ {n} (i j : Fin n) → transpose i j j ≡ i
transpose-i-j-j i j with j ≟ i
... | yes j≡i = j≡i
... | no j≢i with j ≟ j
... | yes j≡j = refl
... | no j≢j = contradiction refl j≢j

transpose-i-j-k : ∀ (i j k : Fin n) → k ≢ i → k ≢ j → transpose i j k ≡ k
transpose-i-j-k i j k k≢i k≢j with k ≟ i
... | yes k≡i = contradiction k≡i k≢i
... | no k≢i with k ≟ j
... | yes k≡j = contradiction k≡j k≢j
... | no k≢j = refl
