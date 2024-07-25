{-# OPTIONS --safe #-}

module Supplementary.Data.Fin.Subset.Properties where

open import Data.Nat using (ℕ; _≤_; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; ∣_∣; _-_)
open import Relation.Nullary.Negation using (contradiction; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Data.Fin.Subset.Properties

import Data.Nat.Properties as ℕₚ

private
  variable
    n : ℕ

x∈p⇒∣p∣≢0 : {x : Fin n} → {p : Subset n} → x ∈ p → ¬ ∣ p ∣ ≡ 0
x∈p⇒∣p∣≢0 {n = n} {x = x} {p = p} x∈p ∣p∣≡0 = contradiction 1+∣p∣≡0 ℕₚ.1+n≢0
  where
  1+∣p∣≡0 = ℕₚ.n≤0⇒n≡0 (subst (suc ∣ p - x ∣ ≤_) ∣p∣≡0 (x∈p⇒∣p-x∣<∣p∣ x∈p))

x∈p⇒∣p∣>0 : {x : Fin n} → {p : Subset n} → x ∈ p → ¬ ∣ p ∣ ≤ 0
x∈p⇒∣p∣>0 {n = n} {x = x} {p = p} x∈p ∣p∣≤0 = x∈p⇒∣p∣≢0 x∈p (ℕₚ.n≤0⇒n≡0 ∣p∣≤0)
