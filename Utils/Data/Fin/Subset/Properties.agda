{-# OPTIONS --safe #-}

module Utils.Data.Fin.Subset.Properties where

open import Level using (Level)
open import Data.Nat using (ℕ; _≤_; suc)
open import Data.Bool using (Bool)
open import Data.Fin using (Fin; suc)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; ∣_∣; _-_)
open import Relation.Nullary.Negation using (contradiction; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; _≢_)
open import Data.Vec using (Vec; []; _∷_)

open import Data.Fin.Subset.Properties

import Data.Nat.Properties as ℕₚ

private
  variable
    A : Set
    n m : ℕ
    ℓ : Level

x∈p⇒∣p∣≢0 : {x : Fin n} → {p : Subset n} → x ∈ p → ¬ ∣ p ∣ ≡ 0
x∈p⇒∣p∣≢0 {n = n} {x = x} {p = p} x∈p ∣p∣≡0 = contradiction 1+∣p∣≡0 ℕₚ.1+n≢0
  where
  1+∣p∣≡0 = ℕₚ.n≤0⇒n≡0 (subst (suc ∣ p - x ∣ ≤_) ∣p∣≡0 (x∈p⇒∣p-x∣<∣p∣ x∈p))

x∈p⇒∣p∣>0 : {x : Fin n} → {p : Subset n} → x ∈ p → ¬ ∣ p ∣ ≤ 0
x∈p⇒∣p∣>0 {n = n} {x = x} {p = p} x∈p ∣p∣≤0 = x∈p⇒∣p∣≢0 x∈p (ℕₚ.n≤0⇒n≡0 ∣p∣≤0)

open import Relation.Unary using (Pred; ∁)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)

p≢∁p : {P : Pred A ℓ} {x y : A} → P x → (∁ P) y → x ≢ y
p≢∁p px ¬py x≡y = contradiction (subst _ x≡y px) ¬py

p≢∀∁p : {P : Pred A ℓ} {x : A} {ys : Vec A m}
   → P x → All (∁ P) ys
   → All (x ≢_) ys
p≢∀∁p px [] = []
p≢∀∁p px (¬py ∷ ¬pys) = p≢∁p px ¬py ∷ p≢∀∁p px ¬pys

∀p≢∀∁p : {P : Pred A ℓ} {xs : Vec A n} {ys : Vec A m}
  → All P xs → All (∁ P) ys
  → All (λ x → All (x ≢_) ys) xs
∀p≢∀∁p [] _ = []
∀p≢∀∁p (_ ∷ pxs) [] = [] ∷ ∀p≢∀∁p pxs []
∀p≢∀∁p {P = P} (px ∷ pxs) ¬pys@(_ ∷ _) = p≢∀∁p px ¬pys ∷ ∀p≢∀∁p pxs ¬pys

i∈p⇒i+1∈b∷p : ∀ {i : Fin n} {b : Bool} {p : Subset n}
            → i ∈ p → suc i ∈ b ∷ p
i∈p⇒i+1∈b∷p Data.Vec.here = Data.Vec.there Data.Vec.here
i∈p⇒i+1∈b∷p (Data.Vec.there i∈p) = Data.Vec.there (i∈p⇒i+1∈b∷p i∈p)

i∉p⇒i+1∉b∷p : ∀ {i : Fin n} {b : Bool} {p : Subset n}
            → i ∉ p → suc i ∉ b ∷ p
i∉p⇒i+1∉b∷p i∉p (Data.Vec.there i∈p) = contradiction i∈p i∉p
