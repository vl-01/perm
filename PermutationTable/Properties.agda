{-# OPTIONS --safe #-}

module PermutationTable.Properties where

open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (≢-sym)

open import Data.Product using (_,_)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Fin using (Fin; _≟_)
open import Data.Fin.Subset using (Subset; _∈_; ∣_∣; _-_; ⊤)
open import Data.Vec using (Vec)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Vec.Relation.Unary.All using (All; map; zip)
open import Data.Vec.Relation.Unary.Any using (here; there)

open import PermutationTable.Properties.Unique public

open import Supplementary.Data.Fin.Subset.Properties
open import Data.Fin.Subset.Properties

open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ᵀ_; _∉_ to _∉ᵀ_)

import Data.Nat.Properties as ℕₚ
import Data.Vec.Relation.Unary.All.Properties as Allₚ

private
  variable
    n m : ℕ

private module _ where
  infixr 5 _∷ⱽ_
  pattern _∷ⱽ_ x xs = Data.Vec._∷_ x xs
  pattern []ⱽ = Data.Vec.[]

  infixr 5 _∷ᴬ_
  pattern _∷ᴬ_ x xs = All._∷_ x xs
  pattern []ᴬ = All.[]

  infixr 5 _∷ᵁ_
  pattern _∷ᵁ_ x xs = Unique._∷_ x xs
  pattern []ᵁ = Unique.[]

all-Fin-∈ : ∀ {n} → {xs : Vec (Fin n) n} → Unique xs → ∀ (i : Fin n) → i ∈ᵀ xs
all-Fin-∈ {n = n} {xs = xs} uxs i = h xs uxs ⊤ (Allₚ.lookup⁻ (λ _ → ∈⊤)) ∈⊤ (∣p∣≤n ⊤)
  where
  h : (xs : Vec (Fin n) m) → (uxs : Unique xs)
    → (unseen : Subset n) → (xs-unseen : All (_∈ unseen) xs)
    → (i ∈ unseen) → ∣ unseen ∣ ≤ m 
    → i ∈ᵀ xs
  h []ⱽ []ᵁ  unseen []ᴬ i-unseen ∣unseen∣≤0 = contradiction ∣unseen∣≤0 (x∈p⇒∣p∣>0 i-unseen)
  h {m = suc m-1} (x ∷ⱽ xs) (ux ∷ᵁ uxs) unseen (x-unseen ∷ᴬ xs-unseen) i-unseen ∣unseen∣≤m with i ≟ x
  ... | yes i≡x = here i≡x
  ... | no  i≢x = there (h xs uxs yet-unseen xs-yet-unseen i-yet-unseen ∣yet-unseen∣≤m-1)
    where
    yet-unseen : Subset n
    yet-unseen = unseen - x

    i-yet-unseen : i ∈ yet-unseen
    i-yet-unseen = x∈p∧x≢y⇒x∈p-y i-unseen i≢x

    xs-yet-unseen : All (_∈ yet-unseen) xs
    xs-yet-unseen = map (λ (x≢y , y-unseen) → x∈p∧x≢y⇒x∈p-y y-unseen (≢-sym x≢y)) (zip (ux , xs-unseen))

    ∣yet-unseen∣≤m-1 : ∣ yet-unseen ∣ ≤ m-1
    ∣yet-unseen∣≤m-1 = ℕₚ.≤-pred (ℕₚ.≤-trans (x∈p⇒∣p-x∣<∣p∣ x-unseen) ∣unseen∣≤m)
