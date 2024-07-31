{-# OPTIONS --safe #-}

module Partition where

open import Level using (Level)
open import Function using (_∘_; flip)

open import Data.Product using (_,_)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; inside; outside)
open import Data.Vec using (Vec; []; _∷_; map; lookup; _++_; here)
open import Data.Bool using (Bool; true; false)

open import Relation.Nullary using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)

open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique; []; _∷_)
open import Data.Vec.Relation.Unary.AllPairs.Properties using (++⁺)

open import Data.Nat.Properties using (+-comm)

open import Data.Fin.Properties using (0≢1+n; suc-injective)

open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (map⁺)
open import Data.Vec.Relation.Unary.All.Properties using (lookup⁻)

open import PermutationTable.Base using (PermutationTable)
open import Utils.Data.Vec.Relation.Unary using (cast-unique)
open import Utils.Data.Vec.Subset.Properties using (disjoint-all-distinct; 0∉·+1; 0∉𝐅∷p; ∀i∈p⇒∀i+1∈b∷p; ∀i∉p⇒∀i+1∉b∷p)

private
  variable
    A : Set
    n m k : ℕ
    ℓ : Level

private module _ where

open import Level using (0ℓ)
open import Relation.Unary using (Pred; Decidable; ∁)
open import Relation.Nullary using (yes; no)

scatter : Vec A n → Vec (Fin n) m → Vec A m
scatter xs = map (lookup xs)

record Partition (P : Pred A 0ℓ) (xs : Vec A n) : Set where
  field
    [P] : Subset n
    ∣𝐓∣ : ℕ
    ∣𝐅∣ : ℕ
    [𝐓‼] : Vec (Fin n) ∣𝐓∣
    [𝐅‼] : Vec (Fin n) ∣𝐅∣
    [!𝐓‼] : Unique [𝐓‼]
    [!𝐅‼] : Unique [𝐅‼]
    [𝐓‼]-𝐓 : All (_∈ [P]) [𝐓‼]
    [𝐅‼]-𝐅 : All (_∉ [P]) [𝐅‼]
    ∣𝐓∣+∣𝐅∣≡n : ∣𝐓∣ + ∣𝐅∣ ≡ n
    --
    ∀x∈p : All   P   (scatter xs [𝐓‼])
    ∀x∉p : All (∁ P) (scatter xs [𝐅‼])

open Partition

∀xᵢ∈p⇒∷xᵢ₊₁∈p : {P : Pred A 0ℓ} {x : A} {xs : Vec A n} {ixs : Vec (Fin n) m}
   → All P (map (lookup xs) ixs) → All P (map (lookup (x ∷ xs)) (map suc ixs))
∀xᵢ∈p⇒∷xᵢ₊₁∈p {ixs = []} [] = []
∀xᵢ∈p⇒∷xᵢ₊₁∈p {ixs = _ ∷ _} (x∈p ∷ ∀x∈p) = x∈p ∷ ∀xᵢ∈p⇒∷xᵢ₊₁∈p ∀x∈p

partition : {P : Pred A 0ℓ} → Decidable P → (xs : Vec A n) → Partition P xs
partition p? [] = record {
    [P] = []
  ; ∣𝐓∣ = 0     ; ∣𝐅∣ = 0
  ; [𝐓‼] = []   ; [𝐅‼] = []
  ; [!𝐓‼] = []  ; [!𝐅‼] = []
  ; [𝐓‼]-𝐓 = [] ; [𝐅‼]-𝐅 = []
  ; ∣𝐓∣+∣𝐅∣≡n = refl
  --
  ; ∀x∈p = [] ; ∀x∉p = []
  }
partition p? (x ∷ xs) with partition p? xs
... | record {
    [P] = [P]
  ; ∣𝐓∣ = ∣𝐓∣       ; ∣𝐅∣ = ∣𝐅∣
  ; [𝐓‼] = [𝐓‼]     ; [𝐅‼] = [𝐅‼]
  ; [!𝐓‼] = [!𝐓‼]   ; [!𝐅‼] = [!𝐅‼]
  ; [𝐓‼]-𝐓 = [𝐓‼]-𝐓 ; [𝐅‼]-𝐅 = [𝐅‼]-𝐅
  ; ∣𝐓∣+∣𝐅∣≡n = ∣𝐓∣+∣𝐅∣≡n
  --
  ; ∀x∈p = ∀x∈p ; ∀x∉p = ∀x∉p
  } with p? x
... | yes px = record {
    [P] = inside ∷ [P]
  ; ∣𝐓∣ = suc ∣𝐓∣
  ; ∣𝐅∣ = ∣𝐅∣
  ; ∣𝐓∣+∣𝐅∣≡n = cong suc ∣𝐓∣+∣𝐅∣≡n
  ; [𝐓‼] = zero ∷ map suc [𝐓‼]
  ; [𝐅‼] = map suc [𝐅‼]
  ; [!𝐓‼] = lookup⁻ (0∉·+1 [𝐓‼]) ∷ map⁺ suc-injective [!𝐓‼]
  ; [!𝐅‼] = map⁺ suc-injective [!𝐅‼]
  ; [𝐓‼]-𝐓 = here ∷ ∀i∈p⇒∀i+1∈b∷p [𝐓‼]-𝐓
  ; [𝐅‼]-𝐅 = ∀i∉p⇒∀i+1∉b∷p [𝐅‼]-𝐅
  --
  ; ∀x∈p = px ∷ ∀xᵢ∈p⇒∷xᵢ₊₁∈p ∀x∈p
  ; ∀x∉p = ∀xᵢ∈p⇒∷xᵢ₊₁∈p ∀x∉p
  }
... | no ¬px = record {
    [P] = outside ∷ [P]
  ; ∣𝐓∣ = ∣𝐓∣
  ; ∣𝐅∣ = suc ∣𝐅∣
  ; ∣𝐓∣+∣𝐅∣≡n = trans (+-comm _ (suc _)) (cong suc (trans (+-comm _ ∣𝐓∣) ∣𝐓∣+∣𝐅∣≡n))
  ; [𝐓‼] = map suc [𝐓‼]
  ; [𝐅‼] = zero ∷ map suc [𝐅‼]
  ; [!𝐓‼] = map⁺ suc-injective [!𝐓‼]
  ; [!𝐅‼] = lookup⁻ (0∉·+1 [𝐅‼]) ∷ map⁺ suc-injective [!𝐅‼]
  ; [𝐓‼]-𝐓 = ∀i∈p⇒∀i+1∈b∷p [𝐓‼]-𝐓
  ; [𝐅‼]-𝐅 = 0∉𝐅∷p ∷ ∀i∉p⇒∀i+1∉b∷p [𝐅‼]-𝐅
  --
  ; ∀x∈p = ∀xᵢ∈p⇒∷xᵢ₊₁∈p ∀x∈p
  ; ∀x∉p = ¬px ∷ ∀xᵢ∈p⇒∷xᵢ₊₁∈p ∀x∉p
  }
  
partition-permutation : {P : Pred A 0ℓ} → {xs : Vec A n} → (π : Partition P xs) → PermutationTable n
partition-permutation record {
    [P] = [P]
  ; [𝐓‼] = [𝐓‼]     ; [𝐅‼] = [𝐅‼]
  ; [!𝐓‼] = [!𝐓‼]   ; [!𝐅‼] = [!𝐅‼]
  ; [𝐓‼]-𝐓 = [𝐓‼]-𝐓 ; [𝐅‼]-𝐅 = [𝐅‼]-𝐅
  ; ∣𝐓∣+∣𝐅∣≡n = ∣𝐓∣+∣𝐅∣≡n
  } = Data.Vec.cast ∣𝐓∣+∣𝐅∣≡n ([𝐓‼] ++ [𝐅‼]) 
      , cast-unique ∣𝐓∣+∣𝐅∣≡n 
                    (++⁺ [!𝐓‼] [!𝐅‼] 
                         (disjoint-all-distinct [P]
                             [𝐓‼]-𝐓 [𝐅‼]-𝐅
                         ))

open import PermutationTable.Permutation.Base
open import PermutationTable.Permutation.Inverse
open import Data.Vec.Relation.Binary.Equality.Cast using (_≈[_]_; module CastReasoning)
open import Data.Vec.Properties using (map-cast; map-++)

partition-permutes : {P : Pred A 0ℓ} {xs : Vec A n}
    → (part : Partition P xs)
    → let π = partition-permutation part
          eq = ∣𝐓∣+∣𝐅∣≡n part 
      in scatter xs ([𝐓‼] part) ++ scatter xs ([𝐅‼] part) ≈[ eq ] permute π xs
partition-permutes {A} {n} {P} {xs} record {
    [P] = [P]
  ; ∣𝐓∣ = ∣𝐓∣       ; ∣𝐅∣ = ∣𝐅∣
  ; [𝐓‼] = [𝐓‼]     ; [𝐅‼] = [𝐅‼]
  ; [!𝐓‼] = [!𝐓‼]   ; [!𝐅‼] = [!𝐅‼]
  ; [𝐓‼]-𝐓 = [𝐓‼]-𝐓 ; [𝐅‼]-𝐅 = [𝐅‼]-𝐅
  ; ∣𝐓∣+∣𝐅∣≡n = ∣𝐓∣+∣𝐅∣≡n 
  --
  ; ∀x∈p = ∀x∈p ; ∀x∉p = ∀x∉p
  } = begin
    map (lookup xs) [𝐓‼] ++ map (lookup xs) [𝐅‼]
      ≂⟨ sym (map-++ (lookup xs) [𝐓‼] [𝐅‼]) ⟩
    map (lookup xs) ([𝐓‼] ++ [𝐅‼])
      ≈⟨ refl ⟩
    Data.Vec.cast _ (map (lookup xs) ([𝐓‼] ++ [𝐅‼]))
      ≂⟨ sym (map-cast _ ∣𝐓∣+∣𝐅∣≡n _) ⟩
    map (lookup xs) (Data.Vec.cast ∣𝐓∣+∣𝐅∣≡n ([𝐓‼] ++ [𝐅‼]))
    ∎
  where
  open CastReasoning
