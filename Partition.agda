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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)

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

record Partition (n : ℕ) : Set where
  field
    [∈] : Subset n
    ∣𝐓∣ : ℕ
    ∣𝐅∣ : ℕ
    ∣𝐓∣+∣𝐅∣≡n : ∣𝐓∣ + ∣𝐅∣ ≡ n
    [𝐓‼] : Vec (Fin n) ∣𝐓∣
    [𝐅‼] : Vec (Fin n) ∣𝐅∣
    [!𝐓‼] : Unique [𝐓‼]
    [!𝐅‼] : Unique [𝐅‼]
    [𝐓‼]-𝐓 : All (_∈ [∈]) [𝐓‼]
    [𝐅‼]-𝐅 : All (_∉ [∈]) [𝐅‼]


open Partition

open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no)

partition : {P : Pred A ℓ} → Decidable P → Vec A n → Partition n
partition p? [] = record {
    [∈] = []
  ; ∣𝐓∣ = 0     ; ∣𝐅∣ = 0
  ; [𝐓‼] = []   ; [𝐅‼] = []
  ; [!𝐓‼] = []  ; [!𝐅‼] = []
  ; [𝐓‼]-𝐓 = [] ; [𝐅‼]-𝐅 = []
  ; ∣𝐓∣+∣𝐅∣≡n = refl
  }
partition p? (x ∷ xs) with partition p? xs
... | record {
    [∈] = [∈]
  ; ∣𝐓∣ = ∣𝐓∣       ; ∣𝐅∣ = ∣𝐅∣
  ; [𝐓‼] = [𝐓‼]     ; [𝐅‼] = [𝐅‼]
  ; [!𝐓‼] = [!𝐓‼]   ; [!𝐅‼] = [!𝐅‼]
  ; [𝐓‼]-𝐓 = [𝐓‼]-𝐓 ; [𝐅‼]-𝐅 = [𝐅‼]-𝐅
  ; ∣𝐓∣+∣𝐅∣≡n = ∣𝐓∣+∣𝐅∣≡n
  } with p? x
... | yes _ = record {
    [∈] = inside ∷ [∈]
  ; ∣𝐓∣ = suc ∣𝐓∣
  ; ∣𝐅∣ = ∣𝐅∣
  ; ∣𝐓∣+∣𝐅∣≡n = cong suc ∣𝐓∣+∣𝐅∣≡n
  ; [𝐓‼] = zero ∷ map suc [𝐓‼]
  ; [𝐅‼] = map suc [𝐅‼]
  ; [!𝐓‼] = lookup⁻ (0∉·+1 [𝐓‼]) ∷ map⁺ suc-injective [!𝐓‼]
  ; [!𝐅‼] = map⁺ suc-injective [!𝐅‼]
  ; [𝐓‼]-𝐓 = here ∷ ∀i∈p⇒∀i+1∈b∷p [𝐓‼]-𝐓
  ; [𝐅‼]-𝐅 = ∀i∉p⇒∀i+1∉b∷p [𝐅‼]-𝐅
  }
... | no _ = record {
    [∈] = outside ∷ [∈]
  ; ∣𝐓∣ = ∣𝐓∣
  ; ∣𝐅∣ = suc ∣𝐅∣
  ; ∣𝐓∣+∣𝐅∣≡n = trans (+-comm _ (suc _)) (cong suc (trans (+-comm _ ∣𝐓∣) ∣𝐓∣+∣𝐅∣≡n))
  ; [𝐓‼] = map suc [𝐓‼]
  ; [𝐅‼] = zero ∷ map suc [𝐅‼]
  ; [!𝐓‼] = map⁺ suc-injective [!𝐓‼]
  ; [!𝐅‼] = lookup⁻ (0∉·+1 [𝐅‼]) ∷ map⁺ suc-injective [!𝐅‼]
  ; [𝐓‼]-𝐓 = ∀i∈p⇒∀i+1∈b∷p [𝐓‼]-𝐓
  ; [𝐅‼]-𝐅 = 0∉𝐅∷p ∷ ∀i∉p⇒∀i+1∉b∷p [𝐅‼]-𝐅
  }
  
partition-permutation : (π : Partition n) → PermutationTable n
partition-permutation record {
    [∈] = [∈]
  ; [𝐓‼] = [𝐓‼]     ; [𝐅‼] = [𝐅‼]
  ; [!𝐓‼] = [!𝐓‼]   ; [!𝐅‼] = [!𝐅‼]
  ; [𝐓‼]-𝐓 = [𝐓‼]-𝐓 ; [𝐅‼]-𝐅 = [𝐅‼]-𝐅
  ; ∣𝐓∣+∣𝐅∣≡n = ∣𝐓∣+∣𝐅∣≡n
  } = Data.Vec.cast ∣𝐓∣+∣𝐅∣≡n ([𝐓‼] ++ [𝐅‼]) 
      , cast-unique ∣𝐓∣+∣𝐅∣≡n 
                    (++⁺ [!𝐓‼] [!𝐅‼] 
                         (disjoint-all-distinct [∈]
                             [𝐓‼]-𝐓 [𝐅‼]-𝐅
                         ))

open import Level using (0ℓ)
open import Relation.Unary using (∁)

record Partitioned {P : Pred A 0ℓ} (p? : Decidable P) {n : ℕ} (xs : Vec A n) : Set where
  field 
    part : Partition n
    xs∈p : Vec A (∣𝐓∣ part)
    xs∉p : Vec A (∣𝐅∣ part)
    ∀x∈p : All P     (map (lookup xs) ([𝐓‼] part))
    ∀x∉p : All (∁ P) (map (lookup xs) ([𝐅‼] part))

open import PermutationTable.Base
open import PermutationTable.Permutation.Base

partitioned : {P : Pred A 0ℓ} (p? : Decidable P) (xs : Vec A n) → Partitioned p? xs
partitioned p? xs with partition p? xs
... | record {
      [∈] = [∈]
    ; [𝐓‼] = [𝐓‼]     ; [𝐅‼] = [𝐅‼]
    ; [!𝐓‼] = [!𝐓‼]   ; [!𝐅‼] = [!𝐅‼]
    ; [𝐓‼]-𝐓 = [𝐓‼]-𝐓 ; [𝐅‼]-𝐅 = [𝐅‼]-𝐅
    ; ∣𝐓∣+∣𝐅∣≡n = ∣𝐓∣+∣𝐅∣≡n
    } = ?

pf : {P : Pred A ℓ} → (p? : Decidable P) → (xs : Vec A n)
   → xs ≡ ?
pf = ?
