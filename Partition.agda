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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)

open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique; []; _∷_)
open import Data.Vec.Relation.Unary.AllPairs.Properties using (++⁺)

open import Data.Nat.Properties using (+-comm)

open import Data.Fin.Properties using (0≢1+n; suc-injective)

open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (map⁺)
open import Data.Vec.Relation.Unary.All.Properties using (lookup⁻)

open import PermutationTable using (PermutationTable)
open import Utils.Data.Vec.Relation.Unary using (cast-unique)
open import Utils.Data.Vec.Subset.Properties using (disjoint-all-distinct; 0∉·+1; 0∉𝐅∷p; ∀i∈p⇒∀i+1∈b∷p; ∀i∉p⇒∀i+1∉b∷p)

private
  variable
    A : Set
    n m : ℕ
    ℓ : Level

private module _ where

open import Level using (0ℓ)
open import Relation.Unary using (Pred; Decidable; ∁)
open import Relation.Nullary using (yes; no)

scatter : Vec A n → Vec (Fin n) m → Vec A m
scatter xs = map (lookup xs)

open import Function using (_⇔_; mk⇔)

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

open import Data.Fin.Properties using (¬Fin0)
open import Data.Vec.Relation.Unary.All.Properties using (map⁻)

partition : {P : Pred A 0ℓ} → Decidable P → (xs : Vec A n) → Partition P xs
partition {P = P} p? [] = record {
    [P] = []
  ; ∣𝐓∣ = 0     ; ∣𝐅∣ = 0
  ; [𝐓‼] = []   ; [𝐅‼] = []
  ; [!𝐓‼] = []  ; [!𝐅‼] = []
  ; [𝐓‼]-𝐓 = [] ; [𝐅‼]-𝐅 = []
  ; ∣𝐓∣+∣𝐅∣≡n = refl
  --
  ; ∀x∈p = [] ; ∀x∉p = []
  }
partition {A = A} {n = suc n} {P = P}  p? (x ∷ xs) with partition p? xs
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

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _,_; _×_)

private
  variable
    B C : Set

dec-sum : {P : Pred A 0ℓ}
  → (p? : Decidable P)
  → (f : Σ A P → B) → (g : Σ A (∁ P) → C)
  → (xs : Vec A n)
  → Vec (B ⊎ C) n
dec-sum p? f g = map h
  where
  h : _ → _ ⊎ _
  h x with p? x
  ... | yes px = inj₁ (f (x , px))
  ... | no ¬px = inj₂ (g (x , ¬px))

open import Data.Vec using (tabulate)
open import Utils.Data.Vec.Relation.Unary using (lookup-dep)

dec-partition : {P : Pred A 0ℓ} {B : Set} {C : Set}
  → (p? : Decidable P)
  → (f : Σ A P → B) → (g : Σ A (∁ P) → C)
  → (xs : Vec A n)
  → ∃ λ (part : Partition P xs) → Vec B (∣𝐓∣ part) × Vec C (∣𝐅∣ part)
dec-partition p? f g xs with partition p? xs
... | part@record {
      ∣𝐓∣ = ∣𝐓∣       ; ∣𝐅∣ = ∣𝐅∣       
    ; [𝐓‼] = [𝐓‼]     ; [𝐅‼] = [𝐅‼]
    ; [𝐓‼]-𝐓 = [𝐓‼]-𝐓 ; [𝐅‼]-𝐅 = [𝐅‼]-𝐅
    ; ∀x∈p = ∀x∈p     ; ∀x∉p = ∀x∉p
    } = part 
      , tabulate (f ∘ lookup-dep ∀x∈p) 
      , tabulate (g ∘ lookup-dep ∀x∉p)

open import Data.Product using (∃₂; <_,_>; -,_)
open import Data.Sum using ([_,_]; fromDec) renaming (map to ⊎-map)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Vec.Relation.Unary.Any using (index)
open import PermutationTable.Permutation.Inverse using (permute-inverseʳ)
open import PermutationTable.Permutation.Properties using (permute-map)
open import Data.Vec.Properties using (map-cast; map-cong; map-∘; tabulate-∘; tabulate∘lookup; tabulate-cong)
open import Utils.Data.Vec.Properties
open import Relation.Binary.PropositionalEquality using (cong₂)
open import Utils.Data.Vec.Relation.Unary using (lookup-dep)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Binary.PropositionalEquality using (_≗_)


open import Relation.Nullary using (toWitness)

open import Data.Vec.Relation.Unary.All.Properties using (lookup⁺)
open import Relation.Unary using (Irrelevant)
open import Relation.Unary.Properties using (∁-irrelevant)

-- TODO lots of repetition in these *-elims, how to extract the common pattern?
yes-elim-lemma1 : {P : Pred A ℓ} {irr : Irrelevant P} → (p? : Decidable P)
            → (f : Σ A P → B) → (g : Σ A (∁ P) → B) → (x : A) → (px : P x)
            → ([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p?) x ≡ f (x , px)
yes-elim-lemma1 {irr = irr} p? f g x px with p? x
... | yes px′ = begin
            f (x , invert (Relation.Nullary.ofʸ px′))
              ≡⟨⟩
            f (x , px′)
              ≡⟨ cong (f ∘ (x ,_)) (irr px′ px) ⟩
            f (x , px)
            ∎
... | no ¬px = contradiction px ¬px

no-elim-lemma1 : {P : Pred A ℓ} → (p? : Decidable P)
            → (f : Σ A P → B) → (g : Σ A (∁ P) → B) → (x : A) → (¬px : (∁ P) x)
            → ([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p?) x ≡ g (x , ¬px)
no-elim-lemma1 {P = P} p? f g x ¬px with p? x
... | yes px = contradiction px ¬px
... | no ¬px′ = begin
            g (x , invert (Relation.Nullary.ofⁿ ¬px′))
              ≡⟨⟩
            g (x , ¬px′)
              ≡⟨ cong (g ∘ (x ,_)) (∁-irrelevant P ¬px′ ¬px) ⟩
            g (x , ¬px)
            ∎

yes-elim-lemma2 : {P : Pred A ℓ} {irr : Irrelevant P} → (p? : Decidable P)
            → (f : Σ A P → B) → (g : Σ A (∁ P) → B) → {xs : Vec A n} → (∀xs : All P xs)
            → [ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p? ∘ lookup xs ≗ f ∘ lookup-dep ∀xs
yes-elim-lemma2 {P = P} {irr = irr} p? f g {xs} ∀xs i = begin
  ([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p? ∘ lookup xs) i
    ≡⟨ yes-elim-lemma1 {irr = irr} p? f g (lookup xs i) (lookup⁺ ∀xs i) ⟩
  (f ∘ lookup-dep ∀xs) i
  ∎

no-elim-lemma2 : {P : Pred A ℓ} → (p? : Decidable P)
            → (f : Σ A P → B) → (g : Σ A (∁ P) → B) → {xs : Vec A n} → (∅xs : All (∁ P) xs)
            → [ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p? ∘ lookup xs ≗ g ∘ lookup-dep ∅xs
no-elim-lemma2 {P = P} p? f g {xs} ∅xs i = begin
  ([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p? ∘ lookup xs) i
    ≡⟨ no-elim-lemma1 p? f g (lookup xs i) (lookup⁺ ∅xs i) ⟩
  (g ∘ lookup-dep ∅xs) i
  ∎

yes-elim : {P : Pred A ℓ} {irr : Irrelevant P} → (p? : Decidable P) → (f : Σ A P → B) → (g : Σ A (∁ P) → B) → {xs : Vec A n} → (∀xs : All P xs)
    → map ([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p?) xs ≡ tabulate (f ∘ lookup-dep ∀xs)
yes-elim {A = A} {P = P} {irr = irr} p? f g {xs = xs} ∀xs = begin
  map ([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p?) xs
    ≡⟨ sym (cong (map _) (tabulate∘lookup xs)) ⟩
  map ([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p?) (tabulate (lookup xs))
    ≡⟨ sym (tabulate-∘ _ _) ⟩
  tabulate (([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p?) ∘ lookup xs)
    ≡⟨ tabulate-cong (yes-elim-lemma2 {irr = irr} p? f g ∀xs) ⟩
  tabulate (f ∘ lookup-dep ∀xs)
  ∎

no-elim : {P : Pred A ℓ} → (p? : Decidable P) → (f : Σ A P → B) → (g : Σ A (∁ P) → B) → {xs : Vec A n} → (∅xs : All (∁ P) xs)
    → map ([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p?) xs ≡ tabulate (g ∘ lookup-dep ∅xs)
no-elim p? f g {xs} ∅xs = begin
  map ([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p?) _
    ≡⟨ sym (cong (map _) (tabulate∘lookup _)) ⟩
  map ([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p?) (tabulate (lookup xs))
    ≡⟨ sym (tabulate-∘ _ _) ⟩
  tabulate (([ f ∘ -,_ , g ∘ -,_ ] ∘ fromDec ∘ p?) ∘ lookup xs)
    ≡⟨ tabulate-cong (no-elim-lemma2 p? f g ∅xs) ⟩
  tabulate (g ∘ lookup-dep ∅xs)
  ∎

dec-partition′ : {P : Pred A 0ℓ} {irr : Irrelevant P} {B C D : Set}
  → (p? : Decidable P)
  → (f : Σ A P → B) → (g : Σ A (∁ P) → C)
  → (φ : B → D) → (γ : C → D)
  → (xs : Vec A n)
  → ∃ λ (part : Partition P xs) 
    → ∃₂ λ (ys : Vec B (∣𝐓∣ part)) (zs : Vec C (∣𝐅∣ part))
      → let π⁻¹ = (partition-permutation part)⁻¹
            eq = ∣𝐓∣+∣𝐅∣≡n part 
        in map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p?) xs 
           ≡ permute π⁻¹ (Data.Vec.cast eq (map φ ys ++ map γ zs))
dec-partition′ 
  {P = P} {irr = irr}
  p? f g φ γ xs with partition p? xs
... | part@record {
      ∣𝐓∣ = ∣𝐓∣       ; ∣𝐅∣ = ∣𝐅∣
    ; [𝐓‼] = [𝐓‼]     ; [𝐅‼] = [𝐅‼]
    ; [!𝐓‼] = [!𝐓‼]   ; [!𝐅‼] = [!𝐅‼]
    ; [𝐓‼]-𝐓 = [𝐓‼]-𝐓 ; [𝐅‼]-𝐅 = [𝐅‼]-𝐅
    ; ∣𝐓∣+∣𝐅∣≡n = ∣𝐓∣+∣𝐅∣≡n
    ; ∀x∈p = ∀x∈p ; ∀x∉p = ∀x∉p
    } = part 
      , ys
      , zs
      , ( begin
          map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p?) xs 
            ≡⟨ sym (permute-inverseʳ σ _) ⟩
          permute σ⁻¹ (permute σ (map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p?) xs))
            ≡⟨ cong (permute σ⁻¹) lemma ⟩
          permute σ⁻¹ (Data.Vec.cast ∣𝐓∣+∣𝐅∣≡n (map φ ys ++ map γ zs))
          ∎ )
      where
      σ = partition-permutation part
      σ⁻¹ = (σ)⁻¹
      ys = tabulate (f ∘ lookup-dep ∀x∈p) 
      zs = tabulate (g ∘ lookup-dep ∀x∉p)
      lemma2 : map (lookup (map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p?) xs)) ([𝐓‼] ++ [𝐅‼]) ≡ map φ (tabulate (λ x → f (lookup-dep ∀x∈p x))) ++ map γ zs
      lemma2 = begin
            map (lookup (map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p?) xs)) ([𝐓‼] ++ [𝐅‼])
              ≡⟨ map-cong (lookup-map-≗ _ xs) _ ⟩
            map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p? ∘ lookup xs) ([𝐓‼] ++ [𝐅‼])
              ≡⟨ map-++ _ [𝐓‼] [𝐅‼] ⟩
            map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p? ∘ lookup xs) [𝐓‼] ++ map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p? ∘ lookup xs) [𝐅‼]
              ≡⟨ cong₂ (_++_) (map-∘ _ (lookup xs) ([𝐓‼]))  (map-∘ _ (lookup xs) ([𝐅‼])) ⟩
            map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p?) (scatter xs [𝐓‼]) ++ map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p?) (scatter xs [𝐅‼])
              ≡⟨ cong₂ (_++_) (yes-elim {irr = irr} p? (φ ∘ f) (γ ∘ g) ∀x∈p) (no-elim p? (φ ∘ f) (γ ∘ g) ∀x∉p) ⟩
            tabulate (φ ∘ f ∘ lookup-dep ∀x∈p) ++ tabulate (γ ∘ g ∘ lookup-dep ∀x∉p)
              ≡⟨ cong₂ (_++_) (tabulate-∘ φ (f ∘ lookup-dep ∀x∈p)) (tabulate-∘ γ _) ⟩
            map φ (tabulate (f ∘ lookup-dep ∀x∈p)) ++ map γ (tabulate (g ∘ lookup-dep ∀x∉p))
            ∎
      lemma : permute σ (map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p?) xs) ≡ Data.Vec.cast ∣𝐓∣+∣𝐅∣≡n (map φ ys ++ map γ zs)
      lemma = begin
            map (lookup (map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p?) xs)) (Data.Vec.cast _ ([𝐓‼] ++ [𝐅‼]))
              ≡⟨ map-cast _ _ _ ⟩
            Data.Vec.cast _ (map (lookup (map ([ φ ∘ f ∘ -,_ , γ ∘ g ∘ -,_ ] ∘ fromDec ∘ p?) xs)) ([𝐓‼] ++ [𝐅‼]))
              ≡⟨ cong (Data.Vec.cast _) lemma2 ⟩
            Data.Vec.cast _ (map φ ys ++ map γ zs)
            ∎
