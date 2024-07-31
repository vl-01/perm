{-# OPTIONS --safe #-}

module PermutationTable.Permutation.Properties where

open import Level using (Level)

open import Function using (_∘_)

open import Data.Nat.Base using (ℕ)
open import Data.Vec using (Vec; []; _∷_; map; lookup)
open import Data.Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)

open import Relation.Unary using (Pred)

open import Data.Vec.Relation.Unary.Any using (Any; here; there; index; toSum)
open import Data.Vec.Relation.Unary.Any.Properties using (lookup-index; ¬Any[])
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)

open import Data.Vec.Membership.Propositional using (_∈_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; ≢-sym)
open import Relation.Nullary using (contradiction)
open import Relation.Binary using (Rel)

open import PermutationTable.Base
open import PermutationTable.Permutation.Base
open import PermutationTable.Properties

open import Utils.Data.Vec.Relation.Unary

module _ where
  open import Data.Nat using (suc)
  open import Relation.Nullary using (contradiction)
  open import Data.Sum using (inj₁; inj₂)

private
  variable
    A : Set
    n m : ℕ
    ℓ : Level

module _ where
  private module _ where
    lemma : {π : Vec (Fin n) m}
          → {P : Pred A ℓ} → {xs : Vec A n} → {∃x : Any P xs}
          → index ∃x ∈ π → Any P (map (lookup xs) π)
    lemma {π = _ ∷ _} {P = P} {xs = xs} {∃x = ∃x} iₓ∈i∷π with toSum iₓ∈i∷π
    ... | inj₁ iₓ∈i = here (subst (P ∘ lookup xs) iₓ∈i (lookup-index ∃x))
    ... | inj₂ iₓ∈π = there (lemma iₓ∈π)
    lemma {π = []} iₓ∈[] = contradiction iₓ∈[] ¬Any[]

  permute-any : (σ : PermutationTable n)
              → {P : Pred A ℓ} → {xs : Vec A n}
              → Any P xs → Any P (permute σ xs)
  permute-any (π , !π) ∃x = lemma (all-Fin-∈ !π (index ∃x))


module _ where
  open import Relation.Unary using (Pred)
  open import Data.Vec.Relation.Unary.All hiding (map; lookup)
  open import Data.Vec using (map) renaming ([] to []ⱽ)
  open import Data.Vec.Relation.Unary.All.Properties using (lookup⁺)

  private module _ where
    lemma : (π : Vec (Fin n) m)
          → {P : Pred A ℓ} → {xs : Vec A n}
          → (∀x : All P xs)
          → All P (map (lookup xs) π)
    lemma []ⱽ ∀x = []
    lemma (i ∷ π) ∀x = lookup⁺ ∀x i ∷ lemma π ∀x

  permute-all : (σ : PermutationTable n)
              → {P : Pred A ℓ} → {xs : Vec A n}
              → All P xs → All P (permute σ xs)
  permute-all (π , _) = lemma π

module _ where
  open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
  open import Data.Vec.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
  open import Relation.Binary.PropositionalEquality using (_≢_)

  private module _ where

    lemma : {R : Rel A ℓ} 
          → (sym : ∀ {x y : A} → R x y → R y x)
          → {π : Vec (Fin n) m}
          → (!π : Unique π)
          → {xs : Vec A n}
          → (∀x : AllPairs R xs)
          → AllPairs R (map (lookup xs) π)
    lemma sym [] ∀xy = []
    lemma {n = n} {R = R} sym (!i ∷ !js) {xs = xs} ∀xy = go !i ∷ lemma sym !js ∀xy
      where
      go : {i : Fin n} → {js : Vec (Fin n) m} → All (i ≢_) js → All (R (lookup xs i)) (map (lookup xs) js)
      go [] = []
      go (i≠j ∷ i≠js) = lookup-rel-sym sym i≠j ∀xy ∷ go i≠js

  permute-allpairs : {R : Rel A ℓ}
                   → (sym : ∀ {x y : A} → R x y → R y x)
                   → (σ : PermutationTable n) → {xs : Vec A n}
                   → AllPairs R xs → AllPairs R (permute σ xs)
  permute-allpairs sym σ@(_ , !π) = lemma sym !π


permute-unique : (σ : PermutationTable n) → {xs : Vec A n} → Unique xs → Unique (permute σ xs)
permute-unique = permute-allpairs ≢-sym

permute-membership : (σ : PermutationTable n) → {x : A} → {xs : Vec A n} → x ∈ xs → x ∈ permute σ xs
permute-membership σ = permute-any σ
