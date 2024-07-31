{-# OPTIONS --safe #-}

module PermutationTable.Reshape where

open import Level using (Level)

import Data.Nat as ℕ using (_<_)
open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.Product using (_,_)
open import Data.Fin using (Fin; suc; zero; _↑ˡ_; _↑ʳ_; toℕ; fromℕ; _<_; opposite; inject₁)

open import Data.Vec using (Vec; []; _∷_; map; _++_; insertAt)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec.Relation.Unary.AllPairs using (AllPairs; []; _∷_)

open import Relation.Nullary using (contradiction; ¬_)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; subst; subst₂; ≢-sym)

open import Data.Nat.Properties using (m≤n+m; m≤m+n; ≤⇒≯)
open import Data.Fin.Properties using (↑ˡ-injective; ↑ʳ-injective; fromℕ≢inject₁; inject₁-injective)
open import Data.Vec.Relation.Unary.AllPairs.Properties using (++⁺)
open import Utils.Data.Fin.Subset.Properties using (∀p≢∀∁p)
open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (map⁺)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ<n)

open import PermutationTable.Base

private
  variable
    A : Set
    n m k : ℕ
    ℓ : Level

private module _ where
  infix 4 _≮_

  _≮_ : (Fin n) → (Fin m) → Set
  x ≮ y = ¬ x < y

↑ˡ-< : (i : Fin n) → i ↑ˡ m < fromℕ n
↑ˡ-< {n = n} {m = m} i = subst₂ ℕ._<_ (sym (toℕ-↑ˡ i m)) (sym (toℕ-fromℕ n)) (toℕ<n i)

↑ʳ-≮ : (i : Fin n) → m ↑ʳ i ≮ fromℕ m
↑ʳ-≮ {n = n} {m = m} i m↑ʳi<m′ = contradiction m↑ʳi<m m↑ʳi≮m
  where
  m↑ʳi<m : toℕ (m ↑ʳ i) ℕ.< m
  m↑ʳi<m = subst (toℕ (m ↑ʳ i) ℕ.<_) (toℕ-fromℕ m) m↑ʳi<m′

  m+i=m↑ʳi : m + toℕ i ≡ toℕ (m ↑ʳ i)
  m+i=m↑ʳi = sym (toℕ-↑ʳ m i)

  m≤m+i : m ℕ.≤ m + toℕ i
  m≤m+i = m≤m+n m (toℕ i)

  m≤m↑ʳi : m ℕ.≤ toℕ (m ↑ʳ i)
  m≤m↑ʳi = subst (m ℕ.≤_) m+i=m↑ʳi m≤m+i

  m↑ʳi≮m : toℕ (m ↑ʳ i) ℕ.≮ m
  m↑ʳi≮m = ≤⇒≯ m≤m↑ʳi

_++ₚ_ : PermutationTable n → PermutationTable m → PermutationTable (n + m)
_++ₚ_ {n = n} {m = m} (π , !π) (ρ , !ρ) = (map (_↑ˡ _) π ++ map (_ ↑ʳ_) ρ , ++⁺ !π↑ !↑ρ (∀p≢∀∁p ∀π↑<n ∀↑ρ≮n))
  where
  !π↑ : Unique (map (_↑ˡ m) π)
  !π↑ = map⁺ (↑ˡ-injective _ _ _) !π
  !↑ρ : Unique (map (n ↑ʳ_) ρ)
  !↑ρ = map⁺ (↑ʳ-injective _ _ _) !ρ
  ∀π↑<n : All (_< fromℕ n) (map (_↑ˡ m) π)
  ∀π↑<n = go π
    where
    go : (xs : Vec (Fin n) k) → All (_< fromℕ n) (map (_↑ˡ m) xs)
    go [] = []
    go (x ∷ xs) = ↑ˡ-< x ∷ go xs
  ∀↑ρ≮n : All (_≮ fromℕ n) (map (n ↑ʳ_) ρ)
  ∀↑ρ≮n = go ρ
    where
    go : {k : ℕ} → (xs : Vec (Fin m) k) → All (_≮ fromℕ n) (map (n ↑ʳ_) xs)
    go [] = []
    go (x ∷ xs) = ↑ʳ-≮ x ∷ go xs

insertAt-all : ∀ {P : Pred A ℓ}
             → {x : A} → {xs : Vec A n}
             → All P xs → (i : Fin (suc n)) → P x
             → All P (insertAt xs i x)
insertAt-all ∀x zero px = px ∷ ∀x
insertAt-all (py ∷ ∀x) (suc i) px = py ∷ insertAt-all ∀x i px

insertAt-allPairs-symm : ∀ {R : Rel A ℓ}
                       → (sym : ∀ {x y : A} → R x y → R y x)
                       → {x : A} → {xs : Vec A n}
                       → AllPairs R xs → (i : Fin (suc n)) → All (R x) xs
                       → AllPairs R (insertAt xs i x)
insertAt-allPairs-symm sym ∀xy zero ∀x = ∀x ∷ ∀xy
insertAt-allPairs-symm sym (x𝑅y ∷ ∀xy) (suc i) (px ∷ ∀x) = insertAt-all x𝑅y i (sym px) ∷ insertAt-allPairs-symm sym ∀xy i ∀x

insertAt-unique : {x : A} → {xs : Vec A n}
                → Unique xs → (i : Fin (suc n)) → All (x ≢_) xs
                → Unique (insertAt xs i x)
insertAt-unique !xs i !x = insertAt-allPairs-symm ≢-sym !xs i !x

insertAppend : (i : Fin (suc n)) → (σ : PermutationTable n) → PermutationTable (suc n)
insertAppend {n = n} i σ@(π , !π) = insertAt (map inject₁ π) i (opposite zero) , insertAt-unique (map⁺ inject₁-injective !π) i (n≢∀ π)
  where
  n≢∀ : {k : ℕ} → (xs : Vec (Fin n) k) → All (opposite zero ≢_) (map inject₁ xs)
  n≢∀ [] = []
  n≢∀ (x ∷ xs) = fromℕ≢inject₁ ∷ n≢∀ xs
