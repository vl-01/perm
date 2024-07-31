{-# OPTIONS --safe #-}

module Utils.Data.Vec.Relation.Unary where

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; _[_]≔_; _∷_; lookup)
open import Data.Fin using (Fin; suc; zero)
open import Relation.Unary using (Pred)
open import Data.Vec.Relation.Unary.Any using (Any; here; there)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)

private
  variable
    A : Set
    n m : ℕ
    ℓ : Level

[]≔-any : {P : Pred A ℓ} {x : A} {xs : Vec A n} {i : Fin n}
        → P x → Any P (xs [ i ]≔ x)
[]≔-any {xs = x ∷ xs} {i = zero } px = here px
[]≔-any {xs = x ∷ xs} {i = suc i} px = there ([]≔-any {i = i} px)


[]≔-all : {P : Pred A ℓ} {y : A} {xs : Vec A n} {i : Fin n}
        → All P xs → P y → All P (xs [ i ]≔ y)
[]≔-all {i = zero } (px ∷ pxs) py = py ∷ pxs
[]≔-all {i = suc i} (px ∷ pxs) py = px ∷ []≔-all {i = i} pxs py

all-lookup : ∀ {P : Pred A ℓ} → {xs : Vec A n} → All P xs → (i : Fin n) → P (lookup xs i)
all-lookup (px ∷ _) zero = px
all-lookup (_ ∷ pxs) (suc i) = all-lookup pxs i

all-replace : ∀ {P : Pred A ℓ} {xs : Vec A n} {x : A}
          → (i : Fin n)
          → P x → All P xs
          → All P (xs [ i ]≔ x)
all-replace zero Px (_ ∷ Pxs) = Px ∷ Pxs
all-replace (suc i) Px (Px₁ ∷ Pxs) = Px₁ ∷ all-replace i Px Pxs

open import Data.Nat using (s<s⁻¹)
open import Data.Fin using (_<_)
open import Data.Fin.Properties using (<-cmp)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (contradiction)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary using (Rel)

lookup-rel : {i j : Fin n}
           → i < j
           → {R : Rel A ℓ} → {xs : Vec A n} → AllPairs R xs
           → R (lookup xs i) (lookup xs j)
lookup-rel {i = suc i-1} {j = suc j-1} i<j (_ ∷ ∀xy) = lookup-rel {i = i-1} {j = j-1} (s<s⁻¹ i<j) ∀xy
lookup-rel {i =  zero}   {j = suc j-1} 0<j {R = R} (x∀y ∷ _) = all-lookup x∀y j-1

lookup-rel-sym : {R : Rel A ℓ}
               → (sym : ∀ {x y : A} → R x y → R y x)
               → {i j : Fin n}
               → i ≢ j
               → {xs : Vec A n} → AllPairs R xs
               → R (lookup xs i) (lookup xs j)
lookup-rel-sym sym {i = i} {j = j} i≠j ∀xy with <-cmp i j
... | tri< i<j _ _ = lookup-rel i<j ∀xy
... | tri≈ _ i=j _ = contradiction i=j i≠j
... | tri> _ _ i>j = sym (lookup-rel i>j ∀xy)

open import Relation.Binary.PropositionalEquality using (sym; subst; _≡_; _≢_)
open import Data.Vec.Properties using (cast-is-id)

cast-unique : {xs : Vec A n} → (eq : n ≡ m) → Unique xs → Unique (Data.Vec.cast eq xs)
cast-unique _≡_.refl [] = []
cast-unique _≡_.refl (!x ∷ !xs) = subst (All (_ ≢_)) (sym (cast-is-id _≡_.refl _)) !x ∷ cast-unique _≡_.refl !xs
