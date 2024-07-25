{-# OPTIONS --safe #-}

module PermutationTable.Properties.Unique where
  open import Function.Base using (id)
  open import Relation.Binary.PropositionalEquality using ( _≢_; refl)
  open import Relation.Nullary.Decidable using (¬?)
  import Relation.Binary.Definitions as B
  import Relation.Unary as U
  open import Data.Nat using (ℕ)
  open import Data.Fin using (_≟_)
  open import Data.Vec using (Vec; allFin)
  open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
  open import Data.Vec.Relation.Unary.AllPairs using (irrelevant)
  import Data.Vec.Relation.Unary.Unique.Propositional.Properties as Uniqueₚ

  private
    variable
      A : Set
      n : ℕ

  distinct-irrelevant : B.Irrelevant {_} {A} _≢_
  distinct-irrelevant x≢y x≢y = refl

  unique-irrelevant : U.Irrelevant {_} {Vec A n} Unique
  unique-irrelevant = irrelevant distinct-irrelevant

  unique? : U.Decidable (Unique {n = n})
  unique? {n = n} = Data.Vec.Relation.Unary.AllPairs.allPairs? (λ x y → ¬? (_≟_ {n} x y))

  allFin-Unique : {n : ℕ} → Unique (allFin n)
  allFin-Unique = Uniqueₚ.tabulate⁺ id
