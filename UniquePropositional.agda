{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecSetoid)
import Data.Vec.Relation.Unary.AllPairs as AllPairs
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Decidable using (¬?)

module UniquePropositional {a ℓ} (DS : DecSetoid a ℓ) where

open DecSetoid DS renaming (setoid to S)

------------------------------------------------------------------------
-- Re-export setoid definition

open import UniqueSetoid S public

------------------------------------------------------------------------
-- Additional properties

unique? : ∀ {n} → Relation.Unary.Decidable (Unique {n})
unique? = AllPairs.allPairs? (λ x y → ¬? (x ≟ y))
