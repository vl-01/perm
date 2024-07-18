{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Nullary.Negation using (¬_)

module UniqueSetoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

private
  Distinct : Rel A ℓ
  Distinct x y = ¬ (x ≈ y)

open import Data.Vec.Relation.Unary.AllPairs.Core Distinct public
     renaming (AllPairs to Unique)

open import Data.Vec.Relation.Unary.AllPairs {R = Distinct} public
  using (head; tail)
