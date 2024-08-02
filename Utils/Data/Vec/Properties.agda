{-# OPTIONS --safe #-}

module Utils.Data.Vec.Properties where

open import Function using (_∘_)
open import Data.Vec using (Vec; lookup; map)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Data.Nat using (ℕ)

private
  variable
    A B : Set
    n : ℕ

lookup-map-≗ : (f : A → B) (xs : Vec A n)
               → lookup (map f xs) ≗ f ∘ lookup xs
lookup-map-≗ f xs i = lookup-map i f xs
