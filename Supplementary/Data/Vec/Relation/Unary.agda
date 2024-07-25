{-# OPTIONS --safe #-}

module Supplementary.Data.Vec.Relation.Unary where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; _[_]≔_; _∷_)
open import Data.Fin using (Fin; suc; zero)
open import Relation.Unary using (Pred)
open import Data.Vec.Relation.Unary.Any
open import Data.Vec.Relation.Unary.All
open import Level using (Level)

private
  variable
    A : Set
    n : ℕ
    ℓ : Level

[]≔-any : {P : Pred A ℓ} {x : A} {xs : Vec A n} {i : Fin n}
        → P x → Any P (xs [ i ]≔ x)
[]≔-any {xs = x ∷ xs} {i = zero } px = here px
[]≔-any {xs = x ∷ xs} {i = suc i} px = there ([]≔-any {i = i} px)


[]≔-all : {P : Pred A ℓ} {y : A} {xs : Vec A n} {i : Fin n}
        → All P xs → P y → All P (xs [ i ]≔ y)
[]≔-all {i = zero } (px ∷ pxs) py = py ∷ pxs
[]≔-all {i = suc i} (px ∷ pxs) py = px ∷ []≔-all {i = i} pxs py
