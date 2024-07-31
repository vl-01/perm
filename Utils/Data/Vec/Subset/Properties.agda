{-# OPTIONS --safe #-}

module Utils.Data.Vec.Subset.Properties where

open import Function using (_∘_; flip)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; map; lookup; there)
open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; inside; outside)

open import Data.Vec.Relation.Unary.All using (All; []; _∷_)

open import Relation.Nullary using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; trans)

open import Data.Fin.Properties using (0≢1+n)
open import Data.Vec.Properties using ([]=⇒lookup; lookup-map)

open import Utils.Data.Fin.Subset.Properties using (p≢∁p; i∉p⇒i+1∉b∷p)

private
  variable
    n m k : ℕ

disjoint-all-distinct : {xs : Vec (Fin n) m} {ys : Vec (Fin n) k}
      → (p : Subset n) → All (_∈ p) xs → All (_∉ p) ys
      → All (λ x → All (x ≢_) ys) xs
disjoint-all-distinct _ [] _ = []
disjoint-all-distinct p (_ ∷ ∀x∈p) [] = [] ∷ disjoint-all-distinct p ∀x∈p []
disjoint-all-distinct {n = n} {m = m} {k = k} {xs = x ∷ xs} {ys = y ∷ ys} p (x∈p ∷ ∀x∈p) (y∉p ∷ ∀y∉p) = (p≢∁p x∈p y∉p ∷ ∉p⇒≢x ∀y∉p) ∷ disjoint-all-distinct p ∀x∈p (y∉p ∷ ∀y∉p)
  where
  ∉p⇒≢x : {j : ℕ} {zs : Vec (Fin n) j} → All (_∉ p) zs → All (x ≢_) zs
  ∉p⇒≢x [] = []
  ∉p⇒≢x {zs = z ∷ zs} (z∉p ∷ ∀z∉p) = p≢∁p x∈p z∉p ∷ ∉p⇒≢x ∀z∉p

∀i∈p⇒∀i+1∈b∷p : {b : Bool} → {p : Subset m} → {xs : Vec (Fin m) k}
            → All (_∈ p) xs → All (_∈ b ∷ p) (map suc xs)
∀i∈p⇒∀i+1∈b∷p [] = []
∀i∈p⇒∀i+1∈b∷p (px ∷ pxs) = there px ∷ ∀i∈p⇒∀i+1∈b∷p pxs

∀i∉p⇒∀i+1∉b∷p : {b : Bool} → {p : Subset m} → {xs : Vec (Fin m) k}
    → All (_∉ p) xs → All (_∉ b ∷ p) (map suc xs)
∀i∉p⇒∀i+1∉b∷p [] = []
∀i∉p⇒∀i+1∉b∷p (px ∷ pxs) = i∉p⇒i+1∉b∷p px ∷ ∀i∉p⇒∀i+1∉b∷p pxs

0∉𝐅∷p : {p : Subset m} → zero ∉ outside ∷ p
0∉𝐅∷p = flip contradiction (λ ()) ∘ []=⇒lookup

0∉·+1 : (xs : Vec (Fin n) m) → (i : Fin m) → zero ≢ lookup (map suc xs) i
0∉·+1 xs i 0≡sucᵢ = contradiction (trans 0≡sucᵢ (lookup-map i suc xs)) 0≢1+n

