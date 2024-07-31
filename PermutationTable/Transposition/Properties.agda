{-# OPTIONS --safe #-}

module PermutationTable.Transposition.Properties where

open import Level using (Level)


open import Function.Base using (_∘_ ; flip; id)

open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Unary using (Pred)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; _[_]≔_; _∷_; lookup)
open import Data.Fin using (Fin; suc; zero; _≟_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Vec.Relation.Unary.Any hiding (lookup)
open import Data.Vec.Relation.Unary.All hiding (lookup)
open import Data.Vec.Relation.Unary.AllPairs
open import Data.Vec.Relation.Unary.Unique.Propositional
open import Data.Vec.Membership.Propositional using (_∈_)

open import Utils.Data.Vec.Relation.Unary
open import PermutationTable.Transposition.Base

import Data.Vec.Properties as Vecₚ
import Data.Vec.Relation.Unary.Any.Properties as Anyₚ
import Data.Vec.Relation.Unary.All.Properties as Allₚ

private
  variable
    A : Set
    n : ℕ
    ℓ : Level

transpose-≡-id : ∀ (i : Fin n) (xs : Vec A n) → transpose i i xs ≡ xs
transpose-≡-id i xs = begin
  xs [ i ]≔ lookup xs i [ i ]≔ lookup xs i
    ≡⟨ Vecₚ.[]≔-idempotent xs i ⟩
  xs [ i ]≔ lookup xs i
    ≡⟨ Vecₚ.[]≔-lookup xs i ⟩
  xs
  ∎

transpose-≡-id′ : ∀ {i j : Fin n} (xs : Vec A n) → i ≡ j → transpose i j xs ≡ xs
transpose-≡-id′ {A} {n} {i} {j} xs i≡j = trans (cong (λ i′ → transpose i′ j xs) i≡j) (transpose-≡-id j xs)
          
transpose-symmetric : ∀ (i j : Fin n) (xs : Vec A n) → transpose i j xs ≡ transpose j i xs
transpose-symmetric i j xs with i ≟ j
... | yes i≡j = trans (transpose-≡-id′ xs i≡j) (sym (transpose-≡-id′ xs (sym i≡j)))
... | no i≢j = Vecₚ.[]≔-commutes xs i j i≢j
  
lookup-transposeˡ : ∀ (i j : Fin n) → (xs : Vec A n) → lookup (transpose i j xs) i ≡ lookup xs j
lookup-transposeˡ i j xs with i ≟ j
... | yes i≡j = begin
        lookup (transpose i j xs) i
          ≡⟨ cong (flip lookup _) (transpose-≡-id′ xs i≡j) ⟩
        lookup xs i
          ≡⟨ cong (lookup xs) i≡j ⟩
        lookup xs j
        ∎
... | no  i≢j = begin
        lookup (xs [ i ]≔ lookup xs j [ j ]≔ lookup xs i) i
          ≡⟨ Vecₚ.lookup∘update′ i≢j (xs [ _ ]≔ _) _ ⟩
        lookup (xs [ i ]≔ lookup xs j) i
          ≡⟨ Vecₚ.lookup∘update _ xs (lookup xs _) ⟩
        lookup xs j
        ∎

lookup-transposeʳ : ∀ (i j : Fin n) → (xs : Vec A n) → lookup (transpose i j xs) j ≡ lookup xs i
lookup-transposeʳ i j xs = begin
  lookup (transpose i j xs) j
    ≡⟨ cong (flip lookup j) (transpose-symmetric i j xs) ⟩ 
  lookup (transpose j i xs) j
    ≡⟨ lookup-transposeˡ j i xs ⟩
  lookup xs i
  ∎

transpose-involutive : ∀ (i j : Fin n) → transpose {A = A} i j ∘ transpose i j ≗ id
transpose-involutive i j xs with i ≟ j
... | yes i≡j = trans (transpose-≡-id′ _ i≡j) (transpose-≡-id′ _ i≡j)
... | no  i≢j = begin
      ys [ i ]≔ lookup ys j [ j ]≔ lookup ys i
        ≡⟨⟩
      xs [ i ]≔ lookup xs j [ j ]≔ lookup xs i [ i ]≔ lookup ys j [ j ]≔ lookup ys i
        ≡⟨ cong ((_[ _ ]≔ lookup ys _) ∘ (_[ _ ]≔ lookup ys _)) (Vecₚ.[]≔-commutes _ _ _ i≢j) ⟩
      xs [ j ]≔ lookup xs i [ i ]≔ lookup xs j [ i ]≔ lookup ys j [ j ]≔ lookup ys i
        ≡⟨ cong (_[ _ ]≔ lookup ys _) (trans (Vecₚ.[]≔-idempotent _ _) (Vecₚ.[]≔-commutes _ _ _ (i≢j ∘ sym))) ⟩
      xs [ i ]≔ lookup ys j [ j ]≔ lookup xs i [ j ]≔ lookup ys i
        ≡⟨ Vecₚ.[]≔-idempotent (_ [ _ ]≔ lookup ys _) _ ⟩
      xs [ i ]≔ lookup ys j [ _ ]≔ lookup ys i
        ≡⟨ cong (_ [ _ ]≔ lookup ys _ [ _ ]≔_) (lookup-transposeˡ _ _ xs) ⟩
      xs [ i ]≔ lookup ys j [ j ]≔ lookup xs j
        ≡⟨ cong ((_[ _ ]≔ lookup xs _) ∘ (_ [ _ ]≔_)) (lookup-transposeʳ _ _ xs) ⟩
      xs [ i ]≔ lookup xs i [ j ]≔ lookup xs j
        ≡⟨ cong (_[ _ ]≔ lookup xs _) (Vecₚ.[]≔-lookup xs _) ⟩
      xs [ j ]≔ lookup xs j
        ≡⟨ Vecₚ.[]≔-lookup xs _ ⟩
      xs
      ∎
      where
      ys = xs [ i ]≔ lookup xs j [ j ]≔ lookup xs i

transpose-minimal : ∀ (i j k : Fin n) → (xs : Vec A n) → ((i ≡ j) ⊎ (k ≢ i) × (k ≢ j)) → lookup (transpose i j xs) k ≡ lookup xs k
transpose-minimal i j k xs (inj₁ i≡j) = cong (flip lookup k) (transpose-≡-id′ xs i≡j)
transpose-minimal i j k xs (inj₂ (k≢i , k≢j)) = begin
  lookup (xs [ i ]≔ lookup xs j [ j ]≔ lookup xs i) k
    ≡⟨ Vecₚ.lookup∘update′ k≢j (xs [ _ ]≔ lookup xs _) (lookup xs _) ⟩
  lookup (xs [ i ]≔ lookup xs j) k
    ≡⟨ Vecₚ.lookup∘update′ k≢i xs (lookup xs _)  ⟩
  lookup xs k
  ∎

private module _ where
  transpose-head-any : ∀ {P : Pred A ℓ} → {x₀ : A} → {xs : Vec A n}
                → (i : Fin n) → Any P xs → Any P (transpose zero (suc i) (x₀ ∷ xs))
  transpose-head-any {P = P} {x₀ = x₀} {xs = xs} i ∃px 
    with index ∃px ≟ i
  ...| yes ?ₓ≡i = here (subst P (cong (lookup xs) ?ₓ≡i) (Anyₚ.lookup-index ∃px))
  ...| no  ?ₓ≢i = there (subst (Any P) (Vecₚ.[]≔-lookup _ _) ([]≔-any px))
                where
                px : P (lookup (xs [ i ]≔ x₀) (index ∃px))
                px = subst P (sym (Vecₚ.lookup∘update′ ?ₓ≢i xs x₀)) (Anyₚ.lookup-index ∃px)

transpose-any : ∀ (i j : Fin n) → {P : Pred A ℓ} → {xs : Vec A n}
         → Any P xs → Any P (transpose i j xs)
transpose-any zero    zero    {P} {x ∷ xs} = subst (Any P) (sym (transpose-≡-id zero (x ∷ xs)))
transpose-any (suc _) (suc _) {xs = _ ∷ _} (here px)   = here px
transpose-any (suc i) (suc j) {xs = _ ∷ _} (there ∃px) = there (transpose-any i j ∃px)
transpose-any zero    (suc j) {xs = _ ∷ _} (there ∃px) = transpose-head-any j ∃px
transpose-any (suc i) zero    {xs = _ ∷ _} (there ∃px) = transpose-head-any i ∃px
transpose-any zero    (suc _) {xs = _ ∷ _} (here px) = there ([]≔-any px)
transpose-any (suc _) zero    {xs = _ ∷ _} (here px) = there ([]≔-any px)

transpose-any← : ∀ (i j : Fin n) → {P : Pred A ℓ} → {xs : Vec A n}
          → Any P (transpose i j xs) → Any P xs
transpose-any← i j px = subst (Any _) (transpose-involutive i j _) (transpose-any i j px)

transpose-all : ∀ (i j : Fin n) → {P : Pred A ℓ} → {xs : Vec A n} → All P xs → All P (transpose i j xs)
transpose-all i j pxs = []≔-all ([]≔-all pxs (Allₚ.lookup⁺ pxs j)) (Allₚ.lookup⁺ pxs i)

open ConstructorDisambiguation

private module _ where
  open import Data.Vec.Relation.Unary.AllPairs using (AllPairs)
  open import Data.Vec.Relation.Unary.All using (All)
  import Data.Vec.Relation.Unary.AllPairs.Properties as AllPairsₚ
  open import Relation.Binary.Core using (Rel)
  open import Level using (Level)
  open import Utils.Data.Vec.Relation.Unary

  transpose-head-allpairs : ∀ {R : Rel A ℓ} → {x₀ : A} → {xs : Vec A n}
                    → (∀ {x y : A} → R x y → R y x)
                    → (i : Fin n) → All (R x₀) xs → AllPairs R xs
                    → All (R (lookup xs i)) (xs [ i ]≔ x₀)
  transpose-head-allpairs sym zero    (x₀𝑅xᵢ ∷ᴬ _) (xᵢ𝑅xs ∷ᴾ _) = sym x₀𝑅xᵢ ∷ᴬ xᵢ𝑅xs
  transpose-head-allpairs sym (suc i) (_ ∷ᴬ x₀𝑅xs) (xⱼ𝑅xs ∷ᴾ xs𝑅xs) 
    = sym (all-lookup xⱼ𝑅xs i) ∷ᴬ transpose-head-allpairs sym i x₀𝑅xs xs𝑅xs

  transpose-head-allpairs… : ∀ {R : Rel A ℓ} → {x₀ : A} → {xs : Vec A n}
                     → (∀ {x y : A} → R x y → R y x)
                     → (i : Fin n) → All (R x₀) xs → AllPairs R xs → AllPairs R (xs [ i ]≔ x₀)
  transpose-head-allpairs… _ zero (_ ∷ᴬ x₀𝑅xs) (_ ∷ᴾ xs𝑅xs) = x₀𝑅xs ∷ᴾ xs𝑅xs
  transpose-head-allpairs… sym (suc i) (x₀𝑅xⱼ ∷ᴬ x₀𝑅xs) (xⱼ𝑅xs ∷ᴾ xs𝑅xs)
    = all-replace i (sym x₀𝑅xⱼ) xⱼ𝑅xs ∷ᴾ transpose-head-allpairs… sym i x₀𝑅xs xs𝑅xs

transpose-allpairs : ∀ (i j : Fin n) → {R : Rel A ℓ} → {xs : Vec A n}
              → (∀ {x y : A} → R x y → R y x)
              → AllPairs R xs → AllPairs R (transpose i j xs)
transpose-allpairs zero zero {R = R} {xs = xs} _ = subst (AllPairs R) (sym (transpose-≡-id zero xs))
transpose-allpairs zero (suc j) sym (x𝑅xs ∷ᴾ xs𝑅xs) 
  = transpose-head-allpairs sym j x𝑅xs xs𝑅xs ∷ᴾ transpose-head-allpairs… sym j x𝑅xs xs𝑅xs
transpose-allpairs (suc i) zero    sym (x𝑅xs ∷ᴾ xs𝑅xs) 
  = transpose-head-allpairs sym i x𝑅xs xs𝑅xs ∷ᴾ transpose-head-allpairs… sym i x𝑅xs xs𝑅xs
transpose-allpairs (suc i) (suc j) sym (x𝑅xs ∷ᴾ xs𝑅xs) 
  = transpose-all i j x𝑅xs ∷ᴾ transpose-allpairs i j sym xs𝑅xs

transpose-membership : ∀ (i j : Fin n) → {x : A} → {xs : Vec A n}
                → (x ∈ xs) → (x ∈ transpose i j xs)
transpose-membership i j {x = x} = transpose-any i j {P = x ≡_}

transpose-unique : ∀ (i j : Fin n) → {xs : Vec (Fin n) n} → Unique xs → Unique (transpose i j xs)
transpose-unique i j = transpose-allpairs i j ≢-sym
