{-# OPTIONS --safe #-}

module PermutationTable.Base where

open import Level using (Level)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (∃; _,_)
open import Data.Vec using (Vec; allFin)
open import Data.Fin using (Fin)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
open import PermutationTable.Properties.Unique

private
  variable
    n m : ℕ
    ℓ : Level

PermutationTable′ : ℕ → ℕ  → Set
PermutationTable′ n m = ∃ (λ (xs : Vec (Fin n) m) → Unique xs)

PermutationTable : ℕ → Set
PermutationTable n = PermutationTable′ n n

table : ∀ {n} → PermutationTable n → Vec (Fin n) n
table {n} (xs , _) = xs

id : (n : ℕ) → PermutationTable n
id n = allFin n , allFin-Unique

open Data.Product using (dmap)
open import PermutationTable.Components.Properties
open import PermutationTable.Components renaming (transpose to transpose′)
open Data.Product using (dmap)

transpose : ∀ (i j : Fin n) → PermutationTable n → PermutationTable n
transpose i j = dmap (transpose′ i j) (transpose-unique i j)

open import Function.Bundles using (_↔_; mk↔ₛ′)
open Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product.Properties using (Σ-≡,≡→≡)

transpose↔ : ∀ (i j : Fin n) → PermutationTable n ↔ PermutationTable n
transpose↔ i j = mk↔ₛ′ swp swp inv inv
  where
  swp = transpose i j
  inv : (xs : PermutationTable _) → swp (swp xs) ≡ xs
  inv (xs , _) = Σ-≡,≡→≡ (transpose-involutive i j xs , unique-irrelevant _ _)

private
  variable
    A : Set

open import Function using (_∘_)
open import Data.Vec using (_∷_; []; map; lookup; tabulate)
open import Data.Vec.Relation.Unary.Unique.Propositional renaming (_∷_ to _∷ᵁ_; [] to []ᵁ; head to headᵁ; tail to tailᵁ)

open import PermutationTable.Properties
open import Data.Vec.Relation.Unary.Any using (index)
open import Relation.Binary.PropositionalEquality using (sym)

open import Data.Product using (proj₁; proj₂)

module _ where
  open import Relation.Nullary using (contraposition)
  open import Relation.Binary.PropositionalEquality using (_≢_)
  open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (tabulate⁺)

  private module _ where
    open import Data.Vec.Relation.Unary.Any using (index; here; there)
    open import Relation.Binary.PropositionalEquality using (trans; sym)
    open import Data.Fin.Properties using (suc-injective)
    open import Data.Vec.Membership.Propositional using (_∈_)

    lemma : {i j : Fin n} → {xs : Vec (Fin n) m}
          → (∃i : i ∈ xs) → (∃j : j ∈ xs) → index ∃i ≡ index ∃j → i ≡ j
    lemma (here i=x) (here j=x) _ = trans i=x (sym j=x)
    lemma (there ∃i) (there ∃j) x = lemma ∃i ∃j (suc-injective x)


  _⁻¹ : PermutationTable n → PermutationTable n
  (σ , !σ)⁻¹ = (σ⁻¹ , !σ⁻¹)
    where
    σ⁻¹ : Vec (Fin _) _
    σ⁻¹ = tabulate (index ∘ all-Fin-∈ !σ)
    !σ⁻¹ : Unique σ⁻¹
    !σ⁻¹ = tabulate⁺ (lemma (all-Fin-∈ !σ _) (all-Fin-∈ !σ _))

permute : PermutationTable n → Vec A n → Vec A n
permute σ xs = map (lookup xs) (table σ)

permute′ : PermutationTable n → Vec A n → Vec A n
permute′ σ xs = tabulate (lookup xs ∘ lookup (table σ))

module _ where
  open import Relation.Binary.PropositionalEquality using (refl)

  permute-empty : (σ : PermutationTable 0) → (xs : Vec A 0) → permute σ xs ≡ xs
  permute-empty ([] , _) [] = refl

module _ where
  open import Relation.Unary using (Pred)
  open import Data.Vec.Relation.Unary.Any hiding (lookup; map)
  open import Relation.Binary.PropositionalEquality using (subst)
  open import Data.Vec using (map)
  open import Data.Nat using (suc)
  open import Relation.Nullary using (contradiction)
  open import Data.Vec.Membership.Propositional using (_∈_)
  open import Data.Sum using (inj₁; inj₂)
  open import PermutationTable.Properties using (all-Fin-∈)
  open import Data.Vec.Relation.Unary.Any.Properties using (lookup-index; ¬Any[])

          
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
  open import Data.Vec.Membership.Propositional using (_∈_)

  permute-membership : (σ : PermutationTable n) → {x : A} → {xs : Vec A n} → x ∈ xs → x ∈ permute σ xs
  permute-membership σ = permute-any σ

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
  open import Relation.Binary.Core using (Rel)
  open import Data.Vec.Relation.Unary.AllPairs hiding (map)
  open import Data.Vec using (map) renaming ([] to []ⱽ)
  open import Relation.Nullary using (yes; no)
  open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

  private module _ where
    open import Data.Fin using (_<_; _<?_; suc; zero; inject₁)
    open import Data.Fin.Properties using (<-cmp; <⇒≤pred; i<1+i)
    open import Relation.Binary.PropositionalEquality using (_≢_)
    open import Relation.Nullary using (contradiction)
    open import Data.Vec.Relation.Unary.All using (All)

    infixr 5 _∷ᴬ_
    pattern _∷ᴬ_ x xs = All._∷_ x xs
    pattern []ᴬ = All.[]

    lookupᴬ : ∀ {R : Rel A ℓ} → {x : A} → {xs : Vec A n} → All (R x) xs → (i : Fin n) → R x (lookup xs i)
    lookupᴬ (xᵢ𝑅x ∷ᴬ _) zero = xᵢ𝑅x
    lookupᴬ {R = R} (_ ∷ᴬ x𝑅xs) (suc i) = lookupᴬ {R = R} x𝑅xs i

    ss : {i j : Fin n} → suc i < suc j → i < j
    ss (Data.Nat.Base.s≤s i<j) = i<j

    lookup-rel : {i j : Fin n}
               → i < j
               → {R : Rel A ℓ} → {xs : Vec A n} → AllPairs R xs
               → R (lookup xs i) (lookup xs j)
    lookup-rel {i = suc i-1} {j = suc j-1} i<j (_ ∷ ∀xy) = lookup-rel {i = i-1} {j = j-1} (ss i<j) ∀xy
    lookup-rel {i =  zero}   {j = suc j-1} 0<j {R = R} (x∀y ∷ _) = lookupᴬ {R = R} x∀y j-1

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

  private module _ where
    open import Data.Vec.Relation.Unary.All using (All)
    open import Relation.Binary.PropositionalEquality using (_≢_)

    lemma : {R : Rel A ℓ} 
          → (sym : ∀ {x y : A} → R x y → R y x)
          → {π : Vec (Fin n) m}
          → (!π : Unique π)
          → {xs : Vec A n}
          → (∀x : AllPairs R xs)
          → AllPairs R (map (lookup xs) π)
    lemma sym []ᵁ ∀xy = []
    lemma {n = n} {R = R} sym (!i ∷ !js) {xs = xs} ∀xy = go !i ∷ lemma sym !js ∀xy
      where
      go : {i : Fin n} → {js : Vec (Fin n) m} → All (i ≢_) js → All (R (lookup xs i)) (map (lookup xs) js)
      go []ᴬ = []ᴬ
      go (i≠j ∷ᴬ i≠js) = lookup-rel-sym sym i≠j ∀xy ∷ᴬ go i≠js

  permute-allpairs : {R : Rel A ℓ}
                   → (sym : ∀ {x y : A} → R x y → R y x)
                   → (σ : PermutationTable n) → {xs : Vec A n}
                   → AllPairs R xs → AllPairs R (permute σ xs)
  permute-allpairs sym σ@(_ , !π) = lemma sym !π

module _ where
  open import Relation.Binary.PropositionalEquality using (≢-sym)

  permute-unique : (σ : PermutationTable n) → {xs : Vec A n} → Unique xs → Unique (permute σ xs)
  permute-unique = permute-allpairs ≢-sym

module _ where
  open import Relation.Binary.PropositionalEquality using (refl; module ≡-Reasoning)
  open ≡-Reasoning
  open import Data.Vec.Properties using (tabulate-∘)

  pf : ∀ {n} (σ : PermutationTable n) → (xs : Vec A n) → permute (σ ⁻¹) (permute σ xs) ≡ xs
  pf σ@(π , !π) xs = begin
    permute (σ ⁻¹) (permute σ xs)
      ≡⟨⟩
    map (lookup (map (lookup xs) π)) (tabulate (index ∘ all-Fin-∈ !π))
      ≡⟨ sym (tabulate-∘ _ _) ⟩
    tabulate (lookup (map (lookup xs) π) ∘ index ∘ all-Fin-∈ !π)
      ≡⟨ ? ⟩
    xs
    ∎
