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
    n m k : ℕ
    ℓ : Level

PermutationTable′ : ℕ → ℕ  → Set
PermutationTable′ n m = ∃ (λ (xs : Vec (Fin n) m) → Unique xs)

PermutationTable : ℕ → Set
PermutationTable n = PermutationTable′ n n

table : ∀ {n} → PermutationTable n → Vec (Fin n) n
table {n} (xs , _) = xs

id : (n : ℕ) → PermutationTable n
id n = allFin n , allFin-Unique

empty : PermutationTable 0
empty = [] , []
  where
  open import Data.Vec using ([])
  open import Data.Vec.Relation.Unary.Unique.Propositional using ([])

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
  open import Relation.Binary.PropositionalEquality using (refl; module ≡-Reasoning; cong; _≗_)
  open ≡-Reasoning
  open import Data.Vec.Properties using (tabulate-∘; tabulate∘lookup; tabulate-cong; lookup-map; map-cong; map-∘; map-lookup-allFin; lookup∘tabulate)
  open import Data.Vec.Relation.Unary.Any.Properties using (lookup-index)

  
  permute-inverse-id : ∀ {n} (σ : PermutationTable n) → (xs : Vec A n) → permute (σ ⁻¹) (table σ) ≡ allFin n
  permute-inverse-id σ@(π , !π) xs = begin
    map (lookup π) (tabulate (index ∘ all-Fin-∈ !π))
      ≡⟨ sym (tabulate-∘ _ _) ⟩
    tabulate (lookup π ∘ index ∘ all-Fin-∈ !π)
      ≡⟨ tabulate-cong (sym ∘ lookup-index ∘ all-Fin-∈ !π) ⟩
    tabulate Function.id
    ∎

  permute-inverse-map : ((π , !π) : PermutationTable n) → (f : Fin n → A)
      → lookup (map f π) ∘ index ∘ all-Fin-∈ !π ≗ f
  permute-inverse-map (π , !π) f i = begin
    lookup (map f π) ((index ∘ all-Fin-∈ !π) i)
      ≡⟨ lookup-map _ f π ⟩
    f (lookup π (index (all-Fin-∈ !π i)))
      ≡⟨ cong f (sym (lookup-index (all-Fin-∈ !π i))) ⟩
    f i
    ∎

  permute-inverseʳ : ∀ {n} (σ : PermutationTable n) → (xs : Vec A n) → permute (σ ⁻¹) (permute σ xs) ≡ xs
  permute-inverseʳ σ@(π , !π) xs = begin
    permute (σ ⁻¹) (permute σ xs)
      ≡⟨⟩
    map (lookup (map (lookup xs) π)) (tabulate (index ∘ all-Fin-∈ !π))
      ≡⟨ sym (tabulate-∘ _ _) ⟩
    tabulate (lookup (map (lookup xs) π) ∘ index ∘ all-Fin-∈ !π)
      ≡⟨ tabulate-cong (permute-inverse-map σ (lookup xs)) ⟩
    tabulate (lookup xs)
      ≡⟨ tabulate∘lookup xs ⟩
    xs
    ∎

  open import Data.Fin using (_≟_)
  open import Relation.Nullary using (yes; no; contradiction)
  open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (lookup-injective)

  index-lookup : ((π , !π) : PermutationTable n) → index ∘ all-Fin-∈ !π ∘ lookup π ≗ Function.id
  index-lookup (π , !π) i = lookup-injective !π _ _ (sym (lookup-index (all-Fin-∈ !π (lookup π i))))

  map-index : ((π , !π) : PermutationTable n) → map (index ∘ all-Fin-∈ !π) π ≡ allFin n
  map-index σ@(π , !π) = begin
    map (index ∘ all-Fin-∈ !π) π
      ≡⟨ cong (map (index ∘ all-Fin-∈ !π)) (sym (tabulate∘lookup _)) ⟩
    map (index ∘ all-Fin-∈ !π) (tabulate (lookup π))
      ≡⟨ sym (tabulate-∘ _ _) ⟩
    tabulate (index ∘ all-Fin-∈ !π ∘ lookup π)
      ≡⟨ tabulate-cong (index-lookup σ) ⟩
    tabulate Function.id
    ∎
      
  permute-inverseˡ : ∀ {n} (σ : PermutationTable n) → (xs : Vec A n) → permute σ (permute (σ ⁻¹) xs) ≡ xs
  permute-inverseˡ σ@(π , !π) xs = begin
    map (lookup (permute (σ ⁻¹) xs)) π
      ≡⟨⟩
    map (lookup (map (lookup xs) (table (σ ⁻¹)))) π
      ≡⟨⟩
    map (lookup (map (lookup xs) (tabulate (index ∘ all-Fin-∈ !π)))) π
      ≡⟨ map-cong (λ i → lookup-map i (lookup xs) (tabulate (index ∘ all-Fin-∈ !π))) π ⟩
    map (lookup xs ∘ lookup (tabulate (index ∘ all-Fin-∈ !π))) π
      ≡⟨ map-cong (cong (lookup xs) ∘ (lookup∘tabulate (index ∘ all-Fin-∈ !π))) π ⟩
    map (lookup xs ∘ index ∘ all-Fin-∈ !π) π
      ≡⟨ map-∘ _ _ _ ⟩
    map (lookup xs) (map (index ∘ all-Fin-∈ !π) π)
      ≡⟨ cong (map (lookup xs)) (map-index σ) ⟩
    map (lookup xs) (allFin _)
      ≡⟨ map-lookup-allFin _ ⟩
    xs
    ∎

  open import Function.Bundles using (_↔_; mk↔ₛ′)
  open import Function.Construct.Composition using (_↔-∘_)
  permutation : ∀ {n} (σ : PermutationTable n) → Vec A n ↔ Vec A n
  permutation σ = mk↔ₛ′ (permute σ) (permute (σ ⁻¹)) (permute-inverseˡ σ) (permute-inverseʳ σ)

  _∘ₚ_ : PermutationTable n → PermutationTable n → PermutationTable n
  σ ∘ₚ (π , !π) = (permute σ π , permute-unique σ !π)

  ∘ₚ-composes : ∀ {n} (σ τ : PermutationTable n) → Function.Inverse.to (permutation {A = A} (σ ∘ₚ τ)) ≗ Function.Inverse.to (permutation σ ↔-∘ permutation τ)
  ∘ₚ-composes {n = n} σ@(π , !π) τ@(ρ , !ρ) xs = begin
    map (lookup xs) (map (lookup ρ) π)
      ≡⟨ sym (map-∘ _ _ _) ⟩
    map (lookup xs ∘ lookup ρ) π
      ≡⟨ map-cong (λ i → sym (lookup-map i (lookup xs) ρ)) π ⟩
    map (lookup (permute τ xs)) π
    ∎

  module _ where
    private variable B : Set


  module _ where
    open import Data.Nat using (_+_; suc; zero)
    open import Data.Nat.Properties using (+-comm)
    open import Data.Fin using (_↑ˡ_; _↑ʳ_; suc; toℕ; fromℕ; _<_; _≥_; _≤_)
    open import Data.Vec using (_++_)
    open import Relation.Binary.PropositionalEquality using (subst; trans)
    open import Data.Product using (_×_)

    open import Data.Fin.Properties using (↑ˡ-injective; ↑ʳ-injective)
    open import Relation.Nullary.Negation.Core using (¬_)

    infix 4 _≮_

    _≮_ : (Fin n) → (Fin m) → Set
    x ≮ y = ¬ x < y

    open import Data.Fin using (fromℕ<)
    open import Data.Fin.Properties using (toℕ-fromℕ; fromℕ-toℕ; toℕ-↑ˡ; toℕ-↑ʳ; toℕ<n; fromℕ<-toℕ; toℕ-cancel-<; toℕ-mono-<)
    open import Data.Nat using (s≤s⁻¹)
    import Data.Nat as ℕ
    open import Relation.Binary.PropositionalEquality using (subst₂)
    open import Data.Nat.Properties using (m≤n+m; m≤m+n; ≤⇒≯)

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

    open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (map⁺)
    open import Data.Vec.Relation.Unary.All using (All)

    module _ where
      infixr 5 _∷ᴬ_
      pattern _∷ᴬ_ x xs = All._∷_ x xs
      pattern []ᴬ = All.[]

    open import Data.Vec.Relation.Unary.AllPairs.Properties using (++⁺)

    open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

    open import Relation.Unary using (Pred; ∁)

    p≢∁p : {P : Pred A ℓ} {x y : A} → P x → (∁ P) y → x ≢ y
    p≢∁p px ¬py x≡y = contradiction (subst _ x≡y px) ¬py

    p≢∀∁p : {P : Pred A ℓ} {x : A} {ys : Vec A m}
       → P x → All (∁ P) ys
       → All (x ≢_) ys
    p≢∀∁p px []ᴬ = []ᴬ
    p≢∀∁p px (¬py ∷ᴬ ¬pys) = p≢∁p px ¬py ∷ᴬ p≢∀∁p px ¬pys

    ∀p≢∀∁p : {P : Pred A ℓ} {xs : Vec A n} {ys : Vec A m}
      → All P xs → All (∁ P) ys
      → All (λ x → All (x ≢_) ys) xs
    ∀p≢∀∁p []ᴬ _ = []ᴬ
    ∀p≢∀∁p (_ ∷ᴬ pxs) []ᴬ = []ᴬ ∷ᴬ ∀p≢∀∁p pxs []ᴬ
    ∀p≢∀∁p {P = P} (px ∷ᴬ pxs) ¬pys@(_ ∷ᴬ _) = p≢∀∁p px ¬pys ∷ᴬ ∀p≢∀∁p pxs ¬pys

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
        go : {k : ℕ} → (xs : Vec (Fin n) k) → All (_< fromℕ n) (map (_↑ˡ m) xs)
        go [] = []ᴬ
        go (x ∷ xs) = ↑ˡ-< x ∷ᴬ go xs
      ∀↑ρ≮n : All (_≮ fromℕ n) (map (n ↑ʳ_) ρ)
      ∀↑ρ≮n = go ρ
        where
        go : {k : ℕ} → (xs : Vec (Fin m) k) → All (_≮ fromℕ n) (map (n ↑ʳ_) xs)
        go [] = []ᴬ
        go (x ∷ xs) = ↑ʳ-≮ x ∷ᴬ go xs

  open import Data.Bool using (Bool; true; false)
  open import Data.Vec using (foldr; _∷ʳ_; countᵇ; _++_) renaming ([] to []ⱽ)
  open import Data.Nat using (suc; _+_; _≤_)
  open import Data.Product using (_×_)
  open import Data.Fin using (zero; suc; inject₁; inject≤; cast) renaming (_+_ to _+ᶠ_)

  open import Data.Vec.Relation.Binary.Equality.Cast using (_≈[_]_)

  length′ : Vec A n → Fin (suc n)
  length′ {n = n} = const (fromℕ n)
    where
    open import Function using (const)
    open import Data.Fin using (fromℕ)

  module _ where
    open import Data.Vec using (insertAt)
    open import Relation.Binary using (Rel)
    open import Relation.Unary using (Pred)
    open import Data.Vec.Relation.Unary.All using (All)
    open import Data.Vec.Relation.Unary.AllPairs using (AllPairs) renaming ([] to []ᴾ; _∷_ to _∷ᴾ_)
    open import Relation.Binary.PropositionalEquality using (_≢_; ≢-sym)
    import Data.Vec.Relation.Unary.All as All using (map)

    module _ where
      open import Data.Nat using (_∸_)

      n∸0≡n : n ∸ 0 ≡ n
      n∸0≡n = refl

    insertAt-all : ∀ {P : Pred A ℓ}
                 → {x : A} → {xs : Vec A n}
                 → All P xs → (i : Fin (suc n)) → P x
                 → All P (insertAt xs i x)
    insertAt-all ∀x zero px = px ∷ᴬ ∀x
    insertAt-all (py ∷ᴬ ∀x) (suc i) px = py ∷ᴬ insertAt-all ∀x i px

    insertAt-allPairs-symm : ∀ {R : Rel A ℓ}
                           → (sym : ∀ {x y : A} → R x y → R y x)
                           → {x : A} → {xs : Vec A n}
                           → AllPairs R xs → (i : Fin (suc n)) → All (R x) xs
                           → AllPairs R (insertAt xs i x)
    insertAt-allPairs-symm sym ∀xy zero ∀x = ∀x ∷ᴾ ∀xy
    insertAt-allPairs-symm sym (x𝑅y ∷ᴾ ∀xy) (suc i) (px ∷ᴬ ∀x) = insertAt-all x𝑅y i (sym px) ∷ᴾ insertAt-allPairs-symm sym ∀xy i ∀x

    insertAt-unique : {x : A} → {xs : Vec A n}
                    → Unique xs → (i : Fin (suc n)) → All (x ≢_) xs
                    → Unique (insertAt xs i x)
    insertAt-unique !xs i !x = insertAt-allPairs-symm ≢-sym !xs i !x

    insertAppend : (i : Fin (suc n)) → (σ : PermutationTable n) → PermutationTable (suc n)
    insertAppend {n = n} i σ@(π , !π) = insertAt (map inject₁ π) i (opposite zero) , insertAt-unique (map⁺ inject₁-injective !π) i (n≢∀ π)
      where
      open import Data.Fin using (opposite)
      open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (map⁺)
      open import Data.Fin.Properties using (inject₁-injective; fromℕ≢inject₁)
      n≢∀ : {k : ℕ} → (xs : Vec (Fin n) k) → All (opposite zero ≢_) (map inject₁ xs)
      n≢∀ []ⱽ = []ᴬ
      n≢∀ (x ∷ xs) = fromℕ≢inject₁ ∷ᴬ n≢∀ xs

    open import Data.Product using (∃₂)

    -- Goal: suc n ≡ suc (Data.Fin.toℕ i) + (n ∸ Data.Fin.toℕ i)
    open import Data.Nat using (_∸_)
    n≡m+n-m : {n m : ℕ} → m ≤ n → n ≡ m + (n ∸ m)
    n≡m+n-m {n = n} {m = m} m≤n = begin
      n
        ≡⟨ sym (+-identityʳ _) ⟩
      n + 0
        ≡⟨ cong (n +_) (sym (n∸n≡0 m)) ⟩ 
      n + (m ∸ m)
        ≡⟨ sym (+-∸-assoc n {o = m} ≤-refl) ⟩ 
      (n + m) ∸ m
        ≡⟨ cong (_∸ m) (+-comm n m) ⟩ 
      (m + n) ∸ m
        ≡⟨ +-∸-assoc m m≤n ⟩ 
      m + (n ∸ m)
      ∎
      where
      open import Data.Nat.Properties using (+-comm; +-∸-assoc; ≤-refl; n∸n≡0; +-identityʳ)


  open import Data.Fin.Subset using (Subset; _∈_; _∉_; inside; outside)
  open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ⱽ_; _∉_ to _∉ⱽ_)
  open import Data.Vec.Relation.Unary.All using (All)

  pf : ∀ {i : Fin n} {b : Bool} {p : Subset n}
      → i ∈ p → suc i ∈ b ∷ p
  pf Data.Vec.here = Data.Vec.there Data.Vec.here
  pf (Data.Vec.there i∈p) = Data.Vec.there (pf i∈p)

  pf2 : ∀ {i : Fin n} {b : Bool} {p : Subset n}
      → i ∉ p → suc i ∉ b ∷ p
  pf2 i∉p (Data.Vec.there i∈p) = contradiction i∈p i∉p

  go1 : {b : Bool} → {p : Subset m} → {xs : Vec (Fin m) k} → All (_∈ p) xs → All (_∈ b ∷ p) (map suc xs)
  go1 []ᴬ = []ᴬ
  go1 (px ∷ᴬ pxs) = Data.Vec.there px ∷ᴬ go1 pxs

  go2 : {b : Bool} → {p : Subset m} → {xs : Vec (Fin m) k} → All (_∉ p) xs → All (_∉ b ∷ p) (map suc xs)
  go2 []ᴬ = []ᴬ
  go2 (px ∷ᴬ pxs) = pf2 px ∷ᴬ go2 pxs

  go0 : {p : Subset m} → zero ∉ outside ∷ p
  go0 = flip contradiction (λ ()) ∘ []=⇒lookup
    where
    open import Data.Vec.Properties using ([]=⇒lookup)
    open import Function using (flip)

  module _ where
    open import Relation.Binary.PropositionalEquality using (_≢_)

    0∉·+1 : (xs : Vec (Fin n) m) → (i : Fin m) → zero ≢ lookup (map suc xs) i
    0∉·+1 xs i 0≡sucᵢ = contradiction (trans 0≡sucᵢ (lookup-map i suc xs)) 0≢1+n
      where
      open import Data.Vec.Properties using (lookup-map)
      open import Relation.Binary.PropositionalEquality using (trans)
      open import Data.Fin.Properties using (0≢1+n)

  record Partition (n : ℕ) : Set where
    field
      [∈] : Subset n
      ∣𝐓∣ : ℕ
      ∣𝐅∣ : ℕ
      ∣𝐓∣+∣𝐅∣≡n : ∣𝐓∣ + ∣𝐅∣ ≡ n
      [𝐓‼] : Vec (Fin n) ∣𝐓∣
      [𝐅‼] : Vec (Fin n) ∣𝐅∣
      [!𝐓‼] : Unique [𝐓‼]
      [!𝐅‼] : Unique [𝐅‼]
      [𝐓‼]-𝐓 : All (_∈ [∈]) [𝐓‼]
      [𝐅‼]-𝐅 : All (_∉ [∈]) [𝐅‼]

  partition : (mask : Vec Bool n) → Partition n
  partition []ⱽ = record {
      [∈] = []
    ; ∣𝐓∣ = 0
    ; ∣𝐅∣ = 0
    ; ∣𝐓∣+∣𝐅∣≡n = refl
    ; [𝐓‼] = []
    ; [𝐅‼] = []
    ; [!𝐓‼] = []ᵁ
    ; [!𝐅‼] = []ᵁ
    ; [𝐓‼]-𝐓 = []ᴬ
    ; [𝐅‼]-𝐅 = []ᴬ
    }
  partition (true ∷ mask) with partition mask
  ... | π = record {
      [∈] = inside ∷ [∈] π
    ; ∣𝐓∣ = suc (∣𝐓∣ π)
    ; ∣𝐅∣ = ∣𝐅∣ π
    ; ∣𝐓∣+∣𝐅∣≡n = cong suc (∣𝐓∣+∣𝐅∣≡n π)
    ; [𝐓‼] = zero ∷ map suc ([𝐓‼] π)
    ; [𝐅‼] = map suc ([𝐅‼] π)
    ; [!𝐓‼] = lookup⁻ (0∉·+1 ([𝐓‼] π)) ∷ᵁ map⁺ suc-injective ([!𝐓‼] π)
    ; [!𝐅‼] = map⁺ suc-injective ([!𝐅‼] π)
    ; [𝐓‼]-𝐓 = Data.Vec.here ∷ᴬ go1 ([𝐓‼]-𝐓 π) 
    ; [𝐅‼]-𝐅 = go2 ([𝐅‼]-𝐅 π)
    }
    where 
    open Partition
    open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (map⁺)
    open import Data.Vec.Relation.Unary.All.Properties using (lookup⁻)
    open import Data.Fin.Properties using (suc-injective)
  partition (false ∷ mask) with partition mask
  ... | π = record {
      [∈] = outside ∷ [∈] π
    ; ∣𝐓∣ = ∣𝐓∣ π
    ; ∣𝐅∣ = suc (∣𝐅∣ π)
    ; ∣𝐓∣+∣𝐅∣≡n = trans (+-comm _ (suc _)) (cong suc (trans (+-comm _ (∣𝐓∣ π)) (∣𝐓∣+∣𝐅∣≡n π)))
    ; [𝐓‼] = map suc ([𝐓‼] π)
    ; [𝐅‼] = zero ∷ map suc ([𝐅‼] π)
    ; [!𝐓‼] = map⁺ suc-injective ([!𝐓‼] π)
    ; [!𝐅‼] = lookup⁻ (0∉·+1 ([𝐅‼] π)) ∷ᵁ map⁺ suc-injective ([!𝐅‼] π)
    ; [𝐓‼]-𝐓 = go1 ([𝐓‼]-𝐓 π)
    ; [𝐅‼]-𝐅 = go0 ∷ᴬ go2 ([𝐅‼]-𝐅 π)
    }
    where 
    open Partition
    open import Data.Vec.Relation.Unary.Unique.Propositional.Properties using (map⁺)
    open import Data.Vec.Relation.Unary.All.Properties using (lookup⁻)
    open import Data.Fin.Properties using (suc-injective)
    open import Relation.Binary.PropositionalEquality using (trans)
    open import Data.Nat.Properties using (+-comm)

  module _ where
    open import Relation.Binary.PropositionalEquality using (_≢_)

    disjoint-all-distinct : {xs : Vec (Fin n) m} {ys : Vec (Fin n) k}
          → (p : Subset n) → All (_∈ p) xs → All (_∉ p) ys
          → All (λ x → All (x ≢_) ys) xs
    disjoint-all-distinct _ []ᴬ _ = []ᴬ
    disjoint-all-distinct p (_ ∷ᴬ ∀x∈p) []ᴬ = []ᴬ ∷ᴬ disjoint-all-distinct p ∀x∈p []ᴬ
    disjoint-all-distinct {n = n} {m = m} {k = k} {xs = x ∷ xs} {ys = y ∷ ys} p (x∈p ∷ᴬ ∀x∈p) (y∉p ∷ᴬ ∀y∉p) = (p≢∁p x∈p y∉p ∷ᴬ ∉p⇒≢x ∀y∉p) ∷ᴬ disjoint-all-distinct p ∀x∈p (y∉p ∷ᴬ ∀y∉p)
      where
      open import Relation.Binary.PropositionalEquality using (subst)
      ∉p⇒≢x : {j : ℕ} {zs : Vec (Fin n) j} → All (_∉ p) zs → All (x ≢_) zs
      ∉p⇒≢x []ᴬ = []ᴬ
      ∉p⇒≢x {zs = z ∷ zs} (z∉p ∷ᴬ ∀z∉p) = p≢∁p x∈p z∉p ∷ᴬ ∉p⇒≢x ∀z∉p
    
cast-unique : {xs : Vec A n} → (eq : n ≡ m) → Unique xs → Unique (Data.Vec.cast eq xs)
cast-unique _≡_.refl []ᵁ = []ᵁ
cast-unique _≡_.refl (!x ∷ᵁ !xs) = subst (All (_ ≢_)) (sym (cast-is-id _≡_.refl _)) !x ∷ᵁ cast-unique _≡_.refl !xs
  where
  open import Relation.Binary.PropositionalEquality using (subst; _≢_)
  open import Data.Vec.Properties using (cast-is-id)
  open import Data.Vec.Relation.Unary.All using (All)

partition-permutation : (π : Partition n) → PermutationTable n
partition-permutation record {
    [∈] = [∈]
  ; ∣𝐓∣ = ∣𝐓∣
  ; ∣𝐅∣ = ∣𝐅∣
  ; ∣𝐓∣+∣𝐅∣≡n = ∣𝐓∣+∣𝐅∣≡n
  ; [𝐓‼] = [𝐓‼]
  ; [𝐅‼] = [𝐅‼]
  ; [!𝐓‼] = [!𝐓‼]
  ; [!𝐅‼] = [!𝐅‼]
  ; [𝐓‼]-𝐓 = [𝐓‼]-𝐓
  ; [𝐅‼]-𝐅 = [𝐅‼]-𝐅
  } = Data.Vec.cast ∣𝐓∣+∣𝐅∣≡n ([𝐓‼] ++ [𝐅‼]) 
      , cast-unique ∣𝐓∣+∣𝐅∣≡n (++⁺ [!𝐓‼] [!𝐅‼] (disjoint-all-distinct [∈] [𝐓‼]-𝐓 [𝐅‼]-𝐅))
  where
  open import Data.Vec using (_++_)
  open import Data.Vec.Relation.Unary.AllPairs.Properties using (++⁺)
