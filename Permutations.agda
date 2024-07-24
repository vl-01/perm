{-# OPTIONS --safe -WnoUnsupportedIndexedMatch #-}
  

module Permutations where

open import Function.Base using (_∘_ ; const; flip; id; case_of_)
open import Function.Bundles using (_⇔_; mk⇔)

open import Relation.Nullary.Negation using (contradiction; ¬_)

open import Data.Product using (_,_)

open import Data.Nat using (ℕ; zero; suc)

open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Fin.Patterns
open import Data.Fin.Permutation using (_⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_) renaming (Permutation′ to Permutation)
open import Data.Fin.Permutation.Transposition.List using (TranspositionList; eval)

open import Data.Vec using (Vec; lookup; tabulate; updateAt; _[_]≔_; _++_; allFin)

import Data.List
infixr 5 _∷ᴸ_
pattern _∷ᴸ_ x xs = Data.List._∷_ x xs
pattern []ᴸ = Data.List.[]

infixr 5 _∷ⱽ_
pattern _∷ⱽ_ x xs = Data.Vec._∷_ x xs
pattern []ⱽ = Data.Vec.[]

private
  variable
    A B : Set
    n m : ℕ
    i j k : Fin n

module Example where
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; _≗_)
  open import Data.Vec.Relation.Binary.Equality.Cast using (_≈[_]_)
  open import Data.Bool renaming (true to 𝐓; false to 𝐅)
  open import Data.Vec using (map)

  mask : Vec Bool 7
  mask = 𝐅 ∷ⱽ 𝐅 ∷ⱽ 𝐓 ∷ⱽ 𝐓 ∷ⱽ 𝐅 ∷ⱽ 𝐓 ∷ⱽ 𝐅 ∷ⱽ []ⱽ

  idxsʸ : Vec (Fin 7) 3
  idxsʸ = 2F ∷ⱽ 3F ∷ⱽ 5F ∷ⱽ []ⱽ

  idxsⁿ : Vec (Fin 7) 4
  idxsⁿ = 0F ∷ⱽ 1F ∷ⱽ 4F ∷ⱽ 6F ∷ⱽ []ⱽ

  idxs : Vec (Fin 7) 7
  idxs = idxsʸ ++ idxsⁿ

  σᵗ : TranspositionList 7
  σᵗ = (0F , 3F) ∷ᴸ   -- [2 3 5 0 1 4 6]  [0 1 2 3 4 5 6]
       (1F , 4F) ∷ᴸ   -- [0 3 5 2 1 4 6]  [3 1 2 0 4 5 6]
       (2F , 3F) ∷ᴸ   -- [0 1 5 2 3 4 6]  [3 4 2 0 1 5 6]
       (3F , 4F) ∷ᴸ   -- [0 1 2 5 3 4 6]  [3 4 0 2 1 5 6]
       (4F , 5F) ∷ᴸ   -- [0 1 2 3 5 4 6]  [3 4 0 1 2 5 6]
       (5F , 5F) ∷ᴸ   -- [0 1 2 3 4 5 6]  [3 4 0 1 5 2 6]
       (6F , 6F) ∷ᴸ   -- [0 1 2 3 4 5 6]  [3 4 0 1 5 2 6]
       []ᴸ            -- [0 1 2 3 4 5 6]  [3 4 0 1 5 2 6]

  σ : Permutation 7
  σ = eval σᵗ

  -- these properties are equivalent
  index-computable : tabulate (σ ⟨$⟩ʳ_) ≈[ refl ] idxs
  index-computable = refl

  scatterable : map (σ ⟨$⟩ˡ_) idxs ≈[ refl ] allFin 7
  scatterable = refl

  -- tabulate f = map f allFin, so these express something like inverses
  -- or maybe we can say the bijection σ is lifted over the index vector

transpose : ∀ (i j : Fin n) → Vec A n → Vec A n
transpose i j xs = xs [ i ]≔ lookup xs j [ j ]≔ lookup xs i

module SwapProperties where
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  import Data.Vec.Properties as Vecₚ
  open import Data.Fin using (_≟_)
  open import Relation.Nullary.Decidable.Core using (yes; no)

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

  module _ where
    open import Data.Product using (_×_)
    open import Data.Sum using (_⊎_; inj₁; inj₂)

    transpose-minimal : ∀ (i j k : Fin n) → (xs : Vec A n) → ((i ≡ j) ⊎ (k ≢ i) × (k ≢ j)) → lookup (transpose i j xs) k ≡ lookup xs k
    transpose-minimal i j k xs (inj₁ i≡j) = cong (flip lookup k) (transpose-≡-id′ xs i≡j)
    transpose-minimal i j k xs (inj₂ (k≢i , k≢j)) = begin
      lookup (xs [ i ]≔ lookup xs j [ j ]≔ lookup xs i) k
        ≡⟨ Vecₚ.lookup∘update′ k≢j (xs [ _ ]≔ lookup xs _) (lookup xs _) ⟩
      lookup (xs [ i ]≔ lookup xs j) k
        ≡⟨ Vecₚ.lookup∘update′ k≢i xs (lookup xs _)  ⟩
      lookup xs k
      ∎

  module _ where
    open import Data.Vec.Relation.Unary.Any hiding (lookup)
    import Data.Vec.Relation.Unary.Any.Properties as Anyₚ
    open import Relation.Unary using (Pred)
    open import Data.Sum using (inj₁; inj₂)

    open import Level using (Level)
    private variable ℓ : Level

    import Data.Vec.Properties as Vecₚ
    open Data.Vec using (_[_]=_; _∷_)

    -- TODO : move this out
    []≔-any : {P : Pred A ℓ} {x : A} {xs : Vec A n} {i : Fin n}
            → P x → Any P (xs [ i ]≔ x)
    []≔-any {xs = x ∷ xs…} {i = 0F}    px = here px
    []≔-any {xs = x ∷ xs…} {i = suc i} px = there ([]≔-any {i = i} px)

    transpose-head-any : ∀ {P : Pred A ℓ} → {x₀ : A} → {xs : Vec A n}
                  → (i : Fin n) → Any P xs → Any P (transpose 0F (suc i) (x₀ ∷ xs))
    transpose-head-any {P = P} {x₀ = x₀} {xs = xs} i ∃px 
      with index ∃px ≟ i
    ...| yes ?ₓ≡i = here (subst P (cong (lookup xs) ?ₓ≡i) (Anyₚ.lookup-index ∃px))
    ...| no  ?ₓ≢i = there (subst (Any P) (Vecₚ.[]≔-lookup _ _) ([]≔-any px))
                  where
                  px : P (lookup (xs [ i ]≔ x₀) (index ∃px))
                  px = subst P (sym (Vecₚ.lookup∘update′ ?ₓ≢i xs x₀)) (Anyₚ.lookup-index ∃px)

    transpose-any : ∀ (i j : Fin n) → {P : Pred A ℓ} → {xs : Vec A n}
             → Any P xs → Any P (transpose i j xs)
    transpose-any 0F      0F      {P} {x ∷ xs} = subst (Any P) (sym (transpose-≡-id 0F (x ∷ xs)))
    transpose-any (suc _) (suc _) {xs = _ ∷ _} (here px)   = here px
    transpose-any (suc i) (suc j) {xs = _ ∷ _} (there ∃px) = there (transpose-any i j ∃px)
    transpose-any 0F      (suc j) {xs = _ ∷ _} (there ∃px) = transpose-head-any j ∃px
    transpose-any (suc i) 0F      {xs = _ ∷ _} (there ∃px) = transpose-head-any i ∃px
    transpose-any 0F      (suc _) {xs = _ ∷ _} (here px) = there ([]≔-any px)
    transpose-any (suc _) 0F      {xs = _ ∷ _} (here px) = there ([]≔-any px)

    transpose-any← : ∀ (i j : Fin n) → {P : Pred A ℓ} → {xs : Vec A n}
              → Any P (transpose i j xs) → Any P xs
    transpose-any← i j px = subst (Any _) (transpose-involutive i j _) (transpose-any i j px)

  module _ where
    open import Data.Vec.Relation.Unary.All hiding (lookup)
    import Data.Vec.Relation.Unary.All.Properties as Allₚ
    open import Relation.Unary using (Pred)
    open import Level using (Level)

    private variable ℓ : Level

    -- TODO : move this out
    []≔-all : {P : Pred A ℓ} {y : A} {xs : Vec A n} {i : Fin n}
            → All P xs → P y → All P (xs [ i ]≔ y)
    []≔-all {i = 0F} (px ∷ pxs) py = py ∷ pxs
    []≔-all {i = suc i} (px ∷ pxs) py = px ∷ []≔-all {i = i} pxs py

    transpose-all : ∀ (i j : Fin n) → {P : Pred A ℓ} → {xs : Vec A n} → All P xs → All P (transpose i j xs)
    transpose-all i j pxs = []≔-all ([]≔-all pxs (Allₚ.lookup⁺ pxs j)) (Allₚ.lookup⁺ pxs i)

  module _ where
    open import Data.Vec.Relation.Unary.AllPairs using (AllPairs)
    open import Data.Vec.Relation.Unary.All using (All)
    import Data.Vec.Relation.Unary.AllPairs.Properties as AllPairsₚ
    open import Relation.Binary.Core using (Rel)
    open import Level using (Level)

    private variable ℓ : Level

    infixr 5 _∷ᴬ_
    pattern _∷ᴬ_ x xs = All._∷_ x xs
    pattern []ᴬ = All.[]

    infixr 5 _∷ᴾ_
    pattern _∷ᴾ_ x xs = AllPairs._∷_ x xs
    pattern []ᴾ = AllPairs.[]

    lookupᴬ : ∀ {R : Rel A ℓ} → {x : A} → {xs : Vec A n} → All (R x) xs → (i : Fin n) → R x (lookup xs i)
    lookupᴬ (xᵢ𝑅x ∷ᴬ _) 0F = xᵢ𝑅x
    lookupᴬ {R = R} (_ ∷ᴬ x𝑅xs) (suc i) = lookupᴬ {R = R} x𝑅xs i

    replaceᴬ : ∀ {R : Rel A ℓ} {xs : Vec A n} {x x₀ : A}
              → (i : Fin n)
              → R x₀ x → All (R x₀) xs
              → All (R x₀) (xs [ i ]≔ x)
    replaceᴬ 0F x₀𝑅x (_ ∷ᴬ x₀𝑅xs) = x₀𝑅x ∷ᴬ x₀𝑅xs
    replaceᴬ {R = R} (suc i) x₀𝑅x (x₀𝑅x₁ ∷ᴬ x₀𝑅xs) = x₀𝑅x₁ ∷ᴬ replaceᴬ {R = R} i x₀𝑅x x₀𝑅xs

    transpose-head-allpairs : ∀ {R : Rel A ℓ} → {x₀ : A} → {xs : Vec A n}
                      → (∀ {x y : A} → R x y → R y x)
                      → (i : Fin n) → All (R x₀) xs → AllPairs R xs
                      → All (R (lookup xs i)) (xs [ i ]≔ x₀)
    transpose-head-allpairs         symm 0F      (x₀𝑅xᵢ ∷ᴬ _) (xᵢ𝑅xs ∷ᴾ _) = symm x₀𝑅xᵢ ∷ᴬ xᵢ𝑅xs
    transpose-head-allpairs {R = R} symm (suc i) (_ ∷ᴬ x₀𝑅xs) (xⱼ𝑅xs ∷ᴾ xs𝑅xs) 
      = symm (lookupᴬ {R = R} xⱼ𝑅xs i) ∷ᴬ transpose-head-allpairs symm i x₀𝑅xs xs𝑅xs

    transpose-head-allpairs… : ∀ {R : Rel A ℓ} → {x₀ : A} → {xs : Vec A n}
                       → (∀ {x y : A} → R x y → R y x)
                       → (i : Fin n) → All (R x₀) xs → AllPairs R xs → AllPairs R (xs [ i ]≔ x₀)
    transpose-head-allpairs… _ 0F (_ ∷ᴬ x₀𝑅xs) (_ ∷ᴾ xs𝑅xs) = x₀𝑅xs ∷ᴾ xs𝑅xs
    transpose-head-allpairs… {R = R} symm (suc i) (x₀𝑅xⱼ ∷ᴬ x₀𝑅xs) (xⱼ𝑅xs ∷ᴾ xs𝑅xs)
      = replaceᴬ {R = R} i (symm x₀𝑅xⱼ) xⱼ𝑅xs ∷ᴾ transpose-head-allpairs… symm i x₀𝑅xs xs𝑅xs

    transpose-allpairs : ∀ (i j : Fin n) → {R : Rel A ℓ} → {xs : Vec A n}
                  → (∀ {x y : A} → R x y → R y x)
                  → AllPairs R xs → AllPairs R (transpose i j xs)
    transpose-allpairs 0F 0F {R = R} {xs = xs} _ = subst (AllPairs R) (sym (transpose-≡-id 0F xs))
    transpose-allpairs 0F      (suc j) symm (x𝑅xs ∷ᴾ xs𝑅xs) 
      = transpose-head-allpairs symm j x𝑅xs xs𝑅xs ∷ᴾ transpose-head-allpairs… symm j x𝑅xs xs𝑅xs
    transpose-allpairs (suc i) 0F      symm (x𝑅xs ∷ᴾ xs𝑅xs) 
      = transpose-head-allpairs symm i x𝑅xs xs𝑅xs ∷ᴾ transpose-head-allpairs… symm i x𝑅xs xs𝑅xs
    transpose-allpairs (suc i) (suc j) symm (x𝑅xs ∷ᴾ xs𝑅xs) 
      = transpose-all i j x𝑅xs ∷ᴾ transpose-allpairs i j symm xs𝑅xs

  module _ where
    open import Data.Vec.Membership.Propositional

    transpose-membership : ∀ (i j : Fin n) → {x : A} → {xs : Vec A n}
                    → (x ∈ xs) → (x ∈ transpose i j xs)
    transpose-membership i j {x = x} = transpose-any i j {P = x ≡_}

module UniqueProperties where
  import Data.Vec.Relation.Unary.AllPairs
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; _≗_; ≢-sym; module ≡-Reasoning)

  private module _ where
    infixr 5 _∷ᴬ_
    pattern _∷ᴬ_ x xs = Data.Vec.Relation.Unary.AllPairs._∷_ x xs
    pattern []ᴬ = Data.Vec.Relation.Unary.AllPairs.[]

  import Data.Vec.Relation.Unary.All.Properties as Allₚ
  import Data.Fin.Properties as Finₚ
  open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)

  lookup-injective : ∀ {xs : Vec (Fin n) m} → Unique xs → ∀ i j → lookup xs i ≡ lookup xs j → i ≡ j
  lookup-injective (px ∷ᴬ pxs) 0F 0F xᵢ≡xⱼ = refl
  lookup-injective (px ∷ᴬ pxs) 0F (suc j) xᵢ≡xⱼ = contradiction xᵢ≡xⱼ (Allₚ.lookup⁺ px j)
  lookup-injective (px ∷ᴬ pxs) (suc i) 0F xᵢ≡xⱼ = contradiction (sym xᵢ≡xⱼ) (Allₚ.lookup⁺ px i)
  lookup-injective (px ∷ᴬ pxs) (suc i) (suc j) xᵢ≡xⱼ = cong suc (lookup-injective pxs i j xᵢ≡xⱼ)

  lookup-surjective : ∀ {xs : Vec (Fin n) m} → Unique xs → ∀ i j → i ≡ j → lookup xs i ≡ lookup xs j
  lookup-surjective (px ∷ᴬ pxs) 0F 0F i≡j = refl
  lookup-surjective {n} {suc m} {xs = x ∷ⱽ xs} (px ∷ᴬ pxs) (suc i) (suc j) si≡sj = lookup-surjective pxs i j (Finₚ.suc-injective si≡sj)

  lookup-bijective : ∀ {xs : Vec (Fin n) m} → Unique xs → ∀ i j → i ≡ j ⇔ lookup xs i ≡ lookup xs j
  lookup-bijective {n} {m} {xs} pxs i j = mk⇔ (lookup-surjective pxs i j) (lookup-injective pxs i j)

  transpose-unique : ∀ (i j : Fin n) → {xs : Vec (Fin n) n} → Unique xs → Unique (transpose i j xs)
  transpose-unique i j = SwapProperties.transpose-allpairs i j ≢-sym

  module _ where
    open import Relation.Binary.Definitions using (Irrelevant)

    distinct-irrelevant : Irrelevant {_} {A} _≢_
    distinct-irrelevant x≢y x≢y = refl

  module _ where
    open import Relation.Unary using (Irrelevant)
    open import Data.Vec.Relation.Unary.AllPairs using (irrelevant)

    unique-irrelevant : Irrelevant {_} {Vec A n} Unique
    unique-irrelevant = irrelevant distinct-irrelevant

  module _ where
    open import Relation.Unary using (Decidable)
    import Data.Vec.Relation.Unary.AllPairs as AllPairs
    open import Relation.Nullary.Decidable using (¬?)
    open import Data.Fin using (_≟_)
    open import Relation.Nullary.Decidable.Core using (yes; no)

    unique? : Relation.Unary.Decidable (Unique {n = n})
    unique? {n = n} = Data.Vec.Relation.Unary.AllPairs.allPairs? (λ x y → ¬? (_≟_ {n} x y))

    import Data.Vec.Relation.Unary.Unique.Propositional.Properties as Uniqueₚ
    allFin-Unique : {n : ℕ} → Unique (allFin n)
    allFin-Unique = Uniqueₚ.tabulate⁺ id

module PermutationTable where
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality

  open UniqueProperties 
  open Data.Product using (∃)
  open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
  open Data.Product using (Σ; dmap)

  PermutationTable : ℕ → Set
  PermutationTable n = ∃ (λ (xs : Vec (Fin n) n) → Unique xs)

  table : ∀ {n} → PermutationTable n → Vec (Fin n) n
  table {n} (xs , _) = xs

  id-table : (n : ℕ) → PermutationTable n
  id-table n = allFin n , allFin-Unique

  open import Function.Bundles
  open import Data.Product.Properties using (Σ-≡,≡→≡)
  open SwapProperties
  open ≡-Reasoning

  transpose↔ : ∀ (i j : Fin n) → Vec (Fin n) n ↔ Vec (Fin n) n
  transpose↔ i j = mk↔ₛ′ swp swp inv inv
    where
    swp = transpose i j
    inv = transpose-involutive i j

  transposeᵀ : ∀ (i j : Fin n) → PermutationTable n → PermutationTable n
  transposeᵀ i j = dmap (transpose i j) (transpose-unique i j)

  transposeᵀ↔ : ∀ (i j : Fin n) → PermutationTable n ↔ PermutationTable n
  transposeᵀ↔ i j = mk↔ₛ′ swp swp inv inv
    where
    swp = transposeᵀ i j
    inv : (xs : Σ (Vec (Fin _) _) Unique) → swp (swp xs) ≡ xs
    inv (xs , _) = Σ-≡,≡→≡ (transpose-involutive i j xs , unique-irrelevant _ _)

module SwapFunctional where
  open SwapProperties
  open import Function.Bundles
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import Data.Fin using (_≟_)
  import Data.Vec.Properties as Vecₚ
  open PermutationTable 

  toVector : ∀ (f : Vec (Fin n) n → Vec A n) → Fin n → A
  toVector f = lookup (f (allFin _))

  transposeᶠ : ∀ (i j : Fin n) → Fin n → Fin n
  transposeᶠ {n = n} i j = toVector (transpose i j)

  open import Data.Sum using (inj₂)
  open import Relation.Nullary.Decidable.Core using (yes; no; Dec)

  transposeᶠ-lemmaˡ : ∀ (i j k : Fin n) → k ≡ i → transposeᶠ i j k ≡ j
  transposeᶠ-lemmaˡ i j k k≡i = begin
    lookup (transpose i j (allFin _)) k
      ≡⟨ cong (lookup (transpose i j (allFin _))) k≡i ⟩
    lookup (transpose i j (allFin _)) i
      ≡⟨ lookup-transposeˡ i j (allFin _) ⟩
    lookup (allFin _) j
      ≡⟨ Vecₚ.lookup-allFin _ ⟩
    j
    ∎
  transposeᶠ-lemmaʳ : (i j k : Fin n) → k ≡ j → transposeᶠ i j k ≡ i
  transposeᶠ-lemmaʳ i j k k≡j = begin
    lookup (transpose i j (allFin _)) k
      ≡⟨ cong (lookup (transpose i j (allFin _))) k≡j ⟩
    lookup (transpose i j (allFin _)) j
      ≡⟨ lookup-transposeʳ i j (allFin _) ⟩
    lookup (allFin _) i
      ≡⟨ Vecₚ.lookup-allFin _ ⟩
    i
    ∎
  transposeᶠ-lemmaᵐⁱⁿ : (i j k : Fin n) → k ≢ i → k ≢ j → transposeᶠ i j k ≡ k
  transposeᶠ-lemmaᵐⁱⁿ i j k k≢i k≢j = begin
    lookup (transpose i j (allFin _)) k
      ≡⟨ transpose-minimal _ _ _ (allFin _) (inj₂ (k≢i , k≢j)) ⟩
    lookup (allFin _) k
      ≡⟨ Vecₚ.lookup-allFin _ ⟩
    k
    ∎

  open import Data.Fin.Permutation.Components renaming (transpose to transpose-⊙)

  open import Function.Construct.Identity using (↔-id)
  open UniqueProperties

  open Data.Product using (dmap)

  evalᵀ : TranspositionList n → PermutationTable n
  evalᵀ []ᴸ = id-table _
  evalᵀ ((i , j) ∷ᴸ idxs) = dmap (transpose i j) (transpose-unique i j) (evalᵀ idxs)

  open import Agda.Builtin.Bool using (Bool; true; false)
  open import Data.Fin.Permutation.Components using () renaming (transpose to transpose-⊙)

  transpose-i-j-i : ∀ (i j : Fin n) → transpose-⊙ i j i ≡ j
  transpose-i-j-i i j with i ≟ i
  ... | yes _  = refl
  ... | no i≢i = contradiction refl i≢i
  transpose-i-j-j : ∀ {n} (i j : Fin n) → transpose-⊙ i j j ≡ i
  transpose-i-j-j i j with j ≟ i
  ... | yes j≡i = j≡i
  ... | no j≢i with j ≟ j
  ... | yes j≡j = refl
  ... | no j≢j = contradiction refl j≢j
  transpose-i-j-k : ∀ (i j k : Fin n) → k ≢ i → k ≢ j → transpose-⊙ i j k ≡ k
  transpose-i-j-k i j k k≢i k≢j with k ≟ i
  ... | yes k≡i = contradiction k≡i k≢i
  ... | no k≢i with k ≟ j
  ... | yes k≡j = contradiction k≡j k≢j
  ... | no k≢j = refl

  index-computable : (σ : TranspositionList n) → eval σ ⟨$⟩ʳ_ ≗ lookup (table (evalᵀ σ))
  index-computable []ᴸ _ = sym (Vecₚ.lookup-allFin _)
  index-computable ((i , j) ∷ᴸ σ) k = h (k ≟ i) (k ≟ j)
    where
    tbl = table (evalᵀ σ)
    h : Dec (k ≡ i) → Dec (k ≡ j) → eval ((i , j) ∷ᴸ σ) ⟨$⟩ʳ k ≡ lookup (table (evalᵀ ((i , j) ∷ᴸ σ))) k
    h (yes k≡i) _ = begin
      eval ((i , j) ∷ᴸ σ) ⟨$⟩ʳ k
        ≡⟨ cong _ k≡i ⟩
      eval ((i , j) ∷ᴸ σ) ⟨$⟩ʳ i
        ≡⟨⟩
      eval σ ⟨$⟩ʳ (transpose-⊙ i j i)
        ≡⟨ cong (eval σ ⟨$⟩ʳ_) (transpose-i-j-i i j) ⟩
      eval σ ⟨$⟩ʳ j
        ≡⟨ index-computable σ j ⟩
      lookup tbl j
        ≡⟨ sym (lookup-transposeˡ i j tbl) ⟩
      lookup (transpose i j tbl) i
        ≡⟨ cong _ (sym k≡i) ⟩
      lookup (transpose i j tbl) k
      ∎
    h (no _) (yes k≡j) = begin
      eval ((i , j) ∷ᴸ σ) ⟨$⟩ʳ k
        ≡⟨ cong _ k≡j ⟩
      eval ((i , j) ∷ᴸ σ) ⟨$⟩ʳ j
        ≡⟨⟩
      eval σ ⟨$⟩ʳ (transpose-⊙ i j j)
        ≡⟨ cong (eval σ ⟨$⟩ʳ_) (transpose-i-j-j i j) ⟩
      eval σ ⟨$⟩ʳ i
        ≡⟨ index-computable σ i ⟩
      lookup tbl i
        ≡⟨ sym (lookup-transposeʳ i j tbl) ⟩
      lookup (transpose i j tbl) j
        ≡⟨ cong _ (sym k≡j) ⟩
      lookup (transpose i j tbl) k
      ∎
    h (no k≢i) (no  k≢j) = begin
      eval ((i , j) ∷ᴸ σ) ⟨$⟩ʳ k
        ≡⟨⟩
      eval σ ⟨$⟩ʳ (transpose-⊙ i j k)
        ≡⟨ cong (eval σ ⟨$⟩ʳ_) (transpose-i-j-k i j k k≢i k≢j) ⟩
      eval σ ⟨$⟩ʳ k
        ≡⟨ index-computable σ k ⟩
      lookup tbl k
        ≡⟨ sym (transpose-minimal i j k tbl (inj₂ (k≢i , k≢j))) ⟩
      lookup (transpose i j tbl) k
      ∎

  open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
  open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ᵀ_; _∉_ to _∉ᵀ_)
  open import Data.Vec.Membership.Propositional.Properties
  open import Data.Fin.Subset using (Subset; _∈_; _∉_; ∣_∣; _-_; ⊤)
  open import Data.Fin.Subset.Properties
  open import Data.Vec.Relation.Unary.Any using (here; there; index)
  open import Data.Nat using (_+_; _<_; _≤_; s≤s)
  import Data.Nat.Properties as ℕₚ
  open import Data.Sum using (_⊎_; inj₁; inj₂)

  open import Data.Vec.Relation.Unary.All using (All; head; map; zip; zipWith)
  import Data.Vec.Relation.Unary.All.Properties as Allₚ

  open import Relation.Unary using (_∩_)
  import Data.Vec.Relation.Unary.Any.Properties as Anyₚ

  infixr 5 _∷ᴬ_
  pattern _∷ᴬ_ x xs = All._∷_ x xs
  pattern []ᴬ = All.[]

  infixr 5 _∷ᵁ_
  pattern _∷ᵁ_ x xs = Unique._∷_ x xs
  pattern []ᵁ = Unique.[]

  x∈p⇒∣p∣≢0 : {x : Fin n} → {p : Subset n} → x ∈ p → ¬ ∣ p ∣ ≡ 0
  x∈p⇒∣p∣≢0 {n = n} {x = x} {p = p} x∈p ∣p∣≡0 = contradiction 1+∣p∣≡0 ℕₚ.1+n≢0
    where
    1+∣p∣≡0 = ℕₚ.n≤0⇒n≡0 (subst (suc ∣ p - x ∣ ≤_) ∣p∣≡0 (x∈p⇒∣p-x∣<∣p∣ x∈p))

  x∈p⇒∣p∣>0 : {x : Fin n} → {p : Subset n} → x ∈ p → ¬ ∣ p ∣ ≤ 0
  x∈p⇒∣p∣>0 {n = n} {x = x} {p = p} x∈p ∣p∣≤0 = x∈p⇒∣p∣≢0 x∈p (ℕₚ.n≤0⇒n≡0 ∣p∣≤0)

  all-Fin-∈-PermutationTable : ∀ {n} → {xs : Vec (Fin n) n} → Unique xs → ∀ (i : Fin n) → i ∈ᵀ xs
  all-Fin-∈-PermutationTable {n = n} {xs = xs} uxs i = h xs uxs ⊤ (Allₚ.lookup⁻ (λ _ → ∈⊤)) ∈⊤ (∣p∣≤n ⊤)
    where
    h : (xs : Vec (Fin n) m) → (uxs : Unique xs)
      → (unseen : Subset n) → (xs-unseen : All (_∈ unseen) xs)
      → (i ∈ unseen) → ∣ unseen ∣ ≤ m 
      → i ∈ᵀ xs
    h []ⱽ []ᵁ  unseen []ᴬ i-unseen ∣unseen∣≤0 = contradiction ∣unseen∣≤0 (x∈p⇒∣p∣>0 i-unseen)
    h {m = suc m-1} (x ∷ⱽ xs) (ux ∷ᵁ uxs) unseen (x-unseen ∷ᴬ xs-unseen) i-unseen ∣unseen∣≤m with i ≟ x
    ... | yes i≡x = here i≡x
    ... | no  i≢x = there (h xs uxs yet-unseen xs-yet-unseen i-yet-unseen ∣yet-unseen∣≤m-1)
      where
      yet-unseen : Subset n
      yet-unseen = unseen - x

      i-yet-unseen : i ∈ yet-unseen
      i-yet-unseen = x∈p∧x≢y⇒x∈p-y i-unseen i≢x

      xs-yet-unseen : All (_∈ yet-unseen) xs
      xs-yet-unseen = map (λ (x≢y , y-unseen) → x∈p∧x≢y⇒x∈p-y y-unseen (≢-sym x≢y)) (zip (ux , xs-unseen))

      ∣yet-unseen∣≤m-1 : ∣ yet-unseen ∣ ≤ m-1
      ∣yet-unseen∣≤m-1 = ℕₚ.≤-pred (ℕₚ.≤-trans (x∈p⇒∣p-x∣<∣p∣ x-unseen) ∣unseen∣≤m)

  open Data.Product using (∃; proj₁; proj₂)

  find-index : ∀ {n} → {xs : Vec (Fin n) n} → Unique xs → ∀ (i : Fin n) → ∃ λ j → lookup xs j ≡ i
  find-index uxs i = index i∈xs , sym (Anyₚ.lookup-index i∈xs)
    where
    i∈xs = all-Fin-∈-PermutationTable uxs i

  open Data.Product using (_×_)

  op-inject : Fin m → m ≤ n → Fin n
  op-inject i m≤n = Data.Fin.opposite (Data.Fin.inject≤ i m≤n)

  transposition-at-n-i : (Fin m) → m ≤ n → PermutationTable n → (Fin n × Fin n)
  transposition-at-n-i i m≤n (xs , uxs) = from , to
    where
    from = op-inject i m≤n
    to = proj₁ (find-index uxs from)

  h : (Fin m) → m ≤ n → PermutationTable n → TranspositionList n
  h 0F m≤n π@(xs , uxs) = transposition-at-n-i 0F m≤n π ∷ᴸ []ᴸ
  h {n = n@(suc n-1)} (suc i) m≤n π@(xs , uxs) = (transposition-at-n-i (suc i) m≤n π) ∷ᴸ h i (ℕₚ.≤-trans (ℕₚ.≤-pred m≤n) (ℕₚ.n≤1+n _)) (transposeᵀ op op-index (xs , uxs))
    where
    op = proj₁ (transposition-at-n-i (suc i) m≤n π)
    op-index = proj₁ (find-index uxs op)

  decomposeᵀ : PermutationTable n → TranspositionList n
  decomposeᵀ {n = 0} ([]ⱽ , []ᴾ) = []ᴸ
  decomposeᵀ {n = n@(suc n-1)} = h (Data.Fin.opposite {n = n} 0F) ℕₚ.≤-refl 

  decomposeᵀ-pf : (π : PermutationTable n) → ∃ λ (σ : TranspositionList n) → eval σ ⟨$⟩ʳ_ ≗ lookup (table π)
  decomposeᵀ-pf {n = 0} ([]ⱽ , []ᴾ) = []ᴸ , λ ()
  decomposeᵀ-pf {n = n@(suc n-1)} π = ?

  module Example… where
    open Example

    infixr 5 _∷ᴬ_
    pattern _∷ᴬ_ x xs = All._∷_ x xs
    pattern []ᴬ = All.[]

    infixr 5 _∷ᵁ_
    pattern _∷ᵁ_ x xs = Unique._∷_ x xs
    pattern []ᵁ = Unique.[]

    idxs-unique : Unique idxs
    idxs-unique =    ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ []ᴬ))))))
                  ∷ᵁ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ []ᴬ)))))
                  ∷ᵁ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ []ᴬ))))
                  ∷ᵁ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ []ᴬ)))
                  ∷ᵁ ((λ ()) ∷ᴬ ((λ ()) ∷ᴬ []ᴬ))
                  ∷ᵁ ((λ ()) ∷ᴬ []ᴬ)
                  ∷ᵁ []ᴬ
                  ∷ᵁ []ᵁ

    idxsᵀ : PermutationTable 7
    idxsᵀ = idxs , idxs-unique

    idxsᴸ : TranspositionList 7
    idxsᴸ = decomposeᵀ idxsᵀ

    idxsᵀ← : PermutationTable 7
    idxsᵀ← = evalᵀ idxsᴸ

    round-trip : idxsᵀ ≡ idxsᵀ←
    round-trip = begin
      idxs , idxs-unique
        ≡⟨ ? ⟩
      ?
      ∎
-- transpose (Permutations.SwapFunctional.op 6 (Data.Fin.fromℕ 5) ℕₚ.≤-refl (proj₁ idxsᵀ) (proj₂ idxsᵀ))
--      (Permutations.SwapFunctional.op-index 6 (Data.Fin.fromℕ 5) ℕₚ.≤-refl (proj₁ idxsᵀ) (proj₂ idxsᵀ))
--      (proj₁ (evalᵀ (
  --      Permutations.SwapFunctional.h 
  --        6 
  --        (Data.Fin.fromℕ 5)
  --        (ℕₚ.≤-trans (ℕₚ.≤-pred ℕₚ.≤-refl) (ℕₚ.n≤1+n 6))
  --        (transposeᵀ 
  --          (Permutations.SwapFunctional.op 
  --            6 
  --            (Data.Fin.fromℕ 5)
  --            ℕₚ.≤-refl
  --            (proj₁ idxsᵀ)
  --            (proj₂ idxsᵀ)
--            )
  --          (Permutations.SwapFunctional.op-index
    --          6
    --          (Data.Fin.fromℕ 5)
    --          ℕₚ.≤-refl
    --          (proj₁ idxsᵀ)
    --          (proj₂ idxsᵀ)
  --          )
  --          (proj₁ idxsᵀ , proj₂ idxsᵀ)
--          )
  --      )))
      
  pf : (π : PermutationTable n) → eval (decomposeᵀ π) ⟨$⟩ʳ_ ≗ lookup (table π)
  pf = ?
