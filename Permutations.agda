{-# OPTIONS --safe -WnoUnsupportedIndexedMatch #-}

module Permutations where

open import Function.Base using (_∘_ ; const; flip)
open import Function.Bundles using (_⇔_; mk⇔)

open import Relation.Nullary.Negation using (contradiction; ¬_)

open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; _≗_)

open import Data.Nat using (ℕ; zero; suc)

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
open import Data.Fin.Permutation using (_⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_) renaming (Permutation′ to Permutation)
open import Data.Fin.Permutation.Transposition.List using (TranspositionList; eval)

open import Data.Vec using (Vec; lookup; tabulate; updateAt; _[_]≔_; _++_; map; allFin)

import Data.List
infixr 5 _∷ᴸ_
pattern _∷ᴸ_ x xs = Data.List._∷_ x xs
pattern []ᴸ = Data.List.[]

infixr 5 _∷ⱽ_
pattern _∷ⱽ_ x xs = Data.Vec._∷_ x xs
pattern []ⱽ = Data.Vec.[]

private
  variable
    A : Set
    n m : ℕ

module Example where
  open import Data.Vec.Relation.Binary.Equality.Cast using (_≈[_]_)
  open import Data.Bool renaming (true to 𝐓; false to 𝐅)

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

swap : ∀ (i j : Fin n) → Vec A n → Vec A n
swap i j xs = xs [ i ]≔ lookup xs j [ j ]≔ lookup xs i

module SwapProperties where
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  import Data.Vec.Properties as Vecₚ
  open import Data.Fin using (_≟_)
  open import Relation.Nullary.Decidable.Core using (yes; no)

  swap-≡-id : ∀ (i : Fin n) (xs : Vec A n) → swap i i xs ≡ xs
  swap-≡-id i xs = begin
    xs [ i ]≔ lookup xs i [ i ]≔ lookup xs i
      ≡⟨ Vecₚ.[]≔-idempotent xs i ⟩
    xs [ i ]≔ lookup xs i
      ≡⟨ Vecₚ.[]≔-lookup xs i ⟩
    xs
    ∎

  swap-≡-id′ : ∀ {i j : Fin n} (xs : Vec A n) → i ≡ j → swap i j xs ≡ xs
  swap-≡-id′ {A} {n} {i} {j} xs i≡j = trans (cong (λ i′ → swap i′ j xs) i≡j) (swap-≡-id j xs)
            
  swap-symmetric : ∀ (i j : Fin n) (xs : Vec A n) → swap i j xs ≡ swap j i xs
  swap-symmetric i j xs with i ≟ j
  ... | yes i≡j = trans (swap-≡-id′ xs i≡j) (sym (swap-≡-id′ xs (sym i≡j)))
  ... | no i≢j = Vecₚ.[]≔-commutes xs i j i≢j
    
  lookup-swapˡ : ∀ (i j : Fin n) → (xs : Vec A n) → lookup (swap i j xs) i ≡ lookup xs j
  lookup-swapˡ i j xs with i ≟ j
  ... | yes i≡j = begin
          lookup (swap i j xs) i
            ≡⟨ cong (flip lookup _) (swap-≡-id′ xs i≡j) ⟩
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

  lookup-swapʳ : ∀ (i j : Fin n) → (xs : Vec A n) → lookup (swap i j xs) j ≡ lookup xs i
  lookup-swapʳ i j xs = begin
    lookup (swap i j xs) j
      ≡⟨ cong (flip lookup j) (swap-symmetric i j xs) ⟩ 
    lookup (swap j i xs) j
      ≡⟨ lookup-swapˡ j i xs ⟩
    lookup xs i
    ∎

  swap-involutive : ∀ (i j : Fin n) → (xs : Vec A n) → swap i j (swap i j xs) ≡ xs
  swap-involutive i j xs with i ≟ j
  ... | yes i≡j = trans (swap-≡-id′ _ i≡j) (swap-≡-id′ _ i≡j)
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
          ≡⟨ cong (_ [ _ ]≔ lookup ys _ [ _ ]≔_) (lookup-swapˡ _ _ xs) ⟩
        xs [ i ]≔ lookup ys j [ j ]≔ lookup xs j
          ≡⟨ cong ((_[ _ ]≔ lookup xs _) ∘ (_ [ _ ]≔_)) (lookup-swapʳ _ _ xs) ⟩
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

    swap-minimal : ∀ (i j k : Fin n) → (xs : Vec A n) → ((i ≡ j) ⊎ (k ≢ i) × (k ≢ j)) → lookup (swap i j xs) k ≡ lookup xs k
    swap-minimal i j k xs (inj₁ i≡j) = cong (flip lookup k) (swap-≡-id′ xs i≡j)
    swap-minimal i j k xs (inj₂ (k≢i , k≢j)) = begin
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

    swap-head-any : ∀ {P : Pred A ℓ} → {x₀ : A} → {xs : Vec A n}
                  → (i : Fin n) → Any P xs → Any P (swap 0F (suc i) (x₀ ∷ xs))
    swap-head-any {P = P} {x₀ = x₀} {xs = xs} i ∃px 
      with index ∃px ≟ i
    ...| yes ?ₓ≡i = here (subst P (cong (lookup xs) ?ₓ≡i) (Anyₚ.lookup-index ∃px))
    ...| no  ?ₓ≢i = there (subst (Any P) (Vecₚ.[]≔-lookup _ _) ([]≔-any px))
                  where
                  px : P (lookup (xs [ i ]≔ x₀) (index ∃px))
                  px = subst P (sym (Vecₚ.lookup∘update′ ?ₓ≢i xs x₀)) (Anyₚ.lookup-index ∃px)

    swap-any : ∀ (i j : Fin n) → {P : Pred A ℓ} → {xs : Vec A n} → Any P xs → Any P (swap i j xs)
    swap-any 0F      0F      {P} {x ∷ xs} = subst (Any P) (sym (swap-≡-id 0F (x ∷ xs)))
    swap-any (suc _) (suc _) {xs = _ ∷ _} (here px)   = here px
    swap-any (suc i) (suc j) {xs = _ ∷ _} (there ∃px) = there (swap-any i j ∃px)
    swap-any 0F      (suc j) {xs = _ ∷ _} (there ∃px) = swap-head-any j ∃px
    swap-any (suc i) 0F      {xs = _ ∷ _} (there ∃px) = swap-head-any i ∃px
    swap-any 0F      (suc _) {xs = _ ∷ _} (here px) = there ([]≔-any px)
    swap-any (suc _) 0F      {xs = _ ∷ _} (here px) = there ([]≔-any px)

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

    swap-all : ∀ (i j : Fin n) → {P : Pred A ℓ} → {xs : Vec A n} → All P xs → All P (swap i j xs)
    swap-all i j pxs = []≔-all ([]≔-all pxs (Allₚ.lookup⁺ pxs j)) (Allₚ.lookup⁺ pxs i)

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

    swap-head-allpairs : ∀ {R : Rel A ℓ} → {x₀ : A} → {xs : Vec A n}
                      → (∀ {x y : A} → R x y → R y x)
                      → (i : Fin n) → All (R x₀) xs → AllPairs R xs
                      → All (R (lookup xs i)) (xs [ i ]≔ x₀)
    swap-head-allpairs         symm 0F      (x₀𝑅xᵢ ∷ᴬ _) (xᵢ𝑅xs ∷ᴾ _) = symm x₀𝑅xᵢ ∷ᴬ xᵢ𝑅xs
    swap-head-allpairs {R = R} symm (suc i) (_ ∷ᴬ x₀𝑅xs) (xⱼ𝑅xs ∷ᴾ xs𝑅xs) 
      = symm (lookupᴬ {R = R} xⱼ𝑅xs i) ∷ᴬ swap-head-allpairs symm i x₀𝑅xs xs𝑅xs

    swap-head-allpairs… : ∀ {R : Rel A ℓ} → {x₀ : A} → {xs : Vec A n}
                       → (∀ {x y : A} → R x y → R y x)
                       → (i : Fin n) → All (R x₀) xs → AllPairs R xs → AllPairs R (xs [ i ]≔ x₀)
    swap-head-allpairs… _ 0F (_ ∷ᴬ x₀𝑅xs) (_ ∷ᴾ xs𝑅xs) = x₀𝑅xs ∷ᴾ xs𝑅xs
    swap-head-allpairs… {R = R} symm (suc i) (x₀𝑅xⱼ ∷ᴬ x₀𝑅xs) (xⱼ𝑅xs ∷ᴾ xs𝑅xs)
      = replaceᴬ {R = R} i (symm x₀𝑅xⱼ) xⱼ𝑅xs ∷ᴾ swap-head-allpairs… symm i x₀𝑅xs xs𝑅xs

    swap-allpairs : ∀ (i j : Fin n) → {R : Rel A ℓ} → {xs : Vec A n}
                  → (∀ {x y : A} → R x y → R y x)
                  → AllPairs R xs → AllPairs R (swap i j xs)
    swap-allpairs 0F 0F {R = R} {xs = xs} _ = subst (AllPairs R) (sym (swap-≡-id 0F xs))
    swap-allpairs 0F      (suc j) symm (x𝑅xs ∷ᴾ xs𝑅xs) 
      = swap-head-allpairs symm j x𝑅xs xs𝑅xs ∷ᴾ swap-head-allpairs… symm j x𝑅xs xs𝑅xs
    swap-allpairs (suc i) 0F      symm (x𝑅xs ∷ᴾ xs𝑅xs) 
      = swap-head-allpairs symm i x𝑅xs xs𝑅xs ∷ᴾ swap-head-allpairs… symm i x𝑅xs xs𝑅xs
    swap-allpairs (suc i) (suc j) symm (x𝑅xs ∷ᴾ xs𝑅xs) 
      = swap-all i j x𝑅xs ∷ᴾ swap-allpairs i j symm xs𝑅xs

module UniqueProperties where
  import Data.Vec.Relation.Unary.AllPairs

  infixr 5 _∷ᴬ_
  pattern _∷ᴬ_ x xs = Data.Vec.Relation.Unary.AllPairs._∷_ x xs
  pattern []ᴬ = Data.Vec.Relation.Unary.AllPairs.[]

  import Data.Vec.Relation.Unary.All.Properties as Allₚ
  import Data.Fin.Properties as Finₚ
  open import UniquePropositional using (Unique) public

  lookup-injective : ∀ {xs : Vec (Fin n) m} → Unique (Finₚ.≡-decSetoid n) xs → ∀ i j → lookup xs i ≡ lookup xs j → i ≡ j
  lookup-injective (px ∷ᴬ pxs) 0F 0F xᵢ≡xⱼ = refl
  lookup-injective (px ∷ᴬ pxs) 0F (suc j) xᵢ≡xⱼ = contradiction xᵢ≡xⱼ (Allₚ.lookup⁺ px j)
  lookup-injective (px ∷ᴬ pxs) (suc i) 0F xᵢ≡xⱼ = contradiction (sym xᵢ≡xⱼ) (Allₚ.lookup⁺ px i)
  lookup-injective (px ∷ᴬ pxs) (suc i) (suc j) xᵢ≡xⱼ = cong suc (lookup-injective pxs i j xᵢ≡xⱼ)

  lookup-surjective : ∀ {xs : Vec (Fin n) m} → Unique (Finₚ.≡-decSetoid n) xs → ∀ i j → i ≡ j → lookup xs i ≡ lookup xs j
  lookup-surjective (px ∷ᴬ pxs) 0F 0F i≡j = refl
  lookup-surjective {n} {suc m} {xs = x ∷ⱽ xs} (px ∷ᴬ pxs) (suc i) (suc j) si≡sj = lookup-surjective pxs i j (Finₚ.suc-injective si≡sj)

  lookup-bijective : ∀ {xs : Vec (Fin n) m} → Unique (Finₚ.≡-decSetoid n) xs → ∀ i j → i ≡ j ⇔ lookup xs i ≡ lookup xs j
  lookup-bijective {n} {m} {xs} pxs i j = mk⇔ (lookup-surjective pxs i j) (lookup-injective pxs i j)

  UniqueFin : Vec (Fin n) n → Set
  UniqueFin {n} = Unique (Finₚ.≡-decSetoid n)

  swap-unique : ∀ (i j : Fin n) → {xs : Vec (Fin n) n} → UniqueFin xs → UniqueFin (swap i j xs)
  swap-unique i j = SwapProperties.swap-allpairs i j (_∘ sym)

module SwapFunctional where
  open SwapProperties
  open import Function.Bundles
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import Data.Fin using (_≟_)
  import Data.Vec.Properties as Vecₚ

  swapᴾ : ∀ (i j : Fin n) → Fin n → Fin n
  swapᴾ {n = n} i j = lookup (swap i j (allFin n))

  open import Data.Sum using (inj₂)
  open import Relation.Nullary.Decidable.Core using (yes; no)

  swapᴾ-involutive : ∀ (i j k : Fin n) → swapᴾ i j (swapᴾ i j k) ≡ k
  swapᴾ-involutive i j k with k ≟ i | k ≟ j
  ... | yes k≡i | _ = begin
          swapᴾ i j (swapᴾ i j k)
            ≡⟨ cong (swapᴾ i j) lemma  ⟩
          swapᴾ i j j
            ≡⟨⟩
          lookup (swap i j (allFin _)) j
            ≡⟨ lookup-swapʳ i j (allFin _) ⟩
          lookup (allFin _) i
            ≡⟨ Vecₚ.lookup-allFin _ ⟩
          i
            ≡⟨ sym k≡i ⟩
          k
          ∎
          where
          lemma : swapᴾ i j k ≡ j
          lemma = begin
            lookup (swap i j (allFin _)) k
              ≡⟨ cong (lookup (swap i j (allFin _))) k≡i ⟩
            lookup (swap i j (allFin _)) i
              ≡⟨ lookup-swapˡ i j (allFin _) ⟩
            lookup (allFin _) j
              ≡⟨ Vecₚ.lookup-allFin _ ⟩
            j
            ∎
  ... | no _ | yes k≡j = begin
          swapᴾ i j (swapᴾ i j k)
            ≡⟨ cong (swapᴾ i j) lemma  ⟩
          swapᴾ i j i
            ≡⟨⟩
          lookup (swap i j (allFin _)) i
            ≡⟨ lookup-swapˡ i j (allFin _) ⟩
          lookup (allFin _) j
            ≡⟨ Vecₚ.lookup-allFin _ ⟩
          j
            ≡⟨ sym k≡j ⟩
          k
          ∎
          where
          lemma : swapᴾ i j k ≡ i
          lemma = begin
            lookup (swap i j (allFin _)) k
              ≡⟨ cong (lookup (swap i j (allFin _))) k≡j ⟩
            lookup (swap i j (allFin _)) j
              ≡⟨ lookup-swapʳ i j (allFin _) ⟩
            lookup (allFin _) i
              ≡⟨ Vecₚ.lookup-allFin _ ⟩
            i
            ∎
  ... | no k≢i | no k≢j = trans (cong (swapᴾ i j) lemma) lemma
          where
          lemma : swapᴾ i j k ≡ k
          lemma = begin
            lookup (swap i j (allFin _)) k
              ≡⟨ swap-minimal _ _ _ (allFin _) (inj₂ (k≢i , k≢j)) ⟩
            lookup (allFin _) k
              ≡⟨ Vecₚ.lookup-allFin _ ⟩
            k
            ∎

  swapᴾ-inverse : ∀ (i j : Fin n) → Fin n ↔ Fin n
  swapᴾ-inverse i j = mk↔ₛ′ (swapᴾ i j) (swapᴾ i j) (swapᴾ-involutive i j) (swapᴾ-involutive i j)
