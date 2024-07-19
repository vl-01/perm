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
  σᵗ = (0F , 3F) ∷ᴸ
       (1F , 4F) ∷ᴸ 
       (2F , 3F) ∷ᴸ
       (3F , 4F) ∷ᴸ
       (4F , 5F) ∷ᴸ
       []ᴸ

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

  swap-involutive : ∀ (i j : Fin n) (xs : Vec A n) → swap i j (swap i j xs) ≡ xs
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
    open import Data.Sum using (_⊎_)

    swap-minimal : ∀ (i j k : Fin n) → (xs : Vec A n) → ((i ≡ j) ⊎ (k ≢ i) × (k ≢ j)) → lookup (swap i j xs) k ≡ lookup xs k
    swap-minimal i j k xs (_⊎_.inj₁ i≡j) = cong (flip lookup k) (swap-≡-id′ xs i≡j)
    swap-minimal i j k xs (_⊎_.inj₂ (k≢i , k≢j)) = begin
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
    open import Level using (Level)
    open import Data.Sum using (inj₁; inj₂)

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
    open import Data.Vec.Relation.Unary.AllPairs
    import Data.Vec.Relation.Unary.AllPairs.Properties as AllPairsₚ
    open import Relation.Binary.Core using (Rel)
    open import Level using (Level)

    private variable ℓ : Level

    swap-allpairs : ∀ (i j : Fin n) → {R : Rel A ℓ} → {xs : Vec A n}
                  → (∀ (x y : A) → R x y → R y x)
                  → AllPairs R xs → AllPairs R (swap i j xs)
    swap-allpairs i j symmetric pxs = ?

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

module SwapUniqueProperties where
  open UniqueProperties
  open SwapProperties
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open Data.Fin using (_≟_)
  open import Relation.Nullary.Decidable.Core using (yes; no)

  swap-unique : ∀ (i j : Fin n) → {xs : Vec (Fin n) n} → UniqueFin xs → UniqueFin (swap i j xs)
  swap-unique i j = SwapProperties.swap-allpairs i j ? -- need to show that Distinct is symmetric

module SwapTranspose where
  open Data.Vec hiding (transpose)
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open Data.Fin.Permutation using (transpose)
  open import Data.Fin.Permutation.Components renaming (transpose to ⊙-transpose)
  import Data.Vec.Properties as Vecₚ

  ⊙-swap-transpose : ∀ (i j : Fin n) (xs : Vec (Fin n) n) → swap i j xs ≡ map (⊙-transpose i j) xs
  ⊙-swap-transpose i j xs = begin
    swap i j xs
    ≡⟨ ? ⟩
    map (⊙-transpose i j) xs
    -- how to deconstruct application?
    --  ⊙-transpose i j k with does (k ≟ i)
    --  ... | true  = j
    --  ... | false with does (k ≟ j)
    --  ...   | true  = i
    --  ...   | false = k
    ∎

  swap-transpose : ∀ {σ : TranspositionList n} {π : Vec (Fin n) n}
                  → (i j : Fin n)
                  → π ≡ map (eval σ ⟨$⟩ˡ_) (allFin n) 
                  → swap i j π ≡ map (eval ((j , i) ∷ᴸ σ) ⟨$⟩ˡ_) (allFin n)
  swap-transpose {n} {σ} {π} i j π≈σ = begin
    π [ i ]≔ lookup π j [ j ]≔ lookup π i
      ≡⟨ ⊙-swap-transpose _ _ _ ⟩
    map (⊙-transpose i j) π
      ≡⟨⟩
    map (transpose j i ⟨$⟩ˡ_) π
      ≡⟨ cong _ π≈σ ⟩
    map (transpose j i ⟨$⟩ˡ_) (map (eval σ ⟨$⟩ˡ_) 0…n)
      ≡⟨⟩
    (map (transpose j i ⟨$⟩ˡ_) ∘ map (eval σ ⟨$⟩ˡ_)) 0…n
      ≡⟨ sym (Vecₚ.map-∘ _ _ _) ⟩
    map ((transpose j i ⟨$⟩ˡ_) ∘ (eval σ ⟨$⟩ˡ_)) 0…n
      ≡⟨⟩
    map (transpose j i ∘ₚ eval σ ⟨$⟩ˡ_) 0…n
      ≡⟨⟩
    map (eval ((j , i) ∷ᴸ σ) ⟨$⟩ˡ_) 0…n
    ∎
    where 0…n = allFin n
