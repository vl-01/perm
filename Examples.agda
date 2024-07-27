{-# OPTIONS --safe -WnoUnsupportedIndexedMatch #-}
  

module Examples where

open import Data.Product using (_,_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
open import Data.Fin.Permutation using (_⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_) renaming (Permutation′ to Permutation)
open import Data.Fin.Permutation.Transposition.List using (TranspositionList; eval)

open import Data.Vec using (Vec; lookup; tabulate; _++_; allFin)

private module _ where
  import Data.List
  import Data.Vec
  open import Data.Vec.Relation.Unary.All using (All)
  open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)

  infixr 5 _∷ᴸ_
  pattern _∷ᴸ_ x xs = Data.List._∷_ x xs
  pattern []ᴸ = Data.List.[]

  infixr 5 _∷ⱽ_
  pattern _∷ⱽ_ x xs = Data.Vec._∷_ x xs
  pattern []ⱽ = Data.Vec.[]

  infixr 5 _∷ᴬ_
  pattern _∷ᴬ_ x xs = All._∷_ x xs
  pattern []ᴬ = All.[]

  infixr 5 _∷ᵁ_
  pattern _∷ᵁ_ x xs = Unique._∷_ x xs
  pattern []ᵁ = Unique.[]

private
  variable
    A B : Set
    n m : ℕ
    i j k : Fin n

module Example where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
  index-computable : tabulate (σ ⟨$⟩ʳ_) ≡ idxs
  index-computable = refl

  scatterable : map (σ ⟨$⟩ˡ_) idxs ≡ allFin 7
  scatterable = refl

  -- tabulate f = map f allFin, so these express something like inverses
  -- or maybe we can say the bijection σ is lifted over the index vector

open import PermutationTable
open import PermutationTable.Properties
open import PermutationTable.Components.Properties

module _ where
  open import Relation.Binary.PropositionalEquality
  open ≡-Reasoning
  open import PermutationTable.TranspositionList renaming (eval to evalᵀ)
  open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
  open import Data.Vec.Relation.Unary.Any using (here; there; index)
  open import Data.Nat using (_+_; _<_; _≤_; s≤s)
  import Data.Nat.Properties as ℕₚ

  import Data.Vec.Relation.Unary.Any.Properties as Anyₚ
  open Data.Product using (∃; _×_; proj₁; proj₂)

  find-index : ∀ {n} → {xs : Vec (Fin n) n} → Unique xs → ∀ (i : Fin n) → ∃ λ j → lookup xs j ≡ i
  find-index uxs i = index i∈xs , sym (Anyₚ.lookup-index i∈xs)
    where
    i∈xs = all-Fin-∈-PermutationTable uxs i

  op-inject : Fin m → m ≤ n → Fin n
  op-inject i m≤n = Data.Fin.opposite (Data.Fin.inject≤ i m≤n)

  transposition-at-i/n : (Fin m) → m ≤ n → PermutationTable n → (Fin n × Fin n)
  transposition-at-i/n i m≤n (xs , uxs) = from , to
    where
    from = op-inject i m≤n
    to = proj₁ (find-index uxs from)

  h : (Fin m) → m ≤ n → PermutationTable n → TranspositionList n
  h 0F m≤n π@(xs , uxs) = transposition-at-i/n 0F m≤n π ∷ᴸ []ᴸ
  h {n = n@(suc n-1)} (suc i) m≤n π@(xs , uxs) = (transposition-at-i/n (suc i) m≤n π) ∷ᴸ h i (ℕₚ.≤-trans (ℕₚ.≤-pred m≤n) (ℕₚ.n≤1+n _)) (transpose op op-index (xs , uxs))
    where
    op = proj₁ (transposition-at-i/n (suc i) m≤n π)
    op-index = proj₁ (find-index uxs op)

  decomposeᵀ : PermutationTable n → TranspositionList n
  decomposeᵀ {n = 0} ([]ⱽ , []ᴾ) = []ᴸ
  decomposeᵀ {n = n@(suc n-1)} = h (Data.Fin.opposite {n = n} 0F) ℕₚ.≤-refl 

  decomposeᵀ-pf : (π : PermutationTable n) → ∃ λ (σ : TranspositionList n) → eval σ ⟨$⟩ʳ_ ≗ lookup (table π)
  decomposeᵀ-pf {n = 0} ([]ⱽ , []ᴾ) = []ᴸ , λ ()
  decomposeᵀ-pf {n = n@(suc n-1)} π = ?

  module Example… where
    open Example

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
      
  pf : (π : PermutationTable n) → eval (decomposeᵀ π) ⟨$⟩ʳ_ ≗ lookup (table π)
  pf = ?
