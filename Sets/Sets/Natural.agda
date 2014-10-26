module Sets.Sets.Natural where

open import Function
import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Sets.Sets.Basic
open import Sets.Sets.Extensionality
open import Sets.Sets.Pairing
open import Sets.Sets.Union
open import Sets.Sets.Separation

_⁺ : (A : Set) → Set
A ⁺ = A ∪ (singleton A)

postulate
  infinite : ∃ \A → (∅ ∈ A) ∧ (∀ X → X ∈ A → X ⁺ ∈ A)

ℕ : Set
ℕ = proj₁ infinite

fromℕ-proof : Nat.ℕ → ∃ \N → N ∈ ℕ
fromℕ-proof Nat.zero = ∅ , (∧-left $ proj₂ infinite)
fromℕ-proof (Nat.suc i) = let I-ex = fromℕ-proof i ; I = proj₁ I-ex in I ⁺ , (∧-right (proj₂ infinite) I $ proj₂ I-ex)

fromℕ : Nat.ℕ → Set
fromℕ n = proj₁ $ fromℕ-proof n

module numbers where
  0≢1inNat : 0 ≢ 1
  0≢1inNat eq = 1+n≰n $ ≤-reflexive {i = 1} (≡-sym eq)
    where
    open DecTotalOrder Nat.decTotalOrder
      renaming (reflexive to ≤-reflexive)

  0inSet : fromℕ 0 ≡ ∅
  0inSet = ≡-refl

  1inSet : fromℕ 1 ≡ ∅ ∪ singleton ∅
  1inSet = ≡-refl

  0≢1inSet : fromℕ 0 ≢ fromℕ 1
  0≢1inSet = lemma
    where
    lemma : ∅ ≢ ∅ ∪ singleton ∅
    lemma eq = proj₂ ∃-empty ∅ $ proj⃖ (replace-≡ eq ∅) $ satisfy-in-union ∅ $ singleton ∅ , B∈[A,B] , A∈[A,B]
open numbers public
