open import Level

module Sets.Sets {a : Level} where

open import Function
open import Function.Equivalence
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product hiding (_,_)
open import Relation.Binary
open import Relation.Binary.Core using (_≡_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary renaming (∅ to ∅₀)

∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (\x → B) = ∃ x ∶ B

separation-syntax : ∀{a b} {A : Set a} → (A → Set b) → Pred A b
separation-syntax P = P

syntax separation-syntax (\a → P) = [ a ∣ P ]

Subset : ∀{ℓ} (A : Set a) → Set _
Subset {ℓ} A = Pred A ℓ

FamilyOfSet : ∀{ℓ} (A : Set a) → Set (suc ℓ ⊔ a)
FamilyOfSet {ℓ} A = Pred (Pred A ℓ) ℓ

infixl 1 _,_
_,_ = _×_

∅ : ∀{ℓ} {A : Set a} → Pred A ℓ
∅ _ = Lift ⊥

U₀ : ∀{ℓ} {A : Set a} → Pred A ℓ
U₀ _ = Lift ⊤

module Axioms {ℓ} where
  postulate
    ≡-extensionality : Extensionality a (suc ℓ)
    ⇔-≡ : {A : Set a} {P Q : Pred A ℓ} → (∀ z → P z ⇔ Q z) → (∀ z → P z ≡ Q z)

    union : {A : Set _} (X : FamilyOfSet {ℓ} A) → ∃ B ∶ (∀ t → (t ∈ B) ≡ (∃ x ∶ x ∈ X , t ∈ x))

  extensionality : {A : Set _} {x y : Subset {_} A} → (∀ z → (z ∈ x) ⇔ (z ∈ y)) → x ≡ y
  extensionality iff = ≡-extensionality (⇔-≡ iff)

Union : ∀{a b ℓ} {A : Set a} {I : Set b} → (I → Pred A ℓ) → Pred A _
Union F = [ a ∣ ∃ i ∶ a ∈ F i ]

UnionOf : ∀{ℓ} {A : Set a} → FamilyOfSet {ℓ} A → Pred A _
UnionOf P = proj₁ (Axioms.union P)

Intersect : ∀{a b ℓ} {A : Set a} {I : Set b} → (I → Pred A ℓ) → Pred A _
Intersect F = [ a ∣ (∀ i → a ∈ F i) ]

module Set-lemmas {A : Set a} where
  Union-⊆ : ∀{ℓ} {X : FamilyOfSet {ℓ} A} → (U : Subset A) → U ∈ X → U ⊆ UnionOf X
  Union-⊆ U U∈X x = {!!}
