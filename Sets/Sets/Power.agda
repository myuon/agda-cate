module Sets.Sets.Power where

open import Level
open import Function
open import Data.Empty
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _,_ ; ∃)
open import Relation.Binary
open import Relation.Nullary
open import Sets.Sets.Basic
open import Sets.Sets.Extensionality
open import Sets.Sets.Union

postulate
  powerset : (A : Set) → ∃ \B → ∀ X → X ∈ B ⇔ X ⊆ A

P[_] : Set → Set
P[ A ] = proj₁ (powerset A)

module power-lemmas where
  ⊆-∈-power : {X A : Set} → A ⊆ X → A ∈ P[ X ]
  ⊆-∈-power {X} {A} = proj⃖ (proj₂ (powerset X) A)

  ∈-⊆-power : {X A : Set} → A ∈ P[ X ] → A ⊆ X
  ∈-⊆-power {X} {A} = proj⃗ (proj₂ (powerset X) A)

  ⋃-power : {X : Set} → ⋃ P[ X ] ≡ X
  ⋃-power {X} = antisym
    (\Y Y∈∪P → let ex = y∈P[X] Y Y∈∪P in y∈X Y (proj₁ ex) (proj₂ ex))
    (\Y Y∈X → proj⃖ (proj₂ (∃-union P[ X ]) Y) $ X , (⊆-∈-power (\_ → id)) , Y∈X)
    where
      open IsPartialOrder ⊆-isPartialOrder public

      y∈P[X] : ∀ Y → Y ∈ ⋃ P[ X ] → ∃ \Z → (Z ∈ P[ X ]) ∧ (Y ∈ Z)
      y∈P[X] Y Y∈∪P = (proj⃗ (proj₂ (∃-union P[ X ]) Y)) Y∈∪P

      y∈X : ∀ Y Z → (Z ∈ P[ X ]) ∧ (Y ∈ Z) → Y ∈ X
      y∈X Y Z and = ∈-⊆-power (∧-left and) Y (∧-right and)
open power-lemmas public
