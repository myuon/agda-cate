module Sets.Topology.Topology where

open import Level
open import Function
open import Data.Empty
open import Data.Product
open import Relation.Binary

open import Sets.Sets

record TopSpace : Set₁ where
  field
    set : Set
    Open : Set
  
  field
    OpenFamily : Open ∈ P[ P[ set ] ]
    ∅-open : ∅ ∈ Open
    all-open : set ∈ Open
    ⋃-open : {F : Set} → F ⊆ Open → ⋃ F ∈ Open
    ∩-open : {A B : Set} → A ∈ Open → B ∈ Open → A ∩ B ∈ Open

Discrete : (X : Set) → TopSpace
Discrete X = record
  { set = X
  ; Open = P[ X ]

  ; OpenFamily = ⊆-∈-power (\_ → id)
  ; ∅-open = ⊆-∈-power ∅-⊆
  ; all-open = ⊆-∈-power (\_ → id)
  ; ⋃-open = \{F} F⊆P[X] → ⊆-∈-power (⊆-≡-reflˡ ⋃-power $ ⋃-cong F⊆P[X])
  ; ∩-open = \{A} {B} A∈P[X] B∈P[X] → ⊆-∈-power (\x x∈A∩B → ∈-≡ ⋃-power (⋃-∈-⊆ A∈P[X] x $ ∩-⊆ˡ x x∈A∩B))
  }

Indiscrete : (X : Set) → TopSpace
Indiscrete X = record
  { set = X
  ; Open = [ ∅ , X ]

  ; OpenFamily = ⊆-∈-power (\Y Y∈pair → ∈-P[X] Y $ in-[A,B] Y Y∈pair)
  ; ∅-open = A∈[A,B]
  ; all-open = B∈[A,B]
  ; ⋃-open = ∪-lemma
  ; ∩-open = \{A} {B} A:open B:open → proj⃖ (proj₂ (∃-pairing ∅ X) (A ∩ B)) $ ∩-lemma (in-[A,B] A A:open) (in-[A,B] B B:open)
  }
  where
    open paring-lemmas
    open IsPartialOrder ⊆-isPartialOrder

    ∈-P[X] : ∀ Y → (Y ≡ ∅) ∨ (Y ≡ X) → Y ∈ P[ X ]
    ∈-P[X] Y (∨-left Y≡∅) = ⊆-∈-power (\z z∈Y → ∅-⊆ z $ ∈-≡ Y≡∅ z∈Y)
    ∈-P[X] Y (∨-right Y≡X) = ⊆-∈-power (\z z∈Y → ∈-≡ Y≡X z∈Y)

    ∩-lemma : ∀{A B} → (A ≡ ∅) ∨ (A ≡ X) → (B ≡ ∅) ∨ (B ≡ X) → (A ∩ B ≡ ∅) ∨ (A ∩ B ≡ X)
    ∩-lemma {A} {B} _ (∨-left B≡∅) = ∨-left $ antisym (\X X∈A∩B → proj⃗ (app-extensionality ∩-∅ X) (∧-∩ X $ ∧-→-reflˡ (∈-≡ B≡∅) $ ∩-∧ X X∈A∩B)) ∅-⊆
    ∩-lemma {A} {B} (∨-left A≡∅) _ = ∨-left $ antisym (\X X∈A∩B → proj⃗ (app-extensionality ∩-∅ X) (∧-∩ X $ ∧-→-reflˡ (∈-≡ A≡∅) $ proj⃗ (∧-comm _ _) $ ∩-∧ X X∈A∩B)) ∅-⊆
    ∩-lemma {A} {B} (∨-right A≡X) (∨-right B≡X) = ∨-right $ ⇔-extensionality $ \Y →
      (\Y∈A∩B → ∈-≡ (≡-trans (∩-≡ A≡X B≡X) ∩-idempotent) $ Y∈A∩B) ,
      (\Y∈X → ∈-≡ (≡-sym $ ≡-trans (∩-≡ A≡X B≡X) ∩-idempotent) Y∈X)

    ∪-lemma : {F : Set} → F ⊆ [ ∅ , X ] → ⋃ F ∈ [ ∅ , X ]
    ∪-lemma {F} F⊆[∅,X] = proj⃖ (proj₂ (∃-pairing ∅ X) (⋃ F)) $ ⋃F≡∅∨X X∈F∨X∉F
      where
        X∈F∨X∉F : (X ∈ F) ∨ (X ∉ F)
        X∈F∨X∉F = non-datur

        lemma : ∀ Y Z → X ∉ F → (Z ∈ F) ∧ (Y ∈ Z) → (Z ≡ ∅) ∨ (Z ≡ X) → Y ∈ ∅
        lemma Y Z _ and (∨-left Z≡∅) = ∈-≡ Z≡∅ (∧-right and)
        lemma Y Z X∉F and (∨-right Z≡X) = ⊥-elim $ X∉F $ ≡-∈ Z≡X (∧-left and)

        ⋃F≡∅∨X : (X ∈ F) ∨ (X ∉ F) → (⋃ F ≡ ∅) ∨ (⋃ F ≡ X)
        ⋃F≡∅∨X (∨-left X∈F) = ∨-right $ antisym
          (⊆-≡-reflˡ ∪-lemmas.∪-∅ $ ⊆-≡-reflˡ (∪-lemmas.∪-comm) $ ⋃-cong F⊆[∅,X]) 
          (⊆-≡-reflʳ ⋃-singleton $ ⋃-cong $ ∈-singleton-⊆ X∈F)
        ⋃F≡∅∨X (∨-right X∉F) = ∨-left $ antisym
          (\Y Y∈∪F → let ex = proj⃗ (proj₂ (∃-union F) Y) Y∈∪F
                         Z = proj₁ ex ; Z∈F∧Y∈Z = proj₂ ex in
              lemma Y Z X∉F Z∈F∧Y∈Z $ in-[A,B] Z $ F⊆[∅,X] Z (∧-left Z∈F∧Y∈Z)
          ) ∅-⊆
