module Sets.Sets.Union where

open import Level
open import Function
open import Data.Empty
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _,_ ; ∃)
open import Sets.Sets.Basic
open import Sets.Sets.Extensionality
open import Sets.Sets.Pairing

postulate
  ∃-union : (A : Set) → ∃ \(B : Set) → ∀ X → X ∈ B ⇔ (∃ \C → (C ∈ A) ∧ (X ∈ C))

infixr 6 _∪_
_∪_ : (A B : Set) → Set
A ∪ B = proj₁ (∃-union [ A , B ])

⋃_ : (F : Set) → Set
⋃ F = proj₁ (∃-union F)

replace-in-union : {A : Set} → ∀ X → X ∈ ⋃ A → ∃ \C → (C ∈ A) ∧ (X ∈ C)
replace-in-union {A} X X∈B = proj⃗ (proj₂ (∃-union A) X) X∈B

satisfy-in-union : {A : Set} → ∀ X → (∃ \C → (C ∈ A) ∧ (X ∈ C)) → X ∈ ⋃ A
satisfy-in-union {A} X cond = proj⃖ (proj₂ (∃-union A) X) cond

⋃-∈-⊆ : {F X : Set} → X ∈ F → X ⊆ ⋃ F
⋃-∈-⊆ {F} {X} X∈⋃F x x∈X = proj⃖ (proj₂ (∃-union F) x) $ X , (X∈⋃F , x∈X)

⋃-⊆-∀ : {F Y : Set} → (∀ X → X ∈ F → X ⊆ Y) → ⋃ F ⊆ Y
⋃-⊆-∀ f x x∈⋃F = let ex = replace-in-union x x∈⋃F ; X = proj₁ ex in
  (f X (∧-left $ proj₂ ex)) x (∧-right $ proj₂ ex)

⋃-cong : {A B : Set} → A ⊆ B → ⋃ A ⊆ ⋃ B
⋃-cong {A} {B} A⊆B x x∈⋃A = proj⃖ (proj₂ (∃-union B) x) $ y , (∧-→-refl (A⊆B y) y∈A∧x∈y)
  where
    y = proj₁ (proj⃗ (proj₂ (∃-union A) x) x∈⋃A)
    y∈A∧x∈y = proj₂ (proj⃗ (proj₂ (∃-union A) x) x∈⋃A)

    ∧-→-refl : ∀{f} {A B C : Set f} → (A → C) → A ∧ B → C ∧ B
    ∧-→-refl f (y , refl) = f y , refl

∪⇔∨ : {A B : Set} → ∀ X → X ∈ A ∪ B ⇔ (X ∈ A) ∨ (X ∈ B)
∪⇔∨ {A} {B} X = lemma ∘ X∈A , X∈A∪B
  where
    X∈A : X ∈ A ∪ B → ∃ \C → ((C ∈ [ A , B ]) ∧ (X ∈ C))
    X∈A X∈A∪B = proj⃗ (proj₂ (∃-union [ A , B ]) X) X∈A∪B

    lemma : (p : ∃ \C → ((C ∈ [ A , B ]) ∧ (X ∈ C))) → (X ∈ A) ∨ (X ∈ B)
    lemma p = let C∈[A,B] = ∧-left $ proj₂ p ; X∈C = ∧-right $ proj₂ p in
      X∈A∨B (proj⃗ (proj₂ (∃-pairing A B) (proj₁ p)) C∈[A,B]) X∈C
      where
        X∈A∨B : (proj₁ p ≡ A) ∨ (proj₁ p ≡ B) → (X ∈ proj₁ p) → (X ∈ A) ∨ (X ∈ B)
        X∈A∨B (∨-left C≡A) X∈C = ∨-left $ ∈-≡ C≡A X∈C
        X∈A∨B (∨-right C≡B) X∈C = ∨-right $ ∈-≡ C≡B X∈C

    X∈A∪B : (X ∈ A) ∨ (X ∈ B) → X ∈ A ∪ B
    X∈A∪B (∨-left X∈A) = proj⃖ (proj₂ (∃-union [ A , B ]) X) $ A , (A∈[A,B] , X∈A)
    X∈A∪B (∨-right X∈B) = proj⃖ (proj₂ (∃-union [ A , B ]) X) $ B , (B∈[A,B] , X∈B)

∪-∨ : {A B : Set} → ∀ X → X ∈ A ∪ B → (X ∈ A) ∨ (X ∈ B)
∪-∨ X = proj⃗ $ ∪⇔∨ X

∨-∪ : {A B : Set} → ∀ X → (X ∈ A) ∨ (X ∈ B) → X ∈ A ∪ B
∨-∪ X = proj⃖ $ ∪⇔∨ X

⋃-singleton : {X : Set} → ⋃ singleton X ≡ X
⋃-singleton = ⇔-extensionality $ \Y →
  (\Y∈∪[X] → ∨-unrefl $ ∪-∨ Y Y∈∪[X]) ,
  (\Y∈X → ∨-∪ Y $ ∨-left $ Y∈X)

module ∪-lemmas where
  ∪-idempotent : {A : Set} → A ∪ A ≡ A
  ∪-idempotent {A} = ⇔-extensionality $ \X →
    (\X∈A∪A → ∨-unrefl $ ∪-∨ X X∈A∪A) ,
    (\X∈A → ∨-∪ X $ ∨-left X∈A)

  ∪-comm : {A B : Set} → A ∪ B ≡ B ∪ A
  ∪-comm {A} {B} = ⇔-extensionality $ \X →
    (\X∈A∪B → ∨-∪ X $ proj⃗ (∨-comm _ _) $ ∪-∨ X X∈A∪B) ,
    (\X∈B∪A → ∨-∪ X $ proj⃗ (∨-comm _ _) $ ∪-∨ X X∈B∪A)

  ∪-assoc : {A B C : Set} → A ∪ (B ∪ C) ≡ (A ∪ B) ∪ C
  ∪-assoc = ⇔-extensionality $ \X →
    (\X∈A∪[B∪C] → ∨-∪ X $ ∨-→-reflʳ (∨-∪ X) $ proj⃖ (∨-assoc _ _ _) $ ∨-→-reflˡ (∪-∨ X) $ ∪-∨ X X∈A∪[B∪C]) ,
    (\X∈[A∪B]∪C → ∨-∪ X $ ∨-→-reflˡ (∨-∪ X) $ proj⃗ (∨-assoc _ _ _) $ ∨-→-reflʳ (∪-∨ X) $ ∪-∨ X X∈[A∪B]∪C)

  ⊆⇔∪ : {A B : Set} → A ⊆ B ⇔ A ∪ B ≡ B
  ⊆⇔∪ {A} {B} =
    (\A⊆B → ⇔-extensionality $ \X → (\X∈A∪B → lemma X A⊆B $ ∪-∨ X X∈A∪B) , \X∈B → ∨-∪ X $ ∨-right X∈B) ,
    (\eq Y Y∈A → Y∈B Y Y∈A $ iff eq Y)
    where
      lemma : ∀ X → A ⊆ B → (X ∈ A) ∨ (X ∈ B) → X ∈ B
      lemma X A⊆B (∨-left X∈A) = A⊆B X X∈A
      lemma _ _ (∨-right X∈B) = X∈B

      iff : A ∪ B ≡ B → ∀ Y → (Y ∈ A ∪ B ⇔ Y ∈ B)
      iff eq X = app-extensionality eq X

      Y∈B : ∀ Y → Y ∈ A → (Y ∈ A ∪ B ⇔ Y ∈ B) → Y ∈ B
      Y∈B Y Y∈A eq = proj⃗ eq $ ∨-∪ Y $ ∨-left Y∈A

  ∪-∅ : {A : Set} → A ∪ ∅ ≡ A
  ∪-∅ {A} = ⇔-extensionality $ \X → (\X∈A∪∅ → lemma X $ ∪-∨ X X∈A∪∅) , (\X∈A → ∨-∪ X $ ∨-left X∈A)
    where
      lemma : ∀ X → (X ∈ A) ∨ (X ∈ ∅) → X ∈ A
      lemma X (∨-left X∈A) = X∈A
      lemma X (∨-right X∈∅) = ⊥-elim $ elem-∈ X X∈∅

_⁺ : (A : Set) → Set
A ⁺ = A ∪ (singleton A)

postulate
  infinite : ∃ \A → (∅ ∈ A) ∧ (∀ X → X ∈ A → X ⁺ ∈ A)
