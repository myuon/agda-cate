module Sets.Sets.Replacement where

open import Level
open import Function
open import Data.Empty
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _,_ ; ∃)
open import Relation.Nullary
open import Sets.Sets.Basic
open import Sets.Sets.Extensionality

postulate
  replacement : (A : Set) → (P : Set → Set₁) → ∃ \B → ∀ x → x ∈ B ⇔ (x ∈ A) ∧ P x

cond-set : (A : Set) → (∀ X → Set₁) → Set
cond-set A f = proj₁ (replacement A f)

syntax cond-set A (\X → P) = ⟦ X ∈ A ∣ P ⟧

prop-1-4 : {A : Set} → let B = ⟦ X ∈ A ∣ X ∉ X ⟧ in B ∉ A
prop-1-4 {A} p = ¬Q∧Q p non-datur
  where
    B = ⟦ X ∈ A ∣ X ∉ X ⟧
    P = B ∈ A
    Q = B ∈ B
    prop = proj₂ (replacement A (\X → X ∉ X))

    lemma : P → (¬ Q) ⇔ Q
    lemma P = (\notQ → proj⃖ (prop B) $ P , notQ)
            , (\q → proj⃖ (⇔-contraposition (prop B)) $ \and → ∧-right and q)

    ¬Q∧Q : P → (Q ∨ (¬ Q)) → ⊥
    ¬Q∧Q p (∨-left q) = proj⃖ (lemma p) q $ q
    ¬Q∧Q p (∨-right nq) = nq $ proj⃗ (lemma p) nq

cor-1-4 : (A : Set) → ∃ \B → B ∉ A
cor-1-4 A = ⟦ X ∈ A ∣ X ∉ X ⟧ , prop-1-4

infixr 7 _∩_
_∩_ : (A B : Set) → Set
A ∩ B = ⟦ X ∈ A ∣ X ∈ B ⟧

module ∩-Hetero where
  ∩⇔∧ : {A B : Set} → ∀ X → X ∈ A ∩ B ⇔ (X ∈ A) ∧ (X ∈ B)
  ∩⇔∧ {A} {B} X = X∈A∧X∈B , X∈A∩B
    where
      X∈A∧X∈B : X ∈ A ∩ B → (X ∈ A) ∧ (X ∈ B)
      X∈A∧X∈B X∈A∩B = proj⃗ (proj₂ (replacement A $ \X → X ∈ B) X) X∈A∩B

      X∈A∩B : (X ∈ A) ∧ (X ∈ B) → X ∈ A ∩ B
      X∈A∩B and = proj⃖ (proj₂ (replacement A $ \X → X ∈ B) X) and

  ∩-∧ : {A B : Set} → ∀ X → X ∈ A ∩ B → (X ∈ A) ∧ (X ∈ B)
  ∩-∧ X = proj⃗ (∩⇔∧ X)

  ∧-∩ : {A B : Set} → ∀ X → (X ∈ A) ∧ (X ∈ B) → X ∈ A ∩ B
  ∧-∩ X = proj⃖ (∩⇔∧ X)

  ∩-⊆ˡ : {A B : Set} → A ∩ B ⊆ A
  ∩-⊆ˡ x x∈A∩B = ∧-left $ ∩-∧ x x∈A∩B

  ∩-⊆ʳ : {A B : Set} → A ∩ B ⊆ B
  ∩-⊆ʳ x x∈A∩B = ∧-right $ ∩-∧ x x∈A∩B
open ∩-Hetero public

module ∩-lemmas where
  ∩-idempotent : {A : Set} → A ∩ A ≡ A
  ∩-idempotent = ⇔-extensionality $ \X →
    (\X∈A∩A → ∧-left $ ∩-∧ X X∈A∩A) ,
    (\X∈A → ∧-∩ X $ ∧-refl X∈A)

  ∩-comm : {A B : Set} → A ∩ B ≡ B ∩ A
  ∩-comm = ⇔-extensionality $ \X → (∧-∩ X ∘ proj⃗ (∧-comm _ _) ∘ ∩-∧ X) , (∧-∩ X ∘ proj⃗ (∧-comm _ _) ∘ ∩-∧ X)
--    ∩-assoc : {A B C : Set} → (A ∩ B) ∩ C ≡ A ∩ (B ∩ C)
  ⊆⇔∩ : {A B : Set} → A ⊆ B ⇔ A ∩ B ≡ A
  ⊆⇔∩ = (\A⊆B → ⇔-extensionality $ \X →
    (\X∈A∩B → ∧-left $ ∩-∧ X X∈A∩B) , (\X∈A → ∧-∩ X $ X∈A , A⊆B X X∈A)) ,
    (\eq X X∈A → ∩-⊆ʳ X $ proj⃖ (app-extensionality eq X) X∈A)

  ∩-∅ : {A : Set} → A ∩ ∅ ≡ ∅
  ∩-∅ {A} = ⇔-extensionality $ \X →
    (\X∈A∩∅ → ∧-right $ ∩-∧ X X∈A∩∅) ,
    (\X∈∅ → ∧-∩ X $ (∅-⊆ A X X∈∅) , X∈∅)

--    distributive law, complement
open ∩-lemmas public
