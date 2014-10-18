module Sets.Sets.Extensionality where

open import Level
open import Function
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _,_ ; ∃)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Sets.Sets.Basic

infix 4 _∈_ _∉_

postulate
  _∈_ : Set → Set → Set₁
  elem-∈ : {A : Set} → ∀ x → x ∈ A → A
  ≡-∈ : {A X Y : Set} → X ≡ Y → X ∈ A → Y ∈ A
  
  extensionality : {A B : Set} → A ≡ B ⇔ Lift {_} {zero} (∀ x → (x ∈ A ⇔ x ∈ B))

_∉_ : Set → Set → Set₁
X ∉ A = X ∈ A → ⊥

⇔-extensionality : {A B : Set} → (∀ X → (X ∈ A ⇔ X ∈ B)) → A ≡ B
⇔-extensionality f = proj⃖ extensionality (lift f)

app-extensionality : {A B : Set} → A ≡ B → ∀ X → (X ∈ A ⇔ X ∈ B)
app-extensionality eq = lower (proj⃗ extensionality eq)

infix 5 _⊆_ _⊊_
_⊆_ : Set → Set → Set₁
A ⊆ B = ∀ x → x ∈ A → x ∈ B

_⊊_ : Set → Set → Set₁
A ⊊ B = (A ≢ B) ∧ (A ⊆ B)

module extensionality-Hetero where
  ∈-≡ : {A B : Set} → {X : Set} → A ≡ B → X ∈ A → X ∈ B
  ∈-≡ {X = X} A≡B X∈A = proj⃗ (app-extensionality A≡B X) X∈A

  ⊆-≡-reflˡ : {A B C : Set} → B ≡ C → A ⊆ B → A ⊆ C
  ⊆-≡-reflˡ B≡C A⊆B x x∈A = proj⃗ (app-extensionality B≡C x) $ A⊆B x x∈A

  ⊆-≡-reflʳ : {A B C : Set} → A ≡ C → A ⊆ B → C ⊆ B
  ⊆-≡-reflʳ A≡C A⊆B x x∈C = A⊆B x $ proj⃖ (app-extensionality A≡C x) x∈C
open extensionality-Hetero public

module ⊆-lemmas where
  ⊆-isPartialOrder : IsPartialOrder _≡_ _⊆_
  ⊆-isPartialOrder = record
    { isPreorder = record
      { isEquivalence = ≡-isEquivalence
      ; reflexive = refl-≡⇒⊆
      ; trans = trans-⊆ }
    ; antisym = antisym-⊆ }
    where
      open IsPartialOrder

      refl-≡⇒⊆ : ∀{i j} → i ≡ j → i ⊆ j
      refl-≡⇒⊆ i≡j x = proj⃗ (lower (proj⃗ extensionality i≡j) x)

      trans-⊆ : {A B C : Set} → A ⊆ B → B ⊆ C → A ⊆ C
      trans-⊆ A⊆B B⊆C x x∈A = B⊆C x (A⊆B x x∈A)

      antisym-⊆ : {A B : Set} → A ⊆ B → B ⊆ A → A ≡ B
      antisym-⊆ A⊆B B⊆A = proj⃖ extensionality (lift (\x → A⊆B x , B⊆A x))
--  open IsPartialOrder ⊆-isPartialOrder public
open ⊆-lemmas public

∅ : Set
∅ = ⊥

∃-empty-prop : Set₁
∃-empty-prop = ∃ \(A : Set) → (∀ x → ¬ (x ∈ A))

∃-empty : ∃-empty-prop
∃-empty = ⊥ , elem-∈

∅-uniqueness : (P : ∃-empty-prop) → (proj₁ P) ≡ ⊥
∅-uniqueness P = proj⃖ extensionality (lift \x → (\x∈projP → ⊥-elim (proj₂ P x x∈projP)) , \x∈⊥ → ⊥-elim (elem-∈ x x∈⊥))

module ∅-Hetero where
  ∅⇔⊆ : ∃-empty-prop ⇔ (∀(A : Set) → ⊥ ⊆ A)
  ∅⇔⊆ = lemma , \_ → ∃-empty where
    lemma : ∃-empty-prop → (A : Set) → ⊥ ⊆ A
    lemma P A x x∈⊥ = ⊥-elim (elem-∈ x x∈⊥)

  ∅-⊆ : (A : Set) → ∅ ⊆ A
  ∅-⊆ = proj⃗ ∅⇔⊆ ∃-empty
open ∅-Hetero public
