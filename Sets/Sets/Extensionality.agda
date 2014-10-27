module Sets.Sets.Extensionality where

open import Level
open import Function
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _,_ ; ∃)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Sets.Sets.Basic

postulate
  extensionality : {A B : Set} → A ≡ B ⇔ Lift {_} {zero} (∀ x → (x ∈ A ⇔ x ∈ B))

⇔-extensionality : {A B : Set} → (∀ x → (x ∈ A ⇔ x ∈ B)) → A ≡ B
⇔-extensionality f = proj⃖ extensionality (lift f)

app-extensionality : {A B : Set} → A ≡ B → ∀ x → (x ∈ A ⇔ x ∈ B)
app-extensionality eq = lower (proj⃗ extensionality eq)

replace-≡ : {A B : Set} → A ≡ B → ∀ x → (x ∈ A ⇔ x ∈ B)
replace-≡ = app-extensionality

satisfy-≡ : {A B : Set} → (∀ x → (x ∈ A ⇔ x ∈ B)) → A ≡ B
satisfy-≡ = ⇔-extensionality

module ⊆-lemmas where
  ⊆-refl : {A : Set} → A ⊆ A
  ⊆-refl = \_ → id

  ⊆-cong : {A B C D : Set} → A ≡ B → C ≡ D → A ⊆ C → B ⊆ D
  ⊆-cong A≡B C≡D A⊆C rewrite A≡B | C≡D = A⊆C

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
      refl-≡⇒⊆ i≡j x x∈i rewrite i≡j = x∈i

      trans-⊆ : {A B C : Set} → A ⊆ B → B ⊆ C → A ⊆ C
      trans-⊆ A⊆B B⊆C x x∈A = B⊆C x (A⊆B x x∈A)

      antisym-⊆ : {A B : Set} → A ⊆ B → B ⊆ A → A ≡ B
      antisym-⊆ A⊆B B⊆A = proj⃖ extensionality $ lift $ \x → (A⊆B x , B⊆A x)
  open IsPartialOrder ⊆-isPartialOrder
    using ()
    renaming (antisym to ⊆-antisym ; reflexive to ⊆-reflexive ; trans to ⊆-trans)
    public
open ⊆-lemmas public

∅ : Set
∅ = ⊥

∃-empty-prop : Set₁
∃-empty-prop = ∃ \(A : Set) → (∀ x → ¬ (x ∈ A))

∃-empty : ∃-empty-prop
∃-empty = ⊥ , elem-∈

∅-uniqueness : (P : ∃-empty-prop) → (proj₁ P) ≡ ⊥
∅-uniqueness P = proj⃖ extensionality (lift \x → (\x∈projP → ⊥-elim $ proj₂ P x x∈projP) , \x∈⊥ → ⊥-elim (elem-∈ x x∈⊥))

module ∅-lemmas where
  ∅⇔⊆ : ∃-empty-prop ⇔ (∀(A : Set) → ⊥ ⊆ A)
  ∅⇔⊆ = lemma , \_ → ∃-empty where
    lemma : ∃-empty-prop → (A : Set) → ⊥ ⊆ A
    lemma P A x x∈⊥ = ⊥-elim $ elem-∈ x x∈⊥

  ∅-⊆ : {A : Set} → ∅ ⊆ A
  ∅-⊆ {A} = proj⃗ ∅⇔⊆ ∃-empty A

  ⊆-∅ : {A : Set} → A ⊆ ∅ → A ≡ ∅
  ⊆-∅ A⊆∅ = ⊆-antisym A⊆∅ ∅-⊆
open ∅-lemmas public

-- ¬∀⟶∃¬ : ∀ n {p} (P : Fin n → Set p) → Decidable P →
--        ¬ (∀ i → P i) → ∃ λ i → ¬ P i
