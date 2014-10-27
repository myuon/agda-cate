module Sets.Sets where

open import Function
open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation

open import Sets.Sets.Basic public
open import Sets.Sets.Extensionality public
open import Sets.Sets.Pairing public
open import Sets.Sets.Union public
open import Sets.Sets.Separation public
open import Sets.Sets.Power public
open import Sets.Sets.Natural public
open import Sets.Sets.Choice public
open import Sets.Sets.NonDatur public

∅-∃ : ∀ {A : Set} → A ≢ ∅ → ∃ \x → x ∈ A
∅-∃ {A} np = map id ¬¬-elim $ ¬∀⇒∃¬ $ contraposition lemma $ np
  where
  lemma : ∀ {A : Set} → (∀ x → ¬ (x ∈ A)) → A ≡ ∅
  lemma {A} np = ∅-uniqueness $ A , np

postulate
  regularity : ∀ X → X ≢ ∅ → ∃ \y → y ∈ X → y ∩ X ≡ ∅

  replacement : ∀{P : Set → Set → Set} → (∀ x y z → (P x y ∧ P x z → y ≡ z)) → ∀ X → ∃ \A → ∀ y → (y ∈ A ⇔ ∃ \x → x ∈ X → P x y)

private
  prop-1-4 : {A : Set} → let B = ⟦ X ∈ A ∣ X ∉ X ⟧ in B ∉ A
  prop-1-4 {A} p = ¬Q∧Q p non-datur
    where
      B = ⟦ X ∈ A ∣ X ∉ X ⟧
      P = B ∈ A
      Q = B ∈ B
      prop = proj₂ (separation A (\X → X ∉ X))

      lemma : P → (¬ Q) ⇔ Q
      lemma P = (\notQ → proj⃖ (prop B) $ P , notQ)
              , (\q → proj⃖ (⇔-contraposition (prop B)) $ \and → ∧-right and q)

      ¬Q∧Q : P → (Q ∨ (¬ Q)) → ⊥
      ¬Q∧Q p (∨-left q) = proj⃖ (lemma p) q $ q
      ¬Q∧Q p (∨-right nq) = nq $ proj⃗ (lemma p) nq

  cor-1-4 : (A : Set) → ∃ \B → B ∉ A
  cor-1-4 A = ⟦ X ∈ A ∣ X ∉ X ⟧ , prop-1-4
