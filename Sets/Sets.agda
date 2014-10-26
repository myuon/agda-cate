module Sets.Sets where

open import Data.Product
open import Relation.Nullary

open import Sets.Sets.Basic public
open import Sets.Sets.Extensionality public
open import Sets.Sets.Pairing public
open import Sets.Sets.Union public
open import Sets.Sets.Separation public
open import Sets.Sets.Power public
open import Sets.Sets.Natural public
open import Sets.Sets.Choice public
open import Sets.Sets.NonDatur public

postulate
  regularity : ∀ X → X ≢ ∅ → ∃ \y → y ∈ X → y ∩ X ≡ ∅

  replacement : ∀{P : Set → Set → Set} → (∀ x y z → (P x y ∧ P x z → y ≡ z)) → ∀ X → ∃ \A → ∀ y → (y ∈ A ⇔ ∃ \x → x ∈ X → P x y)

