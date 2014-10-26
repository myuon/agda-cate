module Sets.Sets.Choice where

open import Data.Product
open import Sets.Sets.Basic
open import Sets.Sets.Extensionality
open import Sets.Sets.Union

postulate
  choice : ∀ X → ∅ ∉ X → ∃ \(f : X ⟶ ⋃ X) → ∀ A → ⟨ f ⟩ A ∈ A

