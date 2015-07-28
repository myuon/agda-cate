module Basic where

open import Level
open import Data.Product
open import Relation.Binary
open Setoid renaming (_≈_ to eqSetoid)

module Map where
  record Map {c₀ c₀′ ℓ ℓ′ : Level} (A : Setoid c₀ ℓ) (B : Setoid c₀′ ℓ′) : Set (suc (c₀ ⊔ ℓ ⊔ c₀′ ⊔ ℓ′)) where
    field
      mapping : Carrier A → Carrier B
      preserveEq : {x y : Carrier A} → (eqSetoid A x y) → eqSetoid B (mapping x) (mapping y)

  open Map public

  equality : {c₀ ℓ : Level} {A B : Setoid c₀ ℓ} (f g : Map A B) → Set _
  equality {A = A} {B = B} f g = ∀(x : Carrier A) → eqSetoid B (mapping f x) (mapping g x)

  compose : {c₀ ℓ : Level} {A B C : Setoid c₀ ℓ} (f : Map B C) (g : Map A B) → Map A C
  compose {C = C} f g = record {
    mapping = λ x → mapping f (mapping g x);
    preserveEq = λ x₁ → (preserveEq f (preserveEq g x₁)) }

  identity : {c₀ ℓ : Level} {A : Setoid c₀ ℓ} → Map A A
  identity = record { mapping = λ x → x ; preserveEq = λ x₁ → x₁ }

  subst : ∀{c₀ ℓ} {A B : Setoid c₀ ℓ} {f g : Map A B} (a : Carrier A) → equality f g → eqSetoid B (mapping f a) (mapping g a)
  subst a eq = eq a
