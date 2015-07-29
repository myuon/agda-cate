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

LiftSetoid : ∀ {a b ℓ ℓ′} (A : Setoid a ℓ) → Setoid (a ⊔ b) (ℓ ⊔ ℓ′)
LiftSetoid {a} {b} {ℓ} {ℓ′} A = record {
  Carrier = Lift {a} {b} (Carrier A) ;
  _≈_ = λ x x₁ → Lift {ℓ} {ℓ′} (eqSetoid A (lower x) (lower x₁)) ;
  isEquivalence = record {
    refl = lift (refl A) ;
    sym = λ x → lift (sym A (lower x)) ;
    trans = λ x x₁ → lift (trans A (lower x) (lower x₁)) } }

liftMap : {c₀ c₀′ d ℓ ℓ′ ℓ″ : Level} {A : Setoid c₀ ℓ} {B : Setoid c₀′ ℓ′} → (f : Map.Map A B) → Map.Map (LiftSetoid {_} {c₀ ⊔ d} {_} {ℓ ⊔ ℓ″} A) (LiftSetoid {_} {c₀′ ⊔ d} {_} {ℓ′ ⊔ ℓ″} B)
liftMap f = record {
  mapping = λ x → lift (Map.mapping f (lower x)) ;
  preserveEq = λ x≈y → lift (Map.preserveEq f (lower x≈y)) }

lowerMap : {c₀ c₀′ d ℓ ℓ′ ℓ″ : Level} {A : Setoid c₀ ℓ} {B : Setoid c₀′ ℓ′} → (f : Map.Map (LiftSetoid {_} {c₀ ⊔ d} {_} {ℓ ⊔ ℓ″} A) (LiftSetoid {_} {c₀′ ⊔ d} {_} {ℓ′ ⊔ ℓ″} B)) → Map.Map A B
lowerMap f = record {
  mapping = λ x → lower (Map.mapping f (lift x)) ;
  preserveEq = λ x≈y → lower (Map.preserveEq f (lift x≈y)) }

