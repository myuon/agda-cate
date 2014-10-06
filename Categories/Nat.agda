module Categories.Nat where

open import Level
open import Categories.Category
open import Categories.Functor

open Category
open Functor

record Nat
  {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′}
  (F G : Functor C D)
  : Set (suc (C₀ ⊔ C₁ ⊔ ℓ ⊔ D₀ ⊔ D₁ ⊔ ℓ′)) where
  field
    component : (r : Obj C) → D [ fobj F r ~> fobj G r ]

  field
    naturality : {a b : Obj C} {f : C [ a ~> b ]}
      → D [ D [ component b ∘ fmap F f ] ≈ D [ fmap G f ∘ component a ] ]
