module Categories.Functor where

open import Level
open import Categories.Category

open Category

record Functor
  {C₀ C₁ ℓ D₀ D₁ ℓ′ : Level}
  (C : Category C₀ C₁ ℓ)
  (D : Category D₀ D₁ ℓ′)
  : Set (suc (C₀ ⊔ C₁ ⊔ ℓ ⊔ D₀ ⊔ D₁ ⊔ ℓ′)) where
  field
    fobj : Obj C → Obj D
    fmap : {a b : Obj C} → C [ a ~> b ] → D [ fobj a ~> fobj b ]

  field
    ≈-cong : {a b : Obj C} {f g : C [ a ~> b ]}
      → C [ f ≈ g ] → D [ fmap f ≈ fmap g ]
    preserveId : {a : Obj C} → D [ fmap (id C {a}) ≈ id D {fobj a} ]
    covariant : {a b c : Obj C} {f : C [ a ~> b ]} {g : C [ b ~> c ]}
      → D [ fmap (C [ g ∘ f ]) ≈ D [ fmap g ∘ fmap f ] ]

open Functor


