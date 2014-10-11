module Categories.Functor where

open import Level
open import Categories.Category
open import Categories.Reasoning

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

_∘F_ : {C₀ C₁ ℓ D₀ D₁ ℓ′ E₀ E₁ ℓ″ : Level}
  {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {E : Category E₀ E₁ ℓ″}
  → Functor D E → Functor C D → Functor C E
_∘F_ {C = C} {D = D} {E = E} F G = record
  { fobj = \x → fobj F (fobj G x)
  ; fmap = \f → fmap F (fmap G f)
  ; ≈-cong = \f≈g → ≈-cong F (≈-cong G f≈g)
  ; preserveId = trans-≈ E (≈-cong F (preserveId G)) (preserveId F)
  ; covariant = \{a} {b} {c} {f} {g} → let open ≈-Reasoning E in
    begin
      fmap F (fmap G (C [ g ∘ f ])) ↓⟨ ≈-cong F (covariant G) ⟩
      fmap F (D [ fmap G g ∘ fmap G f ]) ↓⟨ covariant F ⟩
      E [ fmap F (fmap G g) ∘ fmap F (fmap G f) ]
    ∎
  }
  where
    open ≈-lemmas

