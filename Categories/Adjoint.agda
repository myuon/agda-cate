module Categories.Adjoint where

open import Level
open import Categories.Category
open import Categories.Functor
open import Categories.Yoneda
open import Categories.Nat
open import Categories.Categories.Sets

open Category
open _≅_
open Functor

record Adjoint {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} (F : Functor C D) (G : Functor D C) : Set (ℓ ⊔ suc C₁ ⊔ C₀) where
  field
    adjunction : ∀{x : Obj C} {a : Obj D} → Sets {C₁} [ D [ fobj F x ~> a ] ≅ C [ x ~> fobj G a ] ]

  adjunct-F→G : ∀{x} {a} → Sets [ D [ fobj F x ~> a ] ~> C [ x ~> fobj G a ] ]
  adjunct-F→G {x} {a} = ≅-→ (adjunction {x} {a})

  adjunct-F←G : ∀{x} {a} → Sets [ C [ x ~> fobj G a ] ~> D [ fobj F x ~> a ] ]
  adjunct-F←G {x} {a} = ≅-← (adjunction {x} {a})

  field
    naturality-C : ∀{x y : Obj C} {a : Obj D} → {f : C [ y ~> x ]} →
      Sets [
        Sets [ fmap (fobj (yoneda C) (fobj G a)) f ∘ adjunct-F→G {x} {a} ] ≈
        Sets [ adjunct-F→G {y} {a} ∘ fmap (fobj (yoneda D) a) (fmap F f) ] ]
    naturality-D : ∀{x : Obj C} {a b : Obj D} → {f : D [ a ~> b ]} →
      Sets [
        Sets [ fmap (fobj (grothendieck C) x) (fmap G f) ∘ adjunct-F→G {x} {a} ] ≈
        Sets [ adjunct-F→G {x} {b} ∘ fmap (fobj (grothendieck D) (fobj F x)) f ] ]

_⊣_ : ∀{C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} (F : Functor C D) (G : Functor D C) → Set (ℓ ⊔ suc C₁ ⊔ C₀)
_⊣_ = Adjoint
