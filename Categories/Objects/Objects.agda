open import Categories.Category

module Categories.Objects.Objects {C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) where

open import Level
open import Data.Empty
open import Categories.Functor
open import Categories.Nat
open import Categories.FunctorCategory
open import Categories.Limit
open import Categories.Categories.Index
open import Categories.Reasoning

open Category C
open Nat

record TerminalObject : Set (C₀ ⊔ C₁ ⊔ ℓ) where
  field
    1-obj : Obj

  field
    to-1 : (a : Obj) → a ~> 1-obj
    universality : (a : Obj) → (h : a ~> 1-obj) → h ≈ to-1 a

1! : Set _
1! = TerminalObject

TerminalObject-as-Limit : (F : Functor 𝟘 C) (L : Limit F) → TerminalObject
TerminalObject-as-Limit F L = record
  { 1-obj = Limit.limit L
  ; to-1 = \a → Limit.cone-map L (liftCone a)
  ; universality = universality-1
  }
  where
    liftCone : (a : Obj) → Cone F
    liftCone a = record
      { vertex = a
      ; side = record { component = \(); naturality = λ {a₁} {b} → λ {} } }

    universality-1 : (a : Obj) (h : a ~> Limit.limit L) → h ≈ Limit.cone-map L (liftCone a)
    universality-1 a h = Limit.universality L (liftCone a) h (eqArrow lemma)
      where
        lemma : {r : Category.Obj 𝟘} → component ([ 𝟘 , C ] [ Cone.side (Limit.limiting-cone L) ∘ DiagonalLift 𝟘 C h ]) r ≈ component (Cone.side (liftCone a)) r
        lemma {()}

record BinaryProduct (a₁ a₂ : Obj) : Set (C₀ ⊔ C₁ ⊔ ℓ) where
  field
    a₁×a₂ : Obj
    p₁ : a₁×a₂ ~> a₁
    p₂ : a₁×a₂ ~> a₂

  field
    ⟨_,_⟩ : {z : Obj} → (f₁ : z ~> a₁) → (f₂ : z ~> a₂) → z ~> a₁×a₂
    commute₁ : {z : Obj} → (f₁ : z ~> a₁) → (f₂ : z ~> a₂) → p₁ ∘ ⟨ f₁ , f₂ ⟩ ≈ f₁
    commute₂ : {z : Obj} → (f₁ : z ~> a₁) → (f₂ : z ~> a₂) → p₂ ∘ ⟨ f₁ , f₂ ⟩ ≈ f₂
    universality : {z : Obj} → (f₁ : z ~> a₁) → (f₂ : z ~> a₂) → (h : z ~> a₁×a₂)
      → p₁ ∘ h ≈ f₁ → p₂ ∘ h ≈ f₂ → h ≈ ⟨ f₁ , f₂ ⟩

_×_ : (a b : Obj) → Set _
a × b = BinaryProduct a b

