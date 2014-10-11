module Categories.KanExtension where

open import Level
open import Function hiding (id)
open import Function.Equivalence hiding (id)
open import Categories.Category
open import Categories.Functor
open import Categories.Nat
open import Categories.Categories.Sets
open import Categories.Reasoning

open Category
open Functor
open Nat

record Lan {B₀ B₁ ℓ C₀ C₁ ℓ′ D₀ D₁ ℓ″ : Level}
  {C : Category C₀ C₁ ℓ} {D : Category C₀ C₁ ℓ} {U : Category C₀ C₁ ℓ}
  (F : Functor C D) (E : Functor C U) : Set (suc (ℓ ⊔ C₁ ⊔ C₀)) where
  field
    kan-ext : Functor D U
    kan-nat : Nat E (kan-ext ∘F F)

  field
    nat-induced : (S : Functor D U) → Nat E (S ∘F F) → Nat kan-ext S
    universality : (S : Functor D U) → (θ : Nat E (S ∘F F)) → (τ : Nat kan-ext S) → [ C , U ] [ θ ≈ [ C , U ] [ (F ∘↓ τ) ∘ kan-nat ] ] → [ D , U ] [ τ ≈ nat-induced S θ ]

_†_ : {B₀ B₁ ℓ C₀ C₁ ℓ′ D₀ D₁ ℓ″ : Level}
  {C : Category C₀ C₁ ℓ} {D : Category C₀ C₁ ℓ} {U : Category C₀ C₁ ℓ}
  (F : Functor C D) (E : Functor C U) → Set (suc C₁ ⊔ (suc C₀ ⊔ suc ℓ))
_†_ {B₀} {B₁} {ℓ} {C₀} {C₁} {ℓ′} {D₀} {D₁} {ℓ″} {C} {D} {U}
  = Lan {B₀} {B₁} {ℓ} {C₀} {C₁} {ℓ′} {D₀} {D₁} {ℓ″} {C} {D} {U}

record Ran {B₀ B₁ ℓ C₀ C₁ ℓ′ D₀ D₁ ℓ″ : Level}
  {C : Category C₀ C₁ ℓ} {D : Category C₀ C₁ ℓ} {U : Category C₀ C₁ ℓ}
  (F : Functor C D) (E : Functor C U) : Set (suc (ℓ ⊔ C₁ ⊔ C₀)) where
  field
    kan-ext : Functor D U
    kan-nat : Nat (kan-ext ∘F F) E

  field
    nat-induced : (S : Functor D U) → Nat (S ∘F F) E → Nat S kan-ext
    universality : (S : Functor D U) → (θ : Nat (S ∘F F) E) → (τ : Nat S kan-ext) → [ C , U ] [ θ ≈ [ C , U ] [ kan-nat ∘ (F ∘↓ τ) ] ] → [ D , U ] [ τ ≈ nat-induced S θ ]

_‡_ : {B₀ B₁ ℓ C₀ C₁ ℓ′ D₀ D₁ ℓ″ : Level}
  {C : Category C₀ C₁ ℓ} {D : Category C₀ C₁ ℓ} {U : Category C₀ C₁ ℓ}
  (F : Functor C D) (E : Functor C U) → Set (suc C₁ ⊔ (suc C₀ ⊔ suc ℓ))
_‡_ {B₀} {B₁} {ℓ} {C₀} {C₁} {ℓ′} {D₀} {D₁} {ℓ″} {C} {D} {U}
  = Ran {B₀} {B₁} {ℓ} {C₀} {C₁} {ℓ′} {D₀} {D₁} {ℓ″} {C} {D} {U}

_⁻¹ : {C₀ C₁ ℓ D₀ D₁ ℓ′ U₀ U₁ ℓ″ : Level}
  {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {U : Category U₀ U₁ ℓ″}
  (F : Functor C D) → Functor [ D , U ] [ C , U ]
_⁻¹ {C = C} {D = D} {U = U} F = record
  { fobj = \S → S ∘F F
  ; fmap = \α → F ∘↓ α
  ; ≈-cong = \f≈g → f≈g
  ; preserveId = \{a : Obj [ D , U ]} {r : Obj C} → eqArrow $ let open ≈-Reasoning U in refl-hom
  ; covariant = \{a} {b} {c} {f} {g} {r} → eqArrow $ let open ≈-Reasoning U in refl-hom
  }

{-
hom[_,_⁻¹[-]] : {C₀ C₁ ℓ D₀ D₁ ℓ′ U₀ U₁ ℓ″ : Level} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {U : Category U₀ U₁ ℓ″} → Functor C D → Functor C U → Functor [ U , D ] Sets
hom[_,_⁻¹[-]] {C = C} {D = D} {U = U} E F = record
  { fobj = \r → Nat E (fobj (F ⁻¹) r)
  ; fmap = fmap-hom
  ; ≈-cong = \{a} {b} {f : Nat a b} {g : Nat a b} f≈g → {!!}
  ; preserveId = {!!}
  ; covariant = {!!}
  }
  where
    open ≈-lemmas

    fmap-hom = \{a} {b} (f : [ U , D ] [ a ~> b ]) (α : Nat E (fobj (F ⁻¹) a))
      → record
      { component = \(r : Obj C) → D [ component (fmap (F ⁻¹) f) r ∘ component α r ]
      ; naturality = \{x} {y} {g : C [ x ~> y ]} → let open ≈-Reasoning D in
        begin
          D [ D [ component f (fobj F y) ∘ component α y ] ∘ fmap E g ]
        ↓⟨ assoc D ⟩
          D [ component f (fobj F y) ∘ D [ component α y ∘ fmap E g ] ]
        ↓⟨ ≈-composite-reflˡ D (naturality α) ⟩
          D [ component f (fobj F y) ∘ D [ fmap (a ∘F F) g ∘ component α x ] ]
        ↑⟨ assoc D ⟩
          D [ D [ component (F ∘↓ f) y ∘ fmap (a ∘F F) g ] ∘ component α x ]
        ↓⟨ ≈-composite-reflʳ D (naturality (F ∘↓ f)) ⟩
          D [ D [ fmap (b ∘F F) g ∘ component (F ∘↓ f) x ] ∘ component α x ]
        ↓⟨ assoc D ⟩
          D [ fmap (b ∘F F) g ∘ D [ component f (fobj F x) ∘ component α x ] ]
        ∎
      }
-}

--Prop1 : {B₀ B₁ ℓ C₀ C₁ ℓ′ D₀ D₁ ℓ″ : Level} {C D U : Category C₀ C₁ ℓ}
--  (F : Functor C D) (E : Functor C U) → ∃ Repesentable ()
