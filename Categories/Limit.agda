module Categories.Limit where

open import Level
open import Relation.Binary.Core using (Rel; module IsEquivalence)
open import Categories.Category
open import Categories.Functor
open import Categories.Nat
open import Categories.FunctorCategory
open import Categories.Reasoning

open Category
open Functor
open Nat
open IsEquivalence

Diagonal :
  ∀{S₀ S₁ ℓₛ C₀ C₁ ℓ} (J : Category S₀ S₁ ℓₛ) (C : Category C₀ C₁ ℓ)
  (r : Obj C) → Functor J C
Diagonal _ C r = record
  { fobj = \_ → r
  ; fmap = \_ → id C {r}

  ; ≈-cong = \_ → refl (equivalence C)
  ; preserveId = refl (equivalence C)
  ; covariant = sym (equivalence C) (trans (equivalence C) (leftIdentity C) (refl (equivalence C)))
  }

Δ[_] : ∀{S₀ S₁ ℓₛ C₀ C₁ ℓ} {J : Category S₀ S₁ ℓₛ} {C : Category C₀ C₁ ℓ} (r : Obj C) → Functor J C
Δ[_] {_} {_} {_} {_} {_} {_} {J} {C} r = Diagonal J C r

DiagonalLift : ∀{S₀ S₁ ℓₛ C₀ C₁ ℓ} (J : Category S₀ S₁ ℓₛ) (C : Category C₀ C₁ ℓ)
  {a b : Obj C} → (h : C [ a ~> b ]) → Nat {S₀} {S₁} {ℓₛ} {C₀} {C₁} {ℓ} {J} {C} (Diagonal J C a) (Diagonal J C b)
DiagonalLift J C {a} {b} h = record
  { component = \_ → h
  ; naturality = \{i} {j} {f} → let open ≈-Reasoning C in
    begin
      C [ h ∘ fmap (Diagonal J C a) f ] ↓⟨ refl-hom ⟩
      C [ h ∘ id C {a} ] ↓⟨ rightIdentity C ⟩
      h ↑⟨ leftIdentity C ⟩
      C [ fmap (Diagonal J C b) f ∘ h ]
    ∎
  }

record Cone {S₀ S₁ ℓₛ C₀ C₁ ℓ} {J : Category S₀ S₁ ℓₛ} {C : Category C₀ C₁ ℓ} (F : Functor J C) : Set (suc (ℓ ⊔ C₁ ⊔ C₀ ⊔ ℓₛ ⊔ S₁ ⊔ S₀)) where
  field
    vertex : Obj C
    side : Nat Δ[ vertex ] F
 
record Limit {S₀ S₁ ℓₛ C₀ C₁ ℓ} {J : Category S₀ S₁ ℓₛ} {C : Category C₀ C₁ ℓ} (F : Functor J C) : Set (suc (ℓ ⊔ C₁ ⊔ C₀ ⊔ ℓₛ ⊔ S₁ ⊔ S₀)) where
  field
    limiting-cone : Cone F

  limit : Obj C
  limit = Cone.vertex limiting-cone

  field
    cone-map : (d : Cone F) → C [ Cone.vertex d ~> limit ]
    universality :
      (d : Cone F) (h : C [ Cone.vertex d ~> limit ])
      → [ J , C ] [ [ J , C ] [ (Cone.side limiting-cone) ∘ DiagonalLift J C h ] ≈ (Cone.side d) ]
      → C [ h ≈ (cone-map d) ]

record Cone-Morphism {S₀ S₁ ℓₛ C₀ C₁ ℓ} {J : Category S₀ S₁ ℓₛ} {C : Category C₀ C₁ ℓ} {F : Functor J C} (c d : Cone F) : Set (suc (ℓ ⊔ C₁ ⊔ C₀) ⊔ S₀) where
  field
    vertex-arrow : C [ Cone.vertex c ~> Cone.vertex d ]

  cone-arrow : Nat (Δ[ Cone.vertex c ]) (Δ[ Cone.vertex d ])
  cone-arrow = DiagonalLift J C vertex-arrow

  field
    commute : [ J , C ] [ [ J , C ] [ Cone.side d ∘ cone-arrow ] ≈ Cone.side c ]

{-
Cone-Category : ∀{S₀ S₁ ℓₛ C₀ C₁ ℓ} (J : Category S₀ S₁ ℓₛ) (C : Category C₀ C₁ ℓ) {F : Functor J C} → Category _ _ _
Cone-Category J C {F} = record
  { Obj = Cone F
  ; _~>_ = Cone-Morphism
  ; _∘_ = Cone-Morphism-composite
  ; _≈_ = Cone-Morphism-≈
  ; id = Cone-Morphism-id

  ; leftIdentity = {!!}
  ; rightIdentity = {!!}
  ; assoc = {!!}
  ; equivalence = {!!}
  ; ≈-composite = {!!}
  }
  where
    open Cone-Morphism
    open Cone
    open ≈-lemmas [ J , C ]

    Cone-Morphism-composite : {a b c : Cone F} → Cone-Morphism b c → Cone-Morphism a b → Cone-Morphism a c
    Cone-Morphism-composite {a} {b} {c} bc ab = record
      { vertex-arrow = C [ vertex-arrow bc ∘ vertex-arrow ab ]
      ; commute = let open ≈-Reasoning [ J , C ] in
        begin
          [ J , C ] [ side c ∘ [ J , C ] [ cone-arrow bc ∘ cone-arrow ab ] ]
        ↑⟨ assoc [ J , C ] ⟩
          [ J , C ] [ [ J , C ] [ side c ∘ cone-arrow bc ] ∘ cone-arrow ab ]
        ↓⟨ ≈-composite-refl (commute bc) ⟩
          [ J , C ] [ side b ∘ cone-arrow ab ]
        ↓⟨ commute ab ⟩
          side a
        ∎
      }

    Cone-Morphism-≈ : {a b : Cone F} → (α β : Cone-Morphism a b) → Set _
    Cone-Morphism-≈ α β = C [ vertex-arrow α ~ vertex-arrow β ]

    Cone-Morphism-id : {a : Cone F} → Cone-Morphism a a
    Cone-Morphism-id {a} = record
      { vertex-arrow = id C
      ; commute = rightIdentity [ J , C ]
      }

-}
