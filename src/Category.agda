module Category where

open import Function hiding (_∘_; id)
open import Level
open import Data.Product
open import Relation.Binary
open import Relation.Binary.Core using (_≡_)
open Setoid renaming (_≈_ to eqSetoid)

open import Basic

record Category (C₀ C₁ ℓ : Level) : Set (suc (C₀ ⊔ C₁ ⊔ ℓ)) where
  field
    Obj : Set C₀
    Homsetoid : Obj → Obj → Setoid C₁ ℓ

  Hom : Obj → Obj → Set C₁
  Hom A B = Carrier (Homsetoid A B)

  equal : {A B : Obj} → Hom A B → Hom A B → Set ℓ
  equal {A} {B} f g = eqSetoid (Homsetoid A B) f g

  field
    comp : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    id : {A : Obj} → Hom A A

  field
    leftId : {A B : Obj} {f : Hom A B} → equal (comp id f) f
    rightId : {A B : Obj} {f : Hom A B} → equal (comp f id) f
    assoc : {A B C D : Obj} {f : Hom A B} {g : Hom B C} {h : Hom C D}
      → equal (comp (comp h g) f) (comp h (comp g f))
    ≈-composite : {A B C : Obj} {f g : Hom B C} {h i : Hom A B}
      → equal f g → equal h i → equal (comp f h) (comp g i)

  dom : {A B : Obj} → Hom A B → Obj
  dom {A} _ = A

  cod : {A B : Obj} → Hom A B → Obj
  cod {B} _ = B

  op : Category C₀ C₁ ℓ
  op = record
    { Obj = Obj
    ; Homsetoid = flip Homsetoid
    ; comp = flip comp
    ; id = id

    ; leftId = rightId
    ; rightId = leftId
    ; assoc = λ{A B C D} → IsEquivalence.sym (isEquivalence (Homsetoid D A)) assoc
    ; ≈-composite = flip ≈-composite
    }

open Category

infixr 9 _∘_
infixr 7 _[_∘_]
infixr 2 _≈_
infixr 2 _[_≈_]
infix 4 _[_≅_]

_[_∘_] : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
C [ f ∘ g ] = comp C f g

_∘_ : ∀{C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
_∘_ {C = C} = _[_∘_] C

_[_≈_] : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) {A B : Obj C} → Rel (Hom C A B) ℓ
C [ f ≈ g ] = equal C f g

_≈_ : ∀{C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} {A B : Obj C} → Rel (Hom C A B) ℓ
_≈_ {C = C} = equal C

equiv : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) {A B : Obj C} → IsEquivalence (eqSetoid (Homsetoid C A B))
equiv C {A} {B} = isEquivalence (Homsetoid C A B)

refl-hom : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) {A B : Obj C} {f : Hom C A B} → C [ f ≈ f ]
refl-hom C = IsEquivalence.refl (equiv C)

sym-hom : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) {A B : Obj C} {f g : Hom C A B} → C [ f ≈ g ] → C [ g ≈ f ]
sym-hom C = IsEquivalence.sym (equiv C)

trans-hom : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) {A B : Obj C} {f g h : Hom C A B} → C [ f ≈ g ] → C [ g ≈ h ] → C [ f ≈ h ]
trans-hom C = IsEquivalence.trans (equiv C)

record _[_≅_] {C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) (a b : Obj C) : Set (C₀ ⊔ C₁ ⊔ ℓ) where
  field
    map-→ : Hom C a b
    map-← : Hom C b a
    proof : (C [ C [ map-→ ∘ map-← ] ≈ id C ]) × (C [ C [ map-← ∘ map-→ ] ≈ id C ])

record isomorphism {C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) {a b : Obj C} (f : Hom C a b) : Set (C₀ ⊔ C₁ ⊔ ℓ) where
  field
    inverse-map : Hom C b a
    proof : (C [ C [ f ∘ inverse-map ] ≈ id C ]) × (C [ C [ inverse-map ∘ f ] ≈ id C ])

iso-≅ : ∀ {C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) {a b : Obj C} {f : Hom C a b} → isomorphism C f → C [ a ≅ b ]
iso-≅ C {f = f} iso = record {
  map-→ = f ;
  map-← = isomorphism.inverse-map iso ;
  proof = isomorphism.proof iso }

Setoids : {c₀ ℓ : Level} → Category (suc (c₀ ⊔ ℓ)) (suc (c₀ ⊔ ℓ)) (c₀ ⊔ ℓ)
Setoids {c₀} {ℓ} = record {
  Obj = Setoid c₀ ℓ;
  Homsetoid = λ A B → record { Carrier = Map.Map A B; _≈_ = Map.equality; isEquivalence = Map-Equal-Equiv A B };
  comp = Map.compose;
  id = Map.identity;
  leftId = λ {_ B} _ → refl B;
  rightId = λ {_ B} _ → refl B;
  assoc = λ {_ _ _ D} x → refl D;
  ≈-composite = λ {_ _ C f g h} x x₁ x₂ → trans C (x (Map.Map.mapping h x₂)) (Map.Map.preserveEq g (x₁ x₂)) }
  where
    Map-Equal-Equiv : (A B : Setoid _ _) → IsEquivalence Map.equality
    Map-Equal-Equiv A B = record { refl = λ _ → refl B ; sym = λ x x₁ → sym B (x x₁) ; trans = λ x x₁ x₂ → trans B (x x₂) (x₁ x₂) }

module CategoryReasoning where
  infix 1 begin⟨_⟩_
  infixr 2 _≈⟨_⟩_ _≡⟨_⟩_
  infix 3 _∎

  data IsRelatedTo[_] {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) (a b : Obj C) (x y : Hom C a b) : Set ℓ where
    relTo : C [ x ≈ y ] → IsRelatedTo[ C ] a b x y

  begin⟨_⟩_ : ∀ {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) → {A B : Obj C} {f g : Hom C A B} → IsRelatedTo[ C ] A B f g → equal C f g
  begin⟨_⟩_ C {A} {B} (relTo x≈y) = x≈y

  _∎ : ∀ {c₀ c₁ ℓ} {C : Category c₀ c₁ ℓ} {A B : Obj C} (f : Hom C A B) → IsRelatedTo[ C ] A B f f
  _∎ {C = C} f = relTo (refl-hom C)

  _≈⟨_⟩_ : ∀ {c₀ c₁ ℓ} {C : Category c₀ c₁ ℓ} → {A B : Obj C} (f : Hom C A B) → {g h : Hom C A B} → equal C f g → IsRelatedTo[ C ] A B g h → IsRelatedTo[ C ] A B f h
  _≈⟨_⟩_ {C = C} f f≈g (relTo g≈h) = relTo (trans-hom C f≈g g≈h)

  _≡⟨_⟩_ : ∀ {c₀ c₁ ℓ} {C : Category c₀ c₁ ℓ} → {A B : Obj C} (f : Hom C A B) → {g h : Hom C A B} → f ≡ g → IsRelatedTo[ C ] A B g h → IsRelatedTo[ C ] A B f h
  _≡⟨_⟩_ {C = C} f _≡_.refl (relTo g≈h) = relTo g≈h

open CategoryReasoning public
