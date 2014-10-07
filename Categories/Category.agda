module Categories.Category where

open import Level
open import Function as F using (flip)
open import Relation.Binary

record Category (C₀ C₁ ℓ : Level) : Set (suc (C₀ ⊔ C₁ ⊔ ℓ)) where
  infixr 9 _∘_
  infix 4 _≈_

  field
    Obj : Set C₀
    _~>_ : Obj → Obj → Set C₁
    _∘_ : {A B C : Obj} → B ~> C → A ~> B → A ~> C
    _≈_ : {A B : Obj} → Rel (A ~> B) ℓ
    id : {A : Obj} → A ~> A

  field
    leftIdentity : {A B : Obj} {f : A ~> B} → id ∘ f ≈ f
    rightIdentity : {A B : Obj} {f : A ~> B} → f ∘ id ≈ f
    assoc : {A B C D : Obj} {f : A ~> B} {g : B ~> C} {h : C ~> D}
      → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    equivalence : {A B : Obj} → IsEquivalence (_≈_ {A} {B})
    ≈-composite : {A B C : Obj} {f g : B ~> C} {h i : A ~> B}
      → f ≈ g → h ≈ i → f ∘ h ≈ g ∘ i

  Hom : Obj → Obj → Set C₁
  Hom A B = A ~> B

  op : Category C₀ C₁ ℓ
  op = record
    { Obj = Obj
    ; _~>_ = flip _~>_
    ; _∘_ = flip _∘_
    ; _≈_ = _≈_
    ; id = id

    ; leftIdentity = rightIdentity
    ; rightIdentity = leftIdentity
    ; assoc = IsEquivalence.sym equivalence assoc
    ; equivalence = equivalence
    ; ≈-composite = flip ≈-composite
    }

  dom : {A B : Obj} → A ~> B → Obj
  dom {A} _ = A

  cod : {A B : Obj} → A ~> B → Obj
  cod {B} _ = B

open Category

_[_~>_] : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ)
  → (a b : Obj C) → Set C₁
C [ a ~> b ] = Hom C a b

_[_∘_] : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) {a b c : Obj C}
  → Hom C b c → Hom C a b → Hom C a c
C [ f ∘ g ] = _∘_ C f g

_[_≈_] : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) {a b : Obj C}
  → Rel (C [ a ~> b ]) ℓ
C [ f ≈ g ] = _≈_ C f g

record Iso {C₀ C₁ ℓ : Level} {C : Category C₀ C₁ ℓ} {a b : Obj C}
  (f : C [ a ~> b ]) (g : C [ b ~> a ]) : Set (C₀ ⊔ C₁ ⊔ ℓ) where
  field
    iso-l : C [ C [ g ∘ f ] ≈ id C ]
    iso-r : C [ C [ f ∘ g ] ≈ id C ]

infix 4 _≅_
record _≅_ {C₀ C₁ ℓ : Level} {C : Category C₀ C₁ ℓ} (a b : Obj C) : Set (C₀ ⊔ C₁ ⊔ ℓ) where
  field
    l~>r : C [ a ~> b ]
    r~>l : C [ b ~> a ]
    iso : Iso {C₀} {C₁} {ℓ} {C} {a} {b} l~>r r~>l

_[_≅_] : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) (a b : Obj C) → Set _
C [ a ≅ b ] = _≅_ {_} {_} {_} {C} a b

data _[_~_]
  {C₀ C₁ ℓ : Level} (C : Category C₀ C₁ ℓ) {A B : Obj C} (f : C [ A ~> B ])
  : ∀{X Y : Obj C} → C [ X ~> Y ] → Set (suc (C₀ ⊔ C₁ ⊔ ℓ)) where
  eqArrow : {g : C [ A ~> B ]} → C [ f ≈ g ] → C [ f ~ g ]

module LocallySmall {S₀ S₁ ℓ′} where
  open import Relation.Binary.Core
  postulate ≈-≡ : {C : Category S₀ S₁ ℓ′} {a b : Obj C} {f g : Hom C a b} → C [ f ≈ g ] → f ≡ g
  import Relation.Binary.PropositionalEquality as Eq
  postulate extensionality : Eq.Extensionality S₁ S₁

module ≈-lemmas {C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) where
  open IsEquivalence
  refl-≈ : {a b : Obj C} {f : C [ a ~> b ]} → C [ f ≈ f ]
  refl-≈ = refl (equivalence C)

  sym-≈ : {a b : Obj C} {f g : C [ a ~> b ]} → C [ f ≈ g ] → C [ g ≈ f ]
  sym-≈ f≈g = sym (equivalence C) f≈g

  trans-≈ : {a b : Obj C} {f g h : C [ a ~> b ]} → C [ f ≈ g ] → C [ g ≈ h ] → C [ f ≈ h ]
  trans-≈ f≈g g≈h = trans (equivalence C) f≈g g≈h

  ≈-refl-composite : {a b c : Obj C} {f : C [ b ~> c ]} {h i : C [ a ~> b ]}
      → C [ h ≈ i ] → C [ C [ f ∘ h ] ≈ C [ f ∘ i ] ]
  ≈-refl-composite h≈i = ≈-composite C (refl (equivalence C)) h≈i

  ≈-composite-refl : {a b c : Obj C} {f g : C [ b ~> c ]} {h : C [ a ~> b ]}
      → C [ f ≈ g ] → C [ C [ f ∘ h ] ≈ C [ g ∘ h ] ]
  ≈-composite-refl f≈g = ≈-composite C f≈g (refl (equivalence C))

