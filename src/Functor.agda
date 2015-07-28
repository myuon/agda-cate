module Functor where

open import Level
import Data.Nat as N

open import Basic
open import Category
open Category.Category

record Functor {c₀ c₁ ℓ c₀′ c₁′ ℓ′} (C : Category c₀ c₁ ℓ) (D : Category c₀′ c₁′ ℓ′) : Set (suc (c₀ ⊔ c₀′ ⊔ c₁ ⊔ c₁′ ⊔ ℓ ⊔ ℓ′)) where
  field
    fobj : Obj C → Obj D
    fmapsetoid : {A B : Obj C} → Map.Map (Homsetoid C A B) (Homsetoid D (fobj A) (fobj B))

  fmap : {A B : Obj C} → Hom C A B → Hom D (fobj A) (fobj B)
  fmap {A} {B} = Map.Map.mapping (fmapsetoid {A} {B})

  field
    preserveId : {A : Obj C} → D [ fmap (id C {A}) ≈ id D {fobj A} ]
    preserveComp : {a b c : Obj C} {f : Hom C b c} {g : Hom C a b} → D [ fmap (C [ f ∘ g ]) ≈ (D [ fmap f ∘ fmap g ]) ]

open Functor

preserveEq : ∀ {c₀ c₁ ℓ c₀′ c₁′ ℓ′} {C : Category c₀ c₁ ℓ} {D : Category c₀′ c₁′ ℓ′} {A B : Obj C} {x y : Hom C A B} (F : Functor C D) → C [ x ≈ y ] → D [ fmap F x ≈ fmap F y ]
preserveEq F xy = Map.Map.preserveEq (fmapsetoid F) xy

compose : ∀ {c₀ c₁ ℓ c₀′ c₁′ ℓ′ c₀″ c₁″ ℓ″} {C : Category c₀ c₁ ℓ} {D : Category c₀′ c₁′ ℓ′} {E : Category c₀″ c₁″ ℓ″} → Functor {c₀′} {c₁′} {ℓ′} {c₀″} {c₁″} {ℓ″} D E → Functor {c₀} {c₁} {ℓ} {c₀′} {c₁′} {ℓ′} C D → Functor {c₀} {c₁} {ℓ} {c₀″} {c₁″} {ℓ″} C E
compose {C = C} {D} {E} G F = record {
  fobj = λ x → fobj G (fobj F x);
  fmapsetoid = record { mapping = λ f → fmap G (fmap F f) ; preserveEq = λ {x} {y} x≈y → begin⟨ E ⟩
    fmap G (fmap F x) ≈⟨ preserveEq G (begin⟨ D ⟩
      fmap F x ≈⟨ preserveEq F x≈y ⟩
      fmap F y ∎) ⟩
    fmap G (fmap F y) ∎
  };
  preserveId = begin⟨ E ⟩
    fmap G (fmap F (id C)) ≈⟨ preserveEq G (preserveId F) ⟩
    fmap G (id D) ≈⟨ preserveId G ⟩
    (id E) ∎;
  preserveComp = λ {_} {_} {_} {f} {g} → begin⟨ E ⟩
    fmap G (fmap F (C [ f ∘ g ])) ≈⟨ preserveEq G (preserveComp F) ⟩
    fmap G (D [ fmap F f ∘ fmap F g ]) ≈⟨ preserveComp G ⟩
    (E [ fmap G (fmap F f) ∘ fmap G (fmap F g) ]) ∎
  }

identity : ∀ {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) → Functor {c₀} {c₁} {ℓ} {c₀} {c₁} {ℓ} C C
identity C = record {
  fobj = λ x → x ;
  fmapsetoid = record { mapping = λ x → x ; preserveEq = λ x₁ → x₁ } ;
  preserveId = refl-hom C ; preserveComp = refl-hom C }

exp : ∀ {c₀ c₁ ℓ} {C : Category c₀ c₁ ℓ} → Functor C C → N.ℕ → Functor C C
exp {C = C} F N.zero = identity C
exp F (N.suc N.zero) = F
exp F (N.suc n) = compose F (exp F n)

data _[_~_]
  {C₀ C₁ ℓ : Level} (C : Category C₀ C₁ ℓ) {A B : Obj C} (f : Hom C A B)
  : ∀{X Y : Obj C} → Hom C X Y → Set (suc (C₀ ⊔ C₁ ⊔ ℓ)) where
  eqArrow : {g : Hom C A B} → C [ f ≈ g ] → C [ f ~ g ]

eqArrowRefl : ∀ {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) {A B : Obj C} {f : Hom C A B} → C [ f ~ f ]
eqArrowRefl C = eqArrow (refl-hom C)

eqArrowSym : ∀ {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) {X Y Z W : Obj C} {f : Hom C X Y} {g : Hom C Z W} → C [ f ~ g ] → C [ g ~ f ]
eqArrowSym C (eqArrow f~g) = eqArrow (sym-hom C f~g)

eqArrowTrans : ∀ {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) {X Y Z W S T : Obj C} {f : Hom C X Y} {g : Hom C Z W} {h : Hom C S T} → C [ f ~ g ] → C [ g ~ h ] → C [ f ~ h ]
eqArrowTrans C (eqArrow f~g) (eqArrow g~h) = eqArrow (trans-hom C f~g g~h)

eqArrowFmap : ∀ {c₀ c₁ ℓ c₀′ c₁′ ℓ′} {C : Category c₀ c₁ ℓ} {D : Category c₀′ c₁′ ℓ′} {X Y Z W : Obj C} {x : Category.Hom C X Y} {y : Category.Hom C Z W} (F : Functor C D) → C [ x ~ y ] → D [ fmap F x ~ fmap F y ]
eqArrowFmap F (eqArrow x~y) = eqArrow (preserveEq F x~y)

equality : ∀ {c₀ c₁ ℓ} {C D : Category c₀ c₁ ℓ} → (F G : Functor C D) → _
equality {C = C} {D} F G = ∀ {A B : Obj C} (f : Hom C A B) → D [ fmap F f ~ fmap G f ]

Cat : ∀ {c₀ c₁ ℓ} → Category (suc (c₀ ⊔ c₁ ⊔ ℓ)) _ _
Cat {c₀} {c₁} {ℓ} = record {
  Obj = Category c₀ c₁ ℓ;
  Homsetoid = λ A B → record {
    Carrier = Functor A B ; _≈_ = equality ;
    isEquivalence = record {
      refl = λ f → eqArrowRefl B ;
      sym = λ x f → eqArrowSym B (x f);
      trans = λ x x₁ f → eqArrowTrans B (x f) (x₁ f) } };
  comp = compose;
  id = λ {A} → identity A;
  leftId = λ {A} {B} {f} f₁ → eqArrow (refl-hom B);
  rightId = λ {A} {B} {f} f₁ → eqArrow (refl-hom B);
  assoc = λ {A} {B} {C} {D} {f} {g} {h} f₁ → eqArrow (begin⟨ D ⟩
    fmap (compose (compose h g) f) f₁ ≈⟨ refl-hom D ⟩
    fmap h (fmap g (fmap f f₁)) ≈⟨ refl-hom D ⟩
    fmap (compose h (compose g f)) f₁
    ∎);
  ≈-composite = λ {A} {B} {C} {f} {g} {h} {i} f~g h~i f₁ → eqArrowTrans C (f~g (fmap h f₁)) (eqArrowFmap g (h~i f₁))
  }

