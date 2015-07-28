module Nat where

open import Function hiding (_∘_; id)
open import Level

open import Basic
open import Category
import Functor
open Category.Category
open Functor.Functor

record Nat {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} (F G : Functor.Functor C D) : Set (suc (C₀ ⊔ C₁ ⊔ ℓ ⊔ D₀ ⊔ D₁ ⊔ ℓ′)) where
  field
    component : (X : Obj C) → Hom D (fobj F X) (fobj G X)

  field
    naturality : {a b : Obj C} {f : Hom C a b}
      → D [ D [ component b ∘ fmap F f ] ≈ D [ fmap G f ∘ component a ] ]

open Nat

identity : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} → (F : Functor.Functor C D) → Nat F F
identity {D = D} F = record {
  component = λ X → id D ;
  naturality = λ {a} {b} {f} → trans-hom D (leftId D) (sym-hom D (rightId D)) }

compose : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} → {F G H : Functor.Functor C D} → Nat G H → Nat F G → Nat F H
compose {C = C} {D} {F} {G} {H} η ε  = record {
  component = λ X → D [ component η X ∘ component ε X ] ;
  naturality = λ {a} {b} {f} → (begin⟨ D ⟩
    D [ (D [ component η b ∘ component ε b ]) ∘ fmap F f ] ≈⟨ assoc D ⟩
    D [ component η b ∘ (D [ component ε b ∘ fmap F f ]) ] ≈⟨ ≈-composite D (refl-hom D) (naturality ε) ⟩
    D [ component η b ∘ (D [ fmap G f ∘ component ε a ]) ] ≈⟨ sym-hom D (assoc D) ⟩
    D [ (D [ component η b ∘ fmap G f ]) ∘ component ε a ] ≈⟨ ≈-composite D (naturality η) (refl-hom D) ⟩
    D [ (D [ fmap H f ∘ component η a ]) ∘ component ε a ] ≈⟨ assoc D ⟩
    D [ fmap H f ∘ (D [ component η a ∘ component ε a ]) ] ∎) }

composeNF : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′ E₀ E₁ ℓ″} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {E : Category E₀ E₁ ℓ″} {A B : Functor.Functor D E} → Nat A B → (F : Functor.Functor C D) → Nat (Functor.compose A F) (Functor.compose B F)
composeNF {C = C} {D} {E} {A} {B} η F = record {
  component = λ X → component η (fobj F X) ;
  naturality = λ {a} {b} {f} → naturality η }

composeFN : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′ E₀ E₁ ℓ″} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {E : Category E₀ E₁ ℓ″} {A B : Functor.Functor C D} (F : Functor.Functor D E) → Nat A B → Nat (Functor.compose F A) (Functor.compose F B)
composeFN {C = C} {D} {E} {A} {B} F η = record {
  component = λ X → fmap F (component η X) ;
  naturality = λ {a} {b} {f} → begin⟨ E ⟩
    E [ fmap F (component η b) ∘ fmap (Functor.compose F A) f ] ≈⟨ sym-hom E (preserveComp F) ⟩
    fmap F (D [ component η b ∘ fmap A f ]) ≈⟨ Functor.preserveEq F (naturality η) ⟩
    fmap F (D [ fmap B f ∘ component η a ]) ≈⟨ preserveComp F ⟩
    E [ fmap (Functor.compose F B) f ∘ fmap F (component η a) ]
    ∎ }

equality : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F G : Functor.Functor C D} → (η τ : Nat F G) → Set _
equality {C = C} {D} η τ = ∀ {a : Obj C} → D [ component η a ≈ component τ a ]

subst : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F G : Functor.Functor C D} {η τ : Nat F G} → (a : Obj C) → equality η τ → D [ component η a ≈ component τ a ]
subst a eq = eq {a}

HomFunctor : ∀ {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) (X : Obj C) → Functor.Functor C Setoids
HomFunctor C X = record {
  fobj = λ x → (Homsetoid C X x) ;
  fmapsetoid = record {
    mapping = λ x → record { mapping = λ x₁ → C [ x ∘ x₁ ] ; preserveEq = ≈-composite C (refl-hom C) } ;
    preserveEq = λ x₁ x₂ → ≈-composite C x₁ (refl-hom C) } ;
  preserveId = λ x → leftId C ;
  preserveComp = λ x → assoc C }

HomNat : ∀ {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) {A B : Obj C} (f : Hom C A B) → Nat (HomFunctor C B) (HomFunctor C A)
HomNat C {A} {B} f = record {
  component = component-map ;
  naturality = λ {a} {b} {x} → λ x₁ → begin⟨ C ⟩
    Map.mapping (Setoids [ component-map b ∘ fmap (HomFunctor C B) x ]) x₁ ≈⟨ refl-hom C ⟩
    C [ C [ x ∘ x₁ ] ∘ f ] ≈⟨ assoc C ⟩
    C [ x ∘ C [ x₁ ∘ f ] ] ≈⟨ refl-hom C ⟩
    Map.mapping (Setoids [ fmap (HomFunctor C A) x ∘ component-map a ]) x₁
  ∎ }
  where
    component-map = λ X → record {
      mapping = λ x → C [ x ∘ f ] ;
      preserveEq = λ x₁ → ≈-composite C x₁ (refl-hom C) }

HomFunctorOp : ∀ {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) (X : Obj C) → Functor.Functor (op C) Setoids
HomFunctorOp C X = record {
  fobj = λ x → (Homsetoid C x X) ;
  fmapsetoid = record {
    mapping = λ x → record { mapping = λ x₁ → C [ x₁ ∘ x ] ; preserveEq = ≈-composite (op C) (refl-hom C) } ;
    preserveEq = λ x₁ x₂ → ≈-composite (op C) x₁ (refl-hom C) } ;
  preserveId = λ x → leftId (op C) ;
  preserveComp = λ x → assoc (op C) }

HomNatOp : ∀ {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) {A B : Obj C} (f : Hom C A B) → Nat (HomFunctorOp C A) (HomFunctorOp C B)
HomNatOp C {A} {B} f = record {
  component = component-map ;
  naturality = λ {a} {b} {x} → λ x₁ → begin⟨ C ⟩
    Map.mapping (Setoids [ component-map b ∘ fmap (HomFunctorOp C A) x ]) x₁ ≈⟨ refl-hom C ⟩
    C [ f ∘ C [ x₁ ∘ x ] ] ≈⟨ sym-hom C (assoc C) ⟩
    C [ C [ f ∘ x₁ ] ∘ x ] ≈⟨ refl-hom C ⟩
    Map.mapping (Setoids [ fmap (HomFunctorOp C B) x ∘ component-map a ]) x₁
  ∎ }
  where
    component-map = λ X → record {
      mapping = λ x → C [ f ∘ x ] ;
      preserveEq = λ x₁ → ≈-composite C (refl-hom C) x₁ }

FunCat : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} → (Category C₀ C₁ ℓ) → (Category D₀ D₁ ℓ′) → Category _ _ _
FunCat C D = record {
  Obj = Functor.Functor C D;
  Homsetoid = λ F G → record { Carrier = Nat F G ; _≈_ = equality ; isEquivalence = record {
    refl = λ {x} {a} → refl-hom D ;
    sym = λ x → λ {a} → sym-hom D x ;
    trans = λ x x₁ → λ {a} → trans-hom D x x₁ } };
  comp = compose;
  id = λ {A} → identity A;
  leftId = λ {A} {B} {f} {a} → leftId D;
  rightId = λ {A} {B} {f} {a} → rightId D;
  assoc = λ {A} {B} {C₁} {D₁} {f} {g} {h} {a} → assoc D;
  ≈-composite = λ x x₁ → ≈-composite D x x₁
  }

assocNat→ : ∀{B₀ B₁ ℓ‴ C₀ C₁ ℓ D₀ D₁ ℓ′ E₀ E₁ ℓ″} {B : Category B₀ B₁ ℓ‴} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {E : Category E₀ E₁ ℓ″} {F : Functor.Functor B C} {G : Functor.Functor C D} {H : Functor.Functor D E} → Nat (Functor.compose (Functor.compose H G) F) (Functor.compose H (Functor.compose G F))
assocNat→ {C = C} {D} {E} {F} = record {
  component = λ X → id E ;
  naturality = λ {a} {b} {f} → trans-hom E (leftId E) (sym-hom E (rightId E)) }

assocNat← : ∀{B₀ B₁ ℓ‴ C₀ C₁ ℓ D₀ D₁ ℓ′ E₀ E₁ ℓ″} {B : Category B₀ B₁ ℓ‴} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {E : Category E₀ E₁ ℓ″} {F : Functor.Functor B C} {G : Functor.Functor C D} {H : Functor.Functor D E} → Nat (Functor.compose H (Functor.compose G F)) (Functor.compose (Functor.compose H G) F)
assocNat← {C = C} {D} {E} {F} = record {
  component = λ X → id E ;
  naturality = λ {a} {b} {f} → trans-hom E (leftId E) (sym-hom E (rightId E)) }

leftIdNat→ : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} → Nat (Functor.compose (Functor.identity D) F) F
leftIdNat→ {C = C} {D} {F} = record {
  component = λ X → id D ;
  naturality = λ {a} {b} {f} → trans-hom D (leftId D) (sym-hom D (rightId D)) }

leftIdNat← : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} → Nat F (Functor.compose (Functor.identity D) F)
leftIdNat← {C = C} {D} {F} = record {
  component = λ X → id D ;
  naturality = λ {a} {b} {f} → trans-hom D (leftId D) (sym-hom D (rightId D)) }

rightIdNat→ : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} → Nat (Functor.compose F (Functor.identity C)) F
rightIdNat→ {C = C} {D} {F} = record {
  component = λ X → id D ;
  naturality = λ {a} {b} {f} → trans-hom D (leftId D) (sym-hom D (rightId D)) }

rightIdNat← : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} → Nat F (Functor.compose F (Functor.identity C))
rightIdNat← {C = C} {D} {F} = record {
  component = λ X → id D ;
  naturality = λ {a} {b} {f} → trans-hom D (leftId D) (sym-hom D (rightId D)) }

module Export where
  infixl 6 _F∘N_ _N∘F_
  _F∘N_ = composeFN
  _N∘F_ = composeNF

  Hom[_][_,-] = HomFunctor
  Hom[_][-,_] = HomFunctorOp
  HomNat[_][_,-] = HomNat
  HomNat[_][-,_] = HomNatOp

  [_,_] : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} (C : Category C₀ C₁ ℓ) → (D : Category D₀ D₁ ℓ′) → Category _ _ _
  [_,_] = FunCat

  PSh[_] : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) → Category _ _ _
  PSh[_] {_} {C₁} {ℓ} C = [ op C , Setoids {C₁} {ℓ} ]
