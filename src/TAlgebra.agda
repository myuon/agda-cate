module TAlgebra where

open import Level
open import Data.Product
open import Relation.Binary
open Setoid

open import Basic
open import Category
import Functor
import Nat
import Adjoint
open import Monad

open Category.Category
open Functor.Functor
open Nat.Nat
open Adjoint.Export
open Monad.Monad

record TAlgebra {C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} (T : Monad C) : Set (C₀ ⊔ C₁ ⊔ ℓ) where
  field
    Tobj : Obj C
    Tmap : Hom C (fobj (MFunctor T) Tobj) Tobj

  field
    join-fmap-alg : C [ C [ Tmap ∘ component (Mjoin T) Tobj ] ≈ C [ Tmap ∘ fmap (MFunctor T) Tmap ] ]
    alg-unit : C [ C [ Tmap ∘ component (Munit T) Tobj ] ≈ id C ]

open TAlgebra

record TAlgMap {C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} {T : Monad C} (a b : TAlgebra T) : Set (C₁ ⊔ ℓ) where
  field
    Thom : Hom C (Tobj a) (Tobj b)

  field
    hom-comm : C [ C [ Tmap b ∘ fmap (MFunctor T) Thom ] ≈ C [ Thom ∘ Tmap a ] ]

open TAlgMap

compose : ∀ {C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} {T : Monad C} {a b c : TAlgebra T} → TAlgMap b c → TAlgMap a b → TAlgMap a c
compose {C = C} {T} {a} {b} {c} f g = record {
  Thom = C [ Thom f ∘ Thom g ] ;
  hom-comm = begin⟨ C ⟩
    C [ Tmap c ∘ fmap (MFunctor T) (C [ Thom f ∘ Thom g ]) ] ≈⟨ ≈-composite C (refl-hom C) (preserveComp (MFunctor T)) ⟩
    C [ Tmap c ∘ C [ fmap (MFunctor T) (Thom f) ∘ fmap (MFunctor T) (Thom g) ] ] ≈⟨ sym-hom C (assoc C) ⟩
    C [ C [ Tmap c ∘ fmap (MFunctor T) (Thom f) ] ∘ fmap (MFunctor T) (Thom g) ] ≈⟨ ≈-composite C (hom-comm f) (refl-hom C) ⟩
    C [ C [ Thom f ∘ Tmap b ] ∘ fmap (MFunctor T) (Thom g) ] ≈⟨ assoc C ⟩
    C [ Thom f ∘ C [ Tmap b ∘ fmap (MFunctor T) (Thom g) ] ] ≈⟨ ≈-composite C (refl-hom C) (hom-comm g) ⟩
    C [ Thom f ∘ C [ Thom g ∘ Tmap a ] ] ≈⟨ sym-hom C (assoc C) ⟩
    C [ C [ Thom f ∘ Thom g ] ∘ Tmap a ]
  ∎ }

identity : ∀ {C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} {T : Monad C} {a : TAlgebra T} → TAlgMap a a
identity {C = C} {T} {a} = record {
  Thom = id C ;
  hom-comm = begin⟨ C ⟩
    C [ Tmap a ∘ fmap (MFunctor T) (id C) ] ≈⟨ ≈-composite C (refl-hom C) (preserveId (MFunctor T)) ⟩
    C [ Tmap a ∘ id C ] ≈⟨ rightId C ⟩
    Tmap a ≈⟨ sym-hom C (leftId C) ⟩
    C [ id C ∘ Tmap a ]
  ∎ }

T-Algs : ∀ {C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} (T : Monad C) → Category _ _ _
T-Algs {C = C} T = record {
  Obj = TAlgebra T;
  Homsetoid = λ a b → record {
    Carrier = TAlgMap a b ;
    _≈_ = λ f g → C [ Thom f ≈ Thom g ] ;
    isEquivalence = record { refl = refl-hom C ; sym = sym-hom C ; trans = trans-hom C } };
  comp = compose;
  id = identity;
  leftId = leftId C;
  rightId = rightId C;
  assoc = assoc C;
  ≈-composite = ≈-composite C }

Free-TAlg : ∀ {C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} (T : Monad C) → Functor.Functor C (T-Algs T)
Free-TAlg {C = C} T = record {
  fobj = λ x → record {
    Tobj = fobj (MFunctor T) x ;
    Tmap = component (Mjoin T) x ;
    join-fmap-alg = join_join T ;
    alg-unit = unit_MFunctor T } ;
  fmapsetoid = λ {a} {b} → record {
    mapping = λ x → record {
      Thom = fmap (MFunctor T) x ;
      hom-comm = naturality (Mjoin T) } ;
    preserveEq = Functor.preserveEq (MFunctor T) } ;
  preserveId = preserveId (MFunctor T) ;
  preserveComp = preserveComp (MFunctor T) }

Forgetful-TAlg : ∀ {C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} (T : Monad C) → Functor.Functor (T-Algs T) C
Forgetful-TAlg {C = C} T = record {
  fobj = Tobj ;
  fmapsetoid = record { mapping = Thom ; preserveEq = λ x≈y → x≈y } ;
  preserveId = refl-hom C ;
  preserveComp = refl-hom C }

Free⊣Forgetful-TAlg : ∀ {C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} (T : Monad C) → Free-TAlg T ⊣ Forgetful-TAlg T
Free⊣Forgetful-TAlg T = record {
  adjunction = λ {x} {a} → record {
    map-→ = record {
      mapping = λ Tx→a → lift {!  fmap (MFunctor T) Tx→a!} ;
      preserveEq = {!!} } ;
    map-← = {!!} ; proof = {!!} } ;
  natural-in-→-C = {!!} ;
  natural-in-→-D = {!!} }

