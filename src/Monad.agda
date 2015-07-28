module Monad where

open import Level

open import Category
import Functor
import Nat
import Adjoint

open Category.Category
open Functor.Functor
open Nat.Export
open Nat.Nat
open Adjoint.Export

record Monad {c₀ c₁ ℓ} (C : Category c₀ c₁ ℓ) : Set (suc (c₀ ⊔ c₁ ⊔ ℓ)) where
  field
    MFunctor : Functor.Functor C C
    Mjoin : Nat.Nat (Functor.exp MFunctor 2) MFunctor
    Munit : Nat.Nat (Functor.identity C) MFunctor

  field
    join_join : {A : Obj C} → C [ C [ component Mjoin A ∘ component Mjoin (fobj MFunctor A) ] ≈ C [ component Mjoin A ∘ fmap MFunctor (component Mjoin A) ] ]
    unit_MFunctor : {A : Obj C} → C [ C [ component Mjoin A ∘ component Munit (fobj MFunctor A) ] ≈ id C ]
    MFunctor_unit : {A : Obj C} → C [ C [ component Mjoin A ∘ fmap MFunctor (component Munit A) ] ≈ id C ]

Adjoint-Monad : ∀ {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} {F : Functor.Functor C D} {G : Functor.Functor D C} → F ⊣ G → Monad C
Adjoint-Monad {C = C} {D} {F} {G} F⊣G = record {
  MFunctor = T;
  Mjoin = record {
    component = λ X → component (G F∘N ε N∘F F) X ;
    naturality = λ {a} {b} {f} → begin⟨ C ⟩
      C [ component (G F∘N ε N∘F F) b ∘ fmap G (fmap (Functor.compose F T) f) ] ≈⟨ sym-hom C (preserveComp G) ⟩
      fmap G (D [ component ε (fobj F b) ∘ fmap (Functor.compose F G) (fmap F f) ]) ≈⟨ Functor.preserveEq G (naturality ε) ⟩
      fmap G (D [ fmap F f ∘ component ε (fobj F a) ]) ≈⟨ preserveComp G ⟩
      C [ fmap T f ∘ component (G F∘N ε N∘F F) a ]
      ∎ };
  Munit = Adjoint.unit F⊣G;
  join_join = λ {A} → begin⟨ C ⟩
    C [ component (G F∘N ε N∘F F) A ∘ component (G F∘N ε N∘F F) (fobj T A) ] ≈⟨ sym-hom C (preserveComp G) ⟩
    fmap G (D [ component ε (fobj F A) ∘ component ε (fobj (Functor.compose F G) (fobj F A)) ]) ≈⟨ Functor.preserveEq G (sym-hom D (naturality ε)) ⟩
    fmap G (D [ component ε (fobj F A) ∘ fmap (Functor.compose F G) (component ε (fobj F A)) ]) ≈⟨ preserveComp G ⟩
    C [ component (G F∘N ε N∘F F) A ∘ fmap T (component (G F∘N ε N∘F F) A) ]
    ∎ ;
  unit_MFunctor = λ {A} → begin⟨ C ⟩
    C [ component (G F∘N ε N∘F F) A ∘ component η (fobj T A) ] ≈⟨ refl-hom C ⟩
    C [ component (G F∘N ε) (fobj F A) ∘ component (η N∘F G) (fobj F A) ] ≈⟨ sym-hom C (≈-composite C (leftId C) (trans-hom C (leftId C) (rightId C))) ⟩
    C [ C [ id C ∘ component (G F∘N ε) (fobj F A) ] ∘ C [ id C ∘ C [ component (η N∘F G) (fobj F A) ∘ id C ] ] ] ≈⟨ refl-hom C ⟩
    component (Nat.compose (Nat.compose {H = G} Nat.rightIdNat→ (G F∘N ε)) (Nat.compose (Nat.assocNat→ {F = G} {F} {G}) (Nat.compose (η N∘F G) Nat.leftIdNat←))) (fobj F A) ≈⟨ Adjoint.triangularR F⊣G {fobj F A} ⟩
    component (id [ D , C ] {G}) (fobj F A) ≈⟨ refl-hom C ⟩
    id C
    ∎ ;
  MFunctor_unit = λ {A} → begin⟨ C ⟩
    C [ component (G F∘N ε N∘F F) A ∘ fmap T (component η A) ] ≈⟨ refl-hom C ⟩
    C [ fmap G (component ε (fobj F A)) ∘ fmap G (fmap F (component η A)) ] ≈⟨ sym-hom C (preserveComp G) ⟩
    fmap G (D [ component ε (fobj F A) ∘ fmap F (component η A) ]) ≈⟨ Functor.preserveEq G (≈-composite D (sym-hom D (leftId D)) (sym-hom D (trans-hom D (leftId D) (rightId D)))) ⟩
    fmap G (D [ D [ id D ∘ component ε (fobj F A) ] ∘ D [ id D ∘ D [ fmap F (component η A) ∘ id D ] ] ]) ≈⟨ Functor.preserveEq G (refl-hom D) ⟩
    fmap G (component (Nat.compose (Nat.compose Nat.leftIdNat→ (Adjoint.counit F⊣G N∘F F)) (Nat.compose {F = F} (Nat.assocNat← {F = F} {G} {F}) (Nat.compose {F = F} (F F∘N Adjoint.unit F⊣G) Nat.rightIdNat←))) A ) ≈⟨ Functor.preserveEq G (Adjoint.triangularL F⊣G {A}) ⟩
    fmap G (component (id [ C , D ] {F}) A) ≈⟨ preserveId G ⟩
    id C
    ∎ }
  where
    T = Functor.compose G F
    η = Adjoint.unit F⊣G
    ε = Adjoint.counit F⊣G

