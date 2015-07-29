module Yoneda where

open import Level
open import Data.Product
open import Relation.Binary
import Relation.Binary.SetoidReasoning as SetR
open Setoid renaming (_≈_ to eqSetoid)

open import Basic
open import Category
import Functor
import Nat

open Category.Category
open Functor.Functor
open Nat.Nat
open Nat.Export

yoneda : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) → Functor.Functor C PSh[ C ]
yoneda C = record {
  fobj = λ x → Hom[ C ][-, x ] ;
  fmapsetoid = λ {A} {B} → record { mapping = λ f → HomNat[ C ][-, f ] ; preserveEq = λ {x} {y} x₁ x₂ → begin⟨ C ⟩
    Map.mapping (component HomNat[ C ][-, x ] _) x₂ ≈⟨ refl-hom C ⟩
    C [ x ∘ x₂ ] ≈⟨ ≈-composite C x₁ (refl-hom C) ⟩
    C [ y ∘ x₂ ] ≈⟨ refl-hom C ⟩
    Map.mapping (component HomNat[ C ][-, y ] _) x₂
  ∎ } ;
  preserveId = λ x → leftId C ;
  preserveComp = λ x → assoc C
  }

YonedaLemma : ∀{C₀ C₁ ℓ} {C : Category C₀ C₁ ℓ} {F : Obj PSh[ C ]} {X : Obj C} → Setoids [ Homsetoid [ op C , Setoids ] (fobj (yoneda C) X) F ≅ LiftSetoid {C₁} {suc (suc ℓ) ⊔ (suc (suc C₁) ⊔ suc C₀)} {ℓ} {C₀ ⊔ C₁ ⊔ ℓ} (fobj F X) ]
YonedaLemma {C₀} {C₁} {ℓ} {C} {F} {X} = record {
  map-→ = nat→obj ;
  map-← = obj→nat ;
  proof = obj→obj≈id , nat→nat≈id }
  where
    nat→obj : Map.Map (Homsetoid [ op C , Setoids ] (fobj (yoneda C) X) F) (LiftSetoid (fobj F X))
    nat→obj = record {
      mapping = λ α → lift (Map.mapping (component α X) (id C)) ;
      preserveEq = λ x≈y → lift (x≈y (id C)) }

    obj→nat : Map.Map (LiftSetoid (fobj F X)) (Homsetoid [ op C , Setoids ] (fobj (yoneda C) X) F)
    obj→nat = record {
      mapping = λ a → record {
        component = component-map a ;
        naturality = λ {c} {d} {f} x → SetR.begin⟨ fobj F d ⟩
          Map.mapping (Setoids [ component-map a d ∘ fmap (fobj (yoneda C) X) f ]) x SetR.≈⟨ refl (fobj F d) ⟩
          Map.mapping (Map.mapping (fmapsetoid F) (C [ x ∘ f ])) (lower a) SetR.≈⟨ (preserveComp F) (lower a) ⟩
          Map.mapping (Map.mapping (fmapsetoid F) f) (Map.mapping (Map.mapping (fmapsetoid F) x) (lower a)) SetR.≈⟨ refl (fobj F d) ⟩
          Map.mapping (Setoids [ fmap F f ∘ component-map a c ]) x
        SetR.∎} ;
      preserveEq = λ {x} {y} x≈y f → SetR.begin⟨ fobj F _ ⟩
        Map.mapping (component-map x _) f SetR.≈⟨ refl (fobj F _) ⟩
        Map.mapping (Map.mapping (fmapsetoid F) f) (lower x) SetR.≈⟨ Map.preserveEq (fmap F f) (lower x≈y) ⟩
        Map.mapping (Map.mapping (fmapsetoid F) f) (lower y) SetR.≈⟨ refl (fobj F _) ⟩
        Map.mapping (component-map y _) f
        SetR.∎}
      where
        component-map = λ a b → record {
          mapping = λ u → Map.mapping (fmap F u) (lower a) ;
          preserveEq = λ {x} {y} x≈y → SetR.begin⟨ fobj F b ⟩
            Map.mapping (fmap F x) (lower a) SetR.≈⟨ (Functor.preserveEq F x≈y) (lower a) ⟩
            Map.mapping (fmap F y) (lower a)
          SetR.∎
          }

    obj→obj≈id : Setoids [ Setoids [ nat→obj ∘ obj→nat ] ≈ id Setoids ]
    obj→obj≈id = λ x → lift (SetR.begin⟨ fobj F X ⟩
      lower (Map.mapping (Setoids [ nat→obj ∘ obj→nat ]) x) SetR.≈⟨ refl (fobj F X) ⟩
      Map.mapping (Map.mapping (fmapsetoid F) (id C)) (lower x) SetR.≈⟨ (preserveId F) (lower x) ⟩
      lower x SetR.≈⟨ refl (fobj F X) ⟩
      lower (Map.mapping {A = LiftSetoid {ℓ′ = ℓ} (fobj F X)} (id Setoids) x)
      SetR.∎)

    nat→nat≈id : Setoids [ Setoids [ obj→nat ∘ nat→obj ] ≈ id Setoids ]
    nat→nat≈id α f = SetR.begin⟨ fobj F _ ⟩
      Map.mapping (component (Map.mapping (Setoids [ obj→nat ∘ nat→obj ]) α) _) f SetR.≈⟨ refl (fobj F _) ⟩
      Map.mapping (Setoids [ fmap F f ∘ component α X ]) (id C) SetR.≈⟨ lemma (id C) ⟩
      Map.mapping (Setoids [ component α (dom C f) ∘ fmap (fobj (yoneda C) X) f ]) (id C) SetR.≈⟨ Map.preserveEq (component α (dom C f)) (leftId C) ⟩
      Map.mapping (component α (dom C f)) f SetR.≈⟨ refl (fobj F _) ⟩
      Map.mapping (component (Map.mapping (id Setoids {Homsetoid [ (op C) , Setoids ] _ _}) α) (dom C f)) f
      SetR.∎
      where
        lemma : Setoids [ Setoids [ fmap F f ∘ component α X ] ≈ Setoids [ component α (dom C f) ∘ fmap (fobj (yoneda C) X) f ] ]
        lemma = sym-hom Setoids {f = Setoids [ component α (dom C f) ∘ fmap (fobj (yoneda C) X) f ]} {g = Setoids [ fmap F f ∘ component α X ]} (naturality α)

