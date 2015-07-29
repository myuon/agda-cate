module Adjoint where

open import Level
open import Data.Product

open import Basic
open import Category
import Functor
import Nat

open Category.Category
open Functor.Functor
open Nat.Nat
open Nat.Export

record Adjoint {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} (F : Functor.Functor C D) (G : Functor.Functor D C) : Set (suc ℓ ⊔ suc C₁ ⊔ C₀ ⊔ suc ℓ′ ⊔ suc D₁ ⊔ D₀) where
  field
    adjunction : {x : Obj C} {a : Obj D} → Setoids [ LiftSetoid {b = C₁ ⊔ D₁} {ℓ′ = ℓ ⊔ ℓ′} (Homsetoid D (fobj F x) a) ≅ LiftSetoid {b = C₁ ⊔ D₁} {ℓ′ = ℓ ⊔ ℓ′} (Homsetoid C x (fobj G a)) ]

  adjunct-→-Map : {x : Obj C} {a : Obj D} → Map.Map (Homsetoid D (fobj F x) a) (Homsetoid C x (fobj G a))
  adjunct-→-Map {x} {a} = lowerMap {d = C₁ ⊔ D₁} {ℓ″ = ℓ ⊔ ℓ′} (_[_≅_].map-→ (adjunction {x} {a}))

  adjunct-←-Map : {x : Obj C} {a : Obj D} → Map.Map (Homsetoid C x (fobj G a)) (Homsetoid D (fobj F x) a)
  adjunct-←-Map {x} {a} = lowerMap {d = C₁ ⊔ D₁} {ℓ″ = ℓ ⊔ ℓ′} (_[_≅_].map-← (adjunction {x} {a}))

  adjunct-→ : {x : Obj C} {a : Obj D} → Hom D (fobj F x) a → Hom C x (fobj G a)
  adjunct-→ f = Map.mapping (lowerMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (_[_≅_].map-→ adjunction)) f

  adjunct-← : {x : Obj C} {a : Obj D} → Hom C x (fobj G a) → Hom D (fobj F x) a
  adjunct-← f = Map.mapping (lowerMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (_[_≅_].map-← adjunction)) f

  adjunct-→←≈id : {x : Obj C} {a : Obj D} {f : Hom C x (fobj G a)} → C [ adjunct-→ (adjunct-← f) ≈ f ]
  adjunct-→←≈id {x} {a} {f} = lower (proj₁ (_[_≅_].proof adjunction) (lift f))

  adjunct-←→≈id : {x : Obj C} {a : Obj D} {f : Hom D (fobj F x) a} → D [ adjunct-← (adjunct-→ f) ≈ f ]
  adjunct-←→≈id {x} {a} {f} = lower (proj₂ (_[_≅_].proof adjunction) (lift f))

  field
    natural-in-→-C : {x y : Obj C} {a : Obj D} {f : Hom C y x} →
      Setoids [ Setoids [ liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ C ][ f ,-] (fobj G a)) ∘ _[_≅_].map-→ adjunction ] ≈ Setoids [ _[_≅_].map-→ adjunction ∘ liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ D ][ fmap F f ,-] a) ] ]
    natural-in-→-D : {x : Obj C} {a b : Obj D} {f : Hom D a b} →
      Setoids [ Setoids [ liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ C ][-, fmap G f ] x) ∘ _[_≅_].map-→ adjunction ] ≈ Setoids [ _[_≅_].map-→ adjunction ∘ liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ D ][-, f ] (fobj F x)) ] ]

  natural-in-←-C : {x y : Obj C} {a : Obj D} {f : Hom C y x} →
    Setoids [ Setoids [ liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ D ][ fmap F f ,-] a) ∘ _[_≅_].map-← adjunction ] ≈ Setoids [ _[_≅_].map-← adjunction ∘ liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ C ][ f ,-] (fobj G a)) ] ]
  natural-in-←-C {x} {y} {a} {f} = begin⟨ Setoids ⟩
    Setoids [ Ffa ∘ _[_≅_].map-← adjunction ] ≈⟨ ≈-composite Setoids {f = Ffa} {g = Setoids [ Setoids [ adj← ∘ fGa ] ∘ _[_≅_].map-→ adjunction ]} {h = adj→₂} {i = adj→₂} lem-1 (refl-hom Setoids {f = _[_≅_].map-← adjunction}) ⟩
    Setoids [ Setoids [ adj← ∘ fGa ] ∘ Setoids [ _[_≅_].map-→ adjunction ∘ _[_≅_].map-← adjunction ] ] ≈⟨ ≈-composite Setoids {f = Setoids [ adj← ∘ fGa ]} {g = Setoids [ adj← ∘ fGa ]} {h = Setoids [ _[_≅_].map-→ adjunction ∘ _[_≅_].map-← adjunction ]} {i = id Setoids} (refl-hom Setoids {f = Setoids [ adj← ∘ fGa ]}) (proj₁ (_[_≅_].proof adjunction)) ⟩
    Setoids [ adj← ∘ fGa ]
    ∎
    where
      Ffa = liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ D ][ fmap F f ,-] a)
      fGa = liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ C ][ f ,-] (fobj G a))
      adj← = _[_≅_].map-← adjunction
      adj→₂ = _[_≅_].map-← adjunction
      adj→ = _[_≅_].map-→ adjunction

      lem-1 : Setoids [ Ffa ≈ Setoids [ Setoids [ adj← ∘ fGa ] ∘ _[_≅_].map-→ adjunction ] ]
      lem-1 = begin⟨ Setoids ⟩
        Ffa ≈⟨ leftId Setoids {f = Ffa} ⟩
        Setoids [ id Setoids ∘ Ffa ] ≈⟨ ≈-composite Setoids {f = id Setoids} {g = Setoids [ adj← ∘ adj→ ]} {h = Ffa} {i = Ffa} (sym-hom Setoids {f = Setoids [ adj← ∘ adj→ ]} {g = id Setoids} (proj₂ (_[_≅_].proof adjunction))) (refl-hom Setoids {f = Ffa}) ⟩
        Setoids [ adj← ∘ Setoids [ adj→ ∘ Ffa ] ] ≈⟨ ≈-composite Setoids {f = adj←} {g = adj←} {h = Setoids [ adj→ ∘ Ffa ]} {i = Setoids [ fGa ∘ _[_≅_].map-→ adjunction ]} (refl-hom Setoids {f = adj←}) (sym-hom Setoids {f = Setoids [ fGa ∘ _[_≅_].map-→ adjunction ]} {g = Setoids [ adj→ ∘ Ffa ]} natural-in-→-C) ⟩
        Setoids [ Setoids [ _[_≅_].map-← adjunction ∘ liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ C ][ f ,-] (fobj G a)) ] ∘ _[_≅_].map-→ adjunction ]
        ∎

  natural-in-←-D : {x : Obj C} {a b : Obj D} {f : Hom D a b} →
    Setoids [ Setoids [ liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ D ][-, f ] (fobj F x)) ∘ _[_≅_].map-← adjunction ] ≈ Setoids [ _[_≅_].map-← adjunction ∘ liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ C ][-, fmap G f ] x) ] ]
  natural-in-←-D {x} {a} {b} {f} = begin⟨ Setoids ⟩
    Setoids [ fFx ∘ adj←a ] ≈⟨ ≈-composite Setoids {f = fFx} {g = Setoids [ Setoids [ adj←b ∘ Gfx ] ∘ adj→a ]} {h = adj←a} {i = adj←a} lem-1 (refl-hom Setoids {f = adj←a}) ⟩
    Setoids [ Setoids [ adj←b ∘ Gfx ] ∘ Setoids [ adj→a ∘ adj←a ] ] ≈⟨ ≈-composite Setoids {f = Setoids [ adj←b ∘ Gfx ]} {g = Setoids [ adj←b ∘ Gfx ]} {h = Setoids [ adj→a ∘ adj←a ]} {i = id Setoids} (refl-hom Setoids {f = Setoids [ adj←b ∘ Gfx ]}) (proj₁ (_[_≅_].proof adjunction)) ⟩
    Setoids [ adj←b ∘ Gfx ]
    ∎
    where
      fFx = liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ D ][-, f ] (fobj F x))
      Gfx = liftMap {d = C₁ ⊔ D₁} {ℓ″  = ℓ ⊔ ℓ′} (component HomNat[ C ][-, fmap G f ] x)
      adj←a = _[_≅_].map-← adjunction
      adj←b = _[_≅_].map-← adjunction
      adj→a = _[_≅_].map-→ adjunction
      adj→b = _[_≅_].map-→ adjunction

      lem-1 : Setoids [ fFx ≈ Setoids [ Setoids [ adj←b ∘ Gfx ] ∘ adj→a ] ]
      lem-1 = begin⟨ Setoids ⟩
        fFx ≈⟨ ≈-composite Setoids {f = id Setoids} {g = Setoids [ adj←b ∘ adj→b ]} {h = fFx} {i = fFx} (sym-hom Setoids {f = Setoids [ adj←b ∘ adj→b ]} {g = id Setoids} (proj₂ (_[_≅_].proof adjunction))) (refl-hom Setoids {f = fFx}) ⟩
        Setoids [ adj←b ∘ Setoids [ adj→b ∘ fFx ] ] ≈⟨ ≈-composite Setoids {f = adj←b} {g = adj←b} {h = Setoids [ adj→b ∘ fFx ]} {i = Setoids [ Gfx ∘ adj→a ]} (refl-hom Setoids {f = adj←b}) (sym-hom Setoids {f = Setoids [ Gfx ∘ adj→a ]} {g = Setoids [ adj→b ∘ fFx ]} natural-in-→-D) ⟩
        Setoids [ Setoids [ adj←b ∘ Gfx ] ∘ adj→a ]
        ∎

  naturality-point-←-C : {x y : Obj C} {a : Obj D} {f : Hom C y x} {k : Hom C x (fobj G a)} → D [ D [ adjunct-← k ∘ fmap F f ] ≈ adjunct-← (C [ k ∘ f ]) ]
  naturality-point-←-C = λ {x} {y} {a} {f} {k} → lower (natural-in-←-C (lift k))

  naturality-point-→-C : {x y : Obj C} {a : Obj D} {f : Hom C y x} {k : Hom D (fobj F x) a} → C [ C [ adjunct-→ k ∘ f ] ≈ adjunct-→ (D [ k ∘ fmap F f ]) ]
  naturality-point-→-C = λ {x} {y} {a} {f} {k} → lower (natural-in-→-C (lift k))

  naturality-point-←-D : {x : Obj C} {a b : Obj D} {f : Hom D a b} {k : Hom C x (fobj G a)} → D [ D [ f ∘ adjunct-← k ] ≈ adjunct-← (C [ fmap G f ∘ k ]) ]
  naturality-point-←-D = λ {x} {y} {a} {f} {k} → lower (natural-in-←-D (lift k))

  naturality-point-→-D : {x : Obj C} {a b : Obj D} {f : Hom D a b} {k : Hom D (fobj F x) a} → C [ C [ fmap G f ∘ adjunct-→ k ] ≈ adjunct-→ (D [ f ∘ k ]) ]
  naturality-point-→-D = λ {x} {y} {a} {f} {k} → lower (natural-in-→-D (lift k))

open Adjoint

unit : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → Adjoint F G → Nat.Nat (Functor.identity C) (Functor.compose G F)
unit {C₀} {C₁} {ℓ} {D₀} {D₁} {ℓ′} {C} {D} {F} {G} F⊣G = record {
  component = λ X → adjunct-→ F⊣G (id D) ;
  naturality = λ {a} {b} {f} → begin⟨ C ⟩
    C [ adjunct-→ F⊣G (id D) ∘ fmap (Functor.identity C) f ] ≈⟨ naturality-point-→-C F⊣G ⟩
    adjunct-→ F⊣G (D [ id D ∘ fmap F (fmap (Functor.identity C) f) ]) ≈⟨ Map.preserveEq (adjunct-→-Map F⊣G) (leftId D) ⟩
    adjunct-→ F⊣G (fmap F f) ≈⟨ Map.preserveEq (adjunct-→-Map F⊣G) (sym-hom D (rightId D)) ⟩
    adjunct-→ F⊣G (D [ fmap F f ∘ id D ]) ≈⟨ sym-hom C (naturality-point-→-D F⊣G) ⟩
    C [ fmap (Functor.compose G F) f ∘ adjunct-→ F⊣G (id D) ]
    ∎ }

counit : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → Adjoint F G → Nat.Nat (Functor.compose F G) (Functor.identity D)
counit {C₀} {C₁} {ℓ} {D₀} {D₁} {ℓ′} {C} {D} {F} {G} F⊣G = record {
  component = λ X → adjunct-← F⊣G (id C) ;
  naturality = λ {a} {b} {f} → begin⟨ D ⟩
    D [ adjunct-← F⊣G (id C) ∘ fmap (Functor.compose F G) f ] ≈⟨ naturality-point-←-C F⊣G ⟩
    adjunct-← F⊣G (C [ id C ∘ fmap G f ]) ≈⟨ Map.preserveEq (adjunct-←-Map F⊣G) (leftId C) ⟩
    adjunct-← F⊣G (fmap G f) ≈⟨ Map.preserveEq (adjunct-←-Map F⊣G) (sym-hom C (rightId C)) ⟩
    adjunct-← F⊣G (C [ fmap G f ∘ id C ]) ≈⟨ sym-hom D (naturality-point-←-D F⊣G) ⟩
    D [ fmap (Functor.identity D) f ∘ adjunct-← F⊣G (id C) ]
    ∎}

Unit-universal : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → Adjoint F G → Set _
Unit-universal {C = C} {D} {F} {G} adj = ∀ {X : Obj C} {A : Obj D} (f : Hom C X (fobj G A)) → ∃! (λ x y → D [ x ≈ y ]) (λ (h : Hom D (fobj F X) A) → C [ C [ fmap G h ∘ component (unit adj) X ] ≈ f ])

unit-universality : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → (adj : Adjoint F G) → Unit-universal adj
unit-universality {C = C} {D} {F} {G} F⊣G {X} {A} f = 
  adjunct-← F⊣G f , lem-1 , lem-2
  where
    lem-1 = begin⟨ C ⟩
      C [ fmap G (adjunct-← F⊣G f) ∘ component (unit F⊣G) X ] ≈⟨ naturality-point-→-D F⊣G ⟩
      adjunct-→ F⊣G (D [ adjunct-← F⊣G f ∘ id D ]) ≈⟨ Map.preserveEq (adjunct-→-Map F⊣G) (≈-composite D (refl-hom D) (sym-hom D (preserveId F))) ⟩
      adjunct-→ F⊣G (D [ adjunct-← F⊣G f ∘ fmap F (id C) ]) ≈⟨ sym-hom C (naturality-point-→-C F⊣G) ⟩
      C [ adjunct-→ F⊣G (adjunct-← F⊣G f) ∘ id C ] ≈⟨ rightId C ⟩
      adjunct-→ F⊣G (adjunct-← F⊣G f) ≈⟨ adjunct-→←≈id F⊣G ⟩
      f
      ∎

    lem-2 = λ {y} eq → begin⟨ D ⟩
      adjunct-← F⊣G f ≈⟨ Map.preserveEq (adjunct-←-Map F⊣G) (sym-hom C eq) ⟩
      adjunct-← F⊣G (C [ fmap G y ∘ component (unit F⊣G) X ]) ≈⟨ sym-hom D (naturality-point-←-D (F⊣G)) ⟩
      D [ y ∘ adjunct-← F⊣G (adjunct-→ F⊣G (id D)) ] ≈⟨ ≈-composite D (refl-hom D) (adjunct-←→≈id F⊣G) ⟩
      D [ y ∘ id D ] ≈⟨ rightId D ⟩
      y
      ∎

Counit-universal : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → Adjoint F G → Set _
Counit-universal {C = C} {D} {F} {G} adj = ∀ {X : Obj C} {A : Obj D} (h : Hom D (fobj F X) A) → ∃! (λ x y → C [ x ≈ y ]) (λ (f : Hom C X (fobj G A)) → D [ D [ component (counit adj) A ∘ fmap F f ] ≈ h ])

counit-universality : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → (adj : Adjoint F G) → Counit-universal adj
counit-universality {C = C} {D} {F} {G} F⊣G = λ {X} {A} h →
  adjunct-→ F⊣G h , lem-1 , lem-2
  where
    lem-1 = λ {A} {h} → begin⟨ D ⟩
      D [ component (counit F⊣G) A ∘ fmap F (adjunct-→ F⊣G h) ] ≈⟨ naturality-point-←-C F⊣G ⟩
      adjunct-← F⊣G (C [ id C ∘ adjunct-→ F⊣G h ]) ≈⟨ Map.preserveEq (adjunct-←-Map F⊣G) (leftId C) ⟩
      adjunct-← F⊣G (adjunct-→ F⊣G h) ≈⟨ adjunct-←→≈id F⊣G ⟩
      h
      ∎

    lem-2 = λ {A} {h} {y} eq → begin⟨ C ⟩
      adjunct-→ F⊣G h ≈⟨ Map.preserveEq (adjunct-→-Map F⊣G) (sym-hom D eq) ⟩
      adjunct-→ F⊣G (D [ component (counit F⊣G) A ∘ fmap F y ]) ≈⟨ sym-hom C (naturality-point-→-C F⊣G) ⟩
      C [ adjunct-→ F⊣G (component (counit F⊣G) A) ∘ y ] ≈⟨ ≈-composite C (adjunct-→←≈id F⊣G) (refl-hom C) ⟩
      C [ id C ∘ y ] ≈⟨ leftId C ⟩
      y
      ∎

TriangularL : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → Nat.Nat (Functor.identity C) (Functor.compose G F) → Nat.Nat (Functor.compose F G) (Functor.identity D) → Set _
TriangularL {C = C} {D} {F} {G} η ε = [ C , D ] [ Nat.compose (Nat.compose Nat.leftIdNat→ (ε N∘F F)) (Nat.compose (Nat.assocNat← {F = F} {G} {F}) (Nat.compose (F F∘N η) Nat.rightIdNat←)) ≈ id [ C , D ] ]

triangularL-point : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → (η : Nat.Nat (Functor.identity C) (Functor.compose G F)) → (ε : Nat.Nat (Functor.compose F G) (Functor.identity D)) → {a : Obj C} → (triL : TriangularL {F = F} {G} η ε) → D [ D [ component (ε N∘F F) a ∘ component (F F∘N η) a ] ≈ id D {fobj F a} ]
triangularL-point {C = C} {D} {F} {G} η ε {a} triL = begin⟨ D ⟩
  D [ component (ε N∘F F) a ∘ component (F F∘N η) a ] ≈⟨ sym-hom D (≈-composite D (leftId D) (trans-hom D (leftId D) (rightId D))) ⟩
  D [ D [ id D ∘ component (ε N∘F F) a ] ∘ D [ id D ∘ D [ component (F F∘N η) a ∘ id D ] ] ] ≈⟨ triL {a} ⟩
  id D
  ∎

triangularL : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → (adj : Adjoint F G) → TriangularL {F = F} {G} (unit adj) (counit adj)
triangularL {C = C} {D} {F} {G} adj = λ {a} →
  begin⟨ D ⟩
    component (Nat.compose εF (Nat.compose (Nat.assocNat← {F = F} {G} {F}) Fη)) a
  ≈⟨ ≈-composite D (leftId D) (trans-hom D (leftId D) (rightId D)) ⟩
    D [ component ε (fobj F a) ∘ fmap F (component η a) ]
  ≈⟨ proj₁ (proj₂ (counit-universality adj (id D))) ⟩
    id D
  ≈⟨ refl-hom D ⟩
    component (id [ C , D ] {F}) a
  ∎
  where
    ε = counit adj
    η = unit adj
    εF = Nat.compose Nat.leftIdNat→ (counit adj N∘F F)
    Fη = Nat.compose {F = F} (F F∘N unit adj) Nat.rightIdNat←

TriangularR : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → Nat.Nat (Functor.identity C) (Functor.compose G F) → Nat.Nat (Functor.compose F G) (Functor.identity D) → Set _
TriangularR {C = C} {D} {F} {G} η ε = [ D , C ] [ Nat.compose (Nat.compose Nat.rightIdNat→ (G F∘N ε)) (Nat.compose (Nat.assocNat→ {F = G} {F} {G}) (Nat.compose (η N∘F G) Nat.leftIdNat←)) ≈ id [ D , C ] ]

triangularR : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → (adj : Adjoint F G) → TriangularR {F = F} (unit adj) (counit adj)
triangularR {C = C} {D} {F} {G} adj = λ {a} → begin⟨ C ⟩
  component (Nat.compose Gε (Nat.compose (Nat.assocNat→ {F = G} {F} {G}) ηG)) a ≈⟨ ≈-composite C (leftId C) (trans-hom C (leftId C) (rightId C)) ⟩
  C [ fmap G (component ε a) ∘ component η (fobj G a) ] ≈⟨ proj₁ (proj₂ (unit-universality adj (id C))) ⟩
  id C ≈⟨ refl-hom C ⟩
  component (id [ D , C ] {G}) a
  ∎
  where
    ε = counit adj
    η = unit adj
    Gε = Nat.compose {H = G} Nat.rightIdNat→ (G F∘N counit adj)
    ηG = Nat.compose (unit adj N∘F G) Nat.leftIdNat←

triangularR-point : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → (η : Nat.Nat (Functor.identity C) (Functor.compose G F)) → (ε : Nat.Nat (Functor.compose F G) (Functor.identity D)) → {a : Obj D} → (triR : TriangularR {F = F} {G} η ε) → C [ C [ component (G F∘N ε) a ∘ component (η N∘F G) a ] ≈ id C {fobj G a} ]
triangularR-point {C = C} {D} {F} {G} η ε {a} triR = begin⟨ C ⟩
  C [ component (G F∘N ε) a ∘ component (η N∘F G) a ] ≈⟨ sym-hom C (≈-composite C (leftId C) (trans-hom C (leftId C) (rightId C))) ⟩
  C [ C [ id C ∘ component (G F∘N ε) a ] ∘ C [ id C ∘ C [ component (η N∘F G) a ∘ id C ] ] ] ≈⟨ triR {a = a} ⟩
  id C
  ∎

unit-triangular-holds-adjoint : ∀ {C₀ C₁ ℓ D₀ D₁ ℓ′} {C : Category C₀ C₁ ℓ} {D : Category D₀ D₁ ℓ′} {F : Functor.Functor C D} {G : Functor.Functor D C} → (η : Nat.Nat (Functor.identity C) (Functor.compose G F)) → (ε : Nat.Nat (Functor.compose F G) (Functor.identity D)) → TriangularL {F = F} η ε → TriangularR {F = F} η ε → Adjoint F G
unit-triangular-holds-adjoint {C = C} {D} {F} {G} η ε triL triR = record {
  adjunction = λ {x} {a} → record {
    map-→ = record {
      mapping = λ Fx→a → lift (C [ fmap G (lower Fx→a) ∘ component η x ]) ;
      preserveEq = λ {x′} {y} x₂ → lift (≈-composite C (Functor.preserveEq G (lower x₂)) (refl-hom C)) } ;
    map-← = record {
      mapping = λ x→Ga → lift (D [ component ε a ∘ fmap F (lower x→Ga) ]) ;
      preserveEq = λ {x′} {y} x₂ → lift (≈-composite D (refl-hom D) (Functor.preserveEq F (lower x₂))) } ;
    proof = p1 , p2 } ;
  natural-in-→-C = λ {x} {y} {a} {f} Fx→a → lift (begin⟨ C ⟩
    C [ C [ fmap G (lower Fx→a) ∘ component η x ] ∘ f ] ≈⟨ assoc C ⟩
    C [ fmap G (lower Fx→a) ∘ C [ component η x ∘ f ] ] ≈⟨ ≈-composite C (refl-hom C) (naturality η) ⟩
    C [ fmap G (lower Fx→a) ∘ C [ fmap G (fmap F f) ∘ component η y ] ] ≈⟨ sym-hom C (assoc C) ⟩
    C [ C [ fmap G (lower Fx→a) ∘ fmap G (fmap F f) ] ∘ component η y ] ≈⟨ ≈-composite C (sym-hom C (preserveComp G)) (refl-hom C) ⟩
    C [ fmap G (D [ lower Fx→a ∘ fmap F f ]) ∘ component η y ]
    ∎) ;
  natural-in-→-D = λ {x} {a} {b} {f} Fx→a → lift (begin⟨ C ⟩
    C [ fmap G f ∘ C [ fmap G (lower Fx→a) ∘ component η x ] ] ≈⟨ sym-hom C (assoc C) ⟩
    C [ C [ fmap G f ∘ fmap G (lower Fx→a) ] ∘ component η x ] ≈⟨ ≈-composite C (sym-hom C (preserveComp G)) (refl-hom C) ⟩
    C [ fmap G (D [ f ∘ lower Fx→a ]) ∘ component η x ]
    ∎) }

  where
    p1 = λ {x} {a} x→Ga → lift (begin⟨ C ⟩
      C [ fmap G (D [ component ε a ∘ fmap F (lower x→Ga) ]) ∘ component η x ] ≈⟨ ≈-composite C (preserveComp G) (refl-hom C) ⟩
      C [ C [ fmap G (component ε a) ∘ fmap G (fmap F (lower x→Ga)) ] ∘ component η x ] ≈⟨ assoc C ⟩
      C [ fmap G (component ε a) ∘ C [ fmap G (fmap F (lower x→Ga)) ∘ component η x ] ] ≈⟨ ≈-composite C (refl-hom C) (sym-hom C (naturality η)) ⟩
      C [ fmap G (component ε a) ∘ C [ component η (fobj G a) ∘ (lower x→Ga) ] ] ≈⟨ sym-hom C (assoc C) ⟩
      C [ C [ fmap G (component ε a) ∘ component η (fobj G a) ] ∘ (lower x→Ga) ] ≈⟨ ≈-composite C (triangularR-point {F = F} η ε {a = a} triR) (refl-hom C) ⟩
      C [ id C ∘ (lower x→Ga) ] ≈⟨ leftId C ⟩
      lower x→Ga
      ∎)

    p2 = λ {x} {a} Fx→a → lift (begin⟨ D ⟩
      D [ component ε a ∘ fmap F (C [ fmap G (lower Fx→a) ∘ component η x ]) ] ≈⟨ ≈-composite D (refl-hom D) (preserveComp F) ⟩
      D [ component ε a ∘ D [ fmap F (fmap G (lower Fx→a)) ∘ fmap F (component η x) ] ] ≈⟨ sym-hom D (assoc D) ⟩
      D [ D [ component ε a ∘ fmap F (fmap G (lower Fx→a)) ] ∘ fmap F (component η x) ] ≈⟨ ≈-composite D (naturality ε) (refl-hom D) ⟩
      D [ D [ lower Fx→a ∘ component ε (fobj F x) ] ∘ fmap F (component η x) ] ≈⟨ assoc D ⟩
      D [ lower Fx→a ∘ D [ component ε (fobj F x) ∘ fmap F (component η x) ] ] ≈⟨ ≈-composite D (refl-hom D) (triangularL-point {F = F} η ε {a = x} triL) ⟩
      D [ lower Fx→a ∘ id D ] ≈⟨ rightId D ⟩
      lower Fx→a
      ∎)

module Export where
  _⊣_ = Adjoint


