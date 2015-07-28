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

record Adjoint {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} (F : Functor.Functor C D) (G : Functor.Functor D C) : Set (suc ℓ ⊔ suc C₁ ⊔ C₀) where
  field
    adjunction : {x : Obj C} {a : Obj D} → Setoids [ Homsetoid D (fobj F x) a ≅ Homsetoid C x (fobj G a) ]

  adjunct-→ : {x : Obj C} {a : Obj D} → Hom D (fobj F x) a → Hom C x (fobj G a)
  adjunct-→ f = Map.mapping (_[_≅_].map-→ adjunction) f

  adjunct-← : {x : Obj C} {a : Obj D} → Hom C x (fobj G a) → Hom D (fobj F x) a
  adjunct-← f = Map.mapping (_[_≅_].map-← adjunction) f

  adjunct-→←≈id : {x : Obj C} {a : Obj D} {f : Hom C x (fobj G a)} → C [ adjunct-→ (adjunct-← f) ≈ f ]
  adjunct-→←≈id {x} {a} {f} = proj₁ (_[_≅_].proof adjunction) f

  adjunct-←→≈id : {x : Obj C} {a : Obj D} {f : Hom D (fobj F x) a} → D [ adjunct-← (adjunct-→ f) ≈ f ]
  adjunct-←→≈id {x} {a} {f} = proj₂ (_[_≅_].proof adjunction) f

  field
    natural-in-→-C : {x y : Obj C} {a : Obj D} {f : Hom C y x} →
      Setoids [ Setoids [ component HomNat[ C ][ f ,-] (fobj G a) ∘ _[_≅_].map-→ adjunction ] ≈ Setoids [ _[_≅_].map-→ adjunction ∘ component HomNat[ D ][ fmap F f ,-] a ] ]
    natural-in-→-D : {x : Obj C} {a b : Obj D} {f : Hom D a b} →
      Setoids [ Setoids [ component HomNat[ C ][-, fmap G f ] x ∘ _[_≅_].map-→ adjunction ] ≈ Setoids [ _[_≅_].map-→ adjunction ∘ component HomNat[ D ][-, f ] (fobj F x) ] ]

  natural-in-←-C : {x y : Obj C} {a : Obj D} {f : Hom C y x} →
    Setoids [ Setoids [ component HomNat[ D ][ fmap F f ,-] a ∘ _[_≅_].map-← adjunction ] ≈ Setoids [ _[_≅_].map-← adjunction ∘ component HomNat[ C ][ f ,-] (fobj G a) ] ]
  natural-in-←-C {x} {y} {a} {f} = begin⟨ Setoids ⟩
    Setoids [ Ffa ∘ _[_≅_].map-← adjunction ] ≈⟨ ≈-composite Setoids {f = Ffa} {g = Setoids [ Setoids [ adj← ∘ fGa ] ∘ _[_≅_].map-→ adjunction ]} {h = adj→₂} {i = adj→₂} lem-1 (refl-hom Setoids {f = _[_≅_].map-← adjunction}) ⟩
    Setoids [ Setoids [ adj← ∘ fGa ] ∘ Setoids [ _[_≅_].map-→ adjunction ∘ _[_≅_].map-← adjunction ] ] ≈⟨ ≈-composite Setoids {f = Setoids [ adj← ∘ fGa ]} {g = Setoids [ adj← ∘ fGa ]} {h = Setoids [ _[_≅_].map-→ adjunction ∘ _[_≅_].map-← adjunction ]} {i = id Setoids} (refl-hom Setoids {f = Setoids [ adj← ∘ fGa ]}) (proj₁ (_[_≅_].proof adjunction)) ⟩
    Setoids [ adj← ∘ fGa ]
    ∎
    where
      Ffa = component HomNat[ D ][ fmap F f ,-] a
      fGa = component HomNat[ C ][ f ,-] (fobj G a)
      adj← = _[_≅_].map-← adjunction
      adj→₂ = _[_≅_].map-← adjunction
      adj→ = _[_≅_].map-→ adjunction

      lem-1 : Setoids [ Ffa ≈ Setoids [ Setoids [ adj← ∘ fGa ] ∘ _[_≅_].map-→ adjunction ] ]
      lem-1 = begin⟨ Setoids ⟩
        Ffa ≈⟨ leftId Setoids {f = Ffa} ⟩
        Setoids [ id Setoids ∘ Ffa ] ≈⟨ ≈-composite Setoids {f = id Setoids} {g = Setoids [ adj← ∘ adj→ ]} {h = Ffa} {i = Ffa} (sym-hom Setoids {f = Setoids [ adj← ∘ adj→ ]} {g = id Setoids} (proj₂ ((_[_≅_].proof {C₀ = suc (C₁ ⊔ ℓ)}) adjunction))) (refl-hom Setoids {f = Ffa}) ⟩
        Setoids [ adj← ∘ Setoids [ adj→ ∘ Ffa ] ] ≈⟨ ≈-composite Setoids {f = adj←} {g = adj←} {h = Setoids [ adj→ ∘ Ffa ]} {i = Setoids [ fGa ∘ _[_≅_].map-→ adjunction ]} (refl-hom Setoids {f = adj←}) (sym-hom Setoids {f = Setoids [ fGa ∘ _[_≅_].map-→ adjunction ]} {g = Setoids [ adj→ ∘ Ffa ]} natural-in-→-C) ⟩
        Setoids [ Setoids [ _[_≅_].map-← adjunction ∘ component HomNat[ C ][ f ,-] (fobj G a) ] ∘ _[_≅_].map-→ adjunction ]
        ∎

  natural-in-←-D : {x : Obj C} {a b : Obj D} {f : Hom D a b} →
    Setoids [ Setoids [ component HomNat[ D ][-, f ] (fobj F x) ∘ _[_≅_].map-← adjunction ] ≈ Setoids [ _[_≅_].map-← adjunction ∘ component HomNat[ C ][-, fmap G f ] x ] ]
  natural-in-←-D {x} {a} {b} {f} = begin⟨ Setoids ⟩
    Setoids [ fFx ∘ adj←a ] ≈⟨ ≈-composite Setoids {f = fFx} {g = Setoids [ Setoids [ adj←b ∘ Gfx ] ∘ adj→a ]} {h = adj←a} {i = adj←a} lem-1 (refl-hom Setoids {f = adj←a}) ⟩
    Setoids [ Setoids [ adj←b ∘ Gfx ] ∘ Setoids [ adj→a ∘ adj←a ] ] ≈⟨ ≈-composite Setoids {f = Setoids [ adj←b ∘ Gfx ]} {g = Setoids [ adj←b ∘ Gfx ]} {h = Setoids [ adj→a ∘ adj←a ]} {i = id Setoids} (refl-hom Setoids {f = Setoids [ adj←b ∘ Gfx ]}) (proj₁ (_[_≅_].proof adjunction)) ⟩
    Setoids [ adj←b ∘ Gfx ]
    ∎
    where
      fFx = component HomNat[ D ][-, f ] (fobj F x)
      Gfx = component HomNat[ C ][-, fmap G f ] x
      adj←a = _[_≅_].map-← adjunction
      adj←b = _[_≅_].map-← adjunction
      adj→a = _[_≅_].map-→ adjunction
      adj→b = _[_≅_].map-→ adjunction

      lem-1 : Setoids [ fFx ≈ Setoids [ Setoids [ adj←b ∘ Gfx ] ∘ adj→a ] ]
      lem-1 = begin⟨ Setoids ⟩
        fFx ≈⟨ ≈-composite Setoids {f = id Setoids} {g = Setoids [ adj←b ∘ adj→b ]} {h = fFx} {i = fFx} (sym-hom Setoids {f = Setoids [ adj←b ∘ adj→b ]} {g = id Setoids} (proj₂ (_[_≅_].proof {C₀ = suc (C₁ ⊔ ℓ)} adjunction))) (refl-hom Setoids {f = fFx}) ⟩
        Setoids [ adj←b ∘ Setoids [ adj→b ∘ fFx ] ] ≈⟨ ≈-composite Setoids {f = adj←b} {g = adj←b} {h = Setoids [ adj→b ∘ fFx ]} {i = Setoids [ Gfx ∘ adj→a ]} (refl-hom Setoids {f = adj←b}) (sym-hom Setoids {f = Setoids [ Gfx ∘ adj→a ]} {g = Setoids [ adj→b ∘ fFx ]} natural-in-→-D) ⟩
        Setoids [ Setoids [ adj←b ∘ Gfx ] ∘ adj→a ]
        ∎

  naturality-point-←-C : {x y : Obj C} {a : Obj D} {f : Hom C y x} {k : Hom C x (fobj G a)} → D [ D [ adjunct-← k ∘ fmap F f ] ≈ adjunct-← (C [ k ∘ f ]) ]
  naturality-point-←-C = λ {x} {y} {a} {f} {k} → natural-in-←-C k

  naturality-point-→-C : {x y : Obj C} {a : Obj D} {f : Hom C y x} {k : Hom D (fobj F x) a} → C [ C [ adjunct-→ k ∘ f ] ≈ adjunct-→ (D [ k ∘ fmap F f ]) ]
  naturality-point-→-C = λ {x} {y} {a} {f} {k} → natural-in-→-C k

  naturality-point-←-D : {x : Obj C} {a b : Obj D} {f : Hom D a b} {k : Hom C x (fobj G a)} → D [ D [ f ∘ adjunct-← k ] ≈ adjunct-← (C [ fmap G f ∘ k ]) ]
  naturality-point-←-D = λ {x} {y} {a} {f} {k} → natural-in-←-D k

  naturality-point-→-D : {x : Obj C} {a b : Obj D} {f : Hom D a b} {k : Hom D (fobj F x) a} → C [ C [ fmap G f ∘ adjunct-→ k ] ≈ adjunct-→ (D [ f ∘ k ]) ]
  naturality-point-→-D = λ {x} {y} {a} {f} {k} → natural-in-→-D k

open Adjoint

unit : ∀ {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} {F : Functor.Functor C D} {G : Functor.Functor D C} → Adjoint F G → Nat.Nat (Functor.identity C) (Functor.compose G F)
unit {C = C} {D} {F} {G} F⊣G = record {
  component = λ X → adjunct-→ F⊣G (id D) ;
  naturality = λ {a} {b} {f} → begin⟨ C ⟩
    C [ adjunct-→ F⊣G (id D) ∘ fmap (Functor.identity C) f ] ≈⟨ naturality-point-→-C F⊣G ⟩
    adjunct-→ F⊣G (D [ id D ∘ fmap F (fmap (Functor.identity C) f) ]) ≈⟨ Map.preserveEq (_[_≅_].map-→ (adjunction F⊣G)) (leftId D) ⟩
    adjunct-→ F⊣G (fmap F f) ≈⟨ Map.preserveEq (_[_≅_].map-→ (adjunction F⊣G)) (sym-hom D (rightId D)) ⟩
    adjunct-→ F⊣G (D [ fmap F f ∘ id D ]) ≈⟨ sym-hom C (naturality-point-→-D F⊣G) ⟩
    C [ fmap (Functor.compose G F) f ∘ adjunct-→ F⊣G (id D) ]
    ∎ }

counit : ∀ {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} {F : Functor.Functor C D} {G : Functor.Functor D C} → Adjoint F G → Nat.Nat (Functor.compose F G) (Functor.identity D)
counit {C = C} {D} {F} {G} F⊣G = record {
  component = λ X → adjunct-← F⊣G (id C) ;
  naturality = λ {a} {b} {f} → begin⟨ D ⟩
    D [ adjunct-← F⊣G (id C) ∘ fmap (Functor.compose F G) f ] ≈⟨ naturality-point-←-C F⊣G ⟩
    adjunct-← F⊣G (C [ id C ∘ fmap G f ]) ≈⟨ Map.preserveEq (_[_≅_].map-← (adjunction F⊣G)) (leftId C) ⟩
    adjunct-← F⊣G (fmap G f) ≈⟨ Map.preserveEq (_[_≅_].map-← (adjunction F⊣G)) (sym-hom C (rightId C)) ⟩
    adjunct-← F⊣G (C [ fmap G f ∘ id C ]) ≈⟨ sym-hom D (naturality-point-←-D F⊣G) ⟩
    D [ fmap (Functor.identity D) f ∘ adjunct-← F⊣G (id C) ]
    ∎}

Unit-universal : ∀ {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} {F : Functor.Functor C D} {G : Functor.Functor D C} → Adjoint F G → Set _
Unit-universal {C = C} {D} {F} {G} adj = ∀ {X : Obj C} {A : Obj D} (f : Hom C X (fobj G A)) → ∃! (λ x y → D [ x ≈ y ]) (λ (h : Hom D (fobj F X) A) → C [ C [ fmap G h ∘ component (unit adj) X ] ≈ f ])

unit-universality : ∀ {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} {F : Functor.Functor C D} {G : Functor.Functor D C} → (adj : Adjoint F G) → Unit-universal adj
unit-universality {C = C} {D} {F} {G} F⊣G {X} {A} f = 
  adjunct-← F⊣G f , lem-1 , lem-2
  where
    lem-1 = begin⟨ C ⟩
      C [ fmap G (adjunct-← F⊣G f) ∘ component (unit F⊣G) X ] ≈⟨ naturality-point-→-D F⊣G ⟩
      adjunct-→ F⊣G (D [ adjunct-← F⊣G f ∘ id D ]) ≈⟨ Map.preserveEq (_[_≅_].map-→ (adjunction F⊣G)) (≈-composite D (refl-hom D) (sym-hom D (preserveId F))) ⟩
      adjunct-→ F⊣G (D [ adjunct-← F⊣G f ∘ fmap F (id C) ]) ≈⟨ sym-hom C (naturality-point-→-C F⊣G) ⟩
      C [ adjunct-→ F⊣G (adjunct-← F⊣G f) ∘ id C ] ≈⟨ rightId C ⟩
      adjunct-→ F⊣G (adjunct-← F⊣G f) ≈⟨ adjunct-→←≈id F⊣G ⟩
      f
      ∎

    lem-2 = λ {y} eq → begin⟨ D ⟩
      adjunct-← F⊣G f ≈⟨ Map.preserveEq (_[_≅_].map-← (adjunction F⊣G)) (sym-hom C eq) ⟩
      adjunct-← F⊣G (C [ fmap G y ∘ component (unit F⊣G) X ]) ≈⟨ sym-hom D (naturality-point-←-D (F⊣G)) ⟩
      D [ y ∘ adjunct-← F⊣G (adjunct-→ F⊣G (id D)) ] ≈⟨ ≈-composite D (refl-hom D) (adjunct-←→≈id F⊣G) ⟩
      D [ y ∘ id D ] ≈⟨ rightId D ⟩
      y
      ∎

Counit-universal : ∀ {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} {F : Functor.Functor C D} {G : Functor.Functor D C} → Adjoint F G → Set _
Counit-universal {C = C} {D} {F} {G} adj = ∀ {X : Obj C} {A : Obj D} (h : Hom D (fobj F X) A) → ∃! (λ x y → C [ x ≈ y ]) (λ (f : Hom C X (fobj G A)) → D [ D [ component (counit adj) A ∘ fmap F f ] ≈ h ])

counit-universality : ∀ {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} {F : Functor.Functor C D} {G : Functor.Functor D C} → (adj : Adjoint F G) → Counit-universal adj
counit-universality {C = C} {D} {F} {G} F⊣G = λ {X} {A} h →
  adjunct-→ F⊣G h , lem-1 , lem-2
  where
    lem-1 = λ {A} {h} → begin⟨ D ⟩
      D [ component (counit F⊣G) A ∘ fmap F (adjunct-→ F⊣G h) ] ≈⟨ naturality-point-←-C F⊣G ⟩
      adjunct-← F⊣G (C [ id C ∘ adjunct-→ F⊣G h ]) ≈⟨ Map.preserveEq (_[_≅_].map-← (adjunction F⊣G)) (leftId C) ⟩
      adjunct-← F⊣G (adjunct-→ F⊣G h) ≈⟨ adjunct-←→≈id F⊣G ⟩
      h
      ∎

    lem-2 = λ {A} {h} {y} eq → begin⟨ C ⟩
      adjunct-→ F⊣G h ≈⟨ Map.preserveEq (_[_≅_].map-→ (adjunction F⊣G)) (sym-hom D eq) ⟩
      adjunct-→ F⊣G (D [ component (counit F⊣G) A ∘ fmap F y ]) ≈⟨ sym-hom C (naturality-point-→-C F⊣G) ⟩
      C [ adjunct-→ F⊣G (component (counit F⊣G) A) ∘ y ] ≈⟨ ≈-composite C (adjunct-→←≈id F⊣G) (refl-hom C) ⟩
      C [ id C ∘ y ] ≈⟨ leftId C ⟩
      y
      ∎

triangularL : ∀ {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} {F : Functor.Functor C D} {G : Functor.Functor D C} → (adj : Adjoint F G) → [ C , D ] [ Nat.compose (Nat.compose Nat.leftIdNat→ (counit adj N∘F F)) (Nat.compose (Nat.assocNat← {F = F} {G} {F}) (Nat.compose (F F∘N unit adj) Nat.rightIdNat←)) ≈ id [ C , D ] ]
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

triangularR : ∀ {C₀ C₁ ℓ} {C D : Category C₀ C₁ ℓ} {F : Functor.Functor C D} {G : Functor.Functor D C} → (adj : Adjoint F G) → [ D , C ] [ Nat.compose (Nat.compose Nat.rightIdNat→ (G F∘N counit adj)) (Nat.compose (Nat.assocNat→ {F = G} {F} {G}) (Nat.compose (unit adj N∘F G) Nat.leftIdNat←)) ≈ id [ D , C ] ]
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

module Export where
  _⊣_ = Adjoint



