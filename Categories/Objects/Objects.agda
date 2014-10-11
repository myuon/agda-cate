open import Categories.Category

module Categories.Objects.Objects {C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) where

open import Level
open import Data.Empty
import Data.Fin as Fin
open import Categories.Functor
open import Categories.Nat
open import Categories.Limit
open import Categories.Categories.Index
open import Categories.Reasoning

open Category C
open Functor
open Nat

record TerminalObject : Set (C₀ ⊔ C₁ ⊔ ℓ) where
  field
    1-obj : Obj

  field
    to-1 : (a : Obj) → a ~> 1-obj
    universality : (a : Obj) → (h : a ~> 1-obj) → h ≈ to-1 a

1! : Set _
1! = TerminalObject

TerminalObject-as-Limit : (F : Functor 𝟘 C) (L : Limit F) → TerminalObject
TerminalObject-as-Limit F L = record
  { 1-obj = Limit.limit L
  ; to-1 = \a → Limit.cone-map L (liftCone a)
  ; universality = universality-1
  }
  where
    liftCone : (a : Obj) → Cone F
    liftCone a = record
      { vertex = a
      ; side = record { component = \(); naturality = λ {a₁} {b} → λ {} } }

    universality-1 : (a : Obj) (h : a ~> Limit.limit L) → h ≈ Limit.cone-map L (liftCone a)
    universality-1 a h = Limit.universality L (liftCone a) h (eqArrow lemma)
      where
        lemma : {r : Category.Obj 𝟘} → component ([ 𝟘 , C ] [ Cone.side (Limit.limiting-cone L) ∘ DiagonalLift 𝟘 C h ]) r ≈ component (Cone.side (liftCone a)) r
        lemma {()}

record BinaryProduct (a₁ a₂ : Obj) : Set (C₀ ⊔ C₁ ⊔ ℓ) where
  field
    a₁×a₂ : Obj
    p₁ : a₁×a₂ ~> a₁
    p₂ : a₁×a₂ ~> a₂

  field
    ⟨_,_⟩ : {z : Obj} → (f₁ : z ~> a₁) → (f₂ : z ~> a₂) → z ~> a₁×a₂
    commute₁ : {z : Obj} → (f₁ : z ~> a₁) → (f₂ : z ~> a₂) → p₁ ∘ ⟨ f₁ , f₂ ⟩ ≈ f₁
    commute₂ : {z : Obj} → (f₁ : z ~> a₁) → (f₂ : z ~> a₂) → p₂ ∘ ⟨ f₁ , f₂ ⟩ ≈ f₂
    universality : {z : Obj} → (f₁ : z ~> a₁) → (f₂ : z ~> a₂) → (h : z ~> a₁×a₂)
      → p₁ ∘ h ≈ f₁ → p₂ ∘ h ≈ f₂ → h ≈ ⟨ f₁ , f₂ ⟩

_×_ : (a b : Obj) → Set _
a × b = BinaryProduct a b

{-
BinaryProduct-as-Limit : (F : Functor 𝟚-discrete C) (L : Limit F) → BinaryProduct (fobj F Fin.zero) (fobj F (Fin.suc Fin.zero))
BinaryProduct-as-Limit F L = record
  { a₁×a₂ = Limit.limit L
  ; p₁ = component (Cone.side (Limit.limiting-cone L)) Fin.zero
  ; p₂ = component (Cone.side (Limit.limiting-cone L)) (Fin.suc Fin.zero)

  ; ⟨_,_⟩ = \f₁ f₂ → Limit.cone-map L (liftCone f₁ f₂)
  ; commute₁ = {!!}
  ; commute₂ = {!!}
  ; universality = {!!}
  }
  where
    private
      a₁ = fobj F Fin.zero
      a₂ = fobj F (Fin.suc Fin.zero)

    liftCone : {z : Obj} (f₁ : z ~> a₁) (f₂ : z ~> a₂) → Cone F
    liftCone {z} f₁ f₂ = record
      { vertex = z
      ; side = record { component = component-cone; naturality = naturality-cone }
      }
      where
        component-cone : (r : Category.Obj 𝟚-discrete) → z ~> (fobj F r)
        component-cone Fin.zero = f₁
        component-cone (Fin.suc Fin.zero) = f₂
        component-cone (Fin.suc (Fin.suc ()))

        open ≈-lemmas

        naturality-cone : {a b : Category.Obj 𝟚-discrete} {f : 𝟚-discrete [ a ~> b ]} → component-cone b ∘ fmap Δ[ z ] f ≈ fmap F f ∘ component-cone a
        naturality-cone {Fin.zero} {Fin.zero} {id-𝟚} = let open ≈-Reasoning C in
          begin
            component-cone Fin.zero ∘ id ↓⟨ rightIdentity ⟩
            f₁ ↑⟨ leftIdentity ⟩
            id ∘ f₁ ↑⟨ ≈-composite-refl C (preserveId F) ⟩
            fmap F id-𝟚 ∘ component-cone Fin.zero
          ∎
        naturality-cone {Fin.zero} {Fin.suc _} {()}
        naturality-cone {Fin.suc Fin.zero} {Fin.zero} {()}
        naturality-cone {Fin.suc Fin.zero} {Fin.suc Fin.zero} {f} = {!!}
        naturality-cone {_} {Fin.suc (Fin.suc ())} {_}
        naturality-cone {Fin.suc (Fin.suc ())} {_}
-}
