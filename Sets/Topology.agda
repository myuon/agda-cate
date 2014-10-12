module Sets.Topology where

open import Level
open import Function
import Data.Fin as Fin
open import Data.Product hiding (_,_)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Unary hiding (∅)
open import Sets.Sets

record TopSpace a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    set : Set a
    OpenFamily : FamilyOfSet {a} {ℓ} set

  field
    ∅-open : ∅ ∈ OpenFamily
    all-open : U₀ ∈ OpenFamily
    ⋃-open : {A : Set} (f : A → ∃ OpenFamily) → Union {a} (proj₁ ∘ f) ∈ OpenFamily
    ∩-open : ∀{n} (f : Fin.Fin n → ∃ OpenFamily) → Intersect {a} (proj₁ ∘ f) ∈ OpenFamily

  neighborhood : set → FamilyOfSet {a} {ℓ} set
  neighborhood x = \U → (x ∈ U) × (U ∈ OpenFamily)

module Interior (X : TopSpace zero zero) where
  open TopSpace X

  Int : Subset set → Subset set
  Int U = UnionOf (\V → V ∈ OpenFamily × V ⊆ U)

  Prop-Int-1 : ∀ U → U ∈ OpenFamily → Int U ⊆ U
  Prop-Int-1 U f g = {!!}

Discrete : ∀{a ℓ} (X : Set a) → TopSpace a ℓ
Discrete {_} {ℓ} X = record
  { set = X ; OpenFamily = openFamily
  ; ∅-open = _ ; all-open = _
  ; ⋃-open = _ ; ∩-open = _
  }
  where
    openFamily : Pred (Pred X ℓ) ℓ
    openFamily = U₀

