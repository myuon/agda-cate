module Topology.Topology where

module Topology where
 
open import Level
open import Function
open import Data.Empty
import Data.Fin as Fin
open import Data.Product
open import Data.Unit
open import Relation.Nullary
open import Relation.Unary renaming (∅ to ∅-zero; U to U-zero)

∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (\x → B) = ∃ x ∶ B

separation : ∀{a b} {A : Set a} → (A → Set b) → Pred A _
separation P = P

syntax separation (\a → P) = [ a ∣ P ]

Union : ∀{a b ℓ} {A : Set a} {I : Set b} → (I → Pred A ℓ) → Pred A (b ⊔ ℓ)
Union F = [ a ∣ ∃ i ∶ a ∈ F i ]

Intersect : ∀{a b ℓ} {A : Set a} {I : Set b} → (I → Pred A ℓ) → Pred A (b ⊔ ℓ)
Intersect F = [ a ∣ (∀ i → a ∈ F i) ]

record TopSpace a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    set : Set a
    OpenFamily : Pred (Pred set ℓ) ℓ

  field
    ∅-open : (\_ → Lift ⊥) ∈ OpenFamily
    all-open : (\_ → Lift ⊤) ∈ OpenFamily
    ⋃-open : {A : Set} (f : A → ∃ OpenFamily) → Union (proj₁ ∘ f) ∈ OpenFamily
    ∩-open : ∀{n} (f : Fin.Fin n → ∃ OpenFamily) → Intersect (proj₁ ∘ f) ∈ OpenFamily

  ∅ : Pred set ℓ
  ∅ = \_ → Lift ⊥

  U : Pred set ℓ
  U = \_ → Lift ⊤

open TopSpace

Discrete : ∀{a ℓ} (X : Set a) → TopSpace a ℓ
Discrete {_} {ℓ} X = record
  { set = X ; OpenFamily = openFamily
  ; ∅-open = _ ; all-open = _
  ; ⋃-open = _ ; ∩-open = _
  }
  where
    openFamily : Pred (Pred X ℓ) ℓ
    openFamily _ = Lift ⊤

