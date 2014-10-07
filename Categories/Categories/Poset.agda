module Categories.Categories.Poset {c ℓ₁ ℓ₂} where

open import Level
open import Relation.Binary
open import Relation.Unary
open import Categories.Category

open Category
open Poset renaming (_≈_ to _≈P_; _≤_ to _[_≤_])

Poset-A-Category : (P : Poset c ℓ₁ ℓ₂) → Category c ℓ₂ ℓ₂
Poset-A-Category P = record
  { Obj = Carrier P
  ; _~>_ = \A B → P [ A ≤ B ]
  ; _∘_ = \{A} {B} {C} B≤C A≤B → trans P A≤B B≤C
  ; _≈_ = \{A} {B} _ _ → P [ A ≤ B ]
  ; id = refl P

  ; leftIdentity = λ {A} {B} {f} → f
  ; rightIdentity = λ {A} {B} {f} → f
  ; assoc = \{A} {B} {C} {D} {A≤B} {B≤C} {C≤D} → trans P (trans P A≤B B≤C) C≤D
  ; equivalence = \{A} {B} → record { refl = λ {x} → x; sym = λ {i} {j} z → z; trans = λ {i} {j} {k} _ z → z }
  ; ≈-composite = \B≤C A≤B → trans P A≤B B≤C
  }

