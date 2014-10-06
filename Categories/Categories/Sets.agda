module Categories.Categories.Sets where

open import Function
open import Relation.Binary
open import Relation.Binary.Core
open import Categories.Category

Sets : ∀{ℓ} → Category _ _ ℓ
Sets {ℓ} = record
  { Obj = Set ℓ
  ; _~>_ = hom-Sets
  ; _∘_ = _∘′_
  ; _≈_ = _≡_
  ; id = id

  ; leftIdentity = refl
  ; rightIdentity = refl
  ; assoc = refl
  ; equivalence = record { refl = refl; sym = sym-Sets; trans = trans-Sets }
  ; ≈-composite = ≈-composite-Sets
  }
  where
    hom-Sets : (A B : Set ℓ) → Set _
    hom-Sets A B = A → B

    sym-Sets : ∀{a} {A : Set a} → Symmetric {_} {_} {A} _≡_
    sym-Sets refl = refl

    trans-Sets : ∀{a} {A : Set a} → Transitive {_} {_} {A} _≡_
    trans-Sets refl refl = refl

    ≈-composite-Sets : {a b c : Set ℓ} {f g : hom-Sets b c} {h i : hom-Sets a b}
      → f ≡ g → h ≡ i → (_∘′_ f h) ≡ (_∘′_ g i)
    ≈-composite-Sets refl refl = refl


