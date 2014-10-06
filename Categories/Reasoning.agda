module Categories.Reasoning where

open import Level
open import Relation.Binary
open import Categories.Category
open Category

module ≈-Reasoning {C₀ C₁ ℓ : Level} (C : Category C₀ C₁ ℓ) where
  refl-hom : {a b : Obj C} {x : C [ a ~> b ]} → C [ x ≈ x ]
  refl-hom = IsEquivalence.refl (equivalence C)

  trans-hom : {a b : Obj C} {x y z : C [ a ~> b ]}
    → C [ x ≈ y ] → C [ y ≈ z ] → C [ x ≈ z ]
  trans-hom b c = IsEquivalence.trans (equivalence C) b c

  infixr 2 _∎
  infixr 2 _≈⟨_⟩_ _≈⟨⟩_ _↓⟨_⟩_ _↑⟨_⟩_
  infix 1 begin_

  data _IsRelatedTo_ {a b : Obj C} (x y : C [ a ~> b ])
    : Set (suc (C₀ ⊔ C₁ ⊔ ℓ)) where
    relTo : C [ x ≈ y ] → x IsRelatedTo y
  begin_ : {a b : Obj C} {x y : C [ a ~> b ]} → x IsRelatedTo y → C [ x ≈ y ]
  begin (relTo x≈y) = x≈y
 
  _≈⟨_⟩_ : {a b : Obj C} (x : C [ a ~> b ]) → {y z : C [ a ~> b ]} → 
    C [ x ≈ y ] → y IsRelatedTo z → x IsRelatedTo z
  _ ≈⟨ x≈y ⟩ relTo y≈z = relTo (trans-hom x≈y y≈z)

  _↓⟨_⟩_ : {a b : Obj C} (x : C [ a ~> b ]) → {y z : C [ a ~> b ]} → 
    C [ x ≈ y ] → y IsRelatedTo z → x IsRelatedTo z
  _↓⟨_⟩_ = _≈⟨_⟩_

  _↑⟨_⟩_ : {a b : Obj C} (x : C [ a ~> b ]) → {y z : C [ a ~> b ]} → 
    C [ y ≈ x ] → y IsRelatedTo z → x IsRelatedTo z
  _ ↑⟨ y≈x ⟩ relTo y≈z = relTo (trans-hom (IsEquivalence.sym (equivalence C) y≈x) y≈z)

  _≈⟨⟩_ : {a b : Obj C} (x : C [ a ~> b ]) → {y : C [ a ~> b ]} → x IsRelatedTo y → x IsRelatedTo y
  _ ≈⟨⟩ x∼y = x∼y

  _∎ : {a b : Obj C} (x : C [ a ~> b ]) → x IsRelatedTo x
  _∎ _ = relTo refl-hom
