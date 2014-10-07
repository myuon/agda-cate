module Categories.Categories.Index where

open import Level
open import Data.Empty
import Data.Fin as Fin
import Data.Nat as N
open import Relation.Binary
open import Categories.Category
open import Categories.Functor

open Category
open Functor

𝟘 : Category _ _ zero
𝟘 = record
  { Obj = ∅
  ; _~>_ = \_ _ → ∅
  ; _∘_ = λ {}
  ; _≈_ = λ {A} {B} _ → λ ()
  ; id = λ {}

  ; leftIdentity = λ {A} {B} → λ {}
  ; rightIdentity = λ {A} {B} → λ {}
  ; assoc = λ {A} {B} {C} {D} {f} {g} → λ {}
  ; equivalence = λ {A} {B} → record { refl = λ {} ; sym = λ {} ; trans = λ {} }
  ; ≈-composite = λ {A} {B} {C} {f} {g} {h} → λ {}
  }
  where
    private
      ∅ : Set _
      ∅ = Fin.Fin N.zero

𝟙 : Category _ _ _
𝟙 = record
  { Obj = [*]
  ; _~>_ = \_ _ → [*]
  ; _∘_ = \{a} {b} {c} → composite-𝟙 {a} {b} {c}
  ; _≈_ = \_ _ → [*]
  ; id = \{a} → id-𝟙 {a}

  ; leftIdentity = λ {A} {B} {f} → f
  ; rightIdentity = λ {A} {B} {f} → f
  ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → h
  ; equivalence = λ {A} {B} →
                      record
                      { refl = λ {x} → x
                      ; sym = λ {i} {j} z → z
                      ; trans = λ {i} {j} {k} _ z → z
                      }
  ; ≈-composite = λ {A} {B} {C} {f} {g} {h} {i} _ z → z
  }
  where
    private
      [*] : Set _
      [*] = Fin.Fin (N.suc N.zero)

      * : Fin.Fin (N.suc N.zero)
      * = Fin.zero

    composite-𝟙 : {a b c : [*]} → (f g : [*]) → [*]
    composite-𝟙 _ _ = *

    id-𝟙 : {a : [*]} → [*]
    id-𝟙 = *

𝟚-discrete : Category _ _ _
𝟚-discrete = record
  { Obj = [**]
  ; _~>_ = hom-𝟚
  ; _∘_ = \{a} {b} {c} → composite-𝟚 {a} {b} {c}
  ; _≈_ = \{a} {b} → ≈-𝟚 {a} {b}
  ; id = \{a} → id-𝟚 {a}

  ; leftIdentity = \{a} {b} → leftIdentity-𝟚 {a} {b}
  ; rightIdentity = \{a} {b} → rightIdentity-𝟚 {a} {b}
  ; assoc = \{a} {b} {c} {d} → assoc-𝟚 {a} {b} {c} {d}
  ; equivalence = \{a} {b} → equivalence-𝟚 {a} {b}
  ; ≈-composite = \{a} {b} {c} → ≈-composite-𝟚 {a} {b} {c}
  }
  where
    private
      [**] : Set _
      [**] = Fin.Fin (N.suc (N.suc N.zero))

    hom-𝟚 : (a b : [**]) → Set _
    hom-𝟚 (Fin.suc Fin.zero) (Fin.suc Fin.zero) = Fin.Fin (N.suc N.zero)
    hom-𝟚 Fin.zero Fin.zero = Fin.Fin (N.suc N.zero)
    hom-𝟚 _ _ = Fin.Fin N.zero

    composite-𝟚 : {a b c : [**]} → hom-𝟚 b c → hom-𝟚 a b → hom-𝟚 a c
    composite-𝟚 {_} {_} {Fin.suc (Fin.suc ())} _ _
    composite-𝟚 {_} {Fin.suc (Fin.suc ())} {_} _ _
    composite-𝟚 {Fin.suc (Fin.suc ())} {_} {_} _ _
    composite-𝟚 {_} {Fin.zero} {Fin.suc Fin.zero} () _
    composite-𝟚 {_} {Fin.suc Fin.zero} {Fin.zero} () _
    composite-𝟚 {Fin.zero} {Fin.suc Fin.zero} {_} _ ()
    composite-𝟚 {Fin.suc Fin.zero} {Fin.zero} {_} _ ()
    composite-𝟚 {Fin.zero} {Fin.zero} {Fin.zero} _ _ = Fin.zero
    composite-𝟚 {Fin.suc Fin.zero} {Fin.suc Fin.zero} {Fin.suc Fin.zero} _ _ = Fin.zero

    id-𝟚 : {a : [**]} → hom-𝟚 a a
    id-𝟚 {Fin.zero} = Fin.zero
    id-𝟚 {Fin.suc Fin.zero} = Fin.zero
    id-𝟚 {Fin.suc (Fin.suc ())}

    ≈-𝟚 : {a b : [**]} → (f g : hom-𝟚 a b) → Set _
    ≈-𝟚 {Fin.zero} {Fin.zero} _ _ = Fin.Fin (N.suc N.zero)
    ≈-𝟚 {Fin.suc Fin.zero} {Fin.suc Fin.zero} _ _ = Fin.Fin (N.suc N.zero)
    ≈-𝟚 {_} {_} _ _ = Fin.Fin N.zero

    leftIdentity-𝟚 : {a b : [**]} {f : hom-𝟚 a b} → (≈-𝟚 {a} {b}) (composite-𝟚 {a} {b} {b} (id-𝟚 {b}) f) f
    leftIdentity-𝟚 {Fin.zero} {Fin.zero} {f} = f
    leftIdentity-𝟚 {Fin.suc Fin.zero} {Fin.suc Fin.zero} {f} = f
    leftIdentity-𝟚 {Fin.zero} {Fin.suc _} {()}
    leftIdentity-𝟚 {Fin.suc Fin.zero} {Fin.zero} {()}
    leftIdentity-𝟚 {Fin.suc Fin.zero} {Fin.suc (Fin.suc ())} {_}
    leftIdentity-𝟚 {Fin.suc (Fin.suc ())} {_} {_}

    rightIdentity-𝟚 : {a b : [**]} {f : hom-𝟚 a b} → (≈-𝟚 {a} {b}) (composite-𝟚 {a} {a} {b} f (id-𝟚 {a})) f
    rightIdentity-𝟚 {Fin.zero} {Fin.zero} {f} = f
    rightIdentity-𝟚 {Fin.suc Fin.zero} {Fin.suc Fin.zero} {f} = f
    rightIdentity-𝟚 {Fin.zero} {Fin.suc _} {()}
    rightIdentity-𝟚 {Fin.suc Fin.zero} {Fin.zero} {()}
    rightIdentity-𝟚 {_} {Fin.suc (Fin.suc ())} {_}
    rightIdentity-𝟚 {Fin.suc (Fin.suc ())} {_} {_}

    assoc-𝟚 : {a b c d : [**]} {f : hom-𝟚 a b} {g : hom-𝟚 b c} {h : hom-𝟚 c d}
      → ≈-𝟚 {a} {d} (composite-𝟚 {a} {b} {d} (composite-𝟚 {b} {c} {d} h g) f) (composite-𝟚 {a} {c} {d} h (composite-𝟚 {a} {b} {c} g f))
    assoc-𝟚 {Fin.zero} {Fin.suc _} {_} {_} {()} {_} {_}
    assoc-𝟚 {_} {Fin.zero} {Fin.suc _} {_} {_} {()} {_}
    assoc-𝟚 {_} {_} {Fin.zero} {Fin.suc _} {_} {_} {()}
    assoc-𝟚 {Fin.suc Fin.zero} {Fin.zero} {_} {_} {()} {_} {_}
    assoc-𝟚 {Fin.suc (Fin.suc ())} {_} {_} {_} {_} {_} {_}
    assoc-𝟚 {_} {Fin.suc Fin.zero} {Fin.zero} {_} {_} {()} {_}
    assoc-𝟚 {_} {Fin.suc (Fin.suc ())} {_} {_} {_} {_} {_}
    assoc-𝟚 {_} {Fin.suc Fin.zero} {Fin.suc (Fin.suc ())} {_} {_} {_} {_}
    assoc-𝟚 {_} {_} {Fin.suc Fin.zero} {Fin.zero} {_} {_} {()}
    assoc-𝟚 {_} {_} {_} {Fin.suc (Fin.suc ())} {_} {_} {_}

    assoc-𝟚 {Fin.zero} {Fin.zero} {Fin.zero} {Fin.zero} {f} {_} {_} = f
    assoc-𝟚 {Fin.suc Fin.zero} {Fin.suc Fin.zero} {Fin.suc Fin.zero} {Fin.suc Fin.zero} {f} {_} {_} = f

    equivalence-𝟚 : {a b : [**]} → IsEquivalence (≈-𝟚 {a} {b})
    equivalence-𝟚 {a} {b} = record { refl = \{f} → refl-ab {a} {b} {f}; sym = \{f g} → sym-ab {a} {b} {f} {g}; trans = \{f g h} → trans-ab {a} {b} {f} {g} {h} }
      where
        refl-ab : {a b : [**]} {f : hom-𝟚 a b} → ≈-𝟚 {a} {b} f f
        refl-ab {Fin.zero} {Fin.zero} {f} = f
        refl-ab {Fin.suc Fin.zero} {Fin.zero} {()}
        refl-ab {Fin.suc Fin.zero} {Fin.suc Fin.zero} {f} = f
        refl-ab {Fin.suc (Fin.suc ())} {_} {_}
        refl-ab {Fin.zero} {Fin.suc _} {()}
        refl-ab {_} {Fin.suc (Fin.suc ())} {_}

        sym-ab : {a b : [**]} {f g : hom-𝟚 a b} → ≈-𝟚 {a} {b} f g → ≈-𝟚 {a} {b} g f
        sym-ab {Fin.zero} {Fin.zero} fg = fg
        sym-ab {Fin.suc Fin.zero} {Fin.zero} {()} {_}
        sym-ab {Fin.suc Fin.zero} {Fin.suc Fin.zero} fg = fg
        sym-ab {Fin.suc (Fin.suc ())} {_}
        sym-ab {Fin.zero} {Fin.suc _} {()} {_}
        sym-ab {_} {Fin.suc (Fin.suc ())}

        trans-ab : {a b : [**]} {f g h : hom-𝟚 a b} → ≈-𝟚 {a} {b} f g → ≈-𝟚 {a} {b} g h → ≈-𝟚 {a} {b} f h
        trans-ab {Fin.zero} {Fin.zero} fg gh = fg
        trans-ab {Fin.suc Fin.zero} {Fin.zero} {()} {_}
        trans-ab {Fin.suc Fin.zero} {Fin.suc Fin.zero} fg gh = fg
        trans-ab {Fin.suc (Fin.suc ())} {_}
        trans-ab {Fin.zero} {Fin.suc _} {()} {_}
        trans-ab {_} {Fin.suc (Fin.suc ())}

    ≈-composite-𝟚 : {a b c : [**]} {f g : hom-𝟚 b c} {h i : hom-𝟚 a b}
      → ≈-𝟚 {b} f g → ≈-𝟚 {a} h i → ≈-𝟚 {a} (composite-𝟚 {a} f h) (composite-𝟚 {a} g i)
    ≈-composite-𝟚 {Fin.zero} {Fin.zero} {Fin.zero} fg hi = fg
    ≈-composite-𝟚 {Fin.suc Fin.zero} {Fin.suc Fin.zero} {Fin.suc Fin.zero} fg hi = fg
    ≈-composite-𝟚 {Fin.zero} {Fin.suc _} {_} {_} {_} {()}
    ≈-composite-𝟚 {Fin.suc Fin.zero} {Fin.zero} {_} {_} {_} {()}
    ≈-composite-𝟚 {_} {Fin.zero} {Fin.suc _} {()}
    ≈-composite-𝟚 {_} {Fin.suc Fin.zero} {Fin.zero} {()}
    ≈-composite-𝟚 {Fin.suc (Fin.suc ())} {_} {_}
    ≈-composite-𝟚 {_} {Fin.suc (Fin.suc ())} {_}
    ≈-composite-𝟚 {_} {_} {Fin.suc (Fin.suc ())}
