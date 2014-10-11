module Categories.Categories.Cat where

open import Level
open import Relation.Binary
open import Categories.Category
open import Categories.Functor
open import Categories.Reasoning

open Category
open Functor

Cat : ∀{C₀ C₁ ℓ} → Category (suc (C₀ ⊔ C₁ ⊔ ℓ)) (suc (C₀ ⊔ C₁ ⊔ ℓ)) (suc (C₀ ⊔ C₁ ⊔ ℓ))
Cat {C₀} {C₁} {ℓ} = record
  { Obj = Category C₀ C₁ ℓ
  ; _~>_ = Functor
  ; _∘_ = _∘′_
  ; _≈_ = _≈F_
  ; id = id-Functor

  ; leftIdentity = \{C D} {F} → leftId-Functor {C} {D} {F}
  ; rightIdentity = \{C D} {F : Functor C D} → rightId-Functor {C} {D} {F}
  ; assoc = \{A B C D} {F : Functor A B} {G : Functor B C} {H : Functor C D}
      → assoc-Functor {A} {B} {C} {D} {F} {G} {H}
  ; equivalence = equivalence-Functor
  ; ≈-composite = \{A B C} {F G : Functor B C} {H I : Functor A B}
      → ≈-composite-Functor {A} {B} {C} {F} {G} {H} {I}
  }
  where
    _∘′_ : {C D E : Category C₀ C₁ ℓ} → Functor D E → Functor C D → Functor C E
    _∘′_ {C} {D} {E} F G = record
      { fobj = fobjFG
      ; fmap = fmapFG
      ; ≈-cong = ≈-cong-Functor
      ; preserveId = preserveId-Functor
      ; covariant = \{_} {_} {_} {f} {g} -> let open ≈-Reasoning E in
          begin
            fmapFG (C [ g ∘ f ]) ≈⟨ ≈-cong F (covariant G) ⟩
            fmap F (D [ fmap G g ∘ fmap G f ]) ≈⟨ covariant F ⟩
            E [ fmapFG g ∘ fmapFG f ]
          ∎
      }
      where
        fobjFG : Obj C → Obj E
        fobjFG x = fobj F (fobj G x)

        fmapFG : {a b : Obj C} → C [ a ~> b ] → E [ fobjFG a ~> fobjFG b ]
        fmapFG f = fmap F (fmap G f)

        ≈-cong-Functor : {a b : Obj C} {f g : C [ a ~> b ]}
                         → C [ f ≈ g ] → E [ fmapFG f ≈ fmapFG g ]
        ≈-cong-Functor {_} {_} {f} {g} f≈g = let open ≈-Reasoning E in
          begin
            fmapFG f ≈⟨ ≈-cong F (≈-cong G f≈g) ⟩
            fmapFG g
          ∎

        preserveId-Functor : {a : Obj C} → E [ fmapFG (id C {a}) ≈ id E ]
        preserveId-Functor = let open ≈-Reasoning E in
          begin
            fmapFG (id C) ≈⟨ ≈-cong F (preserveId G) ⟩
            fmap F (id D) ≈⟨ preserveId F ⟩
            id E
          ∎
 
    _≈F_ : {C D : Category C₀ C₁ ℓ} → (F G : Functor C D) → Set _
    _≈F_ {C} {D} F G =
      ∀{a b : Obj C} → (f : C [ a ~> b ]) → D [ fmap F f ~ fmap G f ]

    id-Functor : {C : Category C₀ C₁ ℓ} → Functor C C
    id-Functor {C} = record
      { fobj = \x -> x
      ; fmap = \f -> f

      ; ≈-cong = \f≈g → f≈g
      ; preserveId = IsEquivalence.refl (equivalence C)
      ; covariant = IsEquivalence.refl (equivalence C)
      }

    leftId-Functor : {C D : Category C₀ C₁ ℓ} {F : Functor C D}
      → (id-Functor ∘F F) ≈F F
    leftId-Functor {C} {D} {F} = \{a} {b} (f : C [ a ~> b ]) →
      eqArrow (let open ≈-Reasoning D in
        begin
          fmap (id-Functor ∘F F) f ≈⟨ refl-hom ⟩
          fmap F f
        ∎)

    rightId-Functor : {C D : Category C₀ C₁ ℓ} {F : Functor C D}
      → (F ∘F id-Functor) ≈F F
    rightId-Functor {C} {D} {F} = \{a} {b} (f : C [ a ~> b ]) →
      eqArrow (let open ≈-Reasoning D in
        begin
          fmap (F ∘F id-Functor) f ≈⟨ refl-hom ⟩
          fmap F f
        ∎)

    assoc-Functor : {A B C D : Category C₀ C₁ ℓ}
      {F : Functor A B} {G : Functor B C} {H : Functor C D}
        → ((H ∘F G) ∘F F) ≈F (H ∘F (G ∘F F))
    assoc-Functor {A} {B} {C} {D} {F} {G} {H} = \{a} {b} (f : A [ a ~> b ])
      → eqArrow (let open ≈-Reasoning D in
        begin
          fmap ((H ∘F G) ∘F F) f ≈⟨⟩
          fmap (H ∘F G) (fmap F f) ≈⟨⟩
          fmap H (fmap G (fmap F f)) ≈⟨⟩
          fmap H (fmap (G ∘F F) f) ≈⟨⟩
          fmap (H ∘F (G ∘F F)) f
        ∎
      )

    equivalence-Functor :
      {A B : Category C₀ C₁ ℓ}
      → IsEquivalence (_≈F_ {A} {B})
    equivalence-Functor {A} {B} = record
      { refl = \{F : Functor A B} → F-refl {F}
      ; sym = \{F G : Functor A B} → F-sym {F} {G}
      ; trans = \{F G H : Functor A B} → F-trans {F} {G} {H}
      }
      where
        F-refl : {F : Functor A B} → F ≈F F
        F-refl {F} _ = eqArrow (≈-cong F (IsEquivalence.refl (equivalence A)))

        lemma-sym : ∀{C} {a b c d : Obj C}
          {f : C [ a ~> b ]} {g : C [ c ~> d ]}
          → C [ f ~ g ] → C [ g ~ f ]
        lemma-sym {C} (eqArrow f~g) =
          eqArrow (IsEquivalence.sym (equivalence C) f~g)

        F-sym : {F G : Functor A B} → F ≈F G → G ≈F F
        F-sym F≈G f = lemma-sym (F≈G f)

        lemma-trans : ∀{C} {a b c d e r : Obj C}
          {f : C [ a ~> b ]} {g : C [ c ~> d ]} {h : C [ e ~> r ]}
          → C [ f ~ g ] → C [ g ~ h ] → C [ f ~ h ]
        lemma-trans {C} (eqArrow f~g) (eqArrow g~h) =
          eqArrow (IsEquivalence.trans (equivalence C) f~g g~h)

        F-trans : {F G H : Functor A B} → F ≈F G → G ≈F H → F ≈F H
        F-trans F≈G G≈H f = lemma-trans (F≈G f) (G≈H f)
        
    ≈-composite-Functor :
      {A B C : Category C₀ C₁ ℓ} {F G : Functor B C} {H I : Functor A B}
        → F ≈F G → H ≈F I → (F ∘F H) ≈F (G ∘F I)
    ≈-composite-Functor {A} {B} {C} {F} {G} {H} {I} FG HI = 
      \{a b} (f : A [ a ~> b ]) →
      lemma {f = fmap H f} {g = fmap I f} {h = fmap G (fmap I f)}
            (HI f) (FG (fmap I f))
      where
        lemma : ∀{ a b c d e r }
          {f : B [ a ~> b ]} {g : B [ c ~> d ]} { h : C [ e ~> r ] }
          → B [ f ~ g ] → C [ fmap F g ~ h ] → C [ fmap F f ~ h ]
        lemma (eqArrow f~g) (eqArrow Fg~h) =
          eqArrow (IsEquivalence.trans (equivalence C) (≈-cong F f~g) Fg~h)
