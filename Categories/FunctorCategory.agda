module Categories.FunctorCategory where

open import Level
open import Relation.Binary
open import Categories.Category
open import Categories.Functor
open import Categories.Nat
open import Categories.Reasoning
open import Categories.Categories.Sets

open Category
open Functor
open Nat

FunCat : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′}
  → (Category C₀ C₁ ℓ) → (Category D₀ D₁ ℓ′) → Category _ _ _
FunCat C D = record
  { Obj = Functor C D
  ; _~>_ = Nat
  ; _∘_ = _∘N_
  ; _≈_ = _≈N_
  ; id = id-Nat

  ; leftIdentity = \{F G} {η : Nat F G} → leftIdentity-Nat {F} {G} {η}
  ; rightIdentity = \{F G} {η : Nat F G} → rightIdentity-Nat {F} {G} {η}
  ; assoc = \{F G H I} {η} {τ} {θ} → assoc-Nat {F} {G} {H} {I} {η} {τ} {θ}
  ; equivalence = \{F G} → equivalence-Nat {F} {G}
  ; ≈-composite = \{F G H} {η τ} {θ ε} → ≈-composite-Nat {F} {G} {H} {η} {τ} {θ} {ε}
  }
  where
    _∘N_ : {F G H : Functor C D} → Nat G H → Nat F G → Nat F H
    _∘N_ {F} {G} {H} η τ = record
      { component = ∘-component
      ; naturality = ∘-naturality
      }
      where
        ∘-component : (r : Obj C) → D [ fobj F r ~> fobj H r ]
        ∘-component r = (D [ component η r ∘ component τ r ])

        ∘-naturality : {a b : Obj C} {f : C [ a ~> b ]}
          → D [ D [ ∘-component b ∘ fmap F f ] ≈ D [ fmap H f ∘ ∘-component a ] ]
        ∘-naturality {a} {b} {f} = let open ≈-Reasoning D in
          begin
            D [ ∘-component b ∘ fmap F f ] ≈⟨ refl-hom ⟩
            D [ D [ component η b ∘ component τ b ] ∘ fmap F f ] ≈⟨ assoc D ⟩
            D [ component η b ∘ D [ component τ b ∘ fmap F f ] ] ≈⟨ ≈-composite D (IsEquivalence.refl (equivalence D)) (naturality τ) ⟩
            D [ component η b ∘ D [ fmap G f ∘ component τ a ] ] ↑⟨ assoc D ⟩
            D [ D [ component η b ∘ fmap G f ] ∘ component τ a ] ≈⟨ ≈-composite D (naturality η) (IsEquivalence.refl (equivalence D)) ⟩
            D [ D [ fmap H f ∘ component η a ] ∘ component τ a ] ≈⟨ assoc D ⟩
            D [ fmap H f ∘ D [ component η a ∘ component τ a ] ] ≈⟨ refl-hom ⟩
            D [ fmap H f ∘ ∘-component a ]
          ∎

    _≈N_ : {F G : Functor C D} → (η τ : Nat F G) → Set _
    _≈N_ η τ = ∀{a : Obj C} → D [ component η a ~ component τ a ]

    id-Nat : {F : Functor C D} → Nat F F
    id-Nat {F} = record
      { component = id-component
      ; naturality = id-naturality
      }
      where
        id-component : ∀(r : Obj C) → D [ fobj F r ~> fobj F r ]
        id-component _ = id D

        id-naturality : ∀{a b} {f : C [ a ~> b ]} → D [ D [ id-component b ∘ fmap F f ] ≈ D [ fmap F f ∘ id-component a ] ]
        id-naturality {a} {b} {f} = let open ≈-Reasoning D in
          begin
            D [ id-component b ∘ fmap F f ] ≈⟨ refl-hom ⟩
            D [ id D ∘ fmap F f ] ≈⟨ leftIdentity D ⟩
            fmap F f ↑⟨ rightIdentity D ⟩
            D [ fmap F f ∘ id D ]
          ∎

    leftIdentity-Nat : {F G : Functor C D} {η : Nat F G} → (id-Nat ∘N η) ≈N η
    leftIdentity-Nat {_} {_} {η} {a} = eqArrow (let open ≈-Reasoning D in
      begin
        component (id-Nat ∘N η) a ≈⟨ refl-hom ⟩
        D [ id D ∘ component η a ] ≈⟨ leftIdentity D ⟩
        component η a
      ∎ )

    rightIdentity-Nat : {F G : Functor C D} {η : Nat F G} → (η ∘N id-Nat) ≈N η
    rightIdentity-Nat {_} {_} {η} {a} = eqArrow (let open ≈-Reasoning D in
      begin
        component (η ∘N id-Nat) a ≈⟨ refl-hom ⟩
        D [ component η a ∘ id D ] ≈⟨ rightIdentity D ⟩
        component η a
      ∎ )

    assoc-Nat : {F G H I : Functor C D} {η : Nat F G} {τ : Nat G H} {θ : Nat H I}
      → ((θ ∘N τ) ∘N η) ≈N (θ ∘N (τ ∘N η))
    assoc-Nat {_} {_} {_} {_} {η} {τ} {θ} {a} = eqArrow (let open ≈-Reasoning D in
      begin
        component ((θ ∘N τ) ∘N η) a ≈⟨ refl-hom ⟩
        D [ D [ component θ a ∘ component τ a ] ∘ component η a ] ≈⟨ assoc D ⟩
        D [ component θ a ∘ D [ component τ a ∘ component η a ] ] ≈⟨ refl-hom ⟩
        component (θ ∘N (τ ∘N η)) a
      ∎ )

    equivalence-Nat : {F G : Functor C D} → IsEquivalence (_≈N_ {F} {G})
    equivalence-Nat {F} {G} = record
      { refl = \{η} → refl-Nat {η}
      ; sym = \{η τ} → sym-Nat {η} {τ}
      ; trans = \{η τ θ} → trans-Nat {η} {τ} {θ}
      }
      where
        refl-Nat : {η : Nat F G} → η ≈N η
        refl-Nat {η} = eqArrow (IsEquivalence.refl (equivalence D))

        sym-Nat : {η τ : Nat F G} → η ≈N τ → τ ≈N η
        sym-Nat {η} {τ} η≈τ {a} = lemma-sym (η≈τ {a})
          where
            lemma-sym : D [ component η a ~ component τ a ] → D [ component τ a ~ component η a ]
            lemma-sym (eqArrow η~τ) = eqArrow (IsEquivalence.sym (equivalence D) η~τ)

        trans-Nat : {η τ θ : Nat F G} → η ≈N τ → τ ≈N θ → η ≈N θ
        trans-Nat {η} {τ} {θ} η≈τ τ≈θ {a} = lemma-trans (η≈τ {a}) (τ≈θ {a})
          where
            lemma-trans : D [ component η a ~ component τ a ]
              → D [ component τ a ~ component θ a ]
              → D [ component η a ~ component θ a ]
            lemma-trans (eqArrow η~τ) (eqArrow τ~θ) = eqArrow (IsEquivalence.trans (equivalence D) η~τ τ~θ)

    ≈-composite-Nat : {F G H : Functor C D} {η τ : Nat G H} {θ ε : Nat F G}
      → η ≈N τ → θ ≈N ε → (η ∘N θ) ≈N (τ ∘N ε)
    ≈-composite-Nat {_} {_} {_} {η} {τ} {θ} {ε} η≈τ θ≈ε {a} =
      lemma-∘-resp-≈-Nat (η≈τ {a}) (θ≈ε {a})
      where
        lemma-∘-resp-≈-Nat : D [ component η a ~ component τ a ]
          → D [ component θ a ~ component ε a ]
          → D [ component (η ∘N θ) a ~ component (τ ∘N ε) a ]
        lemma-∘-resp-≈-Nat (eqArrow η~τ) (eqArrow θ~ε) = eqArrow (let open ≈-Reasoning D in
          begin
            component (η ∘N θ) a ≈⟨ refl-hom ⟩
            D [ component η a ∘ component θ a ] ≈⟨ ≈-composite D η~τ θ~ε ⟩
            D [ component τ a ∘ component ε a ] ≈⟨ refl-hom ⟩
            component (τ ∘N ε) a
          ∎ )

[_,_] : ∀{C₀ C₁ ℓ D₀ D₁ ℓ′} (C : Category C₀ C₁ ℓ) → (D : Category D₀ D₁ ℓ′) → Category (suc (C₀ ⊔ C₁ ⊔ ℓ ⊔ D₀ ⊔ D₁ ⊔ ℓ′)) (suc (C₀ ⊔ C₁ ⊔ ℓ ⊔ D₀ ⊔ D₁ ⊔ ℓ′)) (C₀ ⊔ suc (D₀ ⊔ D₁ ⊔ ℓ′))
[ C , D ] = FunCat C D

PSh[_] : ∀{C₀ C₁ ℓ} (C : Category C₀ C₁ ℓ) → Category _ _ _
PSh[_] {_} {C₁} {_} X = FunCat (op X) (Sets {C₁})

