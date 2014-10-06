open import Level

module Categories.Yoneda {S₀ S₁ ℓₛ : Level} where

open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as Eq
open import Categories.Category
open import Categories.Functor
open import Categories.Nat
open import Categories.Categories.Sets
open import Categories.Reasoning
open import Categories.FunctorCategory

open Category
open Functor
open Nat
open LocallySmall {S₀} {S₁} {ℓₛ}

contravariantHom : (C : Category S₀ S₁ ℓₛ) → (r : Obj C) → Functor (op C) (Sets {S₁})
contravariantHom C r = record
  { fobj = fobj-hom
  ; fmap = fmap-hom
  ; ≈-cong = ≈-cong-hom
  ; preserveId = preserveId-hom
  ; covariant = contravariant-hom
  }
  where
    fobj-hom : Obj C → Set S₁
    fobj-hom x = Hom C x r

    fmap-hom : {a b : Obj C} → (f : C [ a ~> b ]) → Sets [ Hom C b r ~> Hom C a r ]
    fmap-hom f u = C [ u ∘ f ]

    ≈-cong-hom : {a b : Obj C} {f g : C [ a ~> b ]} → C [ f ≈ g ] → Sets [ fmap-hom f ≈ fmap-hom g ]
    ≈-cong-hom {a} {b} {f} {g} f≈g = extensionality (lemma-≈-cong f≈g)
      where
        lemma-≈-cong : C [ f ≈ g ] → (u : Hom C b r) → fmap-hom f u ≡ fmap-hom g u
        lemma-≈-cong f≈g u = let open ≈-Reasoning C in ≈-≡ {C} (
          begin
            fmap-hom f u ≈⟨ ≈-composite C refl-hom f≈g ⟩
            fmap-hom g u
          ∎ )

    preserveId-hom : {a : Obj C} → Sets [ fmap-hom (id C {a}) ≈ id (Sets) {fobj-hom a} ]
    preserveId-hom {a} = extensionality lemma
      where
        lemma : (u : C [ a ~> r ]) → fmap-hom (id C) u ≡ u
        lemma u = let open ≈-Reasoning C in ≈-≡ {C} (
          begin
            fmap-hom (id C) u ≈⟨ refl-hom ⟩
            C [ u ∘ (id C) ] ≈⟨ rightIdentity C ⟩
            u
          ∎ )

    contravariant-hom : {a b c : Obj C}
      {f : (op C) [ a ~> b ]} {g : (op C) [ b ~> c ]}
      → Sets [ fmap-hom ((op C) [ g ∘ f ]) ≈ Sets [ fmap-hom g ∘ fmap-hom f ] ]
    contravariant-hom {a} {_} {_} {f} {g} = extensionality lemma
      where
        lemma : (u : C [ a ~> r ]) → fmap-hom ((op C) [ g ∘ f ] ) u ≡ fmap-hom g (fmap-hom f u)
        lemma u = let open ≈-Reasoning C in ≈-≡ {C} (
          begin
            fmap-hom ((op C) [ g ∘ f ]) u ≈⟨ refl-hom ⟩
            fmap-hom (C [ f ∘ g ]) u ≈⟨ refl-hom ⟩
            C [ u ∘ C [ f ∘ g ] ] ↑⟨ assoc C ⟩
            C [ C [ u ∘ f ] ∘ g ] ≈⟨ refl-hom ⟩
            fmap-hom g (fmap-hom f u)
          ∎ )

yoneda : (C : Category S₀ S₁ ℓₛ) → Functor C (PSh[ C ])
yoneda C = record
  { fobj = fobj-yoneda
  ; fmap = fmap-yoneda
  
  ; ≈-cong = ≈-cong-yoneda
  ; preserveId = preserveId-yoneda
  ; covariant = covariant-yoneda
  }
  where
    fobj-yoneda : Obj C → Obj PSh[ C ]
    fobj-yoneda r = contravariantHom C r

    fmap-yoneda : {a b : Obj C}
      → C [ a ~> b ] → Nat (fobj-yoneda a) (fobj-yoneda b)
    fmap-yoneda {a} {b} f = record
      { component = component-fmap
      ; naturality = naturality-fmap
      }
      where
        component-fmap : (r : Obj C) → Sets [ (fobj (fobj-yoneda a) r) ~> (fobj (fobj-yoneda b) r) ]
        component-fmap r u = C [ f ∘ u ]

        naturality-fmap : {c d : Obj C} {g : (op C) [ c ~> d ]}
          → Sets [ Sets [ component-fmap d ∘ fmap (fobj-yoneda a) g ] ≈ Sets [ fmap (fobj-yoneda b) g ∘ component-fmap c ] ]
        naturality-fmap {c} {d} {g} = extensionality lemma
          where
            lemma : (u : C [ c ~> a ]) → component-fmap d (fmap (fobj-yoneda a) g u) ≡ fmap (fobj-yoneda b) g (component-fmap c u)
            lemma u = let open ≈-Reasoning C in ≈-≡ {C} (
              begin
                component-fmap d (fmap (fobj-yoneda a) g u) ≈⟨ refl-hom ⟩
                component-fmap d (C [ u ∘ g ]) ≈⟨ refl-hom ⟩
                C [ f ∘ C [ u ∘ g ] ] ↑⟨ assoc C ⟩
                C [ C [ f ∘ u ] ∘ g ] ≈⟨ refl-hom ⟩
                C [ component-fmap c u ∘ g ] ≈⟨ refl-hom ⟩
                fmap (fobj-yoneda b) g (component-fmap c u)
              ∎ )


    ≈-cong-yoneda : {a b : Obj C} {f g : C [ a ~> b ]}
      → C [ f ≈ g ] → PSh[ C ] [ fmap-yoneda f ≈ fmap-yoneda g ]
    ≈-cong-yoneda {a} {b} {f} {g} f≈g = eqArrow (extensionality lemma)
      where
        lemma : {r : Obj C} (u : fobj (fobj-yoneda a) r) → component (fmap-yoneda f) r u ≡ component (fmap-yoneda g) r u
        lemma {r} u = let open Eq.≡-Reasoning in
          begin
            component (fmap-yoneda f) r u ≡⟨ refl ⟩
            C [ f ∘ u ] ≡⟨ ≈-≡ {C} (≈-composite C f≈g (IsEquivalence.refl (equivalence C))) ⟩
            C [ g ∘ u ] ≡⟨ refl ⟩
            component (fmap-yoneda g) r u
          ∎

    preserveId-yoneda : {a : Obj C} → PSh[ C ] [ fmap-yoneda (id C {a}) ≈ id (PSh[ C ]) {fobj-yoneda a} ]
    preserveId-yoneda {a} = eqArrow (extensionality lemma)
      where
        lemma : {r : Obj C} (u : fobj (fobj-yoneda a) r) → component (fmap-yoneda (id C {a})) r u ≡ component (id (PSh[ C ]) {fobj-yoneda a}) r u
        lemma {r} u = let open Eq.≡-Reasoning in
          begin
            component (fmap-yoneda (id C {a})) r u ≡⟨ refl ⟩
            C [ id C {a} ∘ u ] ≡⟨ ≈-≡ {C} (leftIdentity C) ⟩
            u ≡⟨ refl ⟩
            (id Sets {fobj (fobj-yoneda a) r}) u ≡⟨ refl ⟩
            component (id (PSh[ C ]) {fobj-yoneda a}) r u
          ∎

    covariant-yoneda : {a b c : Obj C} {f : C [ a ~> b ]} {g : C [ b ~> c ]}
      → PSh[ C ] [ fmap-yoneda (C [ g ∘ f ]) ≈ PSh[ C ] [ fmap-yoneda g ∘ fmap-yoneda f ] ]
    covariant-yoneda {a} {_} {_} {f} {g} = eqArrow (extensionality lemma)
      where
        lemma : {r : Obj C} (u : fobj (fobj-yoneda a) r) → component (fmap-yoneda (C [ g ∘ f ])) r u ≡ component (PSh[ C ] [ fmap-yoneda g ∘ fmap-yoneda f ]) r u
        lemma {r} u = let open Eq.≡-Reasoning in
          begin
            component (fmap-yoneda (C [ g ∘ f ])) r u ≡⟨ refl ⟩
            C [ C [ g ∘ f ] ∘ u ] ≡⟨ ≈-≡ {C} (assoc C) ⟩
            C [ g ∘ C [ f ∘ u ] ] ≡⟨ refl ⟩
            component (PSh[ C ] [ fmap-yoneda g ∘ fmap-yoneda f ]) r u
          ∎

y[_] : {C : Category S₀ S₁ ℓₛ} → (a : Obj C) → Obj PSh[ C ]
y[_] {C} a = fobj (yoneda C) a

YonedaLemma : {C : Category S₀ S₁ ℓₛ} {F : Obj PSh[ C ]} {r : Obj C} → Sets [ Nat y[ r ] F ≅ Lift {S₁} {suc S₀ ⊔ (suc (suc S₁) ⊔ suc ℓₛ)} (fobj F r) ]
YonedaLemma {C} {F} {r} = record
  { l~>r = Nat→F
  ; r~>l = F→Nat
  ; iso = record { iso-l = iso-Nat; iso-r = iso-F }
  }
  where
    Nat→F : Nat y[ r ] F → Lift (fobj F r)
    Nat→F α = lift (component α r (id C {r}))

    F→Nat : Lift (fobj F r) → Nat y[ r ] F
    F→Nat (lift x) = record
      { component = component-Nat
      ; naturality = naturality-Nat }
      where
        component-Nat : (d : Obj C) → Sets [ Hom C d r ~> fobj F d ]
        component-Nat _ u = fmap F u x

        naturality-Nat : {a b : Obj C} {f : (op C) [ a ~> b ]}
          → Sets [ Sets [ component-Nat b ∘ fmap (y[_] {C} r) f ] ≈ Sets [ fmap F f ∘ component-Nat a ] ]
        naturality-Nat {a} {b} {f} = extensionality lemma
          where
            commute : (u : Hom C a r) → fmap F (C [ u ∘ f ]) x ≡ fmap F f (fmap F u x)
            commute u = let open ≈-Reasoning (Sets {ℓₛ}) in Eq.cong (\f → f x) (covariant F)

            lemma : (u : Hom C a r)
              → component-Nat b (fmap (y[_] {C} r) f u) ≡ fmap F f (component-Nat a u)
            lemma u = let open Eq.≡-Reasoning in
              begin
                component-Nat b (fmap (y[_] {C} r) f u) ≡⟨⟩
                component-Nat b (C [ u ∘ f ]) ≡⟨⟩
                (fmap F (C [ u ∘ f ])) x ≡⟨ commute u ⟩
                fmap F f (fmap F u x) ≡⟨⟩
                fmap F f (component-Nat a u)
              ∎

    open LocallySmall {_} {suc S₀ ⊔ (suc (suc S₁) ⊔ suc ℓₛ)} {_} renaming
      (extensionality to extensionality′; ≈-≡ to ≈-≡′)

    iso-Nat : Sets [ F→Nat ∘ Nat→F ] ≡ id Sets
    iso-Nat = extensionality′ lemma
      where
        open ≈-Reasoning using (_≈⟨_⟩_)

        nat-α : (α : Nat y[ r ] F) (d : Obj C) (u : C [ d ~> r ])
          → fmap F u (component α r (id C {r})) ≡ component α d (fmap (fobj (yoneda C) r) u (id C {r}))
        nat-α α d u = let open ≈-Reasoning (Sets {ℓₛ}) in Eq.cong (\f → f (id C {r})) (Eq.sym (naturality α))

        component-α-d :
          (α : Nat y[ r ] F) (d : Obj C) {f g : C [ d ~> r ]} →
          C [ f ≈ g ] → component α d f ≡ component α d g
        component-α-d α d f≈g = let open ≈-Reasoning (Sets {ℓₛ}) in Eq.cong (\f → component α d f) (≈-≡ {C} f≈g)

        lemma : (α : Nat y[ r ] F) → F→Nat (Nat→F α) ≡ id Sets α
        lemma α = let open Eq.≡-Reasoning in ≈-≡′ {PSh[ C ]} (\{d : Obj C} → eqArrow (extensionality (\u →
          begin
            component (F→Nat (Nat→F α)) d u ≡⟨⟩
            component (F→Nat (lift (component α r (id C {r})))) d u ≡⟨⟩
            fmap F u (component α r (id C {r})) ≡⟨ nat-α α d u ⟩
            component α d (fmap (fobj (yoneda C) r) u (id C {r})) ≡⟨⟩
            component α d (C [ (id C {r}) ∘ u ]) ≡⟨ component-α-d α d (leftIdentity C) ⟩
            component α d u ≡⟨⟩
            component (id Sets α) d u
          ∎
          ) ) )

    iso-F : Sets [ Nat→F ∘ F→Nat ] ≡ id Sets
    iso-F = extensionality′ lemma
      where
        lemma : (x : Lift (fobj F r)) → Nat→F (F→Nat x) ≡ id Sets x
        lemma (lift x) = let open Eq.≡-Reasoning in
          begin
            Nat→F (F→Nat (lift x)) ≡⟨⟩
            lift (component (F→Nat (lift x)) r (id C {r})) ≡⟨⟩
            lift (fmap F (id C {r}) x) ≡⟨ Eq.cong (\f → lift (f x)) (preserveId F) ⟩
            lift x ≡⟨⟩
            id Sets (lift x)
          ∎

