module Sets.Topology.Neighborhood where

open import Function
open import Data.Empty
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Sets.Sets
open import Sets.Topology.Topology
open import Sets.Topology.Interior

module Neighborhood (X : TopSpace) where
  open TopSpace X
  open Interior X

  Neighborhoods : set ⟶ P[ P[ set ] ]
  Neighborhoods x = ⟦ V ∈ P[ set ] ∣ x ∈ Int V ⟧ , \x-in → ⊆-∈-power (\y y-in → ⊆-∈-power $ \z z∈y → ∈-⊆-power (∧-left (replace-cond y y-in)) z z∈y)

  private
    in-set : ∀ {x} V → V ∈ ⟨ Neighborhoods ⟩ x → V ⊆ set
    in-set V V-in y y∈V = ∈-⊆-power (∧-left $ replace-cond V V-in) y y∈V

  module Neighbor-props where
    open Interior-lemmas

    module Neighbor-prop-type (Neighborhoods′ : set ⟶ P[ P[ set ] ]) where
      prop-1 = ∀{x V} → V ∈ ⟨ Neighborhoods′ ⟩ x → x ∈ V
      prop-2 = ∀{x V W} → W ∈ P[ set ] → V ∈ ⟨ Neighborhoods′ ⟩ x → V ⊆ W → W ∈ ⟨ Neighborhoods′ ⟩ x
      prop-3 = ∀{x V W} → V ∈ ⟨ Neighborhoods′ ⟩ x → W ∈ ⟨ Neighborhoods′ ⟩ x → (V ∩ W) ∈ ⟨ Neighborhoods′ ⟩ x
      prop-4 = ∀{x V} → V ∈ ⟨ Neighborhoods′ ⟩ x → ∃ \W → W ∈ ⟨ Neighborhoods′ ⟩ x ∧ (∀ y → y ∈ W → V ∈ ⟨ Neighborhoods′ ⟩ y)
      cond = prop-1 ∧ prop-2 ∧ prop-3 ∧ prop-4

    prop-1 : ∀{x V} → V ∈ ⟨ Neighborhoods ⟩ x → x ∈ V
    prop-1 {x} {V} V-in = Int-⊆ V x $ ∧-right $ replace-cond V V-in

    prop-2 : ∀ {x V W} → W ∈ P[ set ] → V ∈ ⟨ Neighborhoods ⟩ x → V ⊆ W → W ∈ ⟨ Neighborhoods ⟩ x
    prop-2 {x} {V} {W} W-in V-in V⊆W = let and = replace-cond V V-in in
      satisfy-cond W $ W-in , (satisfy-in-union x $
        Int V ,
        (satisfy-cond (Int V) $ Int-Open V , ⊆-trans (Int-⊆ V) V⊆W) ,
        ∧-right and)

    prop-3 : ∀{x V W} → V ∈ ⟨ Neighborhoods ⟩ x → W ∈ ⟨ Neighborhoods ⟩ x → (V ∩ W) ∈ ⟨ Neighborhoods ⟩ x
    prop-3 {x} {V} {W} V-in W-in = satisfy-cond (V ∩ W) $
      (⊆-∈-power $ ∩-⊆ $ let open ≡-Reasoning in begin
        (V ∩ W) ∩ set  ≡⟨ ∩-assoc ⟩
        V ∩ (W ∩ set)  ≡⟨ ∩-cong ≡-refl $ ⊆-∩ $ in-set W W-in ⟩
        V ∩ W ∎) ,
      (satisfy-in-union x $
        (Int V ∩ Int W) ,
        satisfy-cond (Int V ∩ Int W)
          (∩-open (Int-Open V) (Int-Open W) ,
          (⊆-cong-∩ (Int-⊆ V) (Int-⊆ W))) ,
        ∧-∩ x
          (∧-right (replace-cond V V-in) ,
          ∧-right (replace-cond W W-in)))

    prop-4 : ∀{x V} → V ∈ ⟨ Neighborhoods ⟩ x → ∃ \W → W ∈ ⟨ Neighborhoods ⟩ x → ∀ y → y ∈ W → V ∈ ⟨ Neighborhoods ⟩ y
    prop-4 {V = V} V-in = Int V , (\W-in y y∈W → satisfy-cond V $ (⊆-∈-power $ in-set V V-in) , y∈W)
  open Neighbor-props public

  module Neighbor-cond where
    open Interior-lemmas

    module Neighbor-cond-type (Y : TopSpace) (Neighborhoods′ : set ⟶ P[ P[ set ] ]) where
      prop = ∀ {x V} → V ∈ P[ set ] → x ∈ explicit.Int-in Y V ⇔ V ∈ ⟨ Neighborhoods′ ⟩ x

    Neighbor-cond-original : Neighbor-cond-type.prop X Neighborhoods
    Neighbor-cond-original {x} {V} V-in =
      (\x-in → satisfy-cond V $ V-in , x-in) ,
      (\V-in → let and = replace-cond V V-in in
               satisfy-in-union x $ Int V , satisfy-cond (Int V) (Int-Open V , Int-⊆ V) , ∧-right and)
  open Neighbor-cond public

module Neighborhoods-decides-Topology (X : TopSpace) where
  open TopSpace X
  open Neighborhood X

  Topology-from-Neighborhoods :
    (Neighborhoods′ : set ⟶ P[ P[ set ] ])
    → (∀ x → ⟨ Neighborhoods′ ⟩ x ≢ ∅)
    → Neighbor-props.Neighbor-prop-type.cond Neighborhoods′
    → TopSpace
  Topology-from-Neighborhoods Neighborhoods′ non-∅ (cond-1 , cond-2 , cond-3 , cond-4) = record
    { set = set
    ; Open = Open-set
    ; OpenFamily = ⊆-∈-power (\O O:open → ∧-left $ replace-cond O O:open)
    ; ∅-open = satisfy-cond ∅ $ ⊆-∈-power ∅-⊆ , (\x x∈∅ → ⊥-elim $ elem-∈ x x∈∅)
    ; all-open = satisfy-cond set $ ∈-refl-power , set-neighbor
    ; ⋃-open = \F⊆Open → satisfy-cond _ $ ⋃F:open F⊆Open
    ; ∩-open = \A:open B:open → satisfy-cond _ $ A∩B:open A:open B:open
    }
    where
      Open-set = ⟦ O ∈ P[ set ] ∣ (∀ x → x ∈ O → O ∈ ⟨ Neighborhoods′ ⟩ x) ⟧

      open-set : ∀ X → X ∈ Open-set → X ∈ P[ set ]
      open-set X X:open = ∧-left $ replace-cond X X:open

      set-neighbor : ∀ x → x ∈ set → set ∈ ⟨ Neighborhoods′ ⟩ x
      set-neighbor x x∈set = cond-2 ∈-refl-power U-in U⊆set
        where
        ex = ∅-∃ (non-∅ x)
        U = proj₁ ex ; U-in = proj₂ ex

        U⊆set : U ⊆ set
        U⊆set y y∈U = ∈-⊆-power
          (∈-⊆-power (proj₂ (Neighborhoods′ x) x∈set) U U-in) y y∈U

      ⋃F:open : ∀{F} → F ⊆ Open-set → ⋃ F ∈ P[ set ] × ((x : Set) → x ∈ ⋃ F → ⋃ F ∈ ⟨ Neighborhoods′ ⟩ x)
      ⋃F:open {F} F⊆open = (⊆-∈-power ∪F⊆set) , lemma
        where
        ∪F⊆set : ⋃ F ⊆ set
        ∪F⊆set x x-in = let ex = replace-in-union x x-in ; U = proj₁ ex ; U-cond = proj₂ ex in
          ∈-⊆-power (∧-left $ replace-cond U $ F⊆open U (∧-left U-cond)) x $ ∧-right U-cond

        lemma : ∀ x → x ∈ ⋃ F → ⋃ F ∈ ⟨ Neighborhoods′ ⟩ x
        lemma x x-in = cond-2 (⊆-∈-power ∪F⊆set) U:nbh U⊆∪F
          where
          ex = replace-in-union x x-in
          U = proj₁ ex ; U-cond = proj₂ ex

          U⊆∪F : U ⊆ ⋃ F
          U⊆∪F y y∈U = satisfy-in-union y $ U , ∧-left U-cond , y∈U

          U:nbh : U ∈ ⟨ Neighborhoods′ ⟩ x
          U:nbh = let ex = replace-cond U $ F⊆open U $ ∧-left U-cond
                  in proj₂ ex x (∧-right U-cond)


      A∩B:open : ∀{A B} → A ∈ Open-set → B ∈ Open-set → A ∩ B ∈ P[ set ] × ((x : Set) → x ∈ A ∩ B → A ∩ B ∈ ⟨ Neighborhoods′ ⟩ x)
      A∩B:open {A} {B} A:open B:open = (⊆-∈-power A∩B⊆set) , lemma
        where
        and-A = replace-cond A A:open
        and-B = replace-cond B B:open

        A∩B⊆set : A ∩ B ⊆ set
        A∩B⊆set x x-in = proj₁ $ ∧-map
          (∈-⊆-power (∧-left and-A) x)
          (∈-⊆-power (∧-left and-B) x) $ ∩-∧ x x-in

        lemma : ∀ x → x ∈ A ∩ B → A ∩ B ∈ ⟨ Neighborhoods′ ⟩ x
        lemma x x-in = cond-3
          (∧-right and-A x $ ∧-left $ ∩-∧ x x-in)
          (∧-right and-B x $ ∧-right $ ∩-∧ x x-in)

  uniqueness :
    (Neighborhoods′ : set ⟶ P[ P[ set ] ])
    → (non-∅ : ∀ x → ⟨ Neighborhoods′ ⟩ x ≢ ∅)
    → (cond : Neighbor-props.Neighbor-prop-type.cond Neighborhoods′)
    → Neighbor-cond.Neighbor-cond-type.prop (Topology-from-Neighborhoods Neighborhoods′ non-∅ cond) Neighborhoods′
  uniqueness Neighborhoods′ non-∅ (cond-1 , cond-2 , cond-3 , cond-4) = \V-in → V∈V[x] V-in , x∈Vᵒ V-in
    where
    Y = Topology-from-Neighborhoods Neighborhoods′ non-∅ (cond-1 , cond-2 , cond-3 , cond-4)

    in-set : ∀ {x V} → x ∈ set → V ∈ ⟨ Neighborhoods′ ⟩ x → V ⊆ set
    in-set {x} {V} x-in V-in y y∈V =
      ∈-⊆-power (∈-⊆-power (Image-∈ Neighborhoods′ x x-in) V V-in) y y∈V

    open Interior Y
    open Interior-lemmas

    V∈V[x] : ∀{x V} → V ∈ P[ set ] → x ∈ Int V → V ∈ ⟨ Neighborhoods′ ⟩ x
    V∈V[x] {x} {V} V-in x-in = cond-2 V-in Vᵒ∈V[x] (Int-⊆ V)
      where
      Vᵒ∈V[x] : Int V ∈ ⟨ Neighborhoods′ ⟩ x
      Vᵒ∈V[x] = ∧-right (replace-cond (Int V) (Int-Open V)) x x-in

    x∈Vᵒ : ∀{x V} → V ∈ P[ set ] → V ∈ ⟨ Neighborhoods′ ⟩ x → x ∈ Int V
    x∈Vᵒ {x} {V} V∈P V-in = U⊆Vᵒ x x∈U
      where
      U = ⟦ y ∈ set ∣ V ∈ ⟨ Neighborhoods′ ⟩ y ⟧

      x∈U : x ∈ U
      x∈U = satisfy-cond x $ (∈-⊆-power V∈P x $ cond-1 V-in) , V-in

      U⊆V : U ⊆ V
      U⊆V y y∈U = cond-1 (∧-right $ replace-cond y y∈U)

      U∈V[z] : ∀ z → z ∈ U → U ∈ ⟨ Neighborhoods′ ⟩ z
      U∈V[z] z z∈U =
        cond-2 (⊆-∈-power $ \w w∈U → ∧-left $ replace-cond w w∈U)
               (∧-left $ proj₂ W-ex) W⊆U
        where
        W-ex = cond-4 (∧-right $ replace-cond z z∈U)
        W = proj₁ W-ex

        W⊆U : W ⊆ U
        W⊆U y y∈W = satisfy-cond y $
          (in-set (∧-left $ replace-cond z z∈U)
                  (∧-left $ proj₂ W-ex) y y∈W) , ∧-right (proj₂ W-ex) y y∈W

      U:open : U ∈ TopSpace.Open Y
      U:open = satisfy-cond U $
        (⊆-∈-power $ \y y∈U → ∧-left $ replace-cond y y∈U) ,
        (\y y∈U → U∈V[z] y y∈U)

      U⊆Vᵒ : U ⊆ Int V
      U⊆Vᵒ = Open-⊆-Int _ _ U⊆V U:open


