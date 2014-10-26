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

  Neighborhoods : ∀ x → Set
  Neighborhoods x = ⟦ V ∈ P[ set ] ∣ x ∈ Int V ⟧

  module Neighbor-props where
    private
      in-set : ∀ {x} V → V ∈ Neighborhoods x → V ⊆ set
      in-set V V-in y y∈V = ∈-⊆-power (∧-left $ replace-cond V V-in) y y∈V

    open Interior-lemmas

    module Neighbor-prop-type (Neighborhoods′ : ∀ x → Set) where
      prop-1 = ∀ x V → V ∈ Neighborhoods′ x → x ∈ V
      prop-2 = ∀ x V W → W ∈ P[ set ] → V ∈ Neighborhoods′ x → V ⊆ W → W ∈ Neighborhoods′ x
      prop-3 = ∀ x V W → V ∈ Neighborhoods′ x → W ∈ Neighborhoods′ x → (V ∩ W) ∈ Neighborhoods′ x
      prop-4 = ∀ x V → V ∈ Neighborhoods′ x → ∃ \W → W ∈ Neighborhoods′ x → ∀ y → y ∈ W → V ∈ Neighborhoods′ y
      cond = prop-1 ∧ prop-2 ∧ prop-3 ∧ prop-4

    prop-1 : ∀ x V → V ∈ Neighborhoods x → x ∈ V
    prop-1 x V V-in = Int-⊆ V x $ ∧-right $ replace-cond V V-in

    prop-2 : ∀ x V W → W ∈ P[ set ] → V ∈ Neighborhoods x → V ⊆ W → W ∈ Neighborhoods x
    prop-2 x V W W-in V-in V⊆W = let and = replace-cond V V-in in
      satisfy-cond W $ W-in , (satisfy-in-union x $
        Int V ,
        (satisfy-cond (Int V) $ Int-Open V , ⊆-trans (Int-⊆ V) V⊆W) ,
        ∧-right and)

    prop-3 : ∀ x V W → V ∈ Neighborhoods x → W ∈ Neighborhoods x → (V ∩ W) ∈ Neighborhoods x
    prop-3 x V W V-in W-in = satisfy-cond (V ∩ W) $
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

    prop-4 : ∀ x V → V ∈ Neighborhoods x → ∃ \W → W ∈ Neighborhoods x → ∀ y → y ∈ W → V ∈ Neighborhoods y
    prop-4 x V V-in = Int V , (\W-in y y∈W → satisfy-cond V $ (⊆-∈-power $ in-set V V-in) , y∈W)

{-
  module Closure-decides-Topology where
    Topology-from-Closure :
      (Neighborhoods′ : ∀ x → Set)
      → (∀ x → x ∈ set → Neighborhoods′ x ≢ ∅)
      → Neighbor-props.Neighbor-prop-type.cond Neighborhoods′
      → TopSpace
    Topology-from-Closure Neighborhoods′ non-∅ (cond-1 , cond-2 , cond-3 , cond-4) = record
      { set = set
      ; Open = Open-set
      ; OpenFamily = ⊆-∈-power (\O O:open → ∧-left $ replace-cond O O:open)
      ; ∅-open = satisfy-cond ∅ $ ⊆-∈-power (∅-⊆ set) , (\x x∈∅ → ⊥-elim $ elem-∈ x x∈∅)
      ; all-open = satisfy-cond set $ ⊆-∈-power ⊆-refl , (\x x∈set → cond-2 x  _ _ (⊆-∈-power ⊆-refl) ({!!}) (∅-⊆ set))
      ; ⋃-open = {!!}
      ; ∩-open = {!!}
      }
      where
        Open-set = ⟦ O ∈ P[ set ] ∣ (∀ x → x ∈ O → O ∈ Neighborhoods′ x) ⟧
-}

