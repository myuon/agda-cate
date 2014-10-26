module Sets.Topology.Closure where

open import Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Sets.Sets
open import Sets.Topology.Topology
open import Sets.Topology.Interior

module Closure (X : TopSpace) where
  open TopSpace X

  Closed : Set
  Closed = ⟦ V ∈ P[ set ] ∣ (set \\ V) ∈ Open ⟧

  private
    in-Closed-set : ∀ X → X ∈ Closed → X ⊆ set
    in-Closed-set X X:closed = ∈-⊆-power $ ∧-left $ replace-cond X X:closed

    closed-open : ∀ {X} → X ∈ Closed → (set \\ X) ∈ Open
    closed-open {X} X:closed = ∧-right $ replace-cond X X:closed

  module Closed-lemmas where
    all-closed : set ∈ Closed
    all-closed = satisfy-cond set $ ⊆-∈-power ⊆-refl , ≡-∈ (≡-sym A\\A≡∅) ∅-open

    ∅-closed : ∅ ∈ Closed
    ∅-closed = satisfy-cond ∅ $ ⊆-∈-power (∅-⊆ set) , ≡-∈ (≡-sym \\-∅) all-open

    ∪-closed : {A B : Set} → A ∈ Closed → B ∈ Closed → A ∪ B ∈ Closed
    ∪-closed {A} {B} A:closed B:closed = satisfy-cond (A ∪ B) $ ⊆-∈-power (⊆-cong ≡-refl ∪-idempotent $
      ⊆-cong-∪ (in-Closed-set A A:closed) (in-Closed-set B B:closed)) ,
      (≡-∈ (≡-sym de-Morgan-∪) $ ∩-open (closed-open A:closed) (closed-open B:closed))

--    ⋂-closed : {F : Set} → F ⊆ Closed → ⋂ F ∈ Closed
--    ⋂-closed {F} F⊆Closed = satisfy-cond (⋂ F) $ ⊆-∈-power {!!} , {!!}

  Closure-set : ∀ U → Set
  Closure-set U = ⟦ V ∈ Closed ∣ V ⊆ U ⟧

  Closure : ∀ U → Set
  Closure U = ⋃ Closure-set U

  -- Closure (set - M) ≡ set - (Int M)
  -- Closure-props

  module Interior-Closed where
    open Interior X

--    Closure-Int : ∀ M → M ⊆ set → Closure (set \\ M) ≡ set \\ (Int M)
--    Closure-Int M M⊆set = ⊆-antisym (\x x-in → let ex = replace-in-union x x-in ; U = proj₁ ex ; U-cond = proj₂ ex in satisfy-cond x $ {!!} , {!!}) {!!}
