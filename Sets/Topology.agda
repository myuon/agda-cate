module Sets.Topology where

open import Sets.Topology.Topology public
open import Sets.Topology.Interior public

{-
module Closure (X : TopSpace) where
  open TopSpace X

  Closed : Set
  Closed = ⟦ V ∈ P[ set ] ∣ (set \\ V) ∈ Open ⟧

  -- module Closed-lemmas where

  Closure-set : ∀ U → Set
  Closure-set U = ⟦ V ∈ Closed ∣ V ⊆ U ⟧

  Closure : ∀ U → Set
  Closure U = ⋃ Closure-set U

  -- Closure (set - M) ≡ set - (Int M)
  -- Closure-props

module Neighborhood (X : TopSpace) where
  open TopSpace X
  open Interior X

  nbh-of : ∀ x → Set
  nbh-of x = ⟦ U ∈ Open ∣ x ∈ Int U ⟧
-}
