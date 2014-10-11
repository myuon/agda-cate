module Categories.Categories.Lattice where

open import Level
open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties
import Algebra.Properties.Lattice as APL
open import Relation.Binary
open import Categories.Category
open import Categories.Categories.Poset
open import Categories.Objects.Objects

Lattice-A-Category : ∀{ℓ₁ ℓ₂} (L : Lattice ℓ₁ ℓ₂) → Category ℓ₁ ℓ₂ ℓ₂
Lattice-A-Category L = Poset-A-Category (APL.poset L)

module FunctionProperties {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where
  IdentityOn : A → Op₂ A → Set _
  IdentityOn e _∙_ = ∀ a → (a ∙ e) ≈ a

record IsBoundedLattice {a ℓ} {A : Set a} (≈ : Rel A ℓ)
                        (∨ ∧ : Op₂ A) (0ₗ 1ₗ : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isLattice : IsLattice ≈ ∨ ∧
    ∨-0 : IdentityOn 0ₗ ∨
    ∧-1 : IdentityOn 1ₗ ∧

record BoundedLattice a ℓ : Set (suc (a ⊔ ℓ)) where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_

  field
    Carrier : Set a
    _≈_ : Rel Carrier ℓ
    _∨_ : Op₂ Carrier
    _∧_ : Op₂ Carrier
    0ₗ : Carrier
    1ₗ : Carrier

  field
    isBoundedLattice : IsBoundedLattice _≈_ _∨_ _∧_ 0ₗ 1ₗ

  lattice : Lattice _ _
  lattice = record { isLattice = IsBoundedLattice.isLattice isBoundedLattice }

  open IsBoundedLattice public

open Poset

1-In-Lattice : ∀{a ℓ} (L : BoundedLattice a ℓ)
  → TerminalObject (Poset-A-Category (APL.poset (BoundedLattice.lattice L)))
1-In-Lattice L = record
  { 1-obj = BoundedLattice.1ₗ L
  ; to-1 = to-1-L
  ; universality = universality-L
  }
  where
    open Poset renaming (_≈_ to _≈P_; _≤_ to _[_≤_])
    open BoundedLattice L

    private
      P = APL.poset (BoundedLattice.lattice L)
      C = Poset-A-Category P

    open Category C
    open IsEquivalence (isEquivalence P)
      renaming (refl to refl-P; sym to sym-P; trans to trans-P)

    to-1-L : (a : Obj) → P [ a ≤ 1ₗ ]
    to-1-L a = sym-P (∧-1 isBoundedLattice a)

    universality-L : (a : Obj) → (h : P [ a ≤ 1ₗ ]) → C [ h ≈ to-1-L a ]
    universality-L a _ = trans-P refl-P (sym-P (∧-1 isBoundedLattice a))
