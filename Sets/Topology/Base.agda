module Sets.Topology.Base where

open import Function
open import Data.Product

open import Sets.Sets
open import Sets.Topology.Topology

generated-by : (X : Set) (S : Set) → S ∈ P[ P[ X ] ] → TopSpace
generated-by X S S-family = record
  { set = X
  ; Open = Open-inf
  ; isTopology = record
    { OpenFamily = ⊆-∈-power OpenFamily-inf
    ; ∅-open = ∅-open-inf
    ; all-open = all-open-inf
    ; ⋃-open = ⋃-open-inf
    ; ∩-open = ∩-open-inf
    }
  }
  where
  Open≢∅ = (∃-∅ (P[ X ]) $ satisfy-cond P[ X ] $
      ∈-refl-power , Discrete-is-Topology X , ∈-⊆-power S-family)
  Open-inf = ⋂ ⟦ O ∈ P[ P[ X ] ] ∣ IsTopology X O ∧ S ⊆ O ⟧ Open≢∅

  OpenFamily-inf : Open-inf ⊆ P[ X ]
  OpenFamily-inf O O:open = replace-intersection Open≢∅ O O:open P[ X ]
    (satisfy-cond P[ X ] $ ∈-refl-power ,
                           Discrete-is-Topology X ,
                           ∈-⊆-power S-family)

  ∅-open-inf : ∅ ∈ Open-inf
  ∅-open-inf = satisfy-intersection Open≢∅ ∅ $
    \Y Y:open → IsTopology.∅-open (∧-left $ ∧-right $ replace-cond Y Y:open)

  all-open-inf : X ∈ Open-inf
  all-open-inf = satisfy-intersection Open≢∅ X $
    \Y Y:open → IsTopology.all-open (∧-left $ ∧-right $ replace-cond Y Y:open)

  ⋃-open-inf : ∀{F} → F ⊆ Open-inf → ⋃ F ∈ Open-inf
  ⋃-open-inf {F} F⊆open = satisfy-intersection Open≢∅ _ Open⊆O
    where
    Open⊆O : ∀ O → O ∈ ⟦ O ∈ P[ P[ X ] ] ∣ IsTopology X O ∧ S ⊆ O ⟧ → ⋃ F ∈ O
    Open⊆O O O-in = IsTopology.⋃-open
      (∧-left $ ∧-right $ replace-cond O O-in)
      (\A A∈F → replace-intersection Open≢∅ A (F⊆open A A∈F) O $ satisfy-cond O $ 
        (∧-left $ replace-cond O O-in) ,
        (∧-left $ ∧-right $ replace-cond O O-in) ,
        (∧-right $ ∧-right $ replace-cond O O-in))

  ∩-open-inf : ∀{A B} → A ∈ Open-inf → B ∈ Open-inf → A ∩ B ∈ Open-inf
  ∩-open-inf A:open B:open = satisfy-intersection Open≢∅ _ $ \Y Y:open →
    IsTopology.∩-open (∧-left $ ∧-right $ replace-cond Y Y:open)
                      (∧-right (replace-cond _ A:open) Y Y:open)
                      (∧-right (replace-cond _ B:open) Y Y:open)

generated-Topology : (X : Set) (S : Set) → S ∈ P[ P[ X ] ] → Set
generated-Topology X S S-family = TopSpace.Open $ generated-by X S S-family

record Subbase (X : TopSpace) : Set₁ where
  open TopSpace X

  field
    Subbasis : Set

  field
    SubbasisFamily : Subbasis ⊆ Open
    generating : Open ≡ TopSpace.Open (generated-by set Subbasis (⊆-∈-power $ ⊆-trans SubbasisFamily $ ∈-⊆-power OpenFamily))

record IsBase (X : TopSpace) (Basis : Set) : Set₁ where
  open TopSpace X

  field
    BasisFamily : Basis ⊆ Open
    generating : ∀ O → O ∈ Open → ∃ \W → (∀ Ws → Ws ∈ W → Ws ∈ Basis) ∧ O ≡ ⋃ W

record Base (X : TopSpace) : Set₁ where
  open TopSpace X

  field
    Basis : Set
    isBase : IsBase X Basis

  open IsBase isBase public

module Base-lemmas (X : TopSpace) where
  open TopSpace X

  base-is-subbase : ∀ (B : Base X) →
    Open ≡ generated-Topology set (Base.Basis B) (⊆-∈-power $ ⊆-trans (Base.BasisFamily B) (∈-⊆-power OpenFamily))
  base-is-subbase B = ⊆-antisym O⊆O[B] O[B]⊆O
    where
    open Base B
    B-space = generated-by set Basis (⊆-∈-power $ ⊆-trans (Base.BasisFamily B) (∈-⊆-power OpenFamily))
    O[B] = TopSpace.Open B-space
    O[B]≢∅ = ∃-∅ P[ set ] $ satisfy-cond P[ set ] $
      ∈-refl-power , (Discrete-is-Topology set) , (⊆-trans (Base.BasisFamily B) (∈-⊆-power OpenFamily))

    O⊆O[B] : Open ⊆ O[B]
    O⊆O[B] U U:open = satisfy-intersection O[B]≢∅ U $ lemma
      where
      lemma : ∀ O O-in → U ∈ O
      lemma O O-in = ≡-∈ (≡-sym U≡⋃W) (IsTopology.⋃-open (∧-left $ proj₂ $ replace-cond O O-in) (\Wₐ Wₐ∈W → ∧-right (∧-right O-cond) Wₐ $ ∧-left W-cond Wₐ Wₐ∈W))
        where
        O-cond = replace-cond O O-in
        W-ex = generating U U:open ; W = proj₁ W-ex ; W-cond = proj₂ W-ex
        U≡⋃W = ∧-right W-cond

    O[B]⊆O : O[B] ⊆ Open
    O[B]⊆O U U:openB = ∧-right (replace-cond U U:openB) Open (satisfy-cond Open $ OpenFamily , isTopology , BasisFamily)

{-
  base-iff : ∀ B → B ⊆ Open → IsBase X B ⇔
    (∀ O → O ∈ Open → ∀ x → ∃ \W → x ∈ O → W ∈ B ∧ x ∈ W ∧ W ⊆ O)
  base-iff B B⊆open = cond , base
    where
    cond : IsBase X B → ∀ O → O ∈ Open → ∀ x → x ∈ O → ∃ \W → W ∈ B ∧ x ∈ W ∧ W ⊆ O
    cond isBase O O:open x x:O =
      Wₐ , ∧-left W-cond Wₐ (∧-left Wₐ-cond) ,
      ∧-right Wₐ-cond , (\a a∈Wₐ → ∈-≡ (≡-sym $ ∧-right W-cond) $
        satisfy-in-union a $ Wₐ , proj₁ Wₐ-cond , a∈Wₐ)
      where
      open IsBase isBase
      W-ex = generating O O:open
      W = proj₁ W-ex ; W-cond = proj₂ W-ex

      x∈∪W = ∈-≡ (∧-right W-cond) x:O
      Wₐ-ex = replace-in-union x x∈∪W
      Wₐ = proj₁ Wₐ-ex ; Wₐ-cond = proj₂ Wₐ-ex

    base : (∀ O → O ∈ Open → ∀ x → ∃ \W → x ∈ O → W ∈ B ∧ x ∈ W ∧ W ⊆ O) → IsBase X B
    base f = record
      { BasisFamily = B⊆open
      ; generating = generating-base
      }
      where
      generating-base : ∀ O → O ∈ Open → ∃ \W → (∀ Ws → Ws ∈ W → Ws ∈ B) ∧ O ≡ ⋃ W
      generating-base O O:open = W , Image-⊆ W-set , ⊆-antisym O⊆∪W ∪W⊆O
        where
        W-set : O ⟶ B
        W-set x = proj₁ (f O O:open x) , ∧-left ∘ proj₂ (f O O:open x)
        W-ex = in-Image {f = W-set}
        W = proj₁ W-ex ; W-cond = proj₂ W-ex

        O⊆∪W : O ⊆ ⋃ W
        O⊆∪W x x:O = satisfy-in-union x $ V , V∈W , x∈V
          where
          V = ⟨ W-set ⟩ x
          V∈W = proj⃖ (W-cond V) $ x , x:O , ≡-refl
          x∈V = ∧-left $ ∧-right $ proj₂ (f O O:open x) x:O

        ∪W⊆O : ⋃ W ⊆ O
        ∪W⊆O x x:∪W =
          ∧-right (∧-right $ proj₂ (f O O:open z) (∧-left $ proj₂ ∃z)) x
                  (∈-≡ (≡-sym $ ∧-right $ proj₂ ∃z) $ x∈V)
          where
          V-ex = replace-in-union x x:∪W
          V = proj₁ V-ex ; V-cond = proj₂ V-ex
          x∈V = ∧-right V-cond
          V∈W = ∧-left V-cond
          ∃z = proj⃗ (W-cond V) V∈W
          z = proj₁ ∃z
          Wz = ⟨ W-set ⟩ z
-}

open Base-lemmas public

