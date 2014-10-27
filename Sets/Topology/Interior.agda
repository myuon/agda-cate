module Sets.Topology.Interior where

open import Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Sets.Sets
open import Sets.Topology.Topology

module Interior (X : TopSpace) where
  module explicit where
    open TopSpace

    Interior-set-in : TopSpace → ∀ U → Set
    Interior-set-in Y U = ⟦ V ∈ Open Y ∣ V ⊆ U ⟧

    Int-in : TopSpace → ∀ U → Set
    Int-in Y U = ⋃ Interior-set-in Y U

  open TopSpace X

  Interior-set : ∀ U → Set
  Interior-set U = ⟦ V ∈ Open ∣ V ⊆ U ⟧

  Int : ∀ U → Set
  Int U = ⋃ Interior-set U

  module Interior-lemmas where
    module Interior-cond where
      module Interior-cond-type (Y : TopSpace) (Int′ : ∀ U → Set) where
        prop-1 = ∀ M → Int′ M ⊆ M
        prop-2 = ∀ M → M ∈ P[ TopSpace.set Y ] → Int′ M ∈ (TopSpace.Open Y)
        prop-3 = ∀ M O → O ⊆ M → O ∈ (TopSpace.Open Y) → O ⊆ Int′ M
        cond = prop-1 ∧ prop-2 ∧ prop-3

      Int-⊆ : ∀ M → Int M ⊆ M
      Int-⊆ M x x∈Int = let ex = proj⃗ (proj₂ (∃-union _) x) x∈Int in
        ∧-right (replace-cond (proj₁ ex) (∧-left $ proj₂ ex)) x (∧-right $ proj₂ ex)

      Int-Open : ∀ M → Int M ∈ Open
      Int-Open M = ⋃-open {⟦ V ∈ Open ∣ V ⊆ M ⟧} (\V V-in → ∧-left $ replace-cond V V-in)

      Open-⊆-Int : ∀ M O → O ⊆ M → O ∈ Open → O ⊆ Int M
      Open-⊆-Int M O O⊆M O:open x x∈O = satisfy-in-union x $ O , (satisfy-cond O (O:open , O⊆M) , x∈O)

      Interior-iff-cond :
        (Int′ : ∀ U → Set)
        → Interior-cond-type.cond X Int′
        → ∀ M → M ∈ P[ set ] → Int′ M ≡ Int M
      Interior-iff-cond Int′ (cond-1 , cond-2 , cond-3) M M-in = ⊆-antisym
        (⋃-∈-⊆ $ satisfy-cond (Int′ M) $ cond-2 M M-in , cond-1 M)
        (\x x∈IntM → let ex = replace-in-union x x∈IntM
                         V = proj₁ ex
                         V-cond = replace-cond V $ ∧-left $ proj₂ ex in
          cond-3 M V (∧-right V-cond) (∧-left V-cond) x $ ∧-right $ proj₂ ex)
    open Interior-cond public

    preserveOpen : ∀ M → M ∈ Open ⇔ M ≡ Int M
    preserveOpen M = lemma , (\eq → ≡-∈ (≡-sym eq) (Int-Open M))
      where
        open IsPartialOrder ⊆-isPartialOrder

        lemma : M ∈ Open → M ≡ Int M
        lemma M:open = antisym
          (\x x∈M → satisfy-in-union x $ M , (satisfy-cond M (M:open , ⊆-refl) , x∈M))
          (\x x∈IntM → let ex = replace-in-union x x∈IntM in
            (∧-right $ replace-cond (proj₁ ex) (∧-left $ proj₂ ex)) x (∧-right $ proj₂ ex))

    ⊆-cong-Int : ∀ M N → M ⊆ N → Int M ⊆ Int N
    ⊆-cong-Int M N M⊆N x x∈Mᵒ = satisfy-in-union x $ (Int M) , (satisfy-cond (Int M) (Int-Open M , (\y y∈Mᵒ → M⊆N y $ (Int-⊆ M) y y∈Mᵒ)) , x∈Mᵒ)

  module Interior-props where
    module Interior-props-type (Y : TopSpace) (Int′ : ∀ U → Set) where
      prop-1 = Int′ (TopSpace.set Y) ≡ (TopSpace.set Y)
      prop-2 = ∀ M → Int′ M ⊆ M
      prop-3 = ∀ M N → Int′ (M ∩ N) ≡ Int′ M ∩ Int′ N
      prop-4 = ∀ M → Int′ (Int′ M) ≡ Int′ M
      cond = prop-1 ∧ prop-2 ∧ prop-3 ∧ prop-4

    open Interior-lemmas
    prop-1 : (Int set) ≡ set
    prop-1 = ≡-sym $ proj⃗ (preserveOpen set) all-open

    prop-2 : ∀ M → Int M ⊆ M
    prop-2 M = Int-⊆ M

    prop-3 : ∀ M N → Int (M ∩ N) ≡ Int M ∩ Int N
    prop-3 M N = antisym lemma lemma-2
      where
        open IsPartialOrder ⊆-isPartialOrder

        lemma : Int (M ∩ N) ⊆ Int M ∩ Int N
        lemma x x∈Int[M∩N] = ∧-∩ x $ x∈IntM , x∈IntN
          where
            ex = replace-in-union x x∈Int[M∩N]
            U = proj₁ ex ; U-cond = replace-cond U $ ∧-left $ proj₂ ex

            x∈IntM : x ∈ Int M
            x∈IntM = satisfy-in-union x $ U , (satisfy-cond U
              (∧-left U-cond , (\y y∈U → ∩-⊆ˡ y $ (∧-right U-cond) y y∈U)) ,
              ∧-right (proj₂ ex))

            x∈IntN : x ∈ Int N
            x∈IntN = satisfy-in-union x $ U , (satisfy-cond U
              (∧-left U-cond , (\y y∈U → ∩-⊆ʳ y $ (∧-right U-cond) y y∈U)) ,
              ∧-right (proj₂ ex))

        lemma-2 : Int M ∩ Int N ⊆ Int (M ∩ N)
        lemma-2 x x∈Mᵒ∩Nᵒ = satisfy-in-union x $ U-M ∩ U-N ,
          (satisfy-cond (U-M ∩ U-N) (∩-open (∧-left U-M-cond) (∧-left U-N-cond) , ⊆-cong-∩ (∧-right U-M-cond) (∧-right U-N-cond)) , ∧-∩ x ((∧-right $ proj₂ ex-M) , (∧-right $ proj₂ ex-N)))
          where
            ex-M = replace-in-union x (∩-⊆ˡ x x∈Mᵒ∩Nᵒ)
            U-M = proj₁ ex-M ; U-M-cond = replace-cond U-M $ ∧-left $ proj₂ ex-M
            ex-N = replace-in-union x (∩-⊆ʳ x x∈Mᵒ∩Nᵒ)
            U-N = proj₁ ex-N ; U-N-cond = replace-cond U-N $ ∧-left $ proj₂ ex-N

    prop-4 : ∀ M → Int (Int M) ≡ Int M
    prop-4 M = ≡-sym $ proj⃗ (preserveOpen (Int M)) $ Int-Open M
      where
        open IsPartialOrder ⊆-isPartialOrder

    module Interior-decides-Topology where
      Topology-from-Interior :
        (Int′ : ∀ U → Set)
        → Interior-props-type.cond X Int′
        → TopSpace
      Topology-from-Interior Int′ (cond-1 , cond-2 , cond-3 , cond-4) = record
        { set = set
        ; Open = Open-set
        ; OpenFamily = ⊆-∈-power (\x x:open → ∧-left $ replace-cond x x:open)
        ; ∅-open = satisfy-cond ∅ $ ⊆-∈-power ∅-⊆ , ∅-⊆ , ⊆-∅ (cond-2 ∅)
        ; all-open = satisfy-cond set $ (⊆-∈-power ⊆-refl) , ⊆-refl , cond-1
        ; ⋃-open = ⋃-open-Int
        ; ∩-open = ∩-open-Int
        }
        where
          Open-set = ⟦ M ∈ P[ set ] ∣ M ⊆ set ∧ Int′ M ≡ M ⟧

          ⋃-open-Int : {F : Set} → F ⊆ Open-set → ⋃ F ∈ Open-set
          ⋃-open-Int {F} F⊆Open-set = satisfy-cond (⋃ F) $ (⊆-∈-power ∪F⊆set) , ∪F⊆set , ⊆-antisym (cond-2 (⋃ F)) lemma
            where
              ∪F⊆set : ⋃ F ⊆ set
              ∪F⊆set x x∈∪F = let ex = replace-in-union x x∈∪F ; U = proj₁ ex
                                  U-cond = proj₂ ex in
                  ∈-⊆-power (∧-left $ replace-cond U $ F⊆Open-set U (∧-left U-cond)) x $ ∧-right U-cond

              Int′-cong : {X Y : Set} → X ≡ Y → Int′ X ≡ Int′ Y
              Int′-cong X≡Y rewrite X≡Y = ≡-refl

              in-F : ∀ X → X ∈ F → Int′ X ≡ X
              in-F X X∈F = ∧-right $ ∧-right $ replace-cond X $ F⊆Open-set X X∈F

              lemma : ⋃ F ⊆ Int′ (⋃ F)
              lemma = ⋃-⊆-∀ (\X X∈F → ∩-⊆ $ let open ≡-Reasoning in
                begin
                  X ∩ Int′ (⋃ F) ≡⟨ ∩-cong (≡-sym $ in-F X X∈F) ≡-refl ⟩
                  Int′ X ∩ Int′ (⋃ F) ≡⟨ ≡-sym $ cond-3 X (⋃ F) ⟩
                  Int′ (X ∩ (⋃ F)) ≡⟨ Int′-cong (⊆-∩ $ ⋃-∈-⊆ X∈F) ⟩
                  Int′ X ≡⟨ in-F X X∈F ⟩
                  X
                ∎)

          ∩-open-Int : {A B : Set} → A ∈ Open-set → B ∈ Open-set → A ∩ B ∈ Open-set
          ∩-open-Int {A} {B} A:open B:open = satisfy-cond (A ∩ B) $ (⊆-∈-power A∩B⊆set) , A∩B⊆set , lemma
            where
              A∩B⊆set : A ∩ B ⊆ set
              A∩B⊆set x x∈A∩B = (∧-left $ ∧-right $ replace-cond A A:open) x $ ∧-left $ replace-cond x x∈A∩B

              to-be-open : ∀ U → U ∈ Open-set → Int′ U ≡ U
              to-be-open U U:open = ∧-right $ ∧-right $ replace-cond U U:open

              lemma : Int′ (A ∩ B) ≡ A ∩ B
              lemma = let open ≡-Reasoning in
                begin
                  Int′ (A ∩ B) ≡⟨ cond-3 A B ⟩
                  Int′ A ∩ Int′ B ≡⟨ ∩-cong (to-be-open A A:open) (to-be-open B B:open) ⟩
                  A ∩ B
                ∎

      uniqueness :
        (Int′ : ∀ U → Set)
        → (cond : Interior-props-type.cond X Int′)
        → Interior-cond-type.cond (Topology-from-Interior Int′ cond) Int′
      uniqueness Int′ (cond-1 , cond-2 , cond-3 , cond-4) = cond-2 , (\M M∈P[set] → satisfy-cond (Int′ M) $ ⊆-∈-power (Int′M⊆set M M∈P[set]) , Int′M⊆set M M∈P[set] , cond-4 M) , lemma
        where
          T = Topology-from-Interior Int′ (cond-1 , cond-2 , cond-3 , cond-4)

          Int′M⊆set : ∀ M → M ∈ P[ set ] → Int′ M ⊆ set
          Int′M⊆set M M∈P[set] = ⊆-trans (cond-2 M) (∈-⊆-power M∈P[set])

          Int′-cong : {X Y : Set} → X ≡ Y → Int′ X ≡ Int′ Y
          Int′-cong X≡Y rewrite X≡Y = ≡-refl

          lemma : ∀ M O → O ⊆ M → O ∈ (TopSpace.Open T) → O ⊆ Int′ M
          lemma M O O⊆M O:open = ∩-⊆ $ let open ≡-Reasoning in
            begin
              O ∩ Int′ M ≡⟨ ∩-cong (≡-sym $ ∧-right $ ∧-right $ replace-cond O O:open) ≡-refl ⟩
              Int′ O ∩ Int′ M ≡⟨ ≡-sym $ cond-3 O M ⟩
              Int′ (O ∩ M) ≡⟨ Int′-cong (⊆-∩ O⊆M) ⟩
              Int′ O ≡⟨ ∧-right $ ∧-right $ replace-cond O O:open ⟩
              O
            ∎

