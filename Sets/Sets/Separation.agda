module Sets.Sets.Separation where

open import Level
open import Function
open import Data.Empty
open import Data.Product
open import Relation.Binary
open import Relation.Nullary
open import Sets.Sets.Basic
open import Sets.Sets.Extensionality
open import Sets.Sets.Pairing
open import Sets.Sets.Union

postulate
  separation : (A : Set) → (P : Set → Set₁) → ∃ \B → ∀ x → x ∈ B ⇔ (x ∈ A) ∧ P x

cond-set : (A : Set) → (∀ X → Set₁) → Set
cond-set A f = proj₁ (separation A f)

syntax cond-set A (\X → P) = ⟦ X ∈ A ∣ P ⟧

module replacement-lemmas where
  replace-cond : ∀{A P} → ∀ Z → Z ∈ (cond-set A P) → (Z ∈ A) ∧ P Z
  replace-cond {A} {P} Z Z-∈ = proj⃗ (proj₂ (separation A P) Z) Z-∈

  satisfy-cond : ∀{A P} → ∀ Z → (Z ∈ A) ∧ P Z → Z ∈ (cond-set A P)
  satisfy-cond {A} {P} Z cond = proj⃖ (proj₂ (separation A P) Z) cond
open replacement-lemmas public

infixr 7 _∩_
_∩_ : (A B : Set) → Set
A ∩ B = ⟦ X ∈ A ∣ X ∈ B ⟧

module ∩-Hetero where
  ∩⇔∧ : {A B : Set} → ∀ X → X ∈ A ∩ B ⇔ (X ∈ A) ∧ (X ∈ B)
  ∩⇔∧ {A} {B} X = X∈A∧X∈B , X∈A∩B
    where
      X∈A∧X∈B : X ∈ A ∩ B → (X ∈ A) ∧ (X ∈ B)
      X∈A∧X∈B X∈A∩B = proj⃗ (proj₂ (separation A $ \X → X ∈ B) X) X∈A∩B

      X∈A∩B : (X ∈ A) ∧ (X ∈ B) → X ∈ A ∩ B
      X∈A∩B and = proj⃖ (proj₂ (separation A $ \X → X ∈ B) X) and

  ∩-∧ : {A B : Set} → ∀ X → X ∈ A ∩ B → (X ∈ A) ∧ (X ∈ B)
  ∩-∧ X = proj⃗ (∩⇔∧ X)

  ∧-∩ : {A B : Set} → ∀ X → (X ∈ A) ∧ (X ∈ B) → X ∈ A ∩ B
  ∧-∩ X = proj⃖ (∩⇔∧ X)

  ∩-⊆ˡ : {A B : Set} → A ∩ B ⊆ A
  ∩-⊆ˡ x x∈A∩B = ∧-left $ ∩-∧ x x∈A∩B

  ∩-⊆ʳ : {A B : Set} → A ∩ B ⊆ B
  ∩-⊆ʳ x x∈A∩B = ∧-right $ ∩-∧ x x∈A∩B

  ⊆-cong-∩ : {A B C D : Set} → A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D
  ⊆-cong-∩ A⊆B C⊆D x x∈A∩C = ∧-∩ x $ (A⊆B x $ ∩-⊆ˡ x x∈A∩C) , (C⊆D x $ ∩-⊆ʳ x x∈A∩C)

  ∩-cong : {A B C D : Set} → A ≡ B → C ≡ D → A ∩ C ≡ B ∩ D
  ∩-cong A≡B C≡D rewrite A≡B | C≡D = ≡-refl
open ∩-Hetero public

module ∩-lemmas where
  ∩-idempotent : {A : Set} → A ∩ A ≡ A
  ∩-idempotent = ⇔-extensionality $ \X →
    (\X∈A∩A → ∧-left $ ∩-∧ X X∈A∩A) ,
    (\X∈A → ∧-∩ X $ ∧-refl X∈A)

  ∩-comm : {A B : Set} → A ∩ B ≡ B ∩ A
  ∩-comm = ⇔-extensionality $ \X → (∧-∩ X ∘ proj⃗ (∧-comm _ _) ∘ ∩-∧ X) , (∧-∩ X ∘ proj⃗ (∧-comm _ _) ∘ ∩-∧ X)

  ∩-assoc : {A B C : Set} → (A ∩ B) ∩ C ≡ A ∩ (B ∩ C)
  ∩-assoc {A} {B} {C} = ⇔-extensionality $ \X →
    (\X-in → ∧-∩ X $ map id (∧-∩ X) $ proj⃗ (∧-assoc _ _ _) $ map (∩-∧ X) id $ ∩-∧ X X-in) ,
    (\X-in → ∧-∩ X $ map (∧-∩ X) id $ proj⃖ (∧-assoc _ _ _) $ map id (∩-∧ X) $ ∩-∧ X X-in)

  ⊆⇔∩ : {A B : Set} → A ⊆ B ⇔ A ∩ B ≡ A
  ⊆⇔∩ = (\A⊆B → ⇔-extensionality $ \X →
    (\X∈A∩B → ∧-left $ ∩-∧ X X∈A∩B) , (\X∈A → ∧-∩ X $ X∈A , A⊆B X X∈A)) ,
    (\eq X X∈A → ∩-⊆ʳ X $ proj⃖ (app-extensionality eq X) X∈A)

  ∩-⊆ : {A B : Set} → A ∩ B ≡ A → A ⊆ B
  ∩-⊆ = proj⃖ ⊆⇔∩

  ⊆-∩ : {A B : Set} → A ⊆ B → A ∩ B ≡ A
  ⊆-∩ = proj⃗ ⊆⇔∩

  ∩-∅ : {A : Set} → A ∩ ∅ ≡ ∅
  ∩-∅ {A} = ⇔-extensionality $ \X →
    (\X∈A∩∅ → ∧-right $ ∩-∧ X X∈A∩∅) ,
    (\X∈∅ → ∧-∩ X $ (∅-⊆ X X∈∅) , X∈∅)

  ∩-≡ : {A B C D : Set} → A ≡ C → B ≡ D → A ∩ B ≡ C ∩ D
  ∩-≡ A≡C B≡D = ⇔-extensionality $ \X →
    (\X∈A∩B → ∧-∩ X $ proj⃗ (∧-cong (app-extensionality A≡C X) (app-extensionality B≡D X)) $ ∩-∧ X X∈A∩B) ,
    (\X∈C∩B → ∧-∩ X $ proj⃗ (∧-cong (app-extensionality (≡-sym A≡C) X) (app-extensionality (≡-sym B≡D) X)) $ ∩-∧ X X∈C∩B)
    where
      open ⇔-Reasoning

{-
  ⋂-2-∩ : {A B : Set} → ⋂ [ A , B ] ≡ A ∩ B
  ⋂-2-∩ {A} {B} = ⊆-antisym
    (\x x-in → let and = replace-cond x x-in in ∧-∩ x $ ∧-right and A A∈[A,B] , ∧-right and B B∈[A,B])
    (\x x∈A∩B →
      satisfy-cond x $
        (satisfy-in-union x $ A , A∈[A,B] , (∧-left $ ∩-∧ x x∈A∩B)) ,
        (\Y Y∈[A,B] → lemma x Y x∈A∩B $ in-[A,B] Y Y∈[A,B]))
    where
      lemma : ∀ x Y → x ∈ A ∩ B → (Y ≡ A) ∨ (Y ≡ B) → x ∈ Y
      lemma x Y x-in (∨-left Y≡A) rewrite Y≡A = ∧-left $ ∩-∧ x x-in
      lemma x Y x-in (∨-right Y≡B) rewrite Y≡B = ∧-right $ ∩-∧ x x-in
-}

--  ⋂-cong : {A B : Set} → A ⊆ B → ⋂ B ⊆ ⋂ A
--  ⋂-cong A⊆B x x∈⋂B =
--    satisfy-cond x $ (satisfy-in-union x $ {!!} , {!!} , {!!}) , {!!}
--    distributive law

_\\_ : (A B : Set) → Set
A \\ B = ⟦ X ∈ A ∣ X ∉ B ⟧

module \\-lemmas where
  A\\A≡∅ : {A : Set} → A \\ A ≡ ∅
  A\\A≡∅ {A} = antisym (\x x∈A\\A → let and = replace-cond x x∈A\\A in ⊥-elim $ ∧-right and $ ∧-left and) ∅-⊆
    where
      open IsPartialOrder ⊆-isPartialOrder

  \\-⊆ : {A B : Set} → A \\ B ⊆ A
  \\-⊆ x x∈A\\B = ∧-left $ replace-cond x x∈A\\B

  \\-∅ : {A : Set} → A \\ ∅ ≡ A
  \\-∅ = ⊆-antisym \\-⊆ (\x x∈A → satisfy-cond x $ x∈A , (\x∈∅ → elem-∈ x x∈∅))

  de-Morgan-∪ : {U A B : Set} → (U \\ (A ∪ B)) ≡ ((U \\ A) ∩ (U \\ B))
  de-Morgan-∪ {U} {A} {B} = ⊆-antisym
    (\x x-in → let and = replace-cond x x-in ; x∈U = ∧-left and
                   x-nin-and = ∉-∪-∧ x $ ∧-right and in
        ∧-∩ x $ (satisfy-cond x $ x∈U , ∧-left x-nin-and) , (satisfy-cond x $ x∈U , ∧-right x-nin-and))
    (\x x-in → let and = replace-cond x x-in in
      satisfy-cond x $
        (∧-left $ replace-cond x $ ∧-left and) ,
        (\x∈A∪B → lemma x (∪-∨ x x∈A∪B) and))
    where
      lemma : ∀ x → x ∈ A ∨ x ∈ B → x ∈ (U \\ A) ∧ x ∈ (U \\ B) → ⊥
      lemma x (∨-left x∈A) and = ∧-right (replace-cond x $ ∧-left and) x∈A
      lemma x (∨-right x∈B) and = ∧-right (replace-cond x $ ∧-right and) x∈B
open \\-lemmas public

{-
\\-∪ : {A B C : Set} → A \\ (B \\ C) ≡ (A \\ (B ∪ C)) ∪ (A ∩ C)
\\-∪ {A} {B} {C} = antisym lemma-1 {!!}
  where
    open IsPartialOrder ⊆-isPartialOrder

    lemma-1 : A \\ (B \\ C) ⊆ (A \\ (B ∪ C)) ∪ (A ∩ C)
    lemma-1 x x∈A\\[B\\C] = ∨-∪ x $ {!!}
      where
        x∈A∧x∉B\\C = replace-cond x x∈A\\[B\\C]
-}

{-
\\-\\-⊆ : {A B : Set} → A \\ (A \\ B) ≡ B
\\-\\-⊆ {A} {B} = antisym lemma-1 {!!}
  where
    open IsPartialOrder ⊆-isPartialOrder

    lemma-1 : A \\ (A \\ B) ⊆ B
    lemma-1 x x∈A\\[A\\B] = {!!}
      where
        x∈A = ∧-left $ replace-cond x x∈A\\[A\\B]
        x∉A\\B = ∧-right $ replace-cond x x∈A\\[A\\B]
-}

open ∩-lemmas public
