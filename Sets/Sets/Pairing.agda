module Sets.Sets.Pairing where

open import Level
open import Function
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _,_ ; ∃)
open import Sets.Sets.Basic
open import Sets.Sets.Extensionality

postulate
  ∃-pairing : ∀ (A B : Set) → ∃ \(P : Set) → ∀ x → x ∈ P ⇔ (x ≡ A) ∨ (x ≡ B)

[_,_] : ∀(A B : Set) → Set
[ A , B ] = proj₁ (∃-pairing A B)

singleton : ∀(A : Set) → Set
singleton A = [ A , A ]

[,]-∨ : {A B : Set} → ∀ X → X ∈ [ A , B ] → (X ≡ A) ∨ (X ≡ B)
[,]-∨ {A} {B} X X∈[A,B] = proj⃗ (proj₂ (∃-pairing A B) X) X∈[A,B]

∨-[,] : {A B : Set} → ∀ X → (X ≡ A) ∨ (X ≡ B) → X ∈ [ A , B ]
∨-[,] {A} {B} X or = proj⃖ (proj₂ (∃-pairing A B) X) or

module paring-lemmas where
  [,]-comm : {A B : Set} → [ A , B ] ≡ [ B , A ]
  [,]-comm {A} {B} = proj⃖ extensionality (lift \x → lemma x)
    where
      lemma : (x : Set) → x ∈ [ A , B ] ⇔ x ∈ [ B , A ]
      lemma x = (\x∈[A,B] → ∨-[,] x $ proj⃗ (∨-comm _ _) $ [,]-∨ x x∈[A,B])
              , (\x∈[B,A] → ∨-[,] x $ proj⃗ (∨-comm _ _) $ [,]-∨ x x∈[B,A])

  in-[A,B] : {A B : Set} → (X : Set) → X ∈ [ A , B ] → (X ≡ A) ∨ (X ≡ B)
  in-[A,B] {A} {B} X X∈[A,B] = proj⃗ (proj₂ (∃-pairing A B) X) X∈[A,B]

  A∈[A,B] : {A B : Set} → A ∈ [ A , B ]
  A∈[A,B] {A} {B} = proj⃖ (proj₂ (∃-pairing A B) A) (∨-left ≡-refl)

  B∈[A,B] : {A B : Set} → B ∈ [ A , B ]
  B∈[A,B] {A} {B} = proj⃖ (proj₂ (∃-pairing A B) B) (∨-right ≡-refl)

  in-[A,A] : {A : Set} → ∀ X → X ∈ singleton A → X ≡ A
  in-[A,A] {A} X X∈[A,A] = ∨-unrefl $ in-[A,B] X X∈[A,A]

  ≡-singleton : {A B : Set} → A ≡ B ⇔ singleton A ≡ singleton B
  ≡-singleton {A} {B} = lemma , (\eq → ∨-unrefl $ in-[A,B] A $ A∈[B,B] eq)
    where
      A∈[B,B] : singleton A ≡ singleton B → A ∈ singleton B
      A∈[B,B] eq = ∈-≡ eq A∈[A,B]

      lemma : A ≡ B → singleton A ≡ singleton B
      lemma A≡B = proj⃖ extensionality $ lift $ \X
        → (\X∈A → proj⃖(proj₂ (∃-pairing B B) X) $ ∨-left $ ≡-trans (in-[A,A] {A} X X∈A) A≡B)
        , (\X∈B → proj⃖(proj₂ (∃-pairing A A) X) $ ∨-left $ ≡-trans (in-[A,A] {B} X X∈B) $ ≡-sym A≡B)
open paring-lemmas public

module paring-props where
  prop-1 : {A B : Set} → [ A , B ] ≡ singleton A ⇔ A ≡ B
  prop-1 {A} {B} = lemma-2 ∘ lemma , lemma-3
    where
      lemma : [ A , B ] ≡ singleton A → B ∈ singleton A
      lemma eq = proj⃗ (lower (proj⃗ extensionality eq) B) B∈[A,B]

      lemma-2 : B ∈ singleton A → A ≡ B
      lemma-2 B∈[A,A] = ≡-sym $ ∨-unrefl $ in-[A,B] B B∈[A,A]

      lemma-3 : A ≡ B → [ A , B ] ≡ singleton A
      lemma-3 iff = proj⃖ extensionality $ lift \X
        → (\X∈[A,B] → proj⃖ (proj₂ (∃-pairing A A) X) $ ∨-≡-reflˡ (cong₂ _≡_ ≡-refl (≡-sym iff)) $ in-[A,B] X X∈[A,B])
        , (\X∈[A,A] → proj⃖ (proj₂ (∃-pairing A B) X) $ ∨-≡-reflˡ (cong₂ _≡_ ≡-refl iff) $ in-[A,B] X X∈[A,A])

  prop-1-sym : {A B : Set} → [ B , A ] ≡ singleton A ⇔ A ≡ B
  prop-1-sym {A} {B} = let open ⇔-Reasoning in
    begin
      [ B , A ] ≡ singleton A ↓⟨ ≡-⇔-reflʳ [,]-comm ⟩
      [ A , B ] ≡ singleton A ↓⟨ prop-1 ⟩
      A ≡ B
    ∎

  ≡-[,C] : {A B C : Set} → A ≡ B → [ A , C ] ≡ [ B , C ]
  ≡-[,C] {A} {B} {C} A≡B = proj⃖ extensionality $ lift $ \X → lemma-1 X , lemma-3 X
    where
      lemma-2 : ∀ X → (X ≡ A) ∨ (X ≡ C) → X ∈ [ B , C ]
      lemma-2 X (∨-left X≡A) = proj⃖ (proj₂ (∃-pairing B C) X) $ ∨-left $ ≡-trans X≡A A≡B
      lemma-2 X (∨-right X≡C) = proj⃖ (proj₂ (∃-pairing B C) X) $ ∨-right X≡C

      lemma-1 : ∀ X → X ∈ [ A , C ] → X ∈ [ B , C ]
      lemma-1 X X∈[A,C] = lemma-2 X $ in-[A,B] X X∈[A,C]

      lemma-4 : ∀ X → (X ≡ B) ∨ (X ≡ C) → X ∈ [ A , C ]
      lemma-4 X (∨-left X≡B) = proj⃖ (proj₂ (∃-pairing A C) X) $ ∨-left $ ≡-trans X≡B $ ≡-sym A≡B
      lemma-4 X (∨-right X≡C) = proj⃖ (proj₂ (∃-pairing A C) X) $ ∨-right X≡C

      lemma-3 : ∀ X → X ∈ [ B , C ] → X ∈ [ A , C ]
      lemma-3 X X∈[B,C] = lemma-4 X $ in-[A,B] X X∈[B,C]

  prop-2 : {A B : Set} →
    [ singleton A , [ A , B ] ] ≡ [ singleton B , [ A , B ] ] ⇔ A ≡ B
  prop-2 {A} {B} = (\iff → lemma-2 $ in-[A,B] (singleton A) $ lemma iff)
    , (\A≡B → ≡-[,C] $ proj⃗ (≡-singleton) A≡B)
    where
      lemma : [ singleton A , [ A , B ] ] ≡ [ singleton B , [ A , B ] ] → singleton A ∈ [ singleton B , [ A , B ] ]
      lemma iff = proj⃗ (lower (proj⃗ extensionality iff) [ A , A ]) A∈[A,B]

      lemma-2 : (singleton A ≡ singleton B) ∨ (singleton A ≡ [ A , B ]) → A ≡ B
      lemma-2 (∨-left A≡B) = proj⃖ ≡-singleton A≡B
      lemma-2 (∨-right A≡[A,B]) = proj⃗ prop-1 $ ≡-sym A≡[A,B]

--    ≢-singleton : {A : Set} → A ≢ singleton A

--    prop-3 : ∅ ⊊ singleton ∅
--    prop-4 : singleton ∅ ⊊ [ ∅ , singleton ∅ ]

∈-singleton-⊆ : {A X : Set} → X ∈ A → singleton X ⊆ A
∈-singleton-⊆ X∈A x x∈[X] = ≡-∈ (≡-sym $ in-[A,A] x x∈[X]) X∈A

