module Sets.Sets.NonDatur where

open import Function
open import Algebra.Properties.DistributiveLattice
open import Data.Empty
import Data.Fin as Fin
open import Data.Fin.Properties
import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (cong ; module ≡-Reasoning)

open import Sets.Sets.Basic
open import Sets.Sets.Extensionality
open import Sets.Sets.Pairing
open import Sets.Sets.Separation
open import Sets.Sets.Union
open import Sets.Sets.Natural
open import Sets.Sets.Choice

non-datur : ∀ {P : Set₁} → P ∨ (¬ P)
non-datur {P} = P∨¬P
  where
    [0,1] = [ fromℕ 0 , fromℕ 1 ]
    A = ⟦ x ∈ [0,1] ∣ x ≡ fromℕ 0 ∨ P ⟧
    B = ⟦ x ∈ [0,1] ∣ x ≡ fromℕ 1 ∨ P ⟧
    X = [ A , B ]

    f : ∃ \(f : X ⟶ (A ∪ B)) → ∀ A → ⟨ f ⟩ A ∈ A
    f = choice X $ non-∅ $ \a a∈X → lemma $ in-[A,B] a a∈X
      where
        lemma : ∀ {a} → a ≡ A ∨ a ≡ B → ∃ \b → b ∈ a
        lemma (∨-left a≡A) rewrite a≡A = fromℕ 0 , satisfy-cond (fromℕ 0) (satisfy-pairing (fromℕ 0) (∨-left ≡-refl) , ∨-left ≡-refl)
        lemma (∨-right a≡B) rewrite a≡B = fromℕ 1 , satisfy-cond (fromℕ 1) (satisfy-pairing (fromℕ 1) (∨-right ≡-refl) , ∨-left ≡-refl)

        non-∅ : (∀ a → a ∈ X → ∃ \b → b ∈ a) → ∅ ∉ X
        non-∅ f ∅-in = let ex = f ∅ ∅-in ; b = proj₁ ex ; b∈a = proj₂ ex in ⊥-elim $ elem-∈ b b∈a

    choose : X ⟶ [ fromℕ 0 , fromℕ 1 ]
    choose x = let y = ⟨ proj₁ f ⟩ x in
      y ,
      (\x-in → ⊆-AB y $ ∪-∨ y $ proj₂ (proj₁ f x) x-in)
      where
        lemma-2 : ∀ {y} → y ∈ [0,1] → y ≡ fromℕ 0 ∨ y ≡ fromℕ 1 → y ∈ A ∨ y ∈ B
        lemma-2 y-in (∨-left y≡0) = ∨-left $ satisfy-cond _ $ y-in , (∨-left y≡0)
        lemma-2 y-in (∨-right y≡1) = ∨-right $ satisfy-cond _ $ y-in , (∨-left y≡1)

        ⊆-AB : ∀ y → y ∈ A ∨ y ∈ B → y ∈ [0,1]
        ⊆-AB y (∨-left y∈A) = satisfy-pairing y $ replace-pairing y $ proj₁ $ replace-cond y y∈A
        ⊆-AB y (∨-right y∈B) = satisfy-pairing y $ replace-pairing y $ proj₁ $ replace-cond y y∈B

    lemma : (⟨ choose ⟩ A ≡ fromℕ 0 ∨ P) ∧ (⟨ choose ⟩ B ≡ fromℕ 1 ∨ P)
    lemma = (∨-case (replace-pairing _ $ proj₁ $ replace-cond _ fA∈A) of λ
      { (∨-left fA≡0) → ∨-left fA≡0
      ; (∨-right fA≡1) → ∨-right $ ∨-¬left-right {A = fA ≡ fromℕ 0 } (proj₂ $ replace-cond fA fA∈A) (\fA≡0 → 0≢1inSet $ ≡-trans (≡-sym fA≡0) fA≡1)
      }) ,
      (∨-case (replace-pairing _ $ proj₁ $ replace-cond _ fB∈B) of λ
      { (∨-left fB≡0) → ∨-right $ ∨-¬left-right (proj₂ $ replace-cond fB fB∈B) (\fB≡1 → 0≢1inSet $ ≡-trans (≡-sym fB≡0) fB≡1)
      ; (∨-right fB≡1) → ∨-left fB≡1
      })
      where
        fA = ⟨ proj₁ f ⟩ A
        fB = ⟨ proj₁ f ⟩ B

        fA∈A : fA ∈ A
        fA∈A = proj₂ f A

        fB∈B : fB ∈ B
        fB∈B = proj₂ f B

    lemma-2 : (⟨ choose ⟩ A ≡ fromℕ 0 ∧ ⟨ choose ⟩ B ≡ fromℕ 1) ∨ P
    lemma-2 = proj⃖ (proj₂ (∨-∧-distrib ⇔-∨-∧-DitributiveLattice) P (⟨ choose ⟩ A ≡ fromℕ 0) (⟨ choose ⟩ B ≡ fromℕ 1)) lemma

    cong-f : ∀{A B} → A ≡ B → ⟨ choose ⟩ A ≡ ⟨ choose ⟩ B
    cong-f {A} .{A} ≡-refl = ≡-refl

    ¬P : (⟨ choose ⟩ A ≡ fromℕ 0 ∧ ⟨ choose ⟩ B ≡ fromℕ 1) → ¬ P
    ¬P and P = 0≢1inSet 0≡1
      where
      A≡B : ⟨ choose ⟩ A ≡ ⟨ choose ⟩ B
      A≡B = cong-f $ satisfy-≡ $ \x →
        (\x-in → let ex = replace-cond x x-in in
          satisfy-cond x $ ∧-left ex , ∨-right P) ,
        (\x-in → let ex = replace-cond x x-in in
          satisfy-cond x $ ∧-left ex , ∨-right P)

      open ≡-Reasoning
      0≡1 : fromℕ 0 ≡ fromℕ 1
      0≡1 = begin
        fromℕ 0    ≡⟨ ≡-sym $ ∧-left and ⟩
        ⟨ choose ⟩ A ≡⟨ A≡B ⟩
        ⟨ choose ⟩ B ≡⟨ ∧-right and ⟩
        fromℕ 1     ∎

    P∨¬P : P ∨ ¬ P
    P∨¬P = ∨-→-reflˡ ¬P $ proj⃗ (∨-comm _ _) $ lemma-2

¬¬-elim : ∀ {P : Set₁} → ¬ (¬ P) → P
¬¬-elim {P} ¬¬P = ∨-¬right-left non-datur ¬¬P

