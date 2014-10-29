module Sets.Sets.Basic where

open import Level
open import Function
open import Algebra
open import Algebra.Structures
open import Data.Empty
open import Data.Product
  using ()
  renaming (_×_ to _∧_ ; _,_ to _,_ ; proj₁ to ∧-left ; proj₂ to ∧-right)
  public
open import Data.Product
open import Data.Sum
  using ()
  renaming (_⊎_ to _∨_ ; inj₁ to ∨-left ; inj₂ to ∨-right)
  public
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_)
  renaming (isEquivalence to ≡-isEquivalence ; refl to ≡-refl ; sym to ≡-sym ; trans to ≡-trans)
  public
open import Relation.Binary.PropositionalEquality

infix 0 ∨-case_of_
∨-case_of_ : ∀{a b} {A B : Set a} {C : Set b} → A ∨ B → (A ∨ B → C) → C
∨-case x of f = case x of f

∧-map : ∀{a b p q} {A : Set a} {B : Set b} {P : Set p} {Q : Set q} → (A → B) → (P → Q) → Σ A (\_ → P) → Σ B (\_ → Q)
∧-map f g (x , y) = (f x , g y)

≢-sym : ∀ {a} {A B : Set a} → A ≢ B → B ≢ A
≢-sym neq = \eq → neq $ ≡-sym eq

module iff where
  infix 1 _⇔_
  _⇔_ : ∀{f} → (A B : Set f) → Set f
  _⇔_ A B = (A → B) ∧ (B → A)

  proj⃗ : ∀{f} {A B : Set f} → (A ⇔ B) → (A → B)
  proj⃗ = ∧-left

  proj⃖ : ∀{f} {A B : Set f} → (A ⇔ B) → (B → A)
  proj⃖ = ∧-right

  ⇔-contraposition : ∀{f} {A B : Set f} → A ⇔ B → (¬ A) ⇔ (¬ B)
  ⇔-contraposition P = contraposition (proj⃖ P) , contraposition (proj⃗ P)
open iff public

module ⇔-lemmas where
  ⇔-isEquivalence : ∀{f} → IsEquivalence {suc f} _⇔_
  ⇔-isEquivalence {f} = record
    { refl = id , id
    ; sym = \iff → proj⃖ iff , proj⃗ iff
    ; trans = \ij jk → _∘_ (proj⃗ jk) (proj⃗ ij) , _∘_ {f} (proj⃖ ij) (proj⃖ jk) }
open ⇔-lemmas public

module ∨-∧-lemmas where
  ∨-unrefl : ∀{f} {A : Set f} → A ∨ A → A
  ∨-unrefl (∨-left a) = a
  ∨-unrefl (∨-right a) = a

  ∧-refl : ∀{f} {A : Set f} → A → A ∧ A
  ∧-refl A = A , A

  ∨-¬right-left : ∀{f} {A B : Set f} → A ∨ B → ¬ B → A
  ∨-¬right-left or notB = ∨-case or of λ
    { (∨-left a) → a
    ; (∨-right b) → ⊥-elim $ notB b
    }

  ∨-¬left-right : ∀{f} {A B : Set f} → A ∨ B → ¬ A → B
  ∨-¬left-right or notA = ∨-case or of λ
    { (∨-left a) → ⊥-elim $ notA a
    ; (∨-right b) → b
    }

  ∨-≡-reflʳ : ∀{f} {A B C : Set f} → A ≡ C → A ∨ B → C ∨ B
  ∨-≡-reflʳ A≡C = subst₂ _∨_ A≡C ≡-refl

  ∨-≡-reflˡ : ∀{f} {A B C : Set f} → B ≡ C → A ∨ B → A ∨ C
  ∨-≡-reflˡ B≡C = subst₂ _∨_ ≡-refl B≡C

  ∧-≡ : ∀{f} {A B C D : Set f} → A ≡ C → B ≡ D → A ∧ B → C ∧ D
  ∧-≡ = subst₂ _∧_

  ∨-→-reflʳ : ∀{f} {A B C : Set f} → (A → C) → A ∨ B → C ∨ B
  ∨-→-reflʳ f = λ{(∨-left a) → ∨-left (f a) ; (∨-right b) → ∨-right b}

  ∨-→-reflˡ : ∀{f} {A B C : Set f} → (B → C) → A ∨ B → A ∨ C
  ∨-→-reflˡ f = λ{(∨-left a) → ∨-left a ; (∨-right b) → ∨-right (f b)}

  ∧-→-reflʳ : ∀{f} {A B C : Set f} → (A → C) → A ∧ B → C ∧ B
  ∧-→-reflʳ f = \and → (f $ ∧-left and) , (∧-right and)

  ∧-→-reflˡ : ∀{f} {A B C : Set f} → (B → C) → A ∧ B → A ∧ C
  ∧-→-reflˡ f = \and → (∧-left and) , (f $ ∧-right and)

  ⇔-∨-∧-isLattice : ∀{f} → IsLattice {suc f} _⇔_ _∨_ _∧_
  ⇔-∨-∧-isLattice = record
    { isEquivalence = ⇔-isEquivalence
    ; ∨-comm = \A B → ∨-flip , ∨-flip
    ; ∨-assoc = \A B C → ∨-assoc-flipˡ , ∨-assoc-flipʳ
    ; ∨-cong = \X⇔Y U⇔V → ∨-cong-lemmaˡ X⇔Y U⇔V , ∨-cong-lemmaʳ X⇔Y U⇔V
    ; ∧-comm = \A B → (λ{(a , b) → b , a}) , (λ{(a , b) → b , a})
    ; ∧-assoc = \A B C → (λ{((a , b) , c) → a , (b , c)}) , (λ{(a , (b , c)) → (a , b) , c})
    ; ∧-cong = \X⇔Y U⇔V → (λ{(x , u) → proj⃗ X⇔Y x , proj⃗ U⇔V u})
                         , (λ{(y , v) → proj⃖ X⇔Y y , proj⃖ U⇔V v})
    ; absorptive = (\X Y → (λ{(∨-left x) → x ; (∨-right and) → ∧-left and}) , ∨-left) ,
                   (\X Y → ∧-left , (\X → X , ∨-left X))
    }
    where
      ∨-flip : ∀{A B} → A ∨ B → B ∨ A
      ∨-flip (∨-left A) = ∨-right A
      ∨-flip (∨-right A) = ∨-left A

      ∨-assoc-flipˡ : ∀{A B C} → (A ∨ B) ∨ C → A ∨ (B ∨ C)
      ∨-assoc-flipˡ (∨-left (∨-left A)) = ∨-left A
      ∨-assoc-flipˡ (∨-left (∨-right B)) = ∨-right $ ∨-left B
      ∨-assoc-flipˡ (∨-right C) = ∨-right $ ∨-right C

      ∨-assoc-flipʳ : ∀{A B C} → A ∨ (B ∨ C) → (A ∨ B) ∨ C
      ∨-assoc-flipʳ (∨-left A) = ∨-left $ ∨-left A
      ∨-assoc-flipʳ (∨-right (∨-left B)) = ∨-left $ ∨-right B
      ∨-assoc-flipʳ (∨-right (∨-right C)) = ∨-right C

      ∨-cong-lemmaˡ : ∀{X Y U V} → X ⇔ Y → U ⇔ V → X ∨ U → Y ∨ V
      ∨-cong-lemmaˡ X⇔Y U⇔V (∨-left X) = ∨-left $ proj⃗ X⇔Y X
      ∨-cong-lemmaˡ X⇔Y U⇔V (∨-right U) = ∨-right $ proj⃗ U⇔V U

      ∨-cong-lemmaʳ : ∀{X Y U V} → X ⇔ Y → U ⇔ V → Y ∨ V → X ∨ U
      ∨-cong-lemmaʳ X⇔Y U⇔V (∨-left X) = ∨-left $ proj⃖ X⇔Y X
      ∨-cong-lemmaʳ X⇔Y U⇔V (∨-right U) = ∨-right $ proj⃖ U⇔V U
  open IsLattice (⇔-∨-∧-isLattice {suc zero}) public

  ⇔-∨-∧-isDitributiveLattice : ∀{f} → IsDistributiveLattice {suc f} _⇔_ _∨_ _∧_
  ⇔-∨-∧-isDitributiveLattice = record
    { isLattice = ⇔-∨-∧-isLattice
    ; ∨-∧-distribʳ = distr
    }
    where
    distr : ∀ x y z → (y × z ∨ x) ⇔ (y ∨ x) × (z ∨ x)
    distr x y z =
      (λ{ (∨-left yz) → (∨-left $ ∧-left yz) , (∨-left $ ∧-right yz)
        ; (∨-right x) → ∨-right x , ∨-right x }) ,
      (λ{ (∨-left y , ∨-left z) → (∨-left $ y , z)
        ; (∨-right x , _) → ∨-right x
        ; (_ , ∨-right x) → ∨-right x })
  open IsDistributiveLattice (⇔-∨-∧-isDitributiveLattice {suc zero})
    using (∨-∧-distribʳ)
    public

  ⇔-∨-∧-DitributiveLattice : ∀{f} → DistributiveLattice (suc f) _
  ⇔-∨-∧-DitributiveLattice {f} = record
    { Carrier = Set f
    ; _≈_ = _⇔_
    ; _∨_ = _∨_
    ; _∧_ = _∧_
    ; isDistributiveLattice = ⇔-∨-∧-isDitributiveLattice
    }
open ∨-∧-lemmas public

module ⇔-Hetero where
  ⇔-≡-reflʳ : ∀{f} {A B C : Set f} → A ≡ C → (A ⇔ B) ≡ (C ⇔ B)
  ⇔-≡-reflʳ A≡C = cong₂ _⇔_ A≡C ≡-refl

  ⇔-≡-reflˡ : ∀{f} {A B C : Set f} → A ≡ C → (B ⇔ A) ≡ (B ⇔ C)
  ⇔-≡-reflˡ A≡C = cong₂ _⇔_ ≡-refl A≡C

  ≡-⇔-reflʳ : ∀{f} {A B C : Set f} → A ≡ C → (A ≡ B) ⇔ (C ≡ B)
  ≡-⇔-reflʳ A≡C = (\A≡B → ≡-trans (≡-sym A≡C) A≡B) , (\C≡B → ≡-trans A≡C C≡B)

  ≡-⇔-reflˡ : ∀{f} {A B C : Set f} → A ≡ C → (B ≡ A) ⇔ (B ≡ C)
  ≡-⇔-reflˡ A≡C = (\B≡A → ≡-trans B≡A A≡C) , (\B≡C → ≡-trans B≡C (≡-sym A≡C))
open ⇔-Hetero public

module ⇔-Reasoning {f} where
  ⇔-refl : {A : Set f} → A ⇔ A
  ⇔-refl = IsEquivalence.refl ⇔-isEquivalence

  ⇔-sym : {A B : Set f} → A ⇔ B → B ⇔ A
  ⇔-sym = IsEquivalence.sym ⇔-isEquivalence

  ⇔-trans : {A B C : Set f} → A ⇔ B → B ⇔ C → A ⇔ C
  ⇔-trans = IsEquivalence.trans ⇔-isEquivalence

  infixr 2 _∎
  infixr 2 _⇔⟨⟩_ _↓⟨_⟩_ _↑⟨_⟩_
  infix 1 begin_

  data _IsRelatedTo_ (A B : Set f) : Set (suc f) where
    relTo : A ⇔ B → A IsRelatedTo B

  begin_ : {A B : Set f} → A IsRelatedTo B → A ⇔ B
  begin (relTo A⇔B) = A⇔B

  _↓⟨_⟩_ : (A : Set f) → {B C : Set f} → A ⇔ B → B IsRelatedTo C → A IsRelatedTo C
  _ ↓⟨ x⇔y ⟩ relTo y⇔z = relTo (⇔-trans x⇔y y⇔z)

  _↑⟨_⟩_ : (A : Set f) → {B C : Set f} → B ⇔ A → B IsRelatedTo C → A IsRelatedTo C
  _ ↑⟨ y≈x ⟩ relTo y≈z = relTo (⇔-trans (IsEquivalence.sym ⇔-isEquivalence y≈x) y≈z)

  _⇔⟨⟩_ : (A : Set f) → {B : Set f} → A IsRelatedTo B → A IsRelatedTo B
  _ ⇔⟨⟩ x∼y = x∼y

  _∎ : (A : Set f) → A IsRelatedTo A
  _∎ _ = relTo ⇔-refl

infix 4 _∈_ _∉_
postulate
  _∈_ : Set → Set → Set₁
  elem-∈ : {A : Set} → ∀ x → x ∈ A → A

_∉_ : Set → Set → Set₁
X ∉ A = (X ∈ A) → ⊥

module elem-lemmas where
  ≡-∈ : {A : Set} {x y : Set} → x ≡ y → x ∈ A → y ∈ A
  ≡-∈ x≡y x∈A rewrite x≡y = x∈A

  ∈-≡ : {A B : Set} → {X : Set} → A ≡ B → X ∈ A → X ∈ B
  ∈-≡ {X = X} A≡B X∈A rewrite A≡B = X∈A
open elem-lemmas public

infix 5 _⊆_ _⊊_
_⊆_ : Set → Set → Set₁
_⊆_ A B = ∀ (x : Set) → x ∈ A → x ∈ B

_⊊_ : Set → Set → Set₁
A ⊊ B = (A ≢ B) ∧ (A ⊆ B)

module ⊆-Hetero where
  ⊆-≡-reflˡ : {A B C : Set} → B ≡ C → A ⊆ B → A ⊆ C
  ⊆-≡-reflˡ B≡C A⊆B x∈A rewrite B≡C = A⊆B x∈A

  ⊆-≡-reflʳ : {A B C : Set} → A ≡ C → A ⊆ B → C ⊆ B
  ⊆-≡-reflʳ A≡C A⊆B x∈C rewrite A≡C = A⊆B x∈C
open ⊆-Hetero public

module Map where
  _⟶_ : Set → Set → Set₁
  _⟶_ A B = ∀ x → ∃ \y → (x ∈ A → y ∈ B)

  ⟨_⟩ : ∀ {A B} → A ⟶ B → ∀ x → Set
  ⟨_⟩ f x = proj₁ (f x)
open Map public

