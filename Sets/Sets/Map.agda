module Sets.Sets.Map where

open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Sets.Sets.Basic

_⟨∘⟩_ : ∀ {A B C} → B ⟶ C → A ⟶ B → A ⟶ C
_⟨∘⟩_ f g x = ⟨ f ⟩ (⟨ g ⟩ x) , (proj₂ (f $ ⟨ g ⟩ x) ∘ proj₂ (g x))

Image-∈ : ∀ {A B} (f : A ⟶ B) → ∀ x → x ∈ A → ⟨ f ⟩ x ∈ B
Image-∈ f x x∈A = proj₂ (f x) x∈A

map-graph : ∀ {A B} (f : A ⟶ B) → ∃ \(P : Set → Set → Set₁) → ∀ x y z → P x y ∧ P x z → y ≡ z
map-graph f = P , uniqueness
  where
  P : Set → Set → Set₁
  P a b = ⟨ f ⟩ a ≡ b

  uniqueness : ∀ x y z → P x y ∧ P x z → y ≡ z
  uniqueness x y z and = let open ≡-Reasoning in begin
    y      ≡⟨ ≡-sym $ ∧-left and ⟩
    ⟨ f ⟩ x ≡⟨ ∧-right and ⟩
    z      ∎

Graph : ∀ {A B} (f : A ⟶ B) → Set → Set → Set₁
Graph f = proj₁ $ map-graph f

postulate
  replacement : {P : Set → Set → Set₁} → (∀ x y z → (P x y ∧ P x z → y ≡ z)) → ∀ X → ∃ \A → ∀ y → (y ∈ A ⇔ ∃ \x → x ∈ X ∧ P x y)

in-Image : ∀{X Y} {f : X ⟶ Y} → ∃ \Imf → ∀ y → (y ∈ Imf ⇔ ∃ \x → x ∈ X ∧ ⟨ f ⟩ x ≡ y)
in-Image {X} {Y} {f} = Imf , prop
  where
  ex-P = map-graph f
  ex-Imf = replacement {proj₁ ex-P} (proj₂ ex-P) X
  Imf = proj₁ ex-Imf
  Imf-cond = proj₂ ex-Imf

  prop : ∀ y → y ∈ Imf ⇔ ∃ \x → x ∈ X ∧ ⟨ f ⟩ x ≡ y
  prop y = Imf-cond y

Image : ∀{X Y} (f : X ⟶ Y) → Set
Image f = proj₁ (in-Image {f = f})

replace-in-Image : ∀{X Y} (f : X ⟶ Y) → ∀ y → y ∈ Image f → ∃ \x → x ∈ X ∧ ⟨ f ⟩ x ≡ y
replace-in-Image f y y-in = proj⃗ (proj₂ (in-Image {f = f}) y) y-in

satisfy-in-Image : ∀{X Y} (f : X ⟶ Y) → ∀ y → (∃ \x → x ∈ X ∧ ⟨ f ⟩ x ≡ y) → y ∈ Image f
satisfy-in-Image f y cond = proj⃖ (proj₂ (in-Image {f = f}) y) cond

Image-⊆ : ∀{X Y} (f : X ⟶ Y) → Image f ⊆ Y
Image-⊆ f y y∈Imf =
  let ex = replace-in-Image f y y∈Imf ; x = proj₁ ex in
  ≡-∈ (∧-right $ proj₂ ex) (proj₂ (f x) $ ∧-left $ proj₂ ex)

--_⁻¹|Image : ∀{X Y} (f : X ⟶ Y) → Image f ⟶ X
--f ⁻¹|Image = \y → {!!}
