
-- {-# OPTIONS --cumulativity #-}

open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (curry)
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Function hiding (_∘_; id)

open ≡-Reasoning

module Category
  where

record Category (ℓ n m : Level) : Set (suc (ℓ ⊔ n ⊔ m)) where
  field
    Obj : Set ℓ
    _⇒_ : Obj → Obj → Set n
    _≐_ : ∀ {A B} → (A ⇒ B) → (A ⇒ B) → Set m
    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C

    id : ∀ {A} → A ⇒ A

    left-id : ∀ {A B} {f : A ⇒ B} → (id ∘ f) ≐ f
    right-id : ∀ {A B} {f : A ⇒ B} → (f ∘ id) ≐ f
    assoc : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
      ((f ∘ g) ∘ h) ≐ (f ∘ (g ∘ h))

    ≐-refl : ∀ {A B} {f : A ⇒ B} → f ≐ f
    ≐-sym : ∀ {A B} {f g : A ⇒ B} → f ≐ g → g ≐ f
    ≐-trans : ∀ {A B} {f g h : A ⇒ B} →
      f ≐ g →
      g ≐ h →
      f ≐ h
    ≐-left : ∀ {A B C} {f f′ : B ⇒ C} {g : A ⇒ B} →
      f ≐ f′ →
      (f ∘ g) ≐ (f′ ∘ g)
    ≐-right : ∀ {A B C} {f : B ⇒ C} {g g′ : A ⇒ B} →
      g ≐ g′ →
      (f ∘ g) ≐ (f ∘ g′)

Arr : ∀ {o ℓ n} (𝓒 : Category o ℓ n) → Category.Obj 𝓒 → Category.Obj 𝓒 → Set ℓ
Arr = Category._⇒_

equals : ∀ {o ℓ n} (𝓒 : Category o ℓ n) {A B : Category.Obj 𝓒} →
  (A ⇒[ 𝓒 ] B) → (A ⇒[ 𝓒 ] B) → Set n
equals = Category._≐_

compose : ∀ {o ℓ n} (𝓒 : Category o ℓ n) {A B C : Category.Obj 𝓒} →
  (B ⇒[ 𝓒 ] C) → (A ⇒[ 𝓒 ] B) → (A ⇒[ 𝓒 ] C)
compose = Category._∘_

syntax Arr C A B = A ⇒[ C ] B
syntax equals C f g = f ≐[ C ] g
syntax compose C f g = f ∘[ C ] g

Agda : ∀ {ℓ : Level} → Category (suc ℓ) ℓ ℓ
Agda {ℓ} =
  record
    { Obj = Set ℓ
    ; _⇒_ = λ A B → (A → B)
    ; _≐_ = λ {A B : Set ℓ} (f : A → B) (g : A → B) → ∀ (x : A) → _≡_ {ℓ} (f x) (g x) -- TODO: Generalize
    ; _∘_ = λ f g x → f (g x)
    ; id = λ x → x
    ; left-id = λ x → refl
    ; right-id = λ x → refl
    ; assoc = λ x → refl
    ; ≐-refl = λ x → refl
    ; ≐-sym = λ p x → sym (p x)
    ; ≐-trans = λ p q x → trans (p x) (q x)
    ; ≐-left = λ {_} {_} {_} {_} {_} {g} p x → p (g x)
    ; ≐-right = λ {_} {_} {_} {f} {g} p x → subst (λ z → f (g x) ≡ f z) (p x) refl
    }
  where open Category (Agda {ℓ})

record Functor {ℓ n m ℓ′ n′ m′ : Level} (𝓒 : Category ℓ n m) (𝓓 : Category ℓ′ n′ m′) : Set (ℓ ⊔ ℓ′ ⊔ n ⊔ n′ ⊔ m′) where
  field
    act : Category.Obj 𝓒 → Category.Obj 𝓓
    fmap : ∀ {A B} →
      (A ⇒[ 𝓒 ] B) →
      (act A ⇒[ 𝓓 ] act B)

    fmap-id : ∀ {A : Category.Obj 𝓒} → fmap {A} (Category.id 𝓒) ≐[ 𝓓 ] Category.id 𝓓
    fmap-∘ : ∀ {A B C : Category.Obj 𝓒} {f : B ⇒[ 𝓒 ] C} {g : A ⇒[ 𝓒 ] B} →
      fmap (f ∘[ 𝓒 ] g)
        ≐[ 𝓓 ]
      (fmap f ∘[ 𝓓 ] fmap g)

module Endofunctors {ℓ} {n} {m} (𝓒 : Category ℓ n m) where
  open Category 𝓒

  Id-Functor : Functor 𝓒 𝓒
  Id-Functor =
    record
      { act = λ z → z
      ; fmap = λ z → z
      ; fmap-id = λ {A} → ≐-refl
      ; fmap-∘ = Category.≐-left 𝓒 (Category.≐-refl 𝓒)
      }

module Limits {ℓ} {n} {m} (𝓒 : Category ℓ n m) where
  open Category 𝓒

  Unique : ∀ {ℓ₁} {A B} → (A ⇒ B) → ((A ⇒ B) → Set ℓ₁) → Set (n ⊔ ℓ₁ ⊔ m)
  Unique m P = ∀ m′ → P m′ → m′ ≐ m

  ∃![_⇒_]_ : ∀ {ℓ₁} → (A B : Obj) → ((A ⇒ B) → Set ℓ₁) → Set (ℓ₁ ⊔ n ⊔ m)
  ∃![_⇒_]_ {ℓ₁} A B P = Σ {n} {n ⊔ m ⊔ ℓ₁} (A ⇒ B) λ m → P m × Unique m P

  ∃![_][_⇒_]_ : ∀ ℓ₁ → (A B : Obj) → ((A ⇒ B) → Set ℓ₁) → Set (ℓ₁ ⊔ n ⊔ m)
  ∃![_][_⇒_]_ ℓ₁ A B P = Σ {n} {n ⊔ m ⊔ ℓ₁} (A ⇒ B) λ m → P m × Unique m P

  Final : Obj → Set (ℓ ⊔ n ⊔ m)
  Final T = ∀ A → Σ {n} {m ⊔ n} (A ⇒ T) λ h → Unique h (λ _ → ⊤)

  Initial : Obj → Set (ℓ ⊔ n ⊔ m)
  Initial I = ∀ A → Σ {n} {m ⊔ n} (I ⇒ A) λ h → Unique h (λ _ → ⊤)

  Product : Obj → Obj → Obj → Set (ℓ ⊔ n ⊔ m)
  Product A×B A B =
    Σ {n} {ℓ ⊔ n ⊔ m} (A×B ⇒ A) λ p →
    Σ {n} {ℓ ⊔ n ⊔ m} (A×B ⇒ B) λ q →
    ∀ Z (p′ : Z ⇒ A) (q′ : Z ⇒ B) →
      ∃![ m ][ Z ⇒ A×B ] λ m →
        (p′ ≐ (p ∘ m)) × (q′ ≐ (q ∘ m))

  pair₁ : ∀ {A×B A B} →
    Product A×B A B →
    A×B ⇒ A
  pair₁ (a , _ , _) = a

  pair₂ : ∀ {A×B A B} →
    Product A×B A B →
    A×B ⇒ B
  pair₂ (_ , b , _) = b

  bimap : ∀ {A×B A′×B′ A B A′ B′} →
    Product A×B A B → Product A′×B′ A′ B′ →
    (A ⇒ A′) → (B ⇒ B′) →
    (A×B ⇒ A′×B′)
  bimap {A×B} {A′×B′} {A = A} {B = B} {A′ = A′} {B′ = B′} A×B-Product A′×B′-Product@(fst , fst₁ , snd) f g =
    let z = snd A×B (f ∘ pair₁ A×B-Product) (g ∘ pair₂ A×B-Product)
    in
    proj₁ z

  Exponential :
    (_⊗_ : Obj → Obj → Obj) →
    (∀ A B → Product (A ⊗ B) A B) →
    Obj → Obj → Obj → Set (ℓ ⊔ n ⊔ m)
  Exponential _⊗_ ⊗-Product A⇨B A B =
    Σ {n} {ℓ ⊔ n ⊔ m} ((A⇨B ⊗ A) ⇒ B)
    λ ev →
    ∀ Z (e : (Z ⊗ A) ⇒ B) →
      ∃![ m ][ Z ⇒ A⇨B ] λ u →
        (ev ∘ bimap (⊗-Product Z A) (⊗-Product A⇨B A) u id)
          ≐
        e

  curry :
    (_⊗_ : Obj → Obj → Obj) →
    (⊗-Product : ∀ A B → Product (A ⊗ B) A B) →
    (_⇨_ : Obj → Obj → Obj) →
    (∀ A B → Exponential _⊗_ ⊗-Product (A ⇨ B) A B) →
    ∀ {A B C} →
    (A ⊗ B) ⇒ C →
    A ⇒ (B ⇨ C)
  curry _⊗_ ⊗-Product _⇨_ ⇨-Exponential {A} {B} {C} f with ⇨-Exponential B C
  ... | fst , snd with snd A f
  curry _⊗_ ⊗-Product _⇨_ ⇨-Exponential {A} {B} {C} f | fst , snd | fst₁ , p = fst₁

  eval :
    (_⊗_ : Obj → Obj → Obj) →
    (⊗-Product : ∀ A B → Product (A ⊗ B) A B) →
    (_⇨_ : Obj → Obj → Obj) →
    (∀ A B → Exponential _⊗_ ⊗-Product (A ⇨ B) A B) →
    ∀ {A B} →
    ((A ⇨ B) ⊗ A) ⇒ B
  eval _⊗_ ⊗-Product _⇨_ ⇨-Exponential {A} {B} with ⇨-Exponential A B
  ... | fst , snd = fst

module AgdaLimits {ℓ} where
  open Limits (Agda {ℓ})

  ⊤-Final : Final (Lift ℓ ⊤)
  ⊤-Final = λ A → (λ _ → lift tt) , λ m′ x x₁ → refl

  ⊥-Initial : Initial (Lift ℓ ⊥)
  ⊥-Initial = λ A → (λ ()) , (λ x x₁ ())

  ×-Product : ∀ A B → Product (A × B) A B
  ×-Product _ _ =
    proj₁ , proj₂ , λ Z p′ q′ → (λ z → p′ z , q′ z) , ((λ x → refl) , (λ x → refl)) , λ m′ x x₁ →
      sym
      (begin
        p′ x₁ , q′ x₁ ≡⟨ cong (_, q′ x₁) (proj₁ x x₁) ⟩
        proj₁ (m′ x₁) , q′ x₁ ≡⟨ cong (_ ,_) (proj₂ x x₁) ⟩
        proj₁ (m′ x₁) , proj₂ (m′ x₁) ≡⟨ refl ⟩
        m′ x₁
       ∎)

  -- →-Exponential : ∀ A B → Exponential _×_ ×-Product (A → B) A B
  -- →-Exponential _ _ =
  --   (λ z → proj₁ z (proj₂ z))
  --   , λ Z e → (λ z z₁ → e (z , z₁)) , (λ x → refl) , λ m′ x x₁ → {!!}
