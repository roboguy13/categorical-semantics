open import Data.Product
open import Relation.Nullary
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to Eq-subst)
open import Data.Sum
open import Data.Fin
open import Data.Empty
open import Function hiding (_∋_; _⟶_)
open import Data.Unit

open ≡-Reasoning

module STLC
  where

data Term : Set where
  true : Term
  false : Term

  V : ℕ → Term

  _·_ :
    Term →
    Term →
    Term

  ƛ :
    Term →
    Term

data Type : Set where
  Boolean : Type
  _⇒_ : Type → Type → Type

data Context : Set where
  ∅ : Context
  _,,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  ∋-here : ∀ {Γ} {A} → (Γ ,, A) ∋ A
  ∋-there : ∀ {Γ A B} →
    Γ ∋ A →
    (Γ ,, B) ∋ A

data _∋′_⦂_ : Context → ℕ → Type → Set where
  ∋′-here : ∀ {Γ} {A} → (Γ ,, A) ∋′ 0 ⦂ A
  ∋′-there : ∀ {Γ A B} {x} →
    Γ ∋′ x ⦂ A →
    (Γ ,, B) ∋′ suc x ⦂ A

∋′-unique : ∀ {Γ A x} →
  (p p′ : Γ ∋′ x ⦂ A) →
  p ≡ p′
∋′-unique ∋′-here ∋′-here = refl
∋′-unique (∋′-there p) (∋′-there p′) rewrite ∋′-unique p p′ = refl

ℕ-lookup : ∀ {Γ A x} →
  Γ ∋′ x ⦂ A →
  Γ ∋ A
ℕ-lookup ∋′-here = ∋-here
ℕ-lookup (∋′-there p) = ∋-there (ℕ-lookup p)

lookup-ℕ : ∀ {Γ A} →
  Γ ∋ A →
  ∃[ x ] Γ ∋′ x ⦂ A
lookup-ℕ ∋-here = 0 , ∋′-here
lookup-ℕ (∋-there p) with lookup-ℕ p
... | fst , snd = suc fst , ∋′-there snd

lookup-ℕ-id : ∀ {Γ A} {x} →
  ℕ-lookup {Γ} {A} (proj₂ (lookup-ℕ x)) ≡ x
lookup-ℕ-id {x = ∋-here} = refl
lookup-ℕ-id {x = ∋-there x} rewrite lookup-ℕ-id {x = x} = refl

ℕ-lookup-id₁ : ∀ {Γ A} {z} {x} →
  proj₁ (lookup-ℕ {Γ} {A} (ℕ-lookup {x = z} x)) ≡ z
ℕ-lookup-id₁ {z = zero} {x = ∋′-here} = refl
ℕ-lookup-id₁ {z = suc z} {x = ∋′-there x} rewrite ℕ-lookup-id₁ {z = z} {x = x} = refl

to-ℕ : ∀ {Γ} →
  ∀ {A} → Γ ∋ A →
  ℕ
to-ℕ ∋-here = zero
to-ℕ (∋-there x) = suc (to-ℕ x)

to-ℕ-lookup : ∀ {Γ A} {x} →
  to-ℕ {Γ} {A} x ≡ proj₁ (lookup-ℕ x)
to-ℕ-lookup {.(_ ,, A)} {A} {∋-here} = refl
to-ℕ-lookup {.(_ ,, _)} {A} {∋-there x} rewrite to-ℕ-lookup {x = x} = refl

data _⊢_⦂_ : Context → Term → Type → Set where
  Ty-true : ∀ {Γ} →
    Γ ⊢ true ⦂ Boolean

  Ty-false : ∀ {Γ} →
    Γ ⊢ false ⦂ Boolean

  Ty-V : ∀ {Γ A} {n} →
    (x : Γ ∋ A) →
    n ≡ to-ℕ x →
    Γ ⊢ V n ⦂ A

  Ty-· : ∀ {Γ} {A B} {M N : Term} →
    Γ ⊢ M ⦂ (A ⇒ B) →
    Γ ⊢ N ⦂ A →
    Γ ⊢ (M · N) ⦂ B

  Ty-ƛ : ∀ {Γ} {A B} {M} →
    (Γ ,, A) ⊢ M ⦂ B →
    Γ ⊢ ƛ M ⦂ (A ⇒ B)

data 𝓔 : Set where
  𝓔-hole : 𝓔
  𝓔-·₁ : 𝓔 → Term → 𝓔
  𝓔-·₂ : Term → 𝓔 → 𝓔
  𝓔-ƛ : 𝓔 → 𝓔

plug-in : 𝓔 → Term → Term
plug-in 𝓔-hole M = M
plug-in (𝓔-·₁ E x) M = plug-in E M · x
plug-in (𝓔-·₂ x E) M = x · plug-in E M
plug-in (𝓔-ƛ E) M = ƛ (plug-in E M)

ext : ∀ {Γ Δ} →
  (∀ {A} → Γ ∋ A → Δ ∋ A) →
  (∀ {A B} → (Γ ,, B) ∋ A → (Δ ,, B) ∋ A)
ext ρ ∋-here = ∋-here
ext ρ (∋-there x) = ∋-there (ρ x)

ext′ : (ℕ → ℕ) → (ℕ → ℕ)
ext′ ρ zero = zero
ext′ ρ (suc x) = suc (ρ x)

ext′-preserves-types₁ : ∀ {Γ A B} {ρ} {x} →
  Γ ∋′ ρ x ⦂ A →
  (Γ ,, B) ∋′ ext′ ρ (suc x) ⦂ A
ext′-preserves-types₁ {Γ} {ρ} {x} z = ∋′-there z

ext′-preserves-types₂ :  ∀ {Γ A} {ρ} →
  (Γ ,, A) ∋′ ext′ ρ zero ⦂ A
ext′-preserves-types₂ = ∋′-here

rename′ :
  (ℕ → ℕ) →
  Term →
  Term
rename′ ρ true = true
rename′ ρ false = false
rename′ ρ (V x) = V (ρ x)
rename′ ρ (M · N) = rename′ ρ M · rename′ ρ N
rename′ ρ (ƛ M) = ƛ (rename′ (ext′ ρ) M)

Is-Renaming : Context → Context → (ℕ → ℕ) → Set
Is-Renaming Γ Δ ρ =
  Σ (∀ {A} {x} →
      Γ ∋′ x ⦂ A →
      Δ ∋′ ρ x ⦂ A)
  λ ρ-renaming →
  ∀ {A} {z : Γ ∋ A} →
  ρ (to-ℕ z) ≡ to-ℕ (ℕ-lookup (ρ-renaming (proj₂ (lookup-ℕ z))))

Is-Subst : Context → Context → (ℕ → Term) → Set
Is-Subst Γ Δ σ =
  Σ (∀ {A} {x} →
      Γ ∋′ x ⦂ A →
      Δ ⊢ σ x ⦂ A)
  λ σ-subst →
  ⊤

∋′-here-unique : ∀ {Γ A B} →
  (Γ ,, A) ∋′ zero ⦂ B →
  B ≡ A
∋′-here-unique ∋′-here = refl

ext-Is-Renaming : ∀ {Γ Δ A} {ρ} →
  Is-Renaming Γ Δ ρ →
  Is-Renaming (Γ ,, A) (Δ ,, A) (ext′ ρ)
ext-Is-Renaming {Γ} {Δ} {A} {ρ = ρ} ρ-renaming =
  let renames , eq = ρ-renaming
  in
  (λ { {C} {x = zero} x → Eq-subst (λ z → (Δ ,, A) ∋′ zero ⦂ z) (sym (∋′-here-unique x)) (ext′-preserves-types₂ {Γ = Δ} {A = A} {ρ = ρ}) ; {C} {x = suc y} (∋′-there x) → ext′-preserves-types₁ {ρ = ρ} (renames x) })
  ,
  λ { {A} {∋-here} → refl ; {A} {∋-there x} → cong suc eq}

suc-Is-Renaming : ∀ {Γ A} →
  Is-Renaming Γ (Γ ,, A) suc
suc-Is-Renaming = ∋′-there , λ {A} {z} → cong suc (cong to-ℕ (sym lookup-ℕ-id))

rename′-preserves-type : ∀ {Γ Δ}
  (ρ : ℕ → ℕ) →
  Is-Renaming Γ Δ ρ →
  ∀ {B} {M} →
  Γ ⊢ M ⦂ B →
  Δ ⊢ rename′ ρ M ⦂ B
rename′-preserves-type ρ ρ-renaming Ty-true = Ty-true
rename′-preserves-type ρ ρ-renaming Ty-false = Ty-false
rename′-preserves-type ρ ρ-renaming (Ty-V x refl) = Ty-V (ℕ-lookup (proj₁ ρ-renaming (proj₂ (lookup-ℕ x)))) (proj₂ ρ-renaming)
rename′-preserves-type ρ ρ-renaming (Ty-· M-typed N-typed) = Ty-· (rename′-preserves-type ρ ρ-renaming M-typed)
                                                              (rename′-preserves-type ρ ρ-renaming N-typed)
rename′-preserves-type {Γ} ρ ρ-renaming (Ty-ƛ M-typed) = Ty-ƛ (rename′-preserves-type (ext′ ρ) (ext-Is-Renaming ρ-renaming) M-typed)

rename : ∀ {Γ Δ} →
  (∀ {A} → Γ ∋ A → Δ ∋ A) →
  {M : Term} →
  ∀ {B} →
  Γ ⊢ M ⦂ B →
  Term
rename ρ Ty-true = true
rename ρ Ty-false = false
rename ρ (Ty-V x _) = V (to-ℕ (ρ x))
rename ρ (Ty-· M-typed N-typed) = rename ρ M-typed · rename ρ N-typed
rename ρ (Ty-ƛ M-typed) = ƛ (rename (ext ρ) M-typed)

to-ℕ-preserves-type : ∀ {Γ A} {x : Γ ∋ A} →
  Γ ⊢ V (to-ℕ x) ⦂ A
to-ℕ-preserves-type {x = ∋-here} = Ty-V ∋-here refl
to-ℕ-preserves-type {x = ∋-there x} with to-ℕ-preserves-type {x = x}
... | Ty-V x eq = Ty-V (∋-there x) (cong suc eq)

rename-preserves-type : ∀ {Γ Δ}
  (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A) →
  ∀ {B} {M} →
  (M-typed : Γ ⊢ M ⦂ B) →
  Δ ⊢ rename ρ M-typed ⦂ B
rename-preserves-type ρ Ty-true = Ty-true
rename-preserves-type ρ Ty-false = Ty-false
rename-preserves-type ρ (Ty-V x eq) = to-ℕ-preserves-type
rename-preserves-type ρ (Ty-· M-typed N-typed) = Ty-· (rename-preserves-type ρ M-typed) (rename-preserves-type ρ N-typed)
rename-preserves-type ρ (Ty-ƛ M-typed) = Ty-ƛ (rename-preserves-type (ext ρ) M-typed)


exts : ∀ {Γ Δ} →
  (∀ {A} → Γ ∋ A → ∃[ N ] (Δ ⊢ N ⦂ A)) →
  (∀ {A B} → (Γ ,, B) ∋ A → Term)
exts σ ∋-here = V zero
exts {Δ = Δ} σ {B = B} (∋-there x) = rename (λ {A} → ∋-there {Δ} {A} {B}) (proj₂ (σ x))

exts-preserves-type : ∀ {Γ Δ} →
  (σ : ∀ {A} → Γ ∋ A → ∃[ N ] (Δ ⊢ N ⦂ A)) →
  ∀ {A B} → (x : (Γ ,, B) ∋ A) →
  (Δ ,, B) ⊢ exts σ x ⦂ A
exts-preserves-type σ ∋-here = Ty-V ∋-here refl
exts-preserves-type σ (∋-there x) = rename-preserves-type ∋-there (proj₂ (σ x))

exts′ :
  (ℕ → Term) →
  (ℕ → Term)
exts′ σ zero = V zero
exts′ σ (suc x) = rename′ suc (σ x)

exts′-preserves-type : ∀ {Γ Δ A B} {σ} {x} →
  Is-Subst Γ Δ σ →
  (Γ ,, B) ∋′ x ⦂ A →
  (Δ ,, B) ⊢ exts′ σ x ⦂ A
exts′-preserves-type {x = zero} σ-subst ∋′-here = Ty-V ∋-here refl
exts′-preserves-type {σ = σ} {x = suc x} (fst , snd) (∋′-there x-typed) = rename′-preserves-type suc suc-Is-Renaming (fst x-typed)

-- TODO: Untyped substitution, etc. It should be easier with this formulation

subst : ∀ {Γ Δ} →
  (∀ {A} → Γ ∋ A → ∃[ N ] (Δ ⊢ N ⦂ A)) →
  ∀ {M A} →
  Γ ⊢ M ⦂ A →
  Term
subst σ Ty-true = true
subst σ Ty-false = false
subst σ (Ty-V x y) = proj₁ (σ x)
subst σ (Ty-· M-typed N-typed) = subst σ M-typed · subst σ N-typed
subst σ (Ty-ƛ M-typed) = ƛ (subst (λ x → exts σ x , exts-preserves-type σ x) M-typed)
-- -- -- -- subst σ (ƛ M) = ƛ (subst (exts σ) M)

subst-preserves-type : ∀ {Γ Δ M A} →
  (σ : ∀ {A} → Γ ∋ A → ∃[ N ] (Δ ⊢ N ⦂ A)) →
  (M-typed : Γ ⊢ M ⦂ A) →
  Δ ⊢ subst σ M-typed ⦂ A
subst-preserves-type σ Ty-true = Ty-true
subst-preserves-type σ Ty-false = Ty-false
subst-preserves-type σ (Ty-V x refl) = proj₂ (σ x)
subst-preserves-type σ (Ty-· M-typed N-typed) = Ty-· (subst-preserves-type σ M-typed) (subst-preserves-type σ N-typed)
subst-preserves-type σ (Ty-ƛ M-typed) = Ty-ƛ
                                          (subst-preserves-type (λ z → exts σ z , exts-preserves-type σ z)
                                           M-typed)

subst′ :
  (ℕ → Term) →
  Term →
  Term
subst′ σ true = true
subst′ σ false = false
subst′ σ (V x) = σ x
subst′ σ (M · N) = subst′ σ M · subst′ σ N
subst′ σ (ƛ M) = ƛ (subst′ (exts′ σ) M)

subst′-preserves-type : ∀ {Γ Δ A} {σ} {M} →
  Is-Subst Γ Δ σ →
  Γ ⊢ M ⦂ A →
  Δ ⊢ subst′ σ M ⦂ A
subst′-preserves-type {M = .true} σ-subst Ty-true = Ty-true
subst′-preserves-type {M = .false} σ-subst Ty-false = Ty-false
subst′-preserves-type {σ = σ} {M = .(V (to-ℕ x))} (fst , snd) (Ty-V x refl)
  rewrite to-ℕ-lookup {x = x} = fst (proj₂ (lookup-ℕ x))
subst′-preserves-type {M = .(_ · _)} σ-subst (Ty-· M-typed N-typed) = Ty-· (subst′-preserves-type σ-subst M-typed)
                                                                       (subst′-preserves-type σ-subst N-typed)
subst′-preserves-type {M = .(ƛ _)} σ-subst (Ty-ƛ M-typed) =
  Ty-ƛ (subst′-preserves-type (exts′-preserves-type σ-subst , tt) M-typed)


subst1-σ : ∀ {Γ} {N} {B} → Γ ⊢ N ⦂ B → ∀ {Z} → (Γ ,, B) ∋ Z → ∃[ R ] (Γ ⊢ R ⦂ Z)
subst1-σ {N = N} N-typed ∋-here = N , N-typed
subst1-σ _ (∋-there x) = V (to-ℕ x) , Ty-V x refl

_[[_]] : ∀ {Γ A B M N} →
  (Γ ,, B) ⊢ M ⦂ A →
  Γ ⊢ N ⦂ B →
  Term
_[[_]] {Γ} {A} {B} {M = M} {N = N} M-typed N-typed = subst (subst1-σ N-typed) M-typed

subst1′-σ : Term → ℕ → Term
subst1′-σ N zero = N
subst1′-σ N (suc x) = V x

subst1′-σ-Is-Subst : ∀ {Γ B} {N} →
  Γ ⊢ N ⦂ B →
  Is-Subst (Γ ,, B) Γ (subst1′-σ N)
subst1′-σ-Is-Subst {Γ} {B} Ty-true = (λ { ∋′-here → Ty-true ; (∋′-there {A = A} {x = z} x) → Ty-V (ℕ-lookup x) (trans (sym (ℕ-lookup-id₁ {Γ} {A} {z} {x})) (sym (to-ℕ-lookup {Γ} {A} {ℕ-lookup x}))) }) , tt
subst1′-σ-Is-Subst {Γ} {B} Ty-false = (λ { ∋′-here → Ty-false ; (∋′-there {A = A} {x = z} x) → Ty-V (ℕ-lookup x) (trans (sym (ℕ-lookup-id₁ {Γ} {A} {z} {x})) (sym (to-ℕ-lookup {Γ} {A} {ℕ-lookup x}))) }) , tt
subst1′-σ-Is-Subst {Γ} {B} (Ty-V x refl) =
  (λ { ∋′-here → Ty-V x refl
     ; (∋′-there {A = A} {x = z} x) → Ty-V (ℕ-lookup x) (trans (sym (ℕ-lookup-id₁ {Γ} {A} {z} {x})) (sym (to-ℕ-lookup {Γ} {A} {ℕ-lookup x})))
     })
  , tt
subst1′-σ-Is-Subst {Γ} {B} (Ty-· N-typed N-typed₁) =
  (λ { ∋′-here → Ty-· N-typed N-typed₁
     ; (∋′-there {A = A} {x = z} x) → Ty-V (ℕ-lookup x) (trans (sym (ℕ-lookup-id₁ {Γ} {A} {z} {x})) (sym (to-ℕ-lookup {Γ} {A} {ℕ-lookup x})))
     })
  , tt
subst1′-σ-Is-Subst {Γ} {B} (Ty-ƛ N-typed) =
  (λ { ∋′-here → Ty-ƛ N-typed
     ; (∋′-there {A = A} {x = z} x) → Ty-V (ℕ-lookup x) (trans (sym (ℕ-lookup-id₁ {Γ} {A} {z} {x})) (sym (to-ℕ-lookup {Γ} {A} {ℕ-lookup x})))
     })
  , tt

_[_] :
  Term →
  Term →
  Term
_[_] M N = subst′ (subst1′-σ N) M

subst1-preserves-type : ∀ {Γ A B M N} →
  (M-typed : (Γ ,, B) ⊢ M ⦂ A) →
  (N-typed : Γ ⊢ N ⦂ B) →
  Γ ⊢ (M-typed [[ N-typed ]]) ⦂ A
subst1-preserves-type {Γ} {A} {B} {M} {N} M-typed N-typed = subst-preserves-type (subst1-σ N-typed) M-typed

subst1′-preserves-type : ∀ {Γ A B M N} →
  (Γ ,, B) ⊢ M ⦂ A →
  Γ ⊢ N ⦂ B →
  Γ ⊢ (M [ N ]) ⦂ A
subst1′-preserves-type {Γ} {A} {B} {M = M} {N = N} M-typed N-typed = subst′-preserves-type (subst1′-σ-Is-Subst {Γ} {B} N-typed) M-typed

open-subst1-σ : ∀ {Γ} {N} {B C} → (Γ ,, C) ⊢ N ⦂ B → ∀ {Z} → (Γ ,, B) ∋ Z → ∃[ R ] ((Γ ,, C) ⊢ R ⦂ Z)
open-subst1-σ {N = N} N-typed ∋-here = N , N-typed
open-subst1-σ N-typed {Z = Z} (∋-there x) = V (to-ℕ (∋-there {A = Z} {B = Z} x)) , Ty-V (∋-there x) refl

open-subst1 : ∀ {Γ A B C} {M N} →
  (Γ ,, B) ⊢ M ⦂ A →
  (Γ ,, C) ⊢ N ⦂ B →
  Term
open-subst1 {Γ} {A} {B} {C} {M} {N} M-typed N-typed = subst (open-subst1-σ N-typed) M-typed

open-subst1′-σ :
  Term →
  ℕ →
  Term
open-subst1′-σ N zero = N
open-subst1′-σ N (suc x) = V (suc x)

open-subst1′-σ-Is-Subst : ∀ {Γ A B} {M} →
  (Γ ,, A) ⊢ M ⦂ B →
  Is-Subst (Γ ,, B) (Γ ,, A) (open-subst1′-σ M)
open-subst1′-σ-Is-Subst {Γ} {A} M-typed =
  (λ { ∋′-here → M-typed ; (∋′-there {x = z} x) → Ty-V (∋-there (ℕ-lookup x)) (cong suc (trans (sym (ℕ-lookup-id₁ {Γ} {_} {z} {x})) (sym to-ℕ-lookup))) })
  , tt

open-subst1′ :
  Term →
  Term →
  Term
open-subst1′ M N = subst′ (open-subst1′-σ N) M

open-subst1′-preserves-type : ∀ {Γ A B C} {M N} →
  (Γ ,, B) ⊢ M ⦂ A →
  (Γ ,, C) ⊢ N ⦂ B →
  (Γ ,, C) ⊢ open-subst1′ M N ⦂ A
open-subst1′-preserves-type {Γ} {A} {B} {C} {M = M} {N = N} M-typed N-typed = subst′-preserves-type (open-subst1′-σ-Is-Subst {Γ} {C} {B} N-typed) M-typed

open-subst1-preserves-type : ∀ {Γ A B C} {M N} →
  (M-typed : (Γ ,, B) ⊢ M ⦂ A) →
  (N-typed : (Γ ,, C) ⊢ N ⦂ B) →
  (Γ ,, C) ⊢ open-subst1 M-typed N-typed ⦂ A
open-subst1-preserves-type M-typed N-typed = subst-preserves-type (open-subst1-σ N-typed) M-typed

_O[_] :
  Term →
  Term →
  Term
_O[_] = open-subst1′

mutual
  data Normal : Term → Set where
    Nf-neutral : ∀ {N} → Neutral N → Normal N
    Nf-true : Normal true
    Nf-false : Normal false
    Nf-ƛ : ∀ {N} → Normal (ƛ N)

  data Neutral : Term → Set where
    Ne-V : ∀ {x} → Neutral (V x)
    Ne-· : ∀ {M N} → Neutral M → Normal N → Neutral (M · N)

infix 2 _⟶_
data _⟶_ : Term → Term → Set where
  ⟶-ξ₁ : {f f′ : Term} {x : Term} →
    f ⟶ f′ →
    f · x ⟶ f′ · x

  ⟶-ξ₂ : {f : Term} {x x′ : Term} →
    -- Value f →
    x ⟶ x′ →
    f · x ⟶ f · x′

  ⟶-β : {f : Term} {x : Term} →
    -- Value x →
    (ƛ f · x) ⟶ f [ x ]

subject-reduction : ∀ {Γ A} {M M′} →
  Γ ⊢ M ⦂ A →
  M ⟶ M′ →
  Γ ⊢ M′ ⦂ A
subject-reduction (Ty-· M-typed M-typed₁) (⟶-ξ₁ M⟶M′) = Ty-· (subject-reduction M-typed M⟶M′) M-typed₁
subject-reduction (Ty-· M-typed M-typed₁) (⟶-ξ₂ M⟶M′) = Ty-· M-typed (subject-reduction M-typed₁ M⟶M′)
subject-reduction (Ty-· (Ty-ƛ M-typed) M-typed₁) ⟶-β = subst1′-preserves-type M-typed M-typed₁


open import Category
open import Level renaming (zero to lzero)

_ : ∀ {x : Term} → (true O[ x ]) ≡ true
_ = refl


module TypeInterpret
  (𝓒 : Category lzero lzero lzero)
  (≐-eq : ∀ {A B} {f g : A ⇒[ 𝓒 ] B } → Category._≐_ 𝓒 f g → f ≡ g)
  (𝟘 : Category.Obj 𝓒)
  (𝟙 : Category.Obj 𝓒)
  (𝟘-Initial : Limits.Initial 𝓒 𝟘)
  (𝟙-Final : Limits.Final 𝓒 𝟙)
  (_⊗_ : Category.Obj 𝓒 → Category.Obj 𝓒 → Category.Obj 𝓒)
  (⊗-Product : ∀ A B → Limits.Product 𝓒 (A ⊗ B) A B)
  (_⇨_ : Category.Obj 𝓒 → Category.Obj 𝓒 → Category.Obj 𝓒)
  (⇨-Exponential : ∀ A B → Limits.Exponential 𝓒 _⊗_ ⊗-Product (A ⇨ B) A B)

  (T⟦Boolean⟧ : Category.Obj 𝓒)
  (T⟦⇒⟧ : Category.Obj 𝓒 → Category.Obj 𝓒 → Category.Obj 𝓒)
  where

  T⟦_⟧ : Type → Category.Obj 𝓒
  T⟦ Boolean ⟧ = T⟦Boolean⟧
  T⟦ a ⇒ b ⟧ = T⟦ a ⟧ ⇨ T⟦ b ⟧

  ⊗₁ : ∀ {A B} → (A ⊗ B) ⇒[ 𝓒 ] A
  ⊗₁ {A} {B} with ⊗-Product A B
  ... | fst , _ = fst

  ⊗₂ : ∀ {A B} → (A ⊗ B) ⇒[ 𝓒 ] B
  ⊗₂ {A} {B} with ⊗-Product A B
  ... | _ , snd , _ = snd

  𝟙! : ∀ {A} → (A ⇒[ 𝓒 ] 𝟙)
  𝟙! {A} = proj₁ (𝟙-Final A)

  -- mk-⊗ : ∀ {A B} → A → B → (𝟙 ⇒[ 𝓒 ] (A ⊗ B))
  -- mk-⊗ = ?

  𝟙⊗ : ∀ {B} → (B ⇒[ 𝓒 ] (𝟙 ⊗ B))
  𝟙⊗ {B} with ⊗-Product 𝟙 B
  ... | _ , _ , p = proj₁ (p B 𝟙! (Category.id 𝓒))

  elim-𝟙⊗ : ∀ {B C} → ((𝟙 ⊗ B) ⇒[ 𝓒 ] C) → (B ⇒[ 𝓒 ] C)
  elim-𝟙⊗ f = f ∘[ 𝓒 ] 𝟙⊗

  move𝟙 : ∀ {A B} → ((𝟙 ⊗ A) ⇒[ 𝓒 ] B) → (A ⇒[ 𝓒 ] (𝟙 ⊗ B))
  move𝟙 f = (𝟙⊗ ∘[ 𝓒 ] f) ∘[ 𝓒 ] 𝟙⊗

  _≐_ : ∀ {A B} → (A ⇒[ 𝓒 ] B) → (A ⇒[ 𝓒 ] B) → Set
  _≐_ f g = Category._≐_ 𝓒 f g

  𝟙⊗-id : ∀ {A} →
    (Limits.pair₂ 𝓒 (⊗-Product 𝟙 A) ∘[ 𝓒 ] 𝟙⊗)
      ≐
    Category.id 𝓒
  𝟙⊗-id {A} with ⊗-Product 𝟙 A
  ... | fst , fst₁ , snd with snd A 𝟙! (Category.id 𝓒)
  𝟙⊗-id {A} | fst , fst₁ , snd | fst₂ , (fst₃ , snd₂) , snd₁ = Category.≐-sym 𝓒 snd₂

  C⟦_⟧ : (Γ : Context) → Category.Obj 𝓒
  C⟦_⟧ ∅ = 𝟙
  C⟦_⟧ (Γ ,, A) = C⟦ Γ ⟧ ⊗ T⟦ A ⟧

  pair : ∀ {I A B} →
    I ⇒[ 𝓒 ] A →
    I ⇒[ 𝓒 ] B →
    I ⇒[ 𝓒 ] (A ⊗ B)
  pair {I} {A} {B} f g with ⊗-Product A B
  ... | fst , fst₁ , snd with snd I f g
  pair {I} {A} {B} f g | fst , fst₁ , snd | fst₂ , (fst₃ , snd₂) , snd₁ = fst₂

  const-map : ∀ {A B} (f : A ⇒[ 𝓒 ] B) →
    𝟙! ∘[ 𝓒 ] f
      ≡
    𝟙!
  const-map {A} {B} f with 𝟙-Final A
  ... | fst , snd = ≐-eq (snd (𝟙! ∘[ 𝓒 ] f) tt)

  pair-proj₂ : ∀ {I A B} (f : I ⇒[ 𝓒 ] A) (g : I ⇒[ 𝓒 ] B) →
    Limits.pair₂ 𝓒 (⊗-Product A B) ∘[ 𝓒 ] pair f g
      ≡
    g
  pair-proj₂ {I} {A} {B} f g with ⊗-Product A B
  ... | fst , fst₁ , snd with snd {!!} f g
  pair-proj₂ {I} {A} {B} f g | fst , fst₁ , snd | fst₂ , (fst₃ , snd₂) , snd₁ = sym (≐-eq snd₂)

  -- compose-lemma : ∀ {A B} {f : 𝟙 ⇒[ 𝓒 ] A} {g : B ⇒[ 𝓒 ] 𝟙} →
  --   f ∘[ 𝓒 ] g ≡ f
  -- compose-lemma = ?

  module Semantics
    -- (⟦_⟧ : Term → (C⟦ Γ ⟧ ⇒[ 𝓒 ] T⟦ A ⟧))
    (⟦true⟧ : 𝟙 ⇒[ 𝓒 ] T⟦ Boolean ⟧)
    (⟦false⟧ : 𝟙 ⇒[ 𝓒 ] T⟦ Boolean ⟧)
    -- (⟦ƛ⟧ : ∀ {Γ A B} →
    --     ((C⟦ Γ ⟧ ⊗ T⟦ A ⟧) ⇒[ 𝓒 ] T⟦ B ⟧) →
    --     C⟦ Γ ⟧ ⇒[ 𝓒 ] (T⟦ A ⟧ ⇨ T⟦ B ⟧))

    -- (⟦_⊢_⦂_⟧ : (Γ : Context) → Term → (A : Type) → (C⟦ Γ ⟧ ⇒[ 𝓒 ] T⟦ A ⟧))
    where

    open Category.Category 𝓒

    Var⟦_⟧ : ∀ {Γ A} →
      Γ ∋ A →
      C⟦ Γ ⟧ ⇒[ 𝓒 ] T⟦ A ⟧
    Var⟦_⟧ {Γ ,, _} {A} ∋-here = Limits.pair₂ 𝓒 (⊗-Product C⟦ Γ ⟧ T⟦ A ⟧)
    Var⟦_⟧ {Γ ,, B} {A} (∋-there x) = Var⟦_⟧ x ∘[ 𝓒 ] Limits.pair₁ 𝓒 (⊗-Product C⟦ Γ ⟧ T⟦ B ⟧)

    ⟦_⟧ : ∀ {Γ M A} →
      Γ ⊢ M ⦂ A →
      (C⟦ Γ ⟧ ⇒[ 𝓒 ] T⟦ A ⟧)
    ⟦_⟧ {Γ} {.true} {.Boolean} Ty-true = ⟦true⟧ ∘[ 𝓒 ] 𝟙!
    ⟦_⟧ {Γ} {.false} {.Boolean} Ty-false = ⟦false⟧ ∘[ 𝓒 ] 𝟙!
    ⟦_⟧ {Γ} {.(V _)} {A} (Ty-V x refl) = Var⟦ x ⟧
    ⟦_⟧ {Γ} {.(_ · _)} {A} (Ty-· M-typed N-typed) =
      let ⟦M⟧ = ⟦ M-typed ⟧
          ⟦N⟧ = ⟦ N-typed ⟧
      in
      Limits.eval 𝓒 _⊗_ ⊗-Product _⇨_ ⇨-Exponential
        ∘[ 𝓒 ]
      pair ⟦M⟧ ⟦N⟧
    ⟦_⟧ {Γ} {.(ƛ _)} {.(_ Type.⇒ _)} (Ty-ƛ M-typed) =
      let ⟦M⟧ = ⟦ M-typed ⟧
      in
      Limits.curry 𝓒 _⊗_ ⊗-Product _⇨_ ⇨-Exponential ⟦M⟧

    open-subst1′-V : ∀ {Γ A B} {N} →
      (N-typed : (Γ ,, A) ⊢ N ⦂ B) →
      open-subst1-preserves-type (Ty-V ∋-here refl) N-typed
        ≡
      N-typed
    open-subst1′-V = λ N-typed → refl

    subst-lemma : ∀ {A B C} {M N} →
      (M-typed : (∅ ,, A) ⊢ M ⦂ B) →
      (N-typed : (∅ ,, C) ⊢ N ⦂ A) →
      ⟦ open-subst1′-preserves-type M-typed N-typed ⟧
        ≡
      ⟦ M-typed ⟧
        ∘[ 𝓒 ]
      (𝟙⊗ ∘[ 𝓒 ] ⟦ N-typed ⟧)
    subst-lemma Ty-true N-typed
      rewrite ≐-eq (assoc {f = ⟦true⟧} {g = 𝟙!} {h = 𝟙⊗ ∘[ 𝓒 ] ⟦ N-typed ⟧}) | const-map (𝟙⊗ ∘[ 𝓒 ] ⟦ N-typed ⟧) = refl
    subst-lemma Ty-false N-typed
      rewrite ≐-eq (assoc {f = ⟦false⟧} {g = 𝟙!} {h = 𝟙⊗ ∘[ 𝓒 ] ⟦ N-typed ⟧}) | const-map (𝟙⊗ ∘[ 𝓒 ] ⟦ N-typed ⟧) = refl
    subst-lemma {A} (Ty-V ∋-here refl) N-typed =
      sym (begin
        compose 𝓒 (Limits.pair₂ 𝓒 (⊗-Product 𝟙 T⟦ A ⟧)) (compose 𝓒 𝟙⊗ ⟦ N-typed ⟧)
              ≡⟨ sym (≐-eq assoc) ⟩
        ((Limits.pair₂ 𝓒 (⊗-Product 𝟙 T⟦ A ⟧) ∘[ 𝓒 ] 𝟙⊗) ∘[ 𝓒 ] ⟦ N-typed ⟧)
              ≡⟨ ≐-eq (≐-left 𝟙⊗-id) ⟩
        (Category.id 𝓒 ∘[ 𝓒 ] ⟦ N-typed ⟧)
              ≡⟨ ≐-eq (Category.left-id 𝓒) ⟩
        ⟦ N-typed ⟧
      ∎)
    subst-lemma (Ty-· M-typed M-typed₁) N-typed = {!!}
    subst-lemma (Ty-ƛ M-typed) N-typed = {!!}
