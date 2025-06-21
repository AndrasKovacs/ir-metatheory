{- DOESNT WORK -}

open import Lib
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum
open import Data.Maybe
open import Data.Empty
open import Data.Nat using (ℕ; suc; zero)

module UniversalII (i j : Level) (O : Set j) where

data Arity : Set where
  ι : Arity
  σ : Arity → Arity
  δ : Arity → Arity
  ν : ∀ {n} → (Fin n → Arity) → Arity

Sig : Arity → Set (lsuc i ⊔ j)
Sig ι     = Lift (lsuc i ⊔ j) O
Sig (σ A) = Σ (Set i) λ X → X → Sig A
Sig (δ A) = Σ (Set i) λ X → (X → O) → Sig A
Sig (ν A) = ∀ i → Sig (A i)

Sig≤ : ∀ A → Arity → Sig A → Set i
Sig< : ∀ A → Arity → Sig A → Set i
Sig≤ A B S = A ≡ B ⊎ Sig< A B S
Sig< ι     B S       = Lift _ ⊥
Sig< (σ A) B (X , S) = ∃ λ x → Sig≤ A B (S x)
Sig< (δ A) B (X , S) = {!X → ?!} -- ∃ λ f → Sig≤ A B (S f)
Sig< (ν A) B S       = ∃ λ i → Sig≤ (A i) B (S i)

postulate
  proj≤ : ∀ {A B S} → Sig≤ A B S → Sig B
  proj< : ∀ {A B S} → Sig< A B S → Sig B
  -- proj≤ {A}   {B} {S}     (inj₁ refl) = S
  -- proj≤ {A}   {B} {S}     (inj₂ p)    = proj< p
  -- proj< {σ A} {B} {X , S} (x , p)     = proj≤ p
  -- proj< {δ A} {B} {X , S} p           = proj≤ p
  -- proj< {ν A} {B} {S}     (i , p)     = proj≤ p

  σ≤ : ∀ {A B S} → (p : Sig≤ A (σ B) S) → proj≤ p .₁ → Sig≤ A B S
  -- σ< : ∀ {A B S} → (p : Sig< A (σ B) S) → proj< p .₁ → Sig< A B S
  -- σ≤ {A}   (inj₁ refl) y = inj₂ (y , inj₁ refl)
  -- σ≤ {A}   (inj₂ p)    y = inj₂ (σ< p y)
  -- σ< {σ A} (x , p)     y = x , σ≤ p y
  -- σ< {δ A} p           y = σ≤ p y
  -- σ< {ν A} (i , p)     y = i , σ≤ p y

  -- δ≤ : ∀ {A B S} → (p : Sig≤ A (δ B) S) → Sig≤ A B S
  -- δ< : ∀ {A B S} → (p : Sig< A (δ B) S) → Sig< A B S
  -- δ≤ {A}   (inj₁ refl) = inj₂ (inj₁ refl)
  -- δ≤ {A}   (inj₂ p)    = inj₂ (δ< p)
  -- δ< {σ A} (x , p)     = x , δ≤ p
  -- δ< {δ A} p           = δ≤ p
  -- δ< {ν A} (i , p)     = i , (δ≤ p)

  ν≤ : ∀ {A n B S} → (p : Sig≤ A (ν {n} B) S) → ∀ j → Sig≤ A (B j) S
  ν< : ∀ {A n B S} → (p : Sig< A (ν {n} B) S) → ∀ j → Sig< A (B j) S
  -- ν≤ {A}   (inj₁ refl) j = inj₂ (j , inj₁ refl)
  -- ν≤ {A}   (inj₂ p)    j = inj₂ (ν< p j)
  -- ν< {σ A} (x , p)     j = x , ν≤ p j
  -- ν< {δ A} p           j = ν≤ p j
  -- ν< {ν A} (i , p)     j = i , ν≤ p j

module _ {A}(S : Sig A) where

  data Tm : ∀ B → Sig≤ A B S → Set i
  El : ∀ B p → Tm B p → O

  data Tm where
    ι : ∀ {p} → Tm ι p
    σ : ∀ {B p}(x : proj≤ p .₁) → Tm B (σ≤ p x) → Tm (σ B) p
    ν : ∀ {n B p} i → Tm (B i) (ν≤ p i) → Tm (ν {n} B) p
    δ : ∀ {B p}(f : proj≤ p .₁ → Tm A (inj₁ refl)) → Tm B {!!} → Tm (δ B) p

  El B p ι       = proj≤ p .lower
  El B p (σ x t) = El _ _ t
  El B p (ν i t) = El _ _ t
  El B p (δ f t) = {!!}

    -- ι : ∀ {p} → Tm ι p
    -- σ : ∀ {B p}(x : proj≤ p .₁) → Tm B (σ≤ p x) → Tm (σ B) p
    -- -- δ : ∀ {B p} → (proj≤ p .₁ → Tm A (inj₁ refl)) → Tm B (δ≤ p) → Tm (δ B) p
    -- ν : ∀ {n B p} i → Tm (B i) (ν≤ p i) → Tm (ν {n} B) p
