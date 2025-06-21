
module UniversalInd where

open import Lib
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum
open import Data.Empty
open import Data.Nat

data Arity : Set where
  ι : Arity
  σ : Arity → Arity
  δ : Arity → Arity
  ν : ∀ {n} → (Fin n → Arity) → Arity

Sig : Arity → Set₁
Sig ι     = Lift _ ⊤
Sig (σ A) = Σ Set λ B → B → Sig A
Sig (δ A) = Set × Sig A
Sig (ν A) = ∀ i → Sig (A i)

Sig≤ : ∀ A → Arity → Sig A → Set
Sig< : ∀ A → Arity → Sig A → Set
Sig≤ A B S = A ≡ B ⊎ Sig< A B S
Sig< ι     B S       = ⊥
Sig< (σ A) B (X , S) = ∃ (Sig≤ A B ∘ S)
Sig< (δ A) B (X , S) = Sig≤ A B S
Sig< (ν A) B S       = ∃ λ i → Sig≤ (A i) B (S i)

proj≤ : ∀ {A B S} → Sig≤ A B S → Sig B
proj< : ∀ {A B S} → Sig< A B S → Sig B
proj≤ {A}   {B} {S}     (inj₁ refl) = S
proj≤ {A}   {B} {S}     (inj₂ p)    = proj< p
proj< {σ A} {B} {X , S} (x , p)     = proj≤ p
proj< {δ A} {B} {X , S} p           = proj≤ p
proj< {ν A} {B} {S}     (i , p)     = proj≤ p

σ≤ : ∀ {A B S} → (p : Sig≤ A (σ B) S) → proj≤ p .₁ → Sig≤ A B S
σ< : ∀ {A B S} → (p : Sig< A (σ B) S) → proj< p .₁ → Sig< A B S
σ≤ {A}   (inj₁ refl) y = inj₂ (y , inj₁ refl)
σ≤ {A}   (inj₂ p)    y = inj₂ (σ< p y)
σ< {σ A} (x , p)     y = x , σ≤ p y
σ< {δ A} p           y = σ≤ p y
σ< {ν A} (i , p)     y = i , σ≤ p y

δ≤ : ∀ {A B S} → (p : Sig≤ A (δ B) S) → Sig≤ A B S
δ< : ∀ {A B S} → (p : Sig< A (δ B) S) → Sig< A B S
δ≤ {A}   (inj₁ refl) = inj₂ (inj₁ refl)
δ≤ {A}   (inj₂ p)    = inj₂ (δ< p)
δ< {σ A} (x , p)     = x , δ≤ p
δ< {δ A} p           = δ≤ p
δ< {ν A} (i , p)     = i , (δ≤ p)

ν≤ : ∀ {A n B S} → (p : Sig≤ A (ν {n} B) S) → ∀ j → Sig≤ A (B j) S
ν< : ∀ {A n B S} → (p : Sig< A (ν {n} B) S) → ∀ j → Sig< A (B j) S
ν≤ {A}   (inj₁ refl) j = inj₂ (j , inj₁ refl)
ν≤ {A}   (inj₂ p)    j = inj₂ (ν< p j)
ν< {σ A} (x , p)     j = x , ν≤ p j
ν< {δ A} p           j = ν≤ p j
ν< {ν A} (i , p)     j = i , ν≤ p j

module _ {A}(S : Sig A) where

  data Tm : ∀ B → Sig≤ A B S → Set where
    ι : ∀ {p} → Tm ι p
    σ : ∀ {B p}(x : proj≤ p .₁) → Tm B (σ≤ p x) → Tm (σ B) p
    δ : ∀ {B p} → (proj≤ p .₁ → Tm A (inj₁ refl)) → Tm B (δ≤ p) → Tm (δ B) p
    ν : ∀ {n B p} i → Tm (B i) (ν≤ p i) → Tm (ν {n} B) p
