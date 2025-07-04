
open import Lib renaming (zero to lzero; suc to lsuc; fst to ₁; snd to ₂)

module UniversalIndFam {li j : Level}(I : Set j) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Sum
open import Data.Empty
open import Data.Nat hiding (_⊔_)

data Arity : Set where
  ι : Arity
  σ : Arity → Arity
  δ : Arity → Arity
  ν : ∀ {n} → (Fin n → Arity) → Arity

Sig : Arity → Set (lsuc li ⊔ j)
Sig ι     = Lift (lsuc li ⊔ j) I
Sig (σ A) = Σ (Set li) λ X → X → Sig A
Sig (δ A) = Σ (Set li) λ X → (X → I) × Sig A
Sig (ν A) = ∀ i → Sig (A i)

Sig≤ : ∀ A → Arity → Sig A → Set (li ⊔ j)
Sig< : ∀ A → Arity → Sig A → Set (li ⊔ j)
Sig≤ A B S = A ≡ B ⊎ Sig< A B S
Sig< ι     B S            = Lift _ ⊥
Sig< (σ A) B (X , S)      = ∃ (Sig≤ A B ∘ S)
Sig< (δ A) B (X , ix , S) = Sig≤ A B S
Sig< (ν A) B S            = ∃ λ i → Sig≤ (A i) B (S i)

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

  data Tm : ∀ B → Sig≤ A B S → I → Set (li ⊔ j) where
    ι : ∀ {p} → Tm ι p (proj≤ p .↓)
    σ : ∀ {B p i} x → Tm B (σ≤ p x) i → Tm (σ B) p i
    δ : ∀ {B p i} → (∀ x → Tm A (inj₁ refl) (proj≤ p .₂ .₁ x)) → Tm B (δ≤ p) i → Tm (δ B) p i
    ν : ∀ {n B p i} ix → Tm (B ix) (ν≤ p ix) i → Tm (ν {n} B) p i

  module ElimPriv {k : Level} where

    Motive : ∀ B (p : Sig≤ A B S) → Set (li ⊔ j ⊔ lsuc k)
    Motive B p = ∀ i → Tm B p i → Set k

    Methods : ∀ B (p : Sig≤ A B S) → Motive A (inj₁ refl) → Motive B p → Set (li ⊔ j ⊔ k)
    Methods ι     p P Q = Lift (li ⊔ j ⊔ k) (Q (proj≤ p .↓) ι)
    Methods (σ B) p P Q = ∀ x → Methods B (σ≤ p x) P (λ i t → Q i (σ x t))
    Methods (δ B) p P Q = ∀ f → (∀ x → P (proj≤ p .₂ .₁ x) (f x)) → Methods B (δ≤ p) P (λ i t → Q i (δ f t))
    Methods (ν B) p P Q = ∀ ix → Methods (B ix) (ν≤ p ix) P (λ i t → Q i (ν ix t))

    Elim : ∀ B p (P : Motive A (inj₁ refl)) (Q : Motive B p) → Methods A (inj₁ refl) P P → Methods B p P Q → ∀ i t → Q i t
    Elim B p P Q f g i ι        = g .↓
    Elim B p P Q f g i (σ x t)  = Elim _ (σ≤ p x) P _ f (g x) i t
    Elim B p P Q f g i (δ h t)  = Elim _ (δ≤ p) P _ f (g h λ x → Elim A _ P P f f _ (h x)) i t
    Elim B p P Q f g i (ν ix t) = Elim _ (ν≤ p ix) P _ f (g ix) i t

  Ind : I → Set (li ⊔ j)
  Ind i = Tm A (inj₁ refl) i

  module _ {k} where

    Motive : Set (li ⊔ j ⊔ lsuc k)
    Motive = ElimPriv.Motive {k} A (inj₁ refl)

    Methods : Motive → Set (li ⊔ j ⊔ k)
    Methods P = ElimPriv.Methods {k} A (inj₁ refl) P P

    Elim : (P : Motive) → Methods P → ∀ i t → P i t
    Elim P f i t = ElimPriv.Elim A (inj₁ refl) P P f f i t
