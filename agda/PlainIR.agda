{-# OPTIONS --without-K #-}

open import Lib

-- Section 2.2
module PlainIR where

private variable
  O : Set j

data Sig i {j} (O : Set j) : Set (suc i ⊔ j) where
  ι : O → Sig i O
  σ : (A : Set i) → (A → Sig i O) → Sig i O
  δ : (A : Set i) → ((A → O) → Sig i O) → Sig i O

infix 20 _₀
_₀ : Sig i O → (ir : Set i) → (ir → O) → Set i
(ι _   ₀) ir el = ⊤
(σ A S ₀) ir el = Σ A λ a → (S a ₀) ir el
(δ A S ₀) ir el = Σ (A → ir) λ f → (S (el ∘ f)₀) ir el

infix 20 _₁
_₁ : ∀ (S : Sig i O){ir el} → (S ₀) ir el → O
(ι o   ₁)        x       = o
(σ A S ₁)        (a , x) = (S a ₁) x
(δ A S ₁){ir}{el}(f , x) = (S (el ∘ f)₁) x

infix 20 _ᵢₕ
_ᵢₕ : ∀ S {ir : Set i} {el : ir → O} (P : ir → Set k) → (S ₀) ir el → Set (i ⊔ k)
(ι o   ᵢₕ)          P x       = ⊤
(σ A S ᵢₕ)          P (a , x) = (S a ᵢₕ) P x
(δ A S ᵢₕ) {ir}{el} P (f , x) = (∀ a → P (f a)) × (S (el ∘ f)ᵢₕ) P x

infix 20 _ₘₐₚ
_ₘₐₚ : ∀ S {ir : Set i}{el : ir → O}(P : ir → Set k) → (∀ x → P x) → (x : (S ₀) ir el) → (S ᵢₕ) P x
(ι o   ₘₐₚ)          P h x       = tt
(σ A S ₘₐₚ)          P h (a , x) = (S a ₘₐₚ) P h x
(δ A S ₘₐₚ) {ir}{el} P h (f , x) = (h ∘ f , (S (el ∘ f)ₘₐₚ) P h x)

data IR (S : Sig i O) : Set i
El : {S : Sig i O} → IR S → O

data IR S where
  intro : (S ₀) (IR S) El → IR S

{-# TERMINATING #-}
El {S = S} (intro t) = (S ₁) t

{-# TERMINATING #-}
elim : {S : Sig i O} (P : IR S → Set k) → (∀ x → (S ᵢₕ) P x → P (intro x)) → ∀ x → P x
elim {S = S} P f (intro x) = f x ((S ₘₐₚ) P (elim P f) x)

--------------------------------------------------------------------------------

outro : {S : Sig i O} → IR S → (S ₀) (IR S) El
outro {S = S} = elim _ λ x _ → x

SigElim :   (P : Sig i O → Set k)
          → ((o : O) → P (ι o))
          → ((A : Set i) (S : A → Sig i O) → ((a : A) → P (S a)) → P (σ A S))
          → ((A : Set i) (S : (A → O) → Sig i O) → ((f : A → O) → P (S f)) → P (δ A S))
          → ∀ S → P S
SigElim P ι' σ' δ' (ι o)   = ι' o
SigElim P ι' σ' δ' (σ A S) = σ' A S (SigElim P ι' σ' δ' ∘ S)
SigElim P ι' σ' δ' (δ A S) = δ' A S (SigElim P ι' σ' δ' ∘ S)

module Example-2-1 where

  open import Data.Nat using (ℕ)

  data Tag : Set where
    Nat' : Tag
    Π'   : Tag

  Example-2-1 : Sig zero Set₀
  Example-2-1 = σ Tag λ where
    Nat' → ι ℕ
    Π'   → δ ⊤ λ ElA → δ (ElA tt) λ ElB → ι ((x : ElA tt) → ElB x)
