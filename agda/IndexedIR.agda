{-# OPTIONS --without-K #-}

open import Lib

module IndexedIR where

private variable
  I : Set k
  O : I → Set j

data Sig i {j k}(I : Set k)(O : I → Set j) : Set (suc i ⊔ j ⊔ k) where
  ι : ∀ ix → O ix → Sig i I O
  σ : (A : Set i) → (A → Sig i I O) → Sig i I O
  δ : (A : Set i)(f : A → I) → ((∀ a → O (f a)) → Sig i I O) → Sig i I O

_₀ : Sig i {j}{k} I O → (ir : I → Set (i ⊔ k)) → (∀ {ix} → ir ix → O ix) → I → Set (i ⊔ k)
_₀ {i}{_}{k}(ι ix' o  ) ir el ix = Lift (i ⊔ k) (ix' ≡ ix)
_₀          (σ A S    ) ir el ix = Σ A λ a → (S a ₀) ir el ix
_₀          (δ A ix' S) ir el ix = Σ (∀ a → ir (ix' a)) λ f → (S (el ∘ f)₀) ir el ix

_₁ : ∀ (S : Sig i {j}{k} I O){ir : I → Set (i ⊔ k)}{el : ∀ {i} → ir i → O i} → ∀ {ix} → _₀ S ir el ix → O ix
_₁ {O = O}(ι ix o)            (lift x) = tr O x o
_₁        (σ A S)             (a , x)  = (S a ₁) x
_₁        (δ A ix S) {ir}{el} (f , x)  = (S (el ∘ f)₁) x

_ᵢₕ : ∀ (S : Sig i {j}{k} I O){ir : I → Set (i ⊔ k)}{el : ∀{ix} → ir ix → O ix}
        (P : ∀ {ix} → ir ix → Set l) → ∀ {ix} → (S ₀) ir el ix → Set (i ⊔ l)
_ᵢₕ (ι ix o)            P _       = ⊤
_ᵢₕ (σ A S)             P (a , x) = (S a ᵢₕ) P x
_ᵢₕ (δ A ix S) {ir}{el} P (f , x) = (∀ a → P (f a)) × (S (el ∘ f) ᵢₕ) P x

_ₘₐₚ : ∀ (S : Sig i {j}{k} I O){ir : I → Set (i ⊔ k)}{el : {ix : I} → ir ix → O ix} (P : ∀ {ix} → ir ix → Set l)
        → (∀ {ix} x → P {ix} x) → ∀ {ix} (x : (S ₀) ir el ix) → (S ᵢₕ) P x
_ₘₐₚ (ι i' o)            P h t       = tt
_ₘₐₚ (σ A S)             P h (a , x) = (S a ₘₐₚ) P h x
_ₘₐₚ (δ A ix S) {ir}{el} P h (f , x) = (h ∘ f , (S (el ∘ f)ₘₐₚ) P h x)

mutual
  data IIR (S : Sig i {j}{k} I O) : I → Set (i ⊔ k) where
    intro : ∀ {i} → (S ₀) (IIR S) El i → IIR S i

  {-# TERMINATING #-}
  El : ∀ {S : Sig i {j}{k} I O}{ix} → IIR S ix → O ix
  El {S = S} (intro x) = (S ₁) x

{-# TERMINATING #-}
elim : ∀ {S : Sig i {j}{k} I O}(P : ∀ {ix} → IIR S ix → Set l)
       → (∀ {ix} x → (S ᵢₕ) P {ix} x → P (intro x)) → ∀ {ix} x → P {ix} x
elim {S = S} P f (intro x) = f x ((S ₘₐₚ) P (elim P f) x)
