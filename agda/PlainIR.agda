{-# OPTIONS --without-K #-}

open import Lib

module PlainIR (i : Level) (j : Level) (O : Set j) where

  data Sig : Set (lsuc i ⊔ j) where
    ι : O → Sig
    σ : (A : Set i) → (A → Sig) → Sig
    δ : (A : Set i) → ((A → O) → Sig) → Sig

  F0 : Sig → (ir : Set i) → (ir → O) → Set i
  F0 (ι _)   ir el = Lift _ ⊤
  F0 (σ A Γ) ir el = Σ A λ a → F0 (Γ a) ir el
  F0 (δ A Γ) ir el = Σ (A → ir) λ f → F0 (Γ (el ∘ f)) ir el

  F1 : ∀ S {ir el} → F0 S ir el → O
  F1 (ι o)          x       = o
  F1 (σ A Γ)        (a , x) = F1 (Γ a) x
  F1 (δ A Γ){ir}{el}(f , x) = F1 (Γ (el ∘ f)) x

  IH : ∀ {k} S {ir : Set i} {el : ir → O} (P : ir → Set k) → F0 S ir el → Set (i ⊔ k)
  IH (ι o)            P x       = Lift _ ⊤
  IH (σ A S)          P (a , x) = IH (S a) P x
  IH (δ A S) {ir}{el} P (f , x) = (∀ a → P (f a)) × IH (S (el ∘ f)) P x

  mapIH : ∀ {k} Γ {ir : Set i}{el : ir → O}(P : ir → Set k) → (∀ x → P x) → (x : F0 Γ ir el) → IH Γ P x
  mapIH (ι o)            P h x       = lift tt
  mapIH (σ A Γ)          P h (a , x) = mapIH (Γ a) P h x
  mapIH (δ A Γ) {ir}{el} P h (f , x) = h ∘ f , mapIH (Γ (el ∘ f)) P h x

  data IR (S : Sig) : Set i
  El : ∀ {S} → IR S → O

  data IR S where
    wrap : F0 S (IR S) El → IR S

  {-# TERMINATING #-}
  El {S} (wrap t) = F1 S t

  {-# TERMINATING #-}
  elim : ∀ {k} S (P : IR S → Set k) → (∀ x → IH S P x → P (wrap x)) → ∀ x → P x
  elim S P f (wrap x) = f x (mapIH S P (elim S P f) x)


  -- misc definitions
  ------------------------------------------------------------

  unwrap : ∀ {S} → IR S → F0 S (IR S) El
  unwrap {S} = elim S _ λ x _ → x

  SigElim : ∀ {k}(P : Sig → Set k)
            → ((o : O) → P (ι o))
            → ((A : Set i) (S : A → Sig) → ((a : A) → P (S a)) → P (σ A S))
            → ((A : Set i) (S : (A → O) → Sig) → ((f : A → O) → P (S f)) → P (δ A S))
            → ∀ S → P S
  SigElim P ι' σ' δ' (ι o)   = ι' o
  SigElim P ι' σ' δ' (σ A S) = σ' A S (SigElim P ι' σ' δ' ∘ S)
  SigElim P ι' σ' δ' (δ A S) = δ' A S (SigElim P ι' σ' δ' ∘ S)
