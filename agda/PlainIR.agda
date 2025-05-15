
open import Lib

module PlainIR (ext : Level) (ol : Level) (O : Set ol) where

  data Sig : Set (lsuc (ext ⊔ ol)) where
    ι : O → Sig
    σ : (A : Set ext) → (A → Sig) → Sig
    δ : (A : Set ext) → ((A → O) → Sig) → Sig

  F0 : Sig → (u : Set ext) → (u → O) → Set ext
  F0 (ι _)   u el = Lift _ ⊤
  F0 (σ A Γ) u el = Σ A λ a → F0 (Γ a) u el
  F0 (δ A Γ) u el = Σ (A → u) λ f → F0 (Γ (el ∘ f)) u el

  F1 : ∀ Γ u el → F0 Γ u el → O
  F1 (ι o)   u el t       = o
  F1 (σ A Γ) u el (a , t) = F1 (Γ a) u el t
  F1 (δ A Γ) u el (f , t) = F1 (Γ (el ∘ f)) u el t

  IH : ∀ {j} Γ (u : Set ext) (el : u → O) (P : u → Set j) → F0 Γ u el → Set (ext ⊔ j)
  IH (ι o)   u el P t       = Lift _ ⊤
  IH (σ A Γ) u el P (a , t) = IH (Γ a) u el P t
  IH (δ A Γ) u el P (f , t) = (∀ a → P (f a)) × IH (Γ (el ∘ f)) u el P t

  mapIH : ∀ {j} Γ (u : Set ext)(el : u → O)(P : u → Set j)(t : F0 Γ u el)(f : ∀ x → P x) → IH Γ u el P t
  mapIH (ι _)   u el P t       f = lift tt
  mapIH (σ A Γ) u el P (a , t) f = mapIH (Γ a) u el P t f
  mapIH (δ A Γ) u el P (g , t) f = f ∘ g , mapIH (Γ (el ∘ g)) u el P t f

  data U (Γ : Sig) : Set ext
  El : ∀ Γ → U Γ → O

  data U Γ where
    wrap : F0 Γ (U Γ) (El Γ) → U Γ

  {-# TERMINATING #-}
  El Γ (wrap t) = F1 Γ (U Γ) (El Γ) t

  {-# TERMINATING #-}
  elim : ∀ {j} Γ (P : U Γ → Set j) → (∀ t → IH Γ (U Γ) (El Γ) P t → P (wrap t)) → ∀ t → P t
  elim Γ P f (wrap t) = f t (mapIH _ _ _ _ t (elim Γ P f))
