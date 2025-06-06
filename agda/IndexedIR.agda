{-# OPTIONS --without-K #-}

open import Lib

module IndexedIR {ext il ol}(I : Set il)(O : I → Set ol) where

  data Sig : Set (lsuc (ext ⊔ il ⊔ ol)) where
    ι : ∀ i → O i → Sig
    σ : (A : Set ext) → (A → Sig) → Sig
    δ : (A : Set ext)(f : A → I) → ((∀ a → O (f a)) → Sig) → Sig

  F0 : Sig → (u : I → Set (ext ⊔ il))(el : ∀ {i} → u i → O i) → I → Set (ext ⊔ il)
  F0 (ι i* _)  u el i = Lift (ext ⊔ il) (i* ≡ i)
  F0 (σ A Γ)   u el i = Σ A λ a → F0 (Γ a) u el i
  F0 (δ A f Γ) u el i = Σ (∀ a → u (f a)) λ g → F0 (Γ (el ∘ g)) u el i

  F1 : ∀ (Γ : Sig)(u : I → Set (ext ⊔ il))(el : ∀ {i} → u i → O i) → ∀ {i} → F0 Γ u el i → O i
  F1 (ι _ o)    u el p       = tr O (lower p) o
  F1 (σ A Γ)    u el (a , t) = F1 (Γ a) u el t
  F1 (δ A ix Γ) u el (f , t) = F1 (Γ (el ∘ f)) u el t

  IH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il))(el : ∀{i} → u i → O i)
            (P : ∀ {i} → u i → Set j) → ∀ {i} → F0 Γ u el i → Set (ext ⊔ j)
  IH (ι _ _)    u el P _       = Lift _ ⊤
  IH (σ A Γ)    u el P (a , t) = IH (Γ a) u el P t
  IH (δ A ix Γ) u el P (f , t) = (∀ a → P (f a)) × IH (Γ (el ∘ f)) u el P t

  mapIH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il))(el : {i : I} → u i → O i) i (P : ∀ {i} → u i → Set j)(t : F0 Γ u el i)
          → (∀ {i} u → P {i} u) → IH Γ u el P t
  mapIH (ι i' o)   u el i P t       f = lift tt
  mapIH (σ A Γ)    u el i P (a , t) f = mapIH (Γ a) u el i P t f
  mapIH (δ A ix Γ) u el i P (g , t) f = f ∘ g , mapIH (Γ (el ∘ g)) u el i P t f

  mutual
    data U (Γ : Sig) : I → Set (ext ⊔ il) where
      wrap : ∀ {i} → F0 Γ (U Γ) (El Γ) i → U Γ i

    {-# TERMINATING #-}
    El : ∀ Γ {i} → U Γ i → O i
    El Γ (wrap t) = F1 Γ (U Γ) (El Γ) t

  {-# TERMINATING #-}
  elim : ∀ {j}(Γ : Sig)(P : ∀ {i} → U Γ i → Set j) → (∀ {i} t → IH Γ (U Γ) (El Γ) P {i} t → P (wrap t)) → ∀ {i} t → P {i} t
  elim Γ P f (wrap t) = f t (mapIH _ _ _ _ _ t (elim Γ P f))
