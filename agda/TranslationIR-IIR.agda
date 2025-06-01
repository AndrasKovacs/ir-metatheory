{-# OPTIONS --type-in-type #-}
open import Lib

module TranslationIR-IIR {ext il ol}(I : Set il) (O : I → Set ol) where

  import IndexedIR {ext = ext} I O as IIR
  import PlainIR ext (il ⊔ ol) (Σ I O) as IR

  Sig : Set (lsuc (ext ⊔ il ⊔ ol))
  Sig = IR.Sig

  ι : ∀ i → O i → Sig
  ι i o = IR.ι (i , o)

  σ : (A : Set ext) → (A → Sig) → Sig
  σ A x = IR.σ A x

  δ : (A : Set ext)(f : A → I) → ((∀ a → O (f a)) → Sig) → Sig
  δ A f x = {!!}

  F0 : Sig → (u : I → Set (ext ⊔ il))(el : ∀ {i} → u i → O i) → I → Set (ext ⊔ il)
  F0 Γ u el i = Σ (IR.F0 Γ (u i) λ x → i , el x) λ x → IR.F1 Γ (u i) (λ x₁ → i , el x₁) x .₁ ≡ i

  F1 : ∀ (Γ : Sig)(u : I → Set (ext ⊔ il))(el : ∀ {i} → u i → O i) → ∀ {i} → F0 Γ u el i → O i
  F1 Γ u el {i} (f0 , eq) = tr O eq (IR.F1 Γ (u i) (λ x₁ → i , el x₁) f0 .₂)


  IH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il))(el : ∀{i} → u i → O i)
            (P : ∀ {i} → u i → Set j) → ∀ {i} → F0 Γ u el i → Set (ext ⊔ j)
  IH Γ u el P {i} (f0 , snd) = IR.IH Γ (u i) (λ x₁ → i , el x₁) P f0

  mapIH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il))(el : {i : I} → u i → O i) i (P : ∀ {i} → u i → Set j)(t : F0 Γ u el i)
          → (∀ {i} u → P {i} u) → IH Γ u el P t
  mapIH Γ u el i P t f = IR.mapIH Γ (u i) (λ x₁ → i , el x₁) P (t .₁) f

  mutual
    U : Sig → I → Set (ext ⊔ il)
    U Γ i = Σ (IR.U Γ) λ x → IR.El Γ x .₁ ≡ i

    {-# TERMINATING #-}
    El : ∀ Γ {i} → U Γ i → O i
    El Γ {i} (u , refl) = (IR.El Γ u) .₂

    wrap : ∀ {i Γ} → F0 Γ (U Γ) (El Γ) i → U Γ i
    wrap (fst , snd) = (IR.wrap {!fst!}) , {!!}

  {-# TERMINATING #-}
  elim : ∀ {j}(Γ : Sig)(P : ∀ {i} → U Γ i → Set j) → (∀ {i} t → IH Γ (U Γ) (El Γ) P {i} t → P (wrap t)) → ∀ {i} t → P {i} t
  elim Γ P f br = IR.elim Γ {!!} {!!} (br .₁)
