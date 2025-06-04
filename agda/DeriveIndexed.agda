
open import Lib

module DeriveIndexed {ext il ol : Level }(I : Set il)(O : I → Set ol) where

import PlainIR (ext ⊔ il) (il ⊔ ol) (∃ O) as IR

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

mapIH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il))(el : {i : I} → u i → O i)
          i (P : ∀ {i} → u i → Set j)(t : F0 Γ u el i)
        → (∀ {i} u → P {i} u) → IH Γ u el P t
mapIH (ι i' o)   u el i P t       f = lift tt
mapIH (σ A Γ)    u el i P (a , t) f = mapIH (Γ a) u el i P t f
mapIH (δ A ix Γ) u el i P (g , t) f = f ∘ g , mapIH (Γ (el ∘ g)) u el i P t f

--------------------------------------------------------------------------------

encSig : Sig → IR.Sig
encSig (ι i o)   = IR.ι (i , o)
encSig (σ A S)   = IR.σ (Lift (ext ⊔ il) A) λ a → encSig (S (lower a))
encSig (δ A f S) = IR.δ (Lift (ext ⊔ il) A) λ g → IR.σ ((a : A) → g (lift a) .₁ ≡ f a)
                        λ g* → encSig (S (λ a → tr O (g* a) (g (lift a) .₂)))

module _ (S* : Sig) where

  S*' = encSig S*

  U : I → Set (ext ⊔ il)
  U i = Σ (IR.U S*') (λ x → IR.El S*' x .₁ ≡ i)

  El : ∀ {i} → U i → O i
  El {i} (x , wx) = tr O wx (IR.El S*' x .₂)

  -- characterization of encode-decode
  --   F0 i ≃ ((x : IR.F0) × F1 x .₁ ≡ i)
  encF0 : ∀ {i} S → F0 S U El i → IR.F0 (encSig S) (IR.U S*') (IR.El S*')
  encF0 (ι i o)   x       = lift tt
  encF0 (σ A S)   (a , x) = lift a , encF0 (S a) x
  encF0 (δ A f S) (g , x) = (λ a → g (lower a) .₁) , (λ a → g a .₂) , encF0 (S (El ∘ g)) x

  encF1 : ∀ {i} S (x : F0 S U El i)
          → IR.F1 (encSig S) (IR.U S*') (IR.El S*') (encF0 S x)
          ≡ (i , F1 S U El x)
  encF1 (ι i o)   (lift refl) = refl
  encF1 (σ A S)   (a , x)     = encF1 (S a) x
  encF1 (δ A f S) (g , x)     = encF1 (S _) x

  decF0 : ∀ {i} S → IR.F0 (encSig S) (IR.U S*') (IR.El S*') → F0 S U El i
  decF0 (ι i' o)  x = {!!}
  decF0 (σ A S)   (lift a , x) = a , decF0 (S a) x
  decF0 (δ A f S) (g , gw , x) = {!!} , {!!}

  wrap : ∀ {i} → F0 S* U El i → U i
  wrap x = IR.wrap (encF0 S* x) , ap ₁ (encF1 S* x)

  El≡ : ∀ {i} x → El (wrap {i} x) ≡ F1 S* U El x
  El≡ x = tr-∘ O ₁ (encF1 S* x) _ ◼ apd ₂ (encF1 S* x)

  elim : ∀ {j}(P : ∀ {i} → U i → Set j)
         → (∀ {i} x → IH S* U El P {i} x → P (wrap x)) → ∀ {i} x → P {i} x
  elim P met {i} (x , wx) = IR.elim S*'
    (λ x → ∀ {i} wx → P {i} (x , wx))
    (λ x ih {i} wx' → {!met!})
    x
    wx

  -- elim Γ P f (wrap t) = f t (mapIH _ _ _ _ _ t (elim Γ P f))
