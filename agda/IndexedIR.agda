{-# OPTIONS --without-K #-}

open import Lib

module IndexedIR {li j k}(I : Set k)(O : I → Set j) where

  data Sig : Set (lsuc li ⊔ j ⊔ k) where
    ι : ∀ i → O i → Sig
    σ : (A : Set li) → (A → Sig) → Sig
    δ : (A : Set li)(f : A → I) → ((∀ a → O (f a)) → Sig) → Sig

  F0 : Sig → (ir : I → Set (li ⊔ k)) → (∀ {i} → ir i → O i) → I → Set (li ⊔ k)
  F0 (ι i' _)   ir el i = Lift (li ⊔ k) (i' ≡ i)
  F0 (σ A S)    ir el i = Σ A λ a → F0 (S a) ir el i
  F0 (δ A ix S) ir el i = Σ (∀ a → ir (ix a)) λ f → F0 (S (el ∘ f)) ir el i

  F1 : ∀ (S : Sig){ir : I → Set (li ⊔ k)}{el : ∀ {i} → ir i → O i} → ∀ {i} → F0 S ir el i → O i
  F1 (ι _ o)             (lift x) = tr O x o
  F1 (σ A S)             (a , x)  = F1 (S a) x
  F1 (δ A ix S) {ir}{el} (f , x)  = F1 (S (el ∘ f)) x

  IH : ∀ {l}(S : Sig){ir : I → Set (li ⊔ k)}{el : ∀{i} → ir i → O i}
            (P : ∀ {i} → ir i → Set l) → ∀ {i} → F0 S ir el i → Set (li ⊔ l)
  IH (ι _ _)             P _       = Lift _ ⊤
  IH (σ A S)             P (a , x) = IH (S a) P x
  IH (δ A ix S) {ir}{el} P (f , x) = (∀ a → P (f a)) × IH (S (el ∘ f)) P x

  mapIH : ∀ {l}(S : Sig){ir : I → Set (li ⊔ k)}{el : {i : I} → ir i → O i} (P : ∀ {i} → ir i → Set l)
          → (∀ {i} x → P {i} x) → ∀ {i} (x : F0 S ir el i) → IH S P x
  mapIH (ι i' o)            P h t       = lift tt
  mapIH (σ A S)             P h (a , x) = mapIH (S a) P h x
  mapIH (δ A ix S) {ir}{el} P h (f , x) = h ∘ f , mapIH (S (el ∘ f)) P h x

  mutual
    data IR (S : Sig) : I → Set (li ⊔ k) where
      wrap : ∀ {i} → F0 S (IR S) El i → IR S i

    {-# TERMINATING #-}
    El : ∀ {S i} → IR S i → O i
    El {S} (wrap x) = F1 S x

  {-# TERMINATING #-}
  elim : ∀ {l}(S : Sig)(P : ∀ {i} → IR S i → Set l)
         → (∀ {i} x → IH S P {i} x → P (wrap x)) → ∀ {i} x → P {i} x
  elim S P f (wrap x) = f x (mapIH S P (elim S P f) x)
