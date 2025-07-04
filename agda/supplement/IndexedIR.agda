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

E : Sig i {j}{k} I O → (ir : I → Set (i ⊔ k)) → (∀ {ix} → ir ix → O ix) → I → Set (i ⊔ k)
E {i}{_}{k}(ι ix' o  ) ir el ix = Lift (i ⊔ k) (ix' ≡ ix)
E          (σ A S    ) ir el ix = Σ A λ a → E (S a) ir el ix
E          (δ A ix' S) ir el ix = Σ (∀ a → ir (ix' a)) λ f → E (S (el ∘ f)) ir el ix

F : ∀ {S : Sig i {j}{k} I O}{ir : I → Set (i ⊔ k)}{el : ∀ {i} → ir i → O i} → ∀ {ix} → E S ir el ix → O ix
F {O = O}{S = ι ix o}            (↑ x)   = tr O x o
F        {S = σ A S}             (a , x) = F {S = S a} x
F        {S = δ A ix S} {ir}{el} (f , x) = F {S = S (el ∘ f)} x

IH : ∀ {S : Sig i {j}{k} I O}{ir : I → Set (i ⊔ k)}{el : ∀{ix} → ir ix → O ix}
       (P : ∀ {ix} → ir ix → Set l) → ∀ {ix} → E S ir el ix → Set (i ⊔ l)
IH {S = ι ix o  }          P _       = ⊤
IH {S = σ A S   }          P (a , x) = IH {S = S a} P x
IH {S = δ A ix S} {ir}{el} P (f , x) = (∀ a → P (f a)) × IH {S = S (el ∘ f)} P x

map : ∀ {S : Sig i {j}{k} I O}{ir : I → Set (i ⊔ k)}{el : {ix : I} → ir ix → O ix} {P : ∀ {ix} → ir ix → Set l}
      → (∀ {ix} x → P {ix} x) → ∀ {ix} (x : E S ir el ix) → IH P x
map {S = ι i' o  }          h t       = tt
map {S = σ A S   }          h (a , x) = map {S = S a} h x
map {S = δ A ix S} {ir}{el} h (f , x) = (h ∘ f , map {S = S (el ∘ f)} h x)

mutual
  data IIR (S : Sig i {j}{k} I O) : I → Set (i ⊔ k) where
    intro : ∀ {i} → E S (IIR S) El i → IIR S i

  {-# TERMINATING #-}
  El : ∀ {S : Sig i {j}{k} I O}{ix} → IIR S ix → O ix
  El {S = S} (intro x) = F x

{-# TERMINATING #-}
elim : ∀ {S : Sig i {j}{k} I O}(P : ∀ {ix} → IIR S ix → Set l)
       → (∀ {ix} x → IH P {ix} x → P (intro x)) → ∀ {ix} x → P {ix} x
elim {S = S} P f (intro x) = f x (map (elim P f) x)

module Ex-2-2 where

  import Data.Nat as N

  data Tag : Set where Nil' Cons' : Tag

  S : (A : Set) → Sig zero {zero}{zero} N.ℕ (λ _ → ⊤)
  S A = σ Tag λ where
    Nil'  → ι N.zero tt
    Cons' → σ N.ℕ λ n → σ A λ _ → δ ⊤ (λ _ → n) λ _ → ι (N.suc n) tt
