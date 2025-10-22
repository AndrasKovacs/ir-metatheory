{-# OPTIONS --without-K #-}

open import Lib

-- Section 2.3
----------------------------------------------------------------------------------------------------

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
E          (δ A ixs S) ir el ix = Σ (∀ a → ir (ixs a)) λ f → E (S (el ∘ f)) ir el ix

F : ∀ {S : Sig i {j}{k} I O}{ir : I → Set (i ⊔ k)}{el : ∀ {i} → ir i → O i} → ∀ {ix} → E S ir el ix → O ix
F {O = O}{S = ι ix o}             (↑ x)   = tr O x o
F        {S = σ A S}              (a , x) = F {S = S a} x
F        {S = δ A ixs S} {ir}{el} (f , x) = F {S = S (el ∘ f)} x

IH : ∀ {S : Sig i {j}{k} I O}{ir : I → Set (i ⊔ k)}{el : ∀{ix} → ir ix → O ix}
       (P : ∀ {ix} → ir ix → Set l) → ∀ {ix} → E S ir el ix → Set (i ⊔ l)
IH {S = ι ix o   }          P _       = ⊤
IH {S = σ A S    }          P (a , x) = IH {S = S a} P x
IH {S = δ A ixs S} {ir}{el} P (f , x) = (∀ a → P (f a)) × IH {S = S (el ∘ f)} P x

map : ∀ {S : Sig i {j}{k} I O}{ir : I → Set (i ⊔ k)}{el : {ix : I} → ir ix → O ix} {P : ∀ {ix} → ir ix → Set l}
      → (∀ {ix} x → P {ix} x) → ∀ {ix} (x : E S ir el ix) → IH P x
map {S = ι i' o   }          g t       = tt
map {S = σ A S    }          g (a , x) = map {S = S a} g x
map {S = δ A ixs S} {ir}{el} g (f , x) = (g ∘ f , map {S = S (el ∘ f)} g x)

mutual
  data IIR (S : Sig i {j}{k} I O) : I → Set (i ⊔ k) where
    intro : ∀ {ix} → E S (IIR S) El ix → IIR S ix

  {-# TERMINATING #-}
  El : ∀ {S : Sig i {j}{k} I O}{ix} → IIR S ix → O ix
  El {S = S} (intro x) = F x

{-# TERMINATING #-}
elim : ∀ {S : Sig i {j}{k} I O}(P : ∀ {ix} → IIR S ix → Set l)
       → (∀ {ix} x → IH P {ix} x → P (intro x)) → ∀ {ix} x → P {ix} x
elim {S = S} P f (intro x) = f x (map (elim P f) x)


----------------------------------------------------------------------------------------------------

module Ex-2-3 where

  import Data.Nat as N
  open import Data.Nat using (ℕ)

  data Tag : Set where nil' cons' : Tag

  S : (A : Set) → Sig zero {zero}{zero} N.ℕ (λ _ → ⊤)
  S A = σ Tag λ where
    nil'  → ι N.zero tt
    cons' → σ ℕ λ n → σ A λ _ → δ ⊤ (λ _ → n) λ _ → ι (N.suc n) tt

module Ex-2-4 where

  import Data.Nat as N
  open import Data.Nat using (ℕ)
  open Ex-2-3

  Vec : Set → ℕ → Set
  Vec A n = IIR (S A) n

  nil : ∀{A} → Vec A 0
  nil = intro (nil' , ↑ refl)

  cons : ∀{A} → (n : ℕ) → A → Vec A n → Vec A (N.suc n)
  cons n a as = intro (cons' , n , a , (λ _ → as) , ↑ refl)
