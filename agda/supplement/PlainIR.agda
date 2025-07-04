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

E : Sig i O → (ir : Set i) → (ir → O) → Set i
E (ι _  ) ir el = ⊤
E (σ A S) ir el = Σ A λ a → E (S a) ir el
E (δ A S) ir el = Σ (A → ir) λ f → E (S (el ∘ f)) ir el

F : ∀ {S : Sig i O}{ir el} → E S ir el → O
F {S = ι o  }        x       = o
F {S = σ A S}        (a , x) = F {S = S a} x
F {S = δ A S}{ir}{el}(f , x) = F {S = S (el ∘ f)} x

IH : ∀ {S} {ir : Set i} {el : ir → O} (P : ir → Set k) → E S ir el → Set (i ⊔ k)
IH {S = ι o  }          P x       = ⊤
IH {S = σ A S}          P (a , x) = IH {S = S a} P x
IH {S = δ A S} {ir}{el} P (f , x) = (∀ a → P (f a)) × IH {S = S (el ∘ f)} P x

map : ∀ {S} {ir : Set i}{el : ir → O}{P : ir → Set k} → (∀ x → P x) → (x : E S ir el) → IH P x
map {S = ι o  }          h x       = tt
map {S = σ A S}          h (a , x) = map {S = S a} h x
map {S = δ A S} {ir}{el} h (f , x) = (h ∘ f , map {S = S (el ∘ f)} h x)

data IR (S : Sig i O) : Set i
El : {S : Sig i O} → IR S → O

data IR S where
  intro : E S (IR S) El → IR S

{-# TERMINATING #-}
El {S = S} (intro t) = F t

{-# TERMINATING #-}
elim : {S : Sig i O} (P : IR S → Set k) → (∀ x → IH P x → P (intro x)) → ∀ x → P x
elim P f (intro x) = f x (map (elim P f) x)

--------------------------------------------------------------------------------

outro : {S : Sig i O} → IR S → E S (IR S) El
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
