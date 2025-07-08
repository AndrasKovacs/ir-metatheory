
module NestedIR where

open import Lib renaming (fst to ₁; snd to ₂)
open import Data.Sum


module Foo (i j : Level)(O : Set j) where

  -- data Sort : Set (suc i ⊔ j)
  -- ElS : Sort → Set (i ⊔ j)

  -- data Sort where
  --   σ    : (a : Sort) → (b : ElS a → Sort) → Sort
  --   π    : (A : Set i) → (b : A → Sort) → Sort
  --   K    : (A : Set i) → Sort
  --   ind  : Sort

  -- ElS (K A)   = Lift (i ⊔ j) A
  -- ElS (σ a b) = Σ (ElS a) (ElS ∘ b)
  -- ElS (π A b) = (x : A) → ElS (b x)
  -- ElS ind     = Lift (i ⊔ j) O

  -- data Sig : Set (suc i ⊔ j) where
  --   ι : (o : O) → Sig
  --   π : (a : Sort) → (S : ElS a → Sig) → Sig

  -- ES : Sort → (ir : Set i) → (ir → O) → Set i
  -- ElES : ∀ S → (ir : Set i) → (el : ir → O) → ES S ir el → ElS S
  -- ES (σ a b) ir el = Σ (ES a ir el) λ x → ES (b (ElES a ir el x)) ir el
  -- ES (π A b) ir el = (a : A) → ES (b a) ir el
  -- ES (K A) ir el = A
  -- ES ind ir el = ir
  -- ElES (σ S b) ir el (x , y) = (ElES S ir el x) , ElES _ ir el y
  -- ElES (π A b) ir el x = λ a → ElES (b a) ir el (x a)
  -- ElES (K A) ir el x = ↑ x
  -- ElES ind   ir el x = ↑ (el x)

  -- E : Sig → (ir : Set i) → (ir → O) → Set i
  -- E (ι o) ir el = ⊤
  -- E (π a S) ir el = Σ (ES a ir el) λ x → E (S (ElES a ir el x)) ir el

  -- F : ∀ {S} → (ir : Set i) → (el : ir → O) → E S ir el → O
  -- F {ι o}   ir el x       = o
  -- F {π a S} ir el (x , y) = F {S (ElES a ir el x)} ir el y


  -- data IR (S : Sig) : Set i
  -- El : ∀ {S} → IR S → O

  -- data IR S where
  --   intro : E S (IR S) El → IR S

  -- {-# TERMINATING #-}
  -- El {S} (intro x) = F {S} (IR S) El x

--------------------------------------------------------------------------------

-- Descriptions of IR types are an IR type!!!!

  data Sig : Set (suc i ⊔ j)
  El : Sig → Set (i ⊔ j)

  data Sig where
    Σ'   : (A : Sig) → (B : El A → Sig) → Sig
    Π'   : (A : Set) → (B : A → Sig) → Sig
    <_>  : (A : Set i) → Sig
    O'   : Sig

  El (Σ' A B) = Σ (El A) (El ∘ B)
  El (Π' A B) = (a : A) → El (B a)
  El < A >    = Lift (i ⊔ j) A
  El O'       = Lift (i ⊔ j) O

  E : (S : Sig) → (ir : Set i) → (ir → O) → Σ (Set i) λ X → X → El S
  E (Σ' A B) ir el = Σ (E A ir el .₁) (λ a → E (B (E A ir el .₂ a)) ir el .₁) , λ where
                       (a , b) → (E A ir el .₂ a) , E (B (E A ir el .₂ a)) ir el .₂ b
  E (Π' A B) ir el = ((a : A) → E (B a) ir el .₁) , λ f a → E (B a) ir el .₂ (f a)
  E < A >    ir el = A , ↑
  E O'       ir el = ir , ↑ ∘ el

--------------------------------------------------------------------------------

  data IR (S : Sig)(o : El S → O) : Set i
  ElIR : ∀ {S o} → IR S o → O

  {-# NO_POSITIVITY_CHECK #-}
  data IR S o where
    intro : E S (IR S o) ElIR .₁ → IR S o

  {-# TERMINATING #-}
  ElIR {S}{o} (intro x) = o (E S (IR S o) ElIR .₂ x)

-- LEVITATIONSSS
module Bar (i j : Level)(O : Set j) where

  -- size bump of signatures!
  data Sig : Set (i ⊔ j) → Set (suc (i ⊔ j)) where
    Σ'  : ∀ {A : Set (i ⊔ j)}(a : Sig A){B : A → Set (i ⊔ j)} → (∀ x → Sig (B x)) → Sig (Σ A B)
    Π'  : ∀ (A : Set i){B : A → Set (i ⊔ j)} → (∀ x → Sig (B x)) → Sig (∀ x → B x)
    <_> : (A : Set i) → Sig (Lift (i ⊔ j) A)
    O'  : Sig (Lift (i ⊔ j) O)

  E : ∀ {A} → Sig A → (ir : Set i)(el : ir → O) → Σ (Set i) λ X → X → A
  E {_} (Σ' A B) ir el = Σ (E A ir el .₁) (λ x → E (B _) ir el .₁) , λ where
                           (a , b) → (E A ir el .₂ a) , (E (B _) ir el .₂ b)
  E {_} (Π' A B) ir el = (∀ x → E (B x) ir el .₁) , λ f a → E (B a) ir el .₂ (f a)
  E {_} < A >    ir el = A , ↑
  E {_} O'       ir el = ir , ↑ ∘ el

  data IR {A}(S : Sig A)(o : A → O) : Set i
  El : ∀ {A S o} → IR {A} S o → O

  {-# NO_POSITIVITY_CHECK #-}
  data IR {A} S o where
    intro : E S (IR S o) El .₁ → IR S o

  {-# TERMINATING #-}
  El {A}{S}{o} (intro x) = o (E S (IR S o) El .₂ x)


  -- module Brekk {A}(S : Sig A)(o : A → O) where

  --    E' : ∀ {A} → Sig A → Σ (Sig A) λ S' → {!!}
  --    E' {A} S = {!!}













--------------------------------------------------------------------------------

  -- data Sig' : Set (suc i ⊔ j) where
  --   ι : O → Sig'
  --   σ : (A : Set i) → (A → Sig') → Sig'
  --   δ : (A : Set i) → ((A → O) → Sig') → Sig'

  -- E : Sig' → Sort
  -- E (ι _  ) = K ⊤
  -- E (σ A S) = σ (K A) (E ∘ S ∘ ↓)
  -- E (δ A S) = σ (π A λ _ → ind) λ f → E (S (↓ ∘ f))

  -- F : ∀ {S} → ElS (E S) → O
  -- F {ι o}   x       = o
  -- F {σ _ _} (_ , x) = F x
  -- F {δ _ _} (_ , x) = F x


  -- irsig : Sig' → Sig
  -- irsig S = π (E S) (ι ∘ F)

-- --------------------------------------------------------------------------------

-- data Sig' : Set₁ where
--   ι : Set → Sig'
--   σ : (A : Set) → (S : A → Sig') → Sig'
--   δ : (A : Set) → (S : (A → Set) → Sig') → Sig'

-- E : Sig' → Sort
-- E (ι _  ) = K ⊤
-- E (σ A S) = σ (K A) (E ∘ S ∘ ↓)
-- E (δ A S) = σ (π A λ _ → ind) (E ∘ S)

-- F : (S : Sig') → ⟦ E S ⟧ → Set
-- F (ι o)   x       = o
-- F (σ A S) (a , x) = F _ x
-- F (δ A S) (f , x) = F _ x

-- irsig : Sig' → Sig
-- irsig S = π (E S) (λ x → ι (F S x))



-- E : Sig' → (ir : Set) → (ir → Set) → Sort
-- E (ι _  ) ir el = unit -- ⊤
-- E (σ A S) ir el = σ A λ a → E (S a) ir el
-- E (δ A S) ir el = σ {!!} {!!} -- Σ (A → ir) λ f → E (S (el ∘ f)) ir el

-- F : ∀ {S : Sig'}{ir el} → E S ir el → Set
-- F {S = ι o  }        x       = o
-- F {S = σ A S}        (a , x) = F {S = S a} x
-- F {S = δ A S}{ir}{el}(f , x) = F {S = S (el ∘ f)} x

-- IH : ∀ {S} {ir : Set} {el : ir → Set} (P : ir → Set k) → E S ir el → Set (i ⊔ k)
-- IH {S = ι o  }          P x       = ⊤
-- IH {S = σ A S}          P (a , x) = IH {S = S a} P x
-- IH {S = δ A S} {ir}{el} P (f , x) = (∀ a → P (f a)) × IH {S = S (el ∘ f)} P x

-- map : ∀ {S} {ir : Set}{el : ir → Set}{P : ir → Set k} → (∀ x → P x) → (x : E S ir el) → IH P x
-- map {S = ι o  }          h x       = tt
-- map {S = σ A S}          h (a , x) = map {S = S a} h x
-- map {S = δ A S} {ir}{el} h (f , x) = (h ∘ f , map {S = S (el ∘ f)} h x)

-- data IR (S : Sig i Set) : Set
-- El : {S : Sig i Set} → IR S → Set

-- data IR S where
--   intro : E S (IR S) El → IR S
