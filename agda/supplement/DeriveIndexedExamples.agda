{-# OPTIONS --without-K #-}

module DeriveIndexedExamples where

open import Lib
import Data.Nat as N

-- Section 3.3
--------------------------------------------------------------------------------

module VecExample {i}(A : Set i) where

  open import DeriveIndexed {i} N.ℕ (const (⊤{zero}))

  data Tag : Set i where Nil Cons : Tag

  S : Sig
  S = σ Tag λ where
    Nil  → ι N.zero tt
    Cons → σ (Lift _ N.ℕ) λ n →
           σ A λ _ →
           δ (Lift zero ⊤) (const (↓ n)) λ _ →
           ι (N.suc (↓ n)) tt

  Vec : N.ℕ → Set i
  Vec = IIR S

  nil : Vec 0
  nil = intro S (Nil , ↑ refl)

  cons : ∀ {n} → A → Vec n → Vec (N.suc n)
  cons {n} a as = intro S (Cons , ↑ n , a , (λ _ → as) , ↑ refl)

  VecElim : ∀ {l}(P : ∀ {n} → Vec n → Set l) → P nil → (∀ {n a as} → P {n} as → P (cons a as))
            → ∀ {n} as → P {n} as
  VecElim P nl cs = elim S P λ where
    (Nil  , ↑ refl) ih → nl
    (Cons , _ , a , as , ↑ refl) ih → cs (ih .fst (↑ tt))

  ElimNil : ∀ {l}(P : ∀ {n} → Vec n → Set l)(nl : P nil)(cs : ∀ {n a as} → P {n} as → P (cons a as))
            → VecElim P nl cs nil ≡ nl
  ElimNil P nl cs = refl

  ElimCons : ∀ {l}(P : ∀ {n} → Vec n → Set l)(nl : P nil)(cs : ∀ {n a as} → P {n} as → P (cons a as))
            → ∀ {n a as} → VecElim P nl cs (cons {n} a as) ≡ cs (VecElim P nl cs as)
  ElimCons P nl cs = refl

module CodeExample where

  import DeriveIndexed {zero} (⊤{zero}) (const Set) as IIR

  data Tag : Set where ℕ' Π' : Tag

  S : IIR.Sig
  S = IIR.σ Tag λ where
    ℕ' → IIR.ι tt N.ℕ
    Π' → IIR.δ ⊤ _ λ ElA → IIR.δ (ElA tt) _ λ ElB → IIR.ι _ ((a : ElA tt) → ElB a)

  Code : Set
  Code = IIR.IIR S tt

  El : Code → Set
  El = IIR.El S

  n' : Code
  n' = IIR.intro S (ℕ' , ↑ refl)

  π' : (A : Code) → (El A → Code) → Code
  π' A B = IIR.intro S (Π' , const A , B , ↑ refl)

  Eln' : El n' ≡ N.ℕ
  Eln' = refl

  Elπ' : ∀ {A B} → El (π' A B) ≡ ((a : El A) → El (B a))
  Elπ' = refl

  CodeElim : ∀ {i} (P : Code → Set i)(np : P n')(πp : ∀ {A} → P A → ∀ {B} → (∀ a → P (B a)) → P (π' A B)) → ∀ A → P A
  CodeElim P np πp = IIR.elim S P λ where
    (ℕ' , ↑ refl) _                     → np
    (Π' , A , B , ↑ refl) (Ap , Bp , _) → πp (Ap tt) Bp

  CodeElimn' : ∀ {i} (P : Code → Set i)(np : P n')(πp : ∀ {A} → P A → ∀ {B} → (∀ a → P (B a)) → P (π' A B)) → CodeElim P np πp n' ≡ np
  CodeElimn' P np πp = refl

  CodeElimπ' : ∀ {i} (P : Code → Set i)(np : P n')(πp : ∀ {A} → P A → ∀ {B} → (∀ a → P (B a)) → P (π' A B))
            → ∀ {A B} → CodeElim P np πp (π' A B) ≡ πp (CodeElim P np πp A) (CodeElim P np πp ∘ B )
  CodeElimπ' P np πp = refl

--------------------------------------------------------------------------------
