{-# OPTIONS --without-K --rewriting #-}

module CodeCircExample where

open import Lib
open import IndexedIR

----------------------------------------------------------------------------------------------------

{-
Specifying the signature, deriving constructors & eliminator for Codeᴼ as an IIR type.

We use a representation of the object syntax that's somewhat less shallow than what's
used in IRCanonicity: we postulate concrete object-level term and type formers, although we
still use Set i for object types and universes.
-}

Ty : ∀ i → Set (suc i)
Ty i = Set i

Tm : ∀ {i} → Ty i → Set i
Tm A = A

U : ∀ i → Set (suc i)
U = Ty

U₀ = U zero

postulate
  -- Object-level functions
  Π   : ∀ {i j} → Tm ((A : U i) → (A → U j) → U (i ⊔ j))
  _∙_ : ∀ {i j A B} → Tm (Π {i}{j} A B) → (a : Tm A) → Tm (B a) -- infix application

infixl 8 _∙_
infixr 4 _⇒_

_⇒_ : ∀ {i j} → Ty i → Ty j → Ty (i ⊔ j)
A ⇒ B = Π A λ _ → B

postulate
  -- Object-level natural numbers
  Nat     : Tm U₀
  nzero   : Tm Nat
  nsuc    : Tm (Nat ⇒ Nat)

  -- Object-level Code
  Code    : Tm U₀
  ElC     : Tm (Code ⇒ U₀)
  Nat'    : Tm Code
  Π'      : Tm (Π Code λ A → (ElC ∙ A ⇒ Code) ⇒ Code)
  ElCNat' : ElC ∙ Nat' ≡ Nat
  ElCΠ'   : ∀ {A B} → ElC ∙ (Π' ∙ A ∙ B) ≡ (Π (ElC ∙ A) λ a → ElC ∙ (B ∙ a))

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE ElCNat' ElCΠ' #-}

data Tagᵒ : Set where
  Nat'ᵒtag : Tagᵒ
  Π'ᵒtag   : Tagᵒ

data Natᵒ : Tm Nat → Set where
  zeroᵒ : Natᵒ nzero
  sucᵒ  : ∀ {n} → Natᵒ n → Natᵒ (nsuc ∙ n)

-- The signature for Codeᵒ
S : Sig zero (Tm Code) (λ t → Tm (ElC ∙ t) → Set₀)
S = σ Tagᵒ λ where
  Nat'ᵒtag → ι Nat' Natᵒ
  Π'ᵒtag   → σ (Tm Code) λ A             → δ ⊤ (λ _ → A) λ Aᵒ →
             σ (Tm (ElC ∙ A ⇒ Code)) λ B → δ (Σ (Tm (ElC ∙ A)) (Aᵒ tt)) ((B ∙_) ∘ fst) λ Bᵒ →
             ι (Π' ∙ A ∙ B) λ f → {a : Tm (ElC ∙ A)}(aᵒ : Aᵒ tt a) → Bᵒ (a , aᵒ) (f ∙ a)


-- Deriving Agda-style constructors, eliminator and computation rules
----------------------------------------------------------------------------------------------------

Codeᵒ : Tm Code → Set₀
Codeᵒ = IIR S

Elᵒ : ∀ {t} → Codeᵒ t → (Tm (ElC ∙ t) → Set₀)
Elᵒ = El

-- constructors
Nat'ᵒ : Codeᵒ Nat'
Nat'ᵒ = intro (Nat'ᵒtag , ↑ refl)

Π'ᵒ : {A : Tm Code}(Aᵒ : Codeᵒ A){B : Tm (ElC ∙ A ⇒ Code)}(Bᵒ : {a : Tm (ElC ∙ A)} → Elᵒ Aᵒ a → Codeᵒ (B ∙ a))
        → Codeᵒ (Π' ∙ A ∙ B)
Π'ᵒ {A} Aᵒ {B} Bᵒ = intro (Π'ᵒtag , A , (λ _ → Aᵒ) , B , (λ {(_ , aᵒ) → Bᵒ aᵒ}) , ↑ refl)

-- El computation
ElᵒNat'ᵒ : Elᵒ Nat'ᵒ ≡ Natᵒ
ElᵒNat'ᵒ = refl

ElᵒΠ'ᵒ : {A : Tm Code}(Aᵒ : Codeᵒ A){B : Tm (ElC ∙ A ⇒ Code)}(Bᵒ : {a : Tm (ElC ∙ A)} → Elᵒ Aᵒ a → Codeᵒ (B ∙ a))
         → Elᵒ (Π'ᵒ {A} Aᵒ {B} Bᵒ) ≡ (λ f → {a : Tm (ElC ∙ A)}(aᵒ : Elᵒ Aᵒ a) → Elᵒ (Bᵒ aᵒ) (f ∙ a))
ElᵒΠ'ᵒ Aᵒ Bᵒ = refl

-- eliminator
CodeᵒElim :
  ∀ {i}
    (P : {t : Tm Code} → Codeᵒ t → Set i)
  → P Nat'ᵒ
  → (   {A : Tm Code}(Aᵒ : Codeᵒ A)
      → P Aᵒ
      → {B : Tm (ElC ∙ A ⇒ Code)}(Bᵒ : {a : Tm (ElC ∙ A)} → Elᵒ Aᵒ a → Codeᵒ (B ∙ a))
      → (∀ {a : Tm (ElC ∙ A)} (aᵒ : Elᵒ Aᵒ a) → P (Bᵒ aᵒ))
      → P (Π'ᵒ Aᵒ Bᵒ))
  → {t : Tm Code}(tᵒ : Codeᵒ t) → P tᵒ
CodeᵒElim P PNat'ᵒ PΠ'ᵒ = elim {S = S} P λ where
  (Nat'ᵒtag , ↑ refl)                 tt               → PNat'ᵒ
  (Π'ᵒtag , A , Aᵒ , B , Bᵒ , ↑ refl) (PAᵒ , PBᵒ , tt) → PΠ'ᵒ (Aᵒ tt) (PAᵒ tt) (λ {a} aᵒ → Bᵒ (a , aᵒ)) (λ {a} aᵒ → PBᵒ (a , aᵒ))

module β-rules i (P : {t : Tm Code} → Codeᵒ t → Set i)
                 (PNat'ᵒ : P Nat'ᵒ)
                 (PΠ'ᵒ   : {A : Tm Code}(Aᵒ : Codeᵒ A)
                        → P Aᵒ
                        → {B : Tm (ElC ∙ A ⇒ Code)}(Bᵒ : {a : Tm (ElC ∙ A)} → Elᵒ Aᵒ a → Codeᵒ (B ∙ a))
                        → (∀ {a : Tm (ElC ∙ A)} (aᵒ : Elᵒ Aᵒ a) → P (Bᵒ aᵒ))
                        → P (Π'ᵒ Aᵒ Bᵒ)) where

  Nat'ᵒ-β : CodeᵒElim P PNat'ᵒ PΠ'ᵒ Nat'ᵒ ≡ PNat'ᵒ
  Nat'ᵒ-β = refl

  Π'ᵒ-β : {A : Tm Code}(Aᵒ : Codeᵒ A){B : Tm (ElC ∙ A ⇒ Code)}(Bᵒ : {a : Tm (ElC ∙ A)} → Elᵒ Aᵒ a → Codeᵒ (B ∙ a))
        → CodeᵒElim P PNat'ᵒ PΠ'ᵒ (Π'ᵒ Aᵒ Bᵒ) ≡
             PΠ'ᵒ Aᵒ (CodeᵒElim P PNat'ᵒ PΠ'ᵒ Aᵒ)
                  Bᵒ (λ {a} aᵒ → CodeᵒElim P PNat'ᵒ PΠ'ᵒ (Bᵒ aᵒ))
  Π'ᵒ-β Aᵒ Bᵒ = refl
