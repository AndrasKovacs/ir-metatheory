
module IRCanonicityExamples where

open import Lib
import PlainIR as IR
import IndexedIR as IIR
open import Data.Nat using (ℕ)
import Data.Nat as N

data ℕᵒ : ℕ → Set where
  zeroᵒ : ℕᵒ N.zero
  sucᵒ  : ∀ {n} → ℕᵒ n → ℕᵒ (N.suc n)

⊤₀ = ⊤{zero}

⊤ᵒ : ⊤₀ → Set
⊤ᵒ _ = ⊤₀

ttᵒ : ⊤ᵒ tt
ttᵒ = tt

module Example-4-1 where

  open IR.Example-2-1
  open IR.Example-2-2

  data Codeᵒ : Code → Set
  Elᵒ : ∀ {t} → Codeᵒ t → IR.El t → Set

  data Codeᵒ where
    mkℕ'ᵒ : Codeᵒ mkℕ'
    mkΠ'ᵒ : {A : Code}(Aᵒ : Codeᵒ A)
            {B : IR.El A → Code}(Bᵒ : ∀ {a : IR.El A} → Elᵒ Aᵒ a → Codeᵒ (B a))
          → Codeᵒ (mkΠ' A B)

  Elᵒ mkℕ'ᵒ             = ℕᵒ
  Elᵒ (mkΠ'ᵒ {A} Aᵒ Bᵒ) = λ f → ∀ {a : IR.El A}(aᵒ : Elᵒ Aᵒ a) → Elᵒ (Bᵒ aᵒ) (f a)

module Example-4-4 where
  open IR.Example-2-1 renaming (S to S*)
  import IRCanonicity zero (suc zero) Set as C

  data Tagᵒ : Tag → Set where
    ℕ'ᵒ : Tagᵒ ℕ'
    Π'ᵒ : Tagᵒ Π'

  infixr -1 _$ᵒ_
  _$ᵒ_ :
    ∀ {i j}
      {A : Set i} {Aᵒ : A → Set i}
      {B : A → Set j}{Bᵒ : ∀ {a} → Aᵒ a → B a → Set j}
      {f  : ∀ a → B a}
    → (∀ {a} aᵒ → Bᵒ aᵒ (f a))
    → (∀ {a} aᵒ → Bᵒ aᵒ (f a))
  _$ᵒ_ fᵒ aᵒ = fᵒ aᵒ

  S*ᵒ : C.Sigᵒ (λ A → A → Set) S*
  S*ᵒ = C.σᵒ Tagᵒ λ where
    ℕ'ᵒ → C.ιᵒ ℕᵒ
    Π'ᵒ → C.δᵒ ⊤ᵒ λ {ElA} ElAᵒ → C.δᵒ (ElAᵒ _ ttᵒ) λ {ElB} ElBᵒ →
          C.ιᵒ (λ f → ∀ {a : ElA tt}(aᵒ : ElAᵒ _ ttᵒ a) → ElBᵒ _ aᵒ (f a))

  ⌞S*ᵒ⌟here : IIR.Sig zero (IR.IR S*) (λ t → IR.El t → Set)
  ⌞S*ᵒ⌟here = IIR.σ Tag λ t → IIR.σ (Tagᵒ t) λ where
    ℕ'ᵒ → IIR.ι (IR.intro (ℕ' , tt)) ℕᵒ
    Π'ᵒ → IIR.σ (⊤₀ → IR.IR S*) λ A → IIR.δ (⊤₀ × ⊤₀) (A ∘ fst) λ ElAᵒ →
          IIR.σ (IR.El (A tt) → IR.IR S*) λ B → IIR.δ (Σ (IR.El (A tt)) (ElAᵒ (tt , ttᵒ))) (B ∘ fst) λ ElBᵒ →
          IIR.ι (IR.intro (Π' , A , B , tt)) (λ f → {a : IR.El (A tt)}(aᵒ : ElAᵒ (tt , ttᵒ) a) → ElBᵒ (a , aᵒ) (f a))


  -- Deriving Codeᵒ rules from (IIR ⌞S*ᵒ⌟here),
  -- to check that the definitions make sense

  open IR.Example-2-1
  open IR.Example-2-2

  Codeᵒ : Code → Set
  Codeᵒ = IIR.IIR ⌞S*ᵒ⌟here

  Elᵒ : ∀ {t} → Codeᵒ t → IR.El t → Set
  Elᵒ = IIR.El

  mkℕ'ᵒ : Codeᵒ mkℕ'
  mkℕ'ᵒ = IIR.intro (ℕ' , ℕ'ᵒ , ↑ refl)

  mkΠ'ᵒ :
    {A : Code}(Aᵒ : Codeᵒ A)
    {B : IR.El A → Code}(Bᵒ : ∀ {a : IR.El A} → Elᵒ Aᵒ a → Codeᵒ (B a))
    → Codeᵒ (mkΠ' A B)
  mkΠ'ᵒ {A} Aᵒ {B} Bᵒ = IIR.intro (Π' , Π'ᵒ , (λ _ → A) , (λ _ → Aᵒ) , B , (λ {(a , aᵒ) → Bᵒ aᵒ}) , ↑ refl)

  Elᵒmkℕ'ᵒ : Elᵒ mkℕ'ᵒ ≡ ℕᵒ
  Elᵒmkℕ'ᵒ = refl

  ElᵒmkΠ'ᵒ :
    {A : Code}(Aᵒ : Codeᵒ A)
    {B : IR.El A → Code}(Bᵒ : ∀ {a : IR.El A} → Elᵒ Aᵒ a → Codeᵒ (B a))
    → Elᵒ (mkΠ'ᵒ Aᵒ Bᵒ) ≡ (λ f → ∀ {a}(aᵒ : Elᵒ Aᵒ a) → Elᵒ (Bᵒ aᵒ) (f a))
  ElᵒmkΠ'ᵒ Aᵒ Bᵒ = refl



--------------------------------------------------------------------------------
