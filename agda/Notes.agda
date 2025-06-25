
module Notes where

open import Relation.Binary.PropositionalEquality

record ⊤ {i} : Set i where
  constructor tt

data Bool : Set where true false : Bool

BoolElim : ∀ {i}(P : Bool → Set i) → P true → P false → ∀ b → P b
BoolElim P t f true = t
BoolElim P t f false = f

⊥ : Set
⊥ = true ≡ false

exfalso : ∀{i}(A : Set i) → ⊥ → A
exfalso A p = subst {A = Bool} (BoolElim _ ⊤ A) p tt
