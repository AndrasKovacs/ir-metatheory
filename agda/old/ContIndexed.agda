{-# OPTIONS --rewriting #-}

module old.ContIndexed where

open import Lib

{-# BUILTIN REWRITE _≡_ #-}

module Mod {le lo : Level}(O : Set lo) where

  record Sig : Set (lsuc le ⊔ lo) where
    constructor sig
    field
      Sh : O → Set le
      Ps : ∀ o → Sh o → Set le
      Ix : ∀ o (s : Sh o) → Ps o s → O
  open Sig public

  F : Sig → (u : Set le) → (u → O) → Σ (Set (le ⊔ lo)) λ X → X → O
  F (sig Sh Ps Ix) u el .₁ = Σ O λ o → Σ (Sh o) λ s → (p : Ps o s) → Σ u λ x → el x ≡ Ix o s p
  F (sig Sh Ps Ix) u el .₂ (o , _) = o

  module _ {j}(u : Set le)(el : u → O)(P : u → Set j) where

    IH : (S : Sig) → F S u el .₁ → Set (le ⊔ j)
    IH (sig Sh Ps Ix) (o , s , chd) = (p : Ps o s) → P (chd p .₁)

    mapIH : (S : Sig)(x : F S u el .₁)(f : ∀ x → P x) → IH S x
    mapIH (sig Sh Ps Ix) (o , s , chd) f p = f (chd p .₁)

  --------------------------------------------------------------------------------

  postulate
    U      : Sig → Set le
    El     : ∀ S → U S → O
    wrap   : ∀ {S} → F S (U S) (El S) .₁ → U S
    El≡    : ∀ {S}{x : F S (U S) (El S) .₁} → El S (wrap x) ≡ F S (U S) (El S) .₂ x
    elim   : ∀ {j} S (P : U S → Set j) → (∀ x → IH (U S) (El S) P S x → P (wrap x)) → ∀ x → P x
    elim≡  : ∀ {j S P met x} → elim {j} S P met (wrap x) ≡ met x (mapIH (U S) (El S) P S x (elim S P met))
  {-# REWRITE El≡ elim≡ #-}

  unwrap : ∀ {S} → U S → F S (U S) (El S) .₁
  unwrap {S} = elim S _ λ x hyp → x


open Mod {lzero}{lsuc lzero} Set
open import Data.Empty

S* : Sig
S* .Mod.Sh _ = ⊤
S* .Mod.Ps _ _ = ⊥
S* .Mod.Ix _ _ _ = ⊥

pack : Set → U S*
pack X = wrap (X , tt , ⊥-elim)

unpack : U S* → Set
unpack X = unwrap X .₁

lr : ∀ X → pack (unpack X) ≡ X
lr = elim S* (λ X → pack (unpack X) ≡ X)
          (λ x ih → ap wrap {!!}) -- OK

rl : ∀ {X} → unpack (pack X) ≡ X
rl {X} = refl

-- NOT GOOD, because U S* is in Set₀, but Set₀ ≃ U S*

--------------------------------------------------------------------------------
