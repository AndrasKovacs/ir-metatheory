
module UniversalInd where

open import Lib renaming (fst to ₁; snd to ₂)
open import Data.Sum
open import Data.Empty
open import Data.Maybe


module M1 where

  data Sig : Set₁ where
    ι : Sig
    σ : (X : Set) → (X → Sig) → Sig
    δ : Set → Sig → Sig

  data Tag : Set where ι σ δ : Tag

  Path : Sig → Tag → Set
  Path ι       c = c ≡ ι
  Path (σ X S) c = c ≡ σ ⊎ ∃ λ x → Path (S x) c
  Path (δ X S) c = c ≡ δ ⊎ Path S c

  here : ∀ S → ∃ (Path S)
  here ι       = ι , refl
  here (σ _ _) = σ , inj₁ refl
  here (δ _ _) = δ , inj₁ refl

  projσ : ∀ {S} → Path S σ → Σ Set λ X → Σ (X → Sig) λ S' → ∀ x → Path S (here (S' x) .₁)
  projσ {σ X S} (inj₁ p)       = X , S , λ x → inj₂ (x , here (S x) .₂)
  projσ {σ X S} (inj₂ (x , p)) = (projσ p .₁) , (projσ p .₂ .₁) , λ x' → inj₂ (x , projσ p .₂ .₂ x')
  projσ {δ X S} (inj₂ p)       = projσ p .₁ , projσ p .₂ .₁ , inj₂ ∘ projσ p .₂ .₂

  projδ : ∀ {S} → Path S δ → Set × ∃ λ S' → Path S (here S' .₁)
  projδ {σ X S} (inj₂ (x , p)) = (projδ p .₁) , projδ p .₂ .₁ , inj₂ (x , projδ p .₂ .₂)
  projδ {δ X S} (inj₁ p) = X , S , inj₂ (here S .₂)
  projδ {δ X S} (inj₂ p) = projδ p .₁ , projδ p .₂ .₁ , inj₂ (projδ p .₂ .₂)

  -- data Sig≤ {S} : ∀ {c} → Path S c → Set where
  --   ι : ∀ {p} → Sig≤ {_}{ι} p
  --   σ : ∀ {p} → (∀ x → Sig≤ (projσ p .₂ .₂ x)) → Sig≤ {_}{σ} p
  --   δ : ∀ {p} → Sig≤ (projδ p .₂ .₂) → Sig≤ {_} {δ} p

  -- data Path' : Sig → Sig → Tag → Set₁ where
  --   ι : Path' ι ι ι
  --   σ : ∀ {X S} x → Path' (S x) c S' → Path' (σ S X) σ S'

  module _ {S : Sig} where

    data Tm : ∀ {c} → Path S c → Set where
      ι : ∀ {p} → Tm {ι} p
      σ : ∀ {p} x → Tm (projσ p .₂ .₂ x) → Tm {σ} p
      δ : ∀ {p} → (projδ p .₁ → Tm (here S .₂)) → Tm (projδ p .₂ .₂) → Tm {δ} p

    data Snoc : ∀ {c} → Path S c → Set where
      nil : ∀ {c p} → Snoc {c} p


    module Elim {k : Level} where

      Motive : ∀ {c} (p : Path S c) → Set (suc k)
      Motive p = Tm p → Set k

module M2 where

  data Tag : Set where ι σ δ : Tag

  private variable
     c c' : Tag

  data Sig : Tag → Set₁ where
    ι : Sig ι
    σ : (X : Set){c : X → Tag} → ((x : X) → Sig (c x)) → Sig σ
    δ : Set → Sig c → Sig δ

  Path  : ∀ {c} → Sig c → Tag → Set
  Path' : ∀ {c} → Sig c → Tag → Set
  Path {c} S c' = c ≡ c' ⊎ Path' S c'
  Path' ι       c' = ⊥
  Path' (σ X S) c' = ∃ λ x → Path (S x) c'
  Path' (δ X S) c' = Path S c'

  proj  : (S : Sig c) → Path  S c' → Sig c'
  proj' : (S : Sig c) → Path' S c' → Sig c'
  proj S (inj₁ refl) = S
  proj S (inj₂ p)    = proj' S p
  proj' (σ X S) (x , p) = proj (S x) p
  proj' (δ X S) p       = proj S p

  module _ {c}{S : Sig c} where

    data Tm : ∀ {c'} → Path S c' → Set where
      ι : ∀ {p} → Tm {ι} p
      σ : ∀ {p} x → {!proj _ p!} → Tm {σ} p
      -- δ : ∀ {p} → (projδ p .₁ → Tm (here S .₂)) → Tm (projδ p .₂ .₂) → Tm {δ} p

  --   data Snoc : ∀ {c} → Path S c → Set where
  --     nil : ∀ {c p} → Snoc {c} p


  --   module Elim {k : Level} where

  --     Motive : ∀ {c} (p : Path S c) → Set (suc k)
  --     Motive p = Tm p → Set k

  -- -- Path  : Sig → Tag → Set
  -- -- Path' : Sig → Tag → Set
  -- -- Path S c = tag S ≡ c ⊎ Path' S c
  -- -- Path' ι       c = ⊥
  -- -- Path' (σ X S) c = ∃ λ x → Path (S x) c
  -- -- Path' (δ X S) c = Path S c

  -- -- proj : ∀ {S c} → Path S c → Sig
  -- -- proj
