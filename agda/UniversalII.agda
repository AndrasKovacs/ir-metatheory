{-# OPTIONS --without-K #-}

open import Lib renaming (fst to ₁; snd to ₂)

open import Data.Maybe
open import Data.Empty

module UniversalII where

 module V1 (i j : Level) (O : Set j) where

  data Sig : Set (suc i ⊔ j) where
    ι : O → Sig
    σ : (X : Set i) → (S : X → Sig) → Sig
    δ : (X : Set i) → (S : (X → O) → Sig) → Sig

  module _ (S* : Sig) where

     Path    : Sig → Set i

     data Tm : Maybe (Path S*) → Set i
     El      : ∀ {p} → Tm p → O

     Path (ι o)   = Lift _ ⊥
     Path (σ X S) = (Σ X λ x → Maybe (Path (S x)))
     Path (δ X S) = (Σ (X → Tm nothing) λ f → Maybe (Path (S λ x → El (f x))))

     isι     : ∀ {S} → Maybe (Path S) → Set i
     isι {ι o  } nothing        = ⊤
     isι {σ X S} (just (_ , p)) = isι p
     isι {σ X S} nothing        = Lift _ ⊥
     isι {δ X S} (just (_ , p)) = isι p
     isι {δ X S} nothing        = Lift _ ⊥

     projι : ∀ {S}(p : Maybe (Path S)) → isι p → O
     projι {ι o}   nothing        q = o
     projι {σ X S} (just (_ , p)) q = projι p q
     projι {δ X S} (just (_ , p)) q = projι p q

     isσ     : ∀ {S} → Maybe (Path S) → Set i
     isσ {ι x  } p = Lift _ ⊥
     isσ {σ X S} (just (_ , p)) = isσ p
     isσ {σ X S} nothing = ⊤
     isσ {δ X S} (just (_ , p)) = isσ p
     isσ {δ X S} nothing = Lift _ ⊥

     projσ : ∀ {S}(p : Maybe (Path S)) → isσ p → Σ (Set i) λ P → P → Path S
     projσ {σ X S} (just (y , p)) q = projσ p q .₁ , λ x → y , just (projσ p q .₂ x)
     projσ {σ X S} nothing        q = X , λ x → x , nothing
     projσ {δ X S} (just (y , p)) q = projσ p q .₁ , λ x → y , just (projσ p q .₂ x)

     isδ     : ∀ {S} → Maybe (Path S) → Set i
     isδ {ι x  } p = Lift _ ⊥
     isδ {σ X S} (just (_ , p)) = isδ p
     isδ {σ X S} nothing = Lift _ ⊥
     isδ {δ X S} (just (_ , p)) = isδ p
     isδ {δ X S} nothing = ⊤

     projδ : ∀ {S}(p : Maybe (Path S)) → isδ p → Σ (Set i) λ P → (P → Tm nothing) → Path S
     projδ {σ X S} (just (y , p)) q = projδ p q .₁ , λ x → y , just (projδ p q .₂ x)
     projδ {δ X S} (just (y , p)) q = projδ p q .₁ , λ x → y , just (projδ p q .₂ x)
     projδ {δ X S} nothing        q = X , λ x → x , nothing

     data Tm where
       ι : (p : Maybe (Path S*)) → isι p → Tm p
       σ : (p : Maybe (Path S*))(q : isσ p)(x : projσ p q .₁) → Tm (just (projσ p q .₂ x)) → Tm p
       δ : (p : Maybe (Path S*))(q : isδ p)(f : projδ p q .₁ → Tm nothing) → Tm (just (projδ p q .₂ f)) → Tm p

     El (ι p q)     = projι p q
     El (σ _ _ _ t) = El t
     El (δ _ _ _ t) = El t

 -- module V2 (i j : Level) (O : Set j) where

 --  data Sig : Set (suc i ⊔ j) where
 --    ι : O → Sig
 --    σ : (X : Set i) → (S : X → Sig) → Sig
 --    δ : (X : Set i) → (S : (X → O) → Sig) → Sig

 --  module Path (tm : Set i) (el : tm → O) where

 --    Ty : Sig → O
 --    Ty (ι x)   = {!!}
 --    Ty (σ X S) = {!!}
 --    Ty (δ X S) = {!!}
