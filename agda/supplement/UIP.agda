{-# OPTIONS --safe #-}

module UIP where

open import Lib

UIP : ∀ {i}{A : Set i}{x y : A}{p q : x ≡ y} → p ≡ q
UIP {p = refl}{refl} = refl

coe-UIP : ∀ {i}{A B : Set i}(p q : A ≡ B){x : A}
          → coe p x ≡ coe q x
coe-UIP refl refl = refl
