
module Lib where

open import Agda.Primitive public
open import Relation.Binary.PropositionalEquality
  renaming (cong to ap; trans to infixr 5 _◼_; sym to infix 5 _⁻¹; subst to tr)
  public
open import Data.Product hiding (map) renaming (proj₁ to ₁; proj₂ to ₂)
  public
open import Data.Unit
  public
open import Level using (Lift; lift; lower)
  public
open import Function
  public

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe refl x = x
