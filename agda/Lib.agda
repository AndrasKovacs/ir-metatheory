{-# OPTIONS --without-K #-}

module Lib where

open import Agda.Primitive public
open import Relation.Binary.PropositionalEquality
  renaming (cong to ap; trans to infixr 5 _◼_; sym to infix 6 _⁻¹; subst to tr)
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

apd : ∀ {i j}{A : Set i}{B : A → Set j}(f : ∀ a → B a){x y : A}(p : x ≡ y) → tr B p (f x) ≡ f y
apd f refl = refl

tr-∘ : ∀ {i j k}{A : Set i}{B : Set j} (P : B → Set k) (f : A → B) {a b : A} (p : a ≡ b) (x : P (f a))
       → _≡_ {k}{P (f b)} (tr P (ap f p) x) (tr (P ∘ f) p x)
tr-∘ P f refl x = refl

Σ≡ : ∀ {i j}{A : Set i}{B : A → Set j}{a₀ a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁)
     → _≡_ {A = Σ A B} (a₀ , b₀) (a₁ , b₁)
Σ≡ refl refl = refl

Σ≡₁ : ∀ {i j}{A : Set i}{B : A → Set j}{a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
        {b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁)
        → ap ₁ (Σ≡ a₂ b₂) ≡ a₂
Σ≡₁ refl refl = refl

tr-Σ : ∀ {i j k}{A : Set i}{B : A → Set j}{C : ∀ a → B a → Set k}
         {x y : A}(p : x ≡ y)(s : Σ (B x) (C x))
       → tr (λ x → Σ (B x) (C x)) p s ≡ (tr B p (s .₁) , tr (λ x → C (x .₁) (x .₂)) (Σ≡ p refl) (s .₂))
tr-Σ refl s = refl

tr-const : ∀ {i j}{A : Set i}{B : Set j}{x y : A}(p : x ≡ y)(b : B) → tr (λ _ → B) p b ≡ b
tr-const refl b = refl
