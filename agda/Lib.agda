{-# OPTIONS --without-K --allow-unsolved-metas #-}

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

tr-Σ₁ : ∀ {i j k}{A : Set i}{B : A → Set j}{C : ∀ a → B a → Set k}
         {x y : A}(p : x ≡ y)(s : Σ (B x) (C x))
       → tr (λ x → Σ (B x) (C x)) p s .₁ ≡ tr B p (s .₁)
tr-Σ₁ refl s = refl

tr-×₁ : ∀ {i j k}{A : Set i}{B : A → Set j}{C : A → Set k}
         {x y : A}(p : x ≡ y)(s : B x × C x)
       → tr (λ x → B x × C x) p s .₁ ≡ tr B p (s .₁)
tr-×₁ refl s = refl

tr-×₂ : ∀ {i j k}{A : Set i}{B : A → Set j}{C : A → Set k}
         {x y : A}(p : x ≡ y)(s : B x × C x)
       → tr (λ x → B x × C x) p s .₂ ≡ tr C p (s .₂)
tr-×₂ refl s = refl

tr-const : ∀ {i j}{A : Set i}{B : Set j}{x y : A}(p : x ≡ y)(b : B) → tr (λ _ → B) p b ≡ b
tr-const refl b = refl

the : ∀ {i}(A : Set i) → A → A
the A x = x

tr-app-lem :
   ∀ {i j k}{A : Set i}{B : A → Set j}{C : A → Set k}
     (f : ∀ a → B a → C a)
     {a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
     {b₀ : B a₀}
   → tr C a₂ (f a₀ b₀) ≡ f a₁ (tr B a₂ b₀)
tr-app-lem f refl = refl

tr-app-lem2 :
  ∀ {i j k l}{A : Set i}{B : A → Set j}
    {C : A → Set k}{D : ∀ a → B a → C a → Set j}
    {E : ∀ a → B a → C a → Set l}
    (f : ∀ a (b : B a)(c : C a) → D a b c → E a b c)
  → {!!}
tr-app-lem2 = {!!}



-- -- Pᴾ : {x = x₁ : U} → Uᴾ x₁ → P x₁ → Set j

-- (metᴾ : ∀ {x}(xᴾ : F0ᴾ S*ᴾ x)
--    {ih : IH S* x}(ihᴾ : IHᴾ S*ᴾ xᴾ ih) → Pᴾ {IR.wrap x} (wrapᴾ xᴾ) (met x ih)) where
