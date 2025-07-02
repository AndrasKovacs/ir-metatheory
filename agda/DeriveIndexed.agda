{-# OPTIONS --without-K #-}

open import Lib


-- Section 3
--------------------------------------------------------------------------------

module DeriveIndexed {i j k : Level}(I : Set k)(O : I → Set j) where

data Sig : Set (suc i ⊔ j ⊔ k) where
  ι : ∀ i → O i → Sig
  σ : (A : Set i) → (A → Sig) → Sig
  δ : (A : Set i)(f : A → I) → ((∀ a → O (f a)) → Sig) → Sig

_₀ : Sig → (ir : I → Set (i ⊔ k)) → (∀ {ix} → ir ix → O ix) → I → Set (i ⊔ k)
_₀ (ι ix' o  ) ir el ix = Lift (i ⊔ k) (ix' ≡ ix)
_₀ (σ A S    ) ir el ix = Σ A λ a → (S a ₀) ir el ix
_₀ (δ A ix' S) ir el ix = Σ (∀ a → ir (ix' a)) λ f → (S (el ∘ f)₀) ir el ix

_₁ : ∀ S {ir : I → Set (i ⊔ k)}{el : ∀ {i} → ir i → O i} → ∀ {ix} → _₀ S ir el ix → O ix
_₁ (ι ix o)            (↑ x)   = tr O x o
_₁ (σ A S)             (a , x) = (S a ₁) x
_₁ (δ A ix S) {ir}{el} (f , x) = (S (el ∘ f)₁) x

_ᵢₕ : ∀ S {ir : I → Set (i ⊔ k)}{el : ∀{ix} → ir ix → O ix}
        (P : ∀ {ix} → ir ix → Set l) → ∀ {ix} → (S ₀) ir el ix → Set (i ⊔ l)
_ᵢₕ (ι ix o)            P _       = ⊤
_ᵢₕ (σ A S)             P (a , x) = (S a ᵢₕ) P x
_ᵢₕ (δ A ix S) {ir}{el} P (f , x) = (∀ a → P (f a)) × (S (el ∘ f) ᵢₕ) P x

_ₘₐₚ : ∀ S {ir : I → Set (i ⊔ k)}{el : {ix : I} → ir ix → O ix} (P : ∀ {ix} → ir ix → Set l)
        → (∀ {ix} x → P {ix} x) → ∀ {ix} (x : (S ₀) ir el ix) → (S ᵢₕ) P x
_ₘₐₚ (ι ix' o)           P h t       = tt
_ₘₐₚ (σ A S)             P h (a , x) = (S a ₘₐₚ) P h x
_ₘₐₚ (δ A ix S) {ir}{el} P h (f , x) = (h ∘ f , (S (el ∘ f)ₘₐₚ) P h x)

import PlainIR as IR
open import PlainIR using (IR)

Sigᵢᵣ  = IR.Sig (i ⊔ k) (Σ I O)
Elᵢᵣ   = IR.El
_₀ᵢᵣ   = IR._₀
_₁ᵢᵣ   = IR._₁
_ᵢₕᵢᵣ  = IR._ᵢₕ
_ₘₐₚᵢᵣ  = IR._ₘₐₚ

introᵢᵣ : {S : Sigᵢᵣ} → (S ₀ᵢᵣ) (IR S) Elᵢᵣ → IR S
introᵢᵣ {S} = IR.intro {S = S}

⌞_⌟ : Sig → Sigᵢᵣ
⌞ ι ix o   ⌟ = IR.ι (ix , o)
⌞ σ A S    ⌟ = IR.σ (Lift (i ⊔ k) A) λ a → ⌞ S (↓ a) ⌟
⌞ δ A ix S ⌟ = IR.δ (Lift (i ⊔ k) A) λ f →
               IR.σ ((a : A) → fst (f (↑ a)) ≡ ix a) λ p →
               ⌞ S (λ a → tr O (p a) (snd (f (↑ a)))) ⌟

module Example-3-1 where

   import Data.Nat as N
   data Tag : Set where Nil' Cons' : Tag

   ⌞S⌟ : Set → IR.Sig zero (N.ℕ × ⊤ {zero})
   ⌞S⌟ A = IR.σ (Lift zero Tag) λ where
     (↑ Nil')  → IR.ι (N.zero , tt)
     (↑ Cons') → IR.σ (Lift zero N.ℕ) λ n → IR.σ (Lift zero A) λ _ →
                 IR.δ (Lift zero (⊤ {zero})) λ f → IR.σ (∀ x → fst (f (↑ x)) ≡ (↓ n)) λ p →
                 IR.ι ((N.suc (↓ n)) , tt)


-- Section 3.1
--------------------------------------------------------------------------------

module _ (S* : Sig) where

  ⌞S*⌟ = ⌞ S* ⌟

  private variable
    S  : Sig
    ix : I

  IIR : I → Set (i ⊔ k)
  IIR ix = Σ (IR ⌞S*⌟) λ x → fst (Elᵢᵣ x) ≡ ix

  El : IIR ix → O ix
  El (x , p) = tr O p (snd (Elᵢᵣ x))

  _⌞₀⌟ : Sig → I → Set (i ⊔ k)
  _⌞₀⌟ S ix = Σ ((⌞ S ⌟ ₀ᵢᵣ) (IR ⌞S*⌟) Elᵢᵣ) λ x → fst ((⌞ S ⌟ ₁ᵢᵣ) x) ≡ ix

  0→ : ∀ S → (S ₀) IIR El ix → (S ⌞₀⌟) ix
  0→ (ι i o)    x       .fst             = tt
  0→ (ι i o)    x       .snd             = x .↓
  0→ (σ A S)    (a , x) .fst .fst .↓     = a
  0→ (σ A S)    (a , x) .fst .snd        = 0→ (S a) x .fst
  0→ (σ A S)    (a , x) .snd             = 0→ (S a) x .snd
  0→ (δ A ix S) (f , x) .fst .fst    a   = f (a .↓) .fst
  0→ (δ A ix S) (f , x) .fst .snd .fst a = f a .snd
  0→ (δ A ix S) (f , x) .fst .snd .snd   = 0→ (S (El ∘ f)) x .fst
  0→ (δ A ix S) (f , x) .snd             = 0→ (S (El ∘ f)) x .snd

  0← : ∀ S → (S ⌞₀⌟) ix → (S ₀) IIR El ix
  0← (ι i o)    (x , w)            .↓          = w
  0← (σ A S)    ((↑ a , x) , w)    .fst        = a
  0← (σ A S)    ((↑ a , x) , w)    .snd        = 0← (S a) (x , w)
  0← (δ A ix S) ((f , fw , x) , w) .fst a .fst = f (↑ a)
  0← (δ A ix S) ((f , fw , x) , w) .fst a .snd = fw a
  0← (δ A ix S) ((f , fw , x) , w) .snd        = 0← (S (El ∘ 0← (δ A ix S) ((f , fw , x) , w) .fst)) (x , w)

  η : ∀ S x → 0← {ix} S (0→ S x) ≡ x
  η (ι i o)    (↑ p)    = refl
  η (σ A S)    (a , x)  = ap (a ,_) (η (S a) x)
  η (δ A ix S) (g , x)  = ap (g ,_) (η (S _) x)

  ε : ∀ S x → 0→ {ix} S (0← S x) ≡ x
  ε (ι i o)    (x , w)            = refl
  ε (σ A S)    ((↑ a , x) , w)    = ap (λ xw → ((↑ a , xw .fst) , xw .snd)) (ε (S a) (x , w))
  ε (δ A ix S) ((f , fw , x) , w) = ap (λ xw → (f , fw , xw .fst) , xw .snd) (ε (S _) (x , w))

  τ : ∀ S x → ap (0→ {ix} S) (η S x) ≡ ε S (0→ S x)
  τ (ι i o)   x       = refl
  τ (σ A S)   (a , x) =
       J (λ x eq → ap (0→ (σ A S)) (ap (a ,_) eq)
                 ≡ ap (λ xw → (↑ a , xw .fst) , xw .snd) (ap (0→ (S a)) eq))
         (η (S a) x)
         refl
     ◼ ap (ap (λ xw → (↑ a , xw .fst) , xw .snd)) (τ (S a) x)
  τ (δ A ix S) (f , x) =
    let lhs = ap (0→ (δ A ix S)) (ap (f ,_) (η (S (El ∘ f)) x))
        rhs = ap (λ xw → ((λ a → f (a .↓) .fst) , (λ a → f a .snd) , xw .fst) , xw .snd)
                 (ε (S (El ∘ f)) (0→ (S (El ∘ f)) x))
    in the (lhs ≡ rhs) $
        J (λ x eq → ap (0→ (δ A ix S)) (ap (f ,_) eq)
                  ≡ ap (λ xw → ((λ a → f (a .↓) .fst) , (λ a → f a .snd) , xw .fst) , xw .snd)
                       (ap (0→ (S _)) eq))
          (η (S _) x)
          refl
      ◼ ap (ap (λ xw → ((λ a → f (a .↓) .fst) , (λ a → f a .snd) , xw .fst) , xw .snd))
           (τ (S (El ∘ f)) x)

  _⌞₁⌟ : ∀ S (x : (S ₀) IIR El ix) → tr O (snd (0→ S x)) (snd ((⌞ S ⌟ ₁ᵢᵣ) (fst (0→ S x)))) ≡ (S ₁) x
  (ι i o ⌞₁⌟)    x       = refl
  (σ A S ⌞₁⌟)    (a , x) = (S a ⌞₁⌟) x
  (δ A ix S ⌞₁⌟) (f , x) = (S (El ∘ f) ⌞₁⌟) x

  intro : (S* ₀) IIR El ix → IIR ix
  intro x = introᵢᵣ (fst (0→ S* x)) , snd (0→ S* x)

  El≡ : ∀ x → El (intro {ix} x) ≡ (S* ₁) x
  El≡ = (S* ⌞₁⌟)


-- Section 3.2
--------------------------------------------------------------------------------

  module _ {l} (P : ∀ {i} → IIR i → Set l)(f : ∀ {ix} x → (S* ᵢₕ) P {ix} x → P (intro x)) where

    ⌞P⌟ : IR ⌞ S* ⌟ → Set (k ⊔ l)
    ⌞P⌟ x = ∀ {ix} p → P {ix} (x , p)

    IH← : ∀ S {x : (S ⌞₀⌟) ix} → (⌞ S ⌟ ᵢₕᵢᵣ) ⌞P⌟ (x .fst) → (S ᵢₕ) P (0← S x)
    IH← (ι i o)   {x}                  ih               = tt
    IH← (σ A S)   {((↑ a , x) , w)}    ih               = IH← (S a) {x , w} ih
    IH← (δ A f S) {((g , gw , x) , w)} (gᴾ , ih) .fst a = gᴾ (↑ a) (gw a)
    IH← (δ A f S) {((g , gw , x) , w)} (gᴾ , ih) .snd   = IH← (S _) {x , w} ih

    ⌞f⌟ : (x : (⌞S*⌟ ₀ᵢᵣ) (IR ⌞S*⌟) Elᵢᵣ) →  (⌞S*⌟ ᵢₕᵢᵣ) ⌞P⌟ x → ⌞P⌟ (introᵢᵣ x)
    ⌞f⌟ x ih p = tr (λ {(x , p) → P (IR.intro x , p)})
                    (ε S* (x , p))
                    (f (0← S* (x , p)) (IH← S* ih))

    elim : ∀ {ix} x → P {ix} x
    elim (x , p) = IR.elim ⌞P⌟ ⌞f⌟ x p

    ⌞ₘₐₚ⌟ : ∀ S f (x : (S ₀) IIR El ix) →
                     tr ((S ᵢₕ) P) (η S x) (IH← S ((⌞ S ⌟ ₘₐₚᵢᵣ) ⌞P⌟ f (fst (0→ S x))))
                   ≡ (S ₘₐₚ) P (λ {(x , p) → f x p}) x
    ⌞ₘₐₚ⌟ (ι ix o)   f x       = refl
    ⌞ₘₐₚ⌟ (σ A S)    f (a , x) = tr-∘ ((σ A S ᵢₕ) P) (a ,_) (η (S a) x) _ ◼ ⌞ₘₐₚ⌟ (S a) f x
    ⌞ₘₐₚ⌟ (δ A ix S) f (g , x) =
             tr-∘ ((δ A ix S ᵢₕ) P) (g ,_) (η (S (El ∘ g)) x) _
           ◼ tr-Σ (η (S (El ∘ g)) x) _
           ◼ Σ≡ (tr-const (η (S (El ∘ g)) x) _)
                (
                   tr-const (tr-const (η (S (El ∘ g)) x) _) _
                 ◼ tr-∘ ((S (El ∘ g) ᵢₕ) P) fst (Σ≡ (η (S (El ∘ g)) x) refl) _ ⁻¹
                 ◼ ap (λ eq → tr ((S (El ∘ g) ᵢₕ) P) eq
                                 (IH← (δ A ix S) ((⌞ δ A ix S ⌟ ₘₐₚᵢᵣ) ⌞P⌟ f (0→ (δ A ix S) (g , x) . fst)) .snd))
                      (Σ≡₁ (η (S _) x) refl)
                 ◼ ⌞ₘₐₚ⌟ (S _) f x
                )

    elim-β : ∀ x → elim {ix} (intro x) ≡ f x ((S* ₘₐₚ) P elim x)
    elim-β {ix} x =
       (
       let inner = IH← S* ((⌞S*⌟ ₘₐₚᵢᵣ) ⌞P⌟ (λ x p → elim (x , p)) (0→ S* x .fst))
           lhs   = tr (λ {(x , p) → P (introᵢᵣ x , p)}) (ε S* (0→ S* x))
                      (f (0← S* (0→ S* x)) inner)
           rhs   = f x (tr ((S* ᵢₕ) P) (η S* x) inner)
       in the (lhs ≡ rhs) $
             ap (λ eq → tr (λ {(x , p) → P (introᵢᵣ x , p)}) eq (f (0← S* (0→ S* x)) inner))
                (τ S* x ⁻¹)
           ◼ tr-∘ (λ {(x , p) → P (introᵢᵣ x , p)}) (0→ S*) (η S* x) _
           ◼ tr-app-lem {C = P ∘ intro} f (η S* x)
       )
       ◼ ap (f x) (⌞ₘₐₚ⌟ S* (λ x p → elim (x , p)) x)
