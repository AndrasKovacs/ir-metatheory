{-# OPTIONS --without-K #-}

open import Lib


-- Section 3
----------------------------------------------------------------------------------------------------

module DeriveIndexed {i j k : Level}(I : Set k)(O : I → Set j) where

data Sig : Set (suc i ⊔ j ⊔ k) where
  ι : ∀ ix → O ix → Sig
  σ : (A : Set i) → (A → Sig) → Sig
  δ : (A : Set i)(ixs : A → I) → ((∀ a → O (ixs a)) → Sig) → Sig

E : Sig → (ir : I → Set (i ⊔ k)) → (∀ {ix} → ir ix → O ix) → I → Set (i ⊔ k)
E (ι ix' o  ) ir el ix = Lift (i ⊔ k) (ix' ≡ ix)
E (σ A S    ) ir el ix = Σ A λ a → E (S a) ir el ix
E (δ A ixs S) ir el ix = Σ (∀ a → ir (ixs a)) λ f → E (S (el ∘ f)) ir el ix

F : ∀ {S : Sig}{ir : I → Set (i ⊔ k)}{el : ∀ {i} → ir i → O i} → ∀ {ix} → E S ir el ix → O ix
F {ι ix o}             (↑ x)   = tr O x o
F {σ A S}              (a , x) = F {S a} x
F {δ A ixs S} {ir}{el} (f , x) = F {S (el ∘ f)} x

IH : ∀ {S l}{ir : I → Set (i ⊔ k)}{el : ∀{ix} → ir ix → O ix}
       (P : ∀ {ix} → ir ix → Set l) → ∀ {ix} → E S ir el ix → Set (i ⊔ l)
IH {ι ix o  }            P _       = ⊤
IH {σ A S   }            P (a , x) = IH {S = S a} P x
IH {δ A ixs S} {el = el} P (f , x) = (∀ a → P (f a)) × IH {S (el ∘ f)} P x

map : ∀ {S l}{ir : I → Set (i ⊔ k)}{el : {ix : I} → ir ix → O ix} {P : ∀ {ix} → ir ix → Set l}
      → (∀ {ix} x → P {ix} x) → ∀ {ix} (x : E S ir el ix) → IH P x
map {ι i' o   }          g t       = tt
map {σ A S    }          g (a , x) = map {S = S a} g x
map {δ A ixs S}{el = el} g (f , x) = (g ∘ f , map {S = S (el ∘ f)} g x)

import PlainIR as IR
open import PlainIR using (IR)

Sigᵢᵣ = IR.Sig (i ⊔ k) (Σ I O)

⌞_⌟ : Sig → Sigᵢᵣ
⌞ ι ix o    ⌟ = IR.ι (ix , o)
⌞ σ A S     ⌟ = IR.σ (Lift (i ⊔ k) A) λ a → ⌞ S (↓ a) ⌟
⌞ δ A ixs S ⌟ = IR.δ (Lift (i ⊔ k) A) λ f →
                IR.σ ((a : A) → fst (f (↑ a)) ≡ ixs a) λ p →
                ⌞ S (λ a → tr O (p a) (snd (f (↑ a)))) ⌟

module Example-3-1 where

   import Data.Nat as N
   data Tag : Set where Nil' Cons' : Tag

   ⌞S⌟ : Set → IR.Sig zero (N.ℕ × ⊤ {zero})
   ⌞S⌟ A = IR.σ (Lift zero Tag) λ where
     (↑ Nil')  → IR.ι (N.zero , tt)
     (↑ Cons') → IR.σ (Lift zero N.ℕ) λ n → IR.σ (Lift zero A) λ _ →
                 IR.δ (Lift zero (⊤ {zero})) λ f → IR.σ ((x : ⊤ {zero}) → fst (f (↑ x)) ≡ (↓ n)) λ p →
                 IR.ι ((N.suc (↓ n)) , tt)


-- Section 3.1
----------------------------------------------------------------------------------------------------

module _ (S* : Sig) where

  ⌞S*⌟ = ⌞ S* ⌟

  IIR : I → Set (i ⊔ k)
  IIR ix = Σ (IR ⌞S*⌟) λ x → fst (IR.El x) ≡ ix

  El : ∀ {ix} → IIR ix → O ix
  El (x , p) = tr O p (snd (IR.El x))

  ⌞E⌟ : Sig → I → Set (i ⊔ k)
  ⌞E⌟ S ix = Σ (IR.E (⌞ S ⌟) (IR ⌞S*⌟) IR.El) λ x → fst (IR.F x) ≡ ix

  E→ : ∀ {S ix} → E S IIR El ix → ⌞E⌟ S ix
  E→ {ι i o   } x       .fst             = tt
  E→ {ι i o   } x       .snd             = x .↓
  E→ {σ A S   } (a , x) .fst .fst .↓     = a
  E→ {σ A S   } (a , x) .fst .snd        = E→ x .fst
  E→ {σ A S   } (a , x) .snd             = E→ x .snd
  E→ {δ A ix S} (f , x) .fst .fst    a   = f (a .↓) .fst
  E→ {δ A ix S} (f , x) .fst .snd .fst a = f a .snd
  E→ {δ A ix S} (f , x) .fst .snd .snd   = E→ x .fst
  E→ {δ A ix S} (f , x) .snd             = E→ x .snd

  E← : ∀ {S ix} → ⌞E⌟ S ix → E S IIR El ix
  E← {ι i o    } (x , w)            .↓          = w
  E← {σ A S    } ((↑ a , x) , w)    .fst        = a
  E← {σ A S    } ((↑ a , x) , w)    .snd        = E← (x , w)
  E← {δ A ixs S} ((f , fw , x) , w) .fst a .fst = f (↑ a)
  E← {δ A ixs S} ((f , fw , x) , w) .fst a .snd = fw a
  E← {δ A ixs S} ((f , fw , x) , w) .snd        = E← (x , w)

  η : ∀ {S ix} (x : E S IIR El ix) → E← {S}{ix} (E→ {S} x) ≡ x
  η {ι i o    } (↑ p)    = refl
  η {σ A S    } (a , x)  = ap (a ,_) (η {S = S a} x)
  η {δ A ixs S} (g , x)  = ap (g ,_) (η {S = S (El ∘ g)} x)

  ε : ∀ {S ix} (x : ⌞E⌟ S ix) → E→ {S} {ix} (E← {S} x) ≡ x
  ε {ι i o    } (x , w)            = refl
  ε {σ A S    } ((↑ a , x) , w)    = ap (λ xw → ((↑ a , xw .fst) , xw .snd)) (ε (x , w))
  ε {δ A ixs S} ((f , fw , x) , w) = ap (λ xw → (f , fw , xw .fst) , xw .snd) (ε (x , w))

  τ : ∀ {S ix} (x : E S IIR El ix) → ap (E→ {S}{ix}) (η {S = S} x) ≡ ε (E→ x)
  τ {ι i o}   x       = refl
  τ {σ A S}   (a , x) =
       J (λ x eq → ap (E→ {σ A S}) (ap (a ,_) eq) ≡ ap (λ xw → (↑ a , xw .fst) , xw .snd) (ap (E→ {S a}) eq))
         (η x)
         refl
     ◼ ap (ap (λ xw → (↑ a , xw .fst) , xw .snd)) (τ x)
  τ {δ A ixs S} (f , x) =
    let lhs = ap (E→ {δ A ixs S}) (ap (f ,_) (η x))
        rhs = ap (λ xw → ((λ a → f (a .↓) .fst) , (λ a → f a .snd) , xw .fst) , xw .snd)
                 (ε (E→ x))
    in the (lhs ≡ rhs) $
        J (λ x eq → ap (E→ {δ A ixs S}) (ap (f ,_) eq)
                  ≡ ap (λ xw → ((λ a → f (a .↓) .fst) , (λ a → f a .snd) , xw .fst) , xw .snd)
                       (ap (E→ {S _}) eq))
          (η x)
          refl
      ◼ ap (ap (λ xw → ((λ a → f (a .↓) .fst) , (λ a → f a .snd) , xw .fst) , xw .snd))
           (τ x)

  ⌞F⌟ : ∀ {S ix} (x : E S IIR El ix) → tr O (snd (E→ {S} x)) (snd (IR.F (fst (E→ x)))) ≡ F x
  ⌞F⌟ {ι i o   } x       = refl
  ⌞F⌟ {σ A S   } (a , x) = ⌞F⌟ {S a} x
  ⌞F⌟ {δ A ix S} (f , x) = ⌞F⌟ {S (El ∘ f)} x

  intro : ∀ {ix} → E S* IIR El ix → IIR ix
  intro x = IR.intro (fst (E→ x)) , snd (E→ x)

  El-intro : ∀ {ix} x → El (intro {ix} x) ≡ F x
  El-intro = ⌞F⌟


-- Section 3.2
----------------------------------------------------------------------------------------------------

  module _ {l} (P : ∀ {ix} → IIR ix → Set l)(f : ∀ {ix} x → IH {S*} P {ix} x → P (intro x)) where

    ⌞P⌟ : IR ⌞ S* ⌟ → Set (k ⊔ l)
    ⌞P⌟ x = ∀ {ix} p → P {ix} (x , p)

    IH← : ∀ {S ix}{x : ⌞E⌟ S ix} → IR.IH ⌞P⌟ (x .fst) → IH P (E← x)
    IH← {ι i o  } {ix} {x}                  ih               = tt
    IH← {σ A S  } {ix} {((↑ a , x) , w)}    ih               = IH← {S _} ih
    IH← {δ A f S} {ix} {((g , gw , x) , w)} (gᴾ , ih) .fst a = gᴾ (↑ a) (gw a)
    IH← {δ A f S} {ix} {((g , gw , x) , w)} (gᴾ , ih) .snd   = IH← {S _} ih

    ⌞f⌟ : (x : (IR.E ⌞S*⌟) (IR ⌞S*⌟) IR.El) → IR.IH ⌞P⌟ x → ⌞P⌟ (IR.intro x)
    ⌞f⌟ x ih p = tr (λ {(x , p) → P (IR.intro x , p)})
                    (ε (x , p))
                    (f (E← (x , p)) (IH← {S*} ih))

    elim : ∀ {ix} x → P {ix} x
    elim (x , p) = IR.elim ⌞P⌟ ⌞f⌟ x p

    ⌞map⌟ : ∀ S {ix} (f : ∀ x → ⌞P⌟ x) (x : E S IIR El ix) →
                 tr (IH P) (η x) (IH← {S} (IR.map f (fst (E→ x))))
               ≡ map (λ {(x , p) → f x p}) x
    ⌞map⌟ (ι ix o)    f x       = refl
    ⌞map⌟ (σ A S)     f (a , x) = tr-∘ (IH {σ A S} P) (a ,_) (η x) _ ◼ ⌞map⌟ (S a) f x
    ⌞map⌟ (δ A ixs S) f (g , x) =
             tr-∘ (IH {δ A ixs S} P) (g ,_) (η x) _
           ◼ tr-Σ (η x) _
           ◼ Σ≡ (tr-const (η x) _)
                (  tr-const (tr-const (η x) _) _
                 ◼ tr-∘ (IH {S (El ∘ g)} P) fst (Σ≡ (η x) refl) _ ⁻¹
                 ◼ ap (λ eq → tr (IH {S (El ∘ g)} P) eq
                                 (IH← {δ A ixs S} (IR.map {S = ⌞ δ A ixs S ⌟} f (E→ {δ A ixs S} (g , x) . fst)) .snd))
                      (Σ≡₁ (η {S _} x) refl)
                 ◼ ⌞map⌟ (S _) f x
                )

    elim-β : ∀ {ix} x → elim {ix} (intro x) ≡ f x (map elim x)
    elim-β {ix} x =
       (
       let inner = IH← {S*} (IR.map {S = ⌞S*⌟}{P = ⌞P⌟} (λ x p → elim (x , p)) (E→ x .fst))
           lhs   = tr (λ {(x , p) → P (IR.intro x , p)}) (ε (E→ x))
                      (f (E← (E→ x)) inner)
           rhs   = f x (tr (IH {S*} P) (η x) inner)
       in the (lhs ≡ rhs) $
             ap (λ eq → tr (λ {(x , p) → P (IR.intro x , p)}) eq (f (E← (E→ x)) inner))
                (τ x ⁻¹)
           ◼ tr-∘ (λ {(x , p) → P (IR.intro x , p)}) (E→ {S*}) (η x) _
           ◼ tr-app-lem {C = P ∘ intro} f (η x)
       )
       ◼ ap (f x) (⌞map⌟ S* (λ x p → elim (x , p)) x)
