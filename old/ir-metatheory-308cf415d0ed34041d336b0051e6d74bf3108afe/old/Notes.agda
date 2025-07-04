
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
  renaming (cong to ap; trans to infixr 5 _◼_; sym to infix 5 _⁻¹; subst to tr)
open import Data.Product hiding (map) renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit
open import Level using (Lift; lift; lower)
open import Function

module Notes where

-- deriving indexed IR from IR? with all definitional computation rules

module PlainIR ext i (O : Set i) where

  data Sig : Set (lsuc (ext ⊔ i)) where
    ι : O → Sig
    σ : (A : Set ext) → (A → Sig) → Sig
    δ : (A : Set ext) → ((A → O) → Sig) → Sig

  F0 : Sig → (u : Set ext) → (u → O) → Set ext
  F0 (ι _)   u el = Lift _ ⊤
  F0 (σ A Γ) u el = Σ A λ a → F0 (Γ a) u el
  F0 (δ A Γ) u el = Σ (A → u) λ f → F0 (Γ (el ∘ f)) u el

  F1 : ∀ Γ u el → F0 Γ u el → O
  F1 (ι o)   u el t       = o
  F1 (σ A Γ) u el (a , t) = F1 (Γ a) u el t
  F1 (δ A Γ) u el (f , t) = F1 (Γ (el ∘ f)) u el t

  IH : ∀ {j} Γ (u : Set ext) (el : u → O) (P : u → Set j) → F0 Γ u el → Set (ext ⊔ j)
  IH (ι o)   u el P t       = Lift _ ⊤
  IH (σ A Γ) u el P (a , t) = IH (Γ a) u el P t
  IH (δ A Γ) u el P (f , t) = (∀ a → P (f a)) × IH (Γ (el ∘ f)) u el P t

  mapIH : ∀ {j} Γ (u : Set ext)(el : u → O)(P : u → Set j)(t : F0 Γ u el)(f : ∀ x → P x) → IH Γ u el P t
  mapIH (ι _)   u el P t       f = lift tt
  mapIH (σ A Γ) u el P (a , t) f = mapIH (Γ a) u el P t f
  mapIH (δ A Γ) u el P (g , t) f = f ∘ g , mapIH (Γ (el ∘ g)) u el P t f

  mutual
    data IR (Γ : Sig) : Set ext where
      wrap : F0 Γ (IR Γ) (El Γ) → IR Γ

    {-# TERMINATING #-}
    El : ∀ Γ → IR Γ → O
    El Γ (wrap t) = F1 Γ (IR Γ) (El Γ) t

  {-# TERMINATING #-}
  elim : ∀ {j} Γ (P : IR Γ → Set j) → (∀ (t : F0 Γ (IR Γ) (El Γ)) → IH Γ (IR Γ) (El Γ) P t → P (wrap t)) → (t : IR Γ) → P t
  elim Γ P f (wrap t) = f t (mapIH _ _ _ _ t (elim Γ P f))

module IIR {ext il ol}(I : Set il)(O : I → Set ol) where

  data Sig : Set (lsuc (ext ⊔ il ⊔ ol)) where
    ι : ∀ i → O i → Sig
    σ : (A : Set ext) → (A → Sig) → Sig
    δ : (A : Set ext)(f : A → I) → ((∀ a → O (f a)) → Sig) → Sig

  F0 : Sig → (u : I → Set (ext ⊔ il ⊔ ol))(el : ∀ {i} → u i → O i) → I → Set (ext ⊔ il ⊔ ol)
  F0 (ι i* _)  u el i = Lift (ext ⊔ il ⊔ ol) (i* ≡ i)
  F0 (σ A Γ)   u el i = Σ A λ a → F0 (Γ a) u el i
  F0 (δ A f Γ) u el i = Σ (∀ a → u (f a)) λ g → F0 (Γ (el ∘ g)) u el i

  F1 : ∀ (Γ : Sig)(u : I → Set (ext ⊔ il ⊔ ol))(el : ∀ {i} → u i → O i) → ∀ {i} → F0 Γ u el i → O i
  F1 (ι _ o)    u el p       = tr O (lower p) o
  F1 (σ A Γ)    u el (a , t) = F1 (Γ a) u el t
  F1 (δ A ix Γ) u el (f , t) = F1 (Γ (el ∘ f)) u el t

  IH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il ⊔ ol))(el : ∀{i} → u i → O i)(P : ∀ {i} → u i → Set j) → ∀ {i} → F0 Γ u el i → Set (ext ⊔ j)
  IH (ι _ _)    u el P _       = Lift _ ⊤
  IH (σ A Γ)    u el P (a , t) = IH (Γ a) u el P t
  IH (δ A ix Γ) u el P (f , t) = (∀ a → P (f a)) × IH (Γ (el ∘ f)) u el P t

  mapIH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il ⊔ ol))(el : {i : I} → u i → O i) i (P : ∀ {i} → u i → Set j)(t : F0 Γ u el i)
          → (∀ {i} u → P {i} u) → IH Γ u el P t
  mapIH (ι i' o)   u el i P t       f = lift tt
  mapIH (σ A Γ)    u el i P (a , t) f = mapIH (Γ a) u el i P t f
  mapIH (δ A ix Γ) u el i P (g , t) f = f ∘ g , mapIH (Γ (el ∘ g)) u el i P t f

  mutual
    data IR (Γ : Sig) : I → Set (ext ⊔ il ⊔ ol) where
      wrap : ∀ {i} → F0 Γ (IR Γ) (El Γ) i → IR Γ i

    {-# TERMINATING #-}
    El : ∀ Γ {i} → IR Γ i → O i
    El Γ (wrap t) = F1 Γ (IR Γ) (El Γ) t

  {-# TERMINATING #-}
  elim : ∀ {j}(Γ : Sig)(P : ∀ {i} → IR Γ i → Set j) → (∀ {i} t → IH Γ (IR Γ) (El Γ) P {i} t → P (wrap t)) → ∀ {i} t → P {i} t
  elim Γ P f (wrap t) = f t (mapIH _ _ _ _ _ t (elim Γ P f))


-- Logpred translation of sig for warmup
------------------------------------------------------------------------------------------------------------------------

module LogPredTrans (ext i : Level)(O : Set i) (Oᴾ : O → Set i) where

  module P = PlainIR ext i O

  data Sigᴾ : P.Sig → Set (lsuc ext ⊔ lsuc i) where
    ι : ∀ o → Oᴾ o → Sigᴾ (P.ι o)
    σ : ∀ A (Aᴾ : A → Set ext)(Γ : A → P.Sig)(Γᴾ : ∀ a → Aᴾ a → Sigᴾ (Γ a)) → Sigᴾ (P.σ A Γ)
    δ : ∀ A (Aᴾ : A → Set ext)(Γ : (A → O) → P.Sig)(Γᴾ : ∀ f → (∀ a → Aᴾ a → Oᴾ (f a)) → Sigᴾ (Γ f)) → Sigᴾ (P.δ A Γ)

  module PredImp (Γ : P.Sig) where

    Pred : ∀ {Δ} → Sigᴾ Δ → (t : P.F0 Δ (P.IR Γ) (P.El Γ) → P.IR Γ)(tᴾ : ∀ x → Oᴾ (P.F1 Δ (P.IR Γ) (P.El Γ) x) → Oᴾ (P.El Γ (t x)))
           →  IIR.Sig {ext}{ext}{i} (P.IR Γ) (λ a → Oᴾ (P.El Γ a))
    Pred (ι o oᴾ)      t tᴾ = IIR.ι (t (lift tt)) (tᴾ (lift tt) oᴾ)
    Pred (σ A Aᴾ Δ Δᴾ) t tᴾ = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → Pred (Δᴾ a aᴾ) (λ x → t (a , x)) (λ x → tᴾ (a , x))
    Pred (δ A Aᴾ Δ Δᴾ) t tᴾ = IIR.σ (A → P.IR Γ) λ f → IIR.δ (∃ Aᴾ) (λ aaᴾ → f (aaᴾ .₁)) λ fᴾ →
                              Pred (Δᴾ (P.El Γ ∘ f) (curry fᴾ)) (λ x → t (f , x)) (λ x → tᴾ (f , x))

  Pred : ∀ {Γ} → Sigᴾ Γ → IIR.Sig {ext} (P.IR Γ) (Oᴾ ∘ P.El Γ)
  Pred {Γ} Γᴾ = PredImp.Pred Γ Γᴾ P.wrap (λ x xᴾ → xᴾ)

  IRᴾ : (Γ : P.Sig)(Γᴾ : Sigᴾ Γ) → P.IR Γ → Set (ext ⊔ i)
  IRᴾ Γ Γᴾ t = IIR.IR (P.IR Γ) (Oᴾ ∘ P.El Γ) (Pred Γᴾ) t

  -- prob need F0ᴾ
  wrapᴾ : (Γ : P.Sig)(Γᴾ : Sigᴾ Γ)(t : P.F0 Γ (P.IR Γ) (P.El Γ))(tᴾ : Oᴾ (P.F1 Γ (P.IR Γ) (P.El Γ) t))
        → IRᴾ Γ Γᴾ (P.wrap t)
  wrapᴾ Γ Γᴾ t tᴾ = IIR.wrap {Γ = Pred Γᴾ} {!!}


------------------------------------------------------------------------------------------------------------------------
{-

Canonicity proof. Object theory has vanilla IR and ω levels. Metatheory has indexed IR and ω+1 levels.
Elimination is possible into any level, type formers return in _⊔_
Signatures are assumed to be vanilla inductive types, e.g. W-types.

TODO: do level interpretation by using 2LTT as metatheory instead of first-class level
shenanigans.

(Γ : Con)ᴾ     : Sub ∙ Γ → Setω
(A : Ty Γ i)ᴾ  : ∀ γ γᴾ → Tm ∙ A[γ] → Set i
(σ : Sub Γ Δ)ᴾ : ∀ γ γᴾ → Δᴾ (σ ∘ γ)
(t : Tm Γ A)ᴾ  : ∀ γ γᴾ → Aᴾ γ γᴾ t[γ]

... etc ...

assuming:
  ext : ℕ
  i   : ℕ
  O   : Ty Γ i

  assuming
    O  : Ty ∙ i
    Oᴾ : Tm ∙ O → Set i

    -- canonicity predicate for Sig

    data Sigᴾ : Tm ∙ Sig → Set (ext ⊔ i) where
      ι : (o : Tm ∙ O) → Oᴾ o → Sigᴾ (ι o)
      σ : (A : Ty ∙ ext)     (Aᴾ : Tm ∙ A → Set ext)
          (Γ : Tm (∙,A) Sig) (Γᴾ : ∀ a → Aᴾ a → Sigᴾ (Γ[id,a]))
          → Sigᴾ (σ A Γ)
      δ : (A : Ty ∙ ext)           (Aᴾ : Tm ∙ A → Set ext)
          (Γ : Tm (∙, A → O) Sig)  (Γᴾ : (f : Tm ∙ (A → O)) → (∀ a aᴾ → Oᴾ (f $$ a)) → Sigᴾ (Γ[id, f]))
          → Sigᴾ (δ A Γ)

    assume (Γ : Tm ∙ Sig)

      Pred : ∀ {Δ} → Sigᴾ Δ → (Tm ∙ (F0 Δ (IR Γ) (El Γ)) → Tm ∙ (IR Γ))
                            → (∀ x → Oᴾ (F1 Δ (IR Γ) (El Γ) x → Oᴾ (El Γ (t x))))
                            → Sig (Tm ∙ (IR Γ)) (λ a. Oᴾ (El Γ a))
      Pred (ι o oᴾ)      t tᴾ = ι (t (lift tt)) (tᴾ (lift tt) oᴾ)
      Pred (σ A Aᴾ Δ Δᴾ) t tᴾ = σ (Tm ∙ A) λ a. σ (Aᴾ a) λ aᴾ. Pred (Δᴾ a aᴾ) (λ x. t (a, x)) (λ x. tᴾ (a, x))
      Pred (δ A Aᴾ Δ Δᴾ) t tᴾ = σ (Tm ∙ A → Tm ∙ (IR Γ)) λ f. δ ((a : Tm ∙ A) × Aᴾ a) (λ (a, aᴾ). f a) λ fᴾ.
                                Pred (Δᴾ (λ x. El Γ (f x))) (curry fᴾ) (λ x. t (f, x)) (λ x. tᴾ (f, x))



  (Sig : Ty Γ (ext ⊔ i))ᴾ γ γᴾ : Tm ∙ Sig[γ] → Set (ext ⊔ i)
    Sig γ γᴾ t := Sigᴾ O[γ] (Oᴾ γ γᴾ) t

  -- If we do Sig constructors and SigElim as well,
  -- F0, F1, IH, and mapIH are all obtained automatically in the model.
  -- Now we need to compute by induction on Sigᴾ a meta-Sig indexed over Tm ∙ IR

  (IR (Γ : Sig) : Ty Γ ext)ᴾ γ γᴾ : Tm ∙ (IR Γ[γ]) → Set ext
    (IR Γ)ᴾ γ γᴾ t := IIR (Pred (Γᴾ γ γᴾ) (λ x. wrap x) (λ x xᴾ. xᴾ)) t

  (wrap (t : Tm Γ (F0 S (IR S) (El S))))ᴾ γ γᴾ : IIR (Pred (Sᴾ γ γᴾ) (λ x. wrap x) (λ x xᴾ. xᴾ)) (wrap t[γ])













































-}
