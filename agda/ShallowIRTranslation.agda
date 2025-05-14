
open import Lib
import PlainIR
import IndexedIR

module ShallowIRTranslation (ext : Level) (ol : Level) (O : Set ol) (Oᴾ : O → Set ol) where

  module IR = PlainIR ext ol O

  data Sigᴾ : IR.Sig → Set (lsuc ext ⊔ lsuc ol) where
    ι : ∀ o → Oᴾ o → Sigᴾ (IR.ι o)
    σ : ∀ A (Aᴾ : A → Set ext)(Γ : A → IR.Sig)(Γᴾ : ∀ a → Aᴾ a → Sigᴾ (Γ a)) → Sigᴾ (IR.σ A Γ)
    δ : ∀ A (Aᴾ : A → Set ext)(Γ : (A → O) → IR.Sig)(Γᴾ : ∀ f → (∀ a → Aᴾ a → Oᴾ (f a)) → Sigᴾ (Γ f)) → Sigᴾ (IR.δ A Γ)

  F0ᴾ : (S : IR.Sig)    (Sᴾ : Sigᴾ S)
        (u : Set ext)(uᴾ : u → Set ext)(el : u → O)(elᴾ : ∀ x (xᴾ : uᴾ x) → Oᴾ (el x))
      → IR.F0 S u el → Set ext
  F0ᴾ S (ι o oᴾ)      u uᴾ el elᴾ x       = Lift _ ⊤
  F0ᴾ S (σ A Aᴾ Γ Γᴾ) u uᴾ el elᴾ (a , t) = Σ (Aᴾ a) λ aᴾ → F0ᴾ (Γ a) (Γᴾ a aᴾ) u uᴾ el elᴾ t
  F0ᴾ S (δ A Aᴾ Γ Γᴾ) u uᴾ el elᴾ (f , t) = Σ (∀ a → Aᴾ a → uᴾ (f a)) λ fᴾ →
                                            F0ᴾ (Γ (el ∘ f)) (Γᴾ (el ∘ f) λ a aᴾ → elᴾ _ (fᴾ a aᴾ))
                                                u uᴾ el elᴾ t

  F1ᴾ : (S : IR.Sig)    (Sᴾ : Sigᴾ S)
        (u : Set ext)(uᴾ : u → Set ext)(el : u → O)(elᴾ : ∀ x (xᴾ : uᴾ x) → Oᴾ (el x))
        (x : IR.F0 S u el)(xᴾ : F0ᴾ S Sᴾ u uᴾ el elᴾ x)
        → Oᴾ (IR.F1 S u el x)
  F1ᴾ _ (ι o oᴾ)      u uᴾ el elᴾ x xᴾ = oᴾ
  F1ᴾ _ (σ A Aᴾ S Sᴾ) u uᴾ el elᴾ (a , t) (aᴾ , tᴾ) =
    F1ᴾ (S a) (Sᴾ a aᴾ) u uᴾ el elᴾ t tᴾ
  F1ᴾ _ (δ A Aᴾ S Sᴾ) u uᴾ el elᴾ (f , t) (fᴾ , tᴾ) =
    F1ᴾ (S (el ∘ f)) (Sᴾ (el ∘ f) λ a aᴾ → elᴾ _ (fᴾ a aᴾ)) u uᴾ el elᴾ t tᴾ

  IHᴾ : ∀ {j}
        (S : IR.Sig)(Sᴾ : Sigᴾ S)
        (u : Set ext)(uᴾ : u → Set ext)(el : u → O)(elᴾ : ∀ x (xᴾ : uᴾ x) → Oᴾ (el x))
        (P : u → Set j)(Pᴾ : ∀ x → uᴾ x → P x → Set j)
        (x : IR.F0 S u el)(xᴾ : F0ᴾ S Sᴾ u uᴾ el elᴾ x)
        → IR.IH S u el P x → Set (ext ⊔ j)
  IHᴾ _ (ι o oᴾ)      u uᴾ el elᴾ P Pᴾ x  xᴾ w = Lift _ ⊤
  IHᴾ _ (σ A Aᴾ S Sᴾ) u uᴾ el elᴾ P Pᴾ (a , t) (aᴾ , tᴾ) w =
    IHᴾ (S a) (Sᴾ a aᴾ) u uᴾ el elᴾ P Pᴾ t tᴾ w
  IHᴾ _ (δ A Aᴾ S Sᴾ) u uᴾ el elᴾ P Pᴾ (f , t) (fᴾ , tᴾ) (g , w) =
    Σ (∀ a (aᴾ : Aᴾ a) → Pᴾ (f a) (fᴾ a aᴾ) (g a)) λ gᴾ →
      IHᴾ (S (el ∘ f)) (Sᴾ (el ∘ f) (λ a aᴾ → elᴾ _ (fᴾ a aᴾ))) u uᴾ el elᴾ P Pᴾ t tᴾ w

  mapIHᴾ : ∀ {j}
        (S : IR.Sig)(Sᴾ : Sigᴾ S)
        (u : Set ext)(uᴾ : u → Set ext)(el : u → O)(elᴾ : ∀ x (xᴾ : uᴾ x) → Oᴾ (el x))
        (P : u → Set j)(Pᴾ : ∀ x → uᴾ x → P x → Set j)
        (t : IR.F0 S u el)(tᴾ : F0ᴾ S Sᴾ u uᴾ el elᴾ t)
        (f : ∀ x → P x) (fᴾ : ∀ x (xᴾ : uᴾ x) → Pᴾ x xᴾ (f x))
      → IHᴾ S Sᴾ u uᴾ el elᴾ P Pᴾ t tᴾ (IR.mapIH S u el P t f)
  mapIHᴾ _ (ι o oᴾ) u uᴾ el elᴾ P Pᴾ t tᴾ f fᴾ = lift tt
  mapIHᴾ _ (σ A Aᴾ S Sᴾ) u uᴾ el elᴾ P Pᴾ (a , t) (aᴾ , tᴾ) g gᴾ =
    mapIHᴾ (S a) (Sᴾ a aᴾ) u uᴾ el elᴾ P Pᴾ t tᴾ g gᴾ
  mapIHᴾ _ (δ A Aᴾ S Sᴾ) u uᴾ el elᴾ P Pᴾ (f , t) (fᴾ , tᴾ) g gᴾ =
      (λ a aᴾ → gᴾ (f a) (fᴾ a aᴾ))
    , mapIHᴾ (S (el ∘ f)) (Sᴾ (el ∘ f) (λ a aᴾ → elᴾ _ (fᴾ a aᴾ))) u uᴾ el elᴾ P Pᴾ t tᴾ g gᴾ

  -- And here comes the complication. I can't just predicate-ify the rest of the IR spec, because they
  -- are *postulates*, and I'm not allowed to postulate random crap. I'm only allowed to use features
  -- in my TT. I have indexed IR in my TT, so I shall use that to get predicates for U, El, and elim.

  module _ (S* : IR.Sig) where
    module IIR = IndexedIR {ext}{ext}{ol} (IR.U S*) (Oᴾ ∘ IR.El S*)

    PSig : ∀ (S : IR.Sig) → Sigᴾ S → (f : IR.F0 S (IR.U S*) (IR.El S*) → IR.U S*)
                                   → (∀ x → Oᴾ (IR.F1 S (IR.U S*) (IR.El S*) x) → Oᴾ (IR.El S* (f x))) → IIR.Sig
    PSig _ (ι o oᴾ)      f g = IIR.ι (f (lift tt)) (g (lift tt) oᴾ)
    PSig _ (σ A Aᴾ S Sᴾ) f g = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → PSig (S a) (Sᴾ a aᴾ) (λ x → f (a , x)) (λ x → g (a , x))
    PSig _ (δ A Aᴾ S Sᴾ) f g = IIR.σ (A → IR.U S*) λ ts → IIR.δ (∃ Aᴾ) (λ aaᴾ → ts (aaᴾ .₁)) λ tsᴾ →
                               PSig (S (IR.El S* ∘ ts)) (Sᴾ _ (curry tsᴾ)) (λ x → f (ts , x)) (λ x → g (ts , x))

  Uᴾ : (S : IR.Sig)(Sᴾ : Sigᴾ S) → IR.U S → Set (ext ⊔ ol) -- problem: sigantures are too big for this sizing! I need to shift up everything, but how?
  Uᴾ S Sᴾ x = IIR.U S (PSig S S Sᴾ IR.wrap (λ _ oᴾ → oᴾ)) x

  -- lemmas: if I have a canonical IR.F0, I get an IIR of PSig
  -- similar for IR.F1

  Elᴾ : (S : IR.Sig)(Sᴾ : Sigᴾ S)(x : IR.U S)(xᴾ : Uᴾ S Sᴾ x) → Oᴾ (IR.El S x)
  Elᴾ S Sᴾ x (IndexedIR.wrap x₁) = {!!}
  -- Elᴾ S (ι o oᴾ)      x xᴾ = {!!}
  -- Elᴾ S (σ A Aᴾ Γ Γᴾ) x xᴾ = {!!}
  -- Elᴾ S (δ A Aᴾ Γ Γᴾ) x xᴾ = {!!}

  -- wrapᴾ : (S : IR.Sig)(Sᴾ : Sigᴾ S)(x : IR.F0 S (IR.U S) (IR.El S))(xᴾ : F0ᴾ S Sᴾ (IR.U S) (Uᴾ S Sᴾ) (IR.El S) (Elᴾ S Sᴾ) x)
  --         → Uᴾ S Sᴾ (IR.wrap x)
  -- wrapᴾ S Sᴾ x xᴾ = {!!}

  -- mutual
  --   data U (Γ : Sig) : Set ext where
  --     wrap : F0 Γ (U Γ) (El Γ) → U Γ
  --   {-# TERMINATING #-}
  --   El : ∀ Γ → U Γ → O
  --   El Γ (wrap t) = F1 Γ (U Γ) (El Γ) t

  -- {-# TERMINATING #-}
  -- elim : ∀ {j} Γ (P : U Γ → Set j) → (∀ t → IH Γ (U Γ) (El Γ) P t → P (wrap t)) → ∀ t → P t
  -- elim Γ P f (wrap t) = f t (mapIH _ _ _ _ t (elim Γ P f))

--------------------------------------------------------------------------------
