
open import Lib
import PlainIR
import IndexedIR

module ShallowIRTranslation (ext : Level) (ol : Level) (O : Set ol) (Oᴾ : O → Set ol) where

  module IR = PlainIR ext ol O

  data Sigᴾ : IR.Sig → Set (lsuc ext ⊔ lsuc ol) where
    ι : ∀ o → Oᴾ o → Sigᴾ (IR.ι o)
    σ : ∀ A (Aᴾ : A → Set ext)(Γ : A → IR.Sig)(Γᴾ : ∀ a → Aᴾ a → Sigᴾ (Γ a)) → Sigᴾ (IR.σ A Γ)
    δ : ∀ A (Aᴾ : A → Set ext)(Γ : (A → O) → IR.Sig)(Γᴾ : ∀ f → (∀ a → Aᴾ a → Oᴾ (f a)) → Sigᴾ (Γ f)) → Sigᴾ (IR.δ A Γ)

  F0ᴾ : (S : IR.Sig)(Sᴾ : Sigᴾ S)
        (u : Set ext)(uᴾ : u → Set ext)(el : u → O)(elᴾ : ∀ x (xᴾ : uᴾ x) → Oᴾ (el x))
      → IR.F0 S u el → Set ext
  F0ᴾ S (ι o oᴾ)      u uᴾ el elᴾ x       = Lift _ ⊤
  F0ᴾ S (σ A Aᴾ Γ Γᴾ) u uᴾ el elᴾ (a , t) = Σ (Aᴾ a) λ aᴾ → F0ᴾ (Γ a) (Γᴾ a aᴾ) u uᴾ el elᴾ t
  F0ᴾ S (δ A Aᴾ Γ Γᴾ) u uᴾ el elᴾ (f , t) = Σ (∀ a → Aᴾ a → uᴾ (f a)) λ fᴾ →
                                            F0ᴾ (Γ (el ∘ f)) (Γᴾ (el ∘ f) λ a aᴾ → elᴾ _ (fᴾ a aᴾ))
                                                u uᴾ el elᴾ t

  F1ᴾ : (S : IR.Sig)(Sᴾ : Sigᴾ S)
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

  module _ (S* : IR.Sig) where
    module IIR = IndexedIR {ext}{ext}{ol} (IR.U S*) (Oᴾ ∘ IR.El S*)

    PSig : ∀ (S : IR.Sig) → Sigᴾ S
      → (f : IR.F0 S (IR.U S*) (IR.El S*) → IR.F0 S* (IR.U S*) (IR.El S*))
      → (∀ x → Oᴾ (IR.F1 S (IR.U S*) (IR.El S*) x) → Oᴾ (IR.F1 S* (IR.U S*) (IR.El S*) (f x)))
      → IIR.Sig
    PSig _ (ι o oᴾ)      f g = IIR.ι (IR.wrap (f (lift tt))) (g (lift tt) oᴾ)
    PSig _ (σ A Aᴾ S Sᴾ) f g = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → PSig (S a) (Sᴾ a aᴾ) (λ x → f (a , x)) (λ x → g (a , x))
    PSig _ (δ A Aᴾ S Sᴾ) f g = IIR.σ (A → IR.U S*) λ ts → IIR.δ (∃ Aᴾ) (λ aaᴾ → ts (aaᴾ .₁)) λ tsᴾ →
                               PSig (S (IR.El S* ∘ ts)) (Sᴾ _ (curry tsᴾ)) (λ x → f (ts , x)) (λ x → g (ts , x))

  Uᴾ : (S : IR.Sig)(Sᴾ : Sigᴾ S) → IR.U S → Set ext
  Uᴾ S Sᴾ x = IIR.U S (PSig S S Sᴾ (λ x → x) (λ _ oᴾ → oᴾ)) x

  Elᴾ : (S : IR.Sig)(Sᴾ : Sigᴾ S)(x : IR.U S)(xᴾ : Uᴾ S Sᴾ x) → Oᴾ (IR.El S x)
  Elᴾ S Sᴾ x xᴾ = IIR.El S (PSig S S Sᴾ (λ x → x) (λ _ oᴾ → oᴾ)) {x} xᴾ

  PF0 : (S* : IR.Sig)(S*ᴾ : Sigᴾ S*)
        (S : IR.Sig)(Sᴾ : Sigᴾ S)
        (x : IR.F0 S (IR.U S*) (IR.El S*))(xᴾ : F0ᴾ S Sᴾ (IR.U S*) (Uᴾ S* S*ᴾ) (IR.El S*) (Elᴾ S* S*ᴾ) x)
      → (f : IR.F0 S (IR.U S*) (IR.El S*) → IR.F0 S* (IR.U S*) (IR.El S*))
      → (g : ∀ x → Oᴾ (IR.F1 S (IR.U S*) (IR.El S*) x) → Oᴾ (IR.F1 S* (IR.U S*) (IR.El S*) (f x)))

      → (h : IIR.F0 S* (PSig S* S Sᴾ f g)
                       (IIR.U S* (PSig S* S* S*ᴾ (λ x → x)  (λ _ x → x)))
                       (IIR.El S* (PSig S* S* S*ᴾ (λ x → x) (λ _ x → x)))
                       (IR.wrap (f x))

          → IIR.F0 S*
                  (PSig S* S* S*ᴾ (λ x → x) λ _ x → x)
                  (IIR.U  S* (PSig S* S* S*ᴾ (λ x → x) λ _ x → x))
                  (IIR.El S* (PSig S* S* S*ᴾ (λ x → x) λ _ x → x))
                  (IR.wrap (f x))
        )

      → IIR.F0 S* (PSig S* S* S*ᴾ (λ x → x) λ _ x → x)
                  (IIR.U  S* (PSig S* S* S*ᴾ (λ x → x) λ _ x → x))
                  (IIR.El S* (PSig S* S* S*ᴾ (λ x → x) λ _ x → x))
                  (IR.wrap (f x))
  PF0 S* S*ᴾ _ (ι o oᴾ)      x xᴾ f g h = h (lift refl)
  PF0 S* S*ᴾ _ (σ A Aᴾ S Sᴾ) (a , t) (aᴾ , tᴾ) f g h =
    PF0 S* S*ᴾ (S a) (Sᴾ a aᴾ) t tᴾ (λ x → f (a , x)) (λ x → g (a , x)) (λ x → h (a , aᴾ , x))
  PF0 S* S*ᴾ _ (δ A Aᴾ S Sᴾ) (chd , t) (chdᴾ , tᴾ) f g h =
    PF0 S* S*ᴾ (S (IR.El S* ∘ chd)) (Sᴾ (IR.El S* ∘ chd) (λ a aᴾ → Elᴾ S* S*ᴾ (chd a) (chdᴾ a aᴾ)))
               t tᴾ (λ x → f (chd , x)) (λ x xᴾ → g (chd , x) xᴾ)
               (λ x → h (chd , uncurry chdᴾ , x))

  -- PF0 S* S*ᴾ S (ι o oᴾ)      x xᴾ f g =
  --   lift refl
  -- PF0 S* S*ᴾ _ (σ A Aᴾ S Sᴾ) (a , t) (aᴾ , tᴾ) f g =
  --   a , aᴾ , {!PF0 S* S*ᴾ !}
  --   -- {!PF0 S* S*ᴾ (S a) (Sᴾ a aᴾ) t tᴾ (λ x → f (a , x)) (λ x → g (a , x))!}
  -- PF0 S* S*ᴾ _ (δ A Aᴾ S Sᴾ) (chd , t) (chdᴾ , tᴾ) f g =
  --   {!!}

  -- PF0 _ (ι o oᴾ) x xᴾ = lift refl
  -- PF0 _ (σ A Aᴾ S Sᴾ) (a , t) (aᴾ , tᴾ) = a , aᴾ         , {!PF0 (S a) (Sᴾ a aᴾ) !}
  -- PF0 _ (δ A Aᴾ S Sᴾ) (f , t) (fᴾ , tᴾ) = f , uncurry fᴾ , {!!}

  wrapᴾ : (S : IR.Sig)(Sᴾ : Sigᴾ S)
          (x : IR.F0 S (IR.U S) (IR.El S))(xᴾ : F0ᴾ S Sᴾ (IR.U S) (Uᴾ S Sᴾ) (IR.El S) (Elᴾ S Sᴾ) x)
        → Uᴾ S Sᴾ (IR.wrap x)
  wrapᴾ S Sᴾ x xᴾ = IIR.wrap {!!} -- (PF0 S Sᴾ S Sᴾ x xᴾ (λ x → x) (λ _ x → x))

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
