
open import Lib
import PlainIR
import IndexedIR

module ShallowIRTranslation (ext : Level) (ol : Level) (O : Set ol) (Oᴾ : O → Set ol) where

  module IR = PlainIR ext ol O

  data Sigᴾ : IR.Sig → Set (lsuc ext ⊔ lsuc ol) where
    ι : ∀ {o} → Oᴾ o → Sigᴾ (IR.ι o)
    σ : ∀ {A} (Aᴾ : A → Set ext){S : A → IR.Sig}      (Sᴾ : ∀ {a} → Aᴾ a → Sigᴾ (S a)) → Sigᴾ (IR.σ A S)
    δ : ∀ {A} (Aᴾ : A → Set ext){S : (A → O) → IR.Sig}(Sᴾ : ∀ {f} → (∀ {a} → Aᴾ a → Oᴾ (f a)) → Sigᴾ (S f)) → Sigᴾ (IR.δ A S)

  module _ {u : Set ext}(uᴾ : u → Set ext){el : u → O}(elᴾ : ∀ {x} (xᴾ : uᴾ x) → Oᴾ (el x)) where
    private
      F0 = λ S → IR.F0 S u el
      F1 = λ S → IR.F1 S u el

    F0ᴾ : ∀ {S} → Sigᴾ S → F0 S → Set ext
    F0ᴾ (ι oᴾ)    x       = Lift _ ⊤
    F0ᴾ (σ Aᴾ Sᴾ) (a , t) = Σ (Aᴾ a) λ aᴾ → F0ᴾ (Sᴾ aᴾ) t
    F0ᴾ (δ Aᴾ Sᴾ) (f , t) = Σ (∀ {a} → Aᴾ a → uᴾ (f a)) λ fᴾ → F0ᴾ (Sᴾ (elᴾ ∘ fᴾ)) t

    F1ᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → Oᴾ (F1 S x)
    F1ᴾ (ι oᴾ)    xᴾ        = oᴾ
    F1ᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) = F1ᴾ (Sᴾ aᴾ) tᴾ
    F1ᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) = F1ᴾ (Sᴾ (elᴾ ∘ fᴾ)) tᴾ

    module _ {j}(P : u → Set j)(Pᴾ : ∀ {x} → uᴾ x → P x → Set j) where

      private
        IH = λ S → IR.IH S u el P

      IHᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → IH S x → Set (ext ⊔ j)
      IHᴾ (ι oᴾ)    xᴾ        w       = Lift _ ⊤
      IHᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) w       = IHᴾ (Sᴾ aᴾ) tᴾ w
      IHᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) (g , w) = (∀ {a} aᴾ → Pᴾ (fᴾ aᴾ) (g a)) × IHᴾ (Sᴾ (elᴾ ∘ fᴾ)) tᴾ w

      mapIHᴾ : ∀{S}(Sᴾ : Sigᴾ S){t}(tᴾ : F0ᴾ Sᴾ t){f}(fᴾ : ∀ {x} xᴾ → Pᴾ xᴾ (f x)) → IHᴾ Sᴾ tᴾ (IR.mapIH S u el P t f)
      mapIHᴾ (ι oᴾ)    tᴾ        fᴾ = lift tt
      mapIHᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) gᴾ = mapIHᴾ (Sᴾ aᴾ) tᴾ gᴾ
      mapIHᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) gᴾ = (gᴾ ∘ fᴾ) , mapIHᴾ (Sᴾ (elᴾ ∘ fᴾ)) tᴾ gᴾ

  module _ {S* : IR.Sig}(S*ᴾ : Sigᴾ S*) where
    module IIR = IndexedIR {ext}{ext}{ol} (IR.U S*) (Oᴾ ∘ IR.El S*)

    El = IR.El S*
    U  = IR.U S*
    F0 = λ S → IR.F0 S U El
    F1 = λ S → IR.F1 S U El

    IxSig : ∀ {S} → Sigᴾ S → (acci : F0 S → F0 S*)(acco : ∀ {x} → Oᴾ (F1 S x) → Oᴾ (F1 S* (acci x))) → IIR.Sig
    IxSig (ι oᴾ)        acci acco = IIR.ι (IR.wrap (acci (lift tt))) (acco oᴾ)
    IxSig (σ {A} Aᴾ Sᴾ) acci acco = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → IxSig (Sᴾ aᴾ) (λ x → acci (a , x)) (λ {x} → acco {a , x})
    IxSig (δ {A} Aᴾ Sᴾ) acci acco = IIR.σ (A → U) λ ts → IIR.δ (∃ Aᴾ) (λ aaᴾ → ts (aaᴾ .₁)) λ tsᴾ →
                                    IxSig (Sᴾ (λ aᴾ → tsᴾ (_ , aᴾ))) (λ x → acci (ts , x)) (λ {x} → acco {ts , x})

    Uᴾ : U → Set ext
    Uᴾ = IIR.U (IxSig S*ᴾ id id)

    Elᴾ : {x : U} → Uᴾ x → Oᴾ (El x)
    Elᴾ = IIR.El (IxSig S*ᴾ id id)

    ConvF0 : ∀ {S}(Sᴾ : Sigᴾ S)
            {x     : F0 S}(xᴾ : F0ᴾ Uᴾ Elᴾ Sᴾ x)
          → {acci  : F0 S → F0 S*}
          → {acco  : ∀ {x} → Oᴾ (F1 S x) → Oᴾ (F1 S* (acci x))}
          → (accf0 : IIR.F0 (IxSig Sᴾ acci acco) Uᴾ Elᴾ (IR.wrap (acci x)) → IIR.F0 (IxSig S*ᴾ id id) Uᴾ Elᴾ (IR.wrap (acci x)))
          → IIR.F0 (IxSig S*ᴾ id id) Uᴾ Elᴾ (IR.wrap (acci x))
    ConvF0 (ι oᴾ)    xᴾ          h = h (lift refl)
    ConvF0 (σ Aᴾ Sᴾ) (aᴾ , xᴾ)   h = ConvF0 (Sᴾ aᴾ) xᴾ (λ x → h (_ , aᴾ , x))
    ConvF0 (δ Aᴾ Sᴾ) (chdᴾ , xᴾ) h = ConvF0 (Sᴾ (Elᴾ ∘ chdᴾ)) xᴾ (λ x → h (_ , (λ x → chdᴾ (x .₂)) , x))

    wrapᴾ : {x : F0 S*}(xᴾ : F0ᴾ Uᴾ Elᴾ S*ᴾ x) → Uᴾ (IR.wrap x)
    wrapᴾ xᴾ = IIR.wrap (ConvF0 S*ᴾ xᴾ id)

    ConvF1 :
         ∀ {S}(Sᴾ : Sigᴾ S)
            {x : F0 S}(xᴾ : F0ᴾ Uᴾ Elᴾ Sᴾ x)
          → (acci  : F0 S → F0 S*)
          → (acciᴾ : F0ᴾ Uᴾ Elᴾ Sᴾ x → F0ᴾ Uᴾ Elᴾ S*ᴾ (acci x))
          → (acco  : ∀ {x} → Oᴾ (F1 S x) → Oᴾ (F1 S* (acci x)))
          → (accf0 : IIR.F0 (IxSig Sᴾ acci acco) Uᴾ Elᴾ (IR.wrap (acci x)) → IIR.F0 (IxSig S*ᴾ id id) Uᴾ Elᴾ (IR.wrap (acci x)))
          → (accf1 : IIR.F1 (IxSig Sᴾ acci acco) Uᴾ Elᴾ {IR.wrap (acci x)} {!!} ≡ F1ᴾ Uᴾ Elᴾ S*ᴾ (acciᴾ xᴾ)
                   → IIR.F1 (IxSig S*ᴾ id id) Uᴾ Elᴾ (ConvF0 S*ᴾ (acciᴾ xᴾ) id) ≡ F1ᴾ Uᴾ Elᴾ S*ᴾ (acciᴾ xᴾ))
          → IIR.F1 (IxSig S*ᴾ id id) Uᴾ Elᴾ (ConvF0 S*ᴾ (acciᴾ xᴾ) id)
          ≡ F1ᴾ Uᴾ Elᴾ S*ᴾ (acciᴾ xᴾ)
    ConvF1 (ι oᴾ)    xᴾ acci acciᴾ acco accf0 accf1 = {!!}
    ConvF1 (σ Aᴾ Sᴾ) xᴾ acci acciᴾ acco accf0 accf1 = {!!}
    ConvF1 (δ Aᴾ Sᴾ) xᴾ acci acciᴾ acco accf0 accf1 = {!!}

    El≡ᴾ : ∀ {x} (xᴾ : F0ᴾ Uᴾ Elᴾ S*ᴾ x) → Elᴾ (wrapᴾ xᴾ) ≡ F1ᴾ Uᴾ Elᴾ S*ᴾ xᴾ
    El≡ᴾ xᴾ = ConvF1 S*ᴾ xᴾ id id id id {!!}


--   -- wrapᴾ : (S : IR.Sig)(Sᴾ : Sigᴾ S)
--   --         (x : IR.F0 S (IR.U S) (IR.El S))(xᴾ : F0ᴾ S Sᴾ (IR.U S) (Uᴾ S Sᴾ) (IR.El S) (Elᴾ S Sᴾ) x)
--   --       → Uᴾ S Sᴾ (IR.wrap x)
--   -- wrapᴾ S Sᴾ x xᴾ = IIR.wrap {!!} -- (PF0 S Sᴾ S Sᴾ x xᴾ (λ x → x) (λ _ x → x))

--   -- mutual
--   --   data U (Γ : Sig) : Set ext where
--   --     wrap : F0 Γ (U Γ) (El Γ) → U Γ
--   --   {-# TERMINATING #-}
--   --   El : ∀ Γ → U Γ → O
--   --   El Γ (wrap t) = F1 Γ (U Γ) (El Γ) t

--   -- {-# TERMINATING #-}
--   -- elim : ∀ {j} Γ (P : U Γ → Set j) → (∀ t → IH Γ (U Γ) (El Γ) P t → P (wrap t)) → ∀ t → P t
--   -- elim Γ P f (wrap t) = f t (mapIH _ _ _ _ t (elim Γ P f))

-- --------------------------------------------------------------------------------
