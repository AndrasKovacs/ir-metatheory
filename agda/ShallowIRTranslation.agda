
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

    PSig : ∀ {S} → Sigᴾ S → (f : F0 S → F0 S*) → (∀ {x} → Oᴾ (F1 S x) → Oᴾ (F1 S* (f x))) → IIR.Sig
    PSig (ι oᴾ)        f g = IIR.ι (IR.wrap (f (lift tt))) (g oᴾ)
    PSig (σ {A} Aᴾ Sᴾ) f g = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → PSig (Sᴾ aᴾ) (λ x → f (a , x)) (λ {x} → g {a , x})
    PSig (δ {A} Aᴾ Sᴾ) f g = IIR.σ (A → U) λ ts → IIR.δ (∃ Aᴾ) (λ aaᴾ → ts (aaᴾ .₁)) λ tsᴾ →
                               PSig (Sᴾ (λ aᴾ → tsᴾ (_ , aᴾ))) (λ x → f (ts , x)) (λ {x} → g {ts , x})

    Uᴾ : U → Set ext
    Uᴾ = IIR.U (PSig S*ᴾ id id)

    Elᴾ : {x : U} → Uᴾ x → Oᴾ (El x)
    Elᴾ = IIR.El (PSig S*ᴾ id id)

    PF0 : ∀ {S}(Sᴾ : Sigᴾ S)
            {x : F0 S}(xᴾ : F0ᴾ Uᴾ Elᴾ Sᴾ x)
          → (f : F0 S → F0 S*)
          → (g : ∀ {x} → Oᴾ (F1 S x) → Oᴾ (F1 S* (f x)))
          → (h : IIR.F0 (PSig Sᴾ f g) Uᴾ Elᴾ (IR.wrap (f x)) → IIR.F0 (PSig S*ᴾ id id) Uᴾ Elᴾ (IR.wrap (f x)))
          → IIR.F0 (PSig S*ᴾ id id) Uᴾ Elᴾ (IR.wrap (f x))
    PF0 (ι oᴾ)    xᴾ          f g h = h (lift refl)
    PF0 (σ Aᴾ Sᴾ) (aᴾ , xᴾ)   f g h = PF0 (Sᴾ aᴾ) xᴾ (λ x → f (_ , x)) g (λ x → h (_ , aᴾ , x))
    PF0 (δ Aᴾ Sᴾ) (chdᴾ , xᴾ) f g h = PF0 (Sᴾ (Elᴾ ∘ chdᴾ)) xᴾ (λ x → f (_ , x)) g λ x → h (_ , (λ x → chdᴾ (x .₂)) , x)

    wrapᴾ : {x : F0 S*}(xᴾ : F0ᴾ Uᴾ Elᴾ S*ᴾ x) → Uᴾ (IR.wrap x)
    wrapᴾ xᴾ = IIR.wrap (PF0 S*ᴾ xᴾ id id id)


    El≡ᴾ : ∀ {x} (xᴾ : F0ᴾ Uᴾ Elᴾ S*ᴾ x) → Elᴾ (wrapᴾ xᴾ) ≡ F1ᴾ Uᴾ Elᴾ S*ᴾ xᴾ
    El≡ᴾ xᴾ = {!!}


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
