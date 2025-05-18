
open import Lib
import PlainIR
import IndexedIR

module ShallowIRTranslation2 (ext : Level) (ol : Level) (O : Set ol) (Oᴾ : O → Set ol) where

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

    data Hom : ∀ {S} → Sigᴾ S → Set (lsuc ext ⊔ lsuc ol) where
      idh : Hom S*ᴾ
      σ<  : ∀ {A : Set ext}{Aᴾ : A → Set ext}{S : A → IR.Sig}{Sᴾ : ∀ {a} → Aᴾ a → Sigᴾ (S a)}
            → Hom (σ Aᴾ Sᴾ)
            → ∀ a (aᴾ : Aᴾ a)
            → Hom {S a} (Sᴾ aᴾ)
      δ<  : ∀ {A : Set ext}{Aᴾ : A → Set ext}
              {S : (A → O) → IR.Sig}{Sᴾ : ∀ {f} → (∀ {a} → Aᴾ a → Oᴾ (f a)) → Sigᴾ (S f)}
            → Hom (δ Aᴾ Sᴾ)
            → ∀ (f : A → U)(fᴾ : ∀ {a} → Aᴾ a → Oᴾ (El (f a)))
            → Hom (Sᴾ fᴾ)

    HomF0 : ∀ {S}{Sᴾ} → Hom {S} Sᴾ → F0 S → F0 S*
    HomF0 idh           acc = acc
    HomF0 (σ< hom a aᴾ) acc = HomF0 hom (a , acc)
    HomF0 (δ< hom f fᴾ) acc = HomF0 hom (f , acc)

    HomF1 : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ) → ∀ {x} → F1 S x ≡ F1 S* (HomF0 hom x)
    HomF1 idh           = refl
    HomF1 (σ< hom a aᴾ) = HomF1 hom
    HomF1 (δ< hom f fᴾ) = HomF1 hom

    IxSig : ∀ {S}(Sᴾ : Sigᴾ S) → Hom Sᴾ → IIR.Sig
    IxSig (ι oᴾ)            hom = IIR.ι (IR.wrap (HomF0 hom (lift tt))) (tr Oᴾ (HomF1 hom) oᴾ)
    IxSig (σ {A} Aᴾ {S} Sᴾ) hom = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → IxSig (Sᴾ aᴾ) (σ< hom a aᴾ)
    IxSig (δ {A} Aᴾ Sᴾ)     hom = IIR.σ (A → U) λ f → IIR.δ (∃ Aᴾ) (λ aaᴾ → f (aaᴾ .₁)) λ fᴾ →
                                  IxSig (Sᴾ λ aᴾ → fᴾ (_ , aᴾ)) (δ< hom f (λ aᴾ → fᴾ (_ , aᴾ)))

    Uᴾ : U → Set ext
    Uᴾ = IIR.U (IxSig S*ᴾ idh)

    Elᴾ : {x : U} → Uᴾ x → Oᴾ (El x)
    Elᴾ = IIR.El (IxSig S*ᴾ idh)

    Homᴾ : ∀ {S}{Sᴾ : Sigᴾ S} → Hom Sᴾ → Set (lsuc ext ⊔ lsuc ol)
    Homᴾ idh                   = Lift _ ⊤
    Homᴾ (σ< hom a aᴾ)         = Homᴾ hom
    Homᴾ (δ< {A}{Aᴾ} hom f fᴾ) = Σ (∀ {a} → Aᴾ a → Uᴾ (f a)) λ fᴾ* → ((λ {a} → fᴾ {a}) ≡ Elᴾ ∘ fᴾ*) × Homᴾ hom

    IxF0ᴾ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x : F0 S}(xᴾ : F0ᴾ Uᴾ Elᴾ Sᴾ x) → IIR.F0 (IxSig Sᴾ hom) Uᴾ Elᴾ (IR.wrap (HomF0 hom x))
    IxF0ᴾ (ι oᴾ)    hom xᴾ               = lift refl
    IxF0ᴾ (σ Aᴾ Sᴾ) hom {a , x}(aᴾ , xᴾ) = a , aᴾ , IxF0ᴾ (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ
    IxF0ᴾ (δ Aᴾ Sᴾ) hom {f , x}(fᴾ , xᴾ) = f , (λ aaᴾ → fᴾ (aaᴾ .₂)) , IxF0ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) (δ< hom f (Elᴾ ∘ fᴾ)) xᴾ

    wrapᴾ : {x : F0 S*}(xᴾ : F0ᴾ Uᴾ Elᴾ S*ᴾ x) → Uᴾ (IR.wrap x)
    wrapᴾ xᴾ = IIR.wrap (IxF0ᴾ S*ᴾ idh xᴾ)

    HomF0ᴾ : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ)(homᴾ : Homᴾ hom){x : F0 S}(xᴾ : F0ᴾ Uᴾ Elᴾ Sᴾ x) → F0ᴾ Uᴾ Elᴾ S*ᴾ (HomF0 hom x)
    HomF0ᴾ idh           homᴾ                xᴾ = xᴾ
    HomF0ᴾ (σ< hom a aᴾ) homᴾ                xᴾ = HomF0ᴾ hom homᴾ (aᴾ , xᴾ)
    HomF0ᴾ (δ< hom f fᴾ) (fᴾ* , refl , homᴾ) xᴾ = HomF0ᴾ hom homᴾ (fᴾ* , xᴾ)

    HomF1ᴾ : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ)(homᴾ : Homᴾ hom){x : F0 S}(xᴾ : F0ᴾ Uᴾ Elᴾ Sᴾ x)
             → tr Oᴾ (HomF1 hom {x}) (F1ᴾ Uᴾ Elᴾ Sᴾ xᴾ) ≡ F1ᴾ Uᴾ Elᴾ S*ᴾ (HomF0ᴾ hom homᴾ xᴾ)
    HomF1ᴾ idh           homᴾ              xᴾ = refl
    HomF1ᴾ (σ< hom a aᴾ) homᴾ              xᴾ = HomF1ᴾ hom homᴾ (aᴾ , xᴾ)
    HomF1ᴾ (δ< hom f fᴾ) (_ , refl , homᴾ) xᴾ = HomF1ᴾ hom homᴾ (_ , xᴾ)

    IxF1ᴾ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ)(homᴾ : Homᴾ hom){x : F0 S}(xᴾ : F0ᴾ Uᴾ Elᴾ Sᴾ x)
          → IIR.F1 (IxSig Sᴾ hom) Uᴾ Elᴾ (IxF0ᴾ Sᴾ hom xᴾ) ≡ F1ᴾ Uᴾ Elᴾ S*ᴾ (HomF0ᴾ hom homᴾ xᴾ)
    IxF1ᴾ (ι oᴾ)    hom homᴾ        xᴾ        = HomF1ᴾ hom homᴾ xᴾ
    IxF1ᴾ (σ Aᴾ Sᴾ) hom homᴾ {a , x}(aᴾ , xᴾ) = IxF1ᴾ (Sᴾ aᴾ) (σ< hom a aᴾ) homᴾ xᴾ
    IxF1ᴾ (δ Aᴾ Sᴾ) hom homᴾ {f , x}(fᴾ , xᴾ) = IxF1ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) (δ< hom f (Elᴾ ∘ fᴾ)) (fᴾ , refl , homᴾ) xᴾ

    El≡ᴾ : ∀ {x} (xᴾ : F0ᴾ Uᴾ Elᴾ S*ᴾ x) → Elᴾ (wrapᴾ xᴾ) ≡ F1ᴾ Uᴾ Elᴾ S*ᴾ xᴾ
    El≡ᴾ xᴾ = IxF1ᴾ S*ᴾ idh (lift tt) xᴾ

-- --   -- mutual
-- --   --   data U (Γ : Sig) : Set ext where
-- --   --     wrap : F0 Γ (U Γ) (El Γ) → U Γ
-- --   --   {-# TERMINATING #-}
-- --   --   El : ∀ Γ → U Γ → O
-- --   --   El Γ (wrap t) = F1 Γ (U Γ) (El Γ) t

-- --   -- {-# TERMINATING #-}
-- --   -- elim : ∀ {j} Γ (P : U Γ → Set j) → (∀ t → IH Γ (U Γ) (El Γ) P t → P (wrap t)) → ∀ t → P t
-- --   -- elim Γ P f (wrap t) = f t (mapIH _ _ _ _ t (elim Γ P f))

-- -- --------------------------------------------------------------------------------
