{-# OPTIONS --without-K #-}

open import Lib
import PlainIR
import IndexedIR

module ShallowIRTranslation5 (ext : Level) (ol : Level) (O : Set ol) (Oᴾ : O → Set ol) where

  module IR = PlainIR ext ol O

  data Sigᴾ : IR.Sig → Set (lsuc ext ⊔ lsuc ol) where
    ι : ∀ {o}(oᴾ : Oᴾ o) → Sigᴾ (IR.ι o)
    σ : ∀ {A} (Aᴾ : A → Set ext){S : A → IR.Sig}      (Sᴾ : ∀ {a} → Aᴾ a → Sigᴾ (S a)) → Sigᴾ (IR.σ A S)
    δ : ∀ {A} (Aᴾ : A → Set ext){S : (A → O) → IR.Sig}(Sᴾ : ∀ {f} → (∀ a → Aᴾ a → Oᴾ (f a)) → Sigᴾ (S f)) → Sigᴾ (IR.δ A S)

  module _ {S* : IR.Sig}(S*ᴾ : Sigᴾ S*) where

    module IIR = IndexedIR {ext}{ext}{ol} (IR.U S*) (Oᴾ ∘ IR.El S*)

    El = IR.El S*
    U  = IR.U S*
    F0 = λ S → IR.F0 S U El
    F1 = λ S → IR.F1 S U El

    -- subsignature relation as a snoc list
    data Hom : ∀ {S} → Sigᴾ S → Set (lsuc ext ⊔ lsuc ol) where
      idh : Hom S*ᴾ
      σ<  : ∀ {A : Set ext}{Aᴾ : A → Set ext}{S : A → IR.Sig}{Sᴾ : ∀ {a} → Aᴾ a → Sigᴾ (S a)}
            → Hom (σ Aᴾ Sᴾ)
            → ∀ a (aᴾ : Aᴾ a)
            → Hom {S a} (Sᴾ aᴾ)
      δ<  : ∀ {A : Set ext}{Aᴾ : A → Set ext}
              {S : (A → O) → IR.Sig}{Sᴾ : ∀ {f} → (∀ a → Aᴾ a → Oᴾ (f a)) → Sigᴾ (S f)}
            → Hom (δ Aᴾ Sᴾ)
            → ∀ (f : A → U)(fᴾ : ∀ a → Aᴾ a → Oᴾ (El (f a)))
            → Hom (Sᴾ fᴾ)

    HomF0 : ∀ {S}{Sᴾ} → Hom {S} Sᴾ → F0 S → F0 S*
    HomF0 idh           acc = acc
    HomF0 (σ< hom a aᴾ) acc = HomF0 hom (a , acc)
    HomF0 (δ< hom f fᴾ) acc = HomF0 hom (f , acc)

    HomF1 : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ) → ∀ {x} → F1 S x ≡ F1 S* (HomF0 hom x)
    HomF1 idh           = refl
    HomF1 (σ< hom a aᴾ) = HomF1 hom
    HomF1 (δ< hom f fᴾ) = HomF1 hom

    Sigᴾ→ : ∀ {S}(Sᴾ : Sigᴾ S) → Hom Sᴾ → IIR.Sig
    Sigᴾ→ (ι oᴾ)            hom = IIR.ι (IR.wrap (HomF0 hom (lift tt))) (tr Oᴾ (HomF1 hom) oᴾ)
    Sigᴾ→ (σ {A} Aᴾ {S} Sᴾ) hom = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → Sigᴾ→ (Sᴾ aᴾ) (σ< hom a aᴾ)
    Sigᴾ→ (δ {A} Aᴾ Sᴾ)     hom = IIR.σ (A → U) λ f → IIR.δ (∃ Aᴾ) (λ aaᴾ → f (aaᴾ .₁)) λ fᴾ →
                                  Sigᴾ→ (Sᴾ λ a aᴾ → fᴾ (a , aᴾ)) (δ< hom f (λ a aᴾ → fᴾ (a , aᴾ)))

    S*ᴾ' = Sigᴾ→ S*ᴾ idh

    Uᴾ : U → Set ext
    Uᴾ = IIR.U S*ᴾ'

    Elᴾ : {x : U} → Uᴾ x → Oᴾ (El x)
    Elᴾ = IIR.El S*ᴾ'

    F0ᴾ : ∀ {S} → Sigᴾ S → F0 S → Set ext
    F0ᴾ (ι oᴾ)    x       = Lift _ ⊤
    F0ᴾ (σ Aᴾ Sᴾ) (a , t) = Σ (Aᴾ a) λ aᴾ → F0ᴾ (Sᴾ aᴾ) t
    F0ᴾ (δ Aᴾ Sᴾ) (f , t) = Σ (∀ a → Aᴾ a → Uᴾ (f a)) λ fᴾ → F0ᴾ (Sᴾ λ a aᴾ → Elᴾ (fᴾ a aᴾ)) t

    F1ᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → Oᴾ (F1 S x)
    F1ᴾ (ι oᴾ)    xᴾ        = oᴾ
    F1ᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) = F1ᴾ (Sᴾ aᴾ) tᴾ
    F1ᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) = F1ᴾ (Sᴾ _) tᴾ

    F0ᴾ' : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ) (x : U) → Set ext
    F0ᴾ' Sᴾ hom x = ∃ λ x' → IR.wrap (HomF0 hom x') ≡ x × F0ᴾ Sᴾ x'

    F0ᴾ→ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x} → F0ᴾ' Sᴾ hom x → IIR.F0 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ x
    F0ᴾ→ (ι oᴾ)    hom (x , eq , xᴾ) .lower                    = eq
    F0ᴾ→ (σ Aᴾ Sᴾ) hom ((a , x) , eq , (aᴾ , xᴾ)) .₁           = a
    F0ᴾ→ (σ Aᴾ Sᴾ) hom ((a , x) , eq , aᴾ , xᴾ) .₂ .₁          = aᴾ
    F0ᴾ→ (σ Aᴾ Sᴾ) hom ((a , x) , eq , aᴾ , xᴾ) .₂ .₂          = F0ᴾ→ (Sᴾ aᴾ) (σ< hom a aᴾ) (x , eq , xᴾ)
    F0ᴾ→ (δ Aᴾ Sᴾ) hom ((f , x) , eq , fᴾ , xᴾ) .₁ a           = f a
    F0ᴾ→ (δ Aᴾ Sᴾ) hom ((f , x) , eq , fᴾ , xᴾ) .₂ .₁ (a , aᴾ) = fᴾ a aᴾ
    F0ᴾ→ (δ Aᴾ Sᴾ) hom ((f , x) , eq , fᴾ , xᴾ) .₂ .₂          = F0ᴾ→ (Sᴾ λ a aᴾ → Elᴾ (fᴾ a aᴾ)) (δ< hom f λ a aᴾ → Elᴾ (fᴾ a aᴾ)) (x , eq , xᴾ)

    F0ᴾ→' : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x} → F0ᴾ Sᴾ x → IIR.F0 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ (IR.wrap (HomF0 hom x))
    F0ᴾ→' Sᴾ hom {x} xᴾ = F0ᴾ→ Sᴾ hom (x , refl , xᴾ)

    F0ᴾ← : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x} → IIR.F0 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ x → F0ᴾ' Sᴾ hom x
    F0ᴾ← (ι oᴾ)    hom (lift xᴾ) .₁ .lower         = tt
    F0ᴾ← (ι oᴾ)    hom (lift xᴾ) .₂ .₁             = xᴾ
    F0ᴾ← (ι oᴾ)    hom (lift xᴾ) .₂ .₂ .lower      = tt
    F0ᴾ← (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) .₁ .₁         = a
    F0ᴾ← (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) .₁ .₂         = F0ᴾ← (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ .₁
    F0ᴾ← (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) .₂ .₁         = F0ᴾ← (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ .₂ .₁
    F0ᴾ← (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) .₂ .₂ .₁      = aᴾ
    F0ᴾ← (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) .₂ .₂ .₂      = F0ᴾ← (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ .₂ .₂
    F0ᴾ← (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) .₁ .₁ a       = f a
    F0ᴾ← (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) .₁ .₂         = F0ᴾ← (Sᴾ _) (δ< hom f (λ a aᴾ → Elᴾ (fᴾ (_ , aᴾ)))) xᴾ .₁
    F0ᴾ← (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) .₂ .₁         = F0ᴾ← (Sᴾ _) (δ< hom f (λ a aᴾ → Elᴾ (fᴾ (_ , aᴾ)))) xᴾ .₂ .₁
    F0ᴾ← (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) .₂ .₂ .₁ a aᴾ = fᴾ (a , aᴾ)
    F0ᴾ← (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) .₂ .₂ .₂      = F0ᴾ← (Sᴾ _) (δ< hom f (λ a aᴾ → Elᴾ (fᴾ (_ , aᴾ)))) xᴾ .₂ .₂

    F0ᴾrl : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x}(xᴾ : IIR.F0 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ x)
            → F0ᴾ→ Sᴾ hom (F0ᴾ← Sᴾ hom xᴾ) ≡ xᴾ
    F0ᴾrl (ι oᴾ)    hom xᴾ            = refl
    F0ᴾrl (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) = ap (λ x → a , aᴾ , x) (F0ᴾrl (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ)
    F0ᴾrl (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) = ap (λ x → f , fᴾ , x) (F0ᴾrl (Sᴾ _)  (δ< hom f _) xᴾ)

    F0ᴾlr : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x}(xᴾ : F0ᴾ' Sᴾ hom x)
            → F0ᴾ← Sᴾ hom (F0ᴾ→ Sᴾ hom xᴾ) ≡ xᴾ
    F0ᴾlr (ι oᴾ)    hom xᴾ = refl
    F0ᴾlr (σ Aᴾ Sᴾ) hom ((a , x) , eq , aᴾ , xᴾ) =
      ap (λ x → (a , x .₁) , x .₂ .₁ , aᴾ , x .₂ .₂) (F0ᴾlr (Sᴾ aᴾ) (σ< hom a aᴾ) (x , eq , xᴾ))
    F0ᴾlr (δ Aᴾ Sᴾ) hom ((f , x) , eq , fᴾ , xᴾ) =
      ap (λ x → (f , x .₁) , x .₂ .₁ , fᴾ , x .₂ .₂) (F0ᴾlr (Sᴾ _) (δ< hom f _) (x , eq , xᴾ))

    wrapᴾ : {x : F0 S*}(xᴾ : F0ᴾ S*ᴾ x) → Uᴾ (IR.wrap x)
    wrapᴾ {x} xᴾ = IIR.wrap (F0ᴾ→' S*ᴾ idh xᴾ)

    Hom* : ∀ {S}{Sᴾ : Sigᴾ S} → Hom Sᴾ → Set (lsuc ext ⊔ lsuc ol)
    Hom* idh                   = Lift _ ⊤
    Hom* (σ< hom a aᴾ)         = Hom* hom
    Hom* (δ< {A}{Aᴾ} hom f fᴾ) =
      Σ (∀ a → Aᴾ a → Uᴾ (f a)) λ fᴾ* → (fᴾ ≡ λ a aᴾ → Elᴾ (fᴾ* _ aᴾ)) × Hom* hom

    HomF0ᴾ : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ)(homᴾ : Hom* hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x) → F0ᴾ S*ᴾ (HomF0 hom x)
    HomF0ᴾ idh           homᴾ                xᴾ = xᴾ
    HomF0ᴾ (σ< hom a aᴾ) homᴾ                xᴾ = HomF0ᴾ hom homᴾ (aᴾ , xᴾ)
    HomF0ᴾ (δ< hom f fᴾ) (fᴾ* , refl , homᴾ) xᴾ = HomF0ᴾ hom homᴾ (fᴾ* , xᴾ)

    HomF1ᴾ : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ)(homᴾ : Hom* hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x)
             → tr Oᴾ (HomF1 hom {x}) (F1ᴾ Sᴾ xᴾ) ≡ F1ᴾ  S*ᴾ (HomF0ᴾ hom homᴾ xᴾ)
    HomF1ᴾ idh           homᴾ              xᴾ = refl
    HomF1ᴾ (σ< hom a aᴾ) homᴾ              xᴾ = HomF1ᴾ hom homᴾ (aᴾ , xᴾ)
    HomF1ᴾ (δ< hom f fᴾ) (_ , refl , homᴾ) xᴾ = HomF1ᴾ hom homᴾ (_ , xᴾ)

    F1ᴾ→ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ)(homᴾ : Hom* hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x)
          → IIR.F1 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ (F0ᴾ→' Sᴾ hom xᴾ) ≡ F1ᴾ S*ᴾ (HomF0ᴾ hom homᴾ xᴾ)
    F1ᴾ→ (ι oᴾ)    hom homᴾ        xᴾ        = HomF1ᴾ hom homᴾ xᴾ
    F1ᴾ→ (σ Aᴾ Sᴾ) hom homᴾ {a , x}(aᴾ , xᴾ) = F1ᴾ→ (Sᴾ aᴾ) (σ< hom a aᴾ) homᴾ xᴾ
    F1ᴾ→ (δ Aᴾ Sᴾ) hom homᴾ {f , x}(fᴾ , xᴾ) = F1ᴾ→ (Sᴾ _) (δ< hom f _) (fᴾ , refl , homᴾ) xᴾ

    Elᴾ≡ : ∀ {x} (xᴾ : F0ᴾ S*ᴾ x) → Elᴾ (wrapᴾ xᴾ) ≡ F1ᴾ S*ᴾ xᴾ
    Elᴾ≡ xᴾ = F1ᴾ→ S*ᴾ idh (lift tt) xᴾ

    module _ {j}(P : U → Set j)(Pᴾ : ∀ {x} → Uᴾ x → P x → Set j) where

      IH    = λ S → IR.IH S U El P
      mapIH = λ S → IR.mapIH S U El P

      IHᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → IH S x → Set (ext ⊔ j)
      IHᴾ (ι oᴾ)    xᴾ        w       = Lift _ ⊤
      IHᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) w       = IHᴾ (Sᴾ aᴾ) tᴾ w
      IHᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) (g , w) =
        (∀ a aᴾ → Pᴾ (fᴾ a aᴾ) (g a)) × IHᴾ (Sᴾ (λ a aᴾ → Elᴾ (fᴾ a aᴾ))) tᴾ w

      mapIHᴾ : ∀{S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x){f}(fᴾ : ∀ {x} xᴾ → Pᴾ xᴾ (f x)) → IHᴾ Sᴾ xᴾ (mapIH S x f)
      mapIHᴾ (ι oᴾ)    tᴾ        fᴾ = lift tt
      mapIHᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) gᴾ = mapIHᴾ (Sᴾ aᴾ) tᴾ gᴾ
      mapIHᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) gᴾ = (λ a aᴾ → gᴾ (fᴾ a aᴾ)) , mapIHᴾ (Sᴾ _) tᴾ gᴾ

      module _  (met  : ∀ (x : F0 S*) → IH S* x → P (IR.wrap x))
                (metᴾ : ∀ {x}(xᴾ : F0ᴾ S*ᴾ x)
                {ih : IH S* x}(ihᴾ : IHᴾ S*ᴾ xᴾ ih) → Pᴾ (wrapᴾ xᴾ) (met x ih)) where

        Pᴾ' : ∀ {x} → Uᴾ x → Set j
        Pᴾ' {x} xᴾ = Pᴾ xᴾ (IR.elim S* P met x)

        Pᴾ'' : (∃ λ x → Uᴾ x × P x) → Set j
        Pᴾ'' (x , xᴾ , w) = Pᴾ xᴾ w

        IHᴾ← : ∀ {S} Sᴾ{x}(hom : Hom {S} Sᴾ){xᴾ : IIR.F0 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ x}
                 → IIR.IH (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ Pᴾ' xᴾ
                 → IHᴾ Sᴾ (F0ᴾ← Sᴾ hom xᴾ .₂ .₂) (mapIH S (F0ᴾ← Sᴾ hom xᴾ .₁) (IR.elim S* P met))
        IHᴾ← (ι oᴾ) hom ihᴾ .lower = tt
        IHᴾ← (σ Aᴾ Sᴾ) hom {a , aᴾ , xᴾ} ihᴾ = IHᴾ← (Sᴾ aᴾ) (σ< hom a aᴾ) ihᴾ
        IHᴾ← (δ Aᴾ Sᴾ) hom {f , fᴾ , xᴾ} ihᴾ .₁ a aᴾ = ihᴾ .₁ (a , aᴾ)
        IHᴾ← (δ Aᴾ Sᴾ) hom {f , fᴾ , xᴾ} ihᴾ .₂ = IHᴾ← (Sᴾ _) (δ< hom f _) (ihᴾ .₂)

        abstract
         metᴾ' : ∀ {x} (xᴾ : IIR.F0 (Sigᴾ→ S*ᴾ idh) Uᴾ Elᴾ x) → IIR.IH (Sigᴾ→ S*ᴾ idh) Uᴾ Elᴾ Pᴾ' xᴾ
                  → Pᴾ' (IIR.wrap xᴾ)
         metᴾ' {x} xᴾ ih =
           tr (λ xᴾ → Pᴾ' (IIR.wrap xᴾ))
              (F0ᴾrl S*ᴾ idh xᴾ)
              (J (λ _ eq → Pᴾ' (IIR.wrap (F0ᴾ→ S*ᴾ idh (F0ᴾ← S*ᴾ idh xᴾ .₁ , eq , F0ᴾ← S*ᴾ idh xᴾ .₂ .₂))))
                 (F0ᴾ← S*ᴾ idh xᴾ .₂ .₁)
                 (metᴾ (F0ᴾ← S*ᴾ idh xᴾ .₂ .₂) (IHᴾ← S*ᴾ idh ih)))

        mapIH-trip :
          ∀ {S} Sᴾ {x} (hom : Hom {S} Sᴾ) (xᴾ : F0ᴾ Sᴾ x)(f : ∀ {i}(x : Uᴾ i) → Pᴾ' x)
          →
          tr (λ xᴾ → IHᴾ Sᴾ (xᴾ .₂ .₂) (mapIH S (xᴾ .₁) (IR.elim S* P met)))
             (F0ᴾlr Sᴾ hom (x , refl , xᴾ))
             (IHᴾ← Sᴾ hom (IIR.mapIH (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ _ Pᴾ' (F0ᴾ→' Sᴾ hom xᴾ) f))
          ≡ mapIHᴾ Sᴾ xᴾ f
        mapIH-trip (ι oᴾ) hom xᴾ f = refl
        mapIH-trip (σ {A} Aᴾ {S} Sᴾ) {a , x} hom (aᴾ , xᴾ) f =
            tr-∘ (λ xᴾ₁ →
                   IHᴾ (Sᴾ (xᴾ₁ .₂ .₂ .₁)) (xᴾ₁ .₂ .₂ .₂)
                  (mapIH (IR.σ A S) (xᴾ₁ .₁) (IR.elim S* P met)))
                (λ x₁ → (a , x₁ .₁) , x₁ .₂ .₁ , aᴾ , x₁ .₂ .₂)
                (F0ᴾlr (Sᴾ aᴾ) (σ< hom a aᴾ) (x , refl , xᴾ))
                _
          ◼ mapIH-trip (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ f
        mapIH-trip (δ {A} Aᴾ {S} Sᴾ) {f , x} hom (fᴾ , xᴾ) s =
             tr-∘
                 (λ xᴾ₁ → Σ ((a : A) (aᴾ : Aᴾ a) → Pᴾ (xᴾ₁ .₂ .₂ .₁ a aᴾ)
                   (IR.elim S* P met (xᴾ₁ .₁ .₁ a))) (λ x₁ → IHᴾ (Sᴾ (λ a aᴾ →
                   IndexedIR.El (IR.U S*) (λ x₂ → Oᴾ (IR.El S* x₂)) (Sigᴾ→ S*ᴾ
                   idh) (xᴾ₁ .₂ .₂ .₁ a aᴾ))) (xᴾ₁ .₂ .₂ .₂) (IR.mapIH (S (λ x₂
                   → IR.El S* (xᴾ₁ .₁ .₁ x₂))) (IR.U S*) (IR.El S*) P (xᴾ₁ .₁
                   .₂) (IR.elim S* P met))))
                 (λ x₁ → (f , x₁ .₁) , x₁ .₂ .₁ , fᴾ , x₁ .₂ .₂)
                 (F0ᴾlr (Sᴾ (λ a aᴾ → IndexedIR.El (IR.U S*) (λ x₁ → Oᴾ
                   (IR.El S* x₁)) (Sigᴾ→ S*ᴾ idh) (fᴾ a aᴾ))) (δ< hom f
                   (λ a aᴾ → IndexedIR.El (IR.U S*) (λ x₁ → Oᴾ (IR.El
                   S* x₁)) (Sigᴾ→ S*ᴾ idh) (fᴾ a aᴾ))) (x , refl , xᴾ))
                 _
          ◼ Σ≡
             (   tr-Σ₀ (F0ᴾlr (Sᴾ _) (δ< hom f _) (x , refl , xᴾ)) _
               ◼ tr-const (F0ᴾlr (Sᴾ _) (δ< hom f _) (x , refl , xᴾ)) _
             )
             (
                 tr-const
                   (tr-Σ₀ (F0ᴾlr (Sᴾ (λ a aᴾ → Elᴾ (fᴾ a aᴾ))) (δ< hom f (λ a
                     aᴾ → Elᴾ (fᴾ a aᴾ))) (x , refl , xᴾ)) ((λ a aᴾ →
                     IIR.mapIH (IIR.σ (A → U) (λ f₁ → IIR.δ (∃ Aᴾ) (λ aaᴾ
                     → f₁ (aaᴾ .₁)) (λ fᴾ₁ → Sigᴾ→ (Sᴾ (λ a₁ aᴾ₁ → fᴾ₁ (a₁
                     , aᴾ₁))) (δ< hom f₁ (λ a₁ aᴾ₁ → fᴾ₁ (a₁ , aᴾ₁))))))
                     Uᴾ Elᴾ (IR.wrap (HomF0 hom (f , x))) Pᴾ' (F0ᴾ→' (δ Aᴾ
                     Sᴾ) hom (fᴾ , xᴾ)) s .₁ (a , aᴾ)) , IHᴾ← (Sᴾ (λ a aᴾ
                     → Elᴾ (F0ᴾ→' (δ Aᴾ Sᴾ) hom (fᴾ , xᴾ) .₂ .₁ (a ,
                     aᴾ)))) (δ< hom (F0ᴾ→' (δ Aᴾ Sᴾ) hom (fᴾ , xᴾ) .₁) (λ
                     a aᴾ → Elᴾ (F0ᴾ→' (δ Aᴾ Sᴾ) hom (fᴾ , xᴾ) .₂ .₁ (a ,
                     aᴾ)))) (IIR.mapIH (IIR.σ (A → U) (λ f₁ → IIR.δ (∃ Aᴾ)
                     (λ aaᴾ → f₁ (aaᴾ .₁)) (λ fᴾ₁ → Sigᴾ→ (Sᴾ (λ a aᴾ →
                     fᴾ₁ (a , aᴾ))) (δ< hom f₁ (λ a aᴾ → fᴾ₁ (a , aᴾ))))))
                     Uᴾ Elᴾ (IR.wrap (HomF0 hom (f , x))) Pᴾ' (F0ᴾ→' (δ Aᴾ
                     Sᴾ) hom (fᴾ , xᴾ)) s .₂)) ◼ tr-const (F0ᴾlr (Sᴾ (λ a
                     aᴾ → Elᴾ (fᴾ a aᴾ))) (δ< hom f (λ a aᴾ → Elᴾ (fᴾ a
                     aᴾ))) (x , refl , xᴾ)) (λ a aᴾ → IIR.mapIH (IIR.σ (A
                     → U) (λ f₁ → IIR.δ (∃ Aᴾ) (λ aaᴾ → f₁ (aaᴾ .₁)) (λ
                     fᴾ₁ → Sigᴾ→ (Sᴾ (λ a₁ aᴾ₁ → fᴾ₁ (a₁ , aᴾ₁))) (δ< hom
                     f₁ (λ a₁ aᴾ₁ → fᴾ₁ (a₁ , aᴾ₁)))))) Uᴾ Elᴾ (IR.wrap
                     (HomF0 hom (f , x))) Pᴾ' (F0ᴾ→' (δ Aᴾ Sᴾ) hom (fᴾ ,
                     xᴾ)) s .₁ (a , aᴾ)))
                   _
               ◼ {!Σ!}
               ◼ mapIH-trip (Sᴾ _) (δ< hom f _) xᴾ s
             )

        elimᴾ : ∀ {x}(xᴾ : Uᴾ x) → Pᴾ xᴾ (IR.elim S* P met x)
        elimᴾ {x} xᴾ = IIR.elim (Sigᴾ→ S*ᴾ idh) Pᴾ' metᴾ' xᴾ

        elimβᴾ : ∀ {x : F0 S*} (xᴾ : F0ᴾ S*ᴾ x)
                 → elimᴾ (wrapᴾ xᴾ) ≡ metᴾ xᴾ (mapIHᴾ S*ᴾ xᴾ elimᴾ)
        elimβᴾ {x} xᴾ =
          let lhs = metᴾ' (F0ᴾ→' S*ᴾ idh xᴾ)
                      (IIR.mapIH S*ᴾ' Uᴾ Elᴾ _ Pᴾ' (F0ᴾ→' S*ᴾ idh xᴾ) (IIR.elim S*ᴾ' Pᴾ' metᴾ'))
              rhs = metᴾ xᴾ (mapIHᴾ S*ᴾ xᴾ elimᴾ)
          in {!!}



--------------------------------------------------------------------------------
