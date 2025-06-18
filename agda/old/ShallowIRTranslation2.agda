
open import Lib
import PlainIR
import IndexedIR

module old.ShallowIRTranslation2 (ext : Level) (ol : Level) (O : Set ol) (Oᴾ : O → Set ol) where

  module IR = PlainIR ext ol O

  data Sigᴾ : IR.Sig → Set (lsuc ext ⊔ lsuc ol) where
    ι : ∀ {o}(oᴾ : Oᴾ o) → Sigᴾ (IR.ι o)
    σ : ∀ {A} (Aᴾ : A → Set ext){S : A → IR.Sig}      (Sᴾ : ∀ {a} → Aᴾ a → Sigᴾ (S a)) → Sigᴾ (IR.σ A S)
    δ : ∀ {A} (Aᴾ : A → Set ext){S : (A → O) → IR.Sig}(Sᴾ : ∀ {f} → (∀ {a} → Aᴾ a → Oᴾ (f a)) → Sigᴾ (S f)) → Sigᴾ (IR.δ A S)

  -- -- cons list as subsignature relation
  -- data Moh : ∀ {S} → Sigᴾ S → ∀ {S'} → Sigᴾ S' → Set (lsuc ext ⊔ lsuc ol) where
  --   idh : ∀ {S Sᴾ} → Moh {S} Sᴾ Sᴾ
  --   σ<  : ∀ {A : Set ext}{Aᴾ : A → Set ext}{S : A → IR.Sig}{Sᴾ : ∀ {a} → Aᴾ a → Sigᴾ (S a)}{S' Sᴾ'}
  --         → ∀ a (aᴾ : Aᴾ a)
  --         → Moh (Sᴾ aᴾ) {S'} Sᴾ'
  --         → Moh (σ Aᴾ Sᴾ) {S'} Sᴾ'
  --   δ<  : ∀ {A : Set ext}{Aᴾ : A → Set ext}
  --           {S : (A → O) → IR.Sig}{Sᴾ : ∀ {f} → (∀ {a} → Aᴾ a → Oᴾ (f a)) → Sigᴾ (S f)}{S' Sᴾ'}
  --         → ∀ (f : A → U)(fᴾ : ∀ {a} → Aᴾ a → Oᴾ (El (f a)))
  --         → Moh (Sᴾ ?) {S'} Sᴾ'
  --         → Moh (δ Aᴾ Aᴾ) Sᴾ'

  module _ {S* : IR.Sig}(S*ᴾ : Sigᴾ S*) where

    module IIR = IndexedIR {ext}{ext}{ol} (IR.U S*) (Oᴾ ∘ IR.El S*)

    El = IR.El S*
    U  = IR.U S*
    F0 = λ S → IR.F0 S U El
    F1 = λ S → IR.F1 S U El

    -- snoc list as subsignature relation, holding the larger signature to be fixed S*
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

    -- -- cons list as subsignature relation, holding the smaller signature fixed
    -- data Moh : ∀ {S} → Sigᴾ S → ∀ {S'} → Sigᴾ S' → Set (lsuc ext ⊔ lsuc ol) where
    --   idh : ∀ {S Sᴾ} → Moh {S} Sᴾ Sᴾ
    --   σ<  : ∀ {A : Set ext}{Aᴾ : A → Set ext}{S : A → IR.Sig}{Sᴾ : ∀ {a} → Aᴾ a → Sigᴾ (S a)}{S' Sᴾ'}
    --         → ∀ a (aᴾ : Aᴾ a)
    --         → Moh (Sᴾ aᴾ) {S'} Sᴾ'
    --         → Moh (σ Aᴾ Sᴾ) {S'} Sᴾ'
    --   δ<  : ∀ {A : Set ext}{Aᴾ : A → Set ext}
    --           {S : (A → O) → IR.Sig}{Sᴾ : ∀ {f} → (∀ {a} → Aᴾ a → Oᴾ (f a)) → Sigᴾ (S f)}{S' Sᴾ'}
    --         → ∀ (f : A → U)(fᴾ : ∀ {a} → Aᴾ a → Oᴾ (El (f a)))
    --         → Moh (Sᴾ fᴾ) {S'} Sᴾ'
    --         → Moh (δ Aᴾ Sᴾ) Sᴾ'

    HomF0 : ∀ {S}{Sᴾ} → Hom {S} Sᴾ → F0 S → F0 S*
    HomF0 idh           acc = acc
    HomF0 (σ< hom a aᴾ) acc = HomF0 hom (a , acc)
    HomF0 (δ< hom f fᴾ) acc = HomF0 hom (f , acc)

    -- MohF0 : ∀ {S Sᴾ S' Sᴾ'} → Moh {S} Sᴾ {S'} Sᴾ' → F0 S → F0 S'
    -- MohF0 idh           x        = x
    -- MohF0 (σ< a aᴾ moh) (a' , x) = {!MohF0 moh!}
    -- MohF0 (δ< f fᴾ moh) (f' , x) = {!!}

    HomF1 : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ) → ∀ {x} → F1 S x ≡ F1 S* (HomF0 hom x)
    HomF1 idh           = refl
    HomF1 (σ< hom a aᴾ) = HomF1 hom
    HomF1 (δ< hom f fᴾ) = HomF1 hom

    IxSig : ∀ {S}(Sᴾ : Sigᴾ S) → Hom Sᴾ → IIR.Sig
    IxSig (ι oᴾ)            hom = IIR.ι (IR.wrap (HomF0 hom (lift tt))) (tr Oᴾ (HomF1 hom) oᴾ)  -- we don't need to collect
    IxSig (σ {A} Aᴾ {S} Sᴾ) hom = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → IxSig (Sᴾ aᴾ) (σ< hom a aᴾ) -- ᴾ-s for this shit here!!
    IxSig (δ {A} Aᴾ Sᴾ)     hom = IIR.σ (A → U) λ f → IIR.δ (∃ Aᴾ) (λ aaᴾ → f (aaᴾ .₁)) λ fᴾ →  -- try to refine the Hom accumulation!
                                  IxSig (Sᴾ λ aᴾ → fᴾ (_ , aᴾ)) (δ< hom f (λ aᴾ → fᴾ (_ , aᴾ)))

    Uᴾ : U → Set ext
    Uᴾ = IIR.U (IxSig S*ᴾ idh)

    Elᴾ : {x : U} → Uᴾ x → Oᴾ (El x)
    Elᴾ = IIR.El (IxSig S*ᴾ idh)

    F0ᴾ : ∀ {S} → Sigᴾ S → F0 S → Set ext
    F0ᴾ (ι oᴾ)    x       = Lift _ ⊤
    F0ᴾ (σ Aᴾ Sᴾ) (a , t) = Σ (Aᴾ a) λ aᴾ → F0ᴾ (Sᴾ aᴾ) t
    F0ᴾ (δ Aᴾ Sᴾ) (f , t) = Σ (∀ {a} → Aᴾ a → Uᴾ (f a)) λ fᴾ → F0ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) t

    F1ᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → Oᴾ (F1 S x)
    F1ᴾ (ι oᴾ)    xᴾ        = oᴾ
    F1ᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) = F1ᴾ (Sᴾ aᴾ) tᴾ
    F1ᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) = F1ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) tᴾ

    Homᴾ : ∀ {S}{Sᴾ : Sigᴾ S} → Hom Sᴾ → Set (lsuc ext ⊔ lsuc ol)
    Homᴾ idh                   = Lift _ ⊤
    Homᴾ (σ< hom a aᴾ)         = Homᴾ hom
    Homᴾ (δ< {A}{Aᴾ} hom f fᴾ) = Σ (∀ {a} → Aᴾ a → Uᴾ (f a)) λ fᴾ* → ((λ {a} → fᴾ {a}) ≡ Elᴾ ∘ fᴾ*) × Homᴾ hom

    IxF0ᴾ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x : F0 S} → F0ᴾ Sᴾ x → IIR.F0 (IxSig Sᴾ hom) Uᴾ Elᴾ (IR.wrap (HomF0 hom x))
    IxF0ᴾ (ι oᴾ)    hom xᴾ               = lift refl
    IxF0ᴾ (σ Aᴾ Sᴾ) hom {a , x}(aᴾ , xᴾ) = a , aᴾ , IxF0ᴾ (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ
    IxF0ᴾ (δ Aᴾ Sᴾ) hom {f , x}(fᴾ , xᴾ) = f , (λ aaᴾ → fᴾ (aaᴾ .₂)) , IxF0ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) (δ< hom f (Elᴾ ∘ fᴾ)) xᴾ

    foo : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x : U} → IIR.F0 (IxSig Sᴾ hom) Uᴾ Elᴾ x → F0 S
    foo (ι oᴾ)    hom xᴾ            = lift tt
    foo (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) = a , foo (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ
    foo (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) = f , foo (Sᴾ λ aᴾ → Elᴾ (fᴾ (_ , aᴾ))) (δ< hom f λ aᴾ → Elᴾ (fᴾ (_ , aᴾ))) xᴾ

    foo' : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x : U} → IIR.F0 (IxSig Sᴾ hom) Uᴾ Elᴾ x → F0 S
    foo' Sᴾ hom {x} xᴾ = {!!}

    bar : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x : U}(xᴾ : IIR.F0 (IxSig Sᴾ hom) Uᴾ Elᴾ x) → F0ᴾ Sᴾ (foo Sᴾ hom xᴾ)
    bar (ι oᴾ)    hom xᴾ            = lift tt
    bar (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) = aᴾ , bar (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ
    bar (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) = (λ {a} z → fᴾ (a , z)) , bar (Sᴾ (λ aᴾ → Elᴾ (fᴾ (_ , aᴾ))))
                                                                (δ< hom f (λ aᴾ → Elᴾ (fᴾ (_ , aᴾ)))) xᴾ


    UnIxF0ᴾ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x : F0 S} → IIR.F0 (IxSig Sᴾ hom) Uᴾ Elᴾ (IR.wrap (HomF0 hom x)) → F0ᴾ Sᴾ x
    UnIxF0ᴾ (ι oᴾ)    hom x                       = lift tt
    UnIxF0ᴾ (σ Aᴾ Sᴾ) hom {a' , x'} (a , aᴾ , xᴾ) = {!!} , {!!}
    UnIxF0ᴾ (δ Aᴾ Sᴾ) hom {f' , x'} (f , fᴾ , xᴾ) = {!!} , {!!}

    -- UnIxF0ᴾ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x : U} → IIR.F0 (IxSig Sᴾ hom) Uᴾ Elᴾ x → F0ᴾ Sᴾ {!IR.unwrap x!}
    -- UnIxF0ᴾ = {!U!}

    -- UnIxF0ᴾ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x : U} → IIR.F0 (IxSig Sᴾ hom) Uᴾ Elᴾ (IR.wrap (HomF0 hom {!IR.unwrap x!})) → F0ᴾ Sᴾ {!IR.unwrap x!}
    -- UnIxF0ᴾ  = {!!}





    -- TODO: UnIxF0ᴾ

    wrapᴾ : {x : F0 S*}(xᴾ : F0ᴾ S*ᴾ x) → Uᴾ (IR.wrap x)
    wrapᴾ xᴾ = IIR.wrap (IxF0ᴾ S*ᴾ idh xᴾ)

    HomF0ᴾ : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ)(homᴾ : Homᴾ hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x) → F0ᴾ S*ᴾ (HomF0 hom x)
    HomF0ᴾ idh           homᴾ                xᴾ = xᴾ
    HomF0ᴾ (σ< hom a aᴾ) homᴾ                xᴾ = HomF0ᴾ hom homᴾ (aᴾ , xᴾ)
    HomF0ᴾ (δ< hom f fᴾ) (fᴾ* , refl , homᴾ) xᴾ = HomF0ᴾ hom homᴾ (fᴾ* , xᴾ)

    HomF1ᴾ : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ)(homᴾ : Homᴾ hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x)
             → tr Oᴾ (HomF1 hom {x}) (F1ᴾ Sᴾ xᴾ) ≡ F1ᴾ  S*ᴾ (HomF0ᴾ hom homᴾ xᴾ)
    HomF1ᴾ idh           homᴾ              xᴾ = refl
    HomF1ᴾ (σ< hom a aᴾ) homᴾ              xᴾ = HomF1ᴾ hom homᴾ (aᴾ , xᴾ)
    HomF1ᴾ (δ< hom f fᴾ) (_ , refl , homᴾ) xᴾ = HomF1ᴾ hom homᴾ (_ , xᴾ)

    IxF1ᴾ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ)(homᴾ : Homᴾ hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x)
          → IIR.F1 (IxSig Sᴾ hom) Uᴾ Elᴾ (IxF0ᴾ Sᴾ hom xᴾ) ≡ F1ᴾ S*ᴾ (HomF0ᴾ hom homᴾ xᴾ)
    IxF1ᴾ (ι oᴾ)    hom homᴾ        xᴾ        = HomF1ᴾ hom homᴾ xᴾ
    IxF1ᴾ (σ Aᴾ Sᴾ) hom homᴾ {a , x}(aᴾ , xᴾ) = IxF1ᴾ (Sᴾ aᴾ) (σ< hom a aᴾ) homᴾ xᴾ
    IxF1ᴾ (δ Aᴾ Sᴾ) hom homᴾ {f , x}(fᴾ , xᴾ) = IxF1ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) (δ< hom f (Elᴾ ∘ fᴾ)) (fᴾ , refl , homᴾ) xᴾ

    El≡ᴾ : ∀ {x} (xᴾ : F0ᴾ S*ᴾ x) → Elᴾ (wrapᴾ xᴾ) ≡ F1ᴾ S*ᴾ xᴾ
    El≡ᴾ xᴾ = IxF1ᴾ S*ᴾ idh (lift tt) xᴾ

    module _ {j}(P : U → Set j)(Pᴾ : ∀ {x} → Uᴾ x → P x → Set j) where

      IH    = λ S → IR.IH S U El P
      mapIH = λ S → IR.mapIH S U El P

      IHᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → IH S x → Set (ext ⊔ j)
      IHᴾ (ι oᴾ)    xᴾ        w       = Lift _ ⊤
      IHᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) w       = IHᴾ (Sᴾ aᴾ) tᴾ w
      IHᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) (g , w) = (∀ {a} aᴾ → Pᴾ (fᴾ aᴾ) (g a)) × IHᴾ (Sᴾ (Elᴾ ∘ fᴾ)) tᴾ w

      -- UnIxIHᴾ : ∀ {S}(Sᴾ : Sigᴾ S)(hom : Hom Sᴾ){x}(xᴾ : F0ᴾ Sᴾ x){ih : IH S x}
      --           → IIR.IH (IxSig Sᴾ hom) Uᴾ Elᴾ (λ {x} xᴾ → Pᴾ xᴾ {!!}) (IxF0ᴾ Sᴾ hom xᴾ) → IHᴾ {S} Sᴾ xᴾ ih
      -- UnIxIHᴾ = {!!}

      mapIHᴾ : ∀{S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x){f}(fᴾ : ∀ {x} xᴾ → Pᴾ xᴾ (f x)) → IHᴾ Sᴾ xᴾ (mapIH S x f)
      mapIHᴾ (ι oᴾ)    tᴾ        fᴾ = lift tt
      mapIHᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) gᴾ = mapIHᴾ (Sᴾ aᴾ) tᴾ gᴾ
      mapIHᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) gᴾ = (gᴾ ∘ fᴾ) , mapIHᴾ (Sᴾ (Elᴾ ∘ fᴾ)) tᴾ gᴾ

      elimᴾ : {met : ∀ (x : F0 S*) → IH S* x → P (IR.wrap x)}
              (metᴾ : ∀ {x}(xᴾ : F0ᴾ S*ᴾ x){ih : IH S* x}(ihᴾ : IHᴾ S*ᴾ xᴾ ih) → Pᴾ (wrapᴾ xᴾ) (met x ih))
            → ∀ {x}(xᴾ : Uᴾ x) → Pᴾ xᴾ (IR.elim S* P met x)
      elimᴾ {met} metᴾ {x} =
        IIR.elim (IxSig S*ᴾ idh)
                 (λ {x} xᴾ → Pᴾ xᴾ (IR.elim S* P met x))
                 (λ {x} xᴾ hyp → {!metᴾ {IR.unwrap x} !})

  -- {-# TERMINATING #-}
  -- elim : ∀ {j} Γ (P : U Γ → Set j) → (∀ t → IH Γ (U Γ) (El Γ) P t → P (wrap t)) → ∀ t → P t
  -- elim Γ P f (wrap t) = f t (mapIH _ _ _ _ t (elim Γ P f))

-- -- --------------------------------------------------------------------------------
