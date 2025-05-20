
open import Lib
import PlainIR
import IndexedIR

module ShallowIRTranslation3 (ext : Level) (ol : Level) (O : Set ol) (Oᴾ : O → Set ol) where

  module IR = PlainIR ext ol O

  data Sigᴾ : IR.Sig → Set (lsuc ext ⊔ lsuc ol) where
    ι : ∀ {o}(oᴾ : Oᴾ o) → Sigᴾ (IR.ι o)
    σ : ∀ {A} (Aᴾ : A → Set ext){S : A → IR.Sig}      (Sᴾ : ∀ {a} → Aᴾ a → Sigᴾ (S a)) → Sigᴾ (IR.σ A S)
    δ : ∀ {A} (Aᴾ : A → Set ext){S : (A → O) → IR.Sig}(Sᴾ : ∀ {f} → (∀ {a} → Aᴾ a → Oᴾ (f a)) → Sigᴾ (S f)) → Sigᴾ (IR.δ A S)

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

    encSigᴾ : ∀ {S}(Sᴾ : Sigᴾ S) → Hom Sᴾ → IIR.Sig
    encSigᴾ (ι oᴾ)            hom = IIR.ι (IR.wrap (HomF0 hom (lift tt))) (tr Oᴾ (HomF1 hom) oᴾ)
    encSigᴾ (σ {A} Aᴾ {S} Sᴾ) hom = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → encSigᴾ (Sᴾ aᴾ) (σ< hom a aᴾ)
    encSigᴾ (δ {A} Aᴾ Sᴾ)     hom = IIR.σ (A → U) λ f → IIR.δ (∃ Aᴾ) (λ aaᴾ → f (aaᴾ .₁)) λ fᴾ →
                                  encSigᴾ (Sᴾ λ aᴾ → fᴾ (_ , aᴾ)) (δ< hom f (λ aᴾ → fᴾ (_ , aᴾ)))

    Uᴾ : U → Set ext
    Uᴾ = IIR.U (encSigᴾ S*ᴾ idh)

    Elᴾ : {x : U} → Uᴾ x → Oᴾ (El x)
    Elᴾ = IIR.El (encSigᴾ S*ᴾ idh)

    F0ᴾ : ∀ {S} → Sigᴾ S → F0 S → Set ext
    F0ᴾ (ι oᴾ)    x       = Lift _ ⊤
    F0ᴾ (σ Aᴾ Sᴾ) (a , t) = Σ (Aᴾ a) λ aᴾ → F0ᴾ (Sᴾ aᴾ) t
    F0ᴾ (δ Aᴾ Sᴾ) (f , t) = Σ (∀ {a} → Aᴾ a → Uᴾ (f a)) λ fᴾ → F0ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) t

    F1ᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → Oᴾ (F1 S x)
    F1ᴾ (ι oᴾ)    xᴾ        = oᴾ
    F1ᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) = F1ᴾ (Sᴾ aᴾ) tᴾ
    F1ᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) = F1ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) tᴾ

    encF0ᴾ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x : F0 S} → F0ᴾ Sᴾ x → IIR.F0 (encSigᴾ Sᴾ hom) Uᴾ Elᴾ (IR.wrap (HomF0 hom x))
    encF0ᴾ (ι oᴾ)    hom xᴾ               = lift refl
    encF0ᴾ (σ Aᴾ Sᴾ) hom {a , x}(aᴾ , xᴾ) = a , aᴾ , encF0ᴾ (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ
    encF0ᴾ (δ Aᴾ Sᴾ) hom {f , x}(fᴾ , xᴾ) = f , (λ aaᴾ → fᴾ (aaᴾ .₂)) , encF0ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) (δ< hom f (Elᴾ ∘ fᴾ)) xᴾ

    decF0ᴾ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x : U}(xᴾ : IIR.F0 (encSigᴾ Sᴾ hom) Uᴾ Elᴾ x)
                 → Σ (F0 S) λ x' →
                   Σ (IR.wrap (HomF0 hom x') ≡ x) λ eq →
                   Σ (F0ᴾ Sᴾ x') λ xᴾ' →
                     tr (IIR.F0 (encSigᴾ Sᴾ hom) Uᴾ Elᴾ) eq (encF0ᴾ Sᴾ hom xᴾ') ≡ xᴾ
    decF0ᴾ (ι oᴾ)    hom (lift refl) = lift tt , refl , lift tt , refl
    decF0ᴾ (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) with decF0ᴾ (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ
    ... | x' , refl , xᴾ' , refl = _ , refl , _ , refl
    decF0ᴾ (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) with decF0ᴾ (Sᴾ λ aᴾ → Elᴾ (fᴾ (_ , aᴾ))) (δ< hom f λ aᴾ → Elᴾ (fᴾ (_ , aᴾ))) xᴾ
    ... | x' , refl , xᴾ' , refl  = _ , refl , _ , refl

    unwrap : U → F0 S*
    unwrap = IR.elim S* (λ _ → F0 S*) (λ x _ → x)

    -- note: we never use any IR-elim to prove equations!
    -- morally, all prop equations are definitional for the object theory,
    -- and wrap inj works up to defn eq by applying unwrap to both sides
    wrap-inj : ∀ {x x' : F0 S*} → IR.wrap x ≡ IR.wrap x' → x ≡ x'
    wrap-inj = ap unwrap

    encF0ᴾ-inj : ∀ {S x} Sᴾ (hom : Hom {S} Sᴾ) (xᴾ xᴾ' : F0ᴾ Sᴾ x)
                 → encF0ᴾ Sᴾ hom xᴾ ≡ encF0ᴾ Sᴾ hom xᴾ' → xᴾ ≡ xᴾ'
    encF0ᴾ-inj (ι oᴾ)    hom xᴾ xᴾ' eq = refl
    encF0ᴾ-inj (σ Aᴾ Sᴾ) hom (aᴾ , xᴾ) (aᴾ' , xᴾ') eq = {!!}
    encF0ᴾ-inj (δ Aᴾ Sᴾ) hom (fᴾ , xᴾ) (fᴾ' , xᴾ') eq = {!!}

    wrapᴾ : {x : F0 S*}(xᴾ : F0ᴾ S*ᴾ x) → Uᴾ (IR.wrap x)
    wrapᴾ xᴾ = IIR.wrap (encF0ᴾ S*ᴾ idh xᴾ)

    Hom* : ∀ {S}{Sᴾ : Sigᴾ S} → Hom Sᴾ → Set (lsuc ext ⊔ lsuc ol)
    Hom* idh                   = Lift _ ⊤
    Hom* (σ< hom a aᴾ)         = Hom* hom
    Hom* (δ< {A}{Aᴾ} hom f fᴾ) = Σ (∀ {a} → Aᴾ a → Uᴾ (f a)) λ fᴾ* → ((λ {a} → fᴾ {a}) ≡ Elᴾ ∘ fᴾ*) × Hom* hom

    HomF0ᴾ : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ)(homᴾ : Hom* hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x) → F0ᴾ S*ᴾ (HomF0 hom x)
    HomF0ᴾ idh           homᴾ                xᴾ = xᴾ
    HomF0ᴾ (σ< hom a aᴾ) homᴾ                xᴾ = HomF0ᴾ hom homᴾ (aᴾ , xᴾ)
    HomF0ᴾ (δ< hom f fᴾ) (fᴾ* , refl , homᴾ) xᴾ = HomF0ᴾ hom homᴾ (fᴾ* , xᴾ)

    HomF1ᴾ : ∀ {S}{Sᴾ}(hom : Hom {S} Sᴾ)(homᴾ : Hom* hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x)
             → tr Oᴾ (HomF1 hom {x}) (F1ᴾ Sᴾ xᴾ) ≡ F1ᴾ  S*ᴾ (HomF0ᴾ hom homᴾ xᴾ)
    HomF1ᴾ idh           homᴾ              xᴾ = refl
    HomF1ᴾ (σ< hom a aᴾ) homᴾ              xᴾ = HomF1ᴾ hom homᴾ (aᴾ , xᴾ)
    HomF1ᴾ (δ< hom f fᴾ) (_ , refl , homᴾ) xᴾ = HomF1ᴾ hom homᴾ (_ , xᴾ)

    encF1ᴾ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ)(homᴾ : Hom* hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x)
          → IIR.F1 (encSigᴾ Sᴾ hom) Uᴾ Elᴾ (encF0ᴾ Sᴾ hom xᴾ) ≡ F1ᴾ S*ᴾ (HomF0ᴾ hom homᴾ xᴾ)
    encF1ᴾ (ι oᴾ)    hom homᴾ        xᴾ        = HomF1ᴾ hom homᴾ xᴾ
    encF1ᴾ (σ Aᴾ Sᴾ) hom homᴾ {a , x}(aᴾ , xᴾ) = encF1ᴾ (Sᴾ aᴾ) (σ< hom a aᴾ) homᴾ xᴾ
    encF1ᴾ (δ Aᴾ Sᴾ) hom homᴾ {f , x}(fᴾ , xᴾ) = encF1ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) (δ< hom f (Elᴾ ∘ fᴾ)) (fᴾ , refl , homᴾ) xᴾ

    Elᴾ≡ : ∀ {x} (xᴾ : F0ᴾ S*ᴾ x) → Elᴾ (wrapᴾ xᴾ) ≡ F1ᴾ S*ᴾ xᴾ
    Elᴾ≡ xᴾ = encF1ᴾ S*ᴾ idh (lift tt) xᴾ

    module _ {j}(P : U → Set j)(Pᴾ : ∀ {x} → Uᴾ x → P x → Set j) where

      IH    = λ S → IR.IH S U El P
      mapIH = λ S → IR.mapIH S U El P

      IHᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → IH S x → Set (ext ⊔ j)
      IHᴾ (ι oᴾ)    xᴾ        w       = Lift _ ⊤
      IHᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) w       = IHᴾ (Sᴾ aᴾ) tᴾ w
      IHᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) (g , w) = (∀ {a} aᴾ → Pᴾ (fᴾ aᴾ) (g a)) × IHᴾ (Sᴾ (Elᴾ ∘ fᴾ)) tᴾ w

      mapIHᴾ : ∀{S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x){f}(fᴾ : ∀ {x} xᴾ → Pᴾ xᴾ (f x)) → IHᴾ Sᴾ xᴾ (mapIH S x f)
      mapIHᴾ (ι oᴾ)    tᴾ        fᴾ = lift tt
      mapIHᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) gᴾ = mapIHᴾ (Sᴾ aᴾ) tᴾ gᴾ
      mapIHᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) gᴾ = (gᴾ ∘ fᴾ) , mapIHᴾ (Sᴾ (Elᴾ ∘ fᴾ)) tᴾ gᴾ

      module _  (met  : ∀ (x : F0 S*) → IH S* x → P (IR.wrap x))
                (metᴾ : ∀ {x}(xᴾ : F0ᴾ S*ᴾ x){ih : IH S* x}(ihᴾ : IHᴾ S*ᴾ xᴾ ih) → Pᴾ (wrapᴾ xᴾ) (met x ih)) where

        encPᴾ : ∀ {x} → Uᴾ x → Set j
        encPᴾ {x} xᴾ = Pᴾ xᴾ (IR.elim S* P met x)

        decIHᴾ : ∀ {S} Sᴾ{x xᴾ}(hom : Hom {S} Sᴾ)
                 → (ih : IIR.IH (encSigᴾ Sᴾ hom) Uᴾ Elᴾ encPᴾ (encF0ᴾ Sᴾ hom {x} xᴾ))
                 → IHᴾ Sᴾ xᴾ (mapIH S x (IR.elim S* P met))
        decIHᴾ (ι oᴾ)    hom ih = ih
        decIHᴾ (σ Aᴾ Sᴾ) {a , x}{aᴾ , xᴾ} hom ih = decIHᴾ (Sᴾ aᴾ) (σ< hom a aᴾ) ih
        decIHᴾ (δ Aᴾ Sᴾ) {f , x}{fᴾ , xᴾ} hom (hyp , ih) =
          (λ aᴾ → hyp (_ , aᴾ)) , decIHᴾ (Sᴾ (Elᴾ ∘ fᴾ)) (δ< hom f (Elᴾ ∘ fᴾ)) ih

        encMetᴾ : ∀ {x} (xᴾ : IIR.F0 (encSigᴾ S*ᴾ idh) Uᴾ Elᴾ x) → IIR.IH (encSigᴾ S*ᴾ idh) Uᴾ Elᴾ encPᴾ xᴾ
                 → encPᴾ (IIR.wrap xᴾ)
        encMetᴾ {x} xᴾ ih =
           let x' , eq , xᴾ' , eq' = decF0ᴾ S*ᴾ idh xᴾ
           in J (λ x eq → (xᴾ  : IIR.F0 (encSigᴾ S*ᴾ idh) Uᴾ Elᴾ x)
                          (eq' : tr (IIR.F0 (encSigᴾ S*ᴾ idh) Uᴾ Elᴾ) eq (encF0ᴾ S*ᴾ idh xᴾ') ≡ xᴾ)
                          (ih  : IIR.IH (encSigᴾ S*ᴾ idh) Uᴾ Elᴾ encPᴾ xᴾ)
                           → encPᴾ (IIR.wrap xᴾ))
                  eq
                  (λ xᴾ eq' ih →
                    J (λ xᴾ eq' → IIR.IH (encSigᴾ S*ᴾ idh) Uᴾ Elᴾ encPᴾ xᴾ → encPᴾ (IIR.wrap xᴾ))
                      eq'
                      (λ ih → metᴾ xᴾ' (decIHᴾ S*ᴾ idh ih))
                      ih)
                  xᴾ
                  eq'
                  ih

        elimᴾ : ∀ {x}(xᴾ : Uᴾ x) → Pᴾ xᴾ (IR.elim S* P met x)
        elimᴾ {x} xᴾ = IIR.elim (encSigᴾ S*ᴾ idh) encPᴾ encMetᴾ xᴾ

        -- here we need to have extra proof that:
        --     1. "IR.wrap" is *definitionally* injective (proven by application of IR.unwrap to both sides)
        --     2. encF0 S*ᴾ idh is injective
        elimβᴾ : ∀ {x : F0 S*} (xᴾ : F0ᴾ S*ᴾ x)
                 → elimᴾ (wrapᴾ xᴾ) ≡ metᴾ xᴾ (mapIHᴾ S*ᴾ xᴾ elimᴾ)
        elimβᴾ {x} xᴾ with decF0ᴾ S*ᴾ idh (encF0ᴾ S*ᴾ idh xᴾ)
        ... | x , refl , xᴾ' , eq' with encF0ᴾ-inj S*ᴾ idh _ _ eq' | eq'
        ... | refl | refl =
           let lhs = metᴾ xᴾ (decIHᴾ S*ᴾ idh (IIR.mapIH (encSigᴾ S*ᴾ idh) Uᴾ Elᴾ _ encPᴾ (encF0ᴾ S*ᴾ idh xᴾ) elimᴾ))
               rhs = metᴾ xᴾ (mapIHᴾ S*ᴾ xᴾ elimᴾ)
           in {!lhs7!}

-- metᴾ xᴾ (decIHᴾ S*ᴾ idh elimᴾ) ≡ metᴾ xᴾ (mapIHᴾ S*ᴾ xᴾ elimᴾ)


--------------------------------------------------------------------------------
