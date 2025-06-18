

open import Lib
open import UIP
import PlainIR
import IndexedIR

module ShallowIRTranslation4 (ext : Level) (ol : Level) (O : Set ol) (Oᴾ : O → Set ol) where

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

    Sigᴾ→ : ∀ {S}(Sᴾ : Sigᴾ S) → Hom Sᴾ → IIR.Sig
    Sigᴾ→ (ι oᴾ)            hom = IIR.ι (IR.wrap (HomF0 hom (lift tt))) (tr Oᴾ (HomF1 hom) oᴾ)
    Sigᴾ→ (σ {A} Aᴾ {S} Sᴾ) hom = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → Sigᴾ→ (Sᴾ aᴾ) (σ< hom a aᴾ)
    Sigᴾ→ (δ {A} Aᴾ Sᴾ)     hom = IIR.σ (A → U) λ f → IIR.δ (∃ Aᴾ) (λ aaᴾ → f (aaᴾ .₁)) λ fᴾ →
                                  Sigᴾ→ (Sᴾ λ aᴾ → fᴾ (_ , aᴾ)) (δ< hom f (λ aᴾ → fᴾ (_ , aᴾ)))

    S*ᴾ' = Sigᴾ→ S*ᴾ idh

    Uᴾ : U → Set ext
    Uᴾ = IIR.U S*ᴾ'

    Elᴾ : {x : U} → Uᴾ x → Oᴾ (El x)
    Elᴾ = IIR.El S*ᴾ'

    F0ᴾ : ∀ {S} → Sigᴾ S → F0 S → Set ext
    F0ᴾ (ι oᴾ)    x       = Lift _ ⊤
    F0ᴾ (σ Aᴾ Sᴾ) (a , t) = Σ (Aᴾ a) λ aᴾ → F0ᴾ (Sᴾ aᴾ) t
    F0ᴾ (δ Aᴾ Sᴾ) (f , t) = Σ (∀ {a} → Aᴾ a → Uᴾ (f a)) λ fᴾ → F0ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) t

    F1ᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → Oᴾ (F1 S x)
    F1ᴾ (ι oᴾ)    xᴾ        = oᴾ
    F1ᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) = F1ᴾ (Sᴾ aᴾ) tᴾ
    F1ᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) = F1ᴾ (Sᴾ (Elᴾ ∘ fᴾ)) tᴾ

    F0ᴾ' : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ) (x : U) → Set ext
    F0ᴾ' Sᴾ hom x = ∃ λ x' → IR.wrap (HomF0 hom x') ≡ x × F0ᴾ Sᴾ x'

    F0ᴾ→ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x} → F0ᴾ Sᴾ x → IIR.F0 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ (IR.wrap (HomF0 hom x))
    F0ᴾ→ (ι oᴾ)    hom xᴾ .lower                        = refl
    F0ᴾ→ (σ Aᴾ Sᴾ) hom {a , x} (aᴾ , xᴾ) .₁             = a
    F0ᴾ→ (σ Aᴾ Sᴾ) hom {a , x} (aᴾ , xᴾ) .₂ .₁          = aᴾ
    F0ᴾ→ (σ Aᴾ Sᴾ) hom {a , x} (aᴾ , xᴾ) .₂ .₂          = F0ᴾ→ (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ
    F0ᴾ→ (δ Aᴾ Sᴾ) hom {f , x} (fᴾ , xᴾ) .₁             = f
    F0ᴾ→ (δ Aᴾ Sᴾ) hom {f , x} (fᴾ , xᴾ) .₂ .₁ (a , aᴾ) = fᴾ aᴾ
    F0ᴾ→ (δ Aᴾ Sᴾ) hom {f , x} (fᴾ , xᴾ) .₂ .₂          = F0ᴾ→ (Sᴾ (Elᴾ ∘ fᴾ)) (δ< hom f (Elᴾ ∘ fᴾ)) xᴾ

    F0ᴾ← : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x} → IIR.F0 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ x → F0ᴾ' Sᴾ hom x
    F0ᴾ← (ι oᴾ)    hom (lift xᴾ) .₁ .lower           = tt
    F0ᴾ← (ι oᴾ)    hom (lift xᴾ) .₂ .₁               = xᴾ
    F0ᴾ← (ι oᴾ)    hom (lift xᴾ) .₂ .₂ .lower        = tt
    F0ᴾ← (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) .₁ .₁           = a
    F0ᴾ← (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) .₁ .₂           = F0ᴾ← (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ .₁
    F0ᴾ← (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) .₂ .₁           = F0ᴾ← (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ .₂ .₁
    F0ᴾ← (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) .₂ .₂ .₁        = aᴾ
    F0ᴾ← (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) .₂ .₂ .₂        = F0ᴾ← (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ .₂ .₂
    F0ᴾ← (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) .₁ .₁ a         = f a
    F0ᴾ← (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) .₁ .₂           = F0ᴾ← (Sᴾ _) (δ< hom f (λ aᴾ → Elᴾ (fᴾ (_ , aᴾ)))) xᴾ .₁
    F0ᴾ← (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) .₂ .₁           = F0ᴾ← (Sᴾ _) (δ< hom f (λ aᴾ → Elᴾ (fᴾ (_ , aᴾ)))) xᴾ .₂ .₁
    F0ᴾ← (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) .₂ .₂ .₁ {a} aᴾ = fᴾ (a , aᴾ)
    F0ᴾ← (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) .₂ .₂ .₂        = F0ᴾ← (Sᴾ _) (δ< hom f (λ aᴾ → Elᴾ (fᴾ (_ , aᴾ)))) xᴾ .₂ .₂

    F0ᴾlr : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ){x}(xᴾ : IIR.F0 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ x)
            → tr (IIR.F0 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ) (F0ᴾ← Sᴾ hom xᴾ .₂ .₁) (F0ᴾ→ Sᴾ hom (F0ᴾ← Sᴾ hom xᴾ .₂ .₂))
            ≡ xᴾ
    F0ᴾlr (ι oᴾ)    hom xᴾ = ap lift UIP
    F0ᴾlr (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) = {!!}
    F0ᴾlr (δ Aᴾ Sᴾ) hom xᴾ = {!!}

    wrapᴾ : {x : F0 S*}(xᴾ : F0ᴾ S*ᴾ x) → Uᴾ (IR.wrap x)
    wrapᴾ {x} xᴾ = IIR.wrap (F0ᴾ→ S*ᴾ idh xᴾ)

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

    F1ᴾ→ : ∀ {S} Sᴾ (hom : Hom {S} Sᴾ)(homᴾ : Hom* hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x)
          → IIR.F1 (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ (F0ᴾ→ Sᴾ hom xᴾ) ≡ F1ᴾ S*ᴾ (HomF0ᴾ hom homᴾ xᴾ)
    F1ᴾ→ (ι oᴾ)    hom homᴾ        xᴾ        = HomF1ᴾ hom homᴾ xᴾ
    F1ᴾ→ (σ Aᴾ Sᴾ) hom homᴾ {a , x}(aᴾ , xᴾ) = F1ᴾ→ (Sᴾ aᴾ) (σ< hom a aᴾ) homᴾ xᴾ
    F1ᴾ→ (δ Aᴾ Sᴾ) hom homᴾ {f , x}(fᴾ , xᴾ) = F1ᴾ→ (Sᴾ (Elᴾ ∘ fᴾ)) (δ< hom f (Elᴾ ∘ fᴾ)) (fᴾ , refl , homᴾ) xᴾ

    Elᴾ≡ : ∀ {x} (xᴾ : F0ᴾ S*ᴾ x) → Elᴾ (wrapᴾ xᴾ) ≡ F1ᴾ S*ᴾ xᴾ
    Elᴾ≡ xᴾ = F1ᴾ→ S*ᴾ idh (lift tt) xᴾ

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

        Pᴾ' : ∀ {x} → Uᴾ x → Set j
        Pᴾ' {x} xᴾ = Pᴾ xᴾ (IR.elim S* P met x)

        IHᴾ← : ∀ {S} Sᴾ{x xᴾ}(hom : Hom {S} Sᴾ)
                 → (ih : IIR.IH (Sigᴾ→ Sᴾ hom) Uᴾ Elᴾ Pᴾ' (F0ᴾ→ Sᴾ hom {x} xᴾ))
                 → IHᴾ Sᴾ xᴾ (mapIH S x (IR.elim S* P met))
        IHᴾ← (ι oᴾ)    hom ih = ih
        IHᴾ← (σ Aᴾ Sᴾ) {a , x}{aᴾ , xᴾ} hom ih = IHᴾ← (Sᴾ aᴾ) (σ< hom a aᴾ) ih
        IHᴾ← (δ Aᴾ Sᴾ) {f , x}{fᴾ , xᴾ} hom (hyp , ih) =
          (λ aᴾ → hyp (_ , aᴾ)) , IHᴾ← (Sᴾ (Elᴾ ∘ fᴾ)) (δ< hom f (Elᴾ ∘ fᴾ)) ih

        metᴾ' : ∀ {x} (xᴾ : IIR.F0 (Sigᴾ→ S*ᴾ idh) Uᴾ Elᴾ x) → IIR.IH (Sigᴾ→ S*ᴾ idh) Uᴾ Elᴾ Pᴾ' xᴾ
                 → Pᴾ' (IIR.wrap xᴾ)
        metᴾ' {x} xᴾ ih =
          let x' , eq , x'ᴾ = F0ᴾ← S*ᴾ idh xᴾ
          in {!!}
           -- let x' , eq , xᴾ' , eq' = F0ᴾ← S*ᴾ idh xᴾ
           -- in J (λ x eq → (xᴾ  : IIR.F0 (Sigᴾ→ S*ᴾ idh) Uᴾ Elᴾ x)
           --                (eq' : tr (IIR.F0 (Sigᴾ→ S*ᴾ idh) Uᴾ Elᴾ) eq (F0ᴾ→ S*ᴾ idh xᴾ') ≡ xᴾ)
           --                (ih  : IIR.IH (Sigᴾ→ S*ᴾ idh) Uᴾ Elᴾ Pᴾ' xᴾ)
           --                 → Pᴾ' (IIR.wrap xᴾ))
           --        eq
           --        (λ xᴾ eq' ih →
           --          J (λ xᴾ eq' → IIR.IH (Sigᴾ→ S*ᴾ idh) Uᴾ Elᴾ Pᴾ' xᴾ → Pᴾ' (IIR.wrap xᴾ))
           --            eq'
           --            (λ ih → metᴾ xᴾ' (IHᴾ← S*ᴾ idh ih))
           --            ih)
           --        xᴾ
           --        eq'
           --        ih

--         elimᴾ : ∀ {x}(xᴾ : Uᴾ x) → Pᴾ xᴾ (IR.elim S* P met x)
--         elimᴾ {x} xᴾ = IIR.elim (Sigᴾ→ S*ᴾ idh) encPᴾ encMetᴾ xᴾ

--         -- here we need to have extra proof that:
--         --     1. "IR.wrap" is *definitionally* injective (proven by application of IR.unwrap to both sides)
--         --     2. encF0 S*ᴾ idh is injective
--         elimβᴾ : ∀ {x : F0 S*} (xᴾ : F0ᴾ S*ᴾ x)
--                  → elimᴾ (wrapᴾ xᴾ) ≡ metᴾ xᴾ (mapIHᴾ S*ᴾ xᴾ elimᴾ)
--         elimβᴾ {x} xᴾ with decF0ᴾ S*ᴾ idh (encF0ᴾ S*ᴾ idh xᴾ)
--         ... | x , refl , xᴾ' , eq' with encF0ᴾ-inj S*ᴾ idh _ _ eq' | eq'
--         ... | refl | refl =
--            let lhs = metᴾ xᴾ (decIHᴾ S*ᴾ idh (IIR.mapIH (Sigᴾ→ S*ᴾ idh) Uᴾ Elᴾ _ encPᴾ (encF0ᴾ S*ᴾ idh xᴾ) elimᴾ))
--                rhs = metᴾ xᴾ (mapIHᴾ S*ᴾ xᴾ elimᴾ)
--            in {!!}

-- -- metᴾ xᴾ (decIHᴾ S*ᴾ idh elimᴾ) ≡ metᴾ xᴾ (mapIHᴾ S*ᴾ xᴾ elimᴾ)


-- --------------------------------------------------------------------------------
