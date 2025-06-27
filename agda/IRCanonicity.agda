
open import Lib
open import UIP
import PlainIR
import IndexedIR

module IRCanonicity (i : Level) (j : Level) (O : Set j) (Oᴾ : O → Set j) where

  module IR = PlainIR i j O

  data Sigᴾ : IR.Sig → Set (lsuc i ⊔ j) where
    ι : ∀ {o}(oᴾ : Oᴾ o) → Sigᴾ (IR.ι o)
    σ : ∀ {A} (Aᴾ : A → Set i){S : A → IR.Sig}      (Sᴾ : ∀ {a} → Aᴾ a → Sigᴾ (S a)) → Sigᴾ (IR.σ A S)
    δ : ∀ {A} (Aᴾ : A → Set i){S : (A → O) → IR.Sig}(Sᴾ : ∀ {f} → (∀ a → Aᴾ a → Oᴾ (f a)) → Sigᴾ (S f)) → Sigᴾ (IR.δ A S)

  module _ {S* : IR.Sig}(S*ᴾ : Sigᴾ S*) where

    module IIR = IndexedIR {i}{j}{i} (IR.IR S*) (Oᴾ ∘ IR.El)

    El = IR.El {S*}
    U  = IR.IR S*
    F0 = λ S → IR.F0 S U El
    F1 = λ S → IR.F1 S {U} {El}

    -- subsignatures of S* as snoc lists
    data Path : ∀ {S} → Sigᴾ S → Set (lsuc i ⊔ lsuc j) where
      idh : Path S*ᴾ
      σ<  : ∀ {A : Set i}{Aᴾ : A → Set i}{S : A → IR.Sig}{Sᴾ : ∀ {a} → Aᴾ a → Sigᴾ (S a)}
            → Path (σ Aᴾ Sᴾ)
            → ∀ a (aᴾ : Aᴾ a)
            → Path {S a} (Sᴾ aᴾ)
      δ<  : ∀ {A : Set i}{Aᴾ : A → Set i}
              {S : (A → O) → IR.Sig}{Sᴾ : ∀ {f} → (∀ a → Aᴾ a → Oᴾ (f a)) → Sigᴾ (S f)}
            → Path (δ Aᴾ Sᴾ)
            → ∀ (f : A → U)(fᴾ : ∀ a → Aᴾ a → Oᴾ (El (f a)))
            → Path (Sᴾ fᴾ)

    PathF0 : ∀ {S}{Sᴾ} → Path {S} Sᴾ → F0 S → F0 S*
    PathF0 idh           acc = acc
    PathF0 (σ< hom a aᴾ) acc = PathF0 hom (a , acc)
    PathF0 (δ< hom f fᴾ) acc = PathF0 hom (f , acc)

    PathF1 : ∀ {S}{Sᴾ}(hom : Path {S} Sᴾ) → ∀ {x} → F1 S x ≡ F1 S* (PathF0 hom x)
    PathF1 idh           = refl
    PathF1 (σ< hom a aᴾ) = PathF1 hom
    PathF1 (δ< hom f fᴾ) = PathF1 hom

    Sigᴾ→ : ∀ {S}(Sᴾ : Sigᴾ S) → Path Sᴾ → IIR.Sig
    Sigᴾ→ (ι oᴾ)            hom = the {!IIR.ι!} $ IIR.ι (IR.wrap (PathF0 hom (lift tt))) (tr Oᴾ (PathF1 hom) oᴾ)
    Sigᴾ→ (σ {A} Aᴾ {S} Sᴾ) hom = IIR.σ A λ a → IIR.σ (Aᴾ a) λ aᴾ → Sigᴾ→ (Sᴾ aᴾ) (σ< hom a aᴾ)
    Sigᴾ→ (δ {A} Aᴾ Sᴾ)     hom = IIR.σ (A → U) λ f → IIR.δ (∃ Aᴾ) (λ{(a , _) → f a}) λ fᴾ →
                                  Sigᴾ→ (Sᴾ λ a aᴾ → fᴾ (a , aᴾ)) (δ< hom f (λ a aᴾ → fᴾ (a , aᴾ)))

    S*ᴾ' = Sigᴾ→ S*ᴾ idh

    IRᴾ : U → Set i
    IRᴾ = IIR.IIR S*ᴾ'

    Elᴾ : {x : U} → IRᴾ x → Oᴾ (El x)
    Elᴾ = IIR.El

    F0ᴾ : ∀ {S} → Sigᴾ S → F0 S → Set i
    F0ᴾ (ι oᴾ)    x       = Lift _ ⊤
    F0ᴾ (σ Aᴾ Sᴾ) (a , t) = Σ (Aᴾ a) λ aᴾ → F0ᴾ (Sᴾ aᴾ) t
    F0ᴾ (δ Aᴾ Sᴾ) (f , t) = Σ (∀ a → Aᴾ a → IRᴾ (f a)) λ fᴾ → F0ᴾ (Sᴾ λ a aᴾ → Elᴾ (fᴾ a aᴾ)) t

    F1ᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → Oᴾ (F1 S x)
    F1ᴾ (ι oᴾ)    xᴾ        = oᴾ
    F1ᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) = F1ᴾ (Sᴾ aᴾ) tᴾ
    F1ᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) = F1ᴾ (Sᴾ _) tᴾ

    F0ᴾ' : ∀ {S} Sᴾ (hom : Path {S} Sᴾ) (x : U) → Set i
    F0ᴾ' Sᴾ hom x = ∃ λ x' → IR.wrap (PathF0 hom x') ≡ x × F0ᴾ Sᴾ x'

    F0ᴾ→ : ∀ {S} Sᴾ (hom : Path {S} Sᴾ){x} → F0ᴾ' Sᴾ hom x → IIR.F0 (Sigᴾ→ Sᴾ hom) IRᴾ Elᴾ x
    F0ᴾ→ (ι oᴾ)    hom (x , eq , xᴾ) .lower                    = eq
    F0ᴾ→ (σ Aᴾ Sᴾ) hom ((a , x) , eq , (aᴾ , xᴾ)) .₁           = a
    F0ᴾ→ (σ Aᴾ Sᴾ) hom ((a , x) , eq , aᴾ , xᴾ) .₂ .₁          = aᴾ
    F0ᴾ→ (σ Aᴾ Sᴾ) hom ((a , x) , eq , aᴾ , xᴾ) .₂ .₂          = F0ᴾ→ (Sᴾ aᴾ) (σ< hom a aᴾ) (x , eq , xᴾ)
    F0ᴾ→ (δ Aᴾ Sᴾ) hom ((f , x) , eq , fᴾ , xᴾ) .₁ a           = f a
    F0ᴾ→ (δ Aᴾ Sᴾ) hom ((f , x) , eq , fᴾ , xᴾ) .₂ .₁ (a , aᴾ) = fᴾ a aᴾ
    F0ᴾ→ (δ Aᴾ Sᴾ) hom ((f , x) , eq , fᴾ , xᴾ) .₂ .₂          = F0ᴾ→ (Sᴾ λ a aᴾ → Elᴾ (fᴾ a aᴾ)) (δ< hom f λ a aᴾ → Elᴾ (fᴾ a aᴾ)) (x , eq , xᴾ)

    F0ᴾ→' : ∀ {S} Sᴾ (hom : Path {S} Sᴾ){x} → F0ᴾ Sᴾ x → IIR.F0 (Sigᴾ→ Sᴾ hom) IRᴾ Elᴾ (IR.wrap (PathF0 hom x))
    F0ᴾ→' Sᴾ hom {x} xᴾ = F0ᴾ→ Sᴾ hom (x , refl , xᴾ)

    F0ᴾ← : ∀ {S} Sᴾ (hom : Path {S} Sᴾ){x} → IIR.F0 (Sigᴾ→ Sᴾ hom) IRᴾ Elᴾ x → F0ᴾ' Sᴾ hom x
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

    F0ᴾrl : ∀ {S} Sᴾ (hom : Path {S} Sᴾ){x}(xᴾ : IIR.F0 (Sigᴾ→ Sᴾ hom) IRᴾ Elᴾ x)
            → F0ᴾ→ Sᴾ hom (F0ᴾ← Sᴾ hom xᴾ) ≡ xᴾ
    F0ᴾrl (ι oᴾ)    hom xᴾ            = refl
    F0ᴾrl (σ Aᴾ Sᴾ) hom (a , aᴾ , xᴾ) = ap (λ x → a , aᴾ , x) (F0ᴾrl (Sᴾ aᴾ) (σ< hom a aᴾ) xᴾ)
    F0ᴾrl (δ Aᴾ Sᴾ) hom (f , fᴾ , xᴾ) = ap (λ x → f , fᴾ , x) (F0ᴾrl (Sᴾ _)  (δ< hom f _) xᴾ)

    F0ᴾlr : ∀ {S} Sᴾ (hom : Path {S} Sᴾ){x}(xᴾ : F0ᴾ' Sᴾ hom x)
            → F0ᴾ← Sᴾ hom (F0ᴾ→ Sᴾ hom xᴾ) ≡ xᴾ
    F0ᴾlr (ι oᴾ)    hom xᴾ = refl
    F0ᴾlr (σ Aᴾ Sᴾ) hom ((a , x) , eq , aᴾ , xᴾ) =
      ap (λ x → (a , x .₁) , x .₂ .₁ , aᴾ , x .₂ .₂) (F0ᴾlr (Sᴾ aᴾ) (σ< hom a aᴾ) (x , eq , xᴾ))
    F0ᴾlr (δ Aᴾ Sᴾ) hom ((f , x) , eq , fᴾ , xᴾ) =
      ap (λ x → (f , x .₁) , x .₂ .₁ , fᴾ , x .₂ .₂) (F0ᴾlr (Sᴾ _) (δ< hom f _) (x , eq , xᴾ))

    wrapᴾ : {x : F0 S*}(xᴾ : F0ᴾ S*ᴾ x) → IRᴾ (IR.wrap x)
    wrapᴾ {x} xᴾ = IIR.wrap (F0ᴾ→' S*ᴾ idh xᴾ)

    Path* : ∀ {S}{Sᴾ : Sigᴾ S} → Path Sᴾ → Set (lsuc i ⊔ lsuc j)
    Path* idh                   = Lift _ ⊤
    Path* (σ< hom a aᴾ)         = Path* hom
    Path* (δ< {A}{Aᴾ} hom f fᴾ) =
      Σ (∀ a → Aᴾ a → IRᴾ (f a)) λ fᴾ* → (fᴾ ≡ λ a aᴾ → Elᴾ (fᴾ* _ aᴾ)) × Path* hom

    PathF0ᴾ : ∀ {S}{Sᴾ}(hom : Path {S} Sᴾ)(homᴾ : Path* hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x) → F0ᴾ S*ᴾ (PathF0 hom x)
    PathF0ᴾ idh           homᴾ                xᴾ = xᴾ
    PathF0ᴾ (σ< hom a aᴾ) homᴾ                xᴾ = PathF0ᴾ hom homᴾ (aᴾ , xᴾ)
    PathF0ᴾ (δ< hom f fᴾ) (fᴾ* , refl , homᴾ) xᴾ = PathF0ᴾ hom homᴾ (fᴾ* , xᴾ)

    PathF1ᴾ : ∀ {S}{Sᴾ}(hom : Path {S} Sᴾ)(homᴾ : Path* hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x)
             → tr Oᴾ (PathF1 hom {x}) (F1ᴾ Sᴾ xᴾ) ≡ F1ᴾ  S*ᴾ (PathF0ᴾ hom homᴾ xᴾ)
    PathF1ᴾ idh           homᴾ              xᴾ = refl
    PathF1ᴾ (σ< hom a aᴾ) homᴾ              xᴾ = PathF1ᴾ hom homᴾ (aᴾ , xᴾ)
    PathF1ᴾ (δ< hom f fᴾ) (_ , refl , homᴾ) xᴾ = PathF1ᴾ hom homᴾ (_ , xᴾ)

    F1ᴾ→ : ∀ {S} Sᴾ (hom : Path {S} Sᴾ)(homᴾ : Path* hom){x : F0 S}(xᴾ : F0ᴾ Sᴾ x)
          → IIR.F1 (Sigᴾ→ Sᴾ hom) (F0ᴾ→' Sᴾ hom xᴾ) ≡ F1ᴾ S*ᴾ (PathF0ᴾ hom homᴾ xᴾ)
    F1ᴾ→ (ι oᴾ)    hom homᴾ        xᴾ        = PathF1ᴾ hom homᴾ xᴾ
    F1ᴾ→ (σ Aᴾ Sᴾ) hom homᴾ {a , x}(aᴾ , xᴾ) = F1ᴾ→ (Sᴾ aᴾ) (σ< hom a aᴾ) homᴾ xᴾ
    F1ᴾ→ (δ Aᴾ Sᴾ) hom homᴾ {f , x}(fᴾ , xᴾ) = F1ᴾ→ (Sᴾ _) (δ< hom f _) (fᴾ , refl , homᴾ) xᴾ

    Elᴾ≡ : ∀ {x} (xᴾ : F0ᴾ S*ᴾ x) → Elᴾ (wrapᴾ xᴾ) ≡ F1ᴾ S*ᴾ xᴾ
    Elᴾ≡ xᴾ = F1ᴾ→ S*ᴾ idh (lift tt) xᴾ

    module _ {k}(P : U → Set k)(Pᴾ : ∀ {x} → IRᴾ x → P x → Set k) where

      IH    = λ S → IR.IH S {U} {El} P
      mapIH = λ S → IR.mapIH S {U} {El} P

      IHᴾ : ∀ {S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x) → IH S x → Set (i ⊔ k)
      IHᴾ (ι oᴾ)    xᴾ        w       = Lift _ ⊤
      IHᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) w       = IHᴾ (Sᴾ aᴾ) tᴾ w
      IHᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) (g , w) =
        (∀ a aᴾ → Pᴾ (fᴾ a aᴾ) (g a)) × IHᴾ (Sᴾ (λ a aᴾ → Elᴾ (fᴾ a aᴾ))) tᴾ w

      mapIHᴾ : ∀{S}(Sᴾ : Sigᴾ S){x}(xᴾ : F0ᴾ Sᴾ x){f}(fᴾ : ∀ {x} xᴾ → Pᴾ xᴾ (f x)) → IHᴾ Sᴾ xᴾ (mapIH S f x)
      mapIHᴾ (ι oᴾ)    tᴾ        fᴾ = lift tt
      mapIHᴾ (σ Aᴾ Sᴾ) (aᴾ , tᴾ) gᴾ = mapIHᴾ (Sᴾ aᴾ) tᴾ gᴾ
      mapIHᴾ (δ Aᴾ Sᴾ) (fᴾ , tᴾ) gᴾ = (λ a aᴾ → gᴾ (fᴾ a aᴾ)) , mapIHᴾ (Sᴾ _) tᴾ gᴾ

      module _  (met  : ∀ (x : F0 S*) → IH S* x → P (IR.wrap x))
                (metᴾ : ∀ {x}(xᴾ : F0ᴾ S*ᴾ x){ih}(ihᴾ : IHᴾ S*ᴾ xᴾ ih) → Pᴾ {IR.wrap x} (wrapᴾ xᴾ) (met x ih)) where

        Pᴾ' : ∀ {x} → IRᴾ x → Set k
        Pᴾ' {x} xᴾ = Pᴾ xᴾ (IR.elim S* P met x)

        Pᴾ'' : (∃ λ x → IRᴾ x × P x) → Set k
        Pᴾ'' (x , xᴾ , w) = Pᴾ xᴾ w

        IHᴾ← : ∀ {S} Sᴾ{x}(hom : Path {S} Sᴾ){xᴾ : IIR.F0 (Sigᴾ→ Sᴾ hom) IRᴾ Elᴾ x}
                 → IIR.IH (Sigᴾ→ Sᴾ hom) Pᴾ' xᴾ
                 → IHᴾ Sᴾ (F0ᴾ← Sᴾ hom xᴾ .₂ .₂) (mapIH S (IR.elim S* P met) (F0ᴾ← Sᴾ hom xᴾ .₁))
        IHᴾ← (ι oᴾ) hom ihᴾ .lower = tt
        IHᴾ← (σ Aᴾ Sᴾ) hom {a , aᴾ , xᴾ} ihᴾ = IHᴾ← (Sᴾ aᴾ) (σ< hom a aᴾ) ihᴾ
        IHᴾ← (δ Aᴾ Sᴾ) hom {f , fᴾ , xᴾ} ihᴾ .₁ a aᴾ = ihᴾ .₁ (a , aᴾ)
        IHᴾ← (δ Aᴾ Sᴾ) hom {f , fᴾ , xᴾ} ihᴾ .₂ = IHᴾ← (Sᴾ _) (δ< hom f _) (ihᴾ .₂)


        metᴾ' : ∀ {x} (xᴾ : IIR.F0 (Sigᴾ→ S*ᴾ idh) IRᴾ Elᴾ x) → IIR.IH (Sigᴾ→ S*ᴾ idh) Pᴾ' xᴾ
                 → Pᴾ' (IIR.wrap xᴾ)
        metᴾ' {x} xᴾ ih =
          tr (λ xᴾ → Pᴾ' (IIR.wrap xᴾ))
             (F0ᴾrl S*ᴾ idh xᴾ)
             (J (λ _ eq → Pᴾ' (IIR.wrap (F0ᴾ→ S*ᴾ idh (F0ᴾ← S*ᴾ idh xᴾ .₁ , eq , F0ᴾ← S*ᴾ idh xᴾ .₂ .₂))))
                (F0ᴾ← S*ᴾ idh xᴾ .₂ .₁)
                (metᴾ (F0ᴾ← S*ᴾ idh xᴾ .₂ .₂) (IHᴾ← S*ᴾ idh ih)))

        mapIH-trip :
          ∀ {S} Sᴾ {x} (hom : Path {S} Sᴾ) (h : ∀ {i}(x : IRᴾ i) → Pᴾ' x)(xᴾ : F0ᴾ Sᴾ x)
          →
          tr (λ xᴾ → IHᴾ Sᴾ (xᴾ .₂ .₂) (mapIH S (IR.elim S* P met) (xᴾ .₁)))
             (F0ᴾlr Sᴾ hom (x , refl , xᴾ))
             (IHᴾ← Sᴾ hom (IIR.mapIH (Sigᴾ→ Sᴾ hom) Pᴾ' h (F0ᴾ→' Sᴾ hom xᴾ)))
          ≡ mapIHᴾ Sᴾ xᴾ h
        mapIH-trip (ι oᴾ) hom xᴾ f = refl

        mapIH-trip (σ {A} Aᴾ {S} Sᴾ) {a , x} hom h (aᴾ , xᴾ) =
            tr-∘ (λ xᴾ₁ →
                   IHᴾ (Sᴾ (xᴾ₁ .₂ .₂ .₁)) (xᴾ₁ .₂ .₂ .₂)
                  (mapIH (IR.σ A S) (IR.elim S* P met) (xᴾ₁ .₁)))
                (λ x₁ → (a , x₁ .₁) , x₁ .₂ .₁ , aᴾ , x₁ .₂ .₂)
                (F0ᴾlr (Sᴾ aᴾ) (σ< hom a aᴾ) (x , refl , xᴾ))
                _
          ◼ mapIH-trip (Sᴾ aᴾ) (σ< hom a aᴾ) h xᴾ

        mapIH-trip (δ {A} Aᴾ {S} Sᴾ) {f , x} hom h (fᴾ , xᴾ) =
             tr-∘ (λ xᴾ₁ → IHᴾ (δ Aᴾ Sᴾ) (xᴾ₁ .₂ .₂) (mapIH (IR.δ A S) (IR.elim S* P met) (xᴾ₁ .₁)))
                  (λ x₁ → (f , x₁ .₁) , x₁ .₂ .₁ , fᴾ , x₁ .₂ .₂)
                  (F0ᴾlr (Sᴾ (λ a aᴾ → Elᴾ (fᴾ a aᴾ)))(δ< hom f (λ a aᴾ → Elᴾ (fᴾ a aᴾ))) (x , refl , xᴾ))
                  _
           ◼ Σ≡
             (   tr-×₁ (F0ᴾlr (Sᴾ _) (δ< hom f _) (x , refl , xᴾ)) _
               ◼ tr-const (F0ᴾlr (Sᴾ _) (δ< hom f _) (x , refl , xᴾ)) _
             )
             (  tr-const (tr-×₁ (F0ᴾlr (Sᴾ (λ a aᴾ → Elᴾ (fᴾ a aᴾ))) (δ< hom f (λ a aᴾ → Elᴾ
                          (fᴾ a aᴾ))) (x , refl , xᴾ)) (IHᴾ← (δ Aᴾ Sᴾ) hom (IIR.mapIH (Sigᴾ→ (δ Aᴾ
                          Sᴾ) hom) Pᴾ' h (F0ᴾ→' (δ Aᴾ Sᴾ) hom (fᴾ , xᴾ))) .₁ , IHᴾ← (δ Aᴾ Sᴾ) hom
                          (IIR.mapIH (Sigᴾ→ (δ Aᴾ Sᴾ) hom) Pᴾ' h (F0ᴾ→' (δ Aᴾ Sᴾ) hom (fᴾ , xᴾ)))
                          .₂) ◼ tr-const (F0ᴾlr (Sᴾ (λ a aᴾ → Elᴾ (fᴾ a aᴾ))) (δ< hom f (λ a aᴾ →
                          Elᴾ (fᴾ a aᴾ))) (x , refl , xᴾ)) (IHᴾ← (δ Aᴾ Sᴾ) hom (IIR.mapIH (Sigᴾ→ (δ
                          Aᴾ Sᴾ) hom) Pᴾ' h (F0ᴾ→' (δ Aᴾ Sᴾ) hom (fᴾ , xᴾ))) .₁)) _
              ◼ tr-×₂ (F0ᴾlr (Sᴾ (λ a aᴾ → Elᴾ (fᴾ a aᴾ)))
                        (δ< hom f (λ a aᴾ → Elᴾ (fᴾ a aᴾ))) (x , refl , xᴾ)) _
              ◼ mapIH-trip (Sᴾ _) (δ< hom f _) h xᴾ
             )


        elimᴾ : ∀ {x}(xᴾ : IRᴾ x) → Pᴾ xᴾ (IR.elim S* P met x)
        elimᴾ {x} xᴾ = IIR.elim (Sigᴾ→ S*ᴾ idh) Pᴾ' metᴾ' xᴾ

        metᴾ-tr : ∀ {x : F0 S*} (xᴾ : F0ᴾ S*ᴾ x) →
                tr (λ xᴾ → Pᴾ (wrapᴾ (xᴾ .₂ .₂)) (met (xᴾ .₁) (mapIH S* (IR.elim S* P met) (xᴾ .₁))))
                   (F0ᴾlr S*ᴾ idh (x , refl , xᴾ))
                   (metᴾ (F0ᴾ← S*ᴾ idh (F0ᴾ→' S*ᴾ idh xᴾ) .₂ .₂)
                         (IHᴾ← S*ᴾ idh (IIR.mapIH (Sigᴾ→ S*ᴾ idh) Pᴾ' elimᴾ (F0ᴾ→' S*ᴾ idh xᴾ))))
              ≡ metᴾ xᴾ (tr
                   (λ xᴾ₁ → IHᴾ S*ᴾ (xᴾ₁ .₂ .₂) (mapIH S* (IR.elim S* P met) (xᴾ₁ .₁) ))
                   (F0ᴾlr S*ᴾ idh (x , refl , xᴾ))
                   (IHᴾ← S*ᴾ idh (IIR.mapIH (Sigᴾ→ S*ᴾ idh) Pᴾ' elimᴾ (F0ᴾ→' S*ᴾ idh xᴾ) )))
        metᴾ-tr {x} xᴾ =
          J (λ xᴾ* eq →
                tr (λ xᴾ₁ → Pᴾ (wrapᴾ (xᴾ₁ .₂ .₂)) (met (xᴾ₁ .₁) (mapIH S* (IR.elim S* P met) (xᴾ₁ .₁))))
                   eq
                   (metᴾ (F0ᴾ← S*ᴾ idh (F0ᴾ→' S*ᴾ idh xᴾ) .₂ .₂)
                         (IHᴾ← S*ᴾ idh (IIR.mapIH (Sigᴾ→ S*ᴾ idh) Pᴾ' elimᴾ (F0ᴾ→' S*ᴾ idh xᴾ))))
              ≡ metᴾ (xᴾ* .₂ .₂)
                     (tr (λ xᴾ₁ → IHᴾ S*ᴾ (xᴾ₁ .₂ .₂) (mapIH S* (IR.elim S* P met) (xᴾ₁ .₁)))
                         eq
                         (IHᴾ← S*ᴾ idh (IIR.mapIH (Sigᴾ→ S*ᴾ idh) Pᴾ' elimᴾ (F0ᴾ→' S*ᴾ idh xᴾ) ))))
           (F0ᴾlr S*ᴾ idh (x , refl , xᴾ))
           refl

        elimβᴾ : ∀ {x : F0 S*} (xᴾ : F0ᴾ S*ᴾ x)
                 → elimᴾ (wrapᴾ xᴾ) ≡ metᴾ xᴾ (mapIHᴾ S*ᴾ xᴾ elimᴾ)
        elimβᴾ {x} xᴾ =

          let lhs = metᴾ' (F0ᴾ→' S*ᴾ idh xᴾ) (IIR.mapIH S*ᴾ' Pᴾ' (IIR.elim S*ᴾ' Pᴾ' metᴾ') (F0ᴾ→' S*ᴾ idh xᴾ))
              rhs = metᴾ xᴾ (mapIHᴾ S*ᴾ xᴾ elimᴾ)

          in the (lhs ≡ rhs) $
                 coe-coe
                    (ap (λ xᴾ₁ → Pᴾ (IIR.wrap xᴾ₁) (met x (IR.mapIH S* P (IR.elim S* P met) x)))
                        (F0ᴾrl S*ᴾ idh (F0ᴾ→ S*ᴾ idh (x , refl , xᴾ))))
                    (ap (λ x₁ → Pᴾ (IIR.wrap (F0ᴾ→ S*ᴾ idh (F0ᴾ← S*ᴾ idh (F0ᴾ→ S*ᴾ idh (x , refl , xᴾ)) .₁ , x₁ .₂ , F0ᴾ← S*ᴾ
                                      idh (F0ᴾ→ S*ᴾ idh (x , refl , xᴾ)) .₂ .₂)))
                                   (IR.elim S* P met (x₁ .₁)))
                        (contr (F0ᴾ← S*ᴾ idh (F0ᴾ→ S*ᴾ idh (x , refl , xᴾ)) .₂ .₁)))
                    _
               ◼ coe-UIP
                    (  ap (λ x₁ → Pᴾ (IIR.wrap (F0ᴾ→ S*ᴾ idh (F0ᴾ← S*ᴾ idh (F0ᴾ→ S*ᴾ idh (x , refl , xᴾ)) .₁ , x₁ .₂ , F0ᴾ← S*ᴾ idh
                                   (F0ᴾ→ S*ᴾ idh (x , refl , xᴾ)) .₂ .₂))) (IR.elim S* P met (x₁ .₁)))
                          (contr (F0ᴾ← S*ᴾ idh (F0ᴾ→ S*ᴾ idh (x , refl , xᴾ)) .₂ .₁))
                     ◼ ap (λ xᴾ₁ → Pᴾ (IIR.wrap xᴾ₁) (met x (IR.mapIH S* P (IR.elim S* P met) x)))
                          (F0ᴾrl S*ᴾ idh (F0ᴾ→ S*ᴾ idh (x , refl , xᴾ))))
                    (ap (λ xᴾ₁ → Pᴾ (IIR.wrap (F0ᴾ→ S*ᴾ idh (xᴾ₁ .₁ , refl , xᴾ₁ .₂ .₂)))
                                    (met (xᴾ₁ .₁) (IR.mapIH S* P (IR.elim S* P met) (xᴾ₁ .₁))))
                        (F0ᴾlr S*ᴾ idh (x , refl , xᴾ)))
               ◼ metᴾ-tr xᴾ
               ◼ ap (metᴾ xᴾ) (mapIH-trip S*ᴾ idh elimᴾ xᴾ)


--------------------------------------------------------------------------------
