
open import Lib
open import UIP
import PlainIR
import IndexedIR

module IRCanonicity (i : Level) (j : Level) (O : Set j) (Oᵒ : O → Set j) where

  import PlainIR as IR
  open PlainIR hiding (Sig)
  Sig = IR.Sig i {j} O

  data Sigᵒ : Sig → Set (suc i ⊔ j) where
    ιᵒ : ∀ {o}(oᵒ : Oᵒ o) → Sigᵒ (IR.ι o)
    σᵒ : ∀ {A} (Aᵒ : A → Set i){S : A → Sig}      (Sᵒ : ∀ {a} → Aᵒ a → Sigᵒ (S a)) → Sigᵒ (IR.σ A S)
    δᵒ : ∀ {A} (Aᵒ : A → Set i){S : (A → O) → Sig}(Sᵒ : ∀ {f} → (∀ a → Aᵒ a → Oᵒ (f a)) → Sigᵒ (S f)) → Sigᵒ (IR.δ A S)

  module _ {S* : Sig}(S*ᵒ : Sigᵒ S*) where

    module IIR = IndexedIR
    SigIIR = IIR.Sig i (IR S*) (Oᵒ ∘ El)

    data Path : ∀ {S} → Sigᵒ S → Set (suc i ⊔ suc j) where
      here : Path S*ᵒ
      in-σ  : ∀ {A : Set i}{Aᵒ : A → Set i}{S : A → Sig}{Sᵒ : ∀ {a} → Aᵒ a → Sigᵒ (S a)}
            → Path (σᵒ Aᵒ Sᵒ)
            → ∀ a (aᵒ : Aᵒ a)
            → Path {S a} (Sᵒ aᵒ)
      in-δ  : ∀ {A : Set i}{Aᵒ : A → Set i}
              {S : (A → O) → Sig}{Sᵒ : ∀ {f} → (∀ a → Aᵒ a → Oᵒ (f a)) → Sigᵒ (S f)}
            → Path (δᵒ Aᵒ Sᵒ)
            → ∀ (f : A → IR S*)(fᵒ : ∀ a → Aᵒ a → Oᵒ (El (f a)))
            → Path (Sᵒ fᵒ)

    push : ∀ {S}{Sᵒ} → Path {S} Sᵒ → E S (IR S*) El → E S* (IR S*) El
    push here          acc = acc
    push (in-σ p a aᵒ) acc = push p (a , acc)
    push (in-δ p f fᵒ) acc = push p (f , acc)

    F-push : ∀ {S}{Sᵒ}(p : Path {S} Sᵒ) → ∀ {x} → F  x ≡ F {S = S*} (push p x)
    F-push here           = refl
    F-push (in-σ p a aᵒ) = F-push p
    F-push (in-δ p f fᵒ) = F-push p

    ⌞_⌟ : ∀ {S}(Sᵒ : Sigᵒ S) → Path Sᵒ → SigIIR

    ⌞ ιᵒ oᵒ            ⌟ p = IIR.ι (IR.intro (push p tt)) (tr Oᵒ (F-push p) oᵒ)
    ⌞ σᵒ {A} Aᵒ {S} Sᵒ ⌟ p = IIR.σ A λ a → IIR.σ (Aᵒ a) λ aᵒ → ⌞ Sᵒ aᵒ ⌟ (in-σ p a aᵒ)
    ⌞ δᵒ {A} Aᵒ Sᵒ     ⌟ p = IIR.σ (A → IR S*) λ f → IIR.δ (∃ Aᵒ) (λ{(a , _) → f a}) λ fᵒ →
                                   ⌞ Sᵒ (λ a aᵒ → fᵒ (a , aᵒ)) ⌟ (in-δ p f (λ a aᵒ → fᵒ (a , aᵒ)))

    ⌞S*⌟ = ⌞ S*ᵒ ⌟ here

    IRᵒ : IR S* → Set i
    IRᵒ = IIR.IIR ⌞S*⌟

    Elᵒ : ∀ {x} → IRᵒ x → Oᵒ (El x)
    Elᵒ = IIR.El

    Eᵒ : ∀ {S} → Sigᵒ S → E S (IR S*) El → Set i
    Eᵒ (ιᵒ oᵒ)    x       = ⊤
    Eᵒ (σᵒ Aᵒ Sᵒ) (a , t) = Σ (Aᵒ a) λ aᵒ → Eᵒ (Sᵒ aᵒ) t
    Eᵒ (δᵒ Aᵒ Sᵒ) (f , t) = Σ (∀ a → Aᵒ a → IRᵒ (f a)) λ fᵒ → Eᵒ (Sᵒ λ a aᵒ → Elᵒ (fᵒ a aᵒ)) t

    ⌞E⌟ : ∀ {S} {Sᵒ} (p : Path {S} Sᵒ) (x : IR S*) → Set i
    ⌞E⌟ {Sᵒ = Sᵒ} p x = ∃ λ x' → IR.intro (push p x') ≡ x × Eᵒ Sᵒ x'

    Eᵒ→ : ∀ {S} {Sᵒ} (p : Path {S} Sᵒ){x : IR S*} → ⌞E⌟ {Sᵒ = Sᵒ} p x → IIR.E (⌞ Sᵒ ⌟ p) IRᵒ Elᵒ x
    Eᵒ→ {Sᵒ = ιᵒ oᵒ   } p (x , eq , xᵒ)             .↓                = eq
    Eᵒ→ {Sᵒ = σᵒ Aᵒ Sᵒ} p ((a , x) , eq , (aᵒ , xᵒ)) .fst             = a
    Eᵒ→ {Sᵒ = σᵒ Aᵒ Sᵒ} p ((a , x) , eq , aᵒ , xᵒ) .snd .fst          = aᵒ
    Eᵒ→ {Sᵒ = σᵒ Aᵒ Sᵒ} p ((a , x) , eq , aᵒ , xᵒ) .snd .snd          = Eᵒ→ (in-σ p a aᵒ) (x , eq , xᵒ)
    Eᵒ→ {Sᵒ = δᵒ Aᵒ Sᵒ} p ((f , x) , eq , fᵒ , xᵒ) .fst a             = f a
    Eᵒ→ {Sᵒ = δᵒ Aᵒ Sᵒ} p ((f , x) , eq , fᵒ , xᵒ) .snd .fst (a , aᵒ) = fᵒ a aᵒ
    Eᵒ→ {Sᵒ = δᵒ Aᵒ Sᵒ} p ((f , x) , eq , fᵒ , xᵒ) .snd .snd          = Eᵒ→ (in-δ p f λ a aᵒ → Elᵒ (fᵒ a aᵒ)) (x , eq , xᵒ)

    Eᵒ→' : ∀ {S} {Sᵒ} (p : Path {S} Sᵒ){x} → Eᵒ Sᵒ x → IIR.E (⌞ Sᵒ ⌟ p) IRᵒ Elᵒ (IR.intro (push p x))
    Eᵒ→' p {x} xᵒ = Eᵒ→ p (x , refl , xᵒ)

    Eᵒ← : ∀ {S Sᵒ} (p : Path {S} Sᵒ){x} → IIR.E (⌞ Sᵒ ⌟ p) IRᵒ Elᵒ x → ⌞E⌟ p x
    Eᵒ← {Sᵒ = ιᵒ oᵒ   } p (↑ xᵒ)        .fst                = tt
    Eᵒ← {Sᵒ = ιᵒ oᵒ   } p (↑ xᵒ)        .snd .fst           = xᵒ
    Eᵒ← {Sᵒ = ιᵒ oᵒ   } p (↑ xᵒ)        .snd .snd           = tt
    Eᵒ← {Sᵒ = σᵒ Aᵒ Sᵒ} p (a , aᵒ , xᵒ) .fst .fst           = a
    Eᵒ← {Sᵒ = σᵒ Aᵒ Sᵒ} p (a , aᵒ , xᵒ) .fst .snd           = Eᵒ← (in-σ p a aᵒ) xᵒ .fst
    Eᵒ← {Sᵒ = σᵒ Aᵒ Sᵒ} p (a , aᵒ , xᵒ) .snd .fst           = Eᵒ← (in-σ p a aᵒ) xᵒ .snd .fst
    Eᵒ← {Sᵒ = σᵒ Aᵒ Sᵒ} p (a , aᵒ , xᵒ) .snd .snd .fst      = aᵒ
    Eᵒ← {Sᵒ = σᵒ Aᵒ Sᵒ} p (a , aᵒ , xᵒ) .snd .snd .snd      = Eᵒ← (in-σ p a aᵒ) xᵒ .snd .snd
    Eᵒ← {Sᵒ = δᵒ Aᵒ Sᵒ} p (f , fᵒ , xᵒ) .fst .fst a         = f a
    Eᵒ← {Sᵒ = δᵒ Aᵒ Sᵒ} p (f , fᵒ , xᵒ) .fst .snd           = Eᵒ← (in-δ p f (λ a aᵒ → Elᵒ (fᵒ (_ , aᵒ)))) xᵒ .fst
    Eᵒ← {Sᵒ = δᵒ Aᵒ Sᵒ} p (f , fᵒ , xᵒ) .snd .fst           = Eᵒ← (in-δ p f (λ a aᵒ → Elᵒ (fᵒ (_ , aᵒ)))) xᵒ .snd .fst
    Eᵒ← {Sᵒ = δᵒ Aᵒ Sᵒ} p (f , fᵒ , xᵒ) .snd .snd .fst a aᵒ = fᵒ (a , aᵒ)
    Eᵒ← {Sᵒ = δᵒ Aᵒ Sᵒ} p (f , fᵒ , xᵒ) .snd .snd .snd      = Eᵒ← (in-δ p f (λ a aᵒ → Elᵒ (fᵒ (_ , aᵒ)))) xᵒ .snd .snd

    Eᵒlr : ∀ {S} Sᵒ (p : Path {S} Sᵒ){x}(xᵒ : ⌞E⌟ p x) → Eᵒ← {S}{Sᵒ} p (Eᵒ→ p xᵒ) ≡ xᵒ
    Eᵒlr (ιᵒ oᵒ)    p xᵒ = refl
    Eᵒlr (σᵒ Aᵒ Sᵒ) p ((a , x) , eq , aᵒ , xᵒ) =
      ap (λ x → (a , x .fst) , x .snd .fst , aᵒ , x .snd .snd) (Eᵒlr (Sᵒ aᵒ) (in-σ p a aᵒ) (x , eq , xᵒ))
    Eᵒlr (δᵒ Aᵒ Sᵒ) p ((f , x) , eq , fᵒ , xᵒ) =
      ap (λ x → (f , x .fst) , x .snd .fst , fᵒ , x .snd .snd) (Eᵒlr (Sᵒ _) (in-δ p f _) (x , eq , xᵒ))

    Eᵒrl : ∀ {S} Sᵒ (p : Path {S} Sᵒ){x}(xᵒ : IIR.E (⌞ Sᵒ ⌟ p) IRᵒ Elᵒ x) → Eᵒ→ {S} {Sᵒ} p (Eᵒ← p xᵒ) ≡ xᵒ
    Eᵒrl (ιᵒ oᵒ)    p xᵒ            = refl
    Eᵒrl (σᵒ Aᵒ Sᵒ) p (a , aᵒ , xᵒ) = ap (λ x → a , aᵒ , x) (Eᵒrl (Sᵒ aᵒ) (in-σ p a aᵒ) xᵒ)
    Eᵒrl (δᵒ Aᵒ Sᵒ) p (f , fᵒ , xᵒ) = ap (λ x → f , fᵒ , x) (Eᵒrl (Sᵒ _)  (in-δ p f _) xᵒ)

    introᵒ : ∀ {x : E S* (IR S*) El}(xᵒ : Eᵒ S*ᵒ x) → IRᵒ (IR.intro x)
    introᵒ xᵒ = IIR.intro (Eᵒ→' here xᵒ)

    restrict : ∀ {S}{Sᵒ : Sigᵒ S} → Path Sᵒ → Set (suc i ⊔ suc j)
    restrict here                    = ⊤
    restrict (in-σ p a aᵒ)         = restrict p
    restrict (in-δ {A}{Aᵒ} p f fᵒ) = Σ (∀ a → Aᵒ a → IRᵒ (f a)) λ fᵒ* → (fᵒ ≡ λ a aᵒ → Elᵒ (fᵒ* _ aᵒ)) × restrict p

    pushᵒ : ∀ {S}{Sᵒ}(p : Path {S} Sᵒ)(pᵒ : restrict p){x : E S (IR S*) El}(xᵒ : Eᵒ Sᵒ x) → Eᵒ S*ᵒ (push p x)
    pushᵒ here            pᵒ                xᵒ = xᵒ
    pushᵒ (in-σ p a aᵒ) pᵒ                xᵒ = pushᵒ p pᵒ (aᵒ , xᵒ)
    pushᵒ (in-δ p f fᵒ) (fᵒ* , refl , pᵒ) xᵒ = pushᵒ p pᵒ (fᵒ* , xᵒ)

    Fᵒ : ∀ {S}{Sᵒ : Sigᵒ S}{x}(xᵒ : Eᵒ Sᵒ x) → Oᵒ (F x)
    Fᵒ {Sᵒ = ιᵒ oᵒ}    xᵒ        = oᵒ
    Fᵒ {Sᵒ = σᵒ Aᵒ Sᵒ} (aᵒ , tᵒ) = Fᵒ tᵒ
    Fᵒ {Sᵒ = δᵒ Aᵒ Sᵒ} (fᵒ , tᵒ) = Fᵒ tᵒ

    F-pushᵒ : ∀ {S}{Sᵒ}(p : Path {S} Sᵒ)(pᵒ : restrict p){x : E S (IR S*) El}(xᵒ : Eᵒ Sᵒ x)
             → tr Oᵒ (F-push p {x}) (Fᵒ xᵒ) ≡ Fᵒ (pushᵒ p pᵒ xᵒ)
    F-pushᵒ here            pᵒ              xᵒ = refl
    F-pushᵒ (in-σ p a aᵒ) pᵒ              xᵒ = F-pushᵒ p pᵒ (aᵒ , xᵒ)
    F-pushᵒ (in-δ p f fᵒ) (_ , refl , pᵒ) xᵒ = F-pushᵒ p pᵒ (_ , xᵒ)

    ⌞F⌟ : ∀ {S}{Sᵒ} (p : Path {S} Sᵒ)(pᵒ : restrict p){x : E S (IR S*) El}(xᵒ : Eᵒ Sᵒ x)
          → IIR.F (Eᵒ→' p xᵒ) ≡ Fᵒ (pushᵒ p pᵒ xᵒ)
    ⌞F⌟ {Sᵒ = ιᵒ oᵒ   } p pᵒ xᵒ        = F-pushᵒ p pᵒ xᵒ
    ⌞F⌟ {Sᵒ = σᵒ Aᵒ Sᵒ} p pᵒ (aᵒ , xᵒ) = ⌞F⌟ (in-σ p _ aᵒ) pᵒ xᵒ
    ⌞F⌟ {Sᵒ = δᵒ Aᵒ Sᵒ} p pᵒ (fᵒ , xᵒ) = ⌞F⌟ (in-δ p _ _) (fᵒ , refl , pᵒ) xᵒ

    El-introᵒ : ∀ {x} (xᵒ : Eᵒ S*ᵒ x) → Elᵒ (introᵒ xᵒ) ≡ Fᵒ xᵒ
    El-introᵒ = ⌞F⌟ here tt

    module _ {k}(P : IR S* → Set k)(Pᵒ : ∀ {x} → IRᵒ x → P x → Set k) where

      IHᵒ : ∀ {S}{Sᵒ : Sigᵒ S}{x}(xᵒ : Eᵒ Sᵒ x) → IH P x → Set (i ⊔ k)
      IHᵒ {Sᵒ = ιᵒ oᵒ   } xᵒ        w       = ⊤
      IHᵒ {Sᵒ = σᵒ Aᵒ Sᵒ} (aᵒ , tᵒ) w       = IHᵒ tᵒ w
      IHᵒ {Sᵒ = δᵒ Aᵒ Sᵒ} (fᵒ , tᵒ) (g , w) = (∀ a aᵒ → Pᵒ (fᵒ a aᵒ) (g a)) × IHᵒ tᵒ w

      mapᵒ : ∀{S}{Sᵒ : Sigᵒ S}{f : (x : IR S*) → P x}(fᵒ : ∀ {x : IR S*} (xᵒ : IRᵒ x)
             → Pᵒ xᵒ (f x)){x : E S (IR S*) El}(xᵒ : Eᵒ Sᵒ x) → IHᵒ xᵒ (map f x)
      mapᵒ {Sᵒ = ιᵒ oᵒ   } gᵒ tᵒ         = tt
      mapᵒ {Sᵒ = σᵒ Aᵒ Sᵒ} gᵒ (aᵒ , tᵒ)  = mapᵒ gᵒ tᵒ
      mapᵒ {Sᵒ = δᵒ Aᵒ Sᵒ} gᵒ (fᵒ , tᵒ)  = (λ a aᵒ → gᵒ (fᵒ a aᵒ)) , mapᵒ gᵒ tᵒ

      module _  (f  : ∀ (x : E S* (IR S*) El) → IH P x → P (IR.intro x))
                (fᵒ : ∀ {x}(xᵒ : Eᵒ S*ᵒ x){ih}(ihᵒ : IHᵒ xᵒ ih) → Pᵒ {IR.intro x} (introᵒ xᵒ) (f x ih)) where

        ⌞P⌟ : ∀ {x} → IRᵒ x → Set k
        ⌞P⌟ {x} xᵒ = Pᵒ xᵒ (IR.elim P f x)

        IH← : ∀ {S} {Sᵒ} (p : Path {S} Sᵒ){x}{xᵒ : IIR.E (⌞ Sᵒ ⌟ p) IRᵒ Elᵒ x}
                 → IIR.IH ⌞P⌟ xᵒ
                 → let (t' , _ , tᵒ') = Eᵒ← p xᵒ in
                   IHᵒ tᵒ' (map (IR.elim P f) t')
        IH← {Sᵒ = ιᵒ oᵒ   } p {_}              ihᵒ           = tt
        IH← {Sᵒ = σᵒ Aᵒ Sᵒ} p {_}{a , aᵒ , xᵒ} ihᵒ           = IH← (in-σ p a aᵒ) ihᵒ
        IH← {Sᵒ = δᵒ Aᵒ Sᵒ} p {_}{f , fᵒ , xᵒ} ihᵒ .fst a aᵒ = ihᵒ .fst (a , aᵒ)
        IH← {Sᵒ = δᵒ Aᵒ Sᵒ} p {_}{f , fᵒ , xᵒ} ihᵒ .snd      = IH← (in-δ p f _) (ihᵒ .snd)

        ⌞f⌟ : ∀ {x} (xᵒ : IIR.E (⌞ S*ᵒ ⌟ here) IRᵒ Elᵒ x) → IIR.IH ⌞P⌟ xᵒ → ⌞P⌟ (IIR.intro xᵒ)
        ⌞f⌟ {x} xᵒ ih =
          tr (λ xᵒ → ⌞P⌟ (IIR.intro xᵒ))
             (Eᵒrl S*ᵒ here xᵒ)
             (J (λ _ eq → ⌞P⌟ (IIR.intro (Eᵒ→ here (Eᵒ← here xᵒ .fst , eq , Eᵒ← here xᵒ .snd .snd))))
                (Eᵒ← here xᵒ .snd .fst)
                (fᵒ (Eᵒ← here xᵒ .snd .snd) (IH← here ih)))

        ⌞map⌟ :
          ∀ {S} Sᵒ {x} (p : Path {S} Sᵒ) (g : ∀ {i}(x : IRᵒ i) → ⌞P⌟ x)(xᵒ : Eᵒ Sᵒ x)
          →
          tr (λ xᵒ → IHᵒ (xᵒ .snd .snd) (map (IR.elim P f) (xᵒ .fst)))
             (Eᵒlr Sᵒ p (x , refl , xᵒ))
             (IH← p (IIR.map g (Eᵒ→' p xᵒ)))
          ≡ mapᵒ g xᵒ
        ⌞map⌟ (ιᵒ oᵒ) p xᵒ f = refl
        ⌞map⌟ (σᵒ {A} Aᵒ {S} Sᵒ) {a , x} p h (aᵒ , xᵒ) =
                 tr-∘ {B = ⌞E⌟ p (intro (push p (a , x)))}
                      (λ x → IHᵒ (x .snd .snd .snd) (map (elim P f) (x .fst .snd)))
                      (λ x → (a , x .fst) , x .snd .fst , aᵒ , x .snd .snd)
                      (Eᵒlr (Sᵒ aᵒ) (in-σ p a aᵒ) (x , refl , xᵒ))
                      _
               ◼ ⌞map⌟ (Sᵒ aᵒ) (in-σ p a aᵒ) h xᵒ

        ⌞map⌟ (δᵒ {A} Aᵒ {S} Sᵒ) {g , x} p h (gᵒ , xᵒ) =
           {!tr-∘

                !}


--              tr-∘ (λ xᵒ₁ → IHᵒ (δ Aᵒ Sᵒ) (xᵒ₁ .snd .snd) (mapIH (IR.δ A S) (IR.elim S* P f) (xᵒ₁ .fst)))
--                   (λ x₁ → (f , x₁ .fst) , x₁ .snd .fst , fᵒ , x₁ .snd .snd)
--                   (Eᵒlr (Sᵒ (λ a aᵒ → Elᵒ (fᵒ a aᵒ)))(in-δ p f (λ a aᵒ → Elᵒ (fᵒ a aᵒ))) (x , refl , xᵒ))
--                   _
--            ◼ Σ≡
--              (   tr-×₁ (Eᵒlr (Sᵒ _) (in-δ p f _) (x , refl , xᵒ)) _
--                ◼ tr-const (Eᵒlr (Sᵒ _) (in-δ p f _) (x , refl , xᵒ)) _
--              )
--              (  tr-const (tr-×₁ (Eᵒlr (Sᵒ (λ a aᵒ → Elᵒ (fᵒ a aᵒ))) (in-δ p f (λ a aᵒ → Elᵒ
--                           (fᵒ a aᵒ))) (x , refl , xᵒ)) (IH← (δ Aᵒ Sᵒ) p (IIR.mapIH (Sigᵒ→ (δ Aᵒ
--                           Sᵒ) p) ⌞P⌟ h (Eᵒ→' (δ Aᵒ Sᵒ) p (fᵒ , xᵒ))) .fst , IH← (δ Aᵒ Sᵒ) p
--                           (IIR.mapIH (Sigᵒ→ (δ Aᵒ Sᵒ) p) ⌞P⌟ h (Eᵒ→' (δ Aᵒ Sᵒ) p (fᵒ , xᵒ)))
--                           .snd) ◼ tr-const (Eᵒlr (Sᵒ (λ a aᵒ → Elᵒ (fᵒ a aᵒ))) (in-δ p f (λ a aᵒ →
--                           Elᵒ (fᵒ a aᵒ))) (x , refl , xᵒ)) (IH← (δ Aᵒ Sᵒ) p (IIR.mapIH (Sigᵒ→ (δ
--                           Aᵒ Sᵒ) p) ⌞P⌟ h (Eᵒ→' (δ Aᵒ Sᵒ) p (fᵒ , xᵒ))) .fst)) _
--               ◼ tr-×₂ (Eᵒlr (Sᵒ (λ a aᵒ → Elᵒ (fᵒ a aᵒ)))
--                         (in-δ p f (λ a aᵒ → Elᵒ (fᵒ a aᵒ))) (x , refl , xᵒ)) _
--               ◼ ⌞map⌟ (Sᵒ _) (in-δ p f _) h xᵒ
--              )


--         elimᵒ : ∀ {x}(xᵒ : IRᵒ x) → Pᵒ xᵒ (IR.elim S* P f x)
--         elimᵒ {x} xᵒ = IIR.elim (Sigᵒ→ S*ᵒ here) ⌞P⌟ fᵒ' xᵒ

--         fᵒ-tr : ∀ {x : E S (IR S*) El*} (xᵒ : Eᵒ S*ᵒ x) →
--                 tr (λ xᵒ → Pᵒ (introᵒ (xᵒ .snd .snd)) (f (xᵒ .fst) (mapIH S* (IR.elim S* P f) (xᵒ .fst))))
--                    (Eᵒlr S*ᵒ here (x , refl , xᵒ))
--                    (fᵒ (Eᵒ← S*ᵒ here (Eᵒ→' S*ᵒ here xᵒ) .snd .snd)
--                          (IH← S*ᵒ here (IIR.mapIH (Sigᵒ→ S*ᵒ here) ⌞P⌟ elimᵒ (Eᵒ→' S*ᵒ here xᵒ))))
--               ≡ fᵒ xᵒ (tr
--                    (λ xᵒ₁ → IHᵒ S*ᵒ (xᵒ₁ .snd .snd) (mapIH S* (IR.elim S* P f) (xᵒ₁ .fst) ))
--                    (Eᵒlr S*ᵒ here (x , refl , xᵒ))
--                    (IH← S*ᵒ here (IIR.mapIH (Sigᵒ→ S*ᵒ here) ⌞P⌟ elimᵒ (Eᵒ→' S*ᵒ here xᵒ) )))
--         fᵒ-tr {x} xᵒ =
--           J (λ xᵒ* eq →
--                 tr (λ xᵒ₁ → Pᵒ (introᵒ (xᵒ₁ .snd .snd)) (f (xᵒ₁ .fst) (mapIH S* (IR.elim S* P f) (xᵒ₁ .fst))))
--                    eq
--                    (fᵒ (Eᵒ← S*ᵒ here (Eᵒ→' S*ᵒ here xᵒ) .snd .snd)
--                          (IH← S*ᵒ here (IIR.mapIH (Sigᵒ→ S*ᵒ here) ⌞P⌟ elimᵒ (Eᵒ→' S*ᵒ here xᵒ))))
--               ≡ fᵒ (xᵒ* .snd .snd)
--                      (tr (λ xᵒ₁ → IHᵒ S*ᵒ (xᵒ₁ .snd .snd) (mapIH S* (IR.elim S* P f) (xᵒ₁ .fst)))
--                          eq
--                          (IH← S*ᵒ here (IIR.mapIH (Sigᵒ→ S*ᵒ here) ⌞P⌟ elimᵒ (Eᵒ→' S*ᵒ here xᵒ) ))))
--            (Eᵒlr S*ᵒ here (x , refl , xᵒ))
--            refl

--         elimβᵒ : ∀ {x : E S (IR S*) El*} (xᵒ : Eᵒ S*ᵒ x)
--                  → elimᵒ (introᵒ xᵒ) ≡ fᵒ xᵒ (mapᵒ S*ᵒ elimᵒ xᵒ)
--         elimβᵒ {x} xᵒ =

--           let lhs = fᵒ' (Eᵒ→' S*ᵒ here xᵒ) (IIR.mapIH S*ᵒ' ⌞P⌟ (IIR.elim S*ᵒ' ⌞P⌟ fᵒ') (Eᵒ→' S*ᵒ here xᵒ))
--               rhs = fᵒ xᵒ (mapᵒ S*ᵒ elimᵒ xᵒ)

--           in the (lhs ≡ rhs) $
--                  coe-coe
--                     (ap (λ xᵒ₁ → Pᵒ (IIR.intro xᵒ₁) (f x (IR.mapIH S* P (IR.elim S* P f) x)))
--                         (Eᵒrl S*ᵒ here (Eᵒ→ S*ᵒ here (x , refl , xᵒ))))
--                     (ap (λ x₁ → Pᵒ (IIR.intro (Eᵒ→ S*ᵒ here (Eᵒ← S*ᵒ here (Eᵒ→ S*ᵒ here (x , refl , xᵒ)) .fst , x₁ .snd , Eᵒ← S*ᵒ
--                                       here (Eᵒ→ S*ᵒ here (x , refl , xᵒ)) .snd .snd)))
--                                    (IR.elim S* P f (x₁ .fst)))
--                         (contr (Eᵒ← S*ᵒ here (Eᵒ→ S*ᵒ here (x , refl , xᵒ)) .snd .fst)))
--                     _
--                ◼ coe-UIP
--                     (  ap (λ x₁ → Pᵒ (IIR.intro (Eᵒ→ S*ᵒ here (Eᵒ← S*ᵒ here (Eᵒ→ S*ᵒ here (x , refl , xᵒ)) .fst , x₁ .snd , Eᵒ← S*ᵒ here
--                                    (Eᵒ→ S*ᵒ here (x , refl , xᵒ)) .snd .snd))) (IR.elim S* P f (x₁ .fst)))
--                           (contr (Eᵒ← S*ᵒ here (Eᵒ→ S*ᵒ here (x , refl , xᵒ)) .snd .fst))
--                      ◼ ap (λ xᵒ₁ → Pᵒ (IIR.intro xᵒ₁) (f x (IR.mapIH S* P (IR.elim S* P f) x)))
--                           (Eᵒrl S*ᵒ here (Eᵒ→ S*ᵒ here (x , refl , xᵒ))))
--                     (ap (λ xᵒ₁ → Pᵒ (IIR.intro (Eᵒ→ S*ᵒ here (xᵒ₁ .fst , refl , xᵒ₁ .snd .snd)))
--                                     (f (xᵒ₁ .fst) (IR.mapIH S* P (IR.elim S* P f) (xᵒ₁ .fst))))
--                         (Eᵒlr S*ᵒ here (x , refl , xᵒ)))
--                ◼ fᵒ-tr xᵒ
--                ◼ ap (fᵒ xᵒ) (⌞map⌟ S*ᵒ here elimᵒ xᵒ)


-- --------------------------------------------------------------------------------
