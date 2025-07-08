
open import Lib
open import UIP
import PlainIR
import IndexedIR

module IRCanonicity (i : Level) (j : Level) (O : Set j) (Oᵒ : O → Set j) where


  -- Section 4.3.2
  ----------------------------------------------------------------------------------------------------

  import PlainIR as IR
  open PlainIR hiding (Sig)
  Sig = IR.Sig i {j} O

  data Sigᵒ : Sig → Set (suc i ⊔ j) where
    ιᵒ : ∀ {o}(oᵒ : Oᵒ o) → Sigᵒ (IR.ι o)
    σᵒ : ∀ {A} (Aᵒ : A → Set i){S : A → Sig}      (Sᵒ : ∀ {a} → Aᵒ a → Sigᵒ (S a)) → Sigᵒ (IR.σ A S)
    δᵒ : ∀ {A} (Aᵒ : A → Set i){S : (A → O) → Sig}(Sᵒ : ∀ {f} → (∀ a → Aᵒ a → Oᵒ (f a)) → Sigᵒ (S f)) → Sigᵒ (IR.δ A S)


  -- Section 4.3.3
  ----------------------------------------------------------------------------------------------------
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

    -- Definition 4.3
    ⌞_⌟ : ∀ {S}(Sᵒ : Sigᵒ S) → Path Sᵒ → SigIIR
    ⌞ ιᵒ oᵒ            ⌟ p = IIR.ι (IR.intro (push p tt)) (tr Oᵒ (F-push p) oᵒ)
    ⌞ σᵒ {A} Aᵒ {S} Sᵒ ⌟ p = IIR.σ A λ a → IIR.σ (Aᵒ a) λ aᵒ → ⌞ Sᵒ aᵒ ⌟ (in-σ p a aᵒ)
    ⌞ δᵒ {A} Aᵒ Sᵒ     ⌟ p = IIR.σ (A → IR S*) λ f → IIR.δ (∃ Aᵒ) (λ{(a , _) → f a}) λ fᵒ →
                                   ⌞ Sᵒ (λ a aᵒ → fᵒ (a , aᵒ)) ⌟ (in-δ p f (λ a aᵒ → fᵒ (a , aᵒ)))

    ⌞S*⌟ = ⌞ S*ᵒ ⌟ here

    -- Definition 4.5
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

    E→ : ∀ {S} {Sᵒ} (p : Path {S} Sᵒ){x : IR S*} → ⌞E⌟ {Sᵒ = Sᵒ} p x → IIR.E (⌞ Sᵒ ⌟ p) IRᵒ Elᵒ x
    E→ {Sᵒ = ιᵒ oᵒ   } p (x , eq , xᵒ)             .↓                = eq
    E→ {Sᵒ = σᵒ Aᵒ Sᵒ} p ((a , x) , eq , (aᵒ , xᵒ)) .fst             = a
    E→ {Sᵒ = σᵒ Aᵒ Sᵒ} p ((a , x) , eq , aᵒ , xᵒ) .snd .fst          = aᵒ
    E→ {Sᵒ = σᵒ Aᵒ Sᵒ} p ((a , x) , eq , aᵒ , xᵒ) .snd .snd          = E→ (in-σ p a aᵒ) (x , eq , xᵒ)
    E→ {Sᵒ = δᵒ Aᵒ Sᵒ} p ((f , x) , eq , fᵒ , xᵒ) .fst a             = f a
    E→ {Sᵒ = δᵒ Aᵒ Sᵒ} p ((f , x) , eq , fᵒ , xᵒ) .snd .fst (a , aᵒ) = fᵒ a aᵒ
    E→ {Sᵒ = δᵒ Aᵒ Sᵒ} p ((f , x) , eq , fᵒ , xᵒ) .snd .snd          = E→ (in-δ p f λ a aᵒ → Elᵒ (fᵒ a aᵒ)) (x , eq , xᵒ)

    E→' : ∀ {S} {Sᵒ} (p : Path {S} Sᵒ){x} → Eᵒ Sᵒ x → IIR.E (⌞ Sᵒ ⌟ p) IRᵒ Elᵒ (IR.intro (push p x))
    E→' p {x} xᵒ = E→ p (x , refl , xᵒ)

    E← : ∀ {S Sᵒ} (p : Path {S} Sᵒ){x} → IIR.E (⌞ Sᵒ ⌟ p) IRᵒ Elᵒ x → ⌞E⌟ p x
    E← {Sᵒ = ιᵒ oᵒ   } p (↑ xᵒ)        .fst                = tt
    E← {Sᵒ = ιᵒ oᵒ   } p (↑ xᵒ)        .snd .fst           = xᵒ
    E← {Sᵒ = ιᵒ oᵒ   } p (↑ xᵒ)        .snd .snd           = tt
    E← {Sᵒ = σᵒ Aᵒ Sᵒ} p (a , aᵒ , xᵒ) .fst .fst           = a
    E← {Sᵒ = σᵒ Aᵒ Sᵒ} p (a , aᵒ , xᵒ) .fst .snd           = E← (in-σ p a aᵒ) xᵒ .fst
    E← {Sᵒ = σᵒ Aᵒ Sᵒ} p (a , aᵒ , xᵒ) .snd .fst           = E← (in-σ p a aᵒ) xᵒ .snd .fst
    E← {Sᵒ = σᵒ Aᵒ Sᵒ} p (a , aᵒ , xᵒ) .snd .snd .fst      = aᵒ
    E← {Sᵒ = σᵒ Aᵒ Sᵒ} p (a , aᵒ , xᵒ) .snd .snd .snd      = E← (in-σ p a aᵒ) xᵒ .snd .snd
    E← {Sᵒ = δᵒ Aᵒ Sᵒ} p (f , fᵒ , xᵒ) .fst .fst a         = f a
    E← {Sᵒ = δᵒ Aᵒ Sᵒ} p (f , fᵒ , xᵒ) .fst .snd           = E← (in-δ p f (λ a aᵒ → Elᵒ (fᵒ (_ , aᵒ)))) xᵒ .fst
    E← {Sᵒ = δᵒ Aᵒ Sᵒ} p (f , fᵒ , xᵒ) .snd .fst           = E← (in-δ p f (λ a aᵒ → Elᵒ (fᵒ (_ , aᵒ)))) xᵒ .snd .fst
    E← {Sᵒ = δᵒ Aᵒ Sᵒ} p (f , fᵒ , xᵒ) .snd .snd .fst a aᵒ = fᵒ (a , aᵒ)
    E← {Sᵒ = δᵒ Aᵒ Sᵒ} p (f , fᵒ , xᵒ) .snd .snd .snd      = E← (in-δ p f (λ a aᵒ → Elᵒ (fᵒ (_ , aᵒ)))) xᵒ .snd .snd

    E←→ : ∀ {S} Sᵒ (p : Path {S} Sᵒ){x}(xᵒ : ⌞E⌟ p x) → E← {S}{Sᵒ} p (E→ p xᵒ) ≡ xᵒ
    E←→ (ιᵒ oᵒ)    p xᵒ = refl
    E←→ (σᵒ Aᵒ Sᵒ) p ((a , x) , eq , aᵒ , xᵒ) =
      ap (λ x → (a , x .fst) , x .snd .fst , aᵒ , x .snd .snd) (E←→ (Sᵒ aᵒ) (in-σ p a aᵒ) (x , eq , xᵒ))
    E←→ (δᵒ Aᵒ Sᵒ) p ((f , x) , eq , fᵒ , xᵒ) =
      ap (λ x → (f , x .fst) , x .snd .fst , fᵒ , x .snd .snd) (E←→ (Sᵒ _) (in-δ p f _) (x , eq , xᵒ))

    E→← : ∀ {S} Sᵒ (p : Path {S} Sᵒ){x}(xᵒ : IIR.E (⌞ Sᵒ ⌟ p) IRᵒ Elᵒ x) → E→ {S} {Sᵒ} p (E← p xᵒ) ≡ xᵒ
    E→← (ιᵒ oᵒ)    p xᵒ            = refl
    E→← (σᵒ Aᵒ Sᵒ) p (a , aᵒ , xᵒ) = ap (λ x → a , aᵒ , x) (E→← (Sᵒ aᵒ) (in-σ p a aᵒ) xᵒ)
    E→← (δᵒ Aᵒ Sᵒ) p (f , fᵒ , xᵒ) = ap (λ x → f , fᵒ , x) (E→← (Sᵒ _)  (in-δ p f _) xᵒ)

    -- Definition 4.6
    introᵒ : ∀ {x : E S* (IR S*) El}(xᵒ : Eᵒ S*ᵒ x) → IRᵒ (IR.intro x)
    introᵒ xᵒ = IIR.intro (E→' here xᵒ)

    restrict : ∀ {S}{Sᵒ : Sigᵒ S} → Path Sᵒ → Set (suc i ⊔ suc j)
    restrict here                  = ⊤
    restrict (in-σ p a aᵒ)         = restrict p
    restrict (in-δ {A}{Aᵒ} p f fᵒ) = Σ (∀ a → Aᵒ a → IRᵒ (f a)) λ fᵒ* → (fᵒ ≡ λ a aᵒ → Elᵒ (fᵒ* _ aᵒ)) × restrict p

    pushᵒ : ∀ {S}{Sᵒ}(p : Path {S} Sᵒ)(pᵒ : restrict p){x : E S (IR S*) El}(xᵒ : Eᵒ Sᵒ x) → Eᵒ S*ᵒ (push p x)
    pushᵒ here          pᵒ                xᵒ = xᵒ
    pushᵒ (in-σ p a aᵒ) pᵒ                xᵒ = pushᵒ p pᵒ (aᵒ , xᵒ)
    pushᵒ (in-δ p f fᵒ) (fᵒ* , refl , pᵒ) xᵒ = pushᵒ p pᵒ (fᵒ* , xᵒ)

    Fᵒ : ∀ {S}{Sᵒ : Sigᵒ S}{x}(xᵒ : Eᵒ Sᵒ x) → Oᵒ (F x)
    Fᵒ {Sᵒ = ιᵒ oᵒ}    xᵒ        = oᵒ
    Fᵒ {Sᵒ = σᵒ Aᵒ Sᵒ} (aᵒ , tᵒ) = Fᵒ tᵒ
    Fᵒ {Sᵒ = δᵒ Aᵒ Sᵒ} (fᵒ , tᵒ) = Fᵒ tᵒ

    F-pushᵒ : ∀ {S}{Sᵒ}(p : Path {S} Sᵒ)(pᵒ : restrict p){x : E S (IR S*) El}(xᵒ : Eᵒ Sᵒ x)
             → tr Oᵒ (F-push p {x}) (Fᵒ xᵒ) ≡ Fᵒ (pushᵒ p pᵒ xᵒ)
    F-pushᵒ here          pᵒ              xᵒ = refl
    F-pushᵒ (in-σ p a aᵒ) pᵒ              xᵒ = F-pushᵒ p pᵒ (aᵒ , xᵒ)
    F-pushᵒ (in-δ p f fᵒ) (_ , refl , pᵒ) xᵒ = F-pushᵒ p pᵒ (_ , xᵒ)

    ⌞F⌟ : ∀ {S}{Sᵒ} (p : Path {S} Sᵒ)(pᵒ : restrict p){x : E S (IR S*) El}(xᵒ : Eᵒ Sᵒ x)
          → IIR.F (E→' p xᵒ) ≡ Fᵒ (pushᵒ p pᵒ xᵒ)
    ⌞F⌟ {Sᵒ = ιᵒ oᵒ   } p pᵒ xᵒ        = F-pushᵒ p pᵒ xᵒ
    ⌞F⌟ {Sᵒ = σᵒ Aᵒ Sᵒ} p pᵒ (aᵒ , xᵒ) = ⌞F⌟ (in-σ p _ aᵒ) pᵒ xᵒ
    ⌞F⌟ {Sᵒ = δᵒ Aᵒ Sᵒ} p pᵒ (fᵒ , xᵒ) = ⌞F⌟ (in-δ p _ _) (fᵒ , refl , pᵒ) xᵒ

    -- Definition 4.7
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

        ⌞Pᵒ⌟ : ∀ {x} → IRᵒ x → Set k
        ⌞Pᵒ⌟ {x} xᵒ = Pᵒ xᵒ (IR.elim P f x)

        IH← : ∀ {S} {Sᵒ} (p : Path {S} Sᵒ){x}{xᵒ : IIR.E (⌞ Sᵒ ⌟ p) IRᵒ Elᵒ x}
                 → IIR.IH ⌞Pᵒ⌟ xᵒ
                 → let (t' , _ , tᵒ') = E← p xᵒ in
                   IHᵒ tᵒ' (map (IR.elim P f) t')
        IH← {Sᵒ = ιᵒ oᵒ   } p {_}              ihᵒ           = tt
        IH← {Sᵒ = σᵒ Aᵒ Sᵒ} p {_}{a , aᵒ , xᵒ} ihᵒ           = IH← (in-σ p a aᵒ) ihᵒ
        IH← {Sᵒ = δᵒ Aᵒ Sᵒ} p {_}{f , fᵒ , xᵒ} ihᵒ .fst a aᵒ = ihᵒ .fst (a , aᵒ)
        IH← {Sᵒ = δᵒ Aᵒ Sᵒ} p {_}{f , fᵒ , xᵒ} ihᵒ .snd      = IH← (in-δ p f _) (ihᵒ .snd)

        ⌞fᵒ⌟ : ∀ {x} (xᵒ : IIR.E (⌞ S*ᵒ ⌟ here) IRᵒ Elᵒ x) → IIR.IH ⌞Pᵒ⌟ xᵒ → ⌞Pᵒ⌟ (IIR.intro xᵒ)
        ⌞fᵒ⌟ {x} xᵒ ih =
          tr (λ xᵒ → ⌞Pᵒ⌟ (IIR.intro xᵒ))
             (E→← S*ᵒ here xᵒ)
             (J (λ _ eq → ⌞Pᵒ⌟ (IIR.intro (E→ here (E← here xᵒ .fst , eq , E← here xᵒ .snd .snd))))
                (E← here xᵒ .snd .fst)
                (fᵒ (E← here xᵒ .snd .snd) (IH← here ih)))

        -- Definition 4.8
        elimᵒ : ∀ {x}(xᵒ : IRᵒ x) → Pᵒ xᵒ (IR.elim P f x)
        elimᵒ = IIR.elim ⌞Pᵒ⌟ ⌞fᵒ⌟

        ⌞map⌟ :
          ∀ {S} Sᵒ {x} (p : Path {S} Sᵒ) (g : ∀ {i}(x : IRᵒ i) → ⌞Pᵒ⌟ x)(xᵒ : Eᵒ Sᵒ x)
          →
          tr (λ xᵒ → IHᵒ (xᵒ .snd .snd) (map (IR.elim P f) (xᵒ .fst)))
             (E←→ Sᵒ p (x , refl , xᵒ))
             (IH← p (IIR.map g (E→' p xᵒ)))
          ≡ mapᵒ g xᵒ
        ⌞map⌟ (ιᵒ oᵒ) p xᵒ f = refl
        ⌞map⌟ (σᵒ {A} Aᵒ {S} Sᵒ) {a , x} p h (aᵒ , xᵒ) =
                 tr-∘ {B = ⌞E⌟ p (intro (push p (a , x)))}
                      (λ x → IHᵒ (x .snd .snd .snd) (map (elim P f) (x .fst .snd)))
                      (λ x → (a , x .fst) , x .snd .fst , aᵒ , x .snd .snd)
                      (E←→ (Sᵒ aᵒ) (in-σ p a aᵒ) (x , refl , xᵒ))
                      _
               ◼ ⌞map⌟ (Sᵒ aᵒ) (in-σ p a aᵒ) h xᵒ

        ⌞map⌟ (δᵒ {A} Aᵒ {S} Sᵒ) {g , x} p h (gᵒ , xᵒ) =
              tr-∘ {B = ⌞E⌟ p (intro (push p (g , x)))}
                    (λ xᵒ₁ → ((a : A) (aᵒ : Aᵒ a) → Pᵒ (xᵒ₁ .snd .snd .fst a aᵒ) (elim P f (xᵒ₁ .fst .fst a)))
                             × IHᵒ (xᵒ₁ .snd .snd .snd) (map (elim P f) (xᵒ₁ .fst .snd)))
                    (λ x₁ → (g , x₁ .fst) , x₁ .snd .fst , gᵒ , x₁ .snd .snd)
                    (E←→ (Sᵒ (λ a aᵒ → Elᵒ (gᵒ a aᵒ)))
                       (in-δ p g (λ a aᵒ → Elᵒ (gᵒ a aᵒ))) (x , refl , xᵒ))
                    _
           ◼ Σ≡
              (   tr-×₁ (E←→ (Sᵒ (λ a aᵒ → Elᵒ (gᵒ a aᵒ))) _ (x , refl , xᵒ)) _
                ◼ tr-const (E←→ (Sᵒ (λ a aᵒ → Elᵒ (gᵒ a aᵒ))) _ (x , refl , xᵒ)) _
              )
              (  tr-const (
                   tr-×₁ (E←→ (Sᵒ (λ a aᵒ → IIR.El (gᵒ a aᵒ))) (in-δ p g (λ a aᵒ → IIR.El (gᵒ a aᵒ))) (x ,
                   refl , xᵒ)) ((λ a aᵒ → h (gᵒ a aᵒ)) , IH← (in-δ p (λ a → g a) (λ a aᵒ → IIR.El (gᵒ a aᵒ)))
                  (IIR.map h (E→ (in-δ p g (λ a aᵒ → IIR.El (gᵒ a aᵒ))) (x , refl , xᵒ)))) ◼ tr-const (E←→
                  (Sᵒ (λ a aᵒ → IIR.El (gᵒ a aᵒ))) (in-δ p g (λ a aᵒ → IIR.El (gᵒ a aᵒ))) (x , refl , xᵒ)) (λ
                  a aᵒ → h (gᵒ a aᵒ))) _
               ◼ tr-×₂ (E←→ (Sᵒ (λ a aᵒ → Elᵒ (gᵒ a aᵒ))) (in-δ p g (λ a aᵒ → Elᵒ (gᵒ a aᵒ))) (x , refl , xᵒ)) _
               ◼ ⌞map⌟ (Sᵒ _) (in-δ p g _) h xᵒ
              )

        fᵒ-tr : ∀ {x : E S* (IR S*) El} (xᵒ : Eᵒ S*ᵒ x) →
                tr (λ xᵒ → Pᵒ (introᵒ (xᵒ .snd .snd)) (f (xᵒ .fst) (map (IR.elim P f) (xᵒ .fst))))
                   (E←→ S*ᵒ here (x , refl , xᵒ))
                   (fᵒ (E← here (E→' here xᵒ) .snd .snd)
                         (IH← {Sᵒ = S*ᵒ} here (IIR.map elimᵒ (E→' here xᵒ))))
              ≡ fᵒ xᵒ (tr
                   (λ xᵒ₁ → IHᵒ {Sᵒ = S*ᵒ} (xᵒ₁ .snd .snd) (map (IR.elim P f) (xᵒ₁ .fst) ))
                   (E←→ S*ᵒ here (x , refl , xᵒ))
                   (IH← {Sᵒ = S*ᵒ} here (IIR.map elimᵒ (E→' here xᵒ) )))
        fᵒ-tr {x} xᵒ =
          J (λ xᵒ* eq →
                tr (λ xᵒ₁ → Pᵒ (introᵒ (xᵒ₁ .snd .snd)) (f (xᵒ₁ .fst) (map (IR.elim P f) (xᵒ₁ .fst))))
                   eq
                   (fᵒ (E← here (E→' here xᵒ) .snd .snd)
                         (IH← {Sᵒ = S*ᵒ} here (IIR.map elimᵒ (E→' here xᵒ))))
              ≡ fᵒ (xᵒ* .snd .snd)
                     (tr (λ xᵒ₁ → IHᵒ {Sᵒ = S*ᵒ} (xᵒ₁ .snd .snd) (map (IR.elim  P f) (xᵒ₁ .fst)))
                         eq
                         (IH← {Sᵒ = S*ᵒ} here (IIR.map elimᵒ (E→' here xᵒ) ))))
           (E←→ S*ᵒ here (x , refl , xᵒ))
           refl

        -- Definition 4.9
        elimβᵒ : ∀ {x : E S* (IR S*) El} (xᵒ : Eᵒ S*ᵒ x) → elimᵒ (introᵒ xᵒ) ≡ fᵒ xᵒ (mapᵒ elimᵒ xᵒ)
        elimβᵒ {x} xᵒ =

          let lhs = ⌞fᵒ⌟ (E→' here xᵒ) (IIR.map elimᵒ (E→' here xᵒ))
              rhs = fᵒ xᵒ (mapᵒ elimᵒ xᵒ)

          in the (lhs ≡ rhs) $
              coe-coe (ap (λ xᵒ₁ → Pᵒ (IIR.intro xᵒ₁) (f x (map (elim P f) x))) (E→← S*ᵒ here (E→ here (x , refl , xᵒ))))
                      (ap (λ x₁ → Pᵒ
                              (IIR.intro (  E→ here (E← here (E→ here (x , refl , xᵒ)) .fst
                                          , x₁ .snd , E← here (E→ here (x , refl , xᵒ)) .snd .snd)))
                              (elim P f (x₁ .fst)))
                           (contr (E← here (E→ here (x , refl , xᵒ)) .snd .fst))) _
           ◼ coe-UIP (ap (λ x₁ → Pᵒ
                              (IIR.intro
                               (E→ here
                                (E← here (E→ here (x , refl , xᵒ)) .fst ,
                                 x₁ .snd , E← here (E→ here (x , refl , xᵒ)) .snd .snd)))
                              (elim P f (x₁ .fst)))
                           (contr (E← here (E→ here (x , refl , xᵒ)) .snd .fst))
                           ◼
                           ap (λ xᵒ₁ → Pᵒ (IIR.intro xᵒ₁) (f x (map (elim P f) x)))
                           (E→← S*ᵒ here (E→ here (x , refl , xᵒ))))
                     (ap (λ xᵒ₁ →
                          Pᵒ (IIR.intro (E→ here (xᵒ₁ .fst , refl , xᵒ₁ .snd .snd)))
                          (f (xᵒ₁ .fst) (map (elim P f) (xᵒ₁ .fst))))
                       (E←→ S*ᵒ here (x , refl , xᵒ)))
           ◼ fᵒ-tr xᵒ
           ◼ ap (fᵒ xᵒ) (⌞map⌟ S*ᵒ here elimᵒ xᵒ)

----------------------------------------------------------------------------------------------------
