{-# OPTIONS --type-in-type #-}
open import Lib

module TranslationIR-IIR {ext il ol}(I : Set il) (O : I → Set ol) where
  postulate
    funext : ∀{i j} {A : Set i} → {B : A → Set j} → (f : (a : A) → B a) → (g : (a : A) → B a) → (∀ x → f x ≡ g x) → f ≡ g

  import IndexedIR {ext = ext} I O as IIR
  import PlainIR ext (il ⊔ ol) (Σ I O) as IR

  Sig : Set (lsuc (ext ⊔ il ⊔ ol))
  Sig = IR.Sig

  ι : ∀ i → O i → Sig
  ι i oi = IR.ι (i , oi)

  σ : (A : Set ext) → (A → Sig) → Sig
  σ A f = IR.σ A f

  δ : (A : Set ext)(f : A → I) → ((∀ a → O (f a)) → Sig) → Sig
  δ A ai f = IR.δ A λ x → f (λ a → {!!})

  F0 : Sig → (u : I → Set (ext ⊔ il))(el : ∀ {i} → u i → O i) → I → Set (ext ⊔ il)
  F0 Γ u el i = Σ (IR.F0 Γ (u i) λ x → i , el x) λ x → IR.F1 Γ (u i) (λ x₁ → i , el x₁) x .₁ ≡ i

  F0-tr : (Γ : Sig) → (u u' : I → Set (ext ⊔ il))(el : ∀ {i} → u i → Σ I O) → (el' : ∀ {i} → u' i → Σ I O) → (i : I) → IR.F0 Γ (u i) el → (f : (u i) → (u' i)) → (∀ x → el x ≡ el'( f (x))) → IR.F0 Γ (u' i) el'
  F0-tr (IR.ι x) u u' el el' i f0 f eq = lift tt
  F0-tr (IR.σ A x) u u' el el' i (fst , snd) f eq = fst , F0-tr (x fst) u u' el el' i snd f eq
  F0-tr (IR.δ A x) u u' el el' i (fst , f0) f eq
    rewrite (funext (λ z → el (fst z)) (λ z → el' (f (fst z))) (λ x → eq (fst x)))
    = (λ x₁ → f (fst x₁)) , F0-tr (x (λ x₁ → el' (f (fst x₁)))) u u' el el' i f0 f eq

  F1 : ∀ (Γ : Sig)(u : I → Set (ext ⊔ il))(el : ∀ {i} → u i → O i) → ∀ {i} → F0 Γ u el i → O i
  F1 Γ u el {i} (f0 , eq) = tr O eq (IR.F1 Γ (u i) (λ x₁ → i , el x₁) f0 .₂)

  F1-tr : (Γ : Sig) → {u u' : I → Set (ext ⊔ il)}{el : ∀ {i} → u i → Σ I O} → {el' : ∀ {i} → u' i → Σ I O} → (i : I) → (f0 : IR.F0 Γ (u i) el) → (f : (u i) → (u' i)) → (eq : ∀ x → el x ≡ el'( f (x)))
                                                                                                                     → IR.F1 Γ (u i) el f0 .₁ ≡ i → IR.F1 Γ (u' i) el' (F0-tr Γ u u' el el' i f0 f eq) .₁ ≡ i
  F1-tr (IR.ι x) i f0 f eq f1 = f1
  F1-tr (IR.σ A Γ) i (a , t) f eq f1 = F1-tr (Γ a) i t f eq f1
  F1-tr (IR.δ A Γ) {u = u} {u' = u'} {el = el} {el' = el'} i (f , t) f' eq f1
        rewrite (funext (λ z → el (f z)) (λ z → el' (f' (f z))) (λ x → eq (f x))) =
        F1-tr (Γ (λ z → el' (f' (f z)))) i t f' eq f1
                                                              -- TODO uip the funext and transport enough times to get what we need

  -- todo maybe some equality on i would be useful
  IH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il))(el : ∀{i} → u i → O i)
            (P : ∀ {i} → u i → Set j) → ∀ {i} → F0 Γ u el i → Set (ext ⊔ j)
  IH Γ u el P {i} (f0 , snd) = IR.IH Γ (u i) (λ x₁ → i , el x₁) P f0

  mapIH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il))(el : {i : I} → u i → O i) i (P : ∀ {i} → u i → Set j)(t : F0 Γ u el i)
          → (∀ {i} u → P {i} u) → IH Γ u el P t
  mapIH Γ u el i P t f = IR.mapIH Γ (u i) (λ x₁ → i , el x₁) P (t .₁) f


  mutual
    U : Sig → I → Set (ext ⊔ il)
    U Γ i = Σ (IR.U Γ) λ x → IR.El Γ x .₁ ≡ i

    {-# TERMINATING #-}
    El : ∀ Γ {i} → U Γ i → O i
    El Γ {i} (u , refl) = (IR.El Γ u) .₂

    wrap : ∀ {i Γ} → F0 Γ (U Γ) (El Γ) i → U Γ i
    wrap {i} {Γ} (f0 , snd) = IR.wrap (F0-tr Γ (U Γ) (λ x → IR.U Γ) (λ {i'} x → i' , El Γ x) (IR.El Γ) i f0 (λ x → x .₁) eq)
                              , F1-tr Γ i f0 (λ x → x .₁) eq snd
            where
              eq : (x : U Γ i) → (i , El Γ x) ≡ IR.El Γ (x .₁)
              eq (fst , refl) = refl
    -- one should be easy

  {-# TERMINATING #-}
  elim : ∀ {j}(Γ : Sig)(P : ∀ {i} → U Γ i → Set j) → (∀ {i} t → IH Γ (U Γ) (El Γ) P {i} t → P (wrap t)) → ∀ {i} t → P {i} t
  elim Γ P f {i} (f0 , eq) = (IR.elim Γ (λ x → ((i : I) → (eq : (IR.El Γ x .₁ ≡ i)) → P (x , eq))) (λ t x i₁ eq → {!f ? ?!}) f0) i eq
