{-# OPTIONS --without-K #-}

open import Lib

module DeriveIndexed {ext il ol : Level }(I : Set il)(O : I → Set ol) where

{-
We want to derive IIR types from IR. Now, everything from "Sig" to "mapIH" in the
following are just ordinary MLTT definitions, so we just define them. The non-trivial part is to define

- U
- El
- wrap
- El-β
- elim
- elim-β

which we do using IR.
-}

data Sig : Set (lsuc (ext ⊔ il ⊔ ol)) where
  ι : ∀ i → O i → Sig
  σ : (A : Set ext) → (A → Sig) → Sig
  δ : (A : Set ext)(f : A → I) → ((∀ a → O (f a)) → Sig) → Sig

F0 : Sig → (u : I → Set (ext ⊔ il))(el : ∀ {i} → u i → O i) → I → Set (ext ⊔ il)
F0 (ι i* _)  u el i = Lift (ext ⊔ il) (i* ≡ i)
F0 (σ A Γ)   u el i = Σ A λ a → F0 (Γ a) u el i
F0 (δ A f Γ) u el i = Σ (∀ a → u (f a)) λ g → F0 (Γ (el ∘ g)) u el i

F1 : ∀ (Γ : Sig)(u : I → Set (ext ⊔ il))(el : ∀ {i} → u i → O i) → ∀ {i} → F0 Γ u el i → O i
F1 (ι _ o)    u el p       = tr O (lower p) o
F1 (σ A Γ)    u el (a , t) = F1 (Γ a) u el t
F1 (δ A ix Γ) u el (f , t) = F1 (Γ (el ∘ f)) u el t

IH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il))(el : ∀{i} → u i → O i)
          (P : ∀ {i} → u i → Set j) → ∀ {i} → F0 Γ u el i → Set (ext ⊔ j)
IH (ι _ _)    u el P _       = Lift _ ⊤
IH (σ A Γ)    u el P (a , t) = IH (Γ a) u el P t
IH (δ A ix Γ) u el P (f , t) = (∀ a → P (f a)) × IH (Γ (el ∘ f)) u el P t

mapIH : ∀ {j}(Γ : Sig)(u : I → Set (ext ⊔ il))(el : {i : I} → u i → O i)
          i (P : ∀ {i} → u i → Set j)(t : F0 Γ u el i)
        → (∀ {i} u → P {i} u) → IH Γ u el P t
mapIH (ι i' o)   u el i P t       f = lift tt
mapIH (σ A Γ)    u el i P (a , t) f = mapIH (Γ a) u el i P t f
mapIH (δ A ix Γ) u el i P (g , t) f = f ∘ g , mapIH (Γ (el ∘ g)) u el i P t f


--------------------------------------------------------------------------------

{-
We have to map IIR signature to IR signatures somehow.
The obvious idea is to take a Σ of the indexing type and
the recursive output type.
-}

import PlainIR (ext ⊔ il) (il ⊔ ol) (∃ O) as IR

Sig→ : Sig → IR.Sig
Sig→ (ι i o)   = IR.ι (i , o)
Sig→ (σ A S)   = IR.σ (Lift (ext ⊔ il) A) λ a → Sig→ (S (lower a))
Sig→ (δ A f S) = IR.δ (Lift (ext ⊔ il) A) λ g → IR.σ ((a : A) → g (lift a) .₁ ≡ f a)
                        λ g* → Sig→ (S (λ a → tr O (g* a) (g (lift a) .₂)))

{-
The only interesting part is in "Sig→ (δ A f S)", where we hit a complication, namely
that the recursive call only works if already know that the recursive subtrees (of
the eventual IR type) are well-indexed, meaning that the first projection of their
El is the same that's being selected by the IIR signature's "f" function.

So we put this extra constraint into the signature immediately
as an extra equation.

Thus, "Sig→ S" already enforces in the IR type that *recursive*
subterms are well-indexed. So for full well-indexing, we only need to enforce
in addition that the *top-level* of an IR value is well-indexed.
-}

--------------------------------------------------------------------------------

module _ (S* : Sig) where

  S*'  = Sig→ S*

  -- abbreviations for readability
  IRU  = IR.U S*'
  IREl = IR.El S*'
  IRF0 = λ S → IR.F0 (Sig→ S) IRU IREl
  IRF1 = λ S → IR.F1 (Sig→ S) IRU IREl
  IRIH = λ {j} S → IR.IH {j} (Sig→ S) IRU IREl
  IRMapIH = λ {j} S → IR.mapIH {j} (Sig→ S) IRU IREl

  -- Here's the necessary extra restriction:
  -- the first projection of the El result must be the given "i".
  U : I → Set (ext ⊔ il)
  U i = Σ (IR.U S*') (λ x → IR.El S*' x .₁ ≡ i)

  El : ∀ {i} → U i → O i
  El {i} (x , wx) = tr O wx (IR.El S*' x .₂)

  -- This F0' is basically just the data contained in an U,
  -- that we can access by unwrapping the IR.wrap. In the following,
  -- we'll mostly work with F0' instead of U, because we can do induction on S
  -- to process F0' values.
  F0' : ∀ S I → Set (ext ⊔ il)
  F0' S i = Σ (IRF0 S) λ x → IRF1 S x .₁ ≡ i

  module _ {i} where

    {-
    What we have here is an equivalence of types in the standard type-theoretic sense,
    between F0 and F0'. I define the back and forth maps and the roundtrip equations.

    How do I know that I need this equivalence? Well,
       - This equivalence is pretty obvious and we don't have any more lying around.
       - Having an equivalence is *much* more useful/flexible than only having some maps going
         in one direction or back-and-forth; see the "half-adjoint" later.
    -}

    -- I only use fancy copattern matching to make the unfolded goal types smaller, it
    -- doesn't make any real difference in proofs.
    F0→ : ∀ S → F0 S U El i → F0' S i
    F0→ (ι i o)   x       .₁ .lower    = tt
    F0→ (ι i o)   x       .₂           = x .lower
    F0→ (σ A S)   (a , x) .₁ .₁ .lower = a
    F0→ (σ A S)   (a , x) .₁ .₂        = F0→ (S a) x .₁
    F0→ (σ A S)   (a , x) .₂           = F0→ (S a) x .₂
    F0→ (δ A f S) (g , x) .₁ .₁    a   = g (a .lower) .₁
    F0→ (δ A f S) (g , x) .₁ .₂ .₁ a   = g a .₂
    F0→ (δ A f S) (g , x) .₁ .₂ .₂     = F0→ (S (El ∘ g)) x .₁
    F0→ (δ A f S) (g , x) .₂           = F0→ (S (El ∘ g)) x .₂

    F0← : ∀ S → F0' S i → F0 S U El i
    F0← (ι i o)   (x , w)            .lower  = w
    F0← (σ A S)   ((lift a , x) , w) .₁      = a
    F0← (σ A S)   ((lift a , x) , w) .₂      = F0← (S a) (x , w)
    F0← (δ A f S) ((g , gw , x) , w) .₁ a .₁ = g (lift a)
    F0← (δ A f S) ((g , gw , x) , w) .₁ a .₂ = gw a
    F0← (δ A f S) ((g , gw , x) , w) .₂      = F0← (S (El ∘ F0← (δ A f S) ((g , gw , x) , w) .₁)) (x , w)

    F0lr : ∀ S x → F0← S (F0→ S x) ≡ x
    F0lr (ι i o)   (lift p) = refl
    F0lr (σ A S)   (a , x)  = ap (a ,_) (F0lr (S a) x)
    F0lr (δ A f S) (g , x)  = ap (g ,_) (F0lr (S _) x)

    F0rl : ∀ S x → F0→ S (F0← S x) ≡ x
    F0rl (ι i o)   (x , w)            = refl
    F0rl (σ A S)   ((lift a , x) , w) = ap (λ xw → ((lift a , xw .₁) , xw .₂)) (F0rl (S a) (x , w))
    F0rl (δ A f S) ((g , gw , x) , w) = ap (λ xw → (g , gw , xw .₁) , xw .₂) (F0rl (S _) (x , w))

    -- We need a "half adjoint" coherence condition on the F0 iso, which makes it a proper
    -- equivalence. See Section 4.2 in HoTT book. Technically, we can get it for free just from the iso,
    -- as shown in the HoTT book, but here I get it by quick and dirty induction on signatures.
    half-adjoint : ∀ S x → ap (F0→ S) (F0lr S x) ≡ F0rl S (F0→ S x)
    half-adjoint (ι i o)   x       = refl
    half-adjoint (σ A S)   (a , x) =
         J (λ x eq → ap (F0→ (σ A S)) (ap (a ,_) eq)
                   ≡ ap (λ xw → (lift a , xw .₁) , xw .₂) (ap (F0→ (S a)) eq))
           (F0lr (S a) x)
           refl
       ◼ ap (ap (λ xw → (lift a , xw .₁) , xw .₂)) (half-adjoint (S a) x)
    half-adjoint (δ A f S) (g , x) =
      -- I do some manual definitions of the goal type, to get a better displayed
      -- goal type in the following
      let lhs = ap (F0→ (δ A f S)) (ap (g ,_) (F0lr (S (El ∘ g)) x))
          rhs = ap (λ xw → ((λ a → g (a .lower) .₁) , (λ a → g a .₂) , xw .₁) , xw .₂)
                   (F0rl (S (El ∘ g)) (F0→ (S (El ∘ g)) x))
      in the (lhs ≡ rhs) $
          J (λ x eq → ap (F0→ (δ A f S)) (ap (g ,_) eq)
                    ≡ ap (λ xw → ((λ a → g (a .lower) .₁) , (λ a → g a .₂) , xw .₁) , xw .₂)
                         (ap (F0→ (S _)) eq))
            (F0lr (S _) x)
            refl
        ◼ ap (ap (λ xw → ((λ a → g (a .lower) .₁) , (λ a → g a .₂) , xw .₁) , xw .₂))
             (half-adjoint (S (El ∘ g)) x)

    F1→ : ∀ S x → tr O (F0→ S x .₂) (IRF1 S (F0→ S x .₁) .₂) ≡ F1 S U El x
    F1→ (ι i o)   x       = refl
    F1→ (σ A S)   (a , x) = F1→ (S a) x
    F1→ (δ A f S) (g , x) = F1→ (S (El ∘ g)) x

  wrap : ∀ {i} → F0 S* U El i → U i
  wrap x = IR.wrap (F0→ S* x .₁) , F0→ S* x .₂

  El≡ : ∀ {i} x → El (wrap {i} x) ≡ F1 S* U El x
  El≡ x = F1→ S* x

  -- First let's assume all the constant inputs to elimination. "met" means "induction method".
  module _ j (P : ∀ {i} → U i → Set j)(met : ∀ {i} x → IH S* U El P {i} x → P (wrap x)) where

    P' : IRU → Set (il ⊔ j)
    P' x = ∀ {i} wx → P {i} (x , wx)

    -- converting an IR-encoded induction method data to IIR form
    IH← : ∀ S {i} (x : F0' S i) → IRIH S P' (x .₁) → IH S U El P (F0← S x)
    IH← (ι i o)   x                  ih .lower      = tt
    IH← (σ A S)   ((lift a , x) , w) ih             = IH← (S a) (x , w) ih
    IH← (δ A f S) ((g , gw , x) , w) (gᴾ , ih) .₁ a = gᴾ (lift a) (gw a)
    IH← (δ A f S) ((g , gw , x) , w) (gᴾ , ih) .₂   = IH← (S _) (x , w) ih

    met' : ∀ {i} (x : F0' S* i) → IRIH S* P' (x .₁) → P (IR.wrap (x .₁) , x .₂)
    met' x ih = tr (λ x → P (IR.wrap (x .₁) , x .₂)) (F0rl S* x)
                   (met (F0← S* x) (IH← S* x ih))

    -- as expected, IIR elim is given by IR induction on well-indexed IR values.
    elim : ∀ {i} x → P {i} x
    elim (x , wx) = IR.elim S*' P' (λ x ih {i} wx → met' (x , wx) ih) x wx

    -- mapIH commutes with encoding/decoding
    -- This part and elimβ requires a modest amount of HoTT chops for shuffling
    -- transports.
    mapIH-trip : ∀ {i} S (x : F0 S U El i) f
                 → tr (IH S U El P) (F0lr S x)
                   (IH← S (F0→ S x) (IRMapIH S P' (F0→ S x .₁) f))
                 ≡ mapIH S U El i P x (λ y → f (y .₁) (y .₂))
    mapIH-trip (ι i o)   x       s = refl
    mapIH-trip (σ A S)   (a , x) s =
      tr-∘ (IH (σ A S) U El P) (a ,_) (F0lr (S a) x) _ ◼ mapIH-trip (S a) x s
    mapIH-trip (δ A f S) (g , x) s =
        tr-∘ (IH (δ A f S) U El P) (g ,_) (F0lr (S (El ∘ g)) x) _
      ◼ tr-Σ (F0lr (S (El ∘ g)) x) (IH← (δ A f S) (F0→ (δ A f S) (g , x))
             (IRMapIH (δ A f S) P' (F0→ (δ A f S) (g , x) .₁) s))
      ◼ Σ≡ (tr-const (F0lr (S (El ∘ g)) x) _)
           (  tr-const (tr-const (F0lr (S (El ∘ g)) x)
                       (IH← (δ A f S) (F0→ (δ A f S) (g , x))
                       (IRMapIH (δ A f S) P' (F0→ (δ A f S) (g , x) .₁) s) .₁)) _
            ◼ tr-∘ (IH (S _) U El P) ₁
                   (Σ≡ (F0lr (S _) x) refl) _ ⁻¹
            ◼ ap (λ eq → tr (IH (S _) U El P) eq
                            (IH← (δ A f S) (F0→ (δ A f S) (g , x))
                               (IRMapIH (δ A f S) P' (F0→ (δ A f S) (g , x) .₁) s) .₂))
                 (Σ≡₁ (F0lr (S _) x) refl)
            ◼ mapIH-trip (S _) x s)

    elimβ : ∀ {i} x → elim {i} (wrap x) ≡ met x (mapIH S* U El i P x elim)
    elimβ {i} x rewrite mapIH-trip S* x (λ x wx → elim (x , wx)) ⁻¹ =

      -- as before I manually improve on the quality of goal type display
      let inner = IH← S* (F0→ S* x) (IRMapIH S* P' (F0→ S* x .₁) (λ x wx → elim (x , wx)))
          lhs   = tr (λ x → P (IR.wrap (x .₁) , x .₂)) (F0rl S* (F0→ S* x))
                     (met (F0← S* (F0→ S* x)) inner)
          rhs   = met x (tr (IH S* U El P) (F0lr S* x) inner)

      in the (lhs ≡ rhs) $
        -- The half adjoint lemma is needed because we have an F0rl on one side of the goal
        -- equation and F0lr on the other side, and we can use half-adjoint to get rid of the F0rl,
        -- and only have F0lr on both sides.
         ap (λ eq → tr (P ∘ (λ x₁ → IR.wrap (x₁ .₁) , x₁ .₂))
            eq (met (F0← S* (F0→ S* x)) inner)) (half-adjoint S* x ⁻¹) -- note the half-adjoint
       ◼ tr-∘ (λ x₁ → P (IR.wrap (x₁ .₁) , x₁ .₂)) (F0→ S*) (F0lr S* x) _
       ◼ tr-app-lem {C = P ∘ wrap} met (F0lr S* x)
