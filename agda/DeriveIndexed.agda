{-# OPTIONS --without-K #-}

open import Lib

module DeriveIndexed {li j k : Level }(I : Set k)(O : I → Set j) where

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

data Sig : Set (lsuc li ⊔ j ⊔ k) where
  ι : ∀ i → O i → Sig
  σ : (A : Set li) → (A → Sig) → Sig
  δ : (A : Set li)(f : A → I) → ((∀ a → O (f a)) → Sig) → Sig

F0 : Sig → (ir : I → Set (li ⊔ k)) → (∀ {i} → ir i → O i) → I → Set (li ⊔ k)
F0 (ι i' _)  ir el i = Lift (li ⊔ k) (i' ≡ i)
F0 (σ A S)   ir el i = Σ A λ a → F0 (S a) ir el i
F0 (δ A f S) ir el i = Σ (∀ a → ir (f a)) λ g → F0 (S (el ∘ g)) ir el i

F1 : ∀ (S : Sig){ir : I → Set (li ⊔ k)}{el : ∀ {i} → ir i → O i} → ∀ {i} → F0 S ir el i → O i
F1 (ι _ o)             (lift x) = tr O x o
F1 (σ A S)             (a , x)  = F1 (S a) x
F1 (δ A ix S) {ir}{el} (f , x)  = F1 (S (el ∘ f)) x

IH : ∀ {l}(S : Sig){ir : I → Set (li ⊔ k)}{el : ∀{i} → ir i → O i}
          (P : ∀ {i} → ir i → Set l) → ∀ {i} → F0 S ir el i → Set (li ⊔ l)
IH (ι _ _)             P _       = Lift _ ⊤
IH (σ A S)             P (a , x) = IH (S a) P x
IH (δ A ix S) {ir}{el} P (f , x) = (∀ a → P (f a)) × IH (S (el ∘ f)) P x

mapIH : ∀ {l}(S : Sig){ir : I → Set (li ⊔ k)}{el : {i : I} → ir i → O i} (P : ∀ {i} → ir i → Set l)
        → (∀ {i} x → P {i} x) → ∀ {i} (x : F0 S ir el i) → IH S P x
mapIH (ι i' o)            P h t       = lift tt
mapIH (σ A S)             P h (a , x) = mapIH (S a) P h x
mapIH (δ A ix S) {ir}{el} P h (g , x) = h ∘ g , mapIH (S (el ∘ g)) P h x


--------------------------------------------------------------------------------

{-
We have to map IIR signature to IR signatures somehow.
The obvious idea is to take a Σ of the indexing type and
the recursive output type.
-}

import PlainIR (li ⊔ k) (j ⊔ k) (∃ O) as IR

Sig→ : Sig → IR.Sig
Sig→ (ι i o)    = IR.ι (i , o)
Sig→ (σ A S)    = IR.σ (Lift (li ⊔ k) A) λ a → Sig→ (S (lower a))
Sig→ (δ A ix S) = IR.δ (Lift (li ⊔ k) A) λ f → IR.σ ((a : A) → f (lift a) .₁ ≡ ix a)
                        λ f* → Sig→ (S (λ a → tr O (f* a) (f (lift a) .₂)))

{-
The only interesting part is in "Sig→ (δ A ix S)", where we hit a complication, namely
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
  IREl = IR.El
  IRF0 = λ S → IR.F0 (Sig→ S) IRU IREl
  IRF1 = λ S → IR.F1 (Sig→ S) {IRU} {IREl}
  IRIH = λ {l} S → IR.IH {l} (Sig→ S) {IRU} {IREl}
  IRMapIH = λ {l} S → IR.mapIH {l} (Sig→ S) {IRU} {IREl}

  -- Here's the necessary extra restriction:
  -- the first projection of the El result must be the given "i".
  U : I → Set (li ⊔ k)
  U i = Σ (IR.U S*') λ x → IR.El x .₁ ≡ i

  El : ∀ {i} → U i → O i
  El {i} (x , wx) = tr O wx (IR.El x .₂)

  -- This F0' is basically just the data contained in an U,
  -- that we can access by unwrapping the IR.wrap. In the following,
  -- we'll mostly work with F0' instead of U, because we can do induction on S
  -- to process F0' values.
  F0' : ∀ S I → Set (li ⊔ k)
  F0' S i = Σ (IRF0 S) λ x → IRF1 S x .₁ ≡ i

  module _ {i : I} where

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
    F0→ (ι i o)    x       .₁ .lower    = tt
    F0→ (ι i o)    x       .₂           = x .lower
    F0→ (σ A S)    (a , x) .₁ .₁ .lower = a
    F0→ (σ A S)    (a , x) .₁ .₂        = F0→ (S a) x .₁
    F0→ (σ A S)    (a , x) .₂           = F0→ (S a) x .₂
    F0→ (δ A ix S) (f , x) .₁ .₁    a   = f (a .lower) .₁
    F0→ (δ A ix S) (f , x) .₁ .₂ .₁ a   = f a .₂
    F0→ (δ A ix S) (f , x) .₁ .₂ .₂     = F0→ (S (El ∘ f)) x .₁
    F0→ (δ A ix S) (f , x) .₂           = F0→ (S (El ∘ f)) x .₂

    F0← : ∀ S → F0' S i → F0 S U El i
    F0← (ι i o)    (x , w)            .lower  = w
    F0← (σ A S)    ((lift a , x) , w) .₁      = a
    F0← (σ A S)    ((lift a , x) , w) .₂      = F0← (S a) (x , w)
    F0← (δ A ix S) ((f , fw , x) , w) .₁ a .₁ = f (lift a)
    F0← (δ A ix S) ((f , fw , x) , w) .₁ a .₂ = fw a
    F0← (δ A ix S) ((f , fw , x) , w) .₂      = F0← (S (El ∘ F0← (δ A ix S) ((f , fw , x) , w) .₁)) (x , w)

    F0lr : ∀ S x → F0← S (F0→ S x) ≡ x
    F0lr (ι i o)   (lift p) = refl
    F0lr (σ A S)   (a , x)  = ap (a ,_) (F0lr (S a) x)
    F0lr (δ A f S) (g , x)  = ap (g ,_) (F0lr (S _) x)

    F0rl : ∀ S x → F0→ S (F0← S x) ≡ x
    F0rl (ι i o)    (x , w)            = refl
    F0rl (σ A S)    ((lift a , x) , w) = ap (λ xw → ((lift a , xw .₁) , xw .₂)) (F0rl (S a) (x , w))
    F0rl (δ A ix S) ((f , fw , x) , w) = ap (λ xw → (f , fw , xw .₁) , xw .₂) (F0rl (S _) (x , w))

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
    half-adjoint (δ A ix S) (f , x) =
      -- I do some manual definitions of the goal type, to get a better displayed
      -- goal type in the following
      let lhs = ap (F0→ (δ A ix S)) (ap (f ,_) (F0lr (S (El ∘ f)) x))
          rhs = ap (λ xw → ((λ a → f (a .lower) .₁) , (λ a → f a .₂) , xw .₁) , xw .₂)
                   (F0rl (S (El ∘ f)) (F0→ (S (El ∘ f)) x))
      in the (lhs ≡ rhs) $
          J (λ x eq → ap (F0→ (δ A ix S)) (ap (f ,_) eq)
                    ≡ ap (λ xw → ((λ a → f (a .lower) .₁) , (λ a → f a .₂) , xw .₁) , xw .₂)
                         (ap (F0→ (S _)) eq))
            (F0lr (S _) x)
            refl
        ◼ ap (ap (λ xw → ((λ a → f (a .lower) .₁) , (λ a → f a .₂) , xw .₁) , xw .₂))
             (half-adjoint (S (El ∘ f)) x)

    F1→ : ∀ S x → tr O (F0→ S x .₂) (IRF1 S (F0→ S x .₁) .₂) ≡ F1 S x
    F1→ (ι i o)   x       = refl
    F1→ (σ A S)   (a , x) = F1→ (S a) x
    F1→ (δ A f S) (g , x) = F1→ (S (El ∘ g)) x

  wrap : ∀ {i} → F0 S* U El i → U i
  wrap x = IR.wrap (F0→ S* x .₁) , F0→ S* x .₂

  El≡ : ∀ {i} x → El (wrap {i} x) ≡ F1 S* x
  El≡ x = F1→ S* x

  -- First let's assume all the invariant inputs to elimination. "met" means "induction method".
  module _ l (P : ∀ {i} → U i → Set l)(met : ∀ {i} x → IH S* P {i} x → P (wrap x)) where

    P' : IRU → Set (k ⊔ l)
    P' x = ∀ {i} wx → P {i} (x , wx)

    -- converting an IR-encoded induction method data to IIR form
    IH← : ∀ S {i} (x : F0' S i) → IRIH S P' (x .₁) → IH S P (F0← S x)
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
    mapIH-trip : ∀ {i} S h (x : F0 S U El i)
                 → tr (IH S P) (F0lr S x)
                   (IH← S (F0→ S x) (IRMapIH S P' h (F0→ S x .₁)))
                 ≡ mapIH S P (λ y → h (y .₁) (y .₂)) x
    mapIH-trip (ι i o)   h x       = refl
    mapIH-trip (σ A S)   h (a , x) =
      tr-∘ (IH (σ A S) P) (a ,_) (F0lr (S a) x) _ ◼ mapIH-trip (S a) h x
    mapIH-trip (δ A ix S) h (f , x) =
        tr-∘ (IH (δ A ix S) P) (f ,_) (F0lr (S (El ∘ f)) x) _
      ◼ tr-Σ (F0lr (S (El ∘ f)) x) (IH← (δ A ix S) (F0→ (δ A ix S) (f , x))
             (IRMapIH (δ A ix S) P' h (F0→ (δ A ix S) (f , x) .₁)))
      ◼ Σ≡ (tr-const (F0lr (S (El ∘ f)) x) _)
           (  tr-const (tr-const (F0lr (S (El ∘ f)) x)
                       (IH← (δ A ix S) (F0→ (δ A ix S) (f , x))
                       (IRMapIH (δ A ix S) P' h (F0→ (δ A ix S) (f , x) .₁)) .₁)) _
            ◼ tr-∘ (IH (S _) P) ₁
                   (Σ≡ (F0lr (S _) x) refl) _ ⁻¹
            ◼ ap (λ eq → tr (IH (S _) P) eq
                            (IH← (δ A ix S) (F0→ (δ A ix S) (f , x))
                               (IRMapIH (δ A ix S) P' h (F0→ (δ A ix S) (f , x) .₁)) .₂))
                 (Σ≡₁ (F0lr (S _) x) refl)
            ◼ mapIH-trip (S _) h x)

    elimβ : ∀ {i} x → elim {i} (wrap x) ≡ met x (mapIH S* P elim x)
    elimβ {i} x rewrite mapIH-trip S* (λ x wx → elim (x , wx)) x ⁻¹ =

      -- as before I manually improve on the quality of goal type display
      let inner = IH← S* (F0→ S* x) (IRMapIH S* P' (λ x wx → elim (x , wx)) (F0→ S* x .₁))
          lhs   = tr (λ x → P (IR.wrap (x .₁) , x .₂)) (F0rl S* (F0→ S* x))
                     (met (F0← S* (F0→ S* x)) inner)
          rhs   = met x (tr (IH S* P) (F0lr S* x) inner)

      in the (lhs ≡ rhs) $
        -- The half adjoint lemma is needed because we have an F0rl on one side of the goal
        -- equation and F0lr on the other side, and we can use half-adjoint to get rid of the F0rl,
        -- and only have F0lr on both sides.
         ap (λ eq → tr (P ∘ (λ x₁ → IR.wrap (x₁ .₁) , x₁ .₂))
            eq (met (F0← S* (F0→ S* x)) inner)) (half-adjoint S* x ⁻¹) -- note the half-adjoint
       ◼ tr-∘ (λ x₁ → P (IR.wrap (x₁ .₁) , x₁ .₂)) (F0→ S*) (F0lr S* x) _
       ◼ tr-app-lem {C = P ∘ wrap} met (F0lr S* x)
