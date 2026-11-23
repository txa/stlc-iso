{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- λI terms, weakening and η-expansion.  Preservation of λI under
-- substitution is proved together with Lemma (counting) in STLC.Count.
------------------------------------------------------------------------
module STLC.LamI where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads

------------------------------------------------------------------------
-- λI: every binder occurs in its body

data LI  : ∀ {Γ τ}    → Nf Γ τ    → Set
data LIs : ∀ {Γ τ τ'} → Sp Γ τ τ' → Set

data LI where
  li-lam : ∀ {Γ A τ} {t : Nf (Γ ▷ A) τ} → vz ∈ t → LI t → LI (lam t)
  li-ne  : ∀ {Γ σ n} {x : Var Γ σ} {sp : Sp Γ σ (ι n)} → LIs sp → LI (ne (x ∙ sp))

data LIs where
  lis-nil  : ∀ {Γ τ} → LIs {Γ} {τ} {τ} []S
  lis-cons : ∀ {Γ A τ τ'} {t : Nf Γ A} {ts : Sp Γ τ τ'} → LI t → LIs ts → LIs (t ∷S ts)

------------------------------------------------------------------------
-- Variables

vs-inj : ∀ {Γ A σ τ} {x : Var Γ σ} {y : Var Γ τ} → vs {τ = A} x ≈ vs y → x ≈ y
vs-inj ≈refl = ≈refl

≈-sym : ∀ {Γ σ τ} {x : Var Γ σ} {y : Var Γ τ} → x ≈ y → y ≈ x
≈-sym ≈refl = ≈refl

wkv-inj : ∀ {Γ A} Ξ {σ τ} (y : Var (Γ ⧺ Ξ) σ) (z : Var (Γ ⧺ Ξ) τ)
  → wkv {Γ} {A} Ξ y ≈ wkv Ξ z → y ≈ z
wkv-inj ε y z e = vs-inj e
wkv-inj (Ξ ▷ C) vz     vz     e = ≈refl
wkv-inj (Ξ ▷ C) vz     (vs z) ()
wkv-inj (Ξ ▷ C) (vs y) vz     ()
wkv-inj (Ξ ▷ C) (vs y) (vs z) e with wkv-inj Ξ y z (vs-inj e)
... | ≈refl = ≈refl

wkv≉top : ∀ {Γ A} Ξ {σ} (y : Var (Γ ⧺ Ξ) σ) → wkv {Γ} {A} Ξ y ≈ top Ξ → ⊥
wkv≉top ε       y      ()
wkv≉top (Ξ ▷ C) vz     ()
wkv≉top (Ξ ▷ C) (vs y) e = wkv≉top Ξ y (vs-inj e)

------------------------------------------------------------------------
-- Weakening and η-expansion

∈-wk⁺  : ∀ {Γ A} Ξ {σ τ} {x : Var (Γ ⧺ Ξ) σ} {t : Nf (Γ ⧺ Ξ) τ}
  → x ∈ t → wkv {Γ} {A} Ξ x ∈ wkNf Ξ t
∈s-wk⁺ : ∀ {Γ A} Ξ {σ τ τ'} {x : Var (Γ ⧺ Ξ) σ} {sp : Sp (Γ ⧺ Ξ) τ τ'}
  → x ∈s sp → wkv {Γ} {A} Ξ x ∈s wkSp Ξ sp
∈-wk⁺ Ξ (o-lam p) = o-lam (∈-wk⁺ (Ξ ▷ _) p)
∈-wk⁺ Ξ o-hd      = o-hd
∈-wk⁺ Ξ (o-arg p) = o-arg (∈s-wk⁺ Ξ p)
∈s-wk⁺ Ξ (s-hd p) = s-hd (∈-wk⁺ Ξ p)
∈s-wk⁺ Ξ (s-tl p) = s-tl (∈s-wk⁺ Ξ p)

LI-wk  : ∀ {Γ A} Ξ {τ} {t : Nf (Γ ⧺ Ξ) τ} → LI t → LI (wkNf {Γ} {A} Ξ t)
LIs-wk : ∀ {Γ A} Ξ {τ τ'} {sp : Sp (Γ ⧺ Ξ) τ τ'} → LIs sp → LIs (wkSp {Γ} {A} Ξ sp)
LI-wk Ξ (li-lam o l) = li-lam (∈-wk⁺ (Ξ ▷ _) o) (LI-wk (Ξ ▷ _) l)
LI-wk Ξ (li-ne ls)   = li-ne (LIs-wk Ξ ls)
LIs-wk Ξ lis-nil         = lis-nil
LIs-wk Ξ (lis-cons l ls) = lis-cons (LI-wk Ξ l) (LIs-wk Ξ ls)

∈s-snoc-l : ∀ {Γ σ ρ A B} (sp : Sp Γ ρ (A ⇒ B)) (v : Nf Γ A) {y : Var Γ σ}
  → y ∈s sp → y ∈s snocS sp v
∈s-snoc-l (t ∷S ts) v (s-hd p) = s-hd p
∈s-snoc-l (t ∷S ts) v (s-tl p) = s-tl (∈s-snoc-l ts v p)

∈s-snoc-r : ∀ {Γ σ ρ A B} (sp : Sp Γ ρ (A ⇒ B)) (v : Nf Γ A) {y : Var Γ σ}
  → y ∈ v → y ∈s snocS sp v
∈s-snoc-r []S       v p = s-hd p
∈s-snoc-r (t ∷S ts) v p = s-tl (∈s-snoc-r ts v p)

LIs-snoc : ∀ {Γ ρ A B} {sp : Sp Γ ρ (A ⇒ B)} {v : Nf Γ A} → LIs sp → LI v → LIs (snocS sp v)
LIs-snoc lis-nil         lv = lis-cons lv lis-nil
LIs-snoc (lis-cons l ls) lv = lis-cons l (LIs-snoc ls lv)

∈-ne2nf-hd : ∀ {Γ σ τ} (x : Var Γ σ) (sp : Sp Γ σ τ) → x ∈ ne2nf x sp
∈-ne2nf-hd {τ = ι n}   x sp = o-hd
∈-ne2nf-hd {τ = A ⇒ B} x sp = o-lam (∈-ne2nf-hd (vs x) _)

∈-nvar⁺ : ∀ {Γ σ} (x : Var Γ σ) → x ∈ nvar x
∈-nvar⁺ x = ∈-ne2nf-hd x []S

∈-ne2nf-sp : ∀ {Γ ρ σ τ} (x : Var Γ ρ) (sp : Sp Γ ρ τ) {y : Var Γ σ}
  → y ∈s sp → y ∈ ne2nf x sp
∈-ne2nf-sp {τ = ι n}   x sp q = o-arg q
∈-ne2nf-sp {τ = A ⇒ B} x sp q =
  o-lam (∈-ne2nf-sp (vs x) _ (∈s-snoc-l (wkSp ε sp) (nvar vz) (∈s-wk⁺ ε q)))

LI-ne2nf : ∀ {Γ σ τ} (x : Var Γ σ) (sp : Sp Γ σ τ) → LIs sp → LI (ne2nf x sp)
LI-ne2nf {τ = ι n}   x sp ls = li-ne ls
LI-ne2nf {τ = A ⇒ B} x sp ls =
  li-lam (∈-ne2nf-sp (vs x) _ (∈s-snoc-r (wkSp ε sp) (nvar vz) (∈-nvar⁺ vz)))
         (LI-ne2nf (vs x) _ (LIs-snoc (LIs-wk ε ls) (LI-ne2nf vz []S lis-nil)))

LI-nvar : ∀ {Γ σ} (x : Var Γ σ) → LI (nvar x)
LI-nvar x = LI-ne2nf x []S lis-nil

