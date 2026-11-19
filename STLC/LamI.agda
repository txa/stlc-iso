{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- λI terms and Lemma (preservation) of the note:
--
--   if t and all components of ρ are λI, then so is t [ ρ ], and
--   y occurs in t [ ρ ]  iff  y occurs in ρ_v for some v occurring in t.
--
-- "only if" is no creation (STLC.Heads.nocreate) and holds for all terms.
-- "if" needs λI: hereditary substitution only loses material through a
-- β-step (λq. N) r with q not occurring in N.
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

------------------------------------------------------------------------
-- Single substitution and application on λI terms:
--   LI-*   λI is preserved
--   keep-* occurrences of other variables survive
--   ins-*  occurrences in the substituted term survive, if the
--          substituted variable occurs

LI-sub    : ∀ {Δ A} Ξ {τ} (t : Nf ((Δ ▷ A) ⧺ Ξ) τ) (a : Nf (Δ ⧺ Ξ) A)
  → LI t → LI a → LI (sub {Δ} {A} Ξ t a)
LIs-sub   : ∀ {Δ A} Ξ {τ τ'} (sp : Sp ((Δ ▷ A) ⧺ Ξ) τ τ') (a : Nf (Δ ⧺ Ξ) A)
  → LIs sp → LI a → LIs (subSp {Δ} {A} Ξ sp a)
keep-sub  : ∀ {Δ A} Ξ {σ τ} (t : Nf ((Δ ▷ A) ⧺ Ξ) τ) (a : Nf (Δ ⧺ Ξ) A) {y : Var (Δ ⧺ Ξ) σ}
  → LI t → LI a → wkv Ξ y ∈ t → y ∈ sub {Δ} {A} Ξ t a
keeps-sub : ∀ {Δ A} Ξ {σ τ τ'} (sp : Sp ((Δ ▷ A) ⧺ Ξ) τ τ') (a : Nf (Δ ⧺ Ξ) A)
  {y : Var (Δ ⧺ Ξ) σ}
  → LIs sp → LI a → wkv Ξ y ∈s sp → y ∈s subSp {Δ} {A} Ξ sp a
ins-sub   : ∀ {Δ A} Ξ {σ τ} (t : Nf ((Δ ▷ A) ⧺ Ξ) τ) (a : Nf (Δ ⧺ Ξ) A) {y : Var (Δ ⧺ Ξ) σ}
  → LI t → LI a → top {Δ} {A} Ξ ∈ t → y ∈ a → y ∈ sub {Δ} {A} Ξ t a
inss-sub  : ∀ {Δ A} Ξ {σ τ τ'} (sp : Sp ((Δ ▷ A) ⧺ Ξ) τ τ') (a : Nf (Δ ⧺ Ξ) A)
  {y : Var (Δ ⧺ Ξ) σ}
  → LIs sp → LI a → top {Δ} {A} Ξ ∈s sp → y ∈ a → y ∈s subSp {Δ} {A} Ξ sp a
LI-app    : ∀ {Γ ρ τ} (t : Nf Γ ρ) (sp : Sp Γ ρ τ) → LI t → LIs sp → LI (appNf t sp)
keep-app  : ∀ {Γ ρ τ σ} (t : Nf Γ ρ) (sp : Sp Γ ρ τ) {y : Var Γ σ}
  → LI t → LIs sp → y ∈ t → y ∈ appNf t sp
ins-app   : ∀ {Γ ρ τ σ} (t : Nf Γ ρ) (sp : Sp Γ ρ τ) {y : Var Γ σ}
  → LI t → LIs sp → y ∈s sp → y ∈ appNf t sp

LI-sub Ξ (lam {B} t) a (li-lam o l) la =
  li-lam (keep-sub (Ξ ▷ B) t (wkNf ε a) l (LI-wk ε la) o)
         (LI-sub (Ξ ▷ B) t (wkNf ε a) l (LI-wk ε la))
LI-sub {Δ} {A} Ξ (ne (h ∙ sp)) a (li-ne ls) la with look {Δ} {A} Ξ h
... | same rewrite lk-top {Δ} {A} Ξ =
  LI-app a (subSp Ξ sp a) la (LIs-sub Ξ sp a ls la)
... | diff z rewrite lk-wkv {Δ} {A} Ξ z = li-ne (LIs-sub Ξ sp a ls la)

LIs-sub Ξ []S       a lis-nil         la = lis-nil
LIs-sub Ξ (t ∷S ts) a (lis-cons l ls) la =
  lis-cons (LI-sub Ξ t a l la) (LIs-sub Ξ ts a ls la)

keep-sub Ξ (lam {B} t) a (li-lam o l) la (o-lam p) =
  o-lam (keep-sub (Ξ ▷ B) t (wkNf ε a) l (LI-wk ε la) p)
keep-sub {Δ} {A} Ξ (ne (h ∙ sp)) a {y} (li-ne ls) la p with look {Δ} {A} Ξ h
... | same rewrite lk-top {Δ} {A} Ξ with ne-case p
...   | inl e = ⊥-elim (wkv≉top Ξ y e)
...   | inr q = ins-app a (subSp Ξ sp a) la (LIs-sub Ξ sp a ls la) (keeps-sub Ξ sp a ls la q)
keep-sub {Δ} {A} Ξ (ne (h ∙ sp)) a {y} (li-ne ls) la p | diff z
  rewrite lk-wkv {Δ} {A} Ξ z with ne-case p
... | inl e with wkv-inj Ξ y z e
...   | ≈refl = o-hd
keep-sub {Δ} {A} Ξ (ne (h ∙ sp)) a {y} (li-ne ls) la p | diff z | inr q =
  o-arg (keeps-sub Ξ sp a ls la q)

keeps-sub Ξ (t ∷S ts) a (lis-cons l ls) la (s-hd p) = s-hd (keep-sub Ξ t a l la p)
keeps-sub Ξ (t ∷S ts) a (lis-cons l ls) la (s-tl p) = s-tl (keeps-sub Ξ ts a ls la p)

ins-sub Ξ (lam {B} t) a (li-lam o l) la (o-lam p) q =
  o-lam (ins-sub (Ξ ▷ B) t (wkNf ε a) l (LI-wk ε la) p (∈-wk⁺ ε q))
ins-sub {Δ} {A} Ξ (ne (h ∙ sp)) a (li-ne ls) la p q with look {Δ} {A} Ξ h
... | same rewrite lk-top {Δ} {A} Ξ = keep-app a (subSp Ξ sp a) la (LIs-sub Ξ sp a ls la) q
... | diff z rewrite lk-wkv {Δ} {A} Ξ z with ne-case p
...   | inl e = ⊥-elim (wkv≉top Ξ z (≈-sym e))
...   | inr r = o-arg (inss-sub Ξ sp a ls la r q)

inss-sub Ξ (t ∷S ts) a (lis-cons l ls) la (s-hd p) q = s-hd (ins-sub Ξ t a l la p q)
inss-sub Ξ (t ∷S ts) a (lis-cons l ls) la (s-tl p) q = s-tl (inss-sub Ξ ts a ls la p q)

LI-app t       []S       l            ls               = l
LI-app (lam t) (b ∷S bs) (li-lam o l) (lis-cons lb ls) =
  LI-app (sub ε t b) bs (LI-sub ε t b l lb) ls

keep-app t       []S       l            ls               p         = p
keep-app (lam t) (b ∷S bs) (li-lam o l) (lis-cons lb ls) (o-lam p) =
  keep-app (sub ε t b) bs (LI-sub ε t b l lb) ls (keep-sub ε t b l lb p)

ins-app (lam t) (b ∷S bs) (li-lam o l) (lis-cons lb ls) (s-hd q) =
  keep-app (sub ε t b) bs (LI-sub ε t b l lb) ls (ins-sub ε t b l lb o q)
ins-app (lam t) (b ∷S bs) (li-lam o l) (lis-cons lb ls) (s-tl q) =
  ins-app (sub ε t b) bs (LI-sub ε t b l lb) ls q

------------------------------------------------------------------------
-- Simultaneous substitution

LIS : ∀ {Γ Δ} → Sub Γ Δ → Set
LIS {Δ = Δ} ρ = ∀ {σ} (v : Var Δ σ) → LI (lookup ρ v)

LIS-↑ : ∀ {Γ Δ A} (ρ : Sub Γ Δ) → LIS ρ → LIS (_↑ {A = A} ρ)
LIS-↑ ρ lρ vz     = LI-nvar vz
LIS-↑ {A = A} ρ lρ (vs v) =
  subst LI (sym (lookup-mapS (wkNf {σ = A} ε) ρ v)) (LI-wk ε (lρ v))

LI-[]    : ∀ {Γ Δ τ} (t : Nf Δ τ) (ρ : Sub Γ Δ) → LI t → LIS ρ → LI (t [ ρ ])
LIs-[]   : ∀ {Γ Δ τ τ'} (sp : Sp Δ τ τ') (ρ : Sub Γ Δ) → LIs sp → LIS ρ → LIs (sp [ ρ ]Sp)
keep-[]  : ∀ {Γ Δ τ σ ρ'} (t : Nf Δ τ) (ρ : Sub Γ Δ) {v : Var Δ ρ'} {y : Var Γ σ}
  → LI t → LIS ρ → v ∈ t → y ∈ lookup ρ v → y ∈ t [ ρ ]
keeps-[] : ∀ {Γ Δ τ τ' σ ρ'} (sp : Sp Δ τ τ') (ρ : Sub Γ Δ) {v : Var Δ ρ'} {y : Var Γ σ}
  → LIs sp → LIS ρ → v ∈s sp → y ∈ lookup ρ v → y ∈s sp [ ρ ]Sp

LI-[] (lam t) ρ (li-lam o l) lρ =
  li-lam (keep-[] t (ρ ↑) l (LIS-↑ ρ lρ) o (∈-nvar⁺ vz)) (LI-[] t (ρ ↑) l (LIS-↑ ρ lρ))
LI-[] (ne (x ∙ sp)) ρ (li-ne ls) lρ = LI-app (lookup ρ x) (sp [ ρ ]Sp) (lρ x) (LIs-[] sp ρ ls lρ)

LIs-[] []S       ρ lis-nil         lρ = lis-nil
LIs-[] (t ∷S ts) ρ (lis-cons l ls) lρ = lis-cons (LI-[] t ρ l lρ) (LIs-[] ts ρ ls lρ)

keep-[] (lam {A} t) ρ {v} (li-lam o l) lρ (o-lam p) q =
  o-lam (keep-[] t (ρ ↑) l (LIS-↑ ρ lρ) p
           (subst (_ ∈_) (sym (lookup-mapS (wkNf {σ = A} ε) ρ v)) (∈-wk⁺ ε q)))
keep-[] (ne (x ∙ sp)) ρ (li-ne ls) lρ p q with ne-case p
... | inl ≈refl = keep-app (lookup ρ x) (sp [ ρ ]Sp) (lρ x) (LIs-[] sp ρ ls lρ) q
... | inr r     = ins-app (lookup ρ x) (sp [ ρ ]Sp) (lρ x) (LIs-[] sp ρ ls lρ)
                          (keeps-[] sp ρ ls lρ r q)

keeps-[] (t ∷S ts) ρ (lis-cons l ls) lρ (s-hd p) q = s-hd (keep-[] t ρ l lρ p q)
keeps-[] (t ∷S ts) ρ (lis-cons l ls) lρ (s-tl p) q = s-tl (keeps-[] ts ρ ls lρ p q)

------------------------------------------------------------------------
-- Lemma (preservation)

preservation : ∀ {Γ Δ τ} (t : Nf Δ τ) (ρ : Sub Γ Δ) → LI t → LIS ρ
  → LI (t [ ρ ])
  × (∀ {σ} {y : Var Γ σ} → (y ∈ t [ ρ ] → Src ρ (_∈ t) y) × (Src ρ (_∈ t) y → y ∈ t [ ρ ]))
preservation t ρ l lρ =
  LI-[] t ρ l lρ ,Σ (nocreate t ρ ,Σ λ { (src v o h) → keep-[] t ρ l lρ o h })
