{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Substitution lemmas for hereditary substitution.
------------------------------------------------------------------------
module STLC.Lemmas where

open import STLC.Prelude
open import STLC.Syntax

------------------------------------------------------------------------
-- Variables

wkv-wkv : ∀ {Γ σ ρ τ} Δ Θ (x : Var (Γ ⧺ Δ ⧺ Θ) τ)
  → wkv {(Γ ▷ σ) ⧺ Δ} {ρ} Θ (wkv {Γ} {σ} (Δ ⧺ Θ) x)
  ≡ wkv {Γ} {σ} ((Δ ▷ ρ) ⧺ Θ) (wkv {Γ ⧺ Δ} {ρ} Θ x)
wkv-wkv Δ ε       x      = refl
wkv-wkv Δ (Θ ▷ A) vz     = refl
wkv-wkv Δ (Θ ▷ A) (vs x) = cong vs (wkv-wkv Δ Θ x)

lk-wkv : ∀ {Γ σ ρ} Δ (y : Var (Γ ⧺ Δ) ρ) → lk {Γ} {σ} Δ (wkv Δ y) ≡ inr y
lk-wkv ε       y      = refl
lk-wkv (Δ ▷ A) vz     = refl
lk-wkv {Γ} {σ} (Δ ▷ A) (vs y) rewrite lk-wkv {Γ} {σ} Δ y = refl

lk-top : ∀ {Γ σ} Δ → lk {Γ} {σ} Δ (top Δ) ≡ inl refl
lk-top ε       = refl
lk-top {Γ} {σ} (Δ ▷ A) rewrite lk-top {Γ} {σ} Δ = refl

------------------------------------------------------------------------
-- Weakening commutes with weakening

wkNf-wkNf : ∀ {Γ σ ρ} Δ Θ {τ} (t : Nf (Γ ⧺ Δ ⧺ Θ) τ)
  → wkNf {(Γ ▷ σ) ⧺ Δ} {ρ} Θ (wkNf {Γ} {σ} (Δ ⧺ Θ) t)
  ≡ wkNf {Γ} {σ} ((Δ ▷ ρ) ⧺ Θ) (wkNf {Γ ⧺ Δ} {ρ} Θ t)
wkSp-wkSp : ∀ {Γ σ ρ} Δ Θ {τ τ'} (sp : Sp (Γ ⧺ Δ ⧺ Θ) τ τ')
  → wkSp {(Γ ▷ σ) ⧺ Δ} {ρ} Θ (wkSp {Γ} {σ} (Δ ⧺ Θ) sp)
  ≡ wkSp {Γ} {σ} ((Δ ▷ ρ) ⧺ Θ) (wkSp {Γ ⧺ Δ} {ρ} Θ sp)

wkNf-wkNf Δ Θ (lam t)       = cong lam (wkNf-wkNf Δ (Θ ▷ _) t)
wkNf-wkNf Δ Θ (ne (y ∙ sp)) =
  cong₂ (λ y sp → ne (y ∙ sp)) (wkv-wkv Δ Θ y) (wkSp-wkSp Δ Θ sp)

wkSp-wkSp Δ Θ []S       = refl
wkSp-wkSp Δ Θ (t ∷S ts) = cong₂ _∷S_ (wkNf-wkNf Δ Θ t) (wkSp-wkSp Δ Θ ts)

------------------------------------------------------------------------
-- Weakening commutes with spine operations and η-expansion

wk-snocS : ∀ {Γ σ} Δ {ρ A B} (sp : Sp (Γ ⧺ Δ) ρ (A ⇒ B)) (u : Nf (Γ ⧺ Δ) A)
  → wkSp {Γ} {σ} Δ (snocS sp u) ≡ snocS (wkSp Δ sp) (wkNf Δ u)
wk-snocS Δ []S       u = refl
wk-snocS Δ (t ∷S ts) u = cong (wkNf Δ t ∷S_) (wk-snocS Δ ts u)

wk-ne2nf : ∀ {Γ σ} Δ {ρ τ} (x : Var (Γ ⧺ Δ) ρ) (sp : Sp (Γ ⧺ Δ) ρ τ)
  → wkNf {Γ} {σ} Δ (ne2nf x sp) ≡ ne2nf (wkv Δ x) (wkSp Δ sp)
wk-ne2nf Δ {τ = ι n}   x sp = refl
wk-ne2nf {Γ} {σ} Δ {τ = A ⇒ B} x sp = cong lam
  (wkNf (Δ ▷ A) (ne2nf (vs x) (snocS (wkSp ε sp) (nvar vz)))
     ≡⟨ wk-ne2nf (Δ ▷ A) (vs x) (snocS (wkSp ε sp) (nvar vz)) ⟩
   ne2nf (vs (wkv Δ x)) (wkSp (Δ ▷ A) (snocS (wkSp ε sp) (nvar vz)))
     ≡⟨ cong (ne2nf (vs (wkv Δ x))) (wk-snocS (Δ ▷ A) (wkSp ε sp) (nvar vz)) ⟩
   ne2nf (vs (wkv Δ x)) (snocS (wkSp (Δ ▷ A) (wkSp ε sp)) (wkNf (Δ ▷ A) (nvar vz)))
     ≡⟨ cong₂ (λ s v → ne2nf (vs (wkv Δ x)) (snocS s v))
              (sym (wkSp-wkSp Δ ε sp)) (wk-ne2nf (Δ ▷ A) vz []S) ⟩
   ne2nf (vs (wkv Δ x)) (snocS (wkSp ε (wkSp Δ sp)) (nvar vz))
     ∎)

wk-nvar : ∀ {Γ σ} Δ {ρ} (x : Var (Γ ⧺ Δ) ρ) → wkNf {Γ} {σ} Δ (nvar x) ≡ nvar (wkv Δ x)
wk-nvar Δ x = wk-ne2nf Δ x []S

------------------------------------------------------------------------
-- Substituting for a fresh variable does nothing

sub-fresh : ∀ {Γ σ} Δ {τ} (t : Nf (Γ ⧺ Δ) τ) (u : Nf (Γ ⧺ Δ) σ)
  → sub Δ (wkNf {Γ} {σ} Δ t) u ≡ t
subSp-fresh : ∀ {Γ σ} Δ {τ ρ} (sp : Sp (Γ ⧺ Δ) τ ρ) (u : Nf (Γ ⧺ Δ) σ)
  → subSp Δ (wkSp {Γ} {σ} Δ sp) u ≡ sp

sub-fresh Δ (lam t) u = cong lam (sub-fresh (Δ ▷ _) t (wkNf ε u))
sub-fresh {Γ} {σ} Δ (ne (y ∙ sp)) u rewrite lk-wkv {Γ} {σ} Δ y =
  cong (λ s → ne (y ∙ s)) (subSp-fresh Δ sp u)

subSp-fresh Δ []S       u = refl
subSp-fresh Δ (t ∷S ts) u = cong₂ _∷S_ (sub-fresh Δ t u) (subSp-fresh Δ ts u)

------------------------------------------------------------------------
-- Weakening commutes with substitution and application

wkv-top-below : ∀ {Γ ρ σ} Δ Θ
  → wkv {Γ} {ρ} ((Δ ▷ σ) ⧺ Θ) (top {Γ ⧺ Δ} {σ} Θ) ≡ top {(Γ ▷ ρ) ⧺ Δ} {σ} Θ
wkv-top-below Δ ε       = refl
wkv-top-below Δ (Θ ▷ A) = cong vs (wkv-top-below Δ Θ)

wkv-top-above : ∀ {Γ σ ρ} Δ Θ
  → wkv {(Γ ▷ σ) ⧺ Δ} {ρ} Θ (top {Γ} {σ} (Δ ⧺ Θ)) ≡ top {Γ} {σ} ((Δ ▷ ρ) ⧺ Θ)
wkv-top-above Δ ε       = refl
wkv-top-above Δ (Θ ▷ A) = cong vs (wkv-top-above Δ Θ)

-- weakening at a position below the substituted variable
wk-sub-below : ∀ {Γ ρ σ} Δ Θ {τ} (t : Nf ((Γ ⧺ Δ ▷ σ) ⧺ Θ) τ) (u : Nf (Γ ⧺ Δ ⧺ Θ) σ)
  → wkNf {Γ} {ρ} (Δ ⧺ Θ) (sub {Γ ⧺ Δ} {σ} Θ t u)
  ≡ sub {(Γ ▷ ρ) ⧺ Δ} {σ} Θ (wkNf {Γ} {ρ} ((Δ ▷ σ) ⧺ Θ) t) (wkNf {Γ} {ρ} (Δ ⧺ Θ) u)
wk-subSp-below : ∀ {Γ ρ σ} Δ Θ {τ τ'} (sp : Sp ((Γ ⧺ Δ ▷ σ) ⧺ Θ) τ τ') (u : Nf (Γ ⧺ Δ ⧺ Θ) σ)
  → wkSp {Γ} {ρ} (Δ ⧺ Θ) (subSp {Γ ⧺ Δ} {σ} Θ sp u)
  ≡ subSp {(Γ ▷ ρ) ⧺ Δ} {σ} Θ (wkSp {Γ} {ρ} ((Δ ▷ σ) ⧺ Θ) sp) (wkNf {Γ} {ρ} (Δ ⧺ Θ) u)
wk-appNf : ∀ {Γ ρ} Δ {σ τ} (u : Nf (Γ ⧺ Δ) σ) (sp : Sp (Γ ⧺ Δ) σ τ)
  → wkNf {Γ} {ρ} Δ (appNf u sp) ≡ appNf (wkNf Δ u) (wkSp Δ sp)

wk-sub-below {Γ} {ρ} {σ} Δ Θ (lam {A} t) u = cong lam
  (trans (wk-sub-below Δ (Θ ▷ A) t (wkNf ε u))
         (cong (sub (Θ ▷ A) (wkNf ((Δ ▷ σ) ⧺ (Θ ▷ A)) t))
               (sym (wkNf-wkNf {Γ} {ρ} {A} (Δ ⧺ Θ) ε u))))
wk-sub-below {Γ} {ρ} {σ} Δ Θ (ne (y ∙ sp)) u with look {Γ ⧺ Δ} {σ} Θ y
... | same
  rewrite lk-top {Γ ⧺ Δ} {σ} Θ
        | wkv-top-below {Γ} {ρ} {σ} Δ Θ
        | lk-top {(Γ ▷ ρ) ⧺ Δ} {σ} Θ
  = trans (wk-appNf (Δ ⧺ Θ) u (subSp Θ sp u))
          (cong (appNf (wkNf (Δ ⧺ Θ) u)) (wk-subSp-below Δ Θ sp u))
... | diff z
  rewrite lk-wkv {Γ ⧺ Δ} {σ} Θ z
        | sym (wkv-wkv {Γ} {ρ} {σ} Δ Θ z)
        | lk-wkv {(Γ ▷ ρ) ⧺ Δ} {σ} Θ (wkv {Γ} {ρ} (Δ ⧺ Θ) z)
  = cong (λ s → ne (wkv (Δ ⧺ Θ) z ∙ s)) (wk-subSp-below Δ Θ sp u)

wk-subSp-below Δ Θ []S       u = refl
wk-subSp-below Δ Θ (t ∷S ts) u =
  cong₂ _∷S_ (wk-sub-below Δ Θ t u) (wk-subSp-below Δ Θ ts u)

wk-appNf Δ u       []S       = refl
wk-appNf Δ (lam t) (a ∷S as) =
  trans (wk-appNf Δ (sub ε t a) as)
        (cong (λ v → appNf v (wkSp Δ as)) (wk-sub-below Δ ε t a))

-- weakening at a position above the substituted variable
wk-sub-above : ∀ {Γ σ ρ} Δ Θ {τ} (t : Nf ((Γ ▷ σ) ⧺ Δ ⧺ Θ) τ) (u : Nf (Γ ⧺ Δ ⧺ Θ) σ)
  → wkNf {Γ ⧺ Δ} {ρ} Θ (sub {Γ} {σ} (Δ ⧺ Θ) t u)
  ≡ sub {Γ} {σ} ((Δ ▷ ρ) ⧺ Θ) (wkNf {(Γ ▷ σ) ⧺ Δ} {ρ} Θ t) (wkNf {Γ ⧺ Δ} {ρ} Θ u)
wk-subSp-above : ∀ {Γ σ ρ} Δ Θ {τ τ'} (sp : Sp ((Γ ▷ σ) ⧺ Δ ⧺ Θ) τ τ') (u : Nf (Γ ⧺ Δ ⧺ Θ) σ)
  → wkSp {Γ ⧺ Δ} {ρ} Θ (subSp {Γ} {σ} (Δ ⧺ Θ) sp u)
  ≡ subSp {Γ} {σ} ((Δ ▷ ρ) ⧺ Θ) (wkSp {(Γ ▷ σ) ⧺ Δ} {ρ} Θ sp) (wkNf {Γ ⧺ Δ} {ρ} Θ u)

wk-sub-above {Γ} {σ} {ρ} Δ Θ (lam {A} t) u = cong lam
  (trans (wk-sub-above Δ (Θ ▷ A) t (wkNf ε u))
         (cong (sub ((Δ ▷ ρ) ⧺ (Θ ▷ A)) (wkNf (Θ ▷ A) t))
               (sym (wkNf-wkNf {Γ ⧺ Δ} {ρ} {A} Θ ε u))))
wk-sub-above {Γ} {σ} {ρ} Δ Θ (ne (y ∙ sp)) u with look {Γ} {σ} (Δ ⧺ Θ) y
... | same
  rewrite lk-top {Γ} {σ} (Δ ⧺ Θ)
        | wkv-top-above {Γ} {σ} {ρ} Δ Θ
        | lk-top {Γ} {σ} ((Δ ▷ ρ) ⧺ Θ)
  = trans (wk-appNf Θ u (subSp (Δ ⧺ Θ) sp u))
          (cong (appNf (wkNf Θ u)) (wk-subSp-above Δ Θ sp u))
... | diff z
  rewrite lk-wkv {Γ} {σ} (Δ ⧺ Θ) z
        | wkv-wkv {Γ} {σ} {ρ} Δ Θ z
        | lk-wkv {Γ} {σ} ((Δ ▷ ρ) ⧺ Θ) (wkv {Γ ⧺ Δ} {ρ} Θ z)
  = cong (λ s → ne (wkv Θ z ∙ s)) (wk-subSp-above Δ Θ sp u)

wk-subSp-above Δ Θ []S       u = refl
wk-subSp-above Δ Θ (t ∷S ts) u =
  cong₂ _∷S_ (wk-sub-above Δ Θ t u) (wk-subSp-above Δ Θ ts u)

------------------------------------------------------------------------
-- The substitution lemma, and substitution commutes with application

lk-top-other : ∀ {Γ σ A} Δ Θ
  → lk {Γ} {σ} ((Δ ▷ A) ⧺ Θ) (top {(Γ ▷ σ) ⧺ Δ} {A} Θ) ≡ inr (top {Γ ⧺ Δ} {A} Θ)
lk-top-other Δ ε = refl
lk-top-other {Γ} {σ} {A} Δ (Θ ▷ B) rewrite lk-top-other {Γ} {σ} {A} Δ Θ = refl

sub-appNf : ∀ {Γ σ} Δ {ρ τ} (t : Nf ((Γ ▷ σ) ⧺ Δ) ρ) (sp : Sp ((Γ ▷ σ) ⧺ Δ) ρ τ)
  (u : Nf (Γ ⧺ Δ) σ)
  → sub Δ (appNf t sp) u ≡ appNf (sub Δ t u) (subSp Δ sp u)

sub-sub : ∀ {Γ σ A} Δ Θ {τ} (w : Nf ((Γ ▷ σ) ⧺ Δ ▷ A ⧺ Θ) τ)
  (a : Nf ((Γ ▷ σ) ⧺ Δ ⧺ Θ) A) (u : Nf (Γ ⧺ Δ ⧺ Θ) σ)
  → sub {Γ} {σ} (Δ ⧺ Θ) (sub {(Γ ▷ σ) ⧺ Δ} {A} Θ w a) u
  ≡ sub {Γ ⧺ Δ} {A} Θ (sub {Γ} {σ} ((Δ ▷ A) ⧺ Θ) w (wkNf {Γ ⧺ Δ} {A} Θ u))
                      (sub {Γ} {σ} (Δ ⧺ Θ) a u)

subSp-subSp : ∀ {Γ σ A} Δ Θ {τ τ'} (sp : Sp ((Γ ▷ σ) ⧺ Δ ▷ A ⧺ Θ) τ τ')
  (a : Nf ((Γ ▷ σ) ⧺ Δ ⧺ Θ) A) (u : Nf (Γ ⧺ Δ ⧺ Θ) σ)
  → subSp {Γ} {σ} (Δ ⧺ Θ) (subSp {(Γ ▷ σ) ⧺ Δ} {A} Θ sp a) u
  ≡ subSp {Γ ⧺ Δ} {A} Θ (subSp {Γ} {σ} ((Δ ▷ A) ⧺ Θ) sp (wkNf {Γ ⧺ Δ} {A} Θ u))
                        (sub {Γ} {σ} (Δ ⧺ Θ) a u)

sub-appNf Δ t       []S       u = refl
sub-appNf Δ (lam w) (a ∷S as) u =
  trans (sub-appNf Δ (sub ε w a) as u)
        (cong (λ v → appNf v (subSp Δ as u)) (sub-sub Δ ε w a u))

sub-sub {Γ} {σ} {A} Δ Θ (lam {B} w) a u = cong lam
  (trans (sub-sub Δ (Θ ▷ B) w (wkNf ε a) (wkNf ε u))
         (cong₂ (λ x y → sub (Θ ▷ B) (sub ((Δ ▷ A) ⧺ (Θ ▷ B)) w x) y)
                (sym (wkNf-wkNf {Γ ⧺ Δ} {A} {B} Θ ε u))
                (sym (wk-sub-above {Γ} {σ} {B} (Δ ⧺ Θ) ε a u))))
sub-sub {Γ} {σ} {A} Δ Θ (ne (y ∙ sp)) a u with look {(Γ ▷ σ) ⧺ Δ} {A} Θ y
... | same
  rewrite lk-top {(Γ ▷ σ) ⧺ Δ} {A} Θ
        | lk-top-other {Γ} {σ} {A} Δ Θ
        | lk-top {Γ ⧺ Δ} {A} Θ
  = trans (sub-appNf (Δ ⧺ Θ) a (subSp Θ sp a) u)
          (cong (appNf (sub (Δ ⧺ Θ) a u)) (subSp-subSp Δ Θ sp a u))
... | diff z with look {Γ} {σ} (Δ ⧺ Θ) z
...   | same
  rewrite lk-wkv {(Γ ▷ σ) ⧺ Δ} {A} Θ (top {Γ} {σ} (Δ ⧺ Θ))
        | lk-top {Γ} {σ} (Δ ⧺ Θ)
        | wkv-top-above {Γ} {σ} {A} Δ Θ
        | lk-top {Γ} {σ} ((Δ ▷ A) ⧺ Θ)
  = sym (trans (sub-appNf Θ (wkNf Θ u) (subSp ((Δ ▷ A) ⧺ Θ) sp (wkNf Θ u))
                          (sub (Δ ⧺ Θ) a u))
               (cong₂ appNf (sub-fresh Θ u (sub (Δ ⧺ Θ) a u))
                            (sym (subSp-subSp Δ Θ sp a u))))
...   | diff z'
  rewrite lk-wkv {(Γ ▷ σ) ⧺ Δ} {A} Θ (wkv {Γ} {σ} (Δ ⧺ Θ) z')
        | lk-wkv {Γ} {σ} (Δ ⧺ Θ) z'
        | wkv-wkv {Γ} {σ} {A} Δ Θ z'
        | lk-wkv {Γ} {σ} ((Δ ▷ A) ⧺ Θ) (wkv {Γ ⧺ Δ} {A} Θ z')
        | lk-wkv {Γ ⧺ Δ} {A} Θ z'
  = cong (λ s → ne (z' ∙ s)) (subSp-subSp Δ Θ sp a u)

subSp-subSp Δ Θ []S       a u = refl
subSp-subSp Δ Θ (t ∷S ts) a u =
  cong₂ _∷S_ (sub-sub Δ Θ t a u) (subSp-subSp Δ Θ ts a u)

------------------------------------------------------------------------
-- η-expansion: lemmas

infixr 5 _++S_
_++S_ : ∀ {Γ ρ σ τ} → Sp Γ ρ σ → Sp Γ σ τ → Sp Γ ρ τ
[]S       ++S sp' = sp'
(t ∷S ts) ++S sp' = t ∷S (ts ++S sp')

++S-[] : ∀ {Γ ρ σ} (sp : Sp Γ ρ σ) → sp ++S []S ≡ sp
++S-[] []S       = refl
++S-[] (t ∷S ts) = cong (t ∷S_) (++S-[] ts)

snoc-++ : ∀ {Γ ρ A B τ} (sp : Sp Γ ρ (A ⇒ B)) (a : Nf Γ A) (as : Sp Γ B τ)
  → snocS sp a ++S as ≡ sp ++S (a ∷S as)
snoc-++ []S       a as = refl
snoc-++ (t ∷S ts) a as = cong (t ∷S_) (snoc-++ ts a as)

subSp-snocS : ∀ {Γ σ} Δ {ρ A B} (sp : Sp ((Γ ▷ σ) ⧺ Δ) ρ (A ⇒ B)) v (u : Nf (Γ ⧺ Δ) σ)
  → subSp Δ (snocS sp v) u ≡ snocS (subSp Δ sp u) (sub Δ v u)
subSp-snocS Δ []S       v u = refl
subSp-snocS Δ (t ∷S ts) v u = cong (sub Δ t u ∷S_) (subSp-snocS Δ ts v u)

-- (E1) applying an η-expanded neutral
appNf-ne2nf : ∀ {Γ ρ σ τ} (x : Var Γ ρ) (sp : Sp Γ ρ σ) (sp' : Sp Γ σ τ)
  → appNf (ne2nf x sp) sp' ≡ ne2nf x (sp ++S sp')
-- (E2) substituting into the η-expansion of another variable
sub-ne2nf-other : ∀ {Γ σ} Δ {ρ τ} (z : Var (Γ ⧺ Δ) ρ) (sp : Sp ((Γ ▷ σ) ⧺ Δ) ρ τ)
  (u : Nf (Γ ⧺ Δ) σ) → sub Δ (ne2nf (wkv Δ z) sp) u ≡ ne2nf z (subSp Δ sp u)
-- (E3) substituting into the η-expansion of the substituted variable
sub-ne2nf-top : ∀ {Γ σ} Δ {τ} (sp : Sp ((Γ ▷ σ) ⧺ Δ) σ τ) (u : Nf (Γ ⧺ Δ) σ)
  → sub Δ (ne2nf (top Δ) sp) u ≡ appNf u (subSp Δ sp u)
-- (E4) η for application
appNf-η : ∀ {Γ ρ A B} (v : Nf Γ ρ) (sp : Sp Γ ρ (A ⇒ B))
  → lam (appNf (wkNf ε v) (snocS (wkSp ε sp) (nvar vz))) ≡ appNf v sp
-- (E5) renaming a variable via its η-expansion
sub-η-ren : ∀ {Γ A} Δ {τ} (t : Nf ((Γ ▷ A) ⧺ Δ) τ)
  → sub {Γ ▷ A} {A} Δ (wkNf {Γ} {A} ((ε ▷ A) ⧺ Δ) t) (nvar (top Δ)) ≡ t
subSp-η-ren : ∀ {Γ A} Δ {τ τ'} (sp : Sp ((Γ ▷ A) ⧺ Δ) τ τ')
  → subSp {Γ ▷ A} {A} Δ (wkSp {Γ} {A} ((ε ▷ A) ⧺ Δ) sp) (nvar (top Δ)) ≡ sp
-- the spine that η-expansion builds, under substitution
subSp-ηsnoc : ∀ {Γ σ} Δ {ρ A B} (sp : Sp ((Γ ▷ σ) ⧺ Δ) ρ (A ⇒ B)) (u : Nf (Γ ⧺ Δ) σ)
  → subSp (Δ ▷ A) (snocS (wkSp ε sp) (nvar vz)) (wkNf ε u)
  ≡ snocS (wkSp ε (subSp Δ sp u)) (nvar vz)

appNf-ne2nf x sp []S = cong (ne2nf x) (sym (++S-[] sp))
appNf-ne2nf {Γ} x sp (a ∷S as) =
  trans (cong (λ v → appNf v as)
          (trans (sub-ne2nf-other ε x (snocS (wkSp ε sp) (nvar vz)) a)
                 (cong (ne2nf x)
                   (trans (subSp-snocS ε (wkSp ε sp) (nvar vz) a)
                          (cong₂ snocS (subSp-fresh ε sp a)
                                       (sub-ne2nf-top ε []S a))))))
  (trans (appNf-ne2nf x (snocS sp a) as)
         (cong (ne2nf x) (snoc-++ sp a as)))

sub-ne2nf-other {Γ} {σ} Δ {τ = ι n} z sp u rewrite lk-wkv {Γ} {σ} Δ z = refl
sub-ne2nf-other Δ {τ = A ⇒ B} z sp u = cong lam
  (trans (sub-ne2nf-other (Δ ▷ A) (vs z) (snocS (wkSp ε sp) (nvar vz)) (wkNf ε u))
         (cong (ne2nf (vs z)) (subSp-ηsnoc Δ sp u)))

sub-ne2nf-top {Γ} {σ} Δ {τ = ι n} sp u rewrite lk-top {Γ} {σ} Δ = refl
sub-ne2nf-top Δ {τ = A ⇒ B} sp u =
  trans (cong lam
          (trans (sub-ne2nf-top (Δ ▷ A) (snocS (wkSp ε sp) (nvar vz)) (wkNf ε u))
                 (cong (appNf (wkNf ε u)) (subSp-ηsnoc Δ sp u))))
        (appNf-η u (subSp Δ sp u))

subSp-ηsnoc {Γ} {σ} Δ {A = A} sp u =
  trans (subSp-snocS (Δ ▷ A) (wkSp ε sp) (nvar vz) (wkNf ε u))
        (cong₂ snocS (sym (wk-subSp-above {Γ} {σ} {A} Δ ε sp u))
                     (sub-ne2nf-other (Δ ▷ A) vz []S (wkNf ε u)))

appNf-η (lam v) []S = cong lam (sub-η-ren ε v)
appNf-η {Γ} {A = A} (lam {C} v) (a ∷S as) =
  trans (cong (λ w → lam (appNf w (snocS (wkSp ε as) (nvar vz))))
              (sym (wk-sub-below {Γ} {A} {C} ε ε v a)))
        (appNf-η (sub ε v a) as)

sub-η-ren {Γ} {A} Δ (lam {B} t) = cong lam
  (trans (cong (sub (Δ ▷ B) (wkNf ((ε ▷ A) ⧺ Δ ▷ B) t)) (wk-nvar ε (top Δ)))
         (sub-η-ren (Δ ▷ B) t))
sub-η-ren {Γ} {A} Δ (ne (y ∙ sp)) with look {Γ} {A} Δ y
... | same
  rewrite wkv-top-below {Γ} {A} {A} ε Δ
        | lk-top {Γ ▷ A} {A} Δ
  = trans (cong (appNf (nvar (top Δ))) (subSp-η-ren Δ sp))
          (appNf-ne2nf (top Δ) []S sp)
... | diff z
  rewrite sym (wkv-wkv {Γ} {A} {A} ε Δ z)
        | lk-wkv {Γ ▷ A} {A} Δ (wkv {Γ} {A} Δ z)
  = cong (λ s → ne (wkv Δ z ∙ s)) (subSp-η-ren Δ sp)

subSp-η-ren Δ []S       = refl
subSp-η-ren Δ (t ∷S ts) = cong₂ _∷S_ (sub-η-ren Δ t) (subSp-η-ren Δ ts)

------------------------------------------------------------------------
-- Consequences: normal forms form a category under composition

∘-idl : ∀ {Γ A B} (f : Nf (Γ ▷ A) B) → idNf ∘ f ≡ f
∘-idl {Γ} {A} {B} f =
  trans (cong (λ v → sub ε v f) (wk-nvar {Γ} {A} (ε ▷ B) vz))
        (sub-ne2nf-top ε []S f)

∘-idr : ∀ {Γ A B} (f : Nf (Γ ▷ A) B) → f ∘ idNf ≡ f
∘-idr f = sub-η-ren ε f

∘-assoc : ∀ {Γ A B C D} (h : Nf (Γ ▷ C) D) (g : Nf (Γ ▷ B) C) (f : Nf (Γ ▷ A) B)
  → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
∘-assoc {Γ} {A} {B} {C} h g f =
  sub ε (wkNf (ε ▷ B) (sub ε (wkNf (ε ▷ C) h) g)) f
    ≡⟨ cong (λ v → sub ε v f)
            (wk-sub-below {Γ} {A} {C} (ε ▷ B) ε (wkNf {Γ} {B} (ε ▷ C) h) g) ⟩
  sub ε (sub ε (wkNf (ε ▷ B ▷ C) (wkNf (ε ▷ C) h)) (wkNf (ε ▷ B) g)) f
    ≡⟨ sub-sub {Γ ▷ A} {B} {C} ε ε (wkNf {Γ} {A} (ε ▷ B ▷ C) (wkNf {Γ} {B} (ε ▷ C) h)) (wkNf (ε ▷ B) g) f ⟩
  sub ε (sub (ε ▷ C) (wkNf (ε ▷ B ▷ C) (wkNf (ε ▷ C) h)) (wkNf ε f)) (g ∘ f)
    ≡⟨ cong (λ v → sub ε (sub (ε ▷ C) v (wkNf ε f)) (g ∘ f))
            (sym (wkNf-wkNf {Γ} {A} {B} ε (ε ▷ C) h)) ⟩
  sub ε (sub (ε ▷ C) (wkNf (ε ▷ C) (wkNf (ε ▷ C) h)) (wkNf ε f)) (g ∘ f)
    ≡⟨ cong (λ v → sub ε v (g ∘ f)) (sub-fresh (ε ▷ C) (wkNf (ε ▷ C) h) (wkNf ε f)) ⟩
  h ∘ (g ∘ f)
    ∎
