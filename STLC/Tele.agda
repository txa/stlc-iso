{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Telescopes: the two halves of Γ ⧺ Θ, binder telescopes of types,
-- bodies of η-long terms, and spines as substitutions.
------------------------------------------------------------------------
module STLC.Tele where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads
open import STLC.LamI

------------------------------------------------------------------------
-- Variables of Γ ⧺ Θ

injL : ∀ {Γ} Θ {σ} → Var Γ σ → Var (Γ ⧺ Θ) σ
injL ε       x = x
injL (Θ ▷ B) x = vs (injL Θ x)

injR : ∀ {Γ} Θ {σ} → Var Θ σ → Var (Γ ⧺ Θ) σ
injR (Θ ▷ B) vz         = vz
injR {Γ} (Θ ▷ B) (vs y) = vs (injR {Γ} Θ y)

data Split {Γ} (Θ : Con) {σ} : Var (Γ ⧺ Θ) σ → Set where
  inL : (u : Var Γ σ) → Split Θ (injL Θ u)
  inR : (y : Var Θ σ) → Split Θ (injR {Γ} Θ y)

split : ∀ {Γ} Θ {σ} (x : Var (Γ ⧺ Θ) σ) → Split {Γ} Θ x
split ε       x  = inL x
split (Θ ▷ B) vz = inR vz
split {Γ} (Θ ▷ B) (vs x) with split {Γ} Θ x
... | inL u = inL u
... | inR y = inR (vs y)

≡→≈ : ∀ {Γ σ} {x y : Var Γ σ} → x ≡ y → x ≈ y
≡→≈ refl = ≈refl

injL≉injR : ∀ {Γ} Θ {σ τ} (u : Var Γ σ) (y : Var Θ τ) → injL Θ u ≈ injR {Γ} Θ y → ⊥
injL≉injR ε       u ()     e
injL≉injR (Θ ▷ B) u vz     ()
injL≉injR (Θ ▷ B) u (vs y) e = injL≉injR Θ u y (vs-inj e)

injR-inj : ∀ {Γ} Θ {σ τ} (y : Var Θ σ) (y' : Var Θ τ) → injR {Γ} Θ y ≈ injR {Γ} Θ y' → y ≈ y'
injR-inj (Θ ▷ B) vz     vz      e  = ≈refl
injR-inj (Θ ▷ B) vz     (vs y') ()
injR-inj (Θ ▷ B) (vs y) vz      ()
injR-inj {Γ} (Θ ▷ B) (vs y) (vs y') e with injR-inj {Γ} Θ y y' (vs-inj e)
... | ≈refl = ≈refl

injL-⧺ : ∀ {Γ} Δ Θ {σ} (x : Var Γ σ) → injL (Δ ⧺ Θ) x ≡ injL Θ (injL Δ x)
injL-⧺ Δ ε       x = refl
injL-⧺ Δ (Θ ▷ B) x = cong vs (injL-⧺ Δ Θ x)

injR-⧺L : ∀ {Γ} Δ Θ {σ} (j : Var Δ σ)
  → injR {Γ} (Δ ⧺ Θ) (injL {Δ} Θ j) ≡ injL {Γ ⧺ Δ} Θ (injR {Γ} Δ j)
injR-⧺L Δ ε       j = refl
injR-⧺L {Γ} Δ (Θ ▷ B) j = cong vs (injR-⧺L {Γ} Δ Θ j)

injR-⧺R : ∀ {Γ} Δ Θ {σ} (k : Var Θ σ)
  → injR {Γ} (Δ ⧺ Θ) (injR {Δ} Θ k) ≡ injR {Γ ⧺ Δ} Θ k
injR-⧺R Δ (Θ ▷ B) vz     = refl
injR-⧺R {Γ} Δ (Θ ▷ B) (vs k) = cong vs (injR-⧺R {Γ} Δ Θ k)

------------------------------------------------------------------------
-- Lookup

lookup-∘s : ∀ {Γ Δ Θ σ} (τ : Sub Δ Θ) (ρ : Sub Γ Δ) (x : Var Θ σ)
  → lookup (τ ∘s ρ) x ≡ (lookup τ x) [ ρ ]
lookup-∘s τ ρ x = lookup-mapS (_[ ρ ]) τ x

lookup-⊕L : ∀ {Γ Δ Θ σ} (ρ : Sub Γ Δ) (s : Sub Γ Θ) (u : Var Δ σ)
  → lookup (ρ ⊕ s) (injL Θ u) ≡ lookup ρ u
lookup-⊕L ρ εs       u = refl
lookup-⊕L ρ (s ,s w) u = lookup-⊕L ρ s u

lookup-⊕R : ∀ {Γ Δ Θ σ} (ρ : Sub Γ Δ) (s : Sub Γ Θ) (y : Var Θ σ)
  → lookup (ρ ⊕ s) (injR {Δ} Θ y) ≡ lookup s y
lookup-⊕R ρ (s ,s w) vz     = refl
lookup-⊕R ρ (s ,s w) (vs y) = lookup-⊕R ρ s y

wkTop-nvar : ∀ {Γ} Θ {σ} (u : Var Γ σ) → wkTop Θ (nvar u) ≡ nvar (injL Θ u)
wkTop-nvar ε       u = refl
wkTop-nvar (Θ ▷ B) u = trans (cong (wkNf ε) (wkTop-nvar Θ u)) (wk-nvar ε (injL Θ u))

lookup-p : ∀ {Γ} Θ {σ} (u : Var Γ σ) → lookup (p {Γ} Θ) u ≡ nvar (injL Θ u)
lookup-p {Γ} Θ u = trans (lookup-mapS (wkTop Θ) (idS Γ) u)
                         (trans (cong (wkTop Θ) (lookup-idS u)) (wkTop-nvar Θ u))

lookup-q : ∀ {Γ} Θ {σ} (y : Var Θ σ) → lookup (q {Γ} Θ) y ≡ nvar (injR {Γ} Θ y)
lookup-q (Θ ▷ B) vz = refl
lookup-q {Γ} (Θ ▷ B) (vs y) =
  trans (lookup-mapS (wkNf {σ = B} ε) (q {Γ} Θ) y)
        (trans (cong (wkNf ε) (lookup-q {Γ} Θ y)) (wk-nvar ε (injR {Γ} Θ y)))

lookup-⇑L : ∀ {Γ Δ} (ρ : Sub Γ Δ) W {σ} (h : Var Δ σ)
  → lookup (ρ ⇑ W) (injL W h) ≡ wkTop W (lookup ρ h)
lookup-⇑L ρ ε       h = refl
lookup-⇑L ρ (W ▷ C) h =
  trans (lookup-mapS (wkNf {σ = C} ε) (ρ ⇑ W) (injL W h)) (cong (wkNf ε) (lookup-⇑L ρ W h))

lookup-⇑R : ∀ {Γ Δ} (ρ : Sub Γ Δ) W {σ} (k : Var W σ)
  → lookup (ρ ⇑ W) (injR {Δ} W k) ≡ nvar (injR {Γ} W k)
lookup-⇑R ρ (W ▷ C) vz = refl
lookup-⇑R {Γ} {Δ} ρ (W ▷ C) (vs k) =
  trans (lookup-mapS (wkNf {σ = C} ε) (ρ ⇑ W) (injR {Δ} W k))
        (trans (cong (wkNf ε) (lookup-⇑R ρ W k)) (wk-nvar ε (injR {Γ} W k)))

------------------------------------------------------------------------
-- Weakening and single substitution as simultaneous substitution

wkTop-[] : ∀ {Γ} Θ {τ} (t : Nf Γ τ) → wkTop Θ t ≡ t [ p {Γ} Θ ]
wkTop-[] {Γ} ε t = sym (trans (cong (t [_]) (mapS-id (idS Γ))) ([]-id t))
wkTop-[] {Γ} (Θ ▷ A) t =
  trans (cong (wkNf ε) (wkTop-[] Θ t))
  (trans (sym (nat-[] {A = A} ε t (p {Γ} Θ))) (cong (t [_]) (wk1S-p {Γ} Θ)))

idS⇑ : ∀ Γ Ξ → idS Γ ⇑ Ξ ≡ idS (Γ ⧺ Ξ)
idS⇑ Γ ε       = refl
idS⇑ Γ (Ξ ▷ A) = cong _↑ (idS⇑ Γ Ξ)

lookup-top-ext : ∀ {Γ Δ A} Ξ (σ : Sub Γ Δ) (b : Nf Γ A)
  → lookup ((σ ,s b) ⇑ Ξ) (top {Δ} {A} Ξ) ≡ wkTop Ξ b
lookup-top-ext ε       σ b = refl
lookup-top-ext (Ξ ▷ C) σ b =
  trans (lookup-mapS (wkNf {σ = C} ε) ((σ ,s b) ⇑ Ξ) (top Ξ)) (cong (wkNf ε) (lookup-top-ext Ξ σ b))

sub-as   : ∀ {Γ A} Ξ {τ} (t : Nf ((Γ ▷ A) ⧺ Ξ) τ) (b : Nf Γ A)
  → sub {Γ} {A} Ξ t (wkTop Ξ b) ≡ t [ (idS Γ ,s b) ⇑ Ξ ]
subSp-as : ∀ {Γ A} Ξ {τ τ'} (sp : Sp ((Γ ▷ A) ⧺ Ξ) τ τ') (b : Nf Γ A)
  → subSp {Γ} {A} Ξ sp (wkTop Ξ b) ≡ sp [ (idS Γ ,s b) ⇑ Ξ ]Sp

sub-as Ξ (lam {B} t) b = cong lam (sub-as (Ξ ▷ B) t b)
sub-as {Γ} {A} Ξ (ne (h ∙ sp)) b with look {Γ} {A} Ξ h
... | same rewrite lk-top {Γ} {A} Ξ =
  cong₂ appNf (sym (lookup-top-ext Ξ (idS Γ) b)) (subSp-as Ξ sp b)
... | diff z rewrite lk-wkv {Γ} {A} Ξ z =
  sym (trans (cong₂ appNf
                (trans (lookup-drop Ξ (idS Γ) b z)
                  (trans (cong (λ s → lookup s z) (idS⇑ Γ Ξ)) (lookup-idS z)))
                (sym (subSp-as Ξ sp b)))
             (appNf-ne2nf z []S (subSp Ξ sp (wkTop Ξ b))))

subSp-as Ξ []S       b = refl
subSp-as Ξ (t ∷S ts) b = cong₂ _∷S_ (sub-as Ξ t b) (subSp-as Ξ ts b)

-- composition of closed maps as substitution
comp-[] : ∀ {A B C} (g : Nf (ε ▷ B) C) (f : Nf (ε ▷ A) B) → g ∘ f ≡ g [ εs ,s f ]
comp-[] {A} {B} g f =
  trans (sub-as ε (wkNf {ε} {A} (ε ▷ B) g) f)
  (trans (cong (_[ idS (ε ▷ A) ,s f ]) wk-g)
  (trans ([][] g (εs ,s nvar vz) (idS (ε ▷ A) ,s f))
         (cong (λ u → g [ εs ,s u ]) (nvar-[] vz (idS (ε ▷ A) ,s f)))))
  where
  wk-g : wkNf {ε} {A} (ε ▷ B) g ≡ g [ εs ,s nvar vz ]
  wk-g = sym (trans (nat-[] {A = A} (ε ▷ B) g εs) (cong (wkNf (ε ▷ B)) ([]-id g)))

------------------------------------------------------------------------
-- Pairing

⊕-assoc : ∀ {Γ Δ Θ Ξ} (ρ : Sub Γ Δ) (σ : Sub Γ Θ) (τ : Sub Γ Ξ)
  → ρ ⊕ (σ ⊕ τ) ≡ (ρ ⊕ σ) ⊕ τ
⊕-assoc ρ σ εs       = refl
⊕-assoc ρ σ (τ ,s u) = cong (_,s u) (⊕-assoc ρ σ τ)

⇑-∘s-⊕ : ∀ {Γ Δ} Θ (σ : Sub Γ Δ) (s : Sub Γ Θ) → (σ ⇑ Θ) ∘s (idS Γ ⊕ s) ≡ σ ⊕ s
⇑-∘s-⊕ {Γ} Θ σ s =
  trans (cong (_∘s (idS Γ ⊕ s)) (⇑-pq σ Θ))
  (trans (⊕-∘s (σ ∘s p {Γ} Θ) (q {Γ} Θ) (idS Γ ⊕ s))
         (cong₂ _⊕_ (trans (∘s-assoc σ (p {Γ} Θ) (idS Γ ⊕ s))
                           (trans (cong (σ ∘s_) (p-⊕ Θ (idS Γ) s)) (∘s-idr σ)))
                    (q-⊕ Θ (idS Γ) s)))

⇑-⧺ : ∀ {Γ Δ} (ρ : Sub Γ Δ) Θ Ξ → ρ ⇑ (Θ ⧺ Ξ) ≡ (ρ ⇑ Θ) ⇑ Ξ
⇑-⧺ ρ Θ ε       = refl
⇑-⧺ ρ Θ (Ξ ▷ B) = cong _↑ (⇑-⧺ ρ Θ Ξ)

q-⧺ : ∀ {Γ} Δ Θ → q {Γ} (Δ ⧺ Θ) ≡ (q {Γ} Δ) ⇑ Θ
q-⧺ Δ ε       = refl
q-⧺ Δ (Θ ▷ B) = cong _↑ (q-⧺ Δ Θ)

------------------------------------------------------------------------
-- Binder telescopes and bodies of η-long terms

args : Ty → Con
args (ι n)   = ε
args (A ⇒ B) = (ε ▷ A) ⧺ args B

tgt : Ty → Nat
tgt (ι n)   = n
tgt (A ⇒ B) = tgt B

unlam : ∀ {Γ τ} → Nf Γ τ → Nf (Γ ⧺ args τ) (ι (tgt τ))
unlam {τ = ι n}   t       = t
unlam {τ = A ⇒ B} (lam t) = unlam t

unlam-[] : ∀ {Γ Δ τ} (t : Nf Δ τ) (ρ : Sub Γ Δ) → unlam (t [ ρ ]) ≡ (unlam t) [ ρ ⇑ args τ ]
unlam-[] {τ = ι n}   t       ρ = refl
unlam-[] {τ = A ⇒ B} (lam t) ρ =
  trans (unlam-[] t (ρ ↑)) (cong (unlam t [_]) (sym (⇑-⧺ ρ (ε ▷ A) (args B))))

FH-unlam : ∀ {Γ σ τ} {x : Var Γ σ} {t : Nf Γ τ} → FH x t
  → Σ (Sp (Γ ⧺ args τ) σ (ι (tgt τ))) (λ sp → unlam t ≡ ne (injL (args τ) x ∙ sp))
FH-unlam (fh-ne {sp = sp}) = sp ,Σ refl
FH-unlam {x = x} (fh-lam {A = A} {τ = B} h) with FH-unlam h
... | sp ,Σ e = sp ,Σ trans e (cong (λ y → ne (y ∙ sp)) (sym (injL-⧺ (ε ▷ A) (args B) x)))

-- the η-spine of a type
ηsp : ∀ Γ τ → Sp (Γ ⧺ args τ) τ (ι (tgt τ))
ηsp Γ (ι n)   = []S
ηsp Γ (A ⇒ B) = nvar (injL {Γ ▷ A} (args B) vz) ∷S ηsp (Γ ▷ A) B

wkTopSp : ∀ {Γ} Θ {τ τ'} → Sp Γ τ τ' → Sp (Γ ⧺ Θ) τ τ'
wkTopSp ε       sp = sp
wkTopSp (Θ ▷ A) sp = wkSp {σ = A} ε (wkTopSp Θ sp)

wkTopSp-snoc : ∀ {Γ} Θ {ρ A B} (sp : Sp Γ ρ (A ⇒ B)) (v : Nf Γ A)
  → wkTopSp Θ (snocS sp v) ≡ snocS (wkTopSp Θ sp) (wkTop Θ v)
wkTopSp-snoc ε       sp v = refl
wkTopSp-snoc (Θ ▷ C) sp v =
  trans (cong (wkSp ε) (wkTopSp-snoc Θ sp v)) (wk-snocS ε (wkTopSp Θ sp) (wkTop Θ v))

wkTopSp-⧺ : ∀ {Γ} Δ Θ {τ τ'} (sp : Sp Γ τ τ') → wkTopSp (Δ ⧺ Θ) sp ≡ wkTopSp Θ (wkTopSp Δ sp)
wkTopSp-⧺ Δ ε       sp = refl
wkTopSp-⧺ Δ (Θ ▷ B) sp = cong (wkSp ε) (wkTopSp-⧺ Δ Θ sp)

unlam-ne2nf : ∀ {Γ σ τ} (x : Var Γ σ) (sp : Sp Γ σ τ)
  → unlam (ne2nf x sp) ≡ ne (injL (args τ) x ∙ (wkTopSp (args τ) sp ++S ηsp Γ τ))
unlam-ne2nf {τ = ι n} x sp = cong (λ s → ne (x ∙ s)) (sym (++S-[] sp))
unlam-ne2nf {Γ} {τ = A ⇒ B} x sp =
  trans (unlam-ne2nf (vs x) (snocS (wkSp ε sp) (nvar vz)))
        (cong₂ (λ y s → ne (y ∙ s)) (sym (injL-⧺ (ε ▷ A) (args B) x)) spine)
  where
  spine : wkTopSp (args B) (snocS (wkSp ε sp) (nvar vz)) ++S ηsp (Γ ▷ A) B
        ≡ wkTopSp ((ε ▷ A) ⧺ args B) sp ++S (nvar (injL {Γ ▷ A} (args B) vz) ∷S ηsp (Γ ▷ A) B)
  spine =
    trans (cong (_++S ηsp (Γ ▷ A) B) (wkTopSp-snoc (args B) (wkSp ε sp) (nvar vz)))
    (trans (snoc-++ (wkTopSp (args B) (wkSp ε sp)) (wkTop (args B) (nvar vz)) (ηsp (Γ ▷ A) B))
           (cong₂ (λ s v → s ++S (v ∷S ηsp (Γ ▷ A) B))
                  (sym (wkTopSp-⧺ (ε ▷ A) (args B) sp))
                  (wkTop-nvar (args B) vz)))

unlam-nvar : ∀ {Γ τ} (x : Var Γ τ) → unlam (nvar x) ≡ ne (injL (args τ) x ∙ ηsp Γ τ)
unlam-nvar {Γ} {τ} x =
  trans (unlam-ne2nf x []S) (cong (λ s → ne (injL (args τ) x ∙ (s ++S ηsp Γ τ))) (wkT-nil (args τ)))
  where
  wkT-nil : ∀ Θ → wkTopSp {Γ} Θ {τ} []S ≡ []S
  wkT-nil ε       = refl
  wkT-nil (Θ ▷ B) = cong (wkSp ε) (wkT-nil Θ)

------------------------------------------------------------------------
-- Spines as substitutions

spToSub : ∀ {Γ σ n} → Sp Γ σ (ι n) → Sub Γ (args σ)
spToSub []S       = εs
spToSub (t ∷S ts) = (εs ,s t) ⊕ spToSub ts

spToSub-[] : ∀ {Γ Δ σ n} (sp : Sp Δ σ (ι n)) (ρ : Sub Γ Δ)
  → spToSub (sp [ ρ ]Sp) ≡ spToSub sp ∘s ρ
spToSub-[] []S       ρ = refl
spToSub-[] (t ∷S ts) ρ =
  trans (cong ((εs ,s t [ ρ ]) ⊕_) (spToSub-[] ts ρ)) (sym (⊕-∘s (εs ,s t) (spToSub ts) ρ))

spToSub-ηsp : ∀ Γ τ → spToSub (ηsp Γ τ) ≡ q {Γ} (args τ)
spToSub-ηsp Γ (ι n) = refl
spToSub-ηsp Γ (A ⇒ B) =
  trans (cong ((εs ,s nvar (injL {Γ ▷ A} (args B) vz)) ⊕_) (spToSub-ηsp (Γ ▷ A) B))
  (sym (trans (q-⧺ {Γ} (ε ▷ A) (args B))
         (trans (⇑-pq (q {Γ} (ε ▷ A)) (args B))
                (cong (λ u → (εs ,s u) ⊕ q {Γ ▷ A} (args B))
                      (trans (nvar-[] vz (p {Γ ▷ A} (args B))) (lookup-p (args B) vz))))))

-- applying a term whose body has a free head
app-body : ∀ {Γ σ ρ m} (t : Nf Γ σ) (x0 : Var Γ ρ) (u : Sp (Γ ⧺ args σ) ρ (ι (tgt σ)))
  (sp : Sp Γ σ (ι m))
  → unlam t ≡ ne (injL (args σ) x0 ∙ u)
  → Σ (Sp Γ ρ (ι m)) (λ u' → (appNf t sp ≡ ne (x0 ∙ u'))
                           × (spToSub u' ≡ spToSub u ∘s (idS Γ ⊕ spToSub sp)))
app-body t x0 u []S e = u ,Σ (e ,Σ sym (∘s-idr (spToSub u)))
app-body {Γ} (lam {A} {B} t) x0 u (b ∷S bs) e
  with app-body (sub ε t b) x0 (u [ σ' ]Sp) bs e1
  where
  σ' = (idS Γ ,s b) ⇑ args B
  e1 : unlam (sub ε t b) ≡ ne (injL (args B) x0 ∙ u [ σ' ]Sp)
  e1 = trans (cong unlam (sub-as ε t b))
       (trans (unlam-[] t (idS Γ ,s b))
       (trans (cong (_[ σ' ]) e)
       (trans (cong (λ h → appNf h (u [ σ' ]Sp))
                (trans (cong (lookup σ') (injL-⧺ (ε ▷ A) (args B) x0))
                (trans (lookup-⇑L (idS Γ ,s b) (args B) (vs x0))
                (trans (cong (wkTop (args B)) (lookup-idS x0)) (wkTop-nvar (args B) x0)))))
              (appNf-ne2nf (injL (args B) x0) []S (u [ σ' ]Sp)))))
... | u' ,Σ (e2 ,Σ e3) = u' ,Σ (e2 ,Σ e4)
  where
  σ' = (idS Γ ,s b) ⇑ args B
  e4 : spToSub u' ≡ spToSub u ∘s (idS Γ ⊕ ((εs ,s b) ⊕ spToSub bs))
  e4 = trans e3
       (trans (cong (_∘s (idS Γ ⊕ spToSub bs)) (spToSub-[] u σ'))
       (trans (∘s-assoc (spToSub u) σ' (idS Γ ⊕ spToSub bs))
              (cong (spToSub u ∘s_)
                    (trans (⇑-∘s-⊕ (args B) (idS Γ ,s b) (spToSub bs))
                           (sym (⊕-assoc (idS Γ) (εs ,s b) (spToSub bs)))))))

------------------------------------------------------------------------
-- Occurrences and λI through telescopes

∈-wkTop : ∀ {Γ} W {σ τ} (t : Nf Γ τ) {y : Var (Γ ⧺ W) σ}
  → y ∈ wkTop W t → Σ (Var Γ σ) (λ x → (y ≡ injL W x) × (x ∈ t))
∈-wkTop ε       t o = _ ,Σ (refl ,Σ o)
∈-wkTop (W ▷ C) t o with ∈-wk ε (wkTop W t) o
... | x' ,Σ (refl ,Σ o') with ∈-wkTop W t o'
...   | x ,Σ (refl ,Σ o'') = x ,Σ (refl ,Σ o'')

ηsp-occ : ∀ Γ τ {σ} (k : Var (args τ) σ) → injR {Γ} (args τ) k ∈s ηsp Γ τ
ηsp-occ Γ (A ⇒ B) k with split {ε ▷ A} (args B) k
... | inL vz =
  subst (_∈s ηsp Γ (A ⇒ B)) (sym (injR-⧺L {Γ} (ε ▷ A) (args B) vz)) (s-hd (∈-nvar⁺ _))
... | inR k' =
  subst (_∈s ηsp Γ (A ⇒ B)) (sym (injR-⧺R {Γ} (ε ▷ A) (args B) k')) (s-tl (ηsp-occ (Γ ▷ A) B k'))

∈-unlam⁻ : ∀ {Γ τ σ} (t : Nf Γ τ) {x : Var Γ σ} → injL (args τ) x ∈ unlam t → x ∈ t
∈-unlam⁻ {τ = ι n}   t       o = o
∈-unlam⁻ {τ = A ⇒ B} (lam t) {x} o =
  o-lam (∈-unlam⁻ t (subst (_∈ unlam t) (injL-⧺ (ε ▷ A) (args B) x) o))

LI-unlam : ∀ {Γ τ} (t : Nf Γ τ)
  → (∀ {σ} (k : Var (args τ) σ) → injR {Γ} (args τ) k ∈ unlam t) → LI (unlam t) → LI t
LI-unlam {τ = ι n} t occ l = l
LI-unlam {Γ} {τ = A ⇒ B} (lam t) occ l =
  li-lam (∈-unlam⁻ t (subst (_∈ unlam t) (injR-⧺L {Γ} (ε ▷ A) (args B) vz)
                            (occ (injL {ε ▷ A} (args B) vz))))
         (LI-unlam t (λ k → subst (_∈ unlam t) (injR-⧺R {Γ} (ε ▷ A) (args B) k)
                                  (occ (injR {ε ▷ A} (args B) k))) l)

LIs-spToSub : ∀ {Γ σ n} (sp : Sp Γ σ (ι n))
  → (∀ {ρ} (k : Var (args σ) ρ) → LI (lookup (spToSub sp) k)) → LIs sp
LIs-spToSub []S h = lis-nil
LIs-spToSub (_∷S_ {A} {B} t ts) h =
  lis-cons (subst LI (lookup-⊕L (εs ,s t) (spToSub ts) vz) (h (injL {ε ▷ A} (args B) vz)))
           (LIs-spToSub ts (λ k → subst LI (lookup-⊕R (εs ,s t) (spToSub ts) k)
                                         (h (injR {ε ▷ A} (args B) k))))

-- argument positions of a type
argPos : ∀ τ {σ} → Var (args τ) σ → Arg τ σ
argPos (A ⇒ B) k with split {ε ▷ A} (args B) k
... | inL vz      = az
... | inL (vs ())
... | inR k'      = as (argPos B k')
