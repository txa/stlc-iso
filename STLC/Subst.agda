{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Simultaneous substitutions (context morphisms).
--
--   Sub Γ Δ        a normal form in Γ for each type of Δ
--   t [ ρ ]        simultaneous hereditary substitution (t : Nf Δ τ)
--   σ ∘s ρ         composition
--   ρ ⊕ σ          pairing along ⧺
--   q Θ            the η-expanded variables of the telescope Θ
--   p Θ            the weakening projection  Sub (Γ ⧺ Θ) Γ
--
-- t [ ρ ] is defined by structural recursion on t; at a neutral
-- x ∙ sp it uses the single-variable  appNf  of STLC.Syntax, so no new
-- termination argument is needed.  The laws reduce to STLC.Lemmas.
------------------------------------------------------------------------
module STLC.Subst where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas

------------------------------------------------------------------------
-- Substitutions

infixl 5 _,s_
data Sub (Γ : Con) : Con → Set where
  εs   : Sub Γ ε
  _,s_ : ∀ {Δ A} → Sub Γ Δ → Nf Γ A → Sub Γ (Δ ▷ A)

lookup : ∀ {Γ Δ τ} → Sub Γ Δ → Var Δ τ → Nf Γ τ
lookup (ρ ,s u) vz     = u
lookup (ρ ,s u) (vs x) = lookup ρ x

mapS : ∀ {Γ Γ' Δ} → (∀ {τ} → Nf Γ τ → Nf Γ' τ) → Sub Γ Δ → Sub Γ' Δ
mapS f εs       = εs
mapS f (ρ ,s u) = mapS f ρ ,s f u

infixl 5 _⊕_
_⊕_ : ∀ {Γ Δ Θ} → Sub Γ Δ → Sub Γ Θ → Sub Γ (Δ ⧺ Θ)
ρ ⊕ εs       = ρ
ρ ⊕ (σ ,s u) = (ρ ⊕ σ) ,s u

-- weakening by telescopes at the top
wkTop : ∀ {Γ} Θ {τ} → Nf Γ τ → Nf (Γ ⧺ Θ) τ
wkTop ε       t = t
wkTop (Θ ▷ A) t = wkNf {σ = A} ε (wkTop Θ t)

------------------------------------------------------------------------
-- Lifting

wk1S : ∀ {Γ Δ A} → Sub Γ Δ → Sub (Γ ▷ A) Δ
wk1S {A = A} = mapS (wkNf {σ = A} ε)

infixl 6 _↑
_↑ : ∀ {Γ Δ A} → Sub Γ Δ → Sub (Γ ▷ A) (Δ ▷ A)
ρ ↑ = wk1S ρ ,s nvar vz

infixl 6 _⇑_
_⇑_ : ∀ {Γ Δ} → Sub Γ Δ → ∀ Ξ → Sub (Γ ⧺ Ξ) (Δ ⧺ Ξ)
ρ ⇑ ε       = ρ
ρ ⇑ (Ξ ▷ A) = (ρ ⇑ Ξ) ↑

-- lift past A, then past Ξ   (A given explicitly: ⧺ is not injective)
up : ∀ {Γ Δ} A Ξ → Sub Γ Δ → Sub ((Γ ▷ A) ⧺ Ξ) ((Δ ▷ A) ⧺ Ξ)
up A Ξ ρ = (_↑ {A = A} ρ) ⇑ Ξ

------------------------------------------------------------------------
-- Application and composition

infix 8 _[_] _[_]Sp
_[_]   : ∀ {Γ Δ τ} → Nf Δ τ → Sub Γ Δ → Nf Γ τ
_[_]Sp : ∀ {Γ Δ τ τ'} → Sp Δ τ τ' → Sub Γ Δ → Sp Γ τ τ'

lam t       [ ρ ] = lam (t [ ρ ↑ ])
ne (x ∙ sp) [ ρ ] = appNf (lookup ρ x) (sp [ ρ ]Sp)

[]S       [ ρ ]Sp = []S
(t ∷S ts) [ ρ ]Sp = t [ ρ ] ∷S ts [ ρ ]Sp

infixr 9 _∘s_
_∘s_ : ∀ {Γ Δ Θ} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
σ ∘s ρ = mapS (_[ ρ ]) σ

------------------------------------------------------------------------
-- Identities and projections

q : ∀ {Γ} Θ → Sub (Γ ⧺ Θ) Θ
q ε       = εs
q {Γ} (Θ ▷ A) = wk1S (q {Γ} Θ) ,s nvar vz

idS : ∀ Γ → Sub Γ Γ
idS Γ = q {ε} Γ

p : ∀ {Γ} Θ → Sub (Γ ⧺ Θ) Γ
p {Γ} Θ = mapS (wkTop {Γ} Θ) (idS Γ)

------------------------------------------------------------------------
-- Lookup

lookup-mapS : ∀ {Γ Γ' Δ τ} (f : ∀ {τ} → Nf Γ τ → Nf Γ' τ) (ρ : Sub Γ Δ) (x : Var Δ τ)
  → lookup (mapS f ρ) x ≡ f (lookup ρ x)
lookup-mapS f (ρ ,s u) vz     = refl
lookup-mapS f (ρ ,s u) (vs x) = lookup-mapS f ρ x

lookup-idS : ∀ {Δ τ} (x : Var Δ τ) → lookup (idS Δ) x ≡ nvar x
lookup-idS vz     = refl
lookup-idS {Δ ▷ A} (vs x) =
  trans (lookup-mapS (wkNf {σ = A} ε) (idS Δ) x)
        (trans (cong (wkNf ε) (lookup-idS x)) (wk-nvar ε x))

-- a lifted substitution, at a weakened variable
lookup-wkv : ∀ {Γ Δ A} Ξ (σ : Sub Γ Δ) {τ} (x : Var (Δ ⧺ Ξ) τ)
  → lookup (up A Ξ σ) (wkv {Δ} {A} Ξ x) ≡ wkNf {Γ} {A} Ξ (lookup (σ ⇑ Ξ) x)
lookup-wkv ε σ x = lookup-mapS (wkNf ε) σ x
lookup-wkv {Γ} {Δ} {A} (Ξ ▷ C) σ vz = sym (wk-nvar {Γ} {A} (Ξ ▷ C) vz)
lookup-wkv {Γ} {Δ} {A} (Ξ ▷ C) σ (vs x) =
  trans (lookup-mapS (wkNf {σ = C} ε) (up A Ξ σ) (wkv Ξ x))
  (trans (cong (wkNf {σ = C} ε) (lookup-wkv Ξ σ x))
  (trans (wkNf-wkNf {Γ} {A} {C} Ξ ε (lookup (σ ⇑ Ξ) x))
         (cong (wkNf {Γ} {A} (Ξ ▷ C)) (sym (lookup-mapS (wkNf {σ = C} ε) (σ ⇑ Ξ) x)))))

-- a lifted substitution, at the lifted variable
lookup-top : ∀ {Γ Δ A} Ξ (σ : Sub Γ Δ)
  → lookup (up A Ξ σ) (top {Δ} {A} Ξ) ≡ nvar (top {Γ} {A} Ξ)
lookup-top ε σ = refl
lookup-top {Γ} {Δ} {A} (Ξ ▷ C) σ =
  trans (lookup-mapS (wkNf {σ = C} ε) (up A Ξ σ) (top Ξ))
        (trans (cong (wkNf ε) (lookup-top Ξ σ)) (wk-nvar ε (top {Γ} {A} Ξ)))

-- an extended substitution, at a weakened variable
lookup-drop : ∀ {Γ Δ A} Ξ (σ : Sub Γ Δ) (v : Nf Γ A) {τ} (x : Var (Δ ⧺ Ξ) τ)
  → lookup ((σ ,s v) ⇑ Ξ) (wkv {Δ} {A} Ξ x) ≡ lookup (σ ⇑ Ξ) x
lookup-drop ε σ v x = refl
lookup-drop (Ξ ▷ C) σ v vz = refl
lookup-drop (Ξ ▷ C) σ v (vs x) =
  trans (lookup-mapS (wkNf {σ = C} ε) ((σ ,s v) ⇑ Ξ) (wkv Ξ x))
        (trans (cong (wkNf ε) (lookup-drop Ξ σ v x))
               (sym (lookup-mapS (wkNf {σ = C} ε) (σ ⇑ Ξ) x)))

------------------------------------------------------------------------
-- Weakening and substitution

-- substituting into a weakening, with the weakened variable lifted
wk-[]   : ∀ {Γ Δ A} Ξ {τ} (t : Nf (Δ ⧺ Ξ) τ) (σ : Sub Γ Δ)
  → (wkNf {Δ} {A} Ξ t) [ up A Ξ σ ] ≡ wkNf {Γ} {A} Ξ (t [ σ ⇑ Ξ ])
wk-[]Sp : ∀ {Γ Δ A} Ξ {τ τ'} (sp : Sp (Δ ⧺ Ξ) τ τ') (σ : Sub Γ Δ)
  → (wkSp {Δ} {A} Ξ sp) [ up A Ξ σ ]Sp ≡ wkSp {Γ} {A} Ξ (sp [ σ ⇑ Ξ ]Sp)

wk-[] Ξ (lam {B} t) σ = cong lam (wk-[] (Ξ ▷ B) t σ)
wk-[] {Γ} {Δ} {A} Ξ (ne (x ∙ sp)) σ =
  trans (cong₂ appNf (lookup-wkv Ξ σ x) (wk-[]Sp Ξ sp σ))
        (sym (wk-appNf {Γ} {A} Ξ (lookup (σ ⇑ Ξ) x) (sp [ σ ⇑ Ξ ]Sp)))

wk-[]Sp Ξ []S       σ = refl
wk-[]Sp Ξ (t ∷S ts) σ = cong₂ _∷S_ (wk-[] Ξ t σ) (wk-[]Sp Ξ ts σ)

-- substituting into a weakening, with the weakened variable dropped
drop-[]   : ∀ {Γ Δ A} Ξ {τ} (t : Nf (Δ ⧺ Ξ) τ) (σ : Sub Γ Δ) (v : Nf Γ A)
  → (wkNf {Δ} {A} Ξ t) [ (σ ,s v) ⇑ Ξ ] ≡ t [ σ ⇑ Ξ ]
drop-[]Sp : ∀ {Γ Δ A} Ξ {τ τ'} (sp : Sp (Δ ⧺ Ξ) τ τ') (σ : Sub Γ Δ) (v : Nf Γ A)
  → (wkSp {Δ} {A} Ξ sp) [ (σ ,s v) ⇑ Ξ ]Sp ≡ sp [ σ ⇑ Ξ ]Sp

drop-[] Ξ (lam {B} t) σ v = cong lam (drop-[] (Ξ ▷ B) t σ v)
drop-[] Ξ (ne (x ∙ sp)) σ v =
  cong₂ appNf (lookup-drop Ξ σ v x) (drop-[]Sp Ξ sp σ v)

drop-[]Sp Ξ []S       σ v = refl
drop-[]Sp Ξ (t ∷S ts) σ v = cong₂ _∷S_ (drop-[] Ξ t σ v) (drop-[]Sp Ξ ts σ v)

------------------------------------------------------------------------
-- η-expanded variables look up their substitute

snoc-[] : ∀ {Γ Δ ρ A B} (sp : Sp Δ ρ (A ⇒ B)) (v : Nf Δ A) (σ : Sub Γ Δ)
  → (snocS sp v) [ σ ]Sp ≡ snocS (sp [ σ ]Sp) (v [ σ ])
snoc-[] []S       v σ = refl
snoc-[] (t ∷S ts) v σ = cong (t [ σ ] ∷S_) (snoc-[] ts v σ)

ne2nf-[] : ∀ {Γ Δ ρ τ} (x : Var Δ ρ) (sp : Sp Δ ρ τ) (σ : Sub Γ Δ)
  → (ne2nf x sp) [ σ ] ≡ appNf (lookup σ x) (sp [ σ ]Sp)
ne2nf-[] {τ = ι n} x sp σ = refl
ne2nf-[] {Γ} {τ = A ⇒ B} x sp σ =
  lam ((ne2nf (vs x) (snocS (wkSp ε sp) (nvar vz))) [ σ ↑ ])
    ≡⟨ cong lam (ne2nf-[] (vs x) (snocS (wkSp ε sp) (nvar vz)) (σ ↑)) ⟩
  lam (appNf (lookup (wk1S σ) x) ((snocS (wkSp ε sp) (nvar vz)) [ σ ↑ ]Sp))
    ≡⟨ cong₂ (λ u s → lam (appNf u s))
             (lookup-mapS (wkNf {σ = A} ε) σ x) (snoc-[] (wkSp ε sp) (nvar vz) (σ ↑)) ⟩
  lam (appNf (wkNf ε (lookup σ x)) (snocS ((wkSp ε sp) [ σ ↑ ]Sp) ((nvar vz) [ σ ↑ ])))
    ≡⟨ cong₂ (λ s v → lam (appNf (wkNf ε (lookup σ x)) (snocS s v)))
             (wk-[]Sp ε sp σ) (ne2nf-[] vz []S (σ ↑)) ⟩
  lam (appNf (wkNf ε (lookup σ x)) (snocS (wkSp ε (sp [ σ ]Sp)) (nvar vz)))
    ≡⟨ appNf-η (lookup σ x) (sp [ σ ]Sp) ⟩
  appNf (lookup σ x) (sp [ σ ]Sp)
    ∎

nvar-[] : ∀ {Γ Δ τ} (x : Var Δ τ) (σ : Sub Γ Δ) → (nvar x) [ σ ] ≡ lookup σ x
nvar-[] x σ = ne2nf-[] x []S σ

------------------------------------------------------------------------
-- The identity law

[]-id   : ∀ {Δ τ} (t : Nf Δ τ) → t [ idS Δ ] ≡ t
[]Sp-id : ∀ {Δ τ τ'} (sp : Sp Δ τ τ') → sp [ idS Δ ]Sp ≡ sp

[]-id (lam t)       = cong lam ([]-id t)
[]-id (ne (x ∙ sp)) =
  trans (cong₂ appNf (lookup-idS x) ([]Sp-id sp))
        (appNf-ne2nf x []S sp)

[]Sp-id []S       = refl
[]Sp-id (t ∷S ts) = cong₂ _∷S_ ([]-id t) ([]Sp-id ts)

------------------------------------------------------------------------
-- Single and simultaneous substitution commute; substitution commutes
-- with application.

sub-[]   : ∀ {Γ Δ A} Ξ {τ} (t : Nf ((Δ ▷ A) ⧺ Ξ) τ) (a : Nf (Δ ⧺ Ξ) A) (σ : Sub Γ Δ)
  → (sub {Δ} {A} Ξ t a) [ σ ⇑ Ξ ] ≡ sub {Γ} {A} Ξ (t [ up A Ξ σ ]) (a [ σ ⇑ Ξ ])
subSp-[] : ∀ {Γ Δ A} Ξ {τ τ'} (sp : Sp ((Δ ▷ A) ⧺ Ξ) τ τ') (a : Nf (Δ ⧺ Ξ) A) (σ : Sub Γ Δ)
  → (subSp {Δ} {A} Ξ sp a) [ σ ⇑ Ξ ]Sp ≡ subSp {Γ} {A} Ξ (sp [ up A Ξ σ ]Sp) (a [ σ ⇑ Ξ ])
appNf-[] : ∀ {Γ Δ ρ τ} (t : Nf Δ ρ) (sp : Sp Δ ρ τ) (σ : Sub Γ Δ)
  → (appNf t sp) [ σ ] ≡ appNf (t [ σ ]) (sp [ σ ]Sp)

sub-[] {Γ} {Δ} {A} Ξ (lam {B} t) a σ = cong lam
  (trans (sub-[] (Ξ ▷ B) t (wkNf ε a) σ)
         (cong (sub {Γ} {A} (Ξ ▷ B) (t [ up A (Ξ ▷ B) σ ])) (wk-[] ε a (σ ⇑ Ξ))))
sub-[] {Γ} {Δ} {A} Ξ (ne (y ∙ sp)) a σ with look {Δ} {A} Ξ y
... | same rewrite lk-top {Δ} {A} Ξ =
  (appNf a (subSp Ξ sp a)) [ σ ⇑ Ξ ]
    ≡⟨ appNf-[] a (subSp Ξ sp a) (σ ⇑ Ξ) ⟩
  appNf a' (subSp Ξ sp a [ σ ⇑ Ξ ]Sp)
    ≡⟨ cong (appNf a') (subSp-[] Ξ sp a σ) ⟩
  appNf a' (subSp {Γ} {A} Ξ sp' a')
    ≡⟨ sym (sub-ne2nf-top {Γ} {A} Ξ sp' a') ⟩
  sub {Γ} {A} Ξ (ne2nf (top Ξ) sp') a'
    ≡⟨ cong (λ v → sub {Γ} {A} Ξ v a') (sym (appNf-ne2nf (top {Γ} {A} Ξ) []S sp')) ⟩
  sub {Γ} {A} Ξ (appNf (nvar (top Ξ)) sp') a'
    ≡⟨ cong (λ v → sub {Γ} {A} Ξ (appNf v sp') a') (sym (lookup-top Ξ σ)) ⟩
  sub {Γ} {A} Ξ (appNf (lookup (up A Ξ σ) (top Ξ)) sp') a'
    ∎
  where
  a'  = a [ σ ⇑ Ξ ]
  sp' = sp [ up A Ξ σ ]Sp
... | diff z rewrite lk-wkv {Δ} {A} Ξ z =
  appNf v (subSp Ξ sp a [ σ ⇑ Ξ ]Sp)
    ≡⟨ cong (appNf v) (subSp-[] Ξ sp a σ) ⟩
  appNf v (subSp {Γ} {A} Ξ sp' a')
    ≡⟨ cong (λ w → appNf w (subSp {Γ} {A} Ξ sp' a')) (sym (sub-fresh {Γ} {A} Ξ v a')) ⟩
  appNf (sub {Γ} {A} Ξ (wkNf Ξ v) a') (subSp {Γ} {A} Ξ sp' a')
    ≡⟨ sym (sub-appNf {Γ} {A} Ξ (wkNf Ξ v) sp' a') ⟩
  sub {Γ} {A} Ξ (appNf (wkNf Ξ v) sp') a'
    ≡⟨ cong (λ w → sub {Γ} {A} Ξ (appNf w sp') a') (sym (lookup-wkv Ξ σ z)) ⟩
  sub {Γ} {A} Ξ (appNf (lookup (up A Ξ σ) (wkv Ξ z)) sp') a'
    ∎
  where
  v   = lookup (σ ⇑ Ξ) z
  a'  = a [ σ ⇑ Ξ ]
  sp' = sp [ up A Ξ σ ]Sp

subSp-[] Ξ []S       a σ = refl
subSp-[] Ξ (t ∷S ts) a σ = cong₂ _∷S_ (sub-[] Ξ t a σ) (subSp-[] Ξ ts a σ)

appNf-[] t       []S       σ = refl
appNf-[] (lam t) (a ∷S as) σ =
  trans (appNf-[] (sub ε t a) as σ)
        (cong (λ v → appNf v (as [ σ ]Sp)) (sub-[] ε t a σ))

------------------------------------------------------------------------
-- Associativity

↑-∘s : ∀ {Γ Δ Θ A} (σ : Sub Δ Θ) (ρ : Sub Γ Δ)
  → (_↑ {A = A} σ) ∘s (ρ ↑) ≡ (σ ∘s ρ) ↑
↑-∘s {A = A} σ ρ = cong₂ _,s_ (wk1-∘s σ) (nvar-[] vz (ρ ↑))
  where
  wk1-∘s : ∀ {Θ} (σ : Sub _ Θ) → mapS (_[ ρ ↑ ]) (wk1S {A = A} σ) ≡ wk1S (σ ∘s ρ)
  wk1-∘s εs       = refl
  wk1-∘s (σ ,s u) = cong₂ _,s_ (wk1-∘s σ) (wk-[] ε u ρ)

[][]   : ∀ {Γ Δ Θ τ} (t : Nf Θ τ) (σ : Sub Δ Θ) (ρ : Sub Γ Δ)
  → t [ σ ] [ ρ ] ≡ t [ σ ∘s ρ ]
[][]Sp : ∀ {Γ Δ Θ τ τ'} (sp : Sp Θ τ τ') (σ : Sub Δ Θ) (ρ : Sub Γ Δ)
  → sp [ σ ]Sp [ ρ ]Sp ≡ sp [ σ ∘s ρ ]Sp

[][] (lam t) σ ρ = cong lam (trans ([][] t (σ ↑) (ρ ↑)) (cong (t [_]) (↑-∘s σ ρ)))
[][] (ne (x ∙ sp)) σ ρ =
  trans (appNf-[] (lookup σ x) (sp [ σ ]Sp) ρ)
        (cong₂ appNf (sym (lookup-mapS (_[ ρ ]) σ x)) ([][]Sp sp σ ρ))

[][]Sp []S       σ ρ = refl
[][]Sp (t ∷S ts) σ ρ = cong₂ _∷S_ ([][] t σ ρ) ([][]Sp ts σ ρ)

------------------------------------------------------------------------
-- The category of contexts and substitutions

∘s-idr : ∀ {Γ Δ} (σ : Sub Γ Δ) → σ ∘s idS Γ ≡ σ
∘s-idr εs       = refl
∘s-idr (σ ,s u) = cong₂ _,s_ (∘s-idr σ) ([]-id u)

-- precomposing with a weakening drops the last component
wk1S-∘s : ∀ {Γ Δ Θ A} (σ : Sub Δ Θ) (ρ : Sub Γ Δ) (v : Nf Γ A)
  → wk1S σ ∘s (ρ ,s v) ≡ σ ∘s ρ
wk1S-∘s εs       ρ v = refl
wk1S-∘s (σ ,s u) ρ v = cong₂ _,s_ (wk1S-∘s σ ρ v) (drop-[] ε u ρ v)

∘s-idl : ∀ {Γ Δ} (ρ : Sub Γ Δ) → idS Δ ∘s ρ ≡ ρ
∘s-idl εs       = refl
∘s-idl (ρ ,s v) =
  cong₂ _,s_ (trans (wk1S-∘s (idS _) ρ v) (∘s-idl ρ)) (nvar-[] vz (ρ ,s v))

∘s-assoc : ∀ {Γ Δ Θ Ξ} (τ : Sub Θ Ξ) (σ : Sub Δ Θ) (ρ : Sub Γ Δ)
  → (τ ∘s σ) ∘s ρ ≡ τ ∘s (σ ∘s ρ)
∘s-assoc εs       σ ρ = refl
∘s-assoc (τ ,s t) σ ρ = cong₂ _,s_ (∘s-assoc τ σ ρ) ([][] t σ ρ)

------------------------------------------------------------------------
-- Pairing and projections

⊕-∘s : ∀ {Γ Δ Θ Ξ} (ρ : Sub Δ Θ) (σ : Sub Δ Ξ) (τ : Sub Γ Δ)
  → (ρ ⊕ σ) ∘s τ ≡ (ρ ∘s τ) ⊕ (σ ∘s τ)
⊕-∘s ρ εs       τ = refl
⊕-∘s ρ (σ ,s u) τ = cong (_,s u [ τ ]) (⊕-∘s ρ σ τ)

wkTop-⊕ : ∀ {Γ Δ} Θ {τ} (u : Nf Γ τ) (ρ : Sub Δ Γ) (σ : Sub Δ Θ)
  → (wkTop Θ u) [ ρ ⊕ σ ] ≡ u [ ρ ]
wkTop-⊕ ε       u ρ εs       = refl
wkTop-⊕ (Θ ▷ A) u ρ (σ ,s v) =
  trans (drop-[] ε (wkTop Θ u) (ρ ⊕ σ) v) (wkTop-⊕ Θ u ρ σ)

p-⊕ : ∀ {Γ Δ} Θ (ρ : Sub Δ Γ) (σ : Sub Δ Θ) → p {Γ} Θ ∘s (ρ ⊕ σ) ≡ ρ
p-⊕ {Γ} Θ ρ σ = trans (go (idS Γ)) (∘s-idl ρ)
  where
  go : ∀ {Ξ} (τ : Sub Γ Ξ) → mapS (wkTop Θ) τ ∘s (ρ ⊕ σ) ≡ τ ∘s ρ
  go εs       = refl
  go (τ ,s u) = cong₂ _,s_ (go τ) (wkTop-⊕ Θ u ρ σ)

q-⊕ : ∀ {Γ Δ} Θ (ρ : Sub Δ Γ) (σ : Sub Δ Θ) → q {Γ} Θ ∘s (ρ ⊕ σ) ≡ σ
q-⊕ ε       ρ εs       = refl
q-⊕ {Γ} (Θ ▷ A) ρ (σ ,s v) =
  cong₂ _,s_ (trans (wk1S-∘s (q {Γ} Θ) (ρ ⊕ σ) v) (q-⊕ Θ ρ σ))
             (nvar-[] vz ((ρ ⊕ σ) ,s v))

------------------------------------------------------------------------
-- Naturality: substituting with a weakened substitution

lookup-wk1S : ∀ {Γ Δ A} Ξ (σ : Sub Γ Δ) {τ} (x : Var (Δ ⧺ Ξ) τ)
  → lookup ((wk1S {A = A} σ) ⇑ Ξ) x ≡ wkNf {Γ} {A} Ξ (lookup (σ ⇑ Ξ) x)
lookup-wk1S ε σ x = lookup-mapS (wkNf ε) σ x
lookup-wk1S {Γ} {Δ} {A} (Ξ ▷ C) σ vz = sym (wk-nvar {Γ} {A} (Ξ ▷ C) vz)
lookup-wk1S {Γ} {Δ} {A} (Ξ ▷ C) σ (vs x) =
  trans (lookup-mapS (wkNf {σ = C} ε) ((wk1S {A = A} σ) ⇑ Ξ) x)
  (trans (cong (wkNf {σ = C} ε) (lookup-wk1S Ξ σ x))
  (trans (wkNf-wkNf {Γ} {A} {C} Ξ ε (lookup (σ ⇑ Ξ) x))
         (cong (wkNf {Γ} {A} (Ξ ▷ C)) (sym (lookup-mapS (wkNf {σ = C} ε) (σ ⇑ Ξ) x)))))

nat-[]   : ∀ {Γ Δ A} Ξ {τ} (t : Nf (Δ ⧺ Ξ) τ) (σ : Sub Γ Δ)
  → t [ (wk1S {A = A} σ) ⇑ Ξ ] ≡ wkNf {Γ} {A} Ξ (t [ σ ⇑ Ξ ])
nat-[]Sp : ∀ {Γ Δ A} Ξ {τ τ'} (sp : Sp (Δ ⧺ Ξ) τ τ') (σ : Sub Γ Δ)
  → sp [ (wk1S {A = A} σ) ⇑ Ξ ]Sp ≡ wkSp {Γ} {A} Ξ (sp [ σ ⇑ Ξ ]Sp)

nat-[] Ξ (lam {B} t) σ = cong lam (nat-[] (Ξ ▷ B) t σ)
nat-[] {Γ} {Δ} {A} Ξ (ne (x ∙ sp)) σ =
  trans (cong₂ appNf (lookup-wk1S Ξ σ x) (nat-[]Sp Ξ sp σ))
        (sym (wk-appNf {Γ} {A} Ξ (lookup (σ ⇑ Ξ) x) (sp [ σ ⇑ Ξ ]Sp)))

nat-[]Sp Ξ []S       σ = refl
nat-[]Sp Ξ (t ∷S ts) σ = cong₂ _∷S_ (nat-[] Ξ t σ) (nat-[]Sp Ξ ts σ)

------------------------------------------------------------------------
-- Lifting is pairing with the projection and the variables:
--   ρ ⇑ Θ  =  ⟨ ρ ∘ p , q_Θ ⟩

mapS-id : ∀ {Γ Δ} (σ : Sub Γ Δ) → mapS (λ t → t) σ ≡ σ
mapS-id εs       = refl
mapS-id (σ ,s u) = cong (_,s u) (mapS-id σ)

wk1S-⊕ : ∀ {Γ Δ Θ A} (ρ : Sub Γ Δ) (σ : Sub Γ Θ)
  → wk1S {A = A} (ρ ⊕ σ) ≡ wk1S ρ ⊕ wk1S σ
wk1S-⊕ ρ εs       = refl
wk1S-⊕ ρ (σ ,s u) = cong (_,s _) (wk1S-⊕ ρ σ)

wk1S-∘s-right : ∀ {Γ Δ Θ A} (σ : Sub Δ Θ) (ρ : Sub Γ Δ)
  → wk1S {A = A} (σ ∘s ρ) ≡ σ ∘s wk1S ρ
wk1S-∘s-right εs       ρ = refl
wk1S-∘s-right (σ ,s u) ρ = cong₂ _,s_ (wk1S-∘s-right σ ρ) (sym (nat-[] ε u ρ))

wk1S-p : ∀ {Γ A} Θ → wk1S {A = A} (p {Γ} Θ) ≡ p {Γ} (Θ ▷ A)
wk1S-p {Γ} {A} Θ = go (idS Γ)
  where
  go : ∀ {Ξ} (τ : Sub Γ Ξ)
     → wk1S {A = A} (mapS (wkTop Θ) τ) ≡ mapS (wkTop (Θ ▷ A)) τ
  go εs       = refl
  go (τ ,s u) = cong (_,s _) (go τ)

⇑-pq : ∀ {Γ Δ} (ρ : Sub Γ Δ) Θ → ρ ⇑ Θ ≡ (ρ ∘s p {Γ} Θ) ⊕ q {Γ} Θ
⇑-pq {Γ} ρ ε =
  sym (trans (cong (ρ ∘s_) (mapS-id (idS Γ))) (∘s-idr ρ))
⇑-pq {Γ} {Δ} ρ (Θ ▷ A) = cong (_,s nvar vz)
  (trans (cong (wk1S {A = A}) (⇑-pq ρ Θ))
  (trans (wk1S-⊕ (ρ ∘s p {Γ} Θ) (q {Γ} Θ))
         (cong (_⊕ wk1S (q {Γ} Θ))
               (trans (wk1S-∘s-right ρ (p {Γ} Θ)) (cong (ρ ∘s_) (wk1S-p {Γ} Θ))))))
