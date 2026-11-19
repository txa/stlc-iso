{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Occurrences and heads (Lemmas noncreation and heads of the note).
--
--   x ∈ t        the variable x occurs in t
--   FH x t       t = λΘ. x' sp  with x' = x weakened past Θ  (free head)
--   BH i t       t = λΘ. y sp  with y the i-th binder of Θ   (bound head)
--
-- Positions of binders are positions of arguments in the type
-- (Arg τ σ), since normal forms are η-long.
------------------------------------------------------------------------
module STLC.Heads where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst

------------------------------------------------------------------------
-- Variables of possibly different types

infix 4 _≈_
data _≈_ {Γ σ} (x : Var Γ σ) : ∀ {τ} → Var Γ τ → Set where
  ≈refl : x ≈ x

------------------------------------------------------------------------
-- Occurrences

infix 4 _∈_ _∈s_
data _∈_  : ∀ {Γ σ τ}    → Var Γ σ → Nf Γ τ → Set
data _∈s_ : ∀ {Γ σ τ τ'} → Var Γ σ → Sp Γ τ τ' → Set

data _∈_ where
  o-lam : ∀ {Γ σ A τ} {x : Var Γ σ} {t : Nf (Γ ▷ A) τ} → vs x ∈ t → x ∈ lam t
  o-hd  : ∀ {Γ σ n} {x : Var Γ σ} {sp : Sp Γ σ (ι n)} → x ∈ ne (x ∙ sp)
  o-arg : ∀ {Γ σ ρ n} {x : Var Γ σ} {y : Var Γ ρ} {sp : Sp Γ ρ (ι n)}
        → x ∈s sp → x ∈ ne (y ∙ sp)

data _∈s_ where
  s-hd : ∀ {Γ σ A τ τ'} {x : Var Γ σ} {t : Nf Γ A} {ts : Sp Γ τ τ'}
       → x ∈ t → x ∈s (t ∷S ts)
  s-tl : ∀ {Γ σ A τ τ'} {x : Var Γ σ} {t : Nf Γ A} {ts : Sp Γ τ τ'}
       → x ∈s ts → x ∈s (t ∷S ts)

ne-case : ∀ {Γ σ ρ n} {y : Var Γ σ} {z : Var Γ ρ} {sp : Sp Γ ρ (ι n)}
  → y ∈ ne (z ∙ sp) → (y ≈ z) ⊎ (y ∈s sp)
ne-case o-hd      = inl ≈refl
ne-case (o-arg q) = inr q

-- occurrences in a weakening come from the original term
∈-wk  : ∀ {Γ A} Ξ {σ τ} (t : Nf (Γ ⧺ Ξ) τ) {y : Var ((Γ ▷ A) ⧺ Ξ) σ}
  → y ∈ wkNf {Γ} {A} Ξ t → Σ (Var (Γ ⧺ Ξ) σ) (λ x → (y ≡ wkv Ξ x) × (x ∈ t))
∈s-wk : ∀ {Γ A} Ξ {σ τ τ'} (sp : Sp (Γ ⧺ Ξ) τ τ') {y : Var ((Γ ▷ A) ⧺ Ξ) σ}
  → y ∈s wkSp {Γ} {A} Ξ sp → Σ (Var (Γ ⧺ Ξ) σ) (λ x → (y ≡ wkv Ξ x) × (x ∈s sp))

∈-wk Ξ (lam {B} t) (o-lam p) with ∈-wk (Ξ ▷ B) t p
... | vz   ,Σ (() ,Σ _)
... | vs x ,Σ (refl ,Σ q) = x ,Σ (refl ,Σ o-lam q)
∈-wk Ξ (ne (z ∙ sp)) p with ne-case p
... | inl ≈refl = z ,Σ (refl ,Σ o-hd)
... | inr q with ∈s-wk Ξ sp q
...   | x ,Σ (e ,Σ r) = x ,Σ (e ,Σ o-arg r)

∈s-wk Ξ []S       ()
∈s-wk Ξ (t ∷S ts) (s-hd p) with ∈-wk Ξ t p
... | x ,Σ (e ,Σ r) = x ,Σ (e ,Σ s-hd r)
∈s-wk Ξ (t ∷S ts) (s-tl p) with ∈s-wk Ξ ts p
... | x ,Σ (e ,Σ r) = x ,Σ (e ,Σ s-tl r)

-- occurrences in an η-expansion
∈s-snoc : ∀ {Γ σ ρ A B} (sp : Sp Γ ρ (A ⇒ B)) (v : Nf Γ A) {y : Var Γ σ}
  → y ∈s snocS sp v → (y ∈s sp) ⊎ (y ∈ v)
∈s-snoc []S       v (s-hd p) = inr p
∈s-snoc []S       v (s-tl ())
∈s-snoc (t ∷S ts) v (s-hd p) = inl (s-hd p)
∈s-snoc (t ∷S ts) v (s-tl p) with ∈s-snoc ts v p
... | inl q = inl (s-tl q)
... | inr q = inr q

∈-ne2nf : ∀ {Γ ρ τ σ} (x : Var Γ ρ) (sp : Sp Γ ρ τ) {y : Var Γ σ}
  → y ∈ ne2nf x sp → (y ≈ x) ⊎ (y ∈s sp)
∈-ne2nf {τ = ι n}   x sp p = ne-case p
∈-ne2nf {τ = A ⇒ B} x sp (o-lam p) with ∈-ne2nf (vs x) (snocS (wkSp ε sp) (nvar vz)) p
... | inl ≈refl = inl ≈refl
... | inr q with ∈s-snoc (wkSp ε sp) (nvar vz) q
...   | inl r with ∈s-wk ε sp r
...     | x' ,Σ (refl ,Σ s) = inr s
∈-ne2nf {τ = A ⇒ B} x sp (o-lam p) | inr q | inr r with ∈-ne2nf vz []S r
... | inl ()
... | inr ()

∈-nvar : ∀ {Γ ρ σ} (x : Var Γ ρ) {y : Var Γ σ} → y ∈ nvar x → y ≈ x
∈-nvar x p with ∈-ne2nf x []S p
... | inl e  = e
... | inr ()

-- occurrences in a hereditary substitution, and in an application
∈-sub    : ∀ {Δ A} Ξ {σ τ} (t : Nf ((Δ ▷ A) ⧺ Ξ) τ) (a : Nf (Δ ⧺ Ξ) A) {y : Var (Δ ⧺ Ξ) σ}
  → y ∈ sub {Δ} {A} Ξ t a → (wkv Ξ y ∈ t) ⊎ ((top {Δ} {A} Ξ ∈ t) × (y ∈ a))
∈s-sub   : ∀ {Δ A} Ξ {σ τ τ'} (sp : Sp ((Δ ▷ A) ⧺ Ξ) τ τ') (a : Nf (Δ ⧺ Ξ) A)
  {y : Var (Δ ⧺ Ξ) σ}
  → y ∈s subSp {Δ} {A} Ξ sp a → (wkv Ξ y ∈s sp) ⊎ ((top {Δ} {A} Ξ ∈s sp) × (y ∈ a))
∈-appNf  : ∀ {Γ ρ τ σ} (t : Nf Γ ρ) (sp : Sp Γ ρ τ) {y : Var Γ σ}
  → y ∈ appNf t sp → (y ∈ t) ⊎ (y ∈s sp)

∈-sub {Δ} {A} Ξ (lam {B} t) a (o-lam p) with ∈-sub (Ξ ▷ B) t (wkNf ε a) p
... | inl q = inl (o-lam q)
... | inr (q ,Σ r) with ∈-wk ε a r
...   | x ,Σ (refl ,Σ s) = inr (o-lam q ,Σ s)
∈-sub {Δ} {A} Ξ (ne (h ∙ sp)) a p with look {Δ} {A} Ξ h
... | same rewrite lk-top {Δ} {A} Ξ with ∈-appNf a (subSp Ξ sp a) p
...   | inl q = inr (o-hd ,Σ q)
...   | inr q with ∈s-sub Ξ sp a q
...     | inl r        = inl (o-arg r)
...     | inr (r ,Σ s) = inr (o-arg r ,Σ s)
∈-sub {Δ} {A} Ξ (ne (h ∙ sp)) a p | diff z rewrite lk-wkv {Δ} {A} Ξ z with ne-case p
... | inl ≈refl = inl o-hd
... | inr q with ∈s-sub Ξ sp a q
...   | inl r        = inl (o-arg r)
...   | inr (r ,Σ s) = inr (o-arg r ,Σ s)

∈s-sub Ξ []S       a ()
∈s-sub Ξ (t ∷S ts) a (s-hd p) with ∈-sub Ξ t a p
... | inl q        = inl (s-hd q)
... | inr (q ,Σ r) = inr (s-hd q ,Σ r)
∈s-sub Ξ (t ∷S ts) a (s-tl p) with ∈s-sub Ξ ts a p
... | inl q        = inl (s-tl q)
... | inr (q ,Σ r) = inr (s-tl q ,Σ r)

∈-appNf t       []S       p = inl p
∈-appNf (lam t) (b ∷S bs) p with ∈-appNf (sub ε t b) bs p
... | inr q = inr (s-tl q)
... | inl q with ∈-sub ε t b q
...   | inl r        = inl (o-lam r)
...   | inr (_ ,Σ r) = inr (s-hd r)

------------------------------------------------------------------------
-- Lemma (no creation): a variable occurring in t [ ρ ] occurs in ρ_v
-- for some v occurring in t.

record Src {Γ Δ} (ρ : Sub Γ Δ) (P : ∀ {τ} → Var Δ τ → Set) {σ} (y : Var Γ σ) : Set where
  constructor src
  field
    {ty} : Ty
    v    : Var Δ ty
    occ  : P v
    hit  : y ∈ lookup ρ v

nocreate   : ∀ {Γ Δ τ σ} (t : Nf Δ τ) (ρ : Sub Γ Δ) {y : Var Γ σ}
  → y ∈ t [ ρ ] → Src ρ (_∈ t) y
nocreateSp : ∀ {Γ Δ τ τ' σ} (sp : Sp Δ τ τ') (ρ : Sub Γ Δ) {y : Var Γ σ}
  → y ∈s sp [ ρ ]Sp → Src ρ (_∈s sp) y

nocreate (lam {A} t) ρ (o-lam p) with nocreate t (ρ ↑) p
... | src vz _ h with ∈-nvar vz h
...   | ()
nocreate (lam {A} t) ρ (o-lam p) | src (vs v) o h
  with ∈-wk ε (lookup ρ v) (subst (_ ∈_) (lookup-mapS (wkNf {σ = A} ε) ρ v) h)
... | x ,Σ (refl ,Σ q) = src v (o-lam o) q
nocreate (ne (x ∙ sp)) ρ p with ∈-appNf (lookup ρ x) (sp [ ρ ]Sp) p
... | inl q = src x o-hd q
... | inr q with nocreateSp sp ρ q
...   | src v o h = src v (o-arg o) h

nocreateSp []S       ρ ()
nocreateSp (t ∷S ts) ρ (s-hd p) with nocreate t ρ p
... | src v o h = src v (s-hd o) h
nocreateSp (t ∷S ts) ρ (s-tl p) with nocreateSp ts ρ p
... | src v o h = src v (s-tl o) h

-- the converse direction is not needed: substitution may erase.

------------------------------------------------------------------------
-- Heads

data FH : ∀ {Γ σ τ} → Var Γ σ → Nf Γ τ → Set where
  fh-lam : ∀ {Γ σ A τ} {x : Var Γ σ} {t : Nf (Γ ▷ A) τ} → FH (vs x) t → FH x (lam t)
  fh-ne  : ∀ {Γ σ n} {x : Var Γ σ} {sp : Sp Γ σ (ι n)} → FH x (ne (x ∙ sp))

-- positions of arguments in a type, i.e. of binders in an η-long term
data Arg : Ty → Ty → Set where
  az : ∀ {A B}   → Arg (A ⇒ B) A
  as : ∀ {A B C} → Arg B C → Arg (A ⇒ B) C

data BH : ∀ {Γ τ σ} → Arg τ σ → Nf Γ τ → Set where
  bh-here  : ∀ {Γ A τ} {t : Nf (Γ ▷ A) τ} → FH vz t → BH az (lam t)
  bh-there : ∀ {Γ A τ σ} {i : Arg τ σ} {t : Nf (Γ ▷ A) τ} → BH i t → BH (as i) (lam t)

-- every normal form has exactly one head, free or bound
data Head {Γ τ} (t : Nf Γ τ) : Set where
  free  : ∀ {σ} (x : Var Γ σ) → FH x t → Head t
  bound : ∀ {σ} (i : Arg τ σ) → BH i t → Head t

head : ∀ {Γ τ} (t : Nf Γ τ) → Head t
head (ne (x ∙ sp)) = free x fh-ne
head (lam t) with head t
... | free vz     h = bound az (bh-here h)
... | free (vs x) h = free x (fh-lam h)
... | bound i     h = bound (as i) (bh-there h)

FH-unique : ∀ {Γ σ σ' τ} {x : Var Γ σ} {x' : Var Γ σ'} {t : Nf Γ τ}
  → FH x t → FH x' t → x ≈ x'
FH-unique (fh-lam h) (fh-lam h') with FH-unique h h'
... | ≈refl = ≈refl
FH-unique fh-ne fh-ne = ≈refl

-- a head is not both free and bound
FH-BH : ∀ {Γ τ σ σ'} {x : Var Γ σ} {i : Arg τ σ'} {t : Nf Γ τ} → FH x t → BH i t → ⊥
FH-BH (fh-lam h) (bh-here h') with FH-unique h h'
... | ()
FH-BH (fh-lam h) (bh-there b) = FH-BH h b

BH-unique : ∀ {Γ τ σ σ'} {i : Arg τ σ} {i' : Arg τ σ'} {t : Nf Γ τ}
  → BH i t → BH i' t → Σ (σ ≡ σ') (λ { refl → i ≡ i' })
BH-unique (bh-here h)  (bh-here h')  = refl ,Σ refl
BH-unique (bh-here h)  (bh-there b') = ⊥-elim (FH-BH h b')
BH-unique (bh-there b) (bh-here h')  = ⊥-elim (FH-BH h' b)
BH-unique (bh-there b) (bh-there b') with BH-unique b b'
... | refl ,Σ refl = refl ,Σ refl

------------------------------------------------------------------------
-- Free heads under weakening, substitution and application

FH-wk : ∀ {Γ A} Ξ {σ τ} {x : Var (Γ ⧺ Ξ) σ} {t : Nf (Γ ⧺ Ξ) τ}
  → FH x t → FH (wkv {Γ} {A} Ξ x) (wkNf Ξ t)
FH-wk Ξ (fh-lam h) = fh-lam (FH-wk (Ξ ▷ _) h)
FH-wk Ξ fh-ne      = fh-ne

-- substituting for another variable keeps a free head
FH-sub : ∀ {Δ A} Ξ {σ τ} {x : Var (Δ ⧺ Ξ) σ} (t : Nf ((Δ ▷ A) ⧺ Ξ) τ) (a : Nf (Δ ⧺ Ξ) A)
  → FH (wkv Ξ x) t → FH x (sub {Δ} {A} Ξ t a)
FH-sub Ξ (lam {B} t) a (fh-lam h) = fh-lam (FH-sub (Ξ ▷ B) t (wkNf ε a) h)
FH-sub {Δ} {A} Ξ {x = x} (ne (.(wkv Ξ x) ∙ sp)) a fh-ne rewrite lk-wkv {Δ} {A} Ξ x = fh-ne

-- applying a term with a free head keeps the head
FH-appNf : ∀ {Γ σ ρ τ} {x : Var Γ σ} (t : Nf Γ ρ) (sp : Sp Γ ρ τ)
  → FH x t → FH x (appNf t sp)
FH-appNf t       []S       h          = h
FH-appNf (lam t) (b ∷S bs) (fh-lam h) = FH-appNf (sub ε t b) bs (FH-sub ε t b h)

FH-ne2nf : ∀ {Γ σ τ} (x : Var Γ σ) (sp : Sp Γ σ τ) → FH x (ne2nf x sp)
FH-ne2nf {τ = ι n}   x sp = fh-ne
FH-ne2nf {τ = A ⇒ B} x sp = fh-lam (FH-ne2nf (vs x) _)

FH-nvar : ∀ {Γ σ} (x : Var Γ σ) → FH x (nvar x)
FH-nvar x = FH-ne2nf x []S

------------------------------------------------------------------------
-- Lemma (heads).  Let ρ : Sub Γ Δ.
--  (1) if the head of t is the variable v of Δ and ρ_v has free head h,
--      then t [ ρ ] has free head h;
--  (2) if the head of t is its i-th binder, so is the head of t [ ρ ].

heads-free : ∀ {Γ Δ τ σ σ'} {v : Var Δ σ} {h : Var Γ σ'} {t : Nf Δ τ} (ρ : Sub Γ Δ)
  → FH v t → FH h (lookup ρ v) → FH h (t [ ρ ])
heads-free {v = v} {t = lam {A} t} ρ (fh-lam p) hv =
  fh-lam (heads-free (ρ ↑) p
           (subst (FH _) (sym (lookup-mapS (wkNf {σ = A} ε) ρ v)) (FH-wk ε hv)))
heads-free {v = v} {t = ne (.v ∙ sp)} ρ fh-ne hv = FH-appNf (lookup ρ v) (sp [ ρ ]Sp) hv

heads-bound : ∀ {Γ Δ τ σ} {i : Arg τ σ} {t : Nf Δ τ} (ρ : Sub Γ Δ)
  → BH i t → BH i (t [ ρ ])
heads-bound ρ (bh-here p)  = bh-here (heads-free (ρ ↑) p (FH-nvar vz))
heads-bound ρ (bh-there b) = bh-there (heads-bound (ρ ↑) b)
