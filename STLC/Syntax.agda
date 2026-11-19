{-# OPTIONS --rewriting --local-confluence-check #-}
------------------------------------------------------------------------
-- Simply typed λ-calculus with → only: types, contexts, variables,
-- β-normal η-long forms in spine form, weakening, η-expansion and
-- hereditary substitution (after Keller & Altenkirch, MSFP 2010).
--
-- Positions in a context are given as telescopes: we weaken and
-- substitute at σ in  (Γ ▷ σ) ⧺ Δ.  Three rewrite rules for ⧺ make the
-- context equations that arise when two such operations are commuted
-- definitional.
------------------------------------------------------------------------
module STLC.Syntax where

open import STLC.Prelude
open import Agda.Builtin.Equality.Rewrite

------------------------------------------------------------------------
-- Types

infixr 6 _⇒_
data Ty : Set where
  ι   : Nat → Ty              -- base types
  _⇒_ : Ty → Ty → Ty

-- every type is  As ⇒* n  for a unique list As and base type n
infixr 6 _⇒*_
_⇒*_ : List Ty → Nat → Ty
[]       ⇒* n = ι n
(A ∷ As) ⇒* n = A ⇒ (As ⇒* n)

------------------------------------------------------------------------
-- Contexts, telescopes and variables

infixl 5 _▷_
data Con : Set where
  ε   : Con
  _▷_ : Con → Ty → Con

infixl 5 _⧺_
_⧺_ : Con → Con → Con
Γ ⧺ ε       = Γ
Γ ⧺ (Δ ▷ A) = (Γ ⧺ Δ) ▷ A

⧺-ε : ∀ Δ → ε ⧺ Δ ≡ Δ
⧺-ε ε       = refl
⧺-ε (Δ ▷ A) = cong (_▷ A) (⧺-ε Δ)
{-# REWRITE ⧺-ε #-}

⧺-assoc : ∀ Γ Δ Θ → (Γ ⧺ Δ) ⧺ Θ ≡ Γ ⧺ (Δ ⧺ Θ)
⧺-assoc Γ Δ ε       = refl
⧺-assoc Γ Δ (Θ ▷ A) = cong (_▷ A) (⧺-assoc Γ Δ Θ)

⧺-▷ : ∀ Γ Δ A Θ → Γ ⧺ ((Δ ▷ A) ⧺ Θ) ≡ ((Γ ⧺ Δ) ▷ A) ⧺ Θ
⧺-▷ Γ Δ A ε       = refl
⧺-▷ Γ Δ A (Θ ▷ B) = cong (_▷ B) (⧺-▷ Γ Δ A Θ)
{-# REWRITE ⧺-assoc ⧺-▷ #-}

data Var : Con → Ty → Set where
  vz : ∀ {Γ σ}   → Var (Γ ▷ σ) σ
  vs : ∀ {Γ σ τ} → Var Γ σ → Var (Γ ▷ τ) σ

-- the variable at a position
top : ∀ {Γ σ} Δ → Var ((Γ ▷ σ) ⧺ Δ) σ
top ε       = vz
top (Δ ▷ A) = vs (top Δ)

-- weakening a variable: insert σ at a position
wkv : ∀ {Γ σ τ} Δ → Var (Γ ⧺ Δ) τ → Var ((Γ ▷ σ) ⧺ Δ) τ
wkv ε       y      = vs y
wkv (Δ ▷ A) vz     = vz
wkv (Δ ▷ A) (vs y) = vs (wkv Δ y)

-- looking up a variable relative to a position
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

lk : ∀ {Γ σ ρ} Δ → Var ((Γ ▷ σ) ⧺ Δ) ρ → (σ ≡ ρ) ⊎ Var (Γ ⧺ Δ) ρ
lk ε       vz     = inl refl
lk ε       (vs y) = inr y
lk (Δ ▷ A) vz     = inr vz
lk (Δ ▷ A) (vs y) with lk Δ y
... | inl e = inl e
... | inr z = inr (vs z)

-- the same, as a view (for proofs)
data Look {Γ σ} (Δ : Con) : ∀ {ρ} → Var ((Γ ▷ σ) ⧺ Δ) ρ → Set where
  same : Look Δ (top Δ)
  diff : ∀ {ρ} (z : Var (Γ ⧺ Δ) ρ) → Look Δ (wkv Δ z)

look : ∀ {Γ σ ρ} Δ (y : Var ((Γ ▷ σ) ⧺ Δ) ρ) → Look {Γ} {σ} Δ y
look ε       vz     = same
look ε       (vs y) = diff y
look (Δ ▷ A) vz     = diff vz
look (Δ ▷ A) (vs y) with look Δ y
... | same   = same
... | diff z = diff (vs z)

------------------------------------------------------------------------
-- Normal forms.  Nf is η-long: λ at arrow types, neutral at base types.
-- A neutral is a head variable applied to a spine.

infixr 5 _∷S_
infix  4 _∙_
data Nf (Γ : Con) : Ty → Set
data Ne (Γ : Con) : Ty → Set
data Sp (Γ : Con) : Ty → Ty → Set

data Nf Γ where
  lam : ∀ {σ τ} → Nf (Γ ▷ σ) τ → Nf Γ (σ ⇒ τ)
  ne  : ∀ {n} → Ne Γ (ι n) → Nf Γ (ι n)

data Ne Γ where
  _∙_ : ∀ {σ τ} → Var Γ σ → Sp Γ σ τ → Ne Γ τ

-- Sp Γ σ τ : arguments taking a function of type σ to type τ
data Sp Γ where
  []S  : ∀ {σ} → Sp Γ σ σ
  _∷S_ : ∀ {σ τ ρ} → Nf Γ σ → Sp Γ τ ρ → Sp Γ (σ ⇒ τ) ρ

------------------------------------------------------------------------
-- Weakening: insert σ at a position

wkNf : ∀ {Γ σ} Δ {τ} → Nf (Γ ⧺ Δ) τ → Nf ((Γ ▷ σ) ⧺ Δ) τ
wkSp : ∀ {Γ σ} Δ {τ ρ} → Sp (Γ ⧺ Δ) τ ρ → Sp ((Γ ▷ σ) ⧺ Δ) τ ρ

wkNf Δ (lam t)       = lam (wkNf (Δ ▷ _) t)
wkNf Δ (ne (y ∙ sp)) = ne (wkv Δ y ∙ wkSp Δ sp)

wkSp Δ []S       = []S
wkSp Δ (t ∷S ts) = wkNf Δ t ∷S wkSp Δ ts

-- add an argument at the end of a spine
snocS : ∀ {Γ ρ σ τ} → Sp Γ ρ (σ ⇒ τ) → Nf Γ σ → Sp Γ ρ τ
snocS []S       u = u ∷S []S
snocS (t ∷S ts) u = t ∷S snocS ts u

------------------------------------------------------------------------
-- η-expansion

nvar  : ∀ {Γ σ} → Var Γ σ → Nf Γ σ
ne2nf : ∀ {Γ σ τ} → Var Γ σ → Sp Γ σ τ → Nf Γ τ

nvar x = ne2nf x []S

ne2nf {τ = ι n}   x sp = ne (x ∙ sp)
ne2nf {τ = σ ⇒ τ} x sp = lam (ne2nf (vs x) (snocS (wkSp ε sp) (nvar vz)))

------------------------------------------------------------------------
-- Hereditary substitution of u for σ in  (Γ ▷ σ) ⧺ Δ

sub   : ∀ {Γ σ} Δ {τ} → Nf ((Γ ▷ σ) ⧺ Δ) τ → Nf (Γ ⧺ Δ) σ → Nf (Γ ⧺ Δ) τ
subSp : ∀ {Γ σ} Δ {τ ρ} → Sp ((Γ ▷ σ) ⧺ Δ) τ ρ → Nf (Γ ⧺ Δ) σ → Sp (Γ ⧺ Δ) τ ρ
appNf : ∀ {Γ σ τ} → Nf Γ σ → Sp Γ σ τ → Nf Γ τ

sub Δ (lam t) u = lam (sub (Δ ▷ _) t (wkNf ε u))
sub Δ (ne (y ∙ sp)) u with lk Δ y
... | inl refl = appNf u (subSp Δ sp u)
... | inr z    = ne (z ∙ subSp Δ sp u)

subSp Δ []S       u = []S
subSp Δ (t ∷S ts) u = sub Δ t u ∷S subSp Δ ts u

appNf t       []S       = t
appNf (lam t) (u ∷S us) = appNf (sub ε t u) us

------------------------------------------------------------------------
-- Composition of open maps.  A map A → B over Γ is a normal form in
-- Γ ▷ A of type B; composition is hereditary substitution.

infixr 9 _∘_
_∘_ : ∀ {Γ A B C} → Nf (Γ ▷ B) C → Nf (Γ ▷ A) B → Nf (Γ ▷ A) C
_∘_ {A = A} g f = sub ε (wkNf {σ = A} (ε ▷ _) g) f

idNf : ∀ {Γ A} → Nf (Γ ▷ A) A
idNf = nvar vz
