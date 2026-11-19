{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Thinnings, renaming and strengthening.
--
--   strengthen1 x t : if only x occurs in t, then t = t' [ x ] for a
--                     term t' in the single variable x
--   cancel x        : renaming by a single variable is injective
------------------------------------------------------------------------
module STLC.Thin where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads
open import STLC.LamI

infix 4 _⊑_
data _⊑_ : Con → Con → Set where
  done : ε ⊑ ε
  drop : ∀ {Δ Γ A} → Δ ⊑ Γ → Δ ⊑ Γ ▷ A
  keep : ∀ {Δ Γ A} → Δ ⊑ Γ → Δ ▷ A ⊑ Γ ▷ A

thin : ∀ {Δ Γ σ} → Δ ⊑ Γ → Var Δ σ → Var Γ σ
thin (drop e) x      = vs (thin e x)
thin (keep e) vz     = vz
thin (keep e) (vs x) = vs (thin e x)

renNf : ∀ {Δ Γ τ} → Δ ⊑ Γ → Nf Δ τ → Nf Γ τ
renSp : ∀ {Δ Γ τ τ'} → Δ ⊑ Γ → Sp Δ τ τ' → Sp Γ τ τ'
renNf e (lam t)       = lam (renNf (keep e) t)
renNf e (ne (x ∙ sp)) = ne (thin e x ∙ renSp e sp)
renSp e []S       = []S
renSp e (t ∷S ts) = renNf e t ∷S renSp e ts

------------------------------------------------------------------------
-- Renaming is injective

vs-inj≡ : ∀ {Γ σ τ} {x y : Var Γ σ} → vs {τ = τ} x ≡ vs y → x ≡ y
vs-inj≡ refl = refl

thin-inj : ∀ {Δ Γ σ} (e : Δ ⊑ Γ) (x y : Var Δ σ) → thin e x ≡ thin e y → x ≡ y
thin-inj (drop e) x      y      eq = thin-inj e x y (vs-inj≡ eq)
thin-inj (keep e) vz     vz     eq = refl
thin-inj (keep e) vz     (vs y) ()
thin-inj (keep e) (vs x) vz     ()
thin-inj (keep e) (vs x) (vs y) eq = cong vs (thin-inj e x y (vs-inj≡ eq))

ne-het : ∀ {Γ ρ₁ ρ₂ n} {a : Var Γ ρ₁} {b : Var Γ ρ₂} {s : Sp Γ ρ₁ (ι n)} {s' : Sp Γ ρ₂ (ι n)}
  → ne (a ∙ s) ≡ ne (b ∙ s') → Σ (ρ₁ ≡ ρ₂) (λ { refl → (a ≡ b) × (s ≡ s') })
ne-het refl = refl ,Σ (refl ,Σ refl)

lam-inj : ∀ {Γ A τ} {a b : Nf (Γ ▷ A) τ} → lam a ≡ lam b → a ≡ b
lam-inj refl = refl

∷-inj : ∀ {Γ A τ ρ} {t t' : Nf Γ A} {ts ts' : Sp Γ τ ρ}
  → (t ∷S ts) ≡ (t' ∷S ts') → (t ≡ t') × (ts ≡ ts')
∷-inj refl = refl ,Σ refl

renNf-inj : ∀ {Δ Γ τ} (e : Δ ⊑ Γ) (t t' : Nf Δ τ) → renNf e t ≡ renNf e t' → t ≡ t'
renSp-inj : ∀ {Δ Γ τ τ'} (e : Δ ⊑ Γ) (sp sp' : Sp Δ τ τ') → renSp e sp ≡ renSp e sp' → sp ≡ sp'

renNf-inj e (lam t) (lam t') eq = cong lam (renNf-inj (keep e) t t' (lam-inj eq))
renNf-inj e (ne (x ∙ sp)) (ne (y ∙ sp')) eq with ne-het eq
... | refl ,Σ (e₁ ,Σ e₂) with thin-inj e x y e₁
...   | refl = cong (λ s → ne (x ∙ s)) (renSp-inj e sp sp' e₂)

renSp-inj e []S       []S         eq = refl
renSp-inj e []S       (t' ∷S ts') ()
renSp-inj e (t ∷S ts) []S         ()
renSp-inj e (t ∷S ts) (t' ∷S ts') eq =
  cong₂ _∷S_ (renNf-inj e t t' (fst (∷-inj eq))) (renSp-inj e ts ts' (snd (∷-inj eq)))

------------------------------------------------------------------------
-- Strengthening: a term whose variables are in the image of e

Im : ∀ {Δ Γ} → Δ ⊑ Γ → ∀ {ρ} → Var Γ ρ → Set
Im {Δ} e {ρ} v = Σ (Var Δ ρ) (λ x → v ≡ thin e x)

lift-im : ∀ {Δ Γ A τ} (e : Δ ⊑ Γ) (t : Nf (Γ ▷ A) τ)
  → (∀ {ρ} {v : Var Γ ρ} → v ∈ lam t → Im e v)
  → (∀ {ρ} {v : Var (Γ ▷ A) ρ} → v ∈ t → Im (keep e) v)
lift-im e t h {v = vz}   o = vz ,Σ refl
lift-im e t h {v = vs v} o with h (o-lam o)
... | x ,Σ refl = vs x ,Σ refl

str   : ∀ {Δ Γ τ} (e : Δ ⊑ Γ) (t : Nf Γ τ)
  → (∀ {ρ} {v : Var Γ ρ} → v ∈ t → Im e v) → Σ (Nf Δ τ) (λ t' → renNf e t' ≡ t)
strSp : ∀ {Δ Γ τ τ'} (e : Δ ⊑ Γ) (sp : Sp Γ τ τ')
  → (∀ {ρ} {v : Var Γ ρ} → v ∈s sp → Im e v) → Σ (Sp Δ τ τ') (λ sp' → renSp e sp' ≡ sp)

str e (lam t) h with str (keep e) t (lift-im e t h)
... | t' ,Σ eq = lam t' ,Σ cong lam eq
str e (ne (x ∙ sp)) h with h o-hd | strSp e sp (λ o → h (o-arg o))
... | x' ,Σ refl | sp' ,Σ eq = ne (x' ∙ sp') ,Σ cong (λ s → ne (thin e x' ∙ s)) eq

strSp e []S       h = []S ,Σ refl
strSp e (t ∷S ts) h with str e t (λ o → h (s-hd o)) | strSp e ts (λ o → h (s-tl o))
... | t' ,Σ e₁ | ts' ,Σ e₂ = (t' ∷S ts') ,Σ cong₂ _∷S_ e₁ e₂

------------------------------------------------------------------------
-- Renaming as substitution

thinS : ∀ {Δ Γ} → Δ ⊑ Γ → Sub Γ Δ
thinS done     = εs
thinS (drop e) = wk1S (thinS e)
thinS (keep e) = thinS e ↑

lookup-thinS : ∀ {Δ Γ σ} (e : Δ ⊑ Γ) (x : Var Δ σ) → lookup (thinS e) x ≡ nvar (thin e x)
lookup-thinS (drop {A = A} e) x =
  trans (lookup-mapS (wkNf {σ = A} ε) (thinS e) x)
        (trans (cong (wkNf ε) (lookup-thinS e x)) (wk-nvar ε (thin e x)))
lookup-thinS (keep e) vz = refl
lookup-thinS (keep {A = A} e) (vs x) =
  trans (lookup-mapS (wkNf {σ = A} ε) (thinS e) x)
        (trans (cong (wkNf ε) (lookup-thinS e x)) (wk-nvar ε (thin e x)))

ren-[]   : ∀ {Δ Γ τ} (e : Δ ⊑ Γ) (t : Nf Δ τ) → renNf e t ≡ t [ thinS e ]
renSp-[] : ∀ {Δ Γ τ τ'} (e : Δ ⊑ Γ) (sp : Sp Δ τ τ') → renSp e sp ≡ sp [ thinS e ]Sp
ren-[] e (lam t) = cong lam (ren-[] (keep e) t)
ren-[] e (ne (x ∙ sp)) =
  sym (trans (cong₂ appNf (lookup-thinS e x) (sym (renSp-[] e sp)))
             (appNf-ne2nf (thin e x) []S (renSp e sp)))
renSp-[] e []S       = refl
renSp-[] e (t ∷S ts) = cong₂ _∷S_ (ren-[] e t) (renSp-[] e ts)

------------------------------------------------------------------------
-- Single variables

empty : ∀ Γ → ε ⊑ Γ
empty ε       = done
empty (Γ ▷ A) = drop (empty Γ)

varThin : ∀ {Γ σ} → Var Γ σ → ε ▷ σ ⊑ Γ
varThin {Γ ▷ σ} vz = keep (empty Γ)
varThin (vs x)     = drop (varThin x)

thin-varThin : ∀ {Γ σ} (x : Var Γ σ) → thin (varThin x) vz ≡ x
thin-varThin vz     = refl
thin-varThin (vs x) = cong vs (thin-varThin x)

thinS-empty : ∀ Γ → thinS (empty Γ) ≡ εs
thinS-empty ε       = refl
thinS-empty (Γ ▷ A) = cong (wk1S {A = A}) (thinS-empty Γ)

thinS-varThin : ∀ {Γ σ} (x : Var Γ σ) → thinS (varThin x) ≡ εs ,s nvar x
thinS-varThin {Γ ▷ σ} vz = cong (λ s → wk1S {A = σ} s ,s nvar vz) (thinS-empty Γ)
thinS-varThin (vs {τ = A} x) =
  trans (cong (wk1S {A = A}) (thinS-varThin x)) (cong (εs ,s_) (wk-nvar ε x))

ren1 : ∀ {Γ σ τ} (x : Var Γ σ) (t : Nf (ε ▷ σ) τ) → renNf (varThin x) t ≡ t [ εs ,s nvar x ]
ren1 x t = trans (ren-[] (varThin x) t) (cong (t [_]) (thinS-varThin x))

-- renaming by a single variable is injective
cancel : ∀ {Γ σ τ} (x : Var Γ σ) (t t' : Nf (ε ▷ σ) τ)
  → t [ εs ,s nvar x ] ≡ t' [ εs ,s nvar x ] → t ≡ t'
cancel x t t' eq = renNf-inj (varThin x) t t' (trans (ren1 x t) (trans eq (sym (ren1 x t'))))

-- a term in which only x occurs is a term in the single variable x
strengthen1 : ∀ {Γ σ τ} (x : Var Γ σ) (t : Nf Γ τ)
  → (∀ {ρ} {v : Var Γ ρ} → v ∈ t → v ≈ x)
  → Σ (Nf (ε ▷ σ) τ) (λ t' → t ≡ t' [ εs ,s nvar x ])
strengthen1 x t only with str (varThin x) t h
  where
  h : ∀ {ρ} {v : Var _ ρ} → v ∈ t → Im (varThin x) v
  h o with only o
  ... | ≈refl = vz ,Σ sym (thin-varThin x)
... | t' ,Σ eq = t' ,Σ trans (sym eq) (ren1 x t')
