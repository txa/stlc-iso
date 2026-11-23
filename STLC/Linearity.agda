{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Corollary (linearity): both components of an isomorphism are linear
-- terms.  The input occurs exactly once, and every bound variable
-- occurs exactly once in the body of its binder.
--
-- A binder of P_i is a target variable of the matched pair one level
-- down, where Lemma (linear matched pairs) counts it: it occurs once,
-- as the head of exactly one argument of P_i.
------------------------------------------------------------------------
module STLC.Linearity where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads
open import STLC.LamI
open import STLC.Tele
open import STLC.Iso
open import STLC.Descent
open import STLC.Count
open import STLC.Linear
open import STLC.Char using (LIMP; LI-down; flip; flip-LI; LIS-,s; LIS-εs)

------------------------------------------------------------------------
-- Linear terms: every binder occurs exactly once in its body

data Lin  : ∀ {Γ τ}    → Nf Γ τ    → Set
data Lins : ∀ {Γ τ τ'} → Sp Γ τ τ' → Set

data Lin where
  lin-lam : ∀ {Γ A τ} {t : Nf (Γ ▷ A) τ} → occ vz t ≡ 1 → Lin t → Lin (lam t)
  lin-ne  : ∀ {Γ σ n} {x : Var Γ σ} {sp : Sp Γ σ (ι n)} → Lins sp → Lin (ne (x ∙ sp))

data Lins where
  lins-nil  : ∀ {Γ τ} → Lins {Γ} {τ} {τ} []S
  lins-cons : ∀ {Γ A τ τ'} {t : Nf Γ A} {ts : Sp Γ τ τ'} → Lin t → Lins ts → Lins (t ∷S ts)

------------------------------------------------------------------------
-- Telescopes

occ-unlam : ∀ {Γ τ σ} (x : Var Γ σ) (t : Nf Γ τ) → occ (injL (args τ) x) (unlam t) ≡ occ x t
occ-unlam {τ = ι n}   x t       = refl
occ-unlam {τ = A ⇒ B} x (lam t) =
  trans (cong (λ z → occ z (unlam t)) (injL-⧺ (ε ▷ A) (args B) x)) (occ-unlam (vs x) t)

Lin-unlam : ∀ {Γ τ} (t : Nf Γ τ)
  → (∀ {σ} (k : Var (args τ) σ) → occ (injR {Γ} (args τ) k) (unlam t) ≡ 1) → Lin (unlam t) → Lin t
Lin-unlam {τ = ι n} t h l = l
Lin-unlam {Γ} {τ = A ⇒ B} (lam t) h l =
  lin-lam (trans (sym (occ-unlam vz t))
                 (trans (cong (λ z → occ z (unlam t)) (sym (injR-⧺L {Γ} (ε ▷ A) (args B) vz)))
                        (h (injL {ε ▷ A} (args B) vz))))
          (Lin-unlam t (λ k → trans (cong (λ z → occ z (unlam t)) (sym (injR-⧺R {Γ} (ε ▷ A) (args B) k)))
                                    (h (injR {ε ▷ A} (args B) k))) l)

Lins-spToSub : ∀ {Γ σ n} (sp : Sp Γ σ (ι n))
  → (∀ {ρ} (k : Var (args σ) ρ) → Lin (lookup (spToSub sp) k)) → Lins sp
Lins-spToSub []S h = lins-nil
Lins-spToSub (_∷S_ {A} {B} t ts) h =
  lins-cons (subst Lin (lookup-⊕L (εs ,s t) (spToSub ts) vz) (h (injL {ε ▷ A} (args B) vz)))
            (Lins-spToSub ts (λ k → subst Lin (lookup-⊕R (εs ,s t) (spToSub ts) k)
                                             (h (injR {ε ▷ A} (args B) k))))

------------------------------------------------------------------------
-- Counting over the components of a substitution

sumS : ∀ {Γ Δ σ} → Var Γ σ → Sub Γ Δ → Nat
sumS x εs       = 0
sumS x (ρ ,s u) = sumS x ρ + occ x u

sumS-⊕ : ∀ {Γ Δ Θ σ} (x : Var Γ σ) (ρ : Sub Γ Δ) (s : Sub Γ Θ) → sumS x (ρ ⊕ s) ≡ sumS x ρ + sumS x s
sumS-⊕ x ρ εs       = sym (+0 (sumS x ρ))
sumS-⊕ x ρ (s ,s u) = trans (cong (_+ occ x u) (sumS-⊕ x ρ s)) (+-assoc (sumS x ρ) (sumS x s) (occ x u))

occs-spToSub : ∀ {Γ σ ρ n} (x : Var Γ σ) (sp : Sp Γ ρ (ι n)) → occs x sp ≡ sumS x (spToSub sp)
occs-spToSub x []S       = refl
occs-spToSub x (t ∷S ts) =
  trans (cong (occ x t +_) (occs-spToSub x ts)) (sym (sumS-⊕ x (εs ,s t) (spToSub ts)))

sumS-ge : ∀ {Γ Δ σ ρ'} (x : Var Γ σ) (ρ : Sub Γ Δ) (l : Var Δ ρ') → occ x (lookup ρ l) ≤ sumS x ρ
sumS-ge x (ρ ,s u) vz     = ≤-+l (sumS x ρ)
sumS-ge x (ρ ,s u) (vs l) = ≤-trans (sumS-ge x ρ l) (≤-+r (sumS x ρ) (occ x u))

sumS-le0 : ∀ {Γ Δ σ} (x : Var Γ σ) (ρ : Sub Γ Δ)
  → (∀ {ρ'} (l : Var Δ ρ') → occ x (lookup ρ l) ≤ 0) → sumS x ρ ≤ 0
sumS-le0 x εs       h = z≤n
sumS-le0 x (ρ ,s u) h = +-mono (sumS-le0 x ρ (λ l → h (vs l))) (h vz)

sumS-le1 : ∀ {Γ Δ σ σ₀} (x : Var Γ σ) (ρ : Sub Γ Δ) (l₀ : Var Δ σ₀)
  → (∀ {ρ'} (l : Var Δ ρ') → occ x (lookup ρ l) ≤ eqv l₀ l) → sumS x ρ ≤ 1
sumS-le1 x (ρ ,s u) vz      h = +-mono (sumS-le0 x ρ (λ l → h (vs l))) (h vz)
sumS-le1 x (ρ ,s u) (vs l₀) h = ≤-trans (+-mono (sumS-le1 x ρ l₀ (λ l → h (vs l))) (h vz)) (≤-≡ refl)

eqv-injR : ∀ {Γ} Θ {σ τ} (a : Var Θ σ) (b : Var Θ τ) → eqv (injR {Γ} Θ a) (injR {Γ} Θ b) ≡ eqv a b
eqv-injR (Θ ▷ B) vz     vz     = refl
eqv-injR (Θ ▷ B) vz     (vs b) = refl
eqv-injR (Θ ▷ B) (vs a) vz     = refl
eqv-injR {Γ} (Θ ▷ B) (vs a) (vs b) = eqv-injR {Γ} Θ a b

eqv-injR-injL : ∀ {Γ} Θ {σ τ} (k : Var Θ σ) (u : Var Γ τ) → eqv (injR {Γ} Θ k) (injL Θ u) ≡ 0
eqv-injR-injL (Θ ▷ B) vz     u = refl
eqv-injR-injL (Θ ▷ B) (vs k) u = eqv-injR-injL Θ k u

------------------------------------------------------------------------
-- One level of the descent: the binders of P_i occur exactly once,
-- given that the arguments of P_i are linear.

linP : (M : MP) → LIMP M → ∀ {σ σ'} (i : Var (MP.X M) σ) (y : Var (MP.Y M) σ')
  (fP : FH (injR {MP.ΓP M} (MP.Y M) y) (lookup (MP.P M) i))
  (fQ : FH (injR {MP.ΓQ M} (MP.X M) i) (lookup (MP.Q M) y))
  → (∀ {ρ} (l : Var (args σ') ρ) → Lin (lookup (MP.Q (down M i y fP fQ)) l))
  → Lin (lookup (MP.P M) i)
linP M lm {σ} {σ'} i y fP fQ hv =
  Lin-unlam (lookup P i) binders
    (subst Lin (sym (snd (FH-unlam fP))) (lin-ne (Lins-spToSub v hv)))
  where
  open MP M
  M' = down M i y fP fQ
  l' = LI-down M lm i y fP fQ
  v  = fst (FH-unlam fP)

  -- k occurs exactly once among the arguments of P_i
  once : ∀ {ρ} (k : Var (args σ) ρ) → sumS (injR {ΓP ⧺ Y} (args σ) k) (spToSub v) ≡ 1
  once k with OS.heads-P (MP.left M') k
  ... | _ ,Σ (l₀ ,Σ fl) with OS.heads-P (MP.right M') l₀
  ...   | _ ,Σ (k' ,Σ fk) with OS.heads-match (MP.left M') k l₀ k' fl fk
  ...     | ≈refl =
    ≤-antisym
      (sumS-le1 _ (spToSub v) l₀ (λ l →
         ≤-trans (LinMP.target-bound (MP.right M') l k fl (LIMP.lQ l' l) (LIMP.lρR l'))
                 (≤-≡ (eqv-injR {OneSided.Γ₁ (MP.right M')} (args σ') l₀ l))))
      (≤-trans (FH-occ fk) (sumS-ge _ (spToSub v) l₀))

  binders : ∀ {ρ} (k : Var (args σ) ρ) → occ (injR {ΓP ⧺ Y} (args σ) k) (unlam (lookup P i)) ≡ 1
  binders k =
    trans (cong (occ (injR {ΓP ⧺ Y} (args σ) k)) (snd (FH-unlam fP)))
    (trans (cong₂ _+_ (eqv-injR-injL (args σ) k (injR {ΓP} Y y)) (occs-spToSub _ v))
           (once k))

------------------------------------------------------------------------
-- The descent

lin : (M : MP) → LIMP M → ∀ {σ σ'} (i : Var (MP.X M) σ) (y : Var (MP.Y M) σ')
  (fP : FH (injR {MP.ΓP M} (MP.Y M) y) (lookup (MP.P M) i))
  (fQ : FH (injR {MP.ΓQ M} (MP.X M) i) (lookup (MP.Q M) y))
  → Acc2 σ σ' → Lin (lookup (MP.P M) i) × Lin (lookup (MP.Q M) y)
lin M lm {σ} {σ'} i y fP fQ (acc2 a) =
  linP M lm i y fP fQ hv ,Σ linP (flip M) (flip-LI M lm) y i fQ fP hu
  where
  M' = down M i y fP fQ
  l' = LI-down M lm i y fP fQ

  hv : ∀ {ρ} (l : Var (args σ') ρ) → Lin (lookup (MP.Q M') l)
  hv l with OS.heads-P (MP.right M') l
  ... | _ ,Σ (k ,Σ fk) with OS.heads-P (MP.left M') k
  ...   | _ ,Σ (l'' ,Σ fl) with OS.heads-match (MP.right M') l k l'' fk fl
  ...     | ≈refl = snd (lin M' l' k l fl fk (a (argPos σ k) (argPos σ' l)))

  hu : ∀ {ρ} (k : Var (args σ) ρ) → Lin (lookup (MP.P M') k)
  hu k with OS.heads-P (MP.left M') k
  ... | _ ,Σ (l ,Σ fl) with OS.heads-P (MP.right M') l
  ...   | _ ,Σ (k' ,Σ fk) with OS.heads-match (MP.left M') k l k' fl fk
  ...     | ≈refl = fst (lin M' l' k l fl fk (a (argPos σ k) (argPos σ' l)))

------------------------------------------------------------------------
-- Corollary (linearity)

linearity : ∀ {A B} (iso : A ≅ B)
  → (Lin (fw (pair iso)) × occ vz (fw (pair iso)) ≡ 1)
  × (Lin (bw (pair iso)) × occ vz (bw (pair iso)) ≡ 1)
linearity {A} {B} iso with OS.heads-P (MP.left (initial iso)) vz
                         | OS.heads-P (MP.right (initial iso)) vz
... | _ ,Σ (vs () ,Σ _) | _
... | _ | _ ,Σ (vs () ,Σ _)
... | _ ,Σ (vz ,Σ fP) | _ ,Σ (vz ,Σ fQ) =
  (fst L ,Σ LinMP.no-copy (MP.left M0) vz vz fP (OS.heads-P (MP.right M0)) (LIMP.lP l0 vz) (LIMP.lρL l0))
  ,Σ (snd L ,Σ LinMP.no-copy (MP.right M0) vz vz fQ (OS.heads-P (MP.left M0)) (LIMP.lQ l0 vz) (LIMP.lρR l0))
  where
  M0 = initial iso
  l0 : LIMP M0
  l0 = record { lP = LIS-,s LIS-εs (fst (relevance iso)) ; lQ = LIS-,s LIS-εs (snd (relevance iso))
              ; lαL = LIS-εs ; lβL = LIS-εs ; lαR = LIS-εs ; lβR = LIS-εs }
  L = lin M0 l0 vz vz fP fQ (acc2-all B A)
