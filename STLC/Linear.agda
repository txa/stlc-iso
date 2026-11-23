{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Lemma (linear matched pairs): no copying.
--
-- In a λI one-sided equation (P), with P_i = λ W. y (…):
--
--   * no parameter variable (from ΓP) occurs in P_i,
--   * a variable y_j of Y occurs in P_i only if the head of Q_j is x_i,
--     and then at most once,
--
-- so the head y of P_i occurs exactly once, and nothing else of ΓP ⧺ Y
-- occurs.  This is relevance of the other side (the components of ρP
-- are λI) plus Lemma (counting): an occurrence of v in P_i produces
-- the head of ρP_v in P_i [ ρP ] = η x_i, which mentions x_i once.
------------------------------------------------------------------------
module STLC.Linear where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads
open import STLC.LamI
open import STLC.Tele
open import STLC.Descent
open import STLC.Count

injL≉injR' : ∀ {Γ} Θ {σ τ} (u : Var Γ σ) (y : Var Θ τ) → 1 ≤ eqv (injL Θ u) (injR {Γ} Θ y) → ⊥
injL≉injR' Θ u y p = injL≉injR Θ u y (eqv-≈ _ _ p)

module LinMP {ΓP ΓQ X Y} {P : Sub (ΓP ⧺ Y) X} {Q : Sub (ΓQ ⧺ X) Y}
           (L : OneSided ΓP ΓQ X Y P Q) where
  open OneSided L
  open OS L

  -- the bound from Lemma (counting) and (P)
  count-bound : ∀ {σ ρ' σ''} (i : Var X σ) (v : Var (ΓP ⧺ Y) ρ') (w : Var (Γ₁ ⧺ X) σ'')
    → LI (lookup P i) → LIS ρP
    → occ v (lookup P i) * occ w (lookup ρP v) ≤ eqv w (injR {Γ₁} X i)
  count-bound i v w lP lρ =
    ≤-trans (cnt-[] (lookup P i) ρP v w lP lρ)
            (≤-≡ (trans (cong (occ w) (eq-at i)) (occ-nvar w (injR {Γ₁} X i))))

  FH-ρP-L : ∀ {σ σ'} (u : Var ΓP σ) {w : Var Γ₁ σ'} → FH w (lookup α u)
    → FH (injL X w) (lookup ρP (injL Y u))
  FH-ρP-L u {w} fw =
    subst (FH (injL X w))
          (sym (trans (lookup-⊕L (α ∘s p {Γ₁} X) (Q ∘s αL X β) u) (lookup-∘s α (p {Γ₁} X) u)))
          (FH-p X fw)

  -- parameters do not occur
  param-free : ∀ {σ ρ'} (i : Var X σ) (u : Var ΓP ρ')
    → LI (lookup P i) → LIS ρP → occ (injL Y u) (lookup P i) ≡ 0
  param-free i u lP lρ with hfα u
  ... | _ ,Σ (w ,Σ fw) =
    ≤-not-pos (occ (injL Y u) (lookup P i))
      (≤-*pos (occ (injL Y u) (lookup P i)) (FH-occ (FH-ρP-L u fw)) (count-bound i (injL Y u) (injL X w) lP lρ))
      (injL≉injR' X w i)

  -- a target variable occurs at most as often as the head of its Q
  -- equals x_i
  target-bound : ∀ {σ ρ' σ''} (i : Var X σ) (j : Var Y ρ') {i'' : Var X σ''}
    → FH (injR {ΓQ} X i'') (lookup Q j)
    → LI (lookup P i) → LIS ρP
    → occ (injR {ΓP} Y j) (lookup P i) ≤ eqv (injR {Γ₁} X i'') (injR {Γ₁} X i)
  target-bound i j {i''} fQ lP lρ =
    ≤-*pos (occ (injR {ΓP} Y j) (lookup P i))
           (FH-occ (subst (FH _) (sym (lookup-ρP j)) (FH-Qα j fQ)))
           (count-bound i (injR {ΓP} Y j) (injR {Γ₁} X i'') lP lρ)

  -- no copying: the head of P_i occurs exactly once
  no-copy : ∀ {σ σ'} (i : Var X σ) (y : Var Y σ')
    → FH (injR {ΓP} Y y) (lookup P i)
    → HeadsIn Q → LI (lookup P i) → LIS ρP
    → occ (injR {ΓP} Y y) (lookup P i) ≡ 1
  no-copy i y fP hQ lP lρ with hQ y
  ... | _ ,Σ (i'' ,Σ fQ) with heads-match i y i'' fP fQ
  ...   | ≈refl =
    ≤-antisym (≤-trans (target-bound i y fQ lP lρ) (≤-≡ (eqv-refl (injR {Γ₁} X i))))
              (FH-occ fP)

------------------------------------------------------------------------
-- Lemma (no stray variables): only the head occurs in P_i

module NoStray (M : MP) where
  open MP M

  stray : ∀ {σ σ'} (i : Var X σ) (y : Var Y σ')
    → FH (injR {ΓP} Y y) (lookup P i)
    → LI (lookup P i) → LIS (OS.ρP left)
    → ∀ {ρ} {v : Var (ΓP ⧺ Y) ρ} → v ∈ lookup P i → v ≈ injR {ΓP} Y y
  stray i y fP lP lρ {v = v} o with split {ΓP} Y v
  ... | inL u = ⊥-elim (0≱1 (LinMP.param-free left i u lP lρ) (∈-occ o))
    where
    0≱1 : ∀ {n} → n ≡ 0 → 1 ≤ n → ⊥
    0≱1 refl ()
  ... | inR j with OS.heads-P right j
  ...   | _ ,Σ (i'' ,Σ fQ)
    with injR-inj {OneSided.Γ₁ left} X i'' i
           (eqv-≈ _ _ (≤-trans (∈-occ o) (LinMP.target-bound left i j fQ lP lρ)))
  ...     | ≈refl with OS.heads-match right j i y fQ fP
  ...       | ≈refl = ≈refl
