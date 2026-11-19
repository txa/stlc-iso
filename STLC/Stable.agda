{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Coherence from (S), (N) and (St).
--
--   (S)  sound      : φ ~ ψ  →  ⟦ φ ⟧ = ⟦ ψ ⟧              (STLC.Sound)
--   (N)  normal     : φ ~ dr h  for an insertion form h  (STLC.Coherence)
--   (St) stable     : ⟦ dr h ⟧ = ⟦ h ⟧I                    (here)
--
-- In the paper hereditary permutations are a set of terms.  Here they
-- are an inductive family with a meaning ⟦ h ⟧I, so we also need that
-- this representation is faithful: ⟦ h ⟧I = ⟦ h' ⟧I → h = h'.  This is a
-- statement about terms only; it does not mention derivations.
------------------------------------------------------------------------
module STLC.Stable where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads using (_≈_; FH; fh-lam; FH-unique; heads-free; FH-nvar; FH-ne2nf)
open import STLC.Thin using (cancel)
open import STLC.Iso
open import STLC.Coherence
open import STLC.Sound
open import STLC.Actions
open import STLC.Derivable using (wkC⟨⟩; wkC-nvar; eta-lams)

------------------------------------------------------------------------
-- The meaning of an insertion form, as a closed term:
--   λ y₁ … yₙ. a (⟦ h₁ ⟧I ⟨ y_{i₁} ⟩) …

⟦_⟧I : ∀ {A B} → HPi A B → Map A B
spH  : ∀ {Δ As Bs n} → HPsi As Bs → All (Var Δ) Bs → Sp Δ (As ⇒* n) (ι n)

⟦ hpi {As} {Bs} {n} hs ⟧I = lams Bs (ne2nf (wkMany Bs vz) (spH hs (vars (ε ▷ (As ⇒* n)) Bs)))

spH nil           []A = []S
spH (cons i h hs) env = ⟦ h ⟧I ⟨ nvar (pk i env) ⟩ ∷S spH hs (rest i env)

------------------------------------------------------------------------
-- (St) stability:  ⟦ dr h ⟧ = ⟦ h ⟧I

stable : ∀ {A B} (h : HPi A B) → fw C⟦ dr h ⟧ ≡ ⟦ h ⟧I
spI≡   : ∀ {Δ As Bs n} (hs : HPsi As Bs) (env : All (Var Δ) Bs)
  → spI {n = n} hs env ≡ spH hs env

stable (hpi {As} {Bs} {n} hs) =
  trans (sym (idr⟨⟩ D))
  (trans (sym (eta-lams Bs (D ⟨ v0 ⟩)))
  (trans (cong (λ t → lams Bs (appNf t (spOf (mapA nvar env))))
               (trans (wkC⟨⟩ Bs D v0) (cong (D ⟨_⟩) (wkC-nvar Bs vz))))
         (cong (lams Bs) (trans (act-drs hs x []S env) (cong (ne2nf x) (spI≡ hs env))))))
  where
  D   = fw C⟦ drs hs {n} ⟧
  env = vars (ε ▷ (As ⇒* n)) Bs
  x   = wkMany Bs (vz {ε} {As ⇒* n})

spI≡ nil           []A = refl
spI≡ (cons i h hs) env =
  cong₂ _∷S_ (cong (λ t → t ⟨ nvar (pk i env) ⟩) (stable h)) (spI≡ hs (rest i env))

-- the meaning of  dr h  in the empty context
meaning-dr : ∀ {A B} (h : HPi A B) → to⟦ dr h ⟧ {ε} ≡ ⟦ h ⟧I
meaning-dr h = trans (cong fw (closed (dr h))) (stable h)

------------------------------------------------------------------------
-- Faithfulness of insertion forms:  ⟦ h ⟧I = ⟦ h' ⟧I → h = h'

-- the input is the head of ⟦ h ⟧I
FH-lams : ∀ {Δ σ n} Bs {x : Var Δ σ} {t : Nf (Δ ++C Bs) (ι n)}
  → FH (wkMany Bs x) t → FH x (lams Bs t)
FH-lams []       p = p
FH-lams (B ∷ Bs) p = fh-lam (FH-lams Bs p)

fhI : ∀ {A B} (h : HPi A B) → FH vz ⟦ h ⟧I
fhI (hpi {As} {Bs} {n} hs) = FH-lams Bs (FH-ne2nf (wkMany Bs vz) _)

fhI⟨⟩ : ∀ {Δ A B} (h : HPi A B) (y : Var Δ A) → FH y (⟦ h ⟧I ⟨ nvar y ⟩)
fhI⟨⟩ h y = heads-free (εs ,s nvar y) (fhI h) (FH-nvar y)

lam-inj : ∀ {Γ A B} {t t' : Nf (Γ ▷ A) B} → lam t ≡ lam t' → t ≡ t'
lam-inj refl = refl

lams-inj : ∀ {Δ n} Bs {t t' : Nf (Δ ++C Bs) (ι n)} → lams Bs t ≡ lams Bs t' → t ≡ t'
lams-inj []       e = e
lams-inj (B ∷ Bs) e = lams-inj Bs (lam-inj e)

faithfulI : ∀ {A B} (h h' : HPi A B) → ⟦ h ⟧I ≡ ⟦ h' ⟧I → h ≡ h'
faithfulS : ∀ {Δ As Bs n} (hs hs' : HPsi As Bs) (env : All (Var Δ) Bs)
  → distinct env → spH {n = n} hs env ≡ spH hs' env → hs ≡ hs'

faithfulI (hpi {As} {Bs} {n} hs) h' e with unhp2 h'
... | un2 hs' = cong hpi (faithfulS hs hs' env (distinct-vars _ Bs) (ne-sp (lams-inj Bs e)))
  where
  env = vars (ε ▷ (As ⇒* n)) Bs

faithfulS nil nil []A d e = refl
faithfulS (cons i h hs) (cons i' h' hs') env d e with ∷S-inj e
... | e₁ ,Σ e₂
  with pk-inj i i' env d
         (FH-unique (fhI⟨⟩ h (pk i env))
                    (subst (FH (pk i' env)) (sym e₁) (fhI⟨⟩ h' (pk i' env))))
...   | same with faithfulI h h' (cancel (pk i env) _ _ e₁)
                | faithfulS hs hs' (rest i env) (distinct-rest i env d) e₂
...     | refl | refl = refl

------------------------------------------------------------------------
-- Theorem coh:  two derivations are level-2 equal iff they have the same
-- meaning.  From (N), (S), (St) and faithfulness:
--   ⟦ h ⟧I = ⟦ dr h ⟧ = ⟦ φ ⟧ = ⟦ ψ ⟧ = ⟦ dr h' ⟧ = ⟦ h' ⟧I.

faithful : ∀ {A B} (φ ψ : A ≃ B) → to⟦ φ ⟧ {ε} ≡ to⟦ ψ ⟧ {ε} → φ ~ ψ
faithful φ ψ e with normal φ | normal ψ
... | h ,Σ p | h' ,Σ q
  with faithfulI h h'
         (trans (sym (meaning-dr h))
         (trans (sym (sound p)) (trans e (trans (sound q) (meaning-dr h')))))
...   | refl = ~trans p (~sym q)

coherence : ∀ {A B} (φ ψ : A ≃ B) → (φ ~ ψ → to⟦ φ ⟧ {ε} ≡ to⟦ ψ ⟧ {ε}) × (to⟦ φ ⟧ {ε} ≡ to⟦ ψ ⟧ {ε} → φ ~ ψ)
coherence φ ψ = sound ,Σ faithful φ ψ
