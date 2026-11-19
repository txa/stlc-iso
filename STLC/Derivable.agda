{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Hereditary permutations are derivable: the meaning of the derivation
-- der h  is the hereditary permutation  ⟦ h ⟧H  (HP-derivable of
-- STLC.Iso).  With the characterisation this gives surjectivity: every
-- isomorphism is the meaning of a derivation.
--
-- As in STLC.Actions we only compute how meanings act on argument
-- lists, and recover the term by η:  t = λ ys. t ys.
------------------------------------------------------------------------
module STLC.Derivable where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Tele using (sub-as)
open import STLC.Iso
open import STLC.Sound
open import STLC.Actions using (spOf; appNf-++; ++S-assoc; act-arr; act-swap)
open import STLC.Link using (characterisation-HP; splitA-eq)

------------------------------------------------------------------------
-- Weakening past a list of binders

wkC : ∀ {Γ τ} Bs → Nf Γ τ → Nf (Γ ++C Bs) τ
wkC []       t = t
wkC (B ∷ Bs) t = wkC Bs (wkNf {σ = B} ε t)

wkC-nvar : ∀ {Γ τ} Bs (x : Var Γ τ) → wkC Bs (nvar x) ≡ nvar (wkMany Bs x)
wkC-nvar []       x = refl
wkC-nvar (B ∷ Bs) x = trans (cong (wkC Bs) (wk-nvar ε x)) (wkC-nvar Bs (vs x))

wkC-app1 : ∀ {Γ σ τ} Bs (u : Nf Γ (σ ⇒ τ)) (a : Nf Γ σ)
  → wkC Bs (appNf u (a ∷S []S)) ≡ appNf (wkC Bs u) (wkC Bs a ∷S []S)
wkC-app1 []       u a = refl
wkC-app1 (B ∷ Bs) u a =
  trans (cong (wkC Bs) (wk-appNf ε u (a ∷S []S))) (wkC-app1 Bs (wkNf ε u) (wkNf ε a))

wkC⟨⟩ : ∀ {Γ A τ} Bs (t : Map A τ) (u : Nf Γ A) → wkC Bs (t ⟨ u ⟩) ≡ t ⟨ wkC Bs u ⟩
wkC⟨⟩ []       t u = refl
wkC⟨⟩ (B ∷ Bs) t u = trans (cong (wkC Bs) (sym (nat-[] {A = B} ε t (εs ,s u)))) (wkC⟨⟩ Bs t (wkNf ε u))

-- η for lams:  t = λ ys. t ys
eta-lams : ∀ {Γ n} Bs (t : Nf Γ (Bs ⇒* n))
  → lams Bs (appNf (wkC Bs t) (spOf (mapA nvar (vars Γ Bs)))) ≡ t
eta-lams []                 t       = refl
eta-lams {Γ} (B ∷ Bs) (lam t) = cong lam
  (trans (cong (lams Bs) key) (eta-lams Bs t))
  where
  sp = spOf (mapA nvar (vars (Γ ▷ B) Bs))
  key : appNf (wkC Bs (wkNf ε (lam t))) (nvar (wkMany Bs vz) ∷S sp) ≡ appNf (wkC Bs t) sp
  key =
    trans (sym (appNf-++ (wkC Bs (wkNf ε (lam t))) (nvar (wkMany Bs vz) ∷S []S) sp))
          (cong (λ v → appNf v sp)
            (trans (cong (λ a → appNf (wkC Bs (wkNf ε (lam t))) (a ∷S []S)) (sym (wkC-nvar Bs vz)))
            (trans (sym (wkC-app1 Bs (wkNf ε (lam t)) (nvar vz)))
                   (cong (wkC Bs) (sub-η-ren ε t)))))

------------------------------------------------------------------------
-- Actions on argument lists

mapA-++ : ∀ {A} {P Q : A → Set} (f : ∀ {x} → P x → Q x) {xs ys} (ps : All P xs) (qs : All P ys)
  → mapA f (ps ++A qs) ≡ mapA f ps ++A mapA f qs
mapA-++ f []A       qs = refl
mapA-++ f (p ∷A ps) qs = cong (f p ∷A_) (mapA-++ f ps qs)

act-moveTo : ∀ {Θ B n} Cs {Rest} (F : Nf Θ (B ⇒ ((Cs ++ Rest) ⇒* n)))
  (as₁ : All (Nf Θ) Cs) (y : Nf Θ B) (as₂ : All (Nf Θ) Rest)
  → appNf (fw C⟦ moveTo {n = n} Cs ⟧ ⟨ F ⟩) (spOf (as₁ ++A (y ∷A as₂)))
  ≡ appNf F (y ∷S spOf (as₁ ++A as₂))
act-moveTo []       F []A        y as₂ = cong (λ t → appNf t (y ∷S spOf as₂)) (idl⟨⟩ F)
act-moveTo (C ∷ Cs) F (a ∷A as₁) y as₂ =
  trans (cong (λ t → appNf t (a ∷S spOf (as₁ ++A (y ∷A as₂)))) (assoc⟨⟩ (arrC idNf M) swapNf F))
  (trans (act-arr idNf M (swapNf ⟨ F ⟩) a (spOf (as₁ ++A (y ∷A as₂))))
  (trans (cong (λ u → appNf (M ⟨ appNf (swapNf ⟨ F ⟩) (u ∷S []S) ⟩) (spOf (as₁ ++A (y ∷A as₂))))
               (idl⟨⟩ a))
  (trans (act-moveTo Cs (appNf (swapNf ⟨ F ⟩) (a ∷S []S)) as₁ y as₂)
  (trans (appNf-++ (swapNf ⟨ F ⟩) (a ∷S []S) (y ∷S spOf (as₁ ++A as₂)))
         (act-swap F a y (spOf (as₁ ++A as₂)))))))
  where
  M = fw C⟦ moveTo Cs ⟧

-- substituting a variable into a closed map applied to v0
sub-v0 : ∀ {Θ A B} (t : Map A B) (u : Nf Θ A) → sub ε (t ⟨ v0 ⟩) u ≡ t ⟨ u ⟩
sub-v0 {Θ} t u =
  trans (sub-as ε (t ⟨ v0 ⟩) u)
  (trans (⟨⟩-[] t v0 (idS Θ ,s u)) (cong (t ⟨_⟩) (nvar-[] vz (idS Θ ,s u))))

------------------------------------------------------------------------
-- The meaning of  der h  is  ⟦ h ⟧H

derivable : ∀ {Γ A B} (h : HP A B) → fw C⟦ der h ⟧ ⟨ v0 {Γ} ⟩ ≡ ⟦ h ⟧H {Γ}
act-ders  : ∀ {Θ As Bs n ρ} (hs : HPs As Bs) (x : Var Θ ρ) (sp₀ : Sp Θ ρ (As ⇒* n))
  (env : All (Var Θ) Bs)
  → appNf (fw C⟦ ders hs {n} ⟧ ⟨ ne2nf x sp₀ ⟩) (spOf (mapA nvar env))
  ≡ ne2nf x (sp₀ ++S spine hs env)

derivable {Γ} (hp {As} {Bs} {n} hs) =
  trans (sym (eta-lams Bs (D ⟨ v0 ⟩)))
  (trans (cong (λ t → lams Bs (appNf t (spOf (mapA nvar env))))
               (trans (wkC⟨⟩ Bs D v0) (cong (D ⟨_⟩) (wkC-nvar Bs vz))))
         (cong (lams Bs) (act-ders hs (wkMany Bs vz) []S env)))
  where
  D   = fw C⟦ ders hs {n} ⟧
  env = vars (Γ ▷ (As ⇒* n)) Bs

act-ders []H x sp₀ []A = trans (idl⟨⟩ (ne2nf x sp₀)) (cong (ne2nf x) (sym (++S-[] sp₀)))
act-ders {Θ} (ins Bs₁ h hs) x sp₀ env with splitA Bs₁ env | splitA-eq Bs₁ env
... | e₁ ,Σ (y ∷A e₂) | refl =
  trans (cong (λ t → appNf t (spOf (mapA nvar (e₁ ++A (y ∷A e₂))))) (assoc⟨⟩ M G N))
  (trans (cong (λ as → appNf (M ⟨ G ⟨ N ⟩ ⟩) (spOf as)) (mapA-++ nvar e₁ (y ∷A e₂)))
  (trans (act-moveTo Bs₁ (G ⟨ N ⟩) (mapA nvar e₁) (nvar y) (mapA nvar e₂))
  (trans (act-arr Dh Dhs N (nvar y) (spOf (mapA nvar e₁ ++A mapA nvar e₂)))
  (trans (cong (λ as → appNf (Dhs ⟨ appNf N (Dh ⟨ nvar y ⟩ ∷S []S) ⟩) (spOf as))
               (sym (mapA-++ nvar e₁ e₂)))
  (trans (cong (λ t → appNf (Dhs ⟨ t ⟩) (spOf (mapA nvar (e₁ ++A e₂))))
               (appNf-ne2nf x sp₀ (Dh ⟨ nvar y ⟩ ∷S []S)))
  (trans (act-ders hs x (sp₀ ++S (Dh ⟨ nvar y ⟩ ∷S []S)) (e₁ ++A e₂))
  (trans (cong (ne2nf x) (++S-assoc sp₀ (Dh ⟨ nvar y ⟩ ∷S []S) (spine hs (e₁ ++A e₂))))
         (cong (λ t → ne2nf x (sp₀ ++S (t ∷S spine hs (e₁ ++A e₂))))
               (trans (sym (sub-v0 Dh (nvar y)))
                      (cong (λ t → sub ε t (nvar y)) (derivable {Θ} h)))))))))))
  where
  M   = fw C⟦ moveTo Bs₁ ⟧
  Dh  = fw C⟦ der h ⟧
  Dhs = fw C⟦ ders hs ⟧
  G   = arrC Dh Dhs
  N   = ne2nf x sp₀

------------------------------------------------------------------------
-- The statements of STLC.Iso

hp-derivable : HP-derivable
hp-derivable h = trans (cong fw (closed (der h))) (trans (sym ([]-id _)) (derivable {ε} h))

-- every isomorphism is the meaning of a derivation
surjective : ∀ {A B} (i : A ≅ B) → Σ (A ≃ B) (λ φ → to⟦ φ ⟧ {ε} ≡ fw (pair i))
surjective i with characterisation-HP i
... | h ,Σ e = der h ,Σ trans (hp-derivable h) e
