{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Coherence, part (S): soundness of the level-2 equations, and
-- soundness of derivations (their components are isomorphisms).
--
-- The components of a derivation are natural in the context: at Γ they
-- are the closed components weakened (Lemma nat).  So everything is
-- reduced to closed maps  t : Nf (ε ▷ A) B , applied by substitution
--   t ⟨ u ⟩ = t [ εs ,s u ] ,
-- and each level-2 equation is a short hereditary-substitution
-- computation on closed maps.
------------------------------------------------------------------------
module STLC.Sound where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Tele using (sub-as)
open import STLC.Iso
open import STLC.Coherence

------------------------------------------------------------------------
-- Closed maps

Map : Ty → Ty → Set
Map A B = Nf (ε ▷ A) B

infixl 10 _⟨_⟩
_⟨_⟩ : ∀ {Γ A B} → Map A B → Nf Γ A → Nf Γ B
t ⟨ u ⟩ = t [ εs ,s u ]

⟨⟩-[] : ∀ {Γ Δ A B} (t : Map A B) (u : Nf Δ A) (ρ : Sub Γ Δ) → (t ⟨ u ⟩) [ ρ ] ≡ t ⟨ u [ ρ ] ⟩
⟨⟩-[] t u ρ = [][] t (εs ,s u) ρ

assoc⟨⟩ : ∀ {Γ A B C} (h : Map B C) (g : Map A B) (f : Nf Γ A) → (h ⟨ g ⟩) ⟨ f ⟩ ≡ h ⟨ g ⟨ f ⟩ ⟩
assoc⟨⟩ h g f = ⟨⟩-[] h g (εs ,s f)

idl⟨⟩ : ∀ {Γ A} (f : Nf Γ A) → idNf ⟨ f ⟩ ≡ f
idl⟨⟩ f = nvar-[] vz (εs ,s f)

idr⟨⟩ : ∀ {A B} (f : Map A B) → f ⟨ idNf ⟩ ≡ f
idr⟨⟩ f = []-id f

------------------------------------------------------------------------
-- Variables, the weakening substitution, β

v0 : ∀ {Γ A} → Nf (Γ ▷ A) A
v0 = nvar vz

v1 : ∀ {Γ A B} → Nf (Γ ▷ A ▷ B) A
v1 = nvar (vs vz)

v2 : ∀ {Γ A B C} → Nf (Γ ▷ A ▷ B ▷ C) A
v2 = nvar (vs (vs vz))

π : ∀ {Γ A} → Sub (Γ ▷ A) Γ
π {Γ} {A} = wk1S {A = A} (idS Γ)

lookπ : ∀ {Γ A τ} (x : Var Γ τ) → lookup (π {Γ} {A}) x ≡ nvar (vs x)
lookπ {Γ} {A} x =
  trans (lookup-mapS (wkNf {σ = A} ε) (idS Γ) x)
        (trans (cong (wkNf ε) (lookup-idS x)) (wk-nvar ε x))

nvπ : ∀ {Γ A τ} (x : Var Γ τ) → nvar x [ π {Γ} {A} ] ≡ nvar (vs x)
nvπ x = trans (nvar-[] x π) (lookπ x)

lookππ : ∀ {Γ A B τ} (x : Var Γ τ) → lookup (π {Γ} {A} ∘s π {Γ ▷ A} {B}) x ≡ nvar (vs (vs x))
lookππ x = trans (lookup-mapS (λ t → t [ π ]) π x) (trans (cong (λ t → t [ π ]) (lookπ x)) (nvπ (vs x)))

wkπ : ∀ {Γ A τ} (t : Nf Γ τ) → wkNf {Γ} {A} ε t ≡ t [ π ]
wkπ {Γ} {A} t = sym (trans (nat-[] {A = A} ε t (idS Γ)) (cong (wkNf ε) ([]-id t)))

wk⟨v0⟩ : ∀ {Γ A B C} (t : Map A B) → wkNf {Γ ▷ A} {C} ε (t ⟨ v0 ⟩) ≡ t ⟨ v1 ⟩
wk⟨v0⟩ t = trans (wkπ (t ⟨ v0 ⟩)) (trans (⟨⟩-[] t v0 π) (cong (t ⟨_⟩) (nvπ vz)))

v1-π : ∀ {Γ A B C} (w : Nf (Γ ▷ A ▷ B) C) → v1 [ π ,s w ] ≡ v1 {Γ} {A} {B}
v1-π w = trans (nvar-[] (vs vz) (π ,s w)) (lookπ vz)

β : ∀ {Γ Δ A B τ} (t : Nf (Δ ▷ A) B) (ρ : Sub Γ Δ) (u : Nf Γ A) (sp : Sp Γ B τ)
  → appNf (lam t [ ρ ]) (u ∷S sp) ≡ appNf (t [ ρ ,s u ]) sp
β {Γ} t ρ u sp = cong (λ v → appNf v sp)
  (trans (sub-as ε (t [ ρ ↑ ]) u)
  (trans ([][] t (ρ ↑) (idS Γ ,s u))
         (cong (t [_]) (cong₂ _,s_ (trans (wk1S-∘s ρ (idS Γ) u) (∘s-idr ρ))
                                   (nvar-[] vz (idS Γ ,s u))))))

-- substituting into an η-expanded neutral whose head goes to a variable
infixr 5 _∷≡_
_∷≡_ : ∀ {Γ σ τ ρ} {a a' : Nf Γ σ} {s s' : Sp Γ τ ρ} → a ≡ a' → s ≡ s' → (a ∷S s) ≡ (a' ∷S s')
_∷≡_ = cong₂ _∷S_

ne-sub : ∀ {Γ Δ σ τ} (ρ : Sub Γ Δ) (x : Var Δ σ) {y : Var Γ σ} {sp : Sp Δ σ τ} {sp' : Sp Γ σ τ}
  → lookup ρ x ≡ nvar y → sp [ ρ ]Sp ≡ sp' → (ne2nf x sp) [ ρ ] ≡ ne2nf y sp'
ne-sub ρ x {y} {sp} e es =
  trans (ne2nf-[] x sp ρ)
  (trans (cong (λ v → appNf v (sp [ ρ ]Sp)) e)
  (trans (appNf-ne2nf y []S (sp [ ρ ]Sp)) (cong (ne2nf y) es)))

infixr 6 _⊚_
_⊚_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_⊚_ = trans

------------------------------------------------------------------------
-- Composition is substitution

comp-gen : ∀ {Γ A B C} (g : Nf (Γ ▷ B) C) (f : Nf (Γ ▷ A) B) → g ∘ f ≡ g [ π ,s f ]
comp-gen {Γ} {A} {B} g f =
  trans (sub-as ε (wkNf {Γ} {A} (ε ▷ B) g) f)
  (trans (cong (_[ idS (Γ ▷ A) ,s f ]) wk-g)
  (trans ([][] g (π ↑) (idS (Γ ▷ A) ,s f))
         (cong (g [_]) (cong₂ _,s_ (trans (wk1S-∘s π (idS (Γ ▷ A)) f) (∘s-idr π))
                                   (nvar-[] vz (idS (Γ ▷ A) ,s f))))))
  where
  wk-g : wkNf {Γ} {A} (ε ▷ B) g ≡ g [ π ↑ ]
  wk-g = sym (trans (nat-[] {A = A} (ε ▷ B) g (idS Γ)) (cong (wkNf (ε ▷ B)) ([]-id g)))

-- at ε:  g ∘ f ≡ g ⟨ f ⟩
comp-ε : ∀ {A B C} (g : Map B C) (f : Map A B) → g ∘ f ≡ g ⟨ f ⟩
comp-ε g f = comp-gen {ε} g f

------------------------------------------------------------------------
-- The closed operations

arrC : ∀ {A A' B B'} → Map A' A → Map B B' → Map (A ⇒ B) (A' ⇒ B')
arrC h k = lam (k ⟨ ne2nf (vs vz) (h ⟨ v0 ⟩ ∷S []S) ⟩)

cP : ∀ {A B C} → Pair ε A B → Pair ε B C → Pair ε A C
cP p q = fw q ⟨ fw p ⟩ ,P bw p ⟨ bw q ⟩

aP : ∀ {A A' B B'} → Pair ε A A' → Pair ε B B' → Pair ε (A ⇒ B) (A' ⇒ B')
aP p q = arrC (bw p) (fw q) ,P arrC (fw p) (bw q)

C⟦_⟧ : ∀ {A B} → A ≃ B → Pair ε A B
C⟦ idD ⟧    = idNf ,P idNf
C⟦ symD φ ⟧ = op C⟦ φ ⟧
C⟦ φ ⨾ ψ ⟧  = cP C⟦ φ ⟧ C⟦ ψ ⟧
C⟦ φ ⇒≃ ψ ⟧ = aP C⟦ φ ⟧ C⟦ ψ ⟧
C⟦ swap ⟧   = swapNf ,P swapNf

pair-≡ : ∀ {Γ A B} {p q : Pair Γ A B} → fw p ≡ fw q → bw p ≡ bw q → p ≡ q
pair-≡ = cong₂ _,P_

------------------------------------------------------------------------
-- Naturality: the components at Γ are the closed ones, weakened

wkP : ∀ {Γ A B} → Pair ε A B → Pair Γ A B
wkP p = fw p ⟨ v0 ⟩ ,P bw p ⟨ v0 ⟩

id-nat : ∀ {Γ A} → idNf {Γ} {A} ≡ idNf {ε} ⟨ v0 ⟩
id-nat = sym (nvar-[] vz (εs ,s v0))

comp-nat : ∀ {Γ A B C} (g : Map B C) (f : Map A B) → g ⟨ v0 {Γ} ⟩ ∘ f ⟨ v0 ⟩ ≡ (g ∘ f) ⟨ v0 ⟩
comp-nat g f =
  trans (comp-gen (g ⟨ v0 ⟩) (f ⟨ v0 ⟩))
  (trans (⟨⟩-[] g v0 (π ,s f ⟨ v0 ⟩))
  (trans (cong (g ⟨_⟩) (nvar-[] vz (π ,s f ⟨ v0 ⟩)))
  (trans (sym (⟨⟩-[] g f (εs ,s v0)))
         (cong (_⟨ v0 ⟩) (sym (comp-ε g f))))))

arr-nat : ∀ {Γ A A' B B'} (h : ∀ {Δ} → Nf (Δ ▷ A') A) (k : ∀ {Δ} → Nf (Δ ▷ B) B')
  → (∀ {Δ} → h {Δ} ≡ h {ε} ⟨ v0 ⟩) → (∀ {Δ} → k {Δ} ≡ k {ε} ⟨ v0 ⟩)
  → arrNf {Γ} h k ≡ arrC (h {ε}) (k {ε}) ⟨ v0 ⟩
arr-nat {Γ} {A} {A'} {B} {B'} h k nh nk = cong lam (trans l (sym r))
  where
  E : Nf (Γ ▷ (A ⇒ B) ▷ A') B
  E = ne2nf (vs vz) (h {ε} ⟨ v0 ⟩ ∷S []S)
  σ : Sub (Γ ▷ (A ⇒ B)) (ε ▷ (A ⇒ B))
  σ = εs ,s v0
  l : sub ε (k {Γ ▷ (A ⇒ B) ▷ A'}) (ne2nf (vs vz) (h {Γ ▷ (A ⇒ B)} ∷S []S)) ≡ k {ε} ⟨ E ⟩
  l = trans (cong₂ (λ a b → sub ε a (ne2nf (vs vz) (b ∷S []S))) (nk {Γ ▷ (A ⇒ B) ▷ A'}) (nh {Γ ▷ (A ⇒ B)}))
      (trans (sub-as ε (k {ε} ⟨ v0 ⟩) E)
      (trans (⟨⟩-[] (k {ε}) v0 (idS _ ,s E))
             (cong (k {ε} ⟨_⟩) (nvar-[] vz (idS _ ,s E)))))
  r : (k {ε} ⟨ ne2nf (vs vz) (h {ε} ⟨ v0 ⟩ ∷S []S) ⟩) [ σ ↑ ] ≡ k {ε} ⟨ E ⟩
  r = trans (⟨⟩-[] (k {ε}) _ (σ ↑))
      (cong (k {ε} ⟨_⟩)
        (ne-sub (σ ↑) (vs vz) (wk-nvar ε vz)
          (trans (⟨⟩-[] (h {ε}) v0 (σ ↑)) (cong (h {ε} ⟨_⟩) (nvar-[] vz (σ ↑))) ∷≡ refl)))

arr-ε : ∀ {A A' B B'} (h : ∀ {Δ} → Nf (Δ ▷ A') A) (k : ∀ {Δ} → Nf (Δ ▷ B) B')
  → (∀ {Δ} → h {Δ} ≡ h {ε} ⟨ v0 ⟩) → (∀ {Δ} → k {Δ} ≡ k {ε} ⟨ v0 ⟩)
  → arrNf {ε} h k ≡ arrC (h {ε}) (k {ε})
arr-ε h k nh nk = trans (arr-nat h k nh nk) ([]-id _)

sw-nat : ∀ {Γ A B C} → swapNf {Γ} {A} {B} {C} ≡ swapNf {ε} ⟨ v0 ⟩
sw-nat {Γ} {A} {B} {C} = sym (cong (λ t → lam (lam t))
  (ne-sub ((σ ↑) ↑) (vs (vs vz))
     (trans (cong (wkNf ε) (wk-nvar ε vz)) (wk-nvar ε (vs vz)))
     (nvar-[] vz ((σ ↑) ↑) ∷≡ trans (nvar-[] (vs vz) ((σ ↑) ↑)) (wk-nvar ε vz) ∷≡ refl)))
  where
  σ : Sub (Γ ▷ (A ⇒ B ⇒ C)) (ε ▷ (A ⇒ B ⇒ C))
  σ = εs ,s v0

nat : ∀ {A B} (φ : A ≃ B) {Γ} → ⟦ φ ⟧ {Γ} ≡ wkP (⟦ φ ⟧ {ε})
nat idD      = pair-≡ id-nat id-nat
nat (symD φ) = cong op (nat φ)
nat (φ ⨾ ψ)  = pair-≡
  (trans (cong₂ _∘_ (cong fw (nat ψ)) (cong fw (nat φ))) (comp-nat (fw (⟦ ψ ⟧ {ε})) (fw (⟦ φ ⟧ {ε}))))
  (trans (cong₂ _∘_ (cong bw (nat φ)) (cong bw (nat ψ))) (comp-nat (bw (⟦ φ ⟧ {ε})) (bw (⟦ ψ ⟧ {ε}))))
nat (φ ⇒≃ ψ) = pair-≡
  (trans (arr-nat _ _ (λ {Δ} → cong bw (nat φ {Δ})) (λ {Δ} → cong fw (nat ψ {Δ})))
         (cong (_⟨ v0 ⟩) (sym (arr-ε _ _ (λ {Δ} → cong bw (nat φ {Δ})) (λ {Δ} → cong fw (nat ψ {Δ}))))))
  (trans (arr-nat _ _ (λ {Δ} → cong fw (nat φ {Δ})) (λ {Δ} → cong bw (nat ψ {Δ})))
         (cong (_⟨ v0 ⟩) (sym (arr-ε _ _ (λ {Δ} → cong fw (nat φ {Δ})) (λ {Δ} → cong bw (nat ψ {Δ}))))))
nat swap     = pair-≡ sw-nat sw-nat

-- the components at ε are the closed semantics
closed : ∀ {A B} (φ : A ≃ B) → ⟦ φ ⟧ {ε} ≡ C⟦ φ ⟧
closed idD      = refl
closed (symD φ) = cong op (closed φ)
closed (φ ⨾ ψ)  = trans (pair-≡ (comp-ε (fw (⟦ ψ ⟧ {ε})) (fw (⟦ φ ⟧ {ε}))) (comp-ε (bw (⟦ φ ⟧ {ε})) (bw (⟦ ψ ⟧ {ε})))) (cong₂ cP (closed φ) (closed ψ))
closed (φ ⇒≃ ψ) = trans
  (pair-≡ (arr-ε _ _ (λ {Δ} → cong bw (nat φ {Δ})) (λ {Δ} → cong fw (nat ψ {Δ})))
          (arr-ε _ _ (λ {Δ} → cong fw (nat φ {Δ})) (λ {Δ} → cong bw (nat ψ {Δ}))))
  (cong₂ aP (closed φ) (closed ψ))
closed swap     = refl

------------------------------------------------------------------------
-- Computation rules for the closed operations

arr-lam : ∀ {Γ A A' B B'} (h : Map A' A) (k : Map B B') (L : Nf (Γ ▷ A) B)
  → arrC h k ⟨ lam L ⟩ ≡ lam (k ⟨ L [ π ,s h ⟨ v0 ⟩ ] ⟩)
arr-lam {Γ} {A} {A'} h k L = cong lam
  (trans (⟨⟩-[] k _ σ↑) (cong (k ⟨_⟩)
  (trans (ne2nf-[] (vs vz) (h ⟨ v0 ⟩ ∷S []S) σ↑)
  (trans (cong₂ (λ f a → appNf f (a ∷S []S)) (wkπ (lam L))
                (trans (⟨⟩-[] h v0 σ↑) (cong (h ⟨_⟩) (nvar-[] vz σ↑))))
         (β L π (h ⟨ v0 ⟩) []S)))))
  where
  σ↑ : Sub (Γ ▷ A') (ε ▷ (A ⇒ _) ▷ A')
  σ↑ = (εs ,s lam L) ↑

arr-id-lam : ∀ {Γ A B B'} (k : Map B B') (L : Nf (Γ ▷ A) B)
  → arrC idNf k ⟨ lam L ⟩ ≡ lam (k ⟨ L ⟩)
arr-id-lam k L = trans (arr-lam idNf k L)
  (cong (λ t → lam (k ⟨ t ⟩)) (trans (cong (λ u → L [ π ,s u ]) (idl⟨⟩ v0)) ([]-id L)))

arr-id : ∀ {A B} → arrC {A} {A} {B} {B} idNf idNf ≡ idNf
arr-id = cong lam (trans (idl⟨⟩ _) (cong (λ u → ne2nf (vs vz) (u ∷S []S)) (idl⟨⟩ v0)))

arr-comp : ∀ {A A' A'' B B' B''} (h2 : Map A'' A') (k2 : Map B' B'') (h1 : Map A' A) (k1 : Map B B')
  → arrC h2 k2 ⟨ arrC h1 k1 ⟩ ≡ arrC (h1 ⟨ h2 ⟩) (k2 ⟨ k1 ⟩)
arr-comp h2 k2 h1 k1 = trans (arr-lam h2 k2 _) (cong lam
  (trans (cong (k2 ⟨_⟩)
           (trans (⟨⟩-[] k1 _ (π ,s h2 ⟨ v0 ⟩))
                  (cong (k1 ⟨_⟩)
                    (ne-sub (π ,s h2 ⟨ v0 ⟩) (vs vz) (lookπ vz)
                      (trans (⟨⟩-[] h1 v0 _)
                        (trans (cong (h1 ⟨_⟩) (nvar-[] vz (π ,s h2 ⟨ v0 ⟩)))
                               (sym (assoc⟨⟩ h1 h2 v0))) ∷≡ refl)))))
         (sym (assoc⟨⟩ k2 k1 _))))

sw-gen : ∀ {Γ A B C} (F : Nf Γ (A ⇒ B ⇒ C))
  → swapNf ⟨ F ⟩ ≡ lam (lam (appNf (F [ π ∘s π ]) (v0 ∷S v1 ∷S []S)))
sw-gen {Γ} {A} {B} {C} F = cong (λ t → lam (lam t))
  (trans (ne2nf-[] (vs (vs vz)) (v0 ∷S v1 ∷S []S) ρ)
         (cong₂ appNf
           (trans (cong (wkNf ε) (wkπ F)) (trans (wkπ (F [ π ])) ([][] F π π)))
           (nvar-[] vz ρ ∷≡ trans (nvar-[] (vs vz) ρ) (wk-nvar ε vz) ∷≡ refl)))
  where
  ρ : Sub (Γ ▷ B ▷ A) (ε ▷ (A ⇒ B ⇒ C) ▷ B ▷ A)
  ρ = ((εs ,s F) ↑) ↑

sw-lam : ∀ {Γ A B C} (X : Nf (Γ ▷ A ▷ B) C)
  → swapNf ⟨ lam (lam X) ⟩ ≡ lam (lam (X [ (π ∘s π) ,s v0 ,s v1 ]))
sw-lam X = trans (sw-gen (lam (lam X)))
  (cong (λ t → lam (lam t)) (trans (β (lam X) (π ∘s π) v0 (v1 ∷S []S)) (β X _ v1 []S)))

sw-sw : ∀ {A B C} → swapNf {ε} {B} {A} {C} ⟨ swapNf {ε} {A} {B} {C} ⟩ ≡ idNf
sw-sw = trans (sw-lam _) (cong (λ t → lam (lam t))
  (ne-sub _ (vs (vs vz)) (lookππ vz)
     (trans (nvar-[] vz _) (sym (wk-nvar ε vz)) ∷≡ nvar-[] (vs vz) _ ∷≡ refl)))

-- naturality of swap
sw-natural : ∀ {A A' B B' C C'} (b : Map B' B) (a : Map A' A) (c : Map C C')
  → arrC b (arrC a c) ⟨ swapNf ⟩ ≡ swapNf ⟨ arrC a (arrC b c) ⟩
sw-natural {A} {A'} {B} {B'} {C} {C'} b a c =
  trans (arr-lam b (arrC a c) _)
  (trans (cong lam (cong (arrC a c ⟨_⟩)
            {y = lam (ne2nf (vs (vs vz)) (v0 ∷S b ⟨ v1 ⟩ ∷S []S))}
            (cong lam (ne-sub _ (vs (vs vz))
               (trans (cong (wkNf ε) (lookπ vz)) (wk-nvar ε (vs vz)))
               (nvar-[] vz _ ∷≡ trans (nvar-[] (vs vz) _) (wk⟨v0⟩ b) ∷≡ refl)))))
  (trans (cong lam (arr-lam a c _))
  (trans (cong (λ t → lam (lam (c ⟨ t ⟩)))
            (ne-sub _ (vs (vs vz)) (lookπ (vs vz))
               (nvar-[] vz _ ∷≡ trans (⟨⟩-[] b v1 _) (cong (b ⟨_⟩) (v1-π _)) ∷≡ refl)))
  (sym
  (trans (cong (swapNf ⟨_⟩)
            {y = lam (lam (c ⟨ ne2nf (vs (vs vz)) (a ⟨ v1 ⟩ ∷S b ⟨ v0 ⟩ ∷S []S) ⟩))}
            (cong lam (trans (arr-lam b c _)
              (cong (λ t → lam (c ⟨ t ⟩))
                (ne-sub _ (vs (vs vz)) (lookπ (vs vz))
                  (trans (cong (_[ π ,s b ⟨ v0 ⟩ ]) (wk⟨v0⟩ a))
                         (trans (⟨⟩-[] a v1 _) (cong (a ⟨_⟩) (v1-π _)))
                   ∷≡ nvar-[] vz _ ∷≡ refl))))))
  (trans (sw-lam _)
         (cong (λ t → lam (lam t))
           (trans (⟨⟩-[] c _ _)
             (cong (c ⟨_⟩)
               (ne-sub _ (vs (vs vz)) (lookππ vz)
                 (trans (⟨⟩-[] a v1 _) (cong (a ⟨_⟩) (nvar-[] (vs vz) _))
                  ∷≡ trans (⟨⟩-[] b v0 _) (cong (b ⟨_⟩) (nvar-[] vz _)) ∷≡ refl)))))))))))

-- the braid equation
sw : ∀ {A B C} → Map (A ⇒ B ⇒ C) (B ⇒ A ⇒ C)
sw {A} {B} {C} = swapNf {ε} {A} {B} {C}

aw : ∀ {X A B C} → Map (X ⇒ A ⇒ B ⇒ C) (X ⇒ B ⇒ A ⇒ C)
aw = arrC idNf sw

sp3 : ∀ {Γ A B C D} → Nf Γ A → Nf Γ B → Nf Γ C → Sp Γ (A ⇒ B ⇒ C ⇒ D) D
sp3 a b c = a ∷S b ∷S c ∷S []S

sw-form : ∀ {A B C D} → sw {A} {B} {C ⇒ D} ≡ lam (lam (lam (ne2nf (vs (vs (vs vz))) (sp3 v1 v2 v0))))
sw-form = cong (λ s → lam (lam (lam (ne2nf (vs (vs (vs vz))) s))))
               (wk-nvar ε vz ∷≡ wk-nvar ε (vs vz) ∷≡ refl)

aw-form : ∀ {A B C D} → aw {A} {B} {C} {D} ≡ lam (lam (lam (ne2nf (vs (vs (vs vz))) (sp3 v2 v0 v1))))
aw-form {A} {B} {C} {D} = cong lam
  (trans (cong (sw ⟨_⟩) e)
  (trans (sw-lam _)
         (cong (λ t → lam (lam t))
           (ne-sub _ (vs (vs (vs vz))) (lookππ (vs vz))
              (nvar-[] (vs (vs vz)) _ ⊚ lookππ vz ∷≡ nvar-[] (vs vz) _ ∷≡ nvar-[] vz _ ∷≡ refl)))))
  where
  e : ne2nf (vs vz) (idNf ⟨ v0 ⟩ ∷S []S)
    ≡ lam (lam (ne2nf {ε ▷ (A ⇒ B ⇒ C ⇒ D) ▷ A ▷ B ▷ C} (vs (vs (vs vz))) (sp3 v2 v1 v0)))
  e = cong (λ u → ne2nf (vs vz) (u ∷S []S)) (idl⟨⟩ v0)
    ⊚ cong (λ s → lam (lam (ne2nf (vs (vs (vs vz))) s)))
           ((cong (wkNf ε) (wk-nvar ε vz) ⊚ wk-nvar ε (vs vz)) ∷≡ wk-nvar ε vz ∷≡ refl)

braid-closed : ∀ {A B C D}
  → sw {B} {C} {A ⇒ D} ⟨ aw {B} {A} {C} {D} ⟨ sw {A} {B} {C ⇒ D} ⟩ ⟩
  ≡ aw {C} {A} {B} {D} ⟨ sw {A} {C} {B ⇒ D} ⟨ aw {A} {B} {C} {D} ⟩ ⟩
braid-closed {A} {B} {C} {D} = trans lhs (sym rhs)
  where
  R : Nf (ε ▷ (A ⇒ B ⇒ C ⇒ D) ▷ C ▷ B ▷ A) D
  R = ne2nf (vs (vs (vs vz))) (sp3 v0 v1 v2)
  wkx : ∀ {X Y Z W} → wkNf {ε ▷ X ▷ Y ▷ Z} {W} ε (lookup (π {ε ▷ X} {Y} ∘s π {ε ▷ X ▷ Y} {Z}) vz)
      ≡ nvar {ε ▷ X ▷ Y ▷ Z ▷ W} {X} (vs (vs (vs vz)))
  wkx = cong (wkNf ε) (lookππ vz) ⊚ wk-nvar ε (vs (vs vz))
  lhs : sw ⟨ aw ⟨ sw ⟩ ⟩ ≡ lam (lam (lam R))
  lhs = cong (λ t → sw ⟨ t ⟩)
          (cong (aw ⟨_⟩) sw-form
           ⊚ arr-id-lam sw _
           ⊚ cong lam (sw-lam _
           ⊚ cong (λ t → lam (lam t))
               (ne-sub _ (vs (vs (vs vz))) (lookππ (vs vz))
                  (nvar-[] (vs vz) _ ∷≡ nvar-[] (vs (vs vz)) _ ⊚ lookππ vz ∷≡ nvar-[] vz _ ∷≡ refl))))
      ⊚ sw-lam _
      ⊚ cong (λ t → lam (lam (lam t)))
          (ne-sub _ (vs (vs (vs vz))) wkx
             (nvar-[] vz _ ∷≡ nvar-[] (vs (vs vz)) _ ⊚ wk-nvar ε vz
              ∷≡ nvar-[] (vs vz) _ ⊚ wk-nvar ε (vs vz) ∷≡ refl))
  rhs : aw ⟨ sw ⟨ aw ⟩ ⟩ ≡ lam (lam (lam R))
  rhs = cong (λ t → aw ⟨ t ⟩)
          (cong (sw ⟨_⟩) aw-form
           ⊚ sw-lam _
           ⊚ cong (λ t → lam (lam (lam t)))
               (ne-sub _ (vs (vs (vs vz))) wkx
                  (nvar-[] (vs (vs vz)) _ ⊚ wk-nvar ε vz ∷≡ nvar-[] vz _
                   ∷≡ nvar-[] (vs vz) _ ⊚ wk-nvar ε (vs vz) ∷≡ refl)))
      ⊚ arr-id-lam sw _
      ⊚ cong lam (sw-lam _
      ⊚ cong (λ t → lam (lam t))
          (ne-sub _ (vs (vs (vs vz))) (lookππ (vs vz))
             (nvar-[] (vs vz) _ ∷≡ nvar-[] vz _ ∷≡ nvar-[] (vs (vs vz)) _ ⊚ lookππ vz ∷≡ refl)))

------------------------------------------------------------------------
-- Derivations are isomorphisms

invF : ∀ {A B} (φ : A ≃ B) → bw C⟦ φ ⟧ ⟨ fw C⟦ φ ⟧ ⟩ ≡ idNf
invB : ∀ {A B} (φ : A ≃ B) → fw C⟦ φ ⟧ ⟨ bw C⟦ φ ⟧ ⟩ ≡ idNf

invF idD      = idl⟨⟩ idNf
invF (symD φ) = invB φ
invF (φ ⨾ ψ)  =
  trans (assoc⟨⟩ (bw C⟦ φ ⟧) (bw C⟦ ψ ⟧) _)
  (trans (cong (bw C⟦ φ ⟧ ⟨_⟩)
           (trans (sym (assoc⟨⟩ (bw C⟦ ψ ⟧) (fw C⟦ ψ ⟧) _))
                  (trans (cong (_⟨ fw C⟦ φ ⟧ ⟩) (invF ψ)) (idl⟨⟩ _))))
         (invF φ))
invF (φ ⇒≃ ψ) =
  trans (arr-comp (fw C⟦ φ ⟧) (bw C⟦ ψ ⟧) (bw C⟦ φ ⟧) (fw C⟦ ψ ⟧))
        (trans (cong₂ arrC (invF φ) (invF ψ)) arr-id)
invF swap     = sw-sw

invB idD      = idl⟨⟩ idNf
invB (symD φ) = invF φ
invB (φ ⨾ ψ)  =
  trans (assoc⟨⟩ (fw C⟦ ψ ⟧) (fw C⟦ φ ⟧) _)
  (trans (cong (fw C⟦ ψ ⟧ ⟨_⟩)
           (trans (sym (assoc⟨⟩ (fw C⟦ φ ⟧) (bw C⟦ φ ⟧) _))
                  (trans (cong (_⟨ bw C⟦ ψ ⟧ ⟩) (invB φ)) (idl⟨⟩ _))))
         (invB ψ))
invB (φ ⇒≃ ψ) =
  trans (arr-comp (bw C⟦ φ ⟧) (fw C⟦ ψ ⟧) (fw C⟦ φ ⟧) (bw C⟦ ψ ⟧))
        (trans (cong₂ arrC (invB φ) (invB ψ)) arr-id)
invB swap     = sw-sw

derivations-sound : Derivations-sound
derivations-sound φ =
  trans (comp-ε (bw (⟦ φ ⟧ {ε})) (fw (⟦ φ ⟧ {ε}))) (trans (cong (λ p → bw p ⟨ fw p ⟩) (closed φ)) (invF φ))
  ,Σ trans (comp-ε (fw (⟦ φ ⟧ {ε})) (bw (⟦ φ ⟧ {ε}))) (trans (cong (λ p → fw p ⟨ bw p ⟩) (closed φ)) (invB φ))

------------------------------------------------------------------------
-- Soundness of the level-2 equations

soundC : ∀ {A B} {φ ψ : A ≃ B} → φ ~ ψ → C⟦ φ ⟧ ≡ C⟦ ψ ⟧
soundC ~refl         = refl
soundC (~sym e)      = sym (soundC e)
soundC (~trans e e') = trans (soundC e) (soundC e')
soundC (~⨾ e e')     = cong₂ cP (soundC e) (soundC e')
soundC (~symD e)     = cong op (soundC e)
soundC (~⇒ e e')     = cong₂ aP (soundC e) (soundC e')
soundC (assoc {φ = φ} {ψ} {χ}) =
  pair-≡ (sym (assoc⟨⟩ (fw C⟦ χ ⟧) (fw C⟦ ψ ⟧) (fw C⟦ φ ⟧)))
         (assoc⟨⟩ (bw C⟦ φ ⟧) (bw C⟦ ψ ⟧) (bw C⟦ χ ⟧))
soundC (idl {φ = φ}) = pair-≡ (idr⟨⟩ (fw C⟦ φ ⟧)) (idl⟨⟩ (bw C⟦ φ ⟧))
soundC (idr {φ = φ}) = pair-≡ (idl⟨⟩ (fw C⟦ φ ⟧)) (idr⟨⟩ (bw C⟦ φ ⟧))
soundC (invl {φ = φ}) = pair-≡ (invB φ) (invB φ)
soundC (invr {φ = φ}) = pair-≡ (invF φ) (invF φ)
soundC ⇒id           = pair-≡ arr-id arr-id
soundC (⇒⨾ {φ = φ} {φ'} {ψ} {ψ'}) =
  pair-≡ (sym (arr-comp (bw C⟦ φ' ⟧) (fw C⟦ ψ' ⟧) (bw C⟦ φ ⟧) (fw C⟦ ψ ⟧)))
         (sym (arr-comp (fw C⟦ φ ⟧) (bw C⟦ ψ ⟧) (fw C⟦ φ' ⟧) (bw C⟦ ψ' ⟧)))
soundC swap²         = pair-≡ sw-sw sw-sw
soundC (swap-nat {φ = φ} {ψ} {χ}) =
  pair-≡ (sw-natural (bw C⟦ ψ ⟧) (bw C⟦ φ ⟧) (fw C⟦ χ ⟧))
         (sym (sw-natural (fw C⟦ φ ⟧) (fw C⟦ ψ ⟧) (bw C⟦ χ ⟧)))
soundC (braid {A} {B} {C} {D}) =
  pair-≡ (trans (assoc⟨⟩ (sw {B} {C} {A ⇒ D}) (aw {B} {A} {C} {D}) (sw {A} {B} {C ⇒ D}))
         (trans (braid-closed {A} {B} {C} {D})
                (sym (assoc⟨⟩ (aw {C} {A} {B} {D}) (sw {A} {C} {B ⇒ D}) (aw {A} {B} {C} {D})))))
         (braid-closed {C} {B} {A} {D})

sound : ∀ {A B} {φ ψ : A ≃ B} → φ ~ ψ → to⟦ φ ⟧ {ε} ≡ to⟦ ψ ⟧ {ε}
sound {φ = φ} {ψ} e = cong fw (trans (closed φ) (trans (soundC e) (sym (closed ψ))))

------------------------------------------------------------------------
-- Faithfulness now depends only on determinacy (D).

module FaithfulD
  (determined : ∀ {A B} (h h' : HPi A B) → to⟦ dr h ⟧ {ε} ≡ to⟦ dr h' ⟧ {ε} → h ≡ h')
  where
  open Faithful sound determined public
