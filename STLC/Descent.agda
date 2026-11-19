{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Matched pairs and the descent (Definition matched, Lemma descent and
-- Corollary relevance of the note).
--
-- A matched pair consists of two one-sided equations sharing P and Q:
--
--   (P)  P ∘ ⟨ α ∘ p , Q ∘ ⟨ β ∘ p , q_X ⟩ ⟩ = q_X       over Γ₁ ⧺ X
--   (Q)  Q ∘ ⟨ β₀ ∘ p , P ∘ ⟨ α₀ ∘ p , q_Y ⟩ ⟩ = q_Y     over Γ₂ ⧺ Y
--
-- Every lemma is proved once, for a OneSided equation, and applied to
-- both sides.
------------------------------------------------------------------------
module STLC.Descent where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads
open import STLC.LamI
open import STLC.Tele
open import STLC.Iso

------------------------------------------------------------------------
-- Head-free substitutions

FreeHd : ∀ {Γ τ} → Nf Γ τ → Set
FreeHd {Γ} t = Σ Ty (λ σ → Σ (Var Γ σ) (λ w → FH w t))

HF : ∀ {Γ Δ} → Sub Γ Δ → Set
HF {Δ = Δ} ρ = ∀ {σ} (v : Var Δ σ) → FreeHd (lookup ρ v)

FH-p : ∀ {Γ} X {σ τ} {w : Var Γ σ} {t : Nf Γ τ} → FH w t → FH (injL X w) (t [ p {Γ} X ])
FH-p {Γ} X {w = w} fw =
  heads-free (p {Γ} X) fw (subst (FH (injL X w)) (sym (lookup-p X w)) (FH-nvar (injL X w)))

HF-∘p : ∀ {Γ Δ} X (ρ : Sub Γ Δ) → HF ρ → HF (ρ ∘s p {Γ} X)
HF-∘p {Γ} X ρ h v with h v
... | σ ,Σ (w ,Σ fw) =
  σ ,Σ (injL X w ,Σ subst (FH (injL X w)) (sym (lookup-∘s ρ (p {Γ} X) v)) (FH-p X fw))

HF-q : ∀ {Γ} X → HF (q {Γ} X)
HF-q {Γ} X v = _ ,Σ (injR {Γ} X v ,Σ subst (FH (injR {Γ} X v)) (sym (lookup-q X v)) (FH-nvar _))

HF-⊕ : ∀ {Γ Δ Θ} (ρ : Sub Γ Δ) (s : Sub Γ Θ) → HF ρ → HF s → HF (ρ ⊕ s)
HF-⊕ {Δ = Δ} {Θ} ρ s hρ hs v with split {Δ} Θ v
... | inL u = subst FreeHd (sym (lookup-⊕L ρ s u)) (hρ u)
... | inR y = subst FreeHd (sym (lookup-⊕R ρ s y)) (hs y)

-- the heads of the components of Q are variables of X
HeadsIn : ∀ {ΓQ X Y} → Sub (ΓQ ⧺ X) Y → Set
HeadsIn {ΓQ} {X} {Y} Q =
  ∀ {σ} (y : Var Y σ) → Σ Ty (λ σ' → Σ (Var X σ') (λ i → FH (injR {ΓQ} X i) (lookup Q y)))

------------------------------------------------------------------------
-- Matched pairs

αL : ∀ {Γ₁ ΓQ} X → Sub Γ₁ ΓQ → Sub (Γ₁ ⧺ X) (ΓQ ⧺ X)
αL {Γ₁} X β = (β ∘s p {Γ₁} X) ⊕ q {Γ₁} X

ρL : ∀ {Γ₁ ΓP ΓQ Y} X → Sub Γ₁ ΓP → Sub Γ₁ ΓQ → Sub (ΓQ ⧺ X) Y → Sub (Γ₁ ⧺ X) (ΓP ⧺ Y)
ρL {Γ₁} X α β Q = (α ∘s p {Γ₁} X) ⊕ (Q ∘s αL X β)

record OneSided (ΓP ΓQ X Y : Con) (P : Sub (ΓP ⧺ Y) X) (Q : Sub (ΓQ ⧺ X) Y) : Set where
  field
    Γ₁  : Con
    α   : Sub Γ₁ ΓP
    β   : Sub Γ₁ ΓQ
    hfα : HF α
    hfβ : HF β
    eq  : P ∘s ρL X α β Q ≡ q {Γ₁} X

record MP : Set where
  field
    ΓP ΓQ X Y : Con
    P     : Sub (ΓP ⧺ Y) X
    Q     : Sub (ΓQ ⧺ X) Y
    left  : OneSided ΓP ΓQ X Y P Q
    right : OneSided ΓQ ΓP Y X Q P

ne-inj : ∀ {Γ σ n} {x : Var Γ σ} {s s' : Sp Γ σ (ι n)} → ne (x ∙ s) ≡ ne (x ∙ s') → s ≡ s'
ne-inj refl = refl

------------------------------------------------------------------------
-- The one-sided lemmas

module OS {ΓP ΓQ X Y} {P : Sub (ΓP ⧺ Y) X} {Q : Sub (ΓQ ⧺ X) Y}
          (L : OneSided ΓP ΓQ X Y P Q) where
  open OneSided L

  ρP : Sub (Γ₁ ⧺ X) (ΓP ⧺ Y)
  ρP = ρL X α β Q

  eq-at : ∀ {σ} (i : Var X σ) → (lookup P i) [ ρP ] ≡ nvar (injR {Γ₁} X i)
  eq-at i = trans (sym (lookup-∘s P ρP i)) (trans (cong (λ s → lookup s i) eq) (lookup-q X i))

  lookup-αL : ∀ {σ} (i : Var X σ) → lookup (αL X β) (injR {ΓQ} X i) ≡ nvar (injR {Γ₁} X i)
  lookup-αL i = trans (lookup-⊕R (β ∘s p {Γ₁} X) (q {Γ₁} X) i) (lookup-q X i)

  lookup-ρP : ∀ {σ} (y : Var Y σ) → lookup ρP (injR {ΓP} Y y) ≡ (lookup Q y) [ αL X β ]
  lookup-ρP y = trans (lookup-⊕R (α ∘s p {Γ₁} X) (Q ∘s αL X β) y) (lookup-∘s Q (αL X β) y)

  -- a head of Q in X stays a head after substitution
  FH-Qα : ∀ {σ σ'} (y : Var Y σ) {i : Var X σ'} → FH (injR {ΓQ} X i) (lookup Q y)
    → FH (injR {Γ₁} X i) ((lookup Q y) [ αL X β ])
  FH-Qα y {i} fQ =
    heads-free (αL X β) fQ (subst (FH (injR {Γ₁} X i)) (sym (lookup-αL i)) (FH-nvar _))

  -- (a) the head of P_i is a variable of Y
  heads-P : HeadsIn {ΓP} {Y} {X} P
  heads-P i with head (lookup P i)
  ... | bound b h =
    ⊥-elim (FH-BH (FH-nvar (injR {Γ₁} X i)) (subst (BH b) (eq-at i) (heads-bound ρP h)))
  ... | free h fh with split {ΓP} Y h
  ...   | inR y = _ ,Σ (y ,Σ fh)
  ...   | inL u with hfα u
  ...     | _ ,Σ (w ,Σ fw) =
    ⊥-elim (injL≉injR X w i (FH-unique f5 (FH-nvar (injR {Γ₁} X i))))
    where
    f3 : FH (injL X w) (lookup ρP (injL Y u))
    f3 = subst (FH (injL X w))
               (sym (trans (lookup-⊕L (α ∘s p {Γ₁} X) (Q ∘s αL X β) u) (lookup-∘s α (p {Γ₁} X) u)))
               (FH-p X fw)
    f5 : FH (injL X w) (nvar (injR {Γ₁} X i))
    f5 = subst (FH (injL X w)) (eq-at i) (heads-free ρP fh f3)

  -- (b) every binder of P_i occurs in its body
  binder-occ : ∀ {σ} (i : Var X σ) {ρ'} (k : Var (args σ) ρ')
    → injR {Γ₁ ⧺ X} (args σ) k ∈ (unlam (lookup P i)) [ ρP ⇑ args σ ]
  binder-occ {σ} i k =
    subst (injR {Γ₁ ⧺ X} (args σ) k ∈_)
          (trans (sym (unlam-nvar (injR {Γ₁} X i)))
                 (trans (cong unlam (sym (eq-at i))) (unlam-[] (lookup P i) ρP)))
          (o-arg (ηsp-occ (Γ₁ ⧺ X) σ k))

  binders-P : ∀ {σ} (i : Var X σ) {ρ'} (k : Var (args σ) ρ')
    → injR {ΓP ⧺ Y} (args σ) k ∈ unlam (lookup P i)
  binders-P {σ} i k with nocreate (unlam (lookup P i)) (ρP ⇑ args σ) (binder-occ i k)
  ... | src v occ hit with split {ΓP ⧺ Y} (args σ) v
  ...   | inL h with ∈-wkTop (args σ) (lookup ρP h)
                     (subst (injR {Γ₁ ⧺ X} (args σ) k ∈_) (lookup-⇑L ρP (args σ) h) hit)
  ...     | x ,Σ (e ,Σ _) = ⊥-elim (injL≉injR (args σ) x k (≈-sym (≡→≈ e)))
  binders-P {σ} i k | src v occ hit | inR k'
    with injR-inj {Γ₁ ⧺ X} (args σ) k k'
           (∈-nvar _ (subst (injR {Γ₁ ⧺ X} (args σ) k ∈_) (lookup-⇑R ρP (args σ) k') hit))
  ... | ≈refl = occ

  -- (c) the heads are matched: τ ∘ σ = id
  heads-match : ∀ {σ σ' σ''} (i : Var X σ) (y : Var Y σ') (i' : Var X σ'')
    → FH (injR {ΓP} Y y) (lookup P i) → FH (injR {ΓQ} X i') (lookup Q y) → i' ≈ i
  heads-match i y i' fP fQ =
    injR-inj {Γ₁} X i' i
      (FH-unique (subst (FH _) (eq-at i)
                   (heads-free ρP fP (subst (FH _) (sym (lookup-ρP y)) (FH-Qα y fQ))))
                 (FH-nvar (injR {Γ₁} X i)))

  -- the new parameter substitutions are head-free
  hf-αL : HF (αL X β)
  hf-αL = HF-⊕ (β ∘s p {Γ₁} X) (q {Γ₁} X) (HF-∘p X β hfβ) (HF-q X)

  hf-ρP : HeadsIn Q → HF ρP
  hf-ρP hq = HF-⊕ (α ∘s p {Γ₁} X) (Q ∘s αL X β) (HF-∘p X α hfα) hQ
    where
    hQ : HF (Q ∘s αL X β)
    hQ y with hq y
    ... | _ ,Σ (i ,Σ fQ) =
      _ ,Σ (injR {Γ₁} X i ,Σ subst (FH _) (sym (lookup-∘s Q (αL X β) y)) (FH-Qα y fQ))

  -- (d) the argument families form a one-sided equation one level down
  descend : ∀ {σ σ'} (i : Var X σ) (y : Var Y σ')
    (v : Sp ((ΓP ⧺ Y) ⧺ args σ) σ' (ι (tgt σ)))
    (u : Sp ((ΓQ ⧺ X) ⧺ args σ') σ (ι (tgt σ')))
    → unlam (lookup P i) ≡ ne (injL (args σ) (injR {ΓP} Y y) ∙ v)
    → unlam (lookup Q y) ≡ ne (injL (args σ') (injR {ΓQ} X i) ∙ u)
    → HeadsIn Q
    → OneSided (ΓQ ⧺ X) (ΓP ⧺ Y) (args σ) (args σ') (spToSub u) (spToSub v)
  descend {σ} {σ'} i y v u eP eQ hq = record
    { Γ₁ = Γ₁ ⧺ X ; α = αL X β ; β = ρP ; hfα = hf-αL ; hfβ = hf-ρP hq ; eq = eq' }
    where
    W  = args σ
    Z  = args σ'
    pW = p {Γ₁ ⧺ X} W
    σZ = (αL X β ∘s pW) ⇑ Z
    x0 : Var (Γ₁ ⧺ X ⧺ W) σ
    x0 = injL W (injR {Γ₁} X i)
    T  = (lookup Q y) [ αL X β ∘s pW ]

    e-hd : lookup (ρP ⇑ W) (injL W (injR {ΓP} Y y)) ≡ T
    e-hd = trans (lookup-⇑L ρP W (injR {ΓP} Y y))
           (trans (cong (wkTop W) (lookup-ρP y))
           (trans (wkTop-[] W ((lookup Q y) [ αL X β ])) ([][] (lookup Q y) (αL X β) pW)))

    eT : unlam T ≡ ne (injL Z x0 ∙ u [ σZ ]Sp)
    eT = trans (unlam-[] (lookup Q y) (αL X β ∘s pW))
         (trans (cong (_[ σZ ]) eQ)
         (trans (cong (λ h → appNf h (u [ σZ ]Sp))
                  (trans (lookup-⇑L (αL X β ∘s pW) Z (injR {ΓQ} X i))
                  (trans (cong (wkTop Z)
                           (trans (lookup-∘s (αL X β) pW (injR {ΓQ} X i))
                           (trans (cong (_[ pW ]) (lookup-αL i))
                           (trans (nvar-[] (injR {Γ₁} X i) pW) (lookup-p W (injR {Γ₁} X i))))))
                         (wkTop-nvar Z x0))))
                (appNf-ne2nf (injL Z x0) []S (u [ σZ ]Sp))))

    ab = app-body T x0 (u [ σZ ]Sp) (v [ ρP ⇑ W ]Sp) eT
    u' = fst ab

    eN : ne (x0 ∙ u') ≡ ne (x0 ∙ ηsp (Γ₁ ⧺ X) σ)
    eN = trans (sym (fst (snd ab)))
         (trans (cong (λ h → appNf h (v [ ρP ⇑ W ]Sp)) (sym e-hd))
         (trans (cong (_[ ρP ⇑ W ]) (sym eP))
         (trans (sym (unlam-[] (lookup P i) ρP))
         (trans (cong unlam (eq-at i)) (unlam-nvar (injR {Γ₁} X i))))))

    eq' : spToSub u ∘s ρL W (αL X β) ρP (spToSub v) ≡ q {Γ₁ ⧺ X} W
    eq' = sym
      (trans (sym (spToSub-ηsp (Γ₁ ⧺ X) σ))
      (trans (cong spToSub (sym (ne-inj eN)))
      (trans (snd (snd ab))
      (trans (cong₂ (λ a b → a ∘s (idS (Γ₁ ⧺ X ⧺ W) ⊕ b))
                    (spToSub-[] u σZ) (spToSub-[] v (ρP ⇑ W)))
      (trans (∘s-assoc (spToSub u) σZ (idS (Γ₁ ⧺ X ⧺ W) ⊕ (spToSub v ∘s (ρP ⇑ W))))
             (cong (spToSub u ∘s_)
                   (trans (⇑-∘s-⊕ Z (αL X β ∘s pW) (spToSub v ∘s (ρP ⇑ W)))
                          (cong (λ s → (αL X β ∘s pW) ⊕ (spToSub v ∘s s)) (⇑-pq ρP W)))))))))

------------------------------------------------------------------------
-- Well-founded descent: pairs of types, stepping to pairs of arguments

data Acc2 : Ty → Ty → Set where
  acc2 : ∀ {τ τ'} → (∀ {σ σ'} → Arg τ σ → Arg τ' σ' → Acc2 σ σ') → Acc2 τ τ'

acc2-inv : ∀ {τ τ' σ σ'} → Acc2 τ τ' → Arg τ σ → Arg τ' σ' → Acc2 σ σ'
acc2-inv (acc2 f) = f

acc2-all : ∀ τ τ' → Acc2 τ τ'
acc2-all (ι n)   τ' = acc2 λ ()
acc2-all (A ⇒ B) τ' = acc2 λ { az b → acc2-all A _ ; (as a) b → acc2-inv (acc2-all B τ') a b }

-- the pair one level down, at matched heads i and y
down : (M : MP) → ∀ {σ σ'} (i : Var (MP.X M) σ) (y : Var (MP.Y M) σ')
  → FH (injR {MP.ΓP M} (MP.Y M) y) (lookup (MP.P M) i)
  → FH (injR {MP.ΓQ M} (MP.X M) i) (lookup (MP.Q M) y) → MP
down M {σ} {σ'} i y fP fQ = record
  { ΓP = ΓQ ⧺ X ; ΓQ = ΓP ⧺ Y ; X = args σ ; Y = args σ'
  ; P = spToSub (fst (FH-unlam fQ)) ; Q = spToSub (fst (FH-unlam fP))
  ; left  = OS.descend left i y (fst (FH-unlam fP)) (fst (FH-unlam fQ))
                       (snd (FH-unlam fP)) (snd (FH-unlam fQ)) (OS.heads-P right)
  ; right = OS.descend right y i (fst (FH-unlam fQ)) (fst (FH-unlam fP))
                       (snd (FH-unlam fQ)) (snd (FH-unlam fP)) (OS.heads-P left) }
  where open MP M

------------------------------------------------------------------------
-- Corollary (relevance)

rel : (M : MP) → ∀ {σ σ'} (i : Var (MP.X M) σ) (y : Var (MP.Y M) σ')
  (fP : FH (injR {MP.ΓP M} (MP.Y M) y) (lookup (MP.P M) i))
  (fQ : FH (injR {MP.ΓQ M} (MP.X M) i) (lookup (MP.Q M) y))
  → Acc2 σ σ' → LI (lookup (MP.P M) i) × LI (lookup (MP.Q M) y)
rel M {σ} {σ'} i y fP fQ (acc2 a) = LI-P ,Σ LI-Q
  where
  open MP M
  M' = down M i y fP fQ

  hv : ∀ {ρ} (l : Var (args σ') ρ) → LI (lookup (MP.Q M') l)
  hv l with OS.heads-P (MP.right M') l
  ... | _ ,Σ (k ,Σ fk) with OS.heads-P (MP.left M') k
  ...   | _ ,Σ (l' ,Σ fl) with OS.heads-match (MP.right M') l k l' fk fl
  ...     | ≈refl = snd (rel M' k l fl fk (a (argPos σ k) (argPos σ' l)))

  hu : ∀ {ρ} (k : Var (args σ) ρ) → LI (lookup (MP.P M') k)
  hu k with OS.heads-P (MP.left M') k
  ... | _ ,Σ (l ,Σ fl) with OS.heads-P (MP.right M') l
  ...   | _ ,Σ (k' ,Σ fk) with OS.heads-match (MP.left M') k l k' fl fk
  ...     | ≈refl = fst (rel M' k l fl fk (a (argPos σ k) (argPos σ' l)))

  LI-P : LI (lookup P i)
  LI-P = LI-unlam (lookup P i) (OS.binders-P left i)
           (subst LI (sym (snd (FH-unlam fP))) (li-ne (LIs-spToSub (fst (FH-unlam fP)) hv)))

  LI-Q : LI (lookup Q y)
  LI-Q = LI-unlam (lookup Q y) (OS.binders-P right y)
           (subst LI (sym (snd (FH-unlam fQ))) (li-ne (LIs-spToSub (fst (FH-unlam fQ)) hu)))

-- the initial pair of an isomorphism
initial : ∀ {A B} → A ≅ B → MP
initial {A} {B} iso = record
  { ΓP = ε ; ΓQ = ε ; X = ε ▷ B ; Y = ε ▷ A ; P = εs ,s f ; Q = εs ,s g
  ; left  = record { Γ₁ = ε ; α = εs ; β = εs ; hfα = λ () ; hfβ = λ () ; eq = cong (εs ,s_) eL }
  ; right = record { Γ₁ = ε ; α = εs ; β = εs ; hfα = λ () ; hfβ = λ () ; eq = cong (εs ,s_) eR } }
  where
  f = fw (pair iso)
  g = bw (pair iso)
  eL : f [ εs ,s g [ εs ,s nvar vz ] ] ≡ nvar vz
  eL = trans (cong (λ t → f [ εs ,s t ]) ([]-id g)) (trans (sym (comp-[] f g)) (snd (isIso iso)))
  eR : g [ εs ,s f [ εs ,s nvar vz ] ] ≡ nvar vz
  eR = trans (cong (λ t → g [ εs ,s t ]) ([]-id f)) (trans (sym (comp-[] g f)) (fst (isIso iso)))

relevance : ∀ {A B} (iso : A ≅ B) → LI (fw (pair iso)) × LI (bw (pair iso))
relevance {A} {B} iso with OS.heads-P (MP.left (initial iso)) vz
                         | OS.heads-P (MP.right (initial iso)) vz
... | _ ,Σ (vz ,Σ fP) | _ ,Σ (vz ,Σ fQ) = rel (initial iso) vz vz fP fQ (acc2-all B A)
... | _ ,Σ (vs () ,Σ _) | _
... | _ | _ ,Σ (vs () ,Σ _)
