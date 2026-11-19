{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Coherence, part (D): canonical derivations are determined by their
-- meaning.  With (N) (Coherence.agda) and (S) (Sound.agda) this gives
-- Theorem coh:  φ ~ ψ  iff  ⟦ φ ⟧ = ⟦ ψ ⟧.
--
-- We never write out the meaning of  dr h  as a normal form.  We only
-- compute how it acts on an argument list:
--   move_i ⟨ F ⟩  applied to  as   =  F applied to (as at i , rest of as)
--   drs hs ⟨ x sp₀ ⟩  applied to  ys  =  x sp₀ (D h₁ ⟨ y_i ⟩) …
-- The head of  D h₁ ⟨ y ⟩  is y, so distinct ys determine the insertion,
-- and cancelling the renaming ⟨ y ⟩ recovers D h₁.
------------------------------------------------------------------------
module STLC.Determined where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Tele using (sub-as)
open import STLC.Heads using (_≈_; ≈refl; FH; fh-lam; FH-unique; heads-free; FH-nvar; FH-ne2nf)
open import STLC.LamI using (≈-sym)
open import STLC.Thin using (cancel)
open import STLC.Iso
open import STLC.Coherence
open import STLC.Sound

------------------------------------------------------------------------
-- Spines and argument lists

spOf : ∀ {Δ Cs n} → All (Nf Δ) Cs → Sp Δ (Cs ⇒* n) (ι n)
spOf []A       = []S
spOf (a ∷A as) = a ∷S spOf as

appNf-++ : ∀ {Γ ρ σ τ} (t : Nf Γ ρ) (sp : Sp Γ ρ σ) (sp' : Sp Γ σ τ)
  → appNf (appNf t sp) sp' ≡ appNf t (sp ++S sp')
appNf-++ t       []S       sp' = refl
appNf-++ (lam t) (u ∷S sp) sp' = appNf-++ (sub ε t u) sp sp'

++S-assoc : ∀ {Γ ρ σ τ υ} (s₁ : Sp Γ ρ σ) (s₂ : Sp Γ σ τ) (s₃ : Sp Γ τ υ)
  → (s₁ ++S s₂) ++S s₃ ≡ s₁ ++S (s₂ ++S s₃)
++S-assoc []S       s₂ s₃ = refl
++S-assoc (t ∷S ts) s₂ s₃ = cong (t ∷S_) (++S-assoc ts s₂ s₃)

∷S-inj : ∀ {Γ σ τ ρ} {a a' : Nf Γ σ} {s s' : Sp Γ τ ρ}
  → (a ∷S s) ≡ (a' ∷S s') → (a ≡ a') × (s ≡ s')
∷S-inj refl = refl ,Σ refl

ne-sp : ∀ {Γ σ n} {x : Var Γ σ} {s s' : Sp Γ σ (ι n)} → ne (x ∙ s) ≡ ne (x ∙ s') → s ≡ s'
ne-sp refl = refl

-- the argument at an insertion position, and the others
pk : ∀ {P : Ty → Set} {B Bs Bs'} → Ins B Bs Bs' → All P Bs' → P B
pk here      (y ∷A ys) = y
pk (there i) (y ∷A ys) = pk i ys

rest : ∀ {P : Ty → Set} {B Bs Bs'} → Ins B Bs Bs' → All P Bs' → All P Bs
rest here      (y ∷A ys) = ys
rest (there i) (y ∷A ys) = y ∷A rest i ys

pk-map : ∀ {P Q : Ty → Set} (f : ∀ {x} → P x → Q x) {B Bs Bs'} (i : Ins B Bs Bs') (ys : All P Bs')
  → pk i (mapA f ys) ≡ f (pk i ys)
pk-map f here      (y ∷A ys) = refl
pk-map f (there i) (y ∷A ys) = pk-map f i ys

rest-map : ∀ {P Q : Ty → Set} (f : ∀ {x} → P x → Q x) {B Bs Bs'} (i : Ins B Bs Bs') (ys : All P Bs')
  → rest i (mapA f ys) ≡ mapA f (rest i ys)
rest-map f here      (y ∷A ys) = refl
rest-map f (there i) (y ∷A ys) = cong (f y ∷A_) (rest-map f i ys)

------------------------------------------------------------------------
-- How meanings act on arguments

β-lam : ∀ {Γ A B τ} (Y : Nf (Γ ▷ A) B) (a : Nf Γ A) (sp : Sp Γ B τ)
  → appNf (lam Y) (a ∷S sp) ≡ appNf (Y [ idS Γ ,s a ]) sp
β-lam Y a sp = cong (λ v → appNf v sp) (sub-as ε Y a)

πβ : ∀ {Γ A} (a : Nf Γ A) → π {Γ} {A} ∘s (idS Γ ,s a) ≡ idS Γ
πβ {Γ} a = trans (wk1S-∘s (idS Γ) (idS Γ) a) (∘s-idl (idS Γ))

wkβ : ∀ {Γ A τ} (F : Nf Γ τ) (a : Nf Γ A) → F [ π ] [ idS Γ ,s a ] ≡ F
wkβ F a = trans ([][] F π _) (trans (cong (F [_]) (πβ a)) ([]-id F))

arr-gen : ∀ {Γ A A' B B'} (h : Map A' A) (k : Map B B') (F : Nf Γ (A ⇒ B))
  → arrC h k ⟨ F ⟩ ≡ lam (k ⟨ appNf (F [ π ]) (h ⟨ v0 ⟩ ∷S []S) ⟩)
arr-gen {Γ} {A} {A'} {B} h k F = cong lam
  (trans (⟨⟩-[] k _ σ↑) (cong (k ⟨_⟩)
  (trans (ne2nf-[] (vs vz) (h ⟨ v0 ⟩ ∷S []S) σ↑)
         (cong₂ (λ f a → appNf f (a ∷S []S)) (wkπ F)
                (trans (⟨⟩-[] h v0 σ↑) (cong (h ⟨_⟩) (nvar-[] vz σ↑)))))))
  where
  σ↑ : Sub (Γ ▷ A') (ε ▷ (A ⇒ B) ▷ A')
  σ↑ = (εs ,s F) ↑

act-arr : ∀ {Γ A A' B B' τ} (h : Map A' A) (k : Map B B') (F : Nf Γ (A ⇒ B))
  (a : Nf Γ A') (sp : Sp Γ B' τ)
  → appNf (arrC h k ⟨ F ⟩) (a ∷S sp) ≡ appNf (k ⟨ appNf F (h ⟨ a ⟩ ∷S []S) ⟩) sp
act-arr {Γ} h k F a sp =
  trans (cong (λ t → appNf t (a ∷S sp)) (arr-gen h k F))
  (trans (β-lam (k ⟨ appNf (F [ π ]) (h ⟨ v0 ⟩ ∷S []S) ⟩) a sp)
         (cong (λ t → appNf t sp)
           (trans (⟨⟩-[] k _ τ)
             (cong (k ⟨_⟩)
               (trans (appNf-[] (F [ π ]) (h ⟨ v0 ⟩ ∷S []S) τ)
                      (cong₂ (λ f u → appNf f (u ∷S []S)) (wkβ F a)
                             (trans (⟨⟩-[] h v0 τ) (cong (h ⟨_⟩) (nvar-[] vz τ)))))))))
  where
  τ = idS Γ ,s a

act-swap : ∀ {Γ A B C τ} (F : Nf Γ (A ⇒ B ⇒ C)) (b : Nf Γ B) (a : Nf Γ A) (sp : Sp Γ C τ)
  → appNf (swapNf ⟨ F ⟩) (b ∷S a ∷S sp) ≡ appNf F (a ∷S b ∷S sp)
act-swap {Γ} {A} {B} F b a sp =
  trans (cong (λ t → appNf t (b ∷S a ∷S sp)) (sw-gen F))
  (trans (β-lam (lam Z) b (a ∷S sp))
  (trans (β Z (idS Γ ,s b) a sp)
  (trans (cong (λ t → appNf t sp)
           (trans (appNf-[] (F [ π ∘s π ]) (v0 ∷S v1 ∷S []S) τ)
                  (cong₂ (λ f s → appNf f s) Fτ
                         (nvar-[] vz τ ∷≡ nvar-[] (vs vz) τ ∷≡ refl))))
         (appNf-++ F (a ∷S b ∷S []S) sp))))
  where
  Z : Nf (Γ ▷ B ▷ A) _
  Z = appNf (F [ π ∘s π ]) (v0 ∷S v1 ∷S []S)
  τ : Sub Γ (Γ ▷ B ▷ A)
  τ = idS Γ ,s b ,s a
  Fτ : F [ π ∘s π ] [ τ ] ≡ F
  Fτ = trans ([][] F (π ∘s π) τ)
       (trans (cong (F [_]) (trans (∘s-assoc π π τ)
                (trans (cong (π ∘s_) (trans (wk1S-∘s (idS (Γ ▷ B)) (idS Γ ,s b) a)
                                            (∘s-idl (idS Γ ,s b))))
                       (πβ b))))
              ([]-id F))

act-move : ∀ {Γ B Bs Bs' n} (i : Ins B Bs Bs') (F : Nf Γ (B ⇒ (Bs ⇒* n))) (as : All (Nf Γ) Bs')
  → appNf (fw C⟦ move {n = n} i ⟧ ⟨ F ⟩) (spOf as)
  ≡ appNf F (pk i as ∷S spOf (rest i as))
act-move here      F (a ∷A as) = cong (λ t → appNf t (a ∷S spOf as)) (idl⟨⟩ F)
act-move (there i) F (a ∷A as) =
  trans (cong (λ t → appNf t (a ∷S spOf as)) (assoc⟨⟩ (arrC idNf M) swapNf F))
  (trans (act-arr idNf M (swapNf ⟨ F ⟩) a (spOf as))
  (trans (cong (λ u → appNf (M ⟨ appNf (swapNf ⟨ F ⟩) (u ∷S []S) ⟩) (spOf as)) (idl⟨⟩ a))
  (trans (act-move i (appNf (swapNf ⟨ F ⟩) (a ∷S []S)) as)
  (trans (appNf-++ (swapNf ⟨ F ⟩) (a ∷S []S) (pk i as ∷S spOf (rest i as)))
         (act-swap F a (pk i as) (spOf (rest i as)))))))
  where
  M = fw C⟦ move i ⟧

-- the spine of the meaning of a canonical derivation
spI : ∀ {Δ As Bs n} → HPsi As Bs → All (Var Δ) Bs → Sp Δ (As ⇒* n) (ι n)
spI nil           []A = []S
spI (cons i h hs) env = fw C⟦ dr h ⟧ ⟨ nvar (pk i env) ⟩ ∷S spI hs (rest i env)

act-drs : ∀ {Δ As Bs n ρ} (hs : HPsi As Bs) (x : Var Δ ρ) (sp₀ : Sp Δ ρ (As ⇒* n))
  (env : All (Var Δ) Bs)
  → appNf (fw C⟦ drs hs {n} ⟧ ⟨ ne2nf x sp₀ ⟩) (spOf (mapA nvar env))
  ≡ ne2nf x (sp₀ ++S spI hs env)
act-drs nil x sp₀ []A = trans (idl⟨⟩ (ne2nf x sp₀)) (cong (ne2nf x) (sym (++S-[] sp₀)))
act-drs (cons i h hs) x sp₀ env =
  trans (cong (λ t → appNf t (spOf (mapA nvar env))) (assoc⟨⟩ M G N))
  (trans (act-move i (G ⟨ N ⟩) (mapA nvar env))
  (trans (act-arr Dh Dhs N (pk i (mapA nvar env)) (spOf (rest i (mapA nvar env))))
  (trans (cong₂ (λ u r → appNf (Dhs ⟨ appNf N (Dh ⟨ u ⟩ ∷S []S) ⟩) (spOf r))
                (pk-map nvar i env) (rest-map nvar i env))
  (trans (cong (λ t → appNf (Dhs ⟨ t ⟩) (spOf (mapA nvar (rest i env))))
               (appNf-ne2nf x sp₀ (Dh ⟨ nvar (pk i env) ⟩ ∷S []S)))
  (trans (act-drs hs x (sp₀ ++S (Dh ⟨ nvar (pk i env) ⟩ ∷S []S)) (rest i env))
         (cong (ne2nf x) (++S-assoc sp₀ (Dh ⟨ nvar (pk i env) ⟩ ∷S []S) (spI hs (rest i env)))))))))
  where
  M   = fw C⟦ move i ⟧
  Dh  = fw C⟦ dr h ⟧
  Dhs = fw C⟦ drs hs ⟧
  G   = arrC Dh Dhs
  N   = ne2nf x sp₀

------------------------------------------------------------------------
-- The input is the head of every meaning

fhC : ∀ {A B} (φ : A ≃ B) → FH vz (fw C⟦ φ ⟧) × FH vz (bw C⟦ φ ⟧)
fhC idD      = FH-nvar vz ,Σ FH-nvar vz
fhC (symD φ) = snd (fhC φ) ,Σ fst (fhC φ)
fhC (φ ⨾ ψ)  = heads-free (εs ,s fw C⟦ φ ⟧) (fst (fhC ψ)) (fst (fhC φ))
            ,Σ heads-free (εs ,s bw C⟦ ψ ⟧) (snd (fhC φ)) (snd (fhC ψ))
fhC (φ ⇒≃ ψ) =
     fh-lam (heads-free (εs ,s ne2nf (vs vz) (bw C⟦ φ ⟧ ⟨ v0 ⟩ ∷S []S)) (fst (fhC ψ))
                        (FH-ne2nf (vs vz) (bw C⟦ φ ⟧ ⟨ v0 ⟩ ∷S []S)))
  ,Σ fh-lam (heads-free (εs ,s ne2nf (vs vz) (fw C⟦ φ ⟧ ⟨ v0 ⟩ ∷S []S)) (snd (fhC ψ))
                        (FH-ne2nf (vs vz) (fw C⟦ φ ⟧ ⟨ v0 ⟩ ∷S []S)))
fhC swap     = fh-lam (fh-lam (FH-ne2nf (vs (vs vz)) (nvar vz ∷S nvar (vs vz) ∷S []S)))
            ,Σ fh-lam (fh-lam (FH-ne2nf (vs (vs vz)) (nvar vz ∷S nvar (vs vz) ∷S []S)))

fhD : ∀ {Δ A B} (φ : A ≃ B) (y : Var Δ A) → FH y (fw C⟦ φ ⟧ ⟨ nvar y ⟩)
fhD φ y = heads-free (εs ,s nvar y) (fst (fhC φ)) (FH-nvar y)

------------------------------------------------------------------------
-- Distinct variables determine insertion positions

fresh : ∀ {Δ σ} → Var Δ σ → ∀ {Cs} → All (Var Δ) Cs → Set
fresh y []A       = ⊤
fresh y (z ∷A zs) = (y ≈ z → ⊥) × fresh y zs

distinct : ∀ {Δ Cs} → All (Var Δ) Cs → Set
distinct []A       = ⊤
distinct (z ∷A zs) = fresh z zs × distinct zs

fresh-rest : ∀ {Δ σ B Bs Bs'} {y : Var Δ σ} (i : Ins B Bs Bs') (zs : All (Var Δ) Bs')
  → fresh y zs → fresh y (rest i zs)
fresh-rest here      (z ∷A zs) (n ,Σ f) = f
fresh-rest (there i) (z ∷A zs) (n ,Σ f) = n ,Σ fresh-rest i zs f

fresh-pk : ∀ {Δ σ B Bs Bs'} {y : Var Δ σ} (i : Ins B Bs Bs') (zs : All (Var Δ) Bs')
  → fresh y zs → y ≈ pk i zs → ⊥
fresh-pk here      (z ∷A zs) (n ,Σ f) e = n e
fresh-pk (there i) (z ∷A zs) (n ,Σ f) e = fresh-pk i zs f e

distinct-rest : ∀ {Δ B Bs Bs'} (i : Ins B Bs Bs') (zs : All (Var Δ) Bs')
  → distinct zs → distinct (rest i zs)
distinct-rest here      (z ∷A zs) (f ,Σ d) = d
distinct-rest (there i) (z ∷A zs) (f ,Σ d) = fresh-rest i zs f ,Σ distinct-rest i zs d

data InsEq {B Bs Bs'} (i : Ins B Bs Bs') : ∀ {B' Bs₂} → Ins B' Bs₂ Bs' → Set where
  same : InsEq i i

pk-inj : ∀ {Δ B B' Bs Bs₂ Bs'} (i : Ins B Bs Bs') (i' : Ins B' Bs₂ Bs') (zs : All (Var Δ) Bs')
  → distinct zs → pk i zs ≈ pk i' zs → InsEq i i'
pk-inj here      here       (z ∷A zs) d         e = same
pk-inj here      (there i') (z ∷A zs) (f ,Σ d) e = ⊥-elim (fresh-pk i' zs f e)
pk-inj (there i) here       (z ∷A zs) (f ,Σ d) e = ⊥-elim (fresh-pk i zs f (≈-sym e))
pk-inj (there i) (there i') (z ∷A zs) (f ,Σ d) e with pk-inj i i' zs d e
... | same = same

wkMany-inj : ∀ {Δ σ τ} Bs (a : Var Δ σ) (b : Var Δ τ) → wkMany Bs a ≈ wkMany Bs b → a ≈ b
wkMany-inj []       a b e = e
wkMany-inj (B ∷ Bs) a b e with wkMany-inj Bs (vs a) (vs b) e
... | ≈refl = ≈refl

fresh-vars : ∀ {Δ σ} Bs (x : Var Δ σ) → fresh (wkMany Bs x) (vars Δ Bs)
fresh-vars []       x = tt
fresh-vars (B ∷ Bs) x = (λ e → vs≉vz (wkMany-inj Bs (vs x) vz e)) ,Σ fresh-vars Bs (vs x)
  where
  vs≉vz : ∀ {Γ σ τ} {y : Var Γ σ} → vs {τ = τ} y ≈ vz {Γ} {τ} → ⊥
  vs≉vz ()

distinct-vars : ∀ Δ Bs → distinct (vars Δ Bs)
distinct-vars Δ []       = tt
distinct-vars Δ (B ∷ Bs) = fresh-vars Bs vz ,Σ distinct-vars (Δ ▷ B) Bs

------------------------------------------------------------------------
-- Viewing  h : HPi (As ⇒* n) (Bs ⇒* n)  as  hpi hs

data UnHP2 {As Bs n} : HPi (As ⇒* n) (Bs ⇒* n) → Set where
  un2 : (hs : HPsi As Bs) → UnHP2 (hpi hs)

subst2 : ∀ {X Y : Set} (P : X → Y → Set) {x x' y y'} → x ≡ x' → y ≡ y' → P x y → P x' y'
subst2 P refl refl p = p

unhp2 : ∀ {As Bs n} (h : HPi (As ⇒* n) (Bs ⇒* n)) → UnHP2 h
unhp2 {As} {Bs} {n} h = go h refl refl
  where
  go : ∀ {A B} (h : HPi A B) (eA : A ≡ As ⇒* n) (eB : B ≡ Bs ⇒* n) → UnHP2 (subst2 HPi eA eB h)
  go (hpi {As'} {Bs'} {n'} hs) eA eB with ⇒*-inj As' As eA | ⇒*-inj Bs' Bs eB
  ... | refl ,Σ refl | refl ,Σ refl rewrite uip eA | uip eB = un2 hs

------------------------------------------------------------------------
-- (D)

inj   : ∀ {A B} (h h' : HPi A B) → fw C⟦ dr h ⟧ ≡ fw C⟦ dr h' ⟧ → h ≡ h'
inj-s : ∀ {Δ As Bs n} (hs hs' : HPsi As Bs) (env : All (Var Δ) Bs)
  → distinct env → spI {n = n} hs env ≡ spI hs' env → hs ≡ hs'

inj (hpi {As} {Bs} {n} hs) h' e with unhp2 h'
... | un2 hs' = cong hpi (inj-s hs hs' env (distinct-vars _ Bs) (ne-sp eq))
  where
  env = vars (ε ▷ (As ⇒* n)) Bs
  x   = wkMany Bs (vz {ε} {As ⇒* n})
  eq : ne2nf x (spI hs env) ≡ ne2nf x (spI hs' env)
  eq = trans (sym (act-drs hs x []S env))
      (trans (cong (λ G → appNf (G ⟨ ne2nf x []S ⟩) (spOf (mapA nvar env))) e)
             (act-drs hs' x []S env))

inj-s nil nil []A d e = refl
inj-s (cons i h hs) (cons i' h' hs') env d e with ∷S-inj e
... | e₁ ,Σ e₂
  with pk-inj i i' env d
         (FH-unique (fhD (dr h) (pk i env))
                    (subst (FH (pk i' env)) (sym e₁) (fhD (dr h') (pk i' env))))
...   | same with inj h h' (cancel (pk i env) _ _ e₁)
                | inj-s hs hs' (rest i env) (distinct-rest i env d) e₂
...     | refl | refl = refl

determined : ∀ {A B} (h h' : HPi A B) → to⟦ dr h ⟧ {ε} ≡ to⟦ dr h' ⟧ {ε} → h ≡ h'
determined h h' e = inj h h' (trans (sym (cong fw (closed (dr h)))) (trans e (cong fw (closed (dr h')))))

------------------------------------------------------------------------
-- Theorem coh:  two derivations are level-2 equal iff they have the same
-- meaning, and every derivation is level-2 equal to a canonical one.

open FaithfulD determined public using (faithful)

coherence : ∀ {A B} (φ ψ : A ≃ B) → (φ ~ ψ → to⟦ φ ⟧ {ε} ≡ to⟦ ψ ⟧ {ε}) × (to⟦ φ ⟧ {ε} ≡ to⟦ ψ ⟧ {ε} → φ ~ ψ)
coherence φ ψ = sound ,Σ faithful φ ψ
