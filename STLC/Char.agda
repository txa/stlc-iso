{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Lemma (no stray variables) and Theorem (characterisation):
-- every closed isomorphism is a hereditary permutation.
------------------------------------------------------------------------
module STLC.Char where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads
open import STLC.LamI
open import STLC.Count using (LIS; LIS-↑; LI-[]; LIs-[])
open import STLC.Tele
open import STLC.Thin
open import STLC.Iso
open import STLC.Descent
open import STLC.Linear using (module NoStray)

------------------------------------------------------------------------
-- λI substitutions

LIS-εs : ∀ {Γ} → LIS (εs {Γ})
LIS-εs ()

LIS-,s : ∀ {Γ Δ A} {ρ : Sub Γ Δ} {u : Nf Γ A} → LIS ρ → LI u → LIS (ρ ,s u)
LIS-,s lρ lu vz     = lu
LIS-,s lρ lu (vs x) = lρ x

LIS-∘s : ∀ {Γ Δ Θ} (σ : Sub Δ Θ) (ρ : Sub Γ Δ) → LIS σ → LIS ρ → LIS (σ ∘s ρ)
LIS-∘s σ ρ lσ lρ x = subst LI (sym (lookup-∘s σ ρ x)) (LI-[] (lookup σ x) ρ (lσ x) lρ)

LIS-⊕ : ∀ {Γ Δ Θ} (ρ : Sub Γ Δ) (s : Sub Γ Θ) → LIS ρ → LIS s → LIS (ρ ⊕ s)
LIS-⊕ {Δ = Δ} {Θ} ρ s lρ ls v with split {Δ} Θ v
... | inL u = subst LI (sym (lookup-⊕L ρ s u)) (lρ u)
... | inR y = subst LI (sym (lookup-⊕R ρ s y)) (ls y)

LIS-p : ∀ {Γ} X → LIS (p {Γ} X)
LIS-p X u = subst LI (sym (lookup-p X u)) (LI-nvar _)

LIS-q : ∀ {Γ} X → LIS (q {Γ} X)
LIS-q X y = subst LI (sym (lookup-q X y)) (LI-nvar _)

LIS-αL : ∀ {Γ₁ ΓQ} X (β : Sub Γ₁ ΓQ) → LIS β → LIS (αL X β)
LIS-αL {Γ₁} X β lβ = LIS-⊕ (β ∘s p {Γ₁} X) (q {Γ₁} X) (LIS-∘s β (p {Γ₁} X) lβ (LIS-p X)) (LIS-q X)

LIS-ρL : ∀ {Γ₁ ΓP ΓQ Y} X (α : Sub Γ₁ ΓP) (β : Sub Γ₁ ΓQ) (Q : Sub (ΓQ ⧺ X) Y)
  → LIS α → LIS β → LIS Q → LIS (ρL X α β Q)
LIS-ρL {Γ₁} X α β Q lα lβ lQ =
  LIS-⊕ (α ∘s p {Γ₁} X) (Q ∘s αL X β) (LIS-∘s α (p {Γ₁} X) lα (LIS-p X))
        (LIS-∘s Q (αL X β) lQ (LIS-αL X β lβ))

LIS-spToSub : ∀ {Γ σ n} {sp : Sp Γ σ (ι n)} → LIs sp → LIS (spToSub sp)
LIS-spToSub lis-nil = LIS-εs
LIS-spToSub {sp = t ∷S ts} (lis-cons l ls) =
  LIS-⊕ (εs ,s t) (spToSub ts) (LIS-,s LIS-εs l) (LIS-spToSub ls)

LI-unlam⁺ : ∀ {Γ τ} {t : Nf Γ τ} → LI t → LI (unlam t)
LI-unlam⁺ {τ = ι n}   l            = l
LI-unlam⁺ {τ = A ⇒ B} (li-lam o l) = LI-unlam⁺ l

LIs-of-ne : ∀ {Γ σ n} {x : Var Γ σ} {sp : Sp Γ σ (ι n)} → LI (ne (x ∙ sp)) → LIs sp
LIs-of-ne (li-ne ls) = ls

-- the spine of a λI term with a free head is λI
LIS-spine : ∀ {Γ σ τ} {x : Var Γ σ} {t : Nf Γ τ} (h : FH x t) → LI t
  → LIS (spToSub (fst (FH-unlam h)))
LIS-spine h l = LIS-spToSub (LIs-of-ne (subst LI (snd (FH-unlam h)) (LI-unlam⁺ l)))

------------------------------------------------------------------------
-- λI matched pairs, and the descent preserves them

record LIMP (M : MP) : Set where
  open MP M
  field
    lP  : LIS P
    lQ  : LIS Q
    lαL : LIS (OneSided.α left)
    lβL : LIS (OneSided.β left)
    lαR : LIS (OneSided.α right)
    lβR : LIS (OneSided.β right)

  lρL : LIS (OS.ρP left)
  lρL = LIS-ρL X (OneSided.α left) (OneSided.β left) Q lαL lβL lQ

  lρR : LIS (OS.ρP right)
  lρR = LIS-ρL Y (OneSided.α right) (OneSided.β right) P lαR lβR lP

LI-down : (M : MP) → LIMP M → ∀ {σ σ'} (i : Var (MP.X M) σ) (y : Var (MP.Y M) σ')
  (fP : FH (injR {MP.ΓP M} (MP.Y M) y) (lookup (MP.P M) i))
  (fQ : FH (injR {MP.ΓQ M} (MP.X M) i) (lookup (MP.Q M) y))
  → LIMP (down M i y fP fQ)
LI-down M l i y fP fQ = record
  { lP  = LIS-spine fQ (lQ y)
  ; lQ  = LIS-spine fP (lP i)
  ; lαL = LIS-αL X (OneSided.β left) lβL
  ; lβL = lρL
  ; lαR = LIS-αL Y (OneSided.β right) lβR
  ; lβR = lρR }
  where
  open MP M
  open LIMP l

flip : MP → MP
flip M = record { ΓP = ΓQ ; ΓQ = ΓP ; X = Y ; Y = X ; P = Q ; Q = P ; left = right ; right = left }
  where open MP M

flip-LI : (M : MP) → LIMP M → LIMP (flip M)
flip-LI M l = record { lP = lQ ; lQ = lP ; lαL = lαR ; lβL = lβR ; lαR = lαL ; lβR = lβL }
  where open LIMP l

------------------------------------------------------------------------
-- Lemma (no stray variables, STLC.Linear): in a λI matched pair, the
-- only variable occurring in P_i is its head.

module Stray (M : MP) where
  open MP M
  open OneSided left using (Γ₁ ; α ; β)

  stray = NoStray.stray M

  -- the first-level equation, once P_i and Q_y are strengthened
  comp-eq : ∀ {σ σ'} (i : Var X σ) (y : Var Y σ') (P' : Nf (ε ▷ σ') σ) (Q' : Nf (ε ▷ σ) σ')
    → lookup P i ≡ P' [ εs ,s nvar (injR {ΓP} Y y) ]
    → lookup Q y ≡ Q' [ εs ,s nvar (injR {ΓQ} X i) ]
    → P' [ εs ,s Q' ] ≡ nvar vz
  comp-eq i y P' Q' eP eQ = cancel x (P' [ εs ,s Q' ]) (nvar vz) E
    where
    x = injR {Γ₁} X i
    inner : (lookup Q y) [ αL X β ] ≡ Q' [ εs ,s nvar x ]
    inner = trans (cong (_[ αL X β ]) eQ)
            (trans ([][] Q' (εs ,s nvar (injR {ΓQ} X i)) (αL X β))
                   (cong (λ u → Q' [ εs ,s u ])
                         (trans (nvar-[] (injR {ΓQ} X i) (αL X β)) (OS.lookup-αL left i))))
    lhs : (lookup P i) [ OS.ρP left ] ≡ P' [ εs ,s Q' [ εs ,s nvar x ] ]
    lhs = trans (cong (_[ OS.ρP left ]) eP)
          (trans ([][] P' (εs ,s nvar (injR {ΓP} Y y)) (OS.ρP left))
                 (cong (λ u → P' [ εs ,s u ])
                       (trans (nvar-[] (injR {ΓP} Y y) (OS.ρP left))
                              (trans (OS.lookup-ρP left y) inner))))
    E : P' [ εs ,s Q' ] [ εs ,s nvar x ] ≡ (nvar vz) [ εs ,s nvar x ]
    E = trans ([][] P' (εs ,s Q') (εs ,s nvar x))
        (trans (sym lhs) (trans (OS.eq-at left i) (sym (nvar-[] vz (εs ,s nvar x)))))

------------------------------------------------------------------------
-- Hereditary permutations, as a predicate on normal forms:
--
--   f = λ ys. a (t'_1 [y_τ1]) … (t'_n [y_τn])
--
-- with τ a bijection between the argument positions of A and of B, and
-- each t'_i a hereditary permutation.

data IsHP : ∀ {A B} → Nf (ε ▷ A) B → Set where
  isHP : ∀ {A B} {f : Nf (ε ▷ A) B}
    (τ : ∀ {σ} → Var (args A) σ → Σ Ty (Var (args B)))
    (π : ∀ {σ} → Var (args B) σ → Σ Ty (Var (args A)))
    (πτ : ∀ {σ} (i : Var (args A) σ) → snd (π (snd (τ i))) ≈ i)
    (τπ : ∀ {σ} (j : Var (args B) σ) → snd (τ (snd (π j))) ≈ j)
    (t' : ∀ {σ} (i : Var (args A) σ) → Nf (ε ▷ fst (τ i)) σ)
    (hp : ∀ {σ} (i : Var (args A) σ) → IsHP (t' i))
    (sp : Sp ((ε ▷ A) ⧺ args B) A (ι (tgt B)))
    (body : unlam f ≡ ne (injL (args B) vz ∙ sp))
    (arg  : ∀ {σ} (i : Var (args A) σ)
          → lookup (spToSub sp) i ≡ t' i [ εs ,s nvar (injR {ε ▷ A} (args B) (snd (τ i))) ])
    → IsHP f

------------------------------------------------------------------------
-- Theorem (characterisation)

charPair : ∀ {A B} (iso : A ≅ B) → Acc2 A B → IsHP (fw (pair iso)) × IsHP (bw (pair iso))
char1    : ∀ {A B} (iso : A ≅ B) → Acc2 A B
  → FH vz (fw (pair iso)) → FH vz (bw (pair iso))
  → IsHP (fw (pair iso)) × IsHP (bw (pair iso))

charPair {A} {B} iso a with OS.heads-P (MP.left (initial iso)) vz
                          | OS.heads-P (MP.right (initial iso)) vz
... | _ ,Σ (vz ,Σ fP)   | _ ,Σ (vz ,Σ fQ)   = char1 iso a fP fQ
... | _ ,Σ (vs () ,Σ _) | _
... | _                 | _ ,Σ (vs () ,Σ _)

char1 {A} {B} iso (acc2 a) fP fQ = hpF ,Σ hpG
  where
  f  = fw (pair iso)
  g  = bw (pair iso)
  M0 = initial iso
  l0 : LIMP M0
  l0 = record { lP = LIS-,s LIS-εs (fst (relevance iso)) ; lQ = LIS-,s LIS-εs (snd (relevance iso))
              ; lαL = LIS-εs ; lβL = LIS-εs ; lαR = LIS-εs ; lβR = LIS-εs }
  M1 = down M0 vz vz fP fQ
  l1 = LI-down M0 l0 vz vz fP fQ

  -- t_i: the arguments of f, indexed by args A, with heads in args B
  -- s_j: the arguments of g, indexed by args B, with heads in args A
  t : ∀ {σ} → Var (args A) σ → Nf ((ε ▷ A) ⧺ args B) σ
  t i = lookup (MP.Q M1) i
  s : ∀ {σ} → Var (args B) σ → Nf ((ε ▷ B) ⧺ args A) σ
  s j = lookup (MP.P M1) j

  τP : ∀ {σ} (i : Var (args A) σ)
     → Σ Ty (λ σ' → Σ (Var (args B) σ') (λ j → FH (injR {ε ▷ A} (args B) j) (t i)))
  τP = OS.heads-P (MP.right M1)
  πP : ∀ {σ} (j : Var (args B) σ)
     → Σ Ty (λ σ' → Σ (Var (args A) σ') (λ i → FH (injR {ε ▷ B} (args A) i) (s j)))
  πP = OS.heads-P (MP.left M1)

  -- a matched pair of arguments gives an isomorphism at smaller types
  pairData : ∀ {σ σ'} (i : Var (args A) σ) (j : Var (args B) σ')
    → FH (injR {ε ▷ A} (args B) j) (t i) → FH (injR {ε ▷ B} (args A) i) (s j)
    → Σ (Nf (ε ▷ σ') σ) (λ t' → Σ (Nf (ε ▷ σ) σ') (λ s' →
        ((t i ≡ t' [ εs ,s nvar (injR {ε ▷ A} (args B) j) ]) × IsHP t')
      × ((s j ≡ s' [ εs ,s nvar (injR {ε ▷ B} (args A) i) ]) × IsHP s')))
  pairData {σ} {σ'} i j fT fS =
    t' ,Σ (s' ,Σ ((snd st ,Σ snd rec) ,Σ (snd ss ,Σ fst rec)))
    where
    st = strengthen1 (injR {ε ▷ A} (args B) j) (t i)
           (Stray.stray (flip M1) i j fT (LIMP.lQ l1 i) (LIMP.lρR l1))
    ss = strengthen1 (injR {ε ▷ B} (args A) i) (s j)
           (Stray.stray M1 j i fS (LIMP.lP l1 j) (LIMP.lρL l1))
    t' = fst st
    s' = fst ss
    iso' : σ ≅ σ'
    iso' = record
      { pair  = s' ,P t'
      ; isIso = trans (comp-[] t' s') (Stray.comp-eq (flip M1) i j t' s' (snd st) (snd ss))
             ,Σ trans (comp-[] s' t') (Stray.comp-eq M1 j i s' t' (snd ss) (snd st)) }
    rec = charPair iso' (a (argPos A i) (argPos B j))

  perF : ∀ {σ σ'} (i : Var (args A) σ) (j : Var (args B) σ')
    → FH (injR {ε ▷ A} (args B) j) (t i)
    → Σ (Nf (ε ▷ σ') σ) (λ t' → (t i ≡ t' [ εs ,s nvar (injR {ε ▷ A} (args B) j) ]) × IsHP t')
  perF i j fT with πP j
  ... | _ ,Σ (i' ,Σ fS) with OS.heads-match (MP.right M1) i j i' fT fS
  ...   | ≈refl = fst d ,Σ fst (snd (snd d))
    where d = pairData i j fT fS

  perG : ∀ {σ σ'} (j : Var (args B) σ') (i : Var (args A) σ)
    → FH (injR {ε ▷ B} (args A) i) (s j)
    → Σ (Nf (ε ▷ σ) σ') (λ s' → (s j ≡ s' [ εs ,s nvar (injR {ε ▷ B} (args A) i) ]) × IsHP s')
  perG j i fS with τP i
  ... | _ ,Σ (j' ,Σ fT) with OS.heads-match (MP.left M1) j i j' fS fT
  ...   | ≈refl = fst (snd d) ,Σ snd (snd (snd d))
    where d = pairData i j fT fS

  τ : ∀ {σ} → Var (args A) σ → Σ Ty (Var (args B))
  τ i = fst (τP i) ,Σ fst (snd (τP i))
  π : ∀ {σ} → Var (args B) σ → Σ Ty (Var (args A))
  π j = fst (πP j) ,Σ fst (snd (πP j))

  πτ : ∀ {σ} (i : Var (args A) σ) → snd (π (snd (τ i))) ≈ i
  πτ i = OS.heads-match (MP.right M1) i (fst (snd (τP i))) (fst (snd (πP (fst (snd (τP i))))))
           (snd (snd (τP i))) (snd (snd (πP (fst (snd (τP i))))))
  τπ : ∀ {σ} (j : Var (args B) σ) → snd (τ (snd (π j))) ≈ j
  τπ j = OS.heads-match (MP.left M1) j (fst (snd (πP j))) (fst (snd (τP (fst (snd (πP j))))))
           (snd (snd (πP j))) (snd (snd (τP (fst (snd (πP j))))))

  fI : ∀ {σ} (i : Var (args A) σ) → _
  fI i = perF i (fst (snd (τP i))) (snd (snd (τP i)))
  gJ : ∀ {σ} (j : Var (args B) σ) → _
  gJ j = perG j (fst (snd (πP j))) (snd (snd (πP j)))

  hpF : IsHP f
  hpF = isHP τ π πτ τπ (λ i → fst (fI i)) (λ i → snd (snd (fI i)))
             (fst (FH-unlam fP)) (snd (FH-unlam fP)) (λ i → fst (snd (fI i)))

  hpG : IsHP g
  hpG = isHP π τ τπ πτ (λ j → fst (gJ j)) (λ j → snd (snd (gJ j)))
             (fst (FH-unlam fQ)) (snd (FH-unlam fQ)) (λ j → fst (snd (gJ j)))

characterisation : ∀ {A B} (iso : A ≅ B) → IsHP (fw (pair iso))
characterisation {A} {B} iso = fst (charPair iso (acc2-all A B))
