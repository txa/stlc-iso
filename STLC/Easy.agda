{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Proposition (easy direction): every hereditary permutation is an
-- isomorphism.  The inverse of  λ ys. a (t'_i [y_τi])  is
-- λ xs. b (g_i [x_i])  placed at position τ i, with g_i the inverse of
-- t'_i.
------------------------------------------------------------------------
module STLC.Easy where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads
open import STLC.LamI
open import STLC.Tele
open import STLC.Iso
open import STLC.Char

------------------------------------------------------------------------
-- Substitutions, spines and bodies

sub-ext : ∀ {Γ Δ} (σ σ' : Sub Γ Δ) → (∀ {τ} (x : Var Δ τ) → lookup σ x ≡ lookup σ' x) → σ ≡ σ'
sub-ext εs       εs         h = refl
sub-ext (σ ,s u) (σ' ,s u') h = cong₂ _,s_ (sub-ext σ σ' (λ x → h (vs x))) (h vz)

tabulate : ∀ {Γ Δ} → (∀ {τ} → Var Δ τ → Nf Γ τ) → Sub Γ Δ
tabulate {Δ = ε}     F = εs
tabulate {Δ = Δ ▷ A} F = tabulate (λ x → F (vs x)) ,s F vz

lookup-tab : ∀ {Γ Δ τ} (F : ∀ {τ} → Var Δ τ → Nf Γ τ) (x : Var Δ τ) → lookup (tabulate F) x ≡ F x
lookup-tab F vz     = refl
lookup-tab F (vs x) = lookup-tab (λ y → F (vs y)) x

lamsT : ∀ {Γ} τ → Nf (Γ ⧺ args τ) (ι (tgt τ)) → Nf Γ τ
lamsT (ι n)   t = t
lamsT {Γ} (A ⇒ B) t = lam (lamsT {Γ ▷ A} B t)

lamsT-unlam : ∀ {Γ τ} (t : Nf Γ τ) → lamsT {Γ} τ (unlam t) ≡ t
lamsT-unlam {τ = ι n}   t       = refl
lamsT-unlam {τ = A ⇒ B} (lam t) = cong lam (lamsT-unlam t)

unlam-lamsT : ∀ {Γ} τ (b : Nf (Γ ⧺ args τ) (ι (tgt τ))) → unlam (lamsT {Γ} τ b) ≡ b
unlam-lamsT (ι n)   b = refl
unlam-lamsT {Γ} (A ⇒ B) b = unlam-lamsT {Γ ▷ A} B b

unlam-inj : ∀ {Γ τ} {t t' : Nf Γ τ} → unlam t ≡ unlam t' → t ≡ t'
unlam-inj {Γ} {τ} {t} {t'} e =
  trans (sym (lamsT-unlam t)) (trans (cong (lamsT {Γ} τ) e) (lamsT-unlam t'))

subToSp : ∀ {Γ} σ → Sub Γ (args σ) → Sp Γ σ (ι (tgt σ))
subToSp (ι n)   s = []S
subToSp (A ⇒ B) s =
  lookup s (injL {ε ▷ A} (args B) vz) ∷S subToSp B (tabulate (λ v → lookup s (injR {ε ▷ A} (args B) v)))

spToSub-subToSp : ∀ {Γ} σ (s : Sub Γ (args σ)) → spToSub (subToSp σ s) ≡ s
spToSub-subToSp (ι n) εs = refl
spToSub-subToSp {Γ} (A ⇒ B) s =
  trans (cong ((εs ,s lookup s (injL {ε ▷ A} (args B) vz)) ⊕_)
              (spToSub-subToSp B (tabulate (λ v → lookup s (injR {ε ▷ A} (args B) v)))))
        (sub-ext _ s pt)
  where
  pt : ∀ {τ} (v : Var (args (A ⇒ B)) τ)
     → lookup ((εs ,s lookup s (injL {ε ▷ A} (args B) vz))
                ⊕ tabulate (λ v → lookup s (injR {ε ▷ A} (args B) v))) v ≡ lookup s v
  pt v with split {ε ▷ A} (args B) v
  ... | inL vz = lookup-⊕L (εs ,s lookup s (injL {ε ▷ A} (args B) vz)) T vz
    where T = tabulate (λ v → lookup s (injR {ε ▷ A} (args B) v))
  ... | inR k  = trans (lookup-⊕R (εs ,s lookup s (injL {ε ▷ A} (args B) vz)) T k)
                       (lookup-tab (λ v → lookup s (injR {ε ▷ A} (args B) v)) k)
    where T = tabulate (λ v → lookup s (injR {ε ▷ A} (args B) v))

spToSub-inj : ∀ {Γ σ m} (s s' : Sp Γ σ (ι m)) → spToSub s ≡ spToSub s' → s ≡ s'
spToSub-inj []S []S e = refl
spToSub-inj (_∷S_ {A} {B} t ts) (t' ∷S ts') e = cong₂ _∷S_ e₁ (spToSub-inj ts ts' e₂)
  where
  e₁ = trans (sym (lookup-⊕L (εs ,s t) (spToSub ts) vz))
       (trans (cong (λ s → lookup s (injL {ε ▷ A} (args B) vz)) e)
              (lookup-⊕L (εs ,s t') (spToSub ts') vz))
  e₂ = sub-ext (spToSub ts) (spToSub ts') (λ k →
         trans (sym (lookup-⊕R (εs ,s t) (spToSub ts) k))
         (trans (cong (λ s → lookup s (injR {ε ▷ A} (args B) k)) e)
                (lookup-⊕R (εs ,s t') (spToSub ts') k)))

sp-tgt : ∀ {Γ σ m} → Sp Γ σ (ι m) → tgt σ ≡ m
sp-tgt []S       = refl
sp-tgt (t ∷S ts) = sp-tgt ts

spToSub-subst : ∀ {Γ σ m m'} (e : m ≡ m') (sp : Sp Γ σ (ι m))
  → spToSub (subst (λ k → Sp Γ σ (ι k)) e sp) ≡ spToSub sp
spToSub-subst refl sp = refl

-- a closed term with the input as head, weakened by W
unlam-wkTop : ∀ {A B} W (F : Nf (ε ▷ A) B) (spF : Sp ((ε ▷ A) ⧺ args B) A (ι (tgt B)))
  → unlam F ≡ ne (injL (args B) vz ∙ spF)
  → unlam (wkTop W F) ≡ ne (injL (args B) (injL W vz) ∙ spF [ p {ε ▷ A} W ⇑ args B ]Sp)
unlam-wkTop {A} {B} W F spF e =
  trans (cong unlam (wkTop-[] W F))
  (trans (unlam-[] F (p {ε ▷ A} W))
  (trans (cong (_[ p {ε ▷ A} W ⇑ args B ]) e)
  (trans (cong (λ h → appNf h (spF [ p {ε ▷ A} W ⇑ args B ]Sp))
           (trans (lookup-⇑L (p {ε ▷ A} W) (args B) vz)
           (trans (cong (wkTop (args B)) (lookup-p W vz)) (wkTop-nvar (args B) (injL W vz)))))
         (appNf-ne2nf (injL (args B) (injL W vz)) []S (spF [ p {ε ▷ A} W ⇑ args B ]Sp)))))

------------------------------------------------------------------------
-- The composite of two terms with matched arguments is the identity

compId : ∀ {A B} (F : Nf (ε ▷ A) B) (G : Nf (ε ▷ B) A)
  (spF : Sp ((ε ▷ A) ⧺ args B) A (ι (tgt B))) (spG : Sp ((ε ▷ B) ⧺ args A) B (ι (tgt A)))
  → unlam F ≡ ne (injL (args B) vz ∙ spF) → unlam G ≡ ne (injL (args A) vz ∙ spG)
  → (τ : ∀ {σ} → Var (args A) σ → Σ Ty (Var (args B)))
  → (F' : ∀ {σ} (i : Var (args A) σ) → Nf (ε ▷ fst (τ i)) σ)
  → (K  : ∀ {σ} (i : Var (args A) σ) → Nf (ε ▷ σ) (fst (τ i)))
  → (∀ {σ} (i : Var (args A) σ)
     → lookup (spToSub spF) i ≡ F' i [ εs ,s nvar (injR {ε ▷ A} (args B) (snd (τ i))) ])
  → (∀ {σ} (i : Var (args A) σ)
     → lookup (spToSub spG) (snd (τ i)) ≡ K i [ εs ,s nvar (injR {ε ▷ B} (args A) i) ])
  → (∀ {σ} (i : Var (args A) σ) → F' i [ εs ,s K i ] ≡ nvar vz)
  → G ∘ F ≡ idNf
compId {A} {B} F G spF spG eF eG τ F' K argF argG inv =
  unlam-inj (trans E1 (trans (cong (λ s → ne (x0 ∙ s)) E2) (sym (unlam-nvar vz))))
  where
  W   = args A
  ΓA  = (ε ▷ A) ⧺ W
  σS  = (εs ,s F) ⇑ W
  pW  = p {ε ▷ A} W
  x0  = injL W (vz {ε} {A})
  spF' = spF [ pW ⇑ args B ]Sp
  S   = spToSub (spG [ σS ]Sp)
  ab  = app-body (wkTop W F) x0 spF' (spG [ σS ]Sp) (unlam-wkTop W F spF eF)
  u'  = fst ab

  E1 : unlam (G ∘ F) ≡ ne (x0 ∙ u')
  E1 = trans (cong unlam (comp-[] G F))
       (trans (unlam-[] G (εs ,s F))
       (trans (cong (_[ σS ]) eG)
       (trans (cong (λ h → appNf h (spG [ σS ]Sp)) (lookup-⇑L (εs ,s F) W vz))
              (fst (snd ab)))))

  comp : ∀ {σ} (i : Var W σ) → lookup (spToSub u') i ≡ lookup (spToSub (ηsp (ε ▷ A) A)) i
  comp {σ} i =
    trans (cong (λ s → lookup s i) (snd (snd ab)))
    (trans (lookup-∘s (spToSub spF') (idS ΓA ⊕ S) i)
    (trans (cong (λ s → (lookup s i) [ idS ΓA ⊕ S ]) (spToSub-[] spF (pW ⇑ args B)))
    (trans (cong (_[ idS ΓA ⊕ S ]) (lookup-∘s (spToSub spF) (pW ⇑ args B) i))
    (trans (cong (λ t → t [ pW ⇑ args B ] [ idS ΓA ⊕ S ]) (argF i))
    (trans (cong (_[ idS ΓA ⊕ S ]) ([][] (F' i) (εs ,s nvar yj) (pW ⇑ args B)))
    (trans ([][] (F' i) (εs ,s (nvar yj) [ pW ⇑ args B ]) (idS ΓA ⊕ S))
    (trans (cong (λ u → F' i [ εs ,s u ]) inner)
    (trans (sym ([][] (F' i) (εs ,s K i) (εs ,s nvar xi)))
    (trans (cong (_[ εs ,s nvar xi ]) (inv i))
    (trans (nvar-[] vz (εs ,s nvar xi))
    (trans (sym (lookup-q W i))
    (cong (λ s → lookup s i) (sym (spToSub-ηsp (ε ▷ A) A))))))))))))))
    where
    j  = snd (τ i)
    yj = injR {ε ▷ A} (args B) j
    xi = injR {ε ▷ A} W i
    inner : ((nvar yj) [ pW ⇑ args B ]) [ idS ΓA ⊕ S ] ≡ K i [ εs ,s nvar xi ]
    inner =
      trans (cong (_[ idS ΓA ⊕ S ]) (trans (nvar-[] yj (pW ⇑ args B)) (lookup-⇑R pW (args B) j)))
      (trans (nvar-[] (injR {ΓA} (args B) j) (idS ΓA ⊕ S))
      (trans (lookup-⊕R (idS ΓA) S j)
      (trans (cong (λ s → lookup s j) (spToSub-[] spG σS))
      (trans (lookup-∘s (spToSub spG) σS j)
      (trans (cong (_[ σS ]) (argG i))
      (trans ([][] (K i) (εs ,s nvar (injR {ε ▷ B} W i)) σS)
             (cong (λ u → K i [ εs ,s u ])
                   (trans (nvar-[] (injR {ε ▷ B} W i) σS) (lookup-⇑R (εs ,s F) W i)))))))))

  E2 : u' ≡ ηsp (ε ▷ A) A
  E2 = spToSub-inj u' (ηsp (ε ▷ A) A) (sub-ext _ _ comp)

------------------------------------------------------------------------
-- Retyping along a matched position

module Retype {A B} (τ : ∀ {σ} → Var (args A) σ → Σ Ty (Var (args B))) where

  ret : (P : Ty → Set) → ∀ {σ σ'} (i : Var (args A) σ) (j : Var (args B) σ')
      → snd (τ i) ≈ j → P (fst (τ i)) → P σ'
  ret P i _ ≈refl x = x

  ret-arg : ∀ {σ σ'} (i : Var (args A) σ) (j : Var (args B) σ') (e : snd (τ i) ≈ j)
    {Γ'} (y : ∀ {ρ} → Var (args B) ρ → Var Γ' ρ) (u : Nf Γ' σ) (t : Nf (ε ▷ fst (τ i)) σ)
    → u ≡ t [ εs ,s nvar (y (snd (τ i))) ]
    → u ≡ (ret (λ ρ → Nf (ε ▷ ρ) σ) i j e t) [ εs ,s nvar (y j) ]
  ret-arg i _ ≈refl y u t eq = eq

  ret-inv : ∀ {σ σ'} (i : Var (args A) σ) (j : Var (args B) σ') (e : snd (τ i) ≈ j)
    (g : Nf (ε ▷ σ) (fst (τ i))) (t : Nf (ε ▷ fst (τ i)) σ)
    → g [ εs ,s t ] ≡ nvar vz
    → (ret (λ ρ → Nf (ε ▷ σ) ρ) i j e g) [ εs ,s ret (λ ρ → Nf (ε ▷ ρ) σ) i j e t ] ≡ nvar vz
  ret-inv i _ ≈refl g t eq = eq

  ret-HP : ∀ {σ σ'} (i : Var (args A) σ) (j : Var (args B) σ') (e : snd (τ i) ≈ j)
    (g : Nf (ε ▷ σ) (fst (τ i))) → IsHP g → IsHP (ret (λ ρ → Nf (ε ▷ σ) ρ) i j e g)
  ret-HP i _ ≈refl g h = h

  at-τ : (g : ∀ {σ} (i : Var (args A) σ) → Nf (ε ▷ σ) (fst (τ i)))
    → ∀ {Γ'} (x : ∀ {ρ} → Var (args A) ρ → Var Γ' ρ)
    → ∀ {σ σ'} (i' : Var (args A) σ') (i : Var (args A) σ) (e : snd (τ i') ≈ snd (τ i)) → i' ≈ i
    → (ret (λ ρ → Nf (ε ▷ σ') ρ) i' (snd (τ i)) e (g i')) [ εs ,s nvar (x i') ]
    ≡ g i [ εs ,s nvar (x i) ]
  at-τ g x i' i e ≈refl = helper e
    where
    helper : (e : snd (τ i) ≈ snd (τ i))
      → (ret (λ ρ → Nf (ε ▷ _) ρ) i (snd (τ i)) e (g i)) [ εs ,s nvar (x i) ] ≡ g i [ εs ,s nvar (x i) ]
    helper ≈refl = refl

------------------------------------------------------------------------
-- The inverse of a hereditary permutation

inverse : ∀ {A B} {f : Nf (ε ▷ A) B} → IsHP f
  → Σ (Nf (ε ▷ B) A) (λ g → IsHP g × ((g ∘ f ≡ idNf) × (f ∘ g ≡ idNf)))
inverse {A} {B} {f} (isHP τ π πτ τπ t' hps sp body arg) = g ,Σ (hpg ,Σ (gf ,Σ fg))
  where
  open Retype {A} {B} τ

  IH : ∀ {σ} (i : Var (args A) σ)
     → Σ (Nf (ε ▷ σ) (fst (τ i))) (λ g → IsHP g × ((g ∘ t' i ≡ idNf) × (t' i ∘ g ≡ idNf)))
  IH i = inverse (hps i)

  gi : ∀ {σ} (i : Var (args A) σ) → Nf (ε ▷ σ) (fst (τ i))
  gi i = fst (IH i)

  G'' : ∀ {σ} (j : Var (args B) σ) → Nf (ε ▷ fst (π j)) σ
  G'' j = ret (λ ρ → Nf (ε ▷ fst (π j)) ρ) (snd (π j)) j (τπ j) (gi (snd (π j)))

  K' : ∀ {σ} (j : Var (args B) σ) → Nf (ε ▷ σ) (fst (π j))
  K' j = ret (λ ρ → Nf (ε ▷ ρ) (fst (π j))) (snd (π j)) j (τπ j) (t' (snd (π j)))

  Sg : Sub ((ε ▷ B) ⧺ args A) (args B)
  Sg = tabulate (λ j → G'' j [ εs ,s nvar (injR {ε ▷ B} (args A) (snd (π j))) ])

  et : tgt A ≡ tgt B
  et = sp-tgt sp

  spg : Sp ((ε ▷ B) ⧺ args A) B (ι (tgt A))
  spg = subst (λ k → Sp ((ε ▷ B) ⧺ args A) B (ι k)) (sym et) (subToSp B Sg)

  e-spg : spToSub spg ≡ Sg
  e-spg = trans (spToSub-subst (sym et) (subToSp B Sg)) (spToSub-subToSp B Sg)

  g : Nf (ε ▷ B) A
  g = lamsT {ε ▷ B} A (ne (injL {ε ▷ B} (args A) vz ∙ spg))

  body-g : unlam g ≡ ne (injL {ε ▷ B} (args A) vz ∙ spg)
  body-g = unlam-lamsT {ε ▷ B} A (ne (injL {ε ▷ B} (args A) vz ∙ spg))

  arg-g : ∀ {σ} (j : Var (args B) σ)
    → lookup (spToSub spg) j ≡ G'' j [ εs ,s nvar (injR {ε ▷ B} (args A) (snd (π j))) ]
  arg-g j = trans (cong (λ s → lookup s j) e-spg)
                  (lookup-tab (λ j → G'' j [ εs ,s nvar (injR {ε ▷ B} (args A) (snd (π j))) ]) j)

  hpg : IsHP g
  hpg = isHP π τ τπ πτ G''
             (λ j → ret-HP (snd (π j)) j (τπ j) (gi (snd (π j))) (fst (snd (IH (snd (π j))))))
             spg body-g arg-g

  argG : ∀ {σ} (i : Var (args A) σ)
    → lookup (spToSub spg) (snd (τ i)) ≡ gi i [ εs ,s nvar (injR {ε ▷ B} (args A) i) ]
  argG i = trans (arg-g (snd (τ i)))
                 (at-τ gi (injR {ε ▷ B} (args A)) (snd (π (snd (τ i)))) i (τπ (snd (τ i))) (πτ i))

  gf : g ∘ f ≡ idNf
  gf = compId f g sp spg body body-g τ t' gi arg argG
         (λ i → trans (sym (comp-[] (t' i) (gi i))) (snd (snd (snd (IH i)))))

  fg : f ∘ g ≡ idNf
  fg = compId g f spg sp body-g body π G'' K' arg-g
         (λ j → ret-arg (snd (π j)) j (τπ j) (injR {ε ▷ A} (args B)) _ (t' (snd (π j))) (arg (snd (π j))))
         (λ j → ret-inv (snd (π j)) j (τπ j) (gi (snd (π j))) (t' (snd (π j)))
                  (trans (sym (comp-[] (gi (snd (π j))) (t' (snd (π j)))))
                         (fst (snd (snd (IH (snd (π j))))))))

-- Proposition (easy direction)
easy : ∀ {A B} {f : Nf (ε ▷ A) B} → IsHP f → A ≅ B
easy {f = f} h with inverse h
... | g ,Σ (_ ,Σ (gf ,Σ fg)) = record { pair = f ,P g ; isIso = gf ,Σ fg }
