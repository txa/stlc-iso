{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Isomorphisms, derivations (swap + congruence) and hereditary
-- permutations.
--
-- Symmetry is handled once: a map candidate is a *pair* (fw , bw) with
-- the involution  op  swapping the components.  All operations on
-- pairs commute with op definitionally, so each construction and each
-- law is written once and the dual is obtained by instantiating at op.
------------------------------------------------------------------------
module STLC.Iso where

open import STLC.Prelude
open import STLC.Syntax

------------------------------------------------------------------------
-- Pairs of maps and their involution

infixr 4 _,P_
record Pair (Γ : Con) (A B : Ty) : Set where
  constructor _,P_
  field
    fw : Nf (Γ ▷ A) B
    bw : Nf (Γ ▷ B) A
open Pair public

op : ∀ {Γ A B} → Pair Γ A B → Pair Γ B A
op p = bw p ,P fw p

op-op : ∀ {Γ A B} (p : Pair Γ A B) → op (op p) ≡ p
op-op p = refl

-- one half of the inverse laws; the other half is  Inv (op p)
Inv : ∀ {Γ A B} → Pair Γ A B → Set
Inv p = bw p ∘ fw p ≡ idNf

IsIso : ∀ {Γ A B} → Pair Γ A B → Set
IsIso p = Inv p × Inv (op p)

-- maps natural in the context (as all derivable maps are)
PPair : Ty → Ty → Set
PPair A B = ∀ {Γ} → Pair Γ A B

------------------------------------------------------------------------
-- Definable isomorphisms (closed)

infix 3 _≅_
record _≅_ (A B : Ty) : Set where
  field
    pair  : Pair ε A B
    isIso : IsIso pair
open _≅_ public

------------------------------------------------------------------------
-- Operations on pairs.  Each underlying term is written once.

idP : ∀ {A} → PPair A A
idP = idNf ,P idNf

compP : ∀ {A B C} → PPair A B → PPair B C → PPair A C
compP p q = fw q ∘ fw p ,P bw p ∘ bw q

-- λ a'. k (f (h a'))     with f = vs vz, a' = vz
arrNf : ∀ {Γ A A' B B'} → (∀ {Δ} → Nf (Δ ▷ A') A) → (∀ {Δ} → Nf (Δ ▷ B) B')
      → Nf (Γ ▷ (A ⇒ B)) (A' ⇒ B')
arrNf h k = lam (sub ε k (ne2nf (vs vz) (h ∷S []S)))

arrP : ∀ {A A' B B'} → PPair A A' → PPair B B' → PPair (A ⇒ B) (A' ⇒ B')
arrP p q = arrNf (bw p) (fw q) ,P arrNf (fw p) (bw q)

-- λ b a. f a b           with f = vs (vs vz), b = vs vz, a = vz
swapNf : ∀ {Γ A B C} → Nf (Γ ▷ (A ⇒ B ⇒ C)) (B ⇒ A ⇒ C)
swapNf = lam (lam (ne2nf (vs (vs vz)) (nvar vz ∷S nvar (vs vz) ∷S []S)))

swapP : ∀ {A B C} → PPair (A ⇒ B ⇒ C) (B ⇒ A ⇒ C)
swapP = swapNf ,P swapNf

-- op commutes with every operation, definitionally
op-comp : ∀ {Γ A B C} (p : PPair A B) (q : PPair B C)
        → op (compP p q {Γ}) ≡ compP (op q) (op p)
op-comp p q = refl

op-arr : ∀ {Γ A A' B B'} (p : PPair A A') (q : PPair B B')
       → op (arrP p q {Γ}) ≡ arrP (op p) (op q)
op-arr p q = refl

------------------------------------------------------------------------
-- Derivations: the 2-level theory for → only.

infix  3 _≃_
infixr 4 _⨾_
infixr 6 _⇒≃_
data _≃_ : Ty → Ty → Set where
  idD   : ∀ {A} → A ≃ A
  symD  : ∀ {A B} → A ≃ B → B ≃ A
  _⨾_   : ∀ {A B C} → A ≃ B → B ≃ C → A ≃ C
  _⇒≃_  : ∀ {A A' B B'} → A ≃ A' → B ≃ B' → (A ⇒ B) ≃ (A' ⇒ B')
  swap  : ∀ {A B C} → (A ⇒ B ⇒ C) ≃ (B ⇒ A ⇒ C)

-- the components of a derivation: one function, no duplication
⟦_⟧ : ∀ {A B} → A ≃ B → PPair A B
⟦ idD ⟧    = idP
⟦ symD φ ⟧ = op ⟦ φ ⟧
⟦ φ ⨾ ψ ⟧  = compP ⟦ φ ⟧ ⟦ ψ ⟧
⟦ φ ⇒≃ ψ ⟧ = arrP ⟦ φ ⟧ ⟦ ψ ⟧
⟦ swap ⟧   = swapP

to⟦_⟧ : ∀ {A B} → A ≃ B → ∀ {Γ} → Nf (Γ ▷ A) B
to⟦ φ ⟧ = fw ⟦ φ ⟧

from⟦_⟧ : ∀ {A B} → A ≃ B → ∀ {Γ} → Nf (Γ ▷ B) A
from⟦ φ ⟧ = bw ⟦ φ ⟧

------------------------------------------------------------------------
-- Hereditary permutations.
--
-- HPs As Bs : a bijection between the argument lists As and Bs, with a
-- hereditary permutation for each matched pair.  `ins h hs` sends the
-- first argument A of As to position |Bs₁| of Bs; h maps the B found
-- there back to A.

data HP  : Ty → Ty → Set
data HPs : List Ty → List Ty → Set

data HP where
  hp : ∀ {As Bs n} → HPs As Bs → HP (As ⇒* n) (Bs ⇒* n)

data HPs where
  []H : HPs [] []
  ins : ∀ {A B As} Bs₁ {Bs₂} → HP B A → HPs As (Bs₁ ++ Bs₂)
      → HPs (A ∷ As) (Bs₁ ++ B ∷ Bs₂)

------------------------------------------------------------------------
-- Hereditary permutations as normal terms:
--   λ y₁ … yₙ. a (h₁ y_{π1}) … (hₙ y_{πn})

_++C_ : Con → List Ty → Con
Δ ++C []       = Δ
Δ ++C (B ∷ Bs) = (Δ ▷ B) ++C Bs

wkMany : ∀ {Δ σ} Bs → Var Δ σ → Var (Δ ++C Bs) σ
wkMany []       x = x
wkMany (B ∷ Bs) x = wkMany Bs (vs x)

-- the variables bound by Bs, in order
vars : ∀ Δ Bs → All (Var (Δ ++C Bs)) Bs
vars Δ []       = []A
vars Δ (B ∷ Bs) = wkMany Bs vz ∷A vars (Δ ▷ B) Bs

lams : ∀ {Δ n} Bs → Nf (Δ ++C Bs) (ι n) → Nf Δ (Bs ⇒* n)
lams []       t = t
lams (B ∷ Bs) t = lam (lams Bs t)

⟦_⟧H  : ∀ {A B} → HP A B → ∀ {Γ} → Nf (Γ ▷ A) B
spine : ∀ {As Bs Θ n} → HPs As Bs → All (Var Θ) Bs → Sp Θ (As ⇒* n) (ι n)

⟦ hp {As} {Bs} {n} hs ⟧H {Γ} =
  lams Bs (ne (wkMany Bs vz ∙ spine hs (vars (Γ ▷ (As ⇒* n)) Bs)))

spine []H            []A = []S
spine (ins Bs₁ h hs) env with splitA Bs₁ env
... | env₁ ,Σ (y ∷A env₂) = sub ε ⟦ h ⟧H (nvar y) ∷S spine hs (env₁ ++A env₂)

------------------------------------------------------------------------
-- From hereditary permutations to derivations: a permutation is a
-- product of adjacent swaps.

moveTo : ∀ {B n} Cs {Rest} → (B ⇒ ((Cs ++ Rest) ⇒* n)) ≃ ((Cs ++ B ∷ Rest) ⇒* n)
moveTo []       = idD
moveTo (C ∷ Cs) = swap ⨾ (idD ⇒≃ moveTo Cs)

der  : ∀ {A B} → HP A B → A ≃ B
ders : ∀ {As Bs} → HPs As Bs → ∀ {n} → (As ⇒* n) ≃ (Bs ⇒* n)

der (hp hs) = ders hs
ders []H            = idD
ders (ins Bs₁ h hs) = (symD (der h) ⇒≃ ders hs) ⨾ moveTo Bs₁

------------------------------------------------------------------------
-- The statements.

-- Characterisation: every invertible normal term is a hereditary permutation.
Characterisation : Set
Characterisation = ∀ {A B} (i : A ≅ B) → Σ (HP A B) (λ h → ⟦ h ⟧H ≡ fw (pair i))

-- Soundness of derivations: their components are isomorphisms.
-- (Stated once; IsIso includes both directions.)
Derivations-sound : Set
Derivations-sound = ∀ {A B} (φ : A ≃ B) → IsIso (⟦ φ ⟧ {ε})

-- Hereditary permutations are the components of derivations.
HP-derivable : Set
HP-derivable = ∀ {A B} (h : HP A B) → to⟦ der h ⟧ {ε} ≡ ⟦ h ⟧H
