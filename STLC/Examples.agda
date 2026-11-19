{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Sanity checks by computation (all proofs are refl).
------------------------------------------------------------------------
module STLC.Examples where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Iso

X Y Z W V : Ty
X = ι 0
Y = ι 1
Z = ι 2
W = ι 3
V = ι 4

-- swap at base types
swap₀ : (X ⇒ Y ⇒ Z) ≃ (Y ⇒ X ⇒ Z)
swap₀ = swap

t1 : from⟦ swap₀ ⟧ ∘ to⟦ swap₀ ⟧ {ε} ≡ idNf
t1 = refl

-- swap at higher types: arguments need η-expansion
swap₁ : ((X ⇒ Y) ⇒ (Z ⇒ W) ⇒ V) ≃ ((Z ⇒ W) ⇒ (X ⇒ Y) ⇒ V)
swap₁ = swap

t2 : from⟦ swap₁ ⟧ ∘ to⟦ swap₁ ⟧ {ε} ≡ idNf
t2 = refl

t3 : to⟦ swap₁ ⟧ ∘ from⟦ swap₁ ⟧ {ε} ≡ idNf
t3 = refl

-- congruence: swap in the domain, contravariantly
cong₁ : ((X ⇒ Y ⇒ Z) ⇒ W) ≃ ((Y ⇒ X ⇒ Z) ⇒ W)
cong₁ = swap ⇒≃ idD

t4 : from⟦ cong₁ ⟧ ∘ to⟦ cong₁ ⟧ {ε} ≡ idNf
t4 = refl

t5 : to⟦ cong₁ ⟧ ∘ from⟦ cong₁ ⟧ {ε} ≡ idNf
t5 = refl

-- a 3-cycle and a nested permutation, composed
cyc : (X ⇒ Y ⇒ Z ⇒ W) ≃ (Y ⇒ Z ⇒ X ⇒ W)
cyc = swap ⨾ (idD ⇒≃ swap)

nested : ((X ⇒ Y ⇒ Z) ⇒ W ⇒ V) ≃ (W ⇒ (Y ⇒ X ⇒ Z) ⇒ V)
nested = (swap ⇒≃ idD) ⨾ swap

t6 : from⟦ cyc ⟧ ∘ to⟦ cyc ⟧ {ε} ≡ idNf
t6 = refl

t7 : to⟦ nested ⟧ ∘ from⟦ nested ⟧ {ε} ≡ idNf
t7 = refl

-- the term of the 3-cycle:  λ y z x. f x y z
t8 : to⟦ cyc ⟧ {ε}
   ≡ lam (lam (lam (ne (vs (vs (vs vz)) ∙ nvar vz ∷S nvar (vs (vs vz)) ∷S nvar (vs vz) ∷S []S))))
t8 = refl

-- hereditary permutations and their derivations agree
idH : ∀ {n} → HP (ι n) (ι n)
idH {n} = hp {[]} {[]} {n} []H

-- X ⇒ Y ⇒ Z  ↦  Y ⇒ X ⇒ Z : first argument X goes to position 1
h₁ : HP (X ⇒ Y ⇒ Z) (Y ⇒ X ⇒ Z)
h₁ = hp {X ∷ Y ∷ []} {Y ∷ X ∷ []} {2} (ins (Y ∷ []) idH (ins [] idH []H))

t9 : ⟦ h₁ ⟧H {ε} ≡ to⟦ swap₀ ⟧
t9 = refl

t10 : to⟦ der h₁ ⟧ {ε} ≡ ⟦ h₁ ⟧H
t10 = refl

-- nested:  (X ⇒ Y ⇒ Z) ⇒ W ⇒ V  ↦  W ⇒ (Y ⇒ X ⇒ Z) ⇒ V
h₂ : HP ((X ⇒ Y ⇒ Z) ⇒ W ⇒ V) (W ⇒ (Y ⇒ X ⇒ Z) ⇒ V)
h₂ = hp {(X ⇒ Y ⇒ Z) ∷ W ∷ []} {W ∷ (Y ⇒ X ⇒ Z) ∷ []} {4}
        (ins (W ∷ []) h₁' (ins [] idH []H))
  where
  h₁' : HP (Y ⇒ X ⇒ Z) (X ⇒ Y ⇒ Z)
  h₁' = hp {Y ∷ X ∷ []} {X ∷ Y ∷ []} {2} (ins (X ∷ []) idH (ins [] idH []H))

t11 : to⟦ der h₂ ⟧ {ε} ≡ ⟦ h₂ ⟧H
t11 = refl

t12 : to⟦ nested ⟧ {ε} ≡ ⟦ h₂ ⟧H
t12 = refl
