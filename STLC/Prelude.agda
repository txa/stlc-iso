------------------------------------------------------------------------
-- Minimal prelude (builtins only, no standard library).
------------------------------------------------------------------------
module STLC.Prelude where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public using (Nat; zero; suc)
open import Agda.Builtin.List public

infixr 4 _,Σ_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,Σ_
  field
    fst : A
    snd : B fst
open Σ public

infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- All P xs: one P for each element of xs
infixr 5 _∷A_
data All {A : Set} (P : A → Set) : List A → Set where
  []A  : All P []
  _∷A_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

_++A_ : ∀ {A} {P : A → Set} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
[]A       ++A qs = qs
(p ∷A ps) ++A qs = p ∷A (ps ++A qs)

splitA : ∀ {A} {P : A → Set} xs {ys} → All P (xs ++ ys) → All P xs × All P ys
splitA []       ps        = []A ,Σ ps
splitA (x ∷ xs) (p ∷A ps) with splitA xs ps
... | ps₁ ,Σ ps₂ = (p ∷A ps₁) ,Σ ps₂

mapA : ∀ {A} {P Q : A → Set} → (∀ {x} → P x → Q x) → ∀ {xs} → All P xs → All Q xs
mapA f []A       = []A
mapA f (p ∷A ps) = f p ∷A mapA f ps

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B}
      → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

infixr 2 _≡⟨_⟩_
infix  3 _∎
_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : {A : Set} (x : A) → x ≡ x
x ∎ = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()
