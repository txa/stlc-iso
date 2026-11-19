{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Coherence, syntactic part: the level-2 equations, and every
-- derivation is level-2 equal to a canonical derivation (insertion
-- normal form).  This is the hereditary Coxeter normal form argument;
-- no hereditary substitution is involved.
------------------------------------------------------------------------
module STLC.Coherence where

open import STLC.Prelude
open import Agda.Builtin.Nat using (_+_)
open import STLC.Syntax
open import STLC.Iso

------------------------------------------------------------------------
-- Level-2 equations

infix 3 _~_
data _~_ : ∀ {A B} → A ≃ B → A ≃ B → Set where
  ~refl  : ∀ {A B} {φ : A ≃ B} → φ ~ φ
  ~sym   : ∀ {A B} {φ ψ : A ≃ B} → φ ~ ψ → ψ ~ φ
  ~trans : ∀ {A B} {φ ψ χ : A ≃ B} → φ ~ ψ → ψ ~ χ → φ ~ χ
  ~⨾     : ∀ {A B C} {φ φ' : A ≃ B} {ψ ψ' : B ≃ C} → φ ~ φ' → ψ ~ ψ' → φ ⨾ ψ ~ φ' ⨾ ψ'
  ~symD  : ∀ {A B} {φ ψ : A ≃ B} → φ ~ ψ → symD φ ~ symD ψ
  ~⇒     : ∀ {A A' B B'} {φ φ' : A ≃ A'} {ψ ψ' : B ≃ B'}
         → φ ~ φ' → ψ ~ ψ' → φ ⇒≃ ψ ~ φ' ⇒≃ ψ'
  -- groupoid
  assoc  : ∀ {A B C D} {φ : A ≃ B} {ψ : B ≃ C} {χ : C ≃ D} → (φ ⨾ ψ) ⨾ χ ~ φ ⨾ (ψ ⨾ χ)
  idl    : ∀ {A B} {φ : A ≃ B} → idD ⨾ φ ~ φ
  idr    : ∀ {A B} {φ : A ≃ B} → φ ⨾ idD ~ φ
  invl   : ∀ {A B} {φ : A ≃ B} → symD φ ⨾ φ ~ idD
  invr   : ∀ {A B} {φ : A ≃ B} → φ ⨾ symD φ ~ idD
  -- functoriality of ⇒
  ⇒id    : ∀ {A B} → idD {A} ⇒≃ idD {B} ~ idD
  ⇒⨾     : ∀ {A A' A'' B B' B''} {φ : A ≃ A'} {φ' : A' ≃ A''} {ψ : B ≃ B'} {ψ' : B' ≃ B''}
         → (φ ⨾ φ') ⇒≃ (ψ ⨾ ψ') ~ (φ ⇒≃ ψ) ⨾ (φ' ⇒≃ ψ')
  -- swap: involution, naturality, braid
  swap²    : ∀ {A B C} → swap {A} {B} {C} ⨾ swap ~ idD
  swap-nat : ∀ {A A' B B' C C'} {φ : A ≃ A'} {ψ : B ≃ B'} {χ : C ≃ C'}
           → swap ⨾ (ψ ⇒≃ (φ ⇒≃ χ)) ~ (φ ⇒≃ (ψ ⇒≃ χ)) ⨾ swap
  braid    : ∀ {A B C D}
           → swap {A} {B} {C ⇒ D} ⨾ (idD ⇒≃ swap) ⨾ swap
           ~ (idD ⇒≃ swap) ⨾ swap ⨾ (idD ⇒≃ swap)

infixr 2 _~⟨_⟩_
infix  3 _∎~
_~⟨_⟩_ : ∀ {A B} (φ : A ≃ B) {ψ χ : A ≃ B} → φ ~ ψ → ψ ~ χ → φ ~ χ
φ ~⟨ p ⟩ q = ~trans p q

_∎~ : ∀ {A B} (φ : A ≃ B) → φ ~ φ
φ ∎~ = ~refl

------------------------------------------------------------------------
-- Derived equations

-- rewriting inside composites
_⟩⨾_ : ∀ {A B C} {φ φ' : A ≃ B} (p : φ ~ φ') (ψ : B ≃ C) → φ ⨾ ψ ~ φ' ⨾ ψ
p ⟩⨾ ψ = ~⨾ p ~refl
_⨾⟨_ : ∀ {A B C} (φ : A ≃ B) {ψ ψ' : B ≃ C} (p : ψ ~ ψ') → φ ⨾ ψ ~ φ ⨾ ψ'
φ ⨾⟨ p = ~⨾ ~refl p
infixl 5 _⟩⨾_
infixr 5 _⨾⟨_

assoc⁻ : ∀ {A B C D} {φ : A ≃ B} {ψ : B ≃ C} {χ : C ≃ D} → φ ⨾ (ψ ⨾ χ) ~ (φ ⨾ ψ) ⨾ χ
assoc⁻ = ~sym assoc

-- uniqueness of inverses
inv-unique : ∀ {A B} {φ : A ≃ B} {ψ : B ≃ A} → φ ⨾ ψ ~ idD → ψ ~ symD φ
inv-unique {φ = φ} {ψ} p =
  ψ                       ~⟨ ~sym idl ⟩
  idD ⨾ ψ                 ~⟨ ~sym invl ⟩⨾ ψ ⟩
  (symD φ ⨾ φ) ⨾ ψ        ~⟨ assoc ⟩
  symD φ ⨾ (φ ⨾ ψ)        ~⟨ symD φ ⨾⟨ p ⟩
  symD φ ⨾ idD            ~⟨ idr ⟩
  symD φ ∎~

symD-symD : ∀ {A B} {φ : A ≃ B} → symD (symD φ) ~ φ
symD-symD = ~sym (inv-unique invl)

symD-id : ∀ {A} → symD (idD {A}) ~ idD
symD-id = ~sym (inv-unique idl)

symD-⨾ : ∀ {A B C} {φ : A ≃ B} {ψ : B ≃ C} → symD (φ ⨾ ψ) ~ symD ψ ⨾ symD φ
symD-⨾ {φ = φ} {ψ} = ~sym (inv-unique p)
  where
  p : (φ ⨾ ψ) ⨾ (symD ψ ⨾ symD φ) ~ idD
  p = (φ ⨾ ψ) ⨾ (symD ψ ⨾ symD φ) ~⟨ assoc ⟩
      φ ⨾ (ψ ⨾ (symD ψ ⨾ symD φ)) ~⟨ φ ⨾⟨ assoc⁻ ⟩
      φ ⨾ ((ψ ⨾ symD ψ) ⨾ symD φ) ~⟨ φ ⨾⟨ (invr ⟩⨾ symD φ) ⟩
      φ ⨾ (idD ⨾ symD φ)          ~⟨ φ ⨾⟨ idl ⟩
      φ ⨾ symD φ                  ~⟨ invr ⟩
      idD ∎~

symD-⇒ : ∀ {A A' B B'} {φ : A ≃ A'} {ψ : B ≃ B'} → symD (φ ⇒≃ ψ) ~ symD φ ⇒≃ symD ψ
symD-⇒ {φ = φ} {ψ} = ~sym (inv-unique p)
  where
  p : (φ ⇒≃ ψ) ⨾ (symD φ ⇒≃ symD ψ) ~ idD
  p = ~trans (~sym ⇒⨾) (~trans (~⇒ invr invr) ⇒id)

symD-swap : ∀ {A B C} → symD (swap {A} {B} {C}) ~ swap
symD-swap = ~sym (inv-unique swap²)

-- arrows with an identity
id⇒⨾ : ∀ {A B C D} {φ : B ≃ C} {ψ : C ≃ D} → (idD {A} ⇒≃ φ) ⨾ (idD ⇒≃ ψ) ~ idD ⇒≃ (φ ⨾ ψ)
id⇒⨾ = ~trans (~sym ⇒⨾) (~⇒ idl ~refl)

⇒⨾id : ∀ {A A' B B' B''} {φ : A ≃ A'} {ψ : B ≃ B'} {ψ' : B' ≃ B''}
     → (φ ⇒≃ ψ) ⨾ (idD ⇒≃ ψ') ~ φ ⇒≃ (ψ ⨾ ψ')
⇒⨾id = ~trans (~sym ⇒⨾) (~⇒ idr ~refl)

id⨾⇒ : ∀ {A A' B B' B''} {φ : A ≃ A'} {ψ : B ≃ B'} {ψ' : B' ≃ B''}
     → (idD ⇒≃ ψ) ⨾ (φ ⇒≃ ψ') ~ φ ⇒≃ (ψ ⨾ ψ')
id⨾⇒ = ~trans (~sym ⇒⨾) (~⇒ idl ~refl)

⇒⨾⇒ : ∀ {A A' A'' B B' B''} {φ : A ≃ A'} {φ' : A' ≃ A''} {ψ : B ≃ B'} {ψ' : B' ≃ B''}
    → (φ ⇒≃ ψ) ⨾ (φ' ⇒≃ ψ') ~ (φ ⨾ φ') ⇒≃ (ψ ⨾ ψ')
⇒⨾⇒ = ~sym ⇒⨾

------------------------------------------------------------------------
-- Insertions and moving an argument into place

data Ins (B : Ty) : List Ty → List Ty → Set where
  here  : ∀ {Bs} → Ins B Bs (B ∷ Bs)
  there : ∀ {C Bs Bs'} → Ins B Bs Bs' → Ins B (C ∷ Bs) (C ∷ Bs')

move : ∀ {B Bs Bs' n} → Ins B Bs Bs' → (B ⇒ (Bs ⇒* n)) ≃ (Bs' ⇒* n)
move here      = idD
move (there i) = swap ⨾ (idD ⇒≃ move i)

-- two insertions can be done in the other order
record SwapIns {C D Es Ds Cs} (j : Ins C Es Ds) (j₁ : Ins D Ds Cs) : Set where
  field
    {Es'} : List Ty
    j₁'   : Ins D Es Es'
    j'    : Ins C Es' Cs
    eq    : ∀ {n} → swap {C} {D} {Es ⇒* n} ⨾ (idD ⇒≃ move j) ⨾ move j₁
                  ~ (idD ⇒≃ move j₁') ⨾ move j'

swapIns : ∀ {C D Es Ds Cs} (j : Ins C Es Ds) (j₁ : Ins D Ds Cs) → SwapIns j j₁
swapIns j here = record
  { j₁' = here ; j' = there j
  ; eq  = ~trans (swap ⨾⟨ idr) (~trans (~sym idl) (~sym ⇒id ⟩⨾ _)) }
swapIns here (there j₁) = record
  { j₁' = j₁ ; j' = here
  ; eq  = ~trans (swap ⨾⟨ (⇒id ⟩⨾ _)) (~trans (swap ⨾⟨ idl)
          (~trans assoc⁻ (~trans (swap² ⟩⨾ _) (~trans idl (~sym idr))))) }
swapIns (there j) (there j₁) with swapIns j j₁
... | r = record { j₁' = there (SwapIns.j₁' r) ; j' = there (SwapIns.j' r) ; eq = eq' }
  where
  open SwapIns r
  eq' : ∀ {n} → _
  eq' {n} =
    ~trans (swap ⨾⟨ (~sym id⇒⨾ ⟩⨾ _))
    (~trans (swap ⨾⟨ assoc)
    (~trans (swap ⨾⟨ (_ ⨾⟨ assoc⁻))
    (~trans (swap ⨾⟨ (_ ⨾⟨ (~sym swap-nat ⟩⨾ _)))
    (~trans (swap ⨾⟨ (_ ⨾⟨ assoc))
    (~trans (swap ⨾⟨ assoc⁻)
    (~trans assoc⁻
    (~trans (braid ⟩⨾ _)
    (~trans assoc
    (~trans (_ ⨾⟨ assoc)
    (~trans (_ ⨾⟨ (_ ⨾⟨ (~trans (_ ⨾⟨ id⇒⨾) (~trans id⇒⨾ (~⇒ ~refl (eq {n}))))))
    (~trans (_ ⨾⟨ (_ ⨾⟨ ~sym id⇒⨾))
    (~trans (_ ⨾⟨ assoc⁻)
    (~trans (_ ⨾⟨ (swap-nat ⟩⨾ _))
    (~trans (_ ⨾⟨ assoc)
    (~trans assoc⁻
            (id⇒⨾ ⟩⨾ _))))))))))))))))

------------------------------------------------------------------------
-- Hereditary permutations in insertion form, and canonical derivations

data HPi  : Ty → Ty → Set
data HPsi : List Ty → List Ty → Set

data HPi where
  hpi : ∀ {As Bs n} → HPsi As Bs → HPi (As ⇒* n) (Bs ⇒* n)

-- the first argument A goes to position i, with h mapping it back
data HPsi where
  nil  : HPsi [] []
  cons : ∀ {A B As Bs Bs'} → Ins B Bs Bs' → HPi B A → HPsi As Bs → HPsi (A ∷ As) Bs'

dr  : ∀ {A B} → HPi A B → A ≃ B
drs : ∀ {As Bs} → HPsi As Bs → ∀ {n} → (As ⇒* n) ≃ (Bs ⇒* n)
dr (hpi hs) = drs hs
drs nil            = idD
drs (cons i h hs)  = (symD (dr h) ⇒≃ drs hs) ⨾ move i

------------------------------------------------------------------------
-- Extracting the argument at an insertion position

record Ext {B Bs₀ Bs Cs} (i : Ins B Bs₀ Bs) (ks : HPsi Bs Cs) : Set where
  field
    {C}  : Ty
    {Cs₀} : List Ty
    j    : Ins C Cs₀ Cs
    k₀   : HPi C B
    ks'  : HPsi Bs₀ Cs₀
    key  : ∀ {n} → move i ⨾ drs ks {n} ~ (symD (dr k₀) ⇒≃ drs ks') ⨾ move j

exD : ∀ {B Bs₀ Bs Cs} (i : Ins B Bs₀ Bs) (ks : HPsi Bs Cs) → Ext i ks
exD here (cons j k ks) = record { j = j ; k₀ = k ; ks' = ks ; key = idl }
exD (there i) (cons j₁ k₁ ks₁) with exD i ks₁
... | e = record { j = SwapIns.j' s ; k₀ = Ext.k₀ e ; ks' = cons (SwapIns.j₁' s) k₁ (Ext.ks' e)
                 ; key = key' }
  where
  s = swapIns (Ext.j e) j₁
  key' : ∀ {n} → _
  key' {n} =
    ~trans assoc
    (~trans (swap ⨾⟨ assoc⁻)
    (~trans (swap ⨾⟨ (id⨾⇒ ⟩⨾ _))
    (~trans (swap ⨾⟨ (~⇒ ~refl (Ext.key e {n}) ⟩⨾ _))
    (~trans (swap ⨾⟨ (~sym ⇒⨾id ⟩⨾ _))
    (~trans (swap ⨾⟨ assoc)
    (~trans assoc⁻
    (~trans (swap-nat ⟩⨾ _)
    (~trans assoc
    (~trans (_ ⨾⟨ SwapIns.eq s {n})
    (~trans assoc⁻
            (⇒⨾id ⟩⨾ _)))))))))))

------------------------------------------------------------------------
-- Composition of canonical derivations.  Composition alternates
-- between arguments of the domain and of the codomain, so we recurse on
-- a bound for the height of the types.

record ⊤ : Set where
  constructor tt

Bnd : Nat → Ty → Set
Bnd n       (ι k)   = ⊤
Bnd zero    (A ⇒ B) = ⊥
Bnd (suc n) (A ⇒ B) = Bnd n A × Bnd (suc n) B

bndL : ∀ n As m → Bnd (suc n) (As ⇒* m) → All (Bnd n) As
bndL n []       m b         = []A
bndL n (A ∷ As) m (a ,Σ b) = a ∷A bndL n As m b

ins-bnd : ∀ {P : Ty → Set} {C Cs₀ Cs} → Ins C Cs₀ Cs → All P Cs → P C × All P Cs₀
ins-bnd here      (p ∷A ps) = p ,Σ ps
ins-bnd (there i) (p ∷A ps) with ins-bnd i ps
... | q ,Σ qs = q ,Σ (p ∷A qs)

mono : ∀ n τ → Bnd n τ → Bnd (suc n) τ
mono n       (ι k)   b         = tt
mono zero    (A ⇒ B) ()
mono (suc n) (A ⇒ B) (a ,Σ b) = mono n A a ,Σ mono (suc n) B b

plusL : ∀ m {n} τ → Bnd n τ → Bnd (m + n) τ
plusL zero    τ b = b
plusL (suc m) τ b = mono (m + _) τ (plusL m τ b)

plusR : ∀ n m τ → Bnd n τ → Bnd (n + m) τ
plusR n       m (ι k)   b         = tt
plusR zero    m (A ⇒ B) ()
plusR (suc n) m (A ⇒ B) (a ,Σ b) = plusR n m A a ,Σ plusR (suc n) m B b

ht : Ty → Nat
ht (ι k)   = zero
ht (A ⇒ B) = suc (ht A + ht B)

bnd-ht : ∀ τ → Bnd (ht τ) τ
bnd-ht (ι k)   = tt
bnd-ht (A ⇒ B) = plusR (ht A) (ht B) A (bnd-ht A) ,Σ plusL (suc (ht A)) B (bnd-ht B)

-- inverting hpi at a type of the form Bs ⇒* m
⇒-inj : ∀ {A B X Y} → A ⇒ X ≡ B ⇒ Y → (A ≡ B) × (X ≡ Y)
⇒-inj refl = refl ,Σ refl

⇒*-inj : ∀ As Bs {n m} → As ⇒* n ≡ Bs ⇒* m → (As ≡ Bs) × (n ≡ m)
⇒*-inj []       []       refl = refl ,Σ refl
⇒*-inj []       (B ∷ Bs) ()
⇒*-inj (A ∷ As) []       ()
⇒*-inj (A ∷ As) (B ∷ Bs) e with ⇒-inj e
... | refl ,Σ e' with ⇒*-inj As Bs e'
...   | refl ,Σ refl = refl ,Σ refl

uip : ∀ {X : Set} {x : X} (e : x ≡ x) → e ≡ refl
uip refl = refl

data UnHP {Bs m} : ∀ {C} → HPi (Bs ⇒* m) C → Set where
  un : ∀ {Cs} (ks : HPsi Bs Cs) → UnHP (hpi {n = m} ks)

unhp : ∀ {Bs m C} (k : HPi (Bs ⇒* m) C) → UnHP k
unhp {Bs} {m} k = go k Bs m refl
  where
  go : ∀ {B C} (k : HPi B C) Bs m (e : B ≡ Bs ⇒* m) → UnHP (subst (λ X → HPi X C) e k)
  go (hpi {As} {Cs} {n} ks) Bs m e with ⇒*-inj As Bs e
  ... | refl ,Σ refl rewrite uip e = un ks

Comp : ∀ {A B C} → HPi A B → HPi B C → Set
Comp {A} {C = C} h k = Σ (HPi A C) (λ m → dr h ⨾ dr k ~ dr m)

composeN : ∀ n {A B C} → Bnd n A → Bnd n B → Bnd n C → (h : HPi A B) (k : HPi B C) → Comp h k
composeS : ∀ n {As Bs Cs} → All (Bnd n) As → All (Bnd n) Bs → All (Bnd n) Cs
  → (hs : HPsi As Bs) (ks : HPsi Bs Cs)
  → Σ (HPsi As Cs) (λ ms → ∀ {m} → drs hs {m} ⨾ drs ks ~ drs ms)

composeN zero bA bB bC (hpi nil) k with unhp k
... | un nil = hpi nil ,Σ idl
composeN zero bA bB bC (hpi (cons i h hs)) k = ⊥-elim bA
composeN (suc n) bA bB bC (hpi {As} {Bs} {m} hs) k with unhp k
... | un {Cs} ks with composeS n (bndL n As m bA) (bndL n Bs m bB) (bndL n Cs m bC) hs ks
...   | ms ,Σ p = hpi ms ,Σ p

composeS n bAs bBs bCs nil nil = nil ,Σ idl
composeS n (bA ∷A bAs) bBs bCs (cons i h₀ hs') ks =
  cons (Ext.j e) (fst m₀) (fst ms') ,Σ
  ~trans assoc
  (~trans (_ ⨾⟨ Ext.key e)
  (~trans assoc⁻
  (~trans (⇒⨾⇒ ⟩⨾ _)
          (~⇒ (~trans (~sym symD-⨾) (~symD (snd m₀))) (snd ms') ⟩⨾ _))))
  where
  e   = exD i ks
  bB' = ins-bnd i bBs
  bC' = ins-bnd (Ext.j e) bCs
  m₀  = composeN n (fst bC') (fst bB') bA (Ext.k₀ e) h₀
  ms' = composeS n bAs (snd bB') (snd bC') hs' (Ext.ks' e)

compose : ∀ {A B C} (h : HPi A B) (k : HPi B C) → Comp h k
compose {A} {B} {C} h k = composeN (ht A + (ht B + ht C)) bA bB bC h k
  where
  bA = plusR (ht A) (ht B + ht C) A (bnd-ht A)
  bB = plusL (ht A) B (plusR (ht B) (ht C) B (bnd-ht B))
  bC = plusL (ht A) C (plusL (ht B) C (bnd-ht C))

------------------------------------------------------------------------
-- Identity, congruence and swap

arrHP : ∀ {A A' B B'} → HPi A' A → HPi B B' → HPi (A ⇒ B) (A' ⇒ B')
arrHP h (hpi hs) = hpi (cons here h hs)

dr-arr : ∀ {A A' B B'} (h : HPi A' A) (k : HPi B B') → dr (arrHP h k) ~ symD (dr h) ⇒≃ dr k
dr-arr h (hpi hs) = idr

idHP : ∀ A → HPi A A
idHP (ι n)   = hpi {[]} {[]} {n} nil
idHP (A ⇒ B) = arrHP (idHP A) (idHP B)

dr-id : ∀ A → dr (idHP A) ~ idD
dr-id (ι n)   = ~refl
dr-id (A ⇒ B) =
  ~trans (dr-arr (idHP A) (idHP B))
         (~trans (~⇒ (~trans (~symD (dr-id A)) symD-id) (dr-id B)) ⇒id)

sid : ∀ A → symD (dr (idHP A)) ~ idD
sid A = ~trans (~symD (dr-id A)) symD-id

swapHP' : ∀ {A B C C'} → HPi C C' → HPi (A ⇒ B ⇒ C) (B ⇒ A ⇒ C')
swapHP' {A} {B} (hpi cs) = hpi (cons (there here) (idHP A) (cons here (idHP B) cs))

dr-swap' : ∀ {A B C C'} (k : HPi C C') → dr (swapHP' {A} {B} k) ~ swap ⨾ (idD ⇒≃ (idD ⇒≃ dr k))
dr-swap' {A} {B} (hpi cs) =
  ~trans (~⨾ (~⇒ (sid A) (~trans idr (~⇒ (sid B) ~refl))) (~trans (swap ⨾⟨ ⇒id) idr))
         (~sym swap-nat)

swapHP : ∀ A B C → HPi (A ⇒ B ⇒ C) (B ⇒ A ⇒ C)
swapHP A B C = swapHP' (idHP C)

dr-swap : ∀ A B C → dr (swapHP A B C) ~ swap
dr-swap A B C =
  ~trans (dr-swap' (idHP C))
         (~trans (swap ⨾⟨ ~trans (~⇒ ~refl (~trans (~⇒ ~refl (dr-id C)) ⇒id)) ⇒id) idr)

------------------------------------------------------------------------
-- Normal forms: every derivation is level-2 equal to a canonical one.
-- (Proved together with the same statement for its inverse.)

normal  : ∀ {A B} (φ : A ≃ B) → Σ (HPi A B) (λ h → φ ~ dr h)
normalS : ∀ {A B} (φ : A ≃ B) → Σ (HPi B A) (λ h → symD φ ~ dr h)

normal (idD {A}) = idHP A ,Σ ~sym (dr-id A)
normal (symD φ)  = normalS φ
normal (φ ⨾ ψ) with normal φ | normal ψ
... | h ,Σ p | k ,Σ q = fst (compose h k) ,Σ ~trans (~⨾ p q) (snd (compose h k))
normal (φ ⇒≃ ψ) with normalS φ | normal ψ
... | h ,Σ p | k ,Σ q =
  arrHP h k ,Σ ~trans (~⇒ (~trans (~sym symD-symD) (~symD p)) q) (~sym (dr-arr h k))
normal (swap {A} {B} {C}) = swapHP A B C ,Σ ~sym (dr-swap A B C)

normalS (idD {A}) = idHP A ,Σ ~trans symD-id (~sym (dr-id A))
normalS (symD φ) with normal φ
... | h ,Σ p = h ,Σ ~trans symD-symD p
normalS (φ ⨾ ψ) with normalS φ | normalS ψ
... | h ,Σ p | k ,Σ q =
  fst (compose k h) ,Σ ~trans symD-⨾ (~trans (~⨾ q p) (snd (compose k h)))
normalS (φ ⇒≃ ψ) with normal φ | normalS ψ
... | h ,Σ p | k ,Σ q =
  arrHP h k ,Σ ~trans symD-⇒ (~trans (~⇒ (~symD p) q) (~sym (dr-arr h k)))
normalS (swap {A} {B} {C}) = swapHP B A C ,Σ ~trans symD-swap (~sym (dr-swap B A C))

------------------------------------------------------------------------
-- Faithfulness, from the two semantic facts still to be proved:
--   sound      : level-2 equal derivations have equal components
--   determined : a canonical derivation is determined by its components

module Faithful
  (sound      : ∀ {A B} {φ ψ : A ≃ B} → φ ~ ψ → to⟦ φ ⟧ {ε} ≡ to⟦ ψ ⟧ {ε})
  (determined : ∀ {A B} (h h' : HPi A B) → to⟦ dr h ⟧ {ε} ≡ to⟦ dr h' ⟧ {ε} → h ≡ h')
  where

  faithful : ∀ {A B} (φ ψ : A ≃ B) → to⟦ φ ⟧ {ε} ≡ to⟦ ψ ⟧ {ε} → φ ~ ψ
  faithful φ ψ e with normal φ | normal ψ
  ... | h ,Σ p | h' ,Σ q with determined h h' (trans (sym (sound p)) (trans e (sound q)))
  ...   | refl = ~trans p (~sym q)
