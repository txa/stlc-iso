{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- The link to the list-based hereditary permutations of STLC.Iso:
-- every term satisfying IsHP is ⟦ h ⟧H for some h : HP A B, and hence
-- the statement  Characterisation  of STLC.Iso holds.
------------------------------------------------------------------------
module STLC.Link where

open import STLC.Prelude
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads
open import STLC.LamI
open import STLC.Tele
open import STLC.Iso
open import STLC.Char
open import STLC.Easy using (sp-tgt)

------------------------------------------------------------------------
-- Types as  As ⇒* n

data TyV : Ty → Set where
  tyv : ∀ As n → TyV (As ⇒* n)

tyView : ∀ A → TyV A
tyView (ι n)   = tyv [] n
tyView (A ⇒ B) with tyView B
... | tyv As n = tyv (A ∷ As) n

tgt-⇒* : ∀ As n → tgt (As ⇒* n) ≡ n
tgt-⇒* []       n = refl
tgt-⇒* (A ∷ As) n = tgt-⇒* As n

------------------------------------------------------------------------
-- Positions in lists

data Pos : List Ty → Ty → Set where
  here  : ∀ {A As} → Pos (A ∷ As) A
  there : ∀ {A As σ} → Pos As σ → Pos (A ∷ As) σ

infix 4 _≈P_
data _≈P_ {As σ} (k : Pos As σ) : ∀ {τ} → Pos As τ → Set where
  reflP : k ≈P k

symP : ∀ {As σ τ} {k : Pos As σ} {k' : Pos As τ} → k ≈P k' → k' ≈P k
symP reflP = reflP

transP : ∀ {As σ τ ρ} {k : Pos As σ} {k' : Pos As τ} {k'' : Pos As ρ}
  → k ≈P k' → k' ≈P k'' → k ≈P k''
transP reflP e = e

≡→≈P : ∀ {As σ} {k k' : Pos As σ} → k ≡ k' → k ≈P k'
≡→≈P refl = reflP

there-inj : ∀ {A As σ τ} {k : Pos As σ} {k' : Pos As τ} → there {A} k ≈P there k' → k ≈P k'
there-inj reflP = reflP

cong-there : ∀ {A As σ τ} {k : Pos As σ} {k' : Pos As τ} → k ≈P k' → there {A} k ≈P there k'
cong-there reflP = reflP

noPos : ∀ {σ} → Pos [] σ → ⊥
noPos ()

-- telescope positions and list positions

split-injL : ∀ {Γ} Θ {σ} (u : Var Γ σ) → split {Γ} Θ (injL Θ u) ≡ inL u
split-injL ε u = refl
split-injL {Γ} (Θ ▷ B) u rewrite split-injL {Γ} Θ u = refl

split-injR : ∀ {Γ} Θ {σ} (y : Var Θ σ) → split {Γ} Θ (injR {Γ} Θ y) ≡ inR y
split-injR (Θ ▷ B) vz = refl
split-injR {Γ} (Θ ▷ B) (vs y) rewrite split-injR {Γ} Θ y = refl

varOf : ∀ As n {σ} → Pos As σ → Var (args (As ⇒* n)) σ
varOf (A ∷ As) n here      = injL {ε ▷ A} (args (As ⇒* n)) vz
varOf (A ∷ As) n (there k) = injR {ε ▷ A} (args (As ⇒* n)) (varOf As n k)

posOf : ∀ As n {σ} → Var (args (As ⇒* n)) σ → Pos As σ
posOf (A ∷ As) n v with split {ε ▷ A} (args (As ⇒* n)) v
... | inL vz      = here
... | inL (vs ())
... | inR v'      = there (posOf As n v')

posOf-varOf : ∀ As n {σ} (k : Pos As σ) → posOf As n (varOf As n k) ≡ k
posOf-varOf (A ∷ As) n here
  rewrite split-injL {ε ▷ A} (args (As ⇒* n)) (vz {ε} {A}) = refl
posOf-varOf (A ∷ As) n (there k)
  rewrite split-injR {ε ▷ A} (args (As ⇒* n)) (varOf As n k) = cong there (posOf-varOf As n k)

varOf-posOf : ∀ As n {σ} (v : Var (args (As ⇒* n)) σ) → varOf As n (posOf As n v) ≡ v
varOf-posOf (A ∷ As) n v with split {ε ▷ A} (args (As ⇒* n)) v
... | inL vz      = refl
... | inL (vs ())
... | inR v'      = cong (injR {ε ▷ A} (args (As ⇒* n))) (varOf-posOf As n v')

posOf-≈ : ∀ As n {σ τ} {v : Var (args (As ⇒* n)) σ} {v' : Var (args (As ⇒* n)) τ}
  → v ≈ v' → posOf As n v ≈P posOf As n v'
posOf-≈ As n ≈refl = reflP

------------------------------------------------------------------------
-- Environments, splitting at a position, removal and insertion

lookupA : ∀ {P : Ty → Set} {Bs σ} → All P Bs → Pos Bs σ → P σ
lookupA (p ∷A ps) here      = p
lookupA (p ∷A ps) (there k) = lookupA ps k

mid : ∀ Bs₁ {σ Bs₂} → Pos (Bs₁ ++ σ ∷ Bs₂) σ
mid []        = here
mid (B ∷ Bs₁) = there (mid Bs₁)

data PosV : ∀ (Bs : List Ty) {σ} → Pos Bs σ → Set where
  pv : ∀ Bs₁ {σ} Bs₂ → PosV (Bs₁ ++ σ ∷ Bs₂) (mid Bs₁ {σ} {Bs₂})

posV : ∀ {Bs σ} (k : Pos Bs σ) → PosV Bs k
posV (here {As = As}) = pv [] As
posV (there {A = A} k) with posV k
... | pv Bs₁ Bs₂ = pv (A ∷ Bs₁) Bs₂

remove : ∀ Bs₁ {σ Bs₂ ρ} (k : Pos (Bs₁ ++ σ ∷ Bs₂) ρ) → (k ≈P mid Bs₁ {σ} {Bs₂} → ⊥)
  → Pos (Bs₁ ++ Bs₂) ρ
remove []        here      nq = ⊥-elim (nq reflP)
remove []        (there k) nq = k
remove (B ∷ Bs₁) here      nq = here
remove (B ∷ Bs₁) (there k) nq = there (remove Bs₁ k (λ e → nq (cong-there e)))

insert : ∀ Bs₁ {σ Bs₂ ρ} → Pos (Bs₁ ++ Bs₂) ρ → Pos (Bs₁ ++ σ ∷ Bs₂) ρ
insert []        k         = there k
insert (B ∷ Bs₁) here      = here
insert (B ∷ Bs₁) (there k) = there (insert Bs₁ k)

insert≉mid : ∀ Bs₁ {σ Bs₂ ρ} (k : Pos (Bs₁ ++ Bs₂) ρ) → insert Bs₁ {σ} k ≈P mid Bs₁ {σ} {Bs₂} → ⊥
insert≉mid []        k         ()
insert≉mid (B ∷ Bs₁) here      ()
insert≉mid (B ∷ Bs₁) (there k) e = insert≉mid Bs₁ k (there-inj e)

insert-remove : ∀ Bs₁ {σ Bs₂ ρ} (k : Pos (Bs₁ ++ σ ∷ Bs₂) ρ) nq → insert Bs₁ (remove Bs₁ k nq) ≡ k
insert-remove []        here      nq = ⊥-elim (nq reflP)
insert-remove []        (there k) nq = refl
insert-remove (B ∷ Bs₁) here      nq = refl
insert-remove (B ∷ Bs₁) (there k) nq = cong there (insert-remove Bs₁ k _)

remove-insert : ∀ Bs₁ {σ Bs₂ ρ} (k : Pos (Bs₁ ++ Bs₂) ρ) nq → remove Bs₁ {σ} (insert Bs₁ k) nq ≡ k
remove-insert []        k         nq = refl
remove-insert (B ∷ Bs₁) here      nq = refl
remove-insert (B ∷ Bs₁) (there k) nq = cong there (remove-insert Bs₁ k _)

remove-≈ : ∀ Bs₁ {σ Bs₂ ρ ρ'} (k : Pos (Bs₁ ++ σ ∷ Bs₂) ρ) (k' : Pos (Bs₁ ++ σ ∷ Bs₂) ρ') nq nq'
  → k ≈P k' → remove Bs₁ k nq ≈P remove Bs₁ k' nq'
remove-≈ []        here      .here      nq nq' reflP = ⊥-elim (nq reflP)
remove-≈ []        (there k) .(there k) nq nq' reflP = reflP
remove-≈ (B ∷ Bs₁) here      .here      nq nq' reflP = reflP
remove-≈ (B ∷ Bs₁) (there k) .(there k) nq nq' reflP =
  cong-there (remove-≈ Bs₁ k k _ _ reflP)

lookupA-mid : ∀ {P : Ty → Set} Bs₁ {σ Bs₂} (e₁ : All P Bs₁) (y : P σ) (e₂ : All P Bs₂)
  → lookupA (e₁ ++A (y ∷A e₂)) (mid Bs₁) ≡ y
lookupA-mid []        []A        y e₂ = refl
lookupA-mid (B ∷ Bs₁) (p ∷A e₁) y e₂ = lookupA-mid Bs₁ e₁ y e₂

lookupA-remove : ∀ {P : Ty → Set} Bs₁ {σ Bs₂ ρ} (e₁ : All P Bs₁) (y : P σ) (e₂ : All P Bs₂)
  (k : Pos (Bs₁ ++ σ ∷ Bs₂) ρ) nq
  → lookupA (e₁ ++A e₂) (remove Bs₁ k nq) ≡ lookupA (e₁ ++A (y ∷A e₂)) k
lookupA-remove []        []A        y e₂ here      nq = ⊥-elim (nq reflP)
lookupA-remove []        []A        y e₂ (there k) nq = refl
lookupA-remove (B ∷ Bs₁) (p ∷A e₁) y e₂ here      nq = refl
lookupA-remove (B ∷ Bs₁) (p ∷A e₁) y e₂ (there k) nq = lookupA-remove Bs₁ e₁ y e₂ k _

splitA-eq : ∀ {P : Ty → Set} Bs₁ {Bs₂} (env : All P (Bs₁ ++ Bs₂))
  → fst (splitA Bs₁ env) ++A snd (splitA Bs₁ env) ≡ env
splitA-eq []        env = refl
splitA-eq (B ∷ Bs₁) (p ∷A ps) with splitA Bs₁ ps | splitA-eq Bs₁ ps
... | e₁ ,Σ e₂ | eq = cong (p ∷A_) eq

------------------------------------------------------------------------
-- Elements of spines

spElem : ∀ {Θ As} n {m σ} → Sp Θ (As ⇒* n) (ι m) → Pos As σ → Nf Θ σ
spElem {As = A ∷ As} n (t ∷S ts) here      = t
spElem {As = A ∷ As} n (t ∷S ts) (there k) = spElem {As = As} n ts k

spine-ext : ∀ {Θ} As n {m} (s s' : Sp Θ (As ⇒* n) (ι m))
  → (∀ {σ} (k : Pos As σ) → spElem n s k ≡ spElem n s' k) → s ≡ s'
spine-ext []       n []S       []S         h = refl
spine-ext (A ∷ As) n (t ∷S ts) (t' ∷S ts') h =
  cong₂ _∷S_ (h here) (spine-ext As n ts ts' (λ k → h (there k)))

spElem-spToSub : ∀ As n {Θ m σ} (sp : Sp Θ (As ⇒* n) (ι m)) (k : Pos As σ)
  → spElem n sp k ≡ lookup (spToSub sp) (varOf As n k)
spElem-spToSub (A ∷ As) n (t ∷S ts) here = sym (lookup-⊕L (εs ,s t) (spToSub ts) vz)
spElem-spToSub (A ∷ As) n (t ∷S ts) (there k) =
  trans (spElem-spToSub As n ts k) (sym (lookup-⊕R (εs ,s t) (spToSub ts) (varOf As n k)))

------------------------------------------------------------------------
-- A bijection of list positions is a sequence of insertions

record Bij (As Bs : List Ty) : Set where
  field
    to   : ∀ {σ} → Pos As σ → Σ Ty (Pos Bs)
    from : ∀ {σ} → Pos Bs σ → Σ Ty (Pos As)
    ft   : ∀ {σ} (k : Pos As σ) → snd (from (snd (to k))) ≈P k
    tf   : ∀ {σ} (j : Pos Bs σ) → snd (to (snd (from j))) ≈P j

Spec : ∀ {As Bs} n (to : ∀ {σ} → Pos As σ → Σ Ty (Pos Bs))
  (H : ∀ {σ} (k : Pos As σ) → HP (fst (to k)) σ) → HPs As Bs → Set
Spec {As} {Bs} n to H hs = ∀ {Θ} (env : All (Var Θ) Bs) {σ} (k : Pos As σ)
  → spElem n (spine {n = n} hs env) k ≡ sub ε (⟦ H k ⟧H {Θ}) (nvar (lookupA env (snd (to k))))

consTo : ∀ {A As Bs} σ₀ (j₀ : Pos Bs σ₀) (tt : ∀ {σ} → Pos As σ → Σ Ty (Pos Bs))
  → ∀ {σ} → Pos (A ∷ As) σ → Σ Ty (Pos Bs)
consTo σ₀ j₀ tt here      = σ₀ ,Σ j₀
consTo σ₀ j₀ tt (there k) = tt k

unthere : ∀ {A As σ} (k : Pos (A ∷ As) σ) → (k ≈P here {A} {As} → ⊥) → Pos As σ
unthere here      nq = ⊥-elim (nq reflP)
unthere (there k) nq = k

unthere-≈ : ∀ {A As σ τ} (x : Pos (A ∷ As) σ) nq {k : Pos As τ} → x ≈P there k → unthere x nq ≈P k
unthere-≈ .(there _) nq reflP = reflP

there-unthere : ∀ {A As σ} (x : Pos (A ∷ As) σ) nq → there (unthere x nq) ≈P x
there-unthere here      nq = ⊥-elim (nq reflP)
there-unthere (there k) nq = reflP

buildHPs : ∀ As Bs n (b : Bij As Bs) (H : ∀ {σ} (k : Pos As σ) → HP (fst (Bij.to b k)) σ)
  → Σ (HPs As Bs) (Spec n (Bij.to b) H)

aux : ∀ A As Bs n σ₀ (j₀ : Pos Bs σ₀) (tt : ∀ {σ} → Pos As σ → Σ Ty (Pos Bs))
  (from : ∀ {σ} → Pos Bs σ → Σ Ty (Pos (A ∷ As)))
  (ft : ∀ {σ} (k : Pos (A ∷ As) σ) → snd (from (snd (consTo σ₀ j₀ tt k))) ≈P k)
  (tf : ∀ {σ} (j : Pos Bs σ) → snd (consTo σ₀ j₀ tt (snd (from j))) ≈P j)
  (H : ∀ {σ} (k : Pos (A ∷ As) σ) → HP (fst (consTo σ₀ j₀ tt k)) σ)
  → Σ (HPs (A ∷ As) Bs) (Spec n (consTo σ₀ j₀ tt) H)

buildHPs [] [] n b H = []H ,Σ λ env ()
buildHPs [] (B ∷ Bs) n b H = ⊥-elim (noPos (snd (Bij.from b here)))
buildHPs (A ∷ As) Bs n b H with aux A As Bs n (fst (Bij.to b here)) (snd (Bij.to b here))
                                   (λ k → Bij.to b (there k)) (Bij.from b) ft' tf' H'
  where
  ft' : ∀ {σ} (k : Pos (A ∷ As) σ) → _
  ft' here      = Bij.ft b here
  ft' (there k) = Bij.ft b (there k)
  tf' : ∀ {σ} (j : Pos Bs σ)
    → snd (consTo (fst (Bij.to b here)) (snd (Bij.to b here)) (λ k → Bij.to b (there k))
                  (snd (Bij.from b j))) ≈P j
  tf' j with Bij.from b j | Bij.tf b j
  ... | _ ,Σ here    | e = e
  ... | _ ,Σ there k | e = e
  H' : ∀ {σ} (k : Pos (A ∷ As) σ) → _
  H' here      = H here
  H' (there k) = H (there k)
... | hs ,Σ spec = hs ,Σ spec'
  where
  spec' : Spec n (Bij.to b) H hs
  spec' env here      = spec env here
  spec' env (there k) = spec env (there k)

aux A As Bs n σ₀ j₀ tt from ft tf H with posV j₀
... | pv Bs₁ Bs₂ = hs ,Σ spec
  where
  to = consTo σ₀ (mid Bs₁) tt

  cong-from : ∀ {σ τ} {j : Pos (Bs₁ ++ σ₀ ∷ Bs₂) σ} {j' : Pos _ τ}
    → j ≈P j' → snd (from j) ≈P snd (from j')
  cong-from reflP = reflP
  cong-to : ∀ {σ τ} {k : Pos (A ∷ As) σ} {k' : Pos (A ∷ As) τ} → k ≈P k' → snd (to k) ≈P snd (to k')
  cong-to reflP = reflP

  ne-k : ∀ {σ} (k : Pos As σ) → snd (tt k) ≈P mid Bs₁ → ⊥
  ne-k k e with transP (symP (ft (there k))) (transP (cong-from e) (ft here))
  ... | ()

  ne-j : ∀ {σ} (j : Pos (Bs₁ ++ Bs₂) σ) → snd (from (insert Bs₁ j)) ≈P here {A} {As} → ⊥
  ne-j j e = insert≉mid Bs₁ j (transP (symP (tf (insert Bs₁ j))) (cong-to e))

  tt' : ∀ {σ} → Pos As σ → Σ Ty (Pos (Bs₁ ++ Bs₂))
  tt' k = fst (tt k) ,Σ remove Bs₁ (snd (tt k)) (ne-k k)

  from' : ∀ {σ} → Pos (Bs₁ ++ Bs₂) σ → Σ Ty (Pos As)
  from' j = fst (from (insert Bs₁ j)) ,Σ unthere (snd (from (insert Bs₁ j))) (ne-j j)

  ft' : ∀ {σ} (k : Pos As σ) → snd (from' (snd (tt' k))) ≈P k
  ft' k = unthere-≈ (snd (from (insert Bs₁ (snd (tt' k))))) (ne-j (snd (tt' k)))
            (transP (cong-from (≡→≈P (insert-remove Bs₁ (snd (tt k)) (ne-k k)))) (ft (there k)))

  tf' : ∀ {σ} (j : Pos (Bs₁ ++ Bs₂) σ) → snd (tt' (snd (from' j))) ≈P j
  tf' j = transP (remove-≈ Bs₁ (snd (tt u)) (insert Bs₁ j) (ne-k u) (insert≉mid Bs₁ j) e)
                 (≡→≈P (remove-insert Bs₁ j (insert≉mid Bs₁ j)))
    where
    x = snd (from (insert Bs₁ j))
    u = unthere x (ne-j j)
    e : snd (tt u) ≈P insert Bs₁ j
    e = transP (cong-to (there-unthere x (ne-j j))) (tf (insert Bs₁ j))

  rec = buildHPs As (Bs₁ ++ Bs₂) n (record { to = tt' ; from = from' ; ft = ft' ; tf = tf' })
                 (λ k → H (there k))

  hs : HPs (A ∷ As) (Bs₁ ++ σ₀ ∷ Bs₂)
  hs = ins Bs₁ (H here) (fst rec)

  spec : Spec n to H hs
  spec env k with splitA Bs₁ env | splitA-eq Bs₁ env
  spec .(e₁ ++A (y ∷A e₂)) here      | e₁ ,Σ (y ∷A e₂) | refl =
    cong (λ v → sub ε ⟦ H here ⟧H (nvar v)) (sym (lookupA-mid Bs₁ e₁ y e₂))
  spec .(e₁ ++A (y ∷A e₂)) (there k) | e₁ ,Σ (y ∷A e₂) | refl =
    trans (snd rec (e₁ ++A e₂) k)
          (cong (λ v → sub ε ⟦ H (there k) ⟧H (nvar v))
                (lookupA-remove Bs₁ e₁ y e₂ (snd (tt k)) (ne-k k)))

------------------------------------------------------------------------
-- Γ ++C Bs  and  Γ ⧺ args (Bs ⇒* n): transport by recursion on Bs

convV : ∀ Bs n {Δ σ} → Var (Δ ⧺ args (Bs ⇒* n)) σ → Var (Δ ++C Bs) σ
convV []       n     x = x
convV (B ∷ Bs) n {Δ} x = convV Bs n {Δ ▷ B} x

convNf : ∀ Bs n {Δ σ} → Nf (Δ ⧺ args (Bs ⇒* n)) σ → Nf (Δ ++C Bs) σ
convNf []       n     t = t
convNf (B ∷ Bs) n {Δ} t = convNf Bs n {Δ ▷ B} t

convSpT : ∀ Bs n {Δ ρ} → Sp (Δ ⧺ args (Bs ⇒* n)) ρ (ι (tgt (Bs ⇒* n))) → Sp (Δ ++C Bs) ρ (ι n)
convSpT []       n     sp = sp
convSpT (B ∷ Bs) n {Δ} sp = convSpT Bs n {Δ ▷ B} sp

spElem-conv : ∀ Bs n As {Δ σ} (sp : Sp (Δ ⧺ args (Bs ⇒* n)) (As ⇒* n) (ι (tgt (Bs ⇒* n))))
  (k : Pos As σ) → spElem n (convSpT Bs n {Δ} sp) k ≡ convNf Bs n {Δ} (spElem n sp k)
spElem-conv []       n As     sp k = refl
spElem-conv (B ∷ Bs) n As {Δ} sp k = spElem-conv Bs n As {Δ ▷ B} sp k

convNf-sub1 : ∀ Bs n {Δ ρ σ} (t : Nf (ε ▷ ρ) σ) (y : Var (Δ ⧺ args (Bs ⇒* n)) ρ)
  → convNf Bs n {Δ} (t [ εs ,s nvar y ]) ≡ t [ εs ,s nvar (convV Bs n {Δ} y) ]
convNf-sub1 []       n     t y = refl
convNf-sub1 (B ∷ Bs) n {Δ} t y = convNf-sub1 Bs n {Δ ▷ B} t y

convV-injL : ∀ Bs n {Δ σ} (x : Var Δ σ) → convV Bs n {Δ} (injL (args (Bs ⇒* n)) x) ≡ wkMany Bs x
convV-injL []       n     x = refl
convV-injL (B ∷ Bs) n {Δ} x =
  trans (cong (convV Bs n {Δ ▷ B}) (injL-⧺ (ε ▷ B) (args (Bs ⇒* n)) x)) (convV-injL Bs n (vs x))

convV-vars : ∀ Bs n {Δ σ} (j : Pos Bs σ)
  → convV Bs n {Δ} (injR {Δ} (args (Bs ⇒* n)) (varOf Bs n j)) ≡ lookupA (vars Δ Bs) j
convV-vars (B ∷ Bs) n {Δ} here =
  trans (cong (convV Bs n {Δ ▷ B}) (injR-⧺L {Δ} (ε ▷ B) (args (Bs ⇒* n)) vz)) (convV-injL Bs n vz)
convV-vars (B ∷ Bs) n {Δ} (there j) =
  trans (cong (convV Bs n {Δ ▷ B}) (injR-⧺R {Δ} (ε ▷ B) (args (Bs ⇒* n)) (varOf Bs n j)))
        (convV-vars Bs n {Δ ▷ B} j)

shape : ∀ Bs n {Δ σ} (f : Nf Δ (Bs ⇒* n)) (x : Var Δ σ)
  (sp : Sp (Δ ⧺ args (Bs ⇒* n)) σ (ι (tgt (Bs ⇒* n))))
  → unlam f ≡ ne (injL (args (Bs ⇒* n)) x ∙ sp)
  → f ≡ lams Bs (ne (wkMany Bs x ∙ convSpT Bs n {Δ} sp))
shape []       n     f       x sp e = e
shape (B ∷ Bs) n {Δ} (lam f) x sp e =
  cong lam (shape Bs n f (vs x) sp
              (trans e (cong (λ y → ne (y ∙ sp)) (injL-⧺ (ε ▷ B) (args (Bs ⇒* n)) x))))

sub-ren : ∀ {Θ ρ σ} (t : Nf (ε ▷ ρ) σ) (y : Var Θ ρ)
  → sub ε (t [ εs ,s nvar vz ]) (nvar y) ≡ t [ εs ,s nvar y ]
sub-ren {Θ} t y =
  trans (sub-as ε (t [ εs ,s nvar vz ]) (nvar y))
  (trans ([][] t (εs ,s nvar vz) (idS Θ ,s nvar y))
         (cong (λ u → t [ εs ,s u ]) (nvar-[] vz (idS Θ ,s nvar y))))

------------------------------------------------------------------------
-- Every IsHP term is the meaning of a list-based hereditary permutation

link : ∀ {A B} {f : Nf (ε ▷ A) B} → IsHP f
  → Σ (HP A B) (λ h → ∀ {Γ} → ⟦ h ⟧H {Γ} ≡ f [ εs ,s nvar vz ])
link {A} {B} {f} (isHP τ π πτ τπ t' hps sp body arg) with tyView A | tyView B
... | tyv As n | tyv Bs m with trans (sym (tgt-⇒* As n)) (trans (sp-tgt sp) (tgt-⇒* Bs m))
...   | refl = hp hs ,Σ correct
  where
  W = args (Bs ⇒* n)

  vk : ∀ {σ} → Pos As σ → Var (args (As ⇒* n)) σ
  vk = varOf As n

  congP-π : ∀ {σ} {v v' : Var W σ} → v ≡ v' → posOf As n (snd (π v)) ≈P posOf As n (snd (π v'))
  congP-π refl = reflP
  congP-τ : ∀ {σ} {v v' : Var (args (As ⇒* n)) σ} → v ≡ v'
    → posOf Bs n (snd (τ v)) ≈P posOf Bs n (snd (τ v'))
  congP-τ refl = reflP

  b : Bij As Bs
  b = record
    { to   = λ k → fst (τ (vk k)) ,Σ posOf Bs n (snd (τ (vk k)))
    ; from = λ j → fst (π (varOf Bs n j)) ,Σ posOf As n (snd (π (varOf Bs n j)))
    ; ft   = λ k → transP (congP-π (varOf-posOf Bs n (snd (τ (vk k)))))
                   (transP (posOf-≈ As n (πτ (vk k))) (≡→≈P (posOf-varOf As n k)))
    ; tf   = λ j → transP (congP-τ (varOf-posOf As n (snd (π (varOf Bs n j)))))
                   (transP (posOf-≈ Bs n (τπ (varOf Bs n j))) (≡→≈P (posOf-varOf Bs n j))) }

  IH : ∀ {σ} (k : Pos As σ)
     → Σ (HP (fst (τ (vk k))) σ) (λ h → ∀ {Γ} → ⟦ h ⟧H {Γ} ≡ t' (vk k) [ εs ,s nvar vz ])
  IH k = link (hps (vk k))

  r = buildHPs As Bs n b (λ k → fst (IH k))
  hs = fst r

  correct : ∀ {Γ} → ⟦ hp hs ⟧H {Γ} ≡ f [ εs ,s nvar vz ]
  correct {Γ} = sym (trans (shape Bs n {Γ ▷ (As ⇒* n)} (f [ ρ ]) vz sp₁ e₁)
                           (cong (λ s → lams Bs (ne (wkMany Bs vz ∙ s)))
                                 (spine-ext As n _ _ elems)))
    where
    ρ : Sub (Γ ▷ (As ⇒* n)) (ε ▷ (As ⇒* n))
    ρ = εs ,s nvar vz
    sp₁ = sp [ ρ ⇑ W ]Sp
    env = vars (Γ ▷ (As ⇒* n)) Bs

    e₁ : unlam (f [ ρ ]) ≡ ne (injL W vz ∙ sp₁)
    e₁ = trans (unlam-[] f ρ)
         (trans (cong (_[ ρ ⇑ W ]) body)
         (trans (cong (λ h → appNf h sp₁) (trans (lookup-⇑L ρ W vz) (wkTop-nvar W vz)))
                (appNf-ne2nf (injL W vz) []S sp₁)))

    elems : ∀ {σ} (k : Pos As σ) → spElem n (convSpT Bs n {Γ ▷ (As ⇒* n)} sp₁) k ≡ spElem n (spine hs env) k
    elems k =
      trans (spElem-conv Bs n As {Γ ▷ (As ⇒* n)} sp₁ k)
      (trans (cong (convNf Bs n {Γ ▷ (As ⇒* n)}) (spElem-spToSub As n sp₁ k))
      (trans (cong (λ s → convNf Bs n {Γ ▷ (As ⇒* n)} (lookup s (vk k))) (spToSub-[] sp (ρ ⇑ W)))
      (trans (cong (convNf Bs n {Γ ▷ (As ⇒* n)}) (lookup-∘s (spToSub sp) (ρ ⇑ W) (vk k)))
      (trans (cong (λ t → convNf Bs n {Γ ▷ (As ⇒* n)} (t [ ρ ⇑ W ])) (arg (vk k)))
      (trans (cong (convNf Bs n {Γ ▷ (As ⇒* n)})
               (trans ([][] (t' (vk k)) (εs ,s nvar (injR {ε ▷ (As ⇒* n)} W j)) (ρ ⇑ W))
                      (cong (λ u → t' (vk k) [ εs ,s u ])
                            (trans (nvar-[] (injR {ε ▷ (As ⇒* n)} W j) (ρ ⇑ W))
                                   (lookup-⇑R ρ W j)))))
      (trans (convNf-sub1 Bs n {Γ ▷ (As ⇒* n)} (t' (vk k)) (injR {Γ ▷ (As ⇒* n)} W j))
      (trans (cong (λ v → t' (vk k) [ εs ,s nvar v ])
               (trans (cong (λ v → convV Bs n {Γ ▷ (As ⇒* n)} (injR {Γ ▷ (As ⇒* n)} W v)) (sym (varOf-posOf Bs n j)))
                      (convV-vars Bs n {Γ ▷ (As ⇒* n)} (posOf Bs n j))))
      (sym (trans (snd r env k)
           (trans (cong (λ u → sub ε u (nvar (lookupA env (posOf Bs n j)))) (snd (IH k)))
                  (sub-ren (t' (vk k)) (lookupA env (posOf Bs n j)))))))))))))
      where
      j = snd (τ (vk k))

------------------------------------------------------------------------
-- The statement of STLC.Iso

characterisation-HP : Characterisation
characterisation-HP iso with link (characterisation iso)
... | h ,Σ e = h ,Σ trans e ([]-id (fw (pair iso)))
