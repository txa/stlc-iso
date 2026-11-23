{-# OPTIONS --rewriting #-}
------------------------------------------------------------------------
-- Counting occurrences, and Lemma (counting) of the note:
--
--   if t and all components of ρ are λI, then for all v and y
--
--     #v(t) · #y(ρ_v)  ≤  #y(t [ ρ ])
--
-- Hereditary substitution of λI terms does not erase: every occurrence
-- of v in t contributes all the occurrences of y in ρ_v.  It may copy,
-- hence ≤ and not =.
------------------------------------------------------------------------
module STLC.Count where

open import STLC.Prelude
open import Agda.Builtin.Nat public using (_+_; _*_)
open import STLC.Syntax
open import STLC.Lemmas
open import STLC.Subst
open import STLC.Heads
open import STLC.LamI

------------------------------------------------------------------------
-- Arithmetic

infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     q       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-≡ : ∀ {m n} → m ≡ n → m ≤ n
≤-≡ refl = ≤-refl

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n     z≤n     = refl
≤-antisym (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

≤-suc : ∀ n → n ≤ suc n
≤-suc zero    = z≤n
≤-suc (suc n) = s≤s (≤-suc n)

≤-+l : ∀ a {n} → n ≤ a + n
≤-+l zero    = ≤-refl
≤-+l (suc a) = ≤-trans (≤-+l a) (≤-suc _)

≤-+r : ∀ a b → a ≤ a + b
≤-+r zero    b = z≤n
≤-+r (suc a) b = s≤s (≤-+r a b)

+-mono : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
+-mono {b = b} z≤n q = ≤-trans q (≤-+l b)
+-mono (s≤s p) q = s≤s (+-mono p q)

+0 : ∀ n → n + 0 ≡ n
+0 zero    = refl
+0 (suc n) = cong suc (+0 n)

+suc : ∀ m n → m + suc n ≡ suc (m + n)
+suc zero    n = refl
+suc (suc m) n = cong suc (+suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+0 n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+suc n m))

+-assoc : ∀ l m n → (l + m) + n ≡ l + (m + n)
+-assoc zero    m n = refl
+-assoc (suc l) m n = cong suc (+-assoc l m n)

+-left-comm : ∀ a b c → a + (b + c) ≡ b + (a + c)
+-left-comm a b c =
  trans (sym (+-assoc a b c)) (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

-- (a + b) + (c + d) = (a + c) + (b + d)
+-swap : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-swap a b c d =
  trans (+-assoc a b (c + d)) (trans (cong (a +_) (+-left-comm b c d)) (sym (+-assoc a c (b + d))))

*-distrib : ∀ a b c → (a + b) * c ≡ a * c + b * c
*-distrib zero    b c = refl
*-distrib (suc a) b c = trans (cong (c +_) (*-distrib a b c)) (sym (+-assoc c (a * c) (b * c)))

1* : ∀ n → 1 * n ≡ n
1* n = +0 n

-- multiplying by a positive number does not decrease
≤-*l : ∀ {k} n → 1 ≤ k → n ≤ k * n
≤-*l {suc k} n p = ≤-+r n (k * n)

≤-*r : ∀ n {k} → 1 ≤ k → n ≤ n * k
≤-*r zero    p = z≤n
≤-*r (suc n) p = +-mono p (≤-*r n p)

-- n · k ≤ m with k ≥ 1 gives n ≤ m
≤-*pos : ∀ n {k m} → 1 ≤ k → n * k ≤ m → n ≤ m
≤-*pos n p q = ≤-trans (≤-*r n p) q

-- a number bounded by something that is not positive is 0
≤-not-pos : ∀ n {m} → n ≤ m → (1 ≤ m → ⊥) → n ≡ 0
≤-not-pos zero    p f = refl
≤-not-pos (suc n) p f = ⊥-elim (f (≤-trans (s≤s z≤n) p))

------------------------------------------------------------------------
-- Equality of variables, as a number

eqv : ∀ {Γ σ τ} → Var Γ σ → Var Γ τ → Nat
eqv vz     vz     = 1
eqv vz     (vs y) = 0
eqv (vs x) vz     = 0
eqv (vs x) (vs y) = eqv x y

eqv-refl : ∀ {Γ σ} (x : Var Γ σ) → eqv x x ≡ 1
eqv-refl vz     = refl
eqv-refl (vs x) = eqv-refl x

eqv-≈ : ∀ {Γ σ τ} (x : Var Γ σ) (y : Var Γ τ) → 1 ≤ eqv x y → x ≈ y
eqv-≈ vz     vz     p = ≈refl
eqv-≈ vz     (vs y) ()
eqv-≈ (vs x) vz     ()
eqv-≈ (vs x) (vs y) p with eqv-≈ x y p
... | ≈refl = ≈refl

eqv-wkv : ∀ {Γ A} Ξ {σ τ} (x : Var (Γ ⧺ Ξ) σ) (y : Var (Γ ⧺ Ξ) τ)
  → eqv (wkv {Γ} {A} Ξ x) (wkv Ξ y) ≡ eqv x y
eqv-wkv ε       x      y      = refl
eqv-wkv (Ξ ▷ C) vz     vz     = refl
eqv-wkv (Ξ ▷ C) vz     (vs y) = refl
eqv-wkv (Ξ ▷ C) (vs x) vz     = refl
eqv-wkv (Ξ ▷ C) (vs x) (vs y) = eqv-wkv Ξ x y

eqv-wkv-top : ∀ {Γ A} Ξ {σ} (x : Var (Γ ⧺ Ξ) σ) → eqv (wkv {Γ} {A} Ξ x) (top Ξ) ≡ 0
eqv-wkv-top ε       x      = refl
eqv-wkv-top (Ξ ▷ C) vz     = refl
eqv-wkv-top (Ξ ▷ C) (vs x) = eqv-wkv-top Ξ x

eqv-top-wkv : ∀ {Γ A} Ξ {σ} (x : Var (Γ ⧺ Ξ) σ) → eqv (top {Γ} {A} Ξ) (wkv Ξ x) ≡ 0
eqv-top-wkv ε       x      = refl
eqv-top-wkv (Ξ ▷ C) vz     = refl
eqv-top-wkv (Ξ ▷ C) (vs x) = eqv-top-wkv Ξ x

-- if v = x then f v ≤ f x
eqv-mul : ∀ {Δ σ τ} (v : Var Δ σ) (x : Var Δ τ) (f : ∀ {ρ} → Var Δ ρ → Nat)
  → eqv v x * f v ≤ f x
eqv-mul vz     vz     f = ≤-≡ (1* (f vz))
eqv-mul vz     (vs x) f = z≤n
eqv-mul (vs v) vz     f = z≤n
eqv-mul (vs v) (vs x) f = eqv-mul v x (λ w → f (vs w))

------------------------------------------------------------------------
-- Counting occurrences

occ  : ∀ {Γ σ τ}    → Var Γ σ → Nf Γ τ → Nat
occs : ∀ {Γ σ τ τ'} → Var Γ σ → Sp Γ τ τ' → Nat
occ x (lam t)       = occ (vs x) t
occ x (ne (y ∙ sp)) = eqv x y + occs x sp
occs x []S       = 0
occs x (t ∷S ts) = occ x t + occs x ts

∈-occ  : ∀ {Γ σ τ} {x : Var Γ σ} {t : Nf Γ τ} → x ∈ t → 1 ≤ occ x t
∈s-occ : ∀ {Γ σ τ τ'} {x : Var Γ σ} {sp : Sp Γ τ τ'} → x ∈s sp → 1 ≤ occs x sp
∈-occ (o-lam p) = ∈-occ p
∈-occ {x = x} (o-hd {sp = sp}) = ≤-trans (≤-≡ (sym (eqv-refl x))) (≤-+r (eqv x x) (occs x sp))
∈-occ {x = x} (o-arg {y = y} q) = ≤-trans (∈s-occ q) (≤-+l (eqv x y))
∈s-occ (s-hd {ts = ts} p) = ≤-trans (∈-occ p) (≤-+r _ (occs _ ts))
∈s-occ (s-tl {t = t} q)   = ≤-trans (∈s-occ q) (≤-+l (occ _ t))

+-pos : ∀ a {b} → 1 ≤ a + b → (1 ≤ a) ⊎ (1 ≤ b)
+-pos zero    p = inr p
+-pos (suc a) p = inl (s≤s z≤n)

occ-∈  : ∀ {Γ σ τ} (x : Var Γ σ) (t : Nf Γ τ) → 1 ≤ occ x t → x ∈ t
occs-∈ : ∀ {Γ σ τ τ'} (x : Var Γ σ) (sp : Sp Γ τ τ') → 1 ≤ occs x sp → x ∈s sp
occ-∈ x (lam t) p = o-lam (occ-∈ (vs x) t p)
occ-∈ x (ne (y ∙ sp)) p with +-pos (eqv x y) p
... | inr q = o-arg (occs-∈ x sp q)
... | inl q with eqv-≈ x y q
...   | ≈refl = o-hd
occs-∈ x (t ∷S ts) p with +-pos (occ x t) p
... | inl q = s-hd (occ-∈ x t q)
... | inr q = s-tl (occs-∈ x ts q)

FH-occ : ∀ {Γ σ τ} {x : Var Γ σ} {t : Nf Γ τ} → FH x t → 1 ≤ occ x t
FH-occ (fh-lam h) = FH-occ h
FH-occ {x = x} (fh-ne {sp = sp}) = ≤-trans (≤-≡ (sym (eqv-refl x))) (≤-+r (eqv x x) (occs x sp))

------------------------------------------------------------------------
-- Weakening and η-expansion

occ-wk  : ∀ {Γ A} Ξ {σ τ} (x : Var (Γ ⧺ Ξ) σ) (t : Nf (Γ ⧺ Ξ) τ)
  → occ (wkv {Γ} {A} Ξ x) (wkNf Ξ t) ≡ occ x t
occs-wk : ∀ {Γ A} Ξ {σ τ τ'} (x : Var (Γ ⧺ Ξ) σ) (sp : Sp (Γ ⧺ Ξ) τ τ')
  → occs (wkv {Γ} {A} Ξ x) (wkSp Ξ sp) ≡ occs x sp
occ-wk {Γ} {A} Ξ x (lam {B} t)  = occ-wk {Γ} {A} (Ξ ▷ B) (vs x) t
occ-wk {Γ} {A} Ξ x (ne (y ∙ sp)) = cong₂ _+_ (eqv-wkv {Γ} {A} Ξ x y) (occs-wk {Γ} {A} Ξ x sp)
occs-wk Ξ x []S       = refl
occs-wk {Γ} {A} Ξ x (t ∷S ts) = cong₂ _+_ (occ-wk {Γ} {A} Ξ x t) (occs-wk {Γ} {A} Ξ x ts)

occs-snoc : ∀ {Γ σ ρ A B} (w : Var Γ σ) (sp : Sp Γ ρ (A ⇒ B)) (u : Nf Γ A)
  → occs w (snocS sp u) ≡ occs w sp + occ w u
occs-snoc w []S       u = +0 (occ w u)
occs-snoc w (t ∷S ts) u = trans (cong (occ w t +_) (occs-snoc w ts u)) (sym (+-assoc (occ w t) _ _))

occ-ne2nf : ∀ {Γ σ ρ τ} (w : Var Γ σ) (x : Var Γ ρ) (sp : Sp Γ ρ τ)
  → occ w (ne2nf x sp) ≡ eqv w x + occs w sp
occ-ne2nf {τ = ι n}   w x sp = refl
occ-ne2nf {τ = A ⇒ B} w x sp =
  trans (occ-ne2nf (vs w) (vs x) (snocS (wkSp ε sp) (nvar vz)))
  (cong (eqv w x +_)
    (trans (occs-snoc (vs w) (wkSp ε sp) (nvar vz))
    (trans (cong₂ _+_ (occs-wk {A = A} ε w sp) (occ-ne2nf {τ = A} (vs w) vz []S))
           (+0 (occs w sp)))))

occ-nvar : ∀ {Γ σ ρ} (w : Var Γ σ) (x : Var Γ ρ) → occ w (nvar x) ≡ eqv w x
occ-nvar w x = trans (occ-ne2nf w x []S) (+0 (eqv w x))

------------------------------------------------------------------------
-- Single substitution and application on λI terms: λI is preserved,
-- and occurrences are counted

LI-sub   : ∀ {Δ A} Ξ {τ} (t : Nf ((Δ ▷ A) ⧺ Ξ) τ) (a : Nf (Δ ⧺ Ξ) A)
  → LI t → LI a → LI (sub {Δ} {A} Ξ t a)
LIs-sub  : ∀ {Δ A} Ξ {τ τ'} (sp : Sp ((Δ ▷ A) ⧺ Ξ) τ τ') (a : Nf (Δ ⧺ Ξ) A)
  → LIs sp → LI a → LIs (subSp {Δ} {A} Ξ sp a)
LI-app   : ∀ {Γ ρ τ} (t : Nf Γ ρ) (sp : Sp Γ ρ τ) → LI t → LIs sp → LI (appNf t sp)
cnt-sub  : ∀ {Δ A} Ξ {σ τ} (t : Nf ((Δ ▷ A) ⧺ Ξ) τ) (a : Nf (Δ ⧺ Ξ) A) (y : Var (Δ ⧺ Ξ) σ)
  → LI t → LI a
  → occ (wkv Ξ y) t + occ (top {Δ} {A} Ξ) t * occ y a ≤ occ y (sub {Δ} {A} Ξ t a)
cnt-subs : ∀ {Δ A} Ξ {σ τ τ'} (sp : Sp ((Δ ▷ A) ⧺ Ξ) τ τ') (a : Nf (Δ ⧺ Ξ) A) (y : Var (Δ ⧺ Ξ) σ)
  → LIs sp → LI a
  → occs (wkv Ξ y) sp + occs (top {Δ} {A} Ξ) sp * occ y a ≤ occs y (subSp {Δ} {A} Ξ sp a)
cnt-app  : ∀ {Γ ρ τ σ} (t : Nf Γ ρ) (sp : Sp Γ ρ τ) (y : Var Γ σ)
  → LI t → LIs sp → occ y t + occs y sp ≤ occ y (appNf t sp)

LI-sub Ξ (lam {B} t) a (li-lam o l) la =
  li-lam (occ-∈ vz _ (≤-trans (≤-trans (∈-occ o) (≤-+r (occ vz t) _))
                              (cnt-sub (Ξ ▷ B) t (wkNf ε a) vz l (LI-wk ε la))))
         (LI-sub (Ξ ▷ B) t (wkNf ε a) l (LI-wk ε la))
LI-sub {Δ} {A} Ξ (ne (h ∙ sp)) a (li-ne ls) la with look {Δ} {A} Ξ h
... | same rewrite lk-top {Δ} {A} Ξ =
  LI-app a (subSp Ξ sp a) la (LIs-sub Ξ sp a ls la)
... | diff z rewrite lk-wkv {Δ} {A} Ξ z = li-ne (LIs-sub Ξ sp a ls la)

LIs-sub Ξ []S       a lis-nil         la = lis-nil
LIs-sub Ξ (t ∷S ts) a (lis-cons l ls) la =
  lis-cons (LI-sub Ξ t a l la) (LIs-sub Ξ ts a ls la)

LI-app t       []S       l            ls               = l
LI-app (lam t) (b ∷S bs) (li-lam o l) (lis-cons lb ls) =
  LI-app (sub ε t b) bs (LI-sub ε t b l lb) ls

cnt-sub Ξ (lam {B} t) a y (li-lam o l) la =
  ≤-trans (≤-≡ (cong (λ k → occ (vs (wkv Ξ y)) t + occ (vs (top Ξ)) t * k) (sym (occ-wk ε y a))))
          (cnt-sub (Ξ ▷ B) t (wkNf ε a) (vs y) l (LI-wk ε la))
cnt-sub {Δ} {A} Ξ (ne (h ∙ sp)) a y (li-ne ls) la with look {Δ} {A} Ξ h
... | same rewrite lk-top {Δ} {A} Ξ =
  ≤-trans (≤-≡ e)
  (≤-trans (+-mono (≤-refl {c}) (cnt-subs Ξ sp a y ls la))
           (cnt-app a (subSp Ξ sp a) y la (LIs-sub Ξ sp a ls la)))
  where
  c  = occ y a
  A1 = occs (wkv Ξ y) sp
  B1 = occs (top {Δ} {A} Ξ) sp
  e : (eqv (wkv Ξ y) (top {Δ} {A} Ξ) + A1) + (eqv (top {Δ} {A} Ξ) (top Ξ) + B1) * c ≡ c + (A1 + B1 * c)
  e = trans (cong₂ (λ u v → (u + A1) + (v + B1) * c) (eqv-wkv-top Ξ y) (eqv-refl (top {Δ} {A} Ξ)))
            (+-left-comm A1 c (B1 * c))
... | diff z rewrite lk-wkv {Δ} {A} Ξ z =
  ≤-trans (≤-≡ e) (+-mono (≤-refl {eqv y z}) (cnt-subs Ξ sp a y ls la))
  where
  c  = occ y a
  A1 = occs (wkv Ξ y) sp
  B1 = occs (top {Δ} {A} Ξ) sp
  e : (eqv (wkv Ξ y) (wkv Ξ z) + A1) + (eqv (top {Δ} {A} Ξ) (wkv Ξ z) + B1) * c ≡ eqv y z + (A1 + B1 * c)
  e = trans (cong₂ (λ u v → (u + A1) + (v + B1) * c) (eqv-wkv Ξ y z) (eqv-top-wkv Ξ z))
            (+-assoc (eqv y z) A1 (B1 * c))

cnt-subs Ξ []S       a y lis-nil         la = z≤n
cnt-subs {Δ} {A} Ξ (t ∷S ts) a y (lis-cons l ls) la =
  ≤-trans (≤-≡ e) (+-mono (cnt-sub Ξ t a y l la) (cnt-subs Ξ ts a y ls la))
  where
  c = occ y a
  e : (occ (wkv Ξ y) t + occs (wkv Ξ y) ts) + (occ (top {Δ} {A} Ξ) t + occs (top {Δ} {A} Ξ) ts) * c
    ≡ (occ (wkv Ξ y) t + occ (top {Δ} {A} Ξ) t * c) + (occs (wkv Ξ y) ts + occs (top {Δ} {A} Ξ) ts * c)
  e = trans (cong ((occ (wkv Ξ y) t + occs (wkv Ξ y) ts) +_)
                  (*-distrib (occ (top {Δ} {A} Ξ) t) (occs (top {Δ} {A} Ξ) ts) c))
            (+-swap (occ (wkv Ξ y) t) (occs (wkv Ξ y) ts)
                    (occ (top {Δ} {A} Ξ) t * c) (occs (top {Δ} {A} Ξ) ts * c))

cnt-app t       []S       y l            ls               = ≤-≡ (+0 (occ y t))
cnt-app (lam t) (b ∷S bs) y (li-lam o l) (lis-cons lb ls) =
  ≤-trans (≤-≡ (sym (+-assoc (occ (vs y) t) (occ y b) (occs y bs))))
  (≤-trans (+-mono (+-mono (≤-refl {occ (vs y) t}) (≤-*l (occ y b) (∈-occ o))) (≤-refl {occs y bs}))
  (≤-trans (+-mono (cnt-sub ε t b y l lb) (≤-refl {occs y bs}))
           (cnt-app (sub ε t b) bs y (LI-sub ε t b l lb) ls)))

------------------------------------------------------------------------
-- Lemma (counting): simultaneous substitution

LIS : ∀ {Γ Δ} → Sub Γ Δ → Set
LIS {Δ = Δ} ρ = ∀ {σ} (v : Var Δ σ) → LI (lookup ρ v)

LIS-↑ : ∀ {Γ Δ A} (ρ : Sub Γ Δ) → LIS ρ → LIS (_↑ {A = A} ρ)
LIS-↑ ρ lρ vz     = LI-nvar vz
LIS-↑ {A = A} ρ lρ (vs v) =
  subst LI (sym (lookup-mapS (wkNf {σ = A} ε) ρ v)) (LI-wk ε (lρ v))

LI-[]   : ∀ {Γ Δ τ} (t : Nf Δ τ) (ρ : Sub Γ Δ) → LI t → LIS ρ → LI (t [ ρ ])
LIs-[]  : ∀ {Γ Δ τ τ'} (sp : Sp Δ τ τ') (ρ : Sub Γ Δ) → LIs sp → LIS ρ → LIs (sp [ ρ ]Sp)
cnt-[]  : ∀ {Γ Δ τ σ ρ'} (t : Nf Δ τ) (ρ : Sub Γ Δ) (v : Var Δ ρ') (y : Var Γ σ)
  → LI t → LIS ρ → occ v t * occ y (lookup ρ v) ≤ occ y (t [ ρ ])
cnt-[]s : ∀ {Γ Δ τ τ' σ ρ'} (sp : Sp Δ τ τ') (ρ : Sub Γ Δ) (v : Var Δ ρ') (y : Var Γ σ)
  → LIs sp → LIS ρ → occs v sp * occ y (lookup ρ v) ≤ occs y (sp [ ρ ]Sp)

LI-[] {Γ} (lam {A} t) ρ (li-lam o l) lρ =
  li-lam (occ-∈ vz _ (≤-trans (∈-occ o) (≤-trans (≤-≡ e) (cnt-[] t (ρ ↑) vz vz l (LIS-↑ ρ lρ)))))
         (LI-[] t (ρ ↑) l (LIS-↑ ρ lρ))
  where
  *1 : ∀ n → n * 1 ≡ n
  *1 zero    = refl
  *1 (suc n) = cong suc (*1 n)
  e : occ vz t ≡ occ vz t * occ vz (nvar {Γ ▷ A} vz)
  e = trans (sym (*1 (occ vz t))) (cong (occ vz t *_) (sym (occ-nvar {Γ ▷ A} vz vz)))
LI-[] (ne (x ∙ sp)) ρ (li-ne ls) lρ = LI-app (lookup ρ x) (sp [ ρ ]Sp) (lρ x) (LIs-[] sp ρ ls lρ)

LIs-[] []S       ρ lis-nil         lρ = lis-nil
LIs-[] (t ∷S ts) ρ (lis-cons l ls) lρ = lis-cons (LI-[] t ρ l lρ) (LIs-[] ts ρ ls lρ)

cnt-[] (lam {A} t) ρ v y (li-lam o l) lρ =
  ≤-trans (≤-≡ (cong (λ k → occ (vs v) t * k) (sym e)))
          (cnt-[] t (ρ ↑) (vs v) (vs y) l (LIS-↑ ρ lρ))
  where
  e : occ (vs y) (lookup (_↑ {A = A} ρ) (vs v)) ≡ occ y (lookup ρ v)
  e = trans (cong (occ (vs y)) (lookup-mapS (wkNf {σ = A} ε) ρ v)) (occ-wk ε y (lookup ρ v))
cnt-[] (ne (x ∙ sp)) ρ v y (li-ne ls) lρ =
  ≤-trans (≤-≡ (*-distrib (eqv v x) (occs v sp) c))
  (≤-trans (+-mono (eqv-mul v x (λ w → occ y (lookup ρ w))) (cnt-[]s sp ρ v y ls lρ))
           (cnt-app (lookup ρ x) (sp [ ρ ]Sp) y (lρ x) (LIs-[] sp ρ ls lρ)))
  where c = occ y (lookup ρ v)

cnt-[]s []S       ρ v y lis-nil         lρ = z≤n
cnt-[]s (t ∷S ts) ρ v y (lis-cons l ls) lρ =
  ≤-trans (≤-≡ (*-distrib (occ v t) (occs v ts) _))
          (+-mono (cnt-[] t ρ v y l lρ) (cnt-[]s ts ρ v y ls lρ))
