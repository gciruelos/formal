import Mathlib
import CiruelosLic.Chapter1Preliminaries

/-!
# Background: orthogonality of β-reduction

The thesis cites orthogonality of the λ-calculus from Melliès; we prove it via marked terms (Huet's commutation theorem, Lévy's cube lemma, de Vrijer's finite developments), then derive the Chapter 1 results that rest on it.

Contents:
* Background: residuals of β-reduction via marked terms
* Chapter 0 (support): position and substitution lemmas for λ-terms
* Background: from positional residuals to marked terms
* Background results assumed by the thesis
* Chapter 1: the λ-calculus as an orthogonal rewrite system
-/

namespace CiruelosLic

/-! ## Background: residuals of β-reduction via marked terms

A self-contained formalization of the residual theory of the pure λ-calculus (de Bruijn
indices), following Huet's "Residual theory in λ-calculus: a formal development" and its
adaptation in Stark's Isabelle/AFP entry `ResiduatedTransitionSystem` (theory `LambdaCalculus`).

Terms carry marked redexes (`beta t u` stands for a marked `(λ t) u`), and residuation is a partial
function on marked terms.  This file develops index raising, substitution, residuation, and
Lévy's cube lemma. -/

end CiruelosLic

namespace CiruelosLic.Marked

inductive MT
  | nil : MT
  | var : ℕ → MT
  | lam : MT → MT
  | app : MT → MT → MT
  | beta : MT → MT → MT
  deriving DecidableEq

namespace MT

/-- Raising indices of free variables (above depth `d`) by `n`. -/
def Raise : ℕ → ℕ → MT → MT
  | _, _, nil => nil
  | d, n, var i => if d ≤ i then var (i + n) else var i
  | d, n, lam t => lam (Raise (d + 1) n t)
  | d, n, app t u => app (Raise d n t) (Raise d n u)
  | d, n, beta t u => beta (Raise (d + 1) n t) (Raise d n u)

/-- `Subst n v t`: substitute `v` for the variable `n` in `t`. -/
def Subst : ℕ → MT → MT → MT
  | _, _, nil => nil
  | n, v, var i => if n < i then var (i - 1) else if n = i then Raise 0 n v else var i
  | n, v, lam t => lam (Subst (n + 1) v t)
  | n, v, app t u => app (Subst n v t) (Subst n v u)
  | n, v, beta t u => beta (Subst (n + 1) v t) (Subst n v u)

/-- Closing tactic for the arithmetic on variable cases. -/
macro "var_arith" : tactic =>
  `(tactic| (simp only [Raise]; split_ifs <;> (try simp only [Raise]) <;> (try split_ifs) <;>
    first | omega | (congr 1; omega) | (simp_all; omega) | rfl))

/-! ### Raising -/

theorem Raise_ne_nil {t : MT} (h : t ≠ nil) (d n : ℕ) : Raise d n t ≠ nil := by
  cases t <;> simp_all [Raise] <;> split <;> simp

theorem Raise_plus (t : MT) : ∀ d m n, Raise d (m + n) t = Raise (d + m) n (Raise d m t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro d m n
    var_arith
  | lam t ih =>
    intro d m n
    simp only [Raise]
    rw [ih (d + 1) m n, show d + 1 + m = d + m + 1 by omega]
  | app t u iht ihu => intro d m n; simp [Raise, iht, ihu]
  | beta t u iht ihu =>
    intro d m n
    simp only [Raise]
    rw [ihu d m n, iht (d + 1) m n, show d + 1 + m = d + m + 1 by omega]

theorem Raise_plus' (t : MT) : ∀ d d' m n, d' ≤ d + n → d ≤ d' →
    Raise d (m + n) t = Raise d' m (Raise d n t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro d d' m n h1 h2
    var_arith
  | lam t ih =>
    intro d d' m n h1 h2
    simp only [Raise]
    rw [ih (d + 1) (d' + 1) m n (by omega) (by omega)]
  | app t u iht ihu =>
    intro d d' m n h1 h2; simp [Raise, iht d d' m n h1 h2, ihu d d' m n h1 h2]
  | beta t u iht ihu =>
    intro d d' m n h1 h2
    simp only [Raise]
    rw [iht (d + 1) (d' + 1) m n (by omega) (by omega), ihu d d' m n h1 h2]

theorem Raise_Raise (t : MT) : ∀ i n p k, i ≤ n →
    Raise i p (Raise n k t) = Raise (p + n) k (Raise i p t) := by
  induction t with
  | nil => intros; rfl
  | var j =>
    intro i n p k h
    var_arith
  | lam t ih =>
    intro i n p k h
    simp only [Raise]
    rw [ih (i + 1) (n + 1) p k (by omega)]
    rfl
  | app t u iht ihu => intro i n p k h; simp [Raise, iht i n p k h, ihu i n p k h]
  | beta t u iht ihu =>
    intro i n p k h
    simp only [Raise]
    rw [iht (i + 1) (n + 1) p k (by omega), ihu i n p k h]
    rfl

/-! ### Substitution -/

theorem Subst_ne_nil {v : MT} (hv : v ≠ nil) : ∀ {t : MT}, t ≠ nil → ∀ n, Subst n v t ≠ nil := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | var i =>
    intro _ n
    simp only [Subst]
    split_ifs
    · simp
    · exact Raise_ne_nil hv _ _
    · simp
  | lam t ih => intro _ n; simp [Subst]
  | app t u _ _ => intro _ n; simp [Subst]
  | beta t u _ _ => intro _ n; simp [Subst]

/-- Closing tactic for variable cases involving `Subst` and `Raise`. -/
macro "sub_arith" : tactic =>
  `(tactic| (simp only [Raise, Subst]; split_ifs <;> (try simp only [Raise, Subst]) <;>
    (try split_ifs) <;>
    first | omega | (congr 1; omega) | (simp_all; omega) | rfl))

theorem Raise_Subst (t : MT) : ∀ (p n k : ℕ) (v : MT),
    Raise (p + n) k (Subst p v t) = Subst p (Raise n k v) (Raise (p + n + 1) k t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro p n k v
    by_cases h2 : p = i
    · subst h2
      have e := Raise_Raise v 0 n p k (Nat.zero_le _)
      simp only [Subst, Raise]
      split_ifs <;> (try simp only [Subst, Raise]) <;> (try split_ifs) <;>
        first | omega | (simp_all; done) | (rw [e]) | (rw [← e])
    · sub_arith
  | lam t ih =>
    intro p n k v
    simp only [Subst, Raise]
    have := ih (p + 1) n k v
    rw [show p + 1 + n = p + n + 1 by omega] at this
    rw [this]
  | app t u iht ihu => intro p n k v; simp only [Subst, Raise, iht, ihu]
  | beta t u iht ihu =>
    intro p n k v
    simp only [Subst, Raise]
    have := iht (p + 1) n k v
    rw [show p + 1 + n = p + n + 1 by omega] at this
    rw [this, ihu]

theorem Raise_Subst' {v : MT} (hv : v ≠ nil) (t : MT) : ∀ (k p n : ℕ), k ≤ n →
    Raise k p (Subst n v t) = Subst (p + n) v (Raise k p t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro k p n h
    have e := Raise_plus' v 0 k p n (by omega) (by omega)
    simp only [Subst, Raise]
    split_ifs <;> (try simp only [Subst, Raise]) <;> (try split_ifs) <;>
      first | omega | (simp_all; done) | (congr 1; omega) | (rw [e]) | (rw [← e]) | rfl
  | lam t ih =>
    intro k p n h
    simp only [Subst, Raise]
    rw [ih (k + 1) p (n + 1) (by omega), show p + (n + 1) = p + n + 1 by omega]
  | app t u iht ihu => intro k p n h; simp only [Subst, Raise, iht k p n h, ihu k p n h]
  | beta t u iht ihu =>
    intro k p n h
    simp only [Subst, Raise]
    rw [iht (k + 1) p (n + 1) (by omega), ihu k p n h, show p + (n + 1) = p + n + 1 by omega]

theorem Subst_Raise {v : MT} (t : MT) : ∀ (d m n : ℕ), d ≤ m → m ≤ n + d →
    Subst m v (Raise d (n + 1) t) = Raise d n t := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro d m n h1 h2
    simp only [Raise]
    split_ifs <;> (try simp only [Subst, Raise]) <;> (try split_ifs) <;>
      first | omega | (congr 1; omega) | (simp_all; omega) | rfl
  | lam t ih =>
    intro d m n h1 h2
    simp only [Raise, Subst]
    rw [ih (d + 1) (m + 1) n (by omega) (by omega)]
  | app t u iht ihu => intro d m n h1 h2; simp only [Raise, Subst, iht d m n h1 h2, ihu d m n h1 h2]
  | beta t u iht ihu =>
    intro d m n h1 h2
    simp only [Raise, Subst]
    rw [iht (d + 1) (m + 1) n (by omega) (by omega), ihu d m n h1 h2]

theorem Subst_Subst {v w : MT} (hv : v ≠ nil) (hw : w ≠ nil) (t : MT) : ∀ (m n : ℕ),
    Subst (m + n) w (Subst m v t) = Subst m (Subst n w v) (Subst (m + n + 1) w t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro m n
    have e1 := Raise_Subst' (v := w) hw v 0 m n (Nat.zero_le _)
    have e2 := Subst_Raise (v := Subst n w v) w 0 m (m + n) (Nat.zero_le _) (by omega)
    simp only [Subst]
    split_ifs <;> (try simp only [Subst]) <;> (try split_ifs) <;>
      first | omega | (simp_all; done) | (congr 1; omega) | (rw [← e1]) | (rw [e1]) | (rw [e2]) |
        (rw [← e2]) | rfl
  | lam t ih =>
    intro m n
    simp only [Subst]
    have := ih (m + 1) n
    rw [show m + 1 + n = m + n + 1 by omega] at this
    rw [this]
  | app t u iht ihu => intro m n; simp only [Subst, iht, ihu]
  | beta t u iht ihu =>
    intro m n
    simp only [Subst]
    have := iht (m + 1) n
    rw [show m + 1 + n = m + n + 1 by omega] at this
    rw [this, ihu]

theorem substitution_lemma {v w : MT} (hv : v ≠ nil) (hw : w ≠ nil) (t : MT) (n : ℕ) :
    Subst n v (Subst 0 w t) = Subst 0 (Subst n v w) (Subst (n + 1) v t) := by
  have := Subst_Subst hw hv t 0 n
  simpa using this

theorem Raise_subst (t v : MT) (n k : ℕ) :
    Raise n k (Subst 0 v t) = Subst 0 (Raise n k v) (Raise (n + 1) k t) := by
  have := Raise_Subst t 0 n k v
  simpa using this

theorem Raise_eq_nil_iff {t : MT} {d n : ℕ} : Raise d n t = nil ↔ t = nil := by
  constructor
  · intro h; by_contra hne; exact Raise_ne_nil hne d n h
  · rintro rfl; rfl

/-! ### Residuation -/

/-- Residuation of marked terms: `resid t u` is `t \ u` (or `nil` if undefined). -/
def resid : MT → MT → MT
  | var i, var j => if i = j then var i else nil
  | lam t, lam t' => if resid t t' = nil then nil else lam (resid t t')
  | app t u, app t' u' =>
      if resid t t' = nil ∨ resid u u' = nil then nil else app (resid t t') (resid u u')
  | beta t u, beta t' u' =>
      if resid t t' = nil ∨ resid u u' = nil then nil else Subst 0 (resid u u') (resid t t')
  | app (lam t) u, beta t' u' =>
      if resid t t' = nil ∨ resid u u' = nil then nil else Subst 0 (resid u u') (resid t t')
  | beta t u, app (lam t') u' =>
      if resid t t' = nil ∨ resid u u' = nil then nil else beta (resid t t') (resid u u')
  | _, _ => nil

@[simp] theorem resid_nil_left (u : MT) : resid nil u = nil := by cases u <;> rfl

/-- Size of a marked term (for well-founded induction). -/
def size : MT → ℕ
  | nil => 0
  | var _ => 1
  | lam t => size t + 1
  | app t u => size t + size u + 1
  | beta t u => size t + size u + 2

@[simp] theorem Raise_var' (d n i : ℕ) :
    Raise d n (var i) = var (if d ≤ i then i + n else i) := by
  simp only [Raise]; split_ifs <;> rfl

@[simp] theorem Raise_lam (d n : ℕ) (t : MT) : Raise d n (lam t) = lam (Raise (d + 1) n t) := rfl
@[simp] theorem Raise_app (d n : ℕ) (t u : MT) :
    Raise d n (app t u) = app (Raise d n t) (Raise d n u) := rfl
@[simp] theorem Raise_beta (d n : ℕ) (t u : MT) :
    Raise d n (beta t u) = beta (Raise (d + 1) n t) (Raise d n u) := rfl
@[simp] theorem Raise_nil' (d n : ℕ) : Raise d n nil = nil := rfl

@[simp] theorem resid_nil_right (t : MT) : resid t nil = nil := by cases t <;> rfl

/-- Raising commutes with residuation (stated right to left so the induction hypotheses rewrite). -/
theorem resid_Raise (t u : MT) (k n : ℕ) :
    resid (Raise k n t) (Raise k n u) = Raise k n (resid t u) := by
  induction t, u using resid.induct generalizing k
  case case13 t x h1 h2 h3 h4 h5 h6 =>
    cases t <;> cases x
    all_goals first
      | exact (h1 _ _ rfl rfl).elim | exact (h2 _ _ rfl rfl).elim | exact (h3 _ _ _ _ rfl rfl).elim
      | exact (h4 _ _ _ _ rfl rfl).elim | skip
    case app.beta a b c d => cases a <;> first | exact (h5 _ _ _ _ rfl rfl).elim | simp [resid]
    case beta.app a b c d => cases c <;> first | exact (h6 _ _ _ _ rfl rfl).elim | simp [resid]
    all_goals simp [resid]
  all_goals simp_all [resid, Raise_eq_nil_iff, Raise_subst]
  split_ifs <;> omega

theorem Raise_resid (t u : MT) (k n : ℕ) :
    Raise k n (resid t u) = resid (Raise k n t) (Raise k n u) :=
  (resid_Raise t u k n).symm

@[simp] theorem Subst_var_eq (n : ℕ) (v : MT) : Subst n v (var n) = Raise 0 n v := by
  simp [Subst]

/-- **Huet's commutation theorem**: substitution commutes with residuation. -/
theorem resid_Subst {t t' u u' : MT} (ht : resid t t' ≠ nil) (hu : resid u u' ≠ nil) (n : ℕ) :
    resid (Subst n t u) (Subst n t' u') = Subst n (resid t t') (resid u u') := by
  induction u, u' using resid.induct generalizing n <;> simp_all [Subst, resid, Subst_ne_nil]
  · split_ifs <;> simp [resid, Raise_resid]
  all_goals exact (substitution_lemma ht (by simp_all) _ n).symm

/-! ### Arrows, sources and targets -/

/-- Arrows: terms without `nil`. -/
def Arr : MT → Prop
  | nil => False
  | var _ => True
  | lam t => Arr t
  | app t u => Arr t ∧ Arr u
  | beta t u => Arr t ∧ Arr u

/-- Source: erase all marks. -/
def Src : MT → MT
  | nil => nil
  | var i => var i
  | lam t => lam (Src t)
  | app t u => app (Src t) (Src u)
  | beta t u => app (lam (Src t)) (Src u)

/-- Target: contract all marked redexes. -/
def Trg : MT → MT
  | nil => nil
  | var i => var i
  | lam t => lam (Trg t)
  | app t u => app (Trg t) (Trg u)
  | beta t u => Subst 0 (Trg u) (Trg t)

theorem Arr_ne_nil {t : MT} (h : Arr t) : t ≠ nil := by
  rintro rfl; exact h

theorem Arr_Raise (t : MT) : ∀ d n, Arr (Raise d n t) ↔ Arr t := by
  induction t with
  | nil => intros; rfl
  | var i => intro d n; simp [Arr]
  | lam t ih => intro d n; simp [Arr, ih]
  | app t u iht ihu => intro d n; simp [Arr, iht, ihu]
  | beta t u iht ihu => intro d n; simp [Arr, iht, ihu]

theorem Arr_Subst {v : MT} (hv : Arr v) (t : MT) : ∀ n, Arr t → Arr (Subst n v t) := by
  induction t with
  | nil => intro n h; exact h.elim
  | var i =>
    intro n _
    simp only [Subst]
    split_ifs
    · trivial
    · exact (Arr_Raise v 0 n).2 hv
    · trivial
  | lam t ih => intro n h; exact ih (n + 1) h
  | app t u iht ihu => intro n h; exact ⟨iht n h.1, ihu n h.2⟩
  | beta t u iht ihu => intro n h; exact ⟨iht (n + 1) h.1, ihu n h.2⟩

theorem Src_Raise (t : MT) : ∀ d n, Src (Raise d n t) = Raise d n (Src t) := by
  induction t with
  | nil => intros; rfl
  | var i => intro d n; simp [Src]
  | lam t ih => intro d n; simp [Src, ih]
  | app t u iht ihu => intro d n; simp [Src, iht, ihu]
  | beta t u iht ihu => intro d n; simp [Src, iht, ihu]

theorem Src_Subst {v : MT} (t : MT) : ∀ d, Src (Subst d v t) = Subst d (Src v) (Src t) := by
  induction t with
  | nil => intros; rfl
  | var i =>
    intro d
    simp only [Subst, Src]
    split_ifs <;> simp [Src, Src_Raise]
  | lam t ih => intro d; simp [Subst, Src, ih]
  | app t u iht ihu => intro d; simp [Subst, Src, iht, ihu]
  | beta t u iht ihu => intro d; simp [Subst, Src, iht, ihu]

theorem Arr_resid {t u : MT} (h : resid t u ≠ nil) : Arr (resid t u) := by
  fun_induction resid t u <;> simp_all [Arr, Arr_Subst]

/-- The leftover case of `resid.induct`: terms of non-matching shapes are not coinitial. -/
theorem not_coinitial_of_shape {t x : MT}
    (h1 : ∀ i j, t = var i → x = var j → False) (h2 : ∀ a b, t = lam a → x = lam b → False)
    (h3 : ∀ a b c d, t = app a b → x = app c d → False)
    (h4 : ∀ a b c d, t = beta a b → x = beta c d → False)
    (h5 : ∀ a b c d, t = app (lam a) b → x = beta c d → False)
    (h6 : ∀ a b c d, t = beta a b → x = app (lam c) d → False)
    (ht : Arr t) (hx : Arr x) (he : Src t = Src x) : False := by
  cases t <;> cases x <;> simp only [Arr, Src, reduceCtorEq, app.injEq, lam.injEq] at ht hx he
  all_goals first
    | exact h1 _ _ rfl rfl | exact h2 _ _ rfl rfl | exact h3 _ _ _ _ rfl rfl
    | exact h4 _ _ _ _ rfl rfl | skip
  case app.beta a b c d =>
    cases a <;> simp only [Src, reduceCtorEq, false_and] at he
    exact h5 _ _ _ _ rfl rfl
  case beta.app a b c d =>
    cases c <;> simp only [Src, reduceCtorEq, false_and] at he
    exact h6 _ _ _ _ rfl rfl

theorem Con_iff {t u : MT} : resid t u ≠ nil ↔ Arr t ∧ Arr u ∧ Src t = Src u := by
  constructor
  · intro h
    fun_induction resid t u <;> simp_all [Arr, Src]
  · rintro ⟨ht, hu, he⟩
    fun_induction resid t u <;> simp_all [Arr, Src, resid, Subst_ne_nil]
    exact not_coinitial_of_shape ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ht hu he

theorem Arr_Trg (t : MT) : Arr t → Arr (Trg t) := by
  induction t with
  | nil => intro h; exact h.elim
  | var i => intro _; trivial
  | lam t ih => intro h; exact ih h
  | app t u iht ihu => intro h; exact ⟨iht h.1, ihu h.2⟩
  | beta t u iht ihu => intro h; exact Arr_Subst (ihu h.2) _ 0 (iht h.1)

theorem resid_self (t : MT) : Arr t → resid t t = Trg t := by
  induction t with
  | nil => intro h; exact h.elim
  | var i => intro _; simp [resid, Trg]
  | lam t ih => intro h; simp [resid, Trg, ih h, Arr_ne_nil (Arr_Trg t h)]
  | app t u iht ihu =>
    intro h
    simp [resid, Trg, iht h.1, ihu h.2, Arr_ne_nil (Arr_Trg t h.1), Arr_ne_nil (Arr_Trg u h.2)]
  | beta t u iht ihu =>
    intro h
    simp [resid, Trg, iht h.1, ihu h.2, Arr_ne_nil (Arr_Trg t h.1), Arr_ne_nil (Arr_Trg u h.2)]

theorem Src_resid {t u : MT} (h : resid t u ≠ nil) : Src (resid t u) = Trg u := by
  fun_induction resid t u <;> simp_all [Src, Trg, Src_Subst]

/-- Residuals of coinitial terms along the same term are consistent. -/
theorem Con_resid_resid {t u v : MT} (h1 : resid t v ≠ nil) (h2 : resid u v ≠ nil) :
    resid (resid t v) (resid u v) ≠ nil :=
  Con_iff.2 ⟨Arr_resid h1, Arr_resid h2, by rw [Src_resid h1, Src_resid h2]⟩

theorem resid_ne_nil_parts {a b : MT} (h : resid a b ≠ nil) : a ≠ nil ∧ b ≠ nil :=
  ⟨fun e => by subst e; simp at h, fun e => by subst e; simp at h⟩

set_option maxHeartbeats 4000000 in
/-- **Lévy's cube lemma** for marked terms. -/
theorem Cube_aux : ∀ (s : ℕ) (t u v : MT), size t ≤ s → resid (resid v t) (resid u t) ≠ nil →
    resid (resid v t) (resid u t) = resid (resid v u) (resid t u) := by
  intro s
  induction s with
  | zero => intro t u v hs H; cases t <;> simp_all [size]
  | succ s ih =>
    intro t u v hs H
    have hv : resid v t ≠ nil := (resid_ne_nil_parts H).1
    have hu : resid u t ≠ nil := (resid_ne_nil_parts H).2
    -- the generic induction step for a pair of components
    have step : ∀ {t1 u1 v1 : MT}, size t1 ≤ s → resid v1 t1 ≠ nil → resid u1 t1 ≠ nil →
        resid (resid v1 t1) (resid u1 t1) = resid (resid v1 u1) (resid t1 u1) ∧
        resid (resid v1 t1) (resid u1 t1) ≠ nil ∧
        resid (resid v1 u1) (resid t1 u1) ≠ nil ∧ resid v1 u1 ≠ nil ∧ resid t1 u1 ≠ nil := by
      intro t1 u1 v1 hs1 h1 h2
      have hc := Con_resid_resid h1 h2
      have E := ih t1 u1 v1 hs1 hc
      have hR : resid (resid v1 u1) (resid t1 u1) ≠ nil := E ▸ hc
      exact ⟨E, hc, hR, (resid_ne_nil_parts hR).1, (resid_ne_nil_parts hR).2⟩
    cases t with
    | nil => simp at hv
    | var i =>
      cases v with
      | var j =>
        cases u with
        | var k => by_cases hij : j = i <;> by_cases hki : k = i <;> simp_all [resid]
        | _ => simp [resid] at hu
      | _ => simp [resid] at hv
    | lam t1 =>
      cases v with
      | lam v1 =>
        cases u with
        | lam u1 =>
          have hv1 : resid v1 t1 ≠ nil := by intro e; simp [resid, e] at hv
          have hu1 : resid u1 t1 ≠ nil := by intro e; simp [resid, e] at hu
          obtain ⟨E, hc, hR, h3, h4⟩ := step (by simp [size] at hs; omega) hv1 hu1
          simp only [resid, hv1, hu1, h3, h4, hc, hR, ite_false]
          rw [E]
        | _ => simp [resid] at hu
      | _ => simp [resid] at hv
    | app t1 t2 =>
      cases v with
      | app v1 v2 =>
        cases u with
        | app u1 u2 =>
          have hv1 : resid v1 t1 ≠ nil := by intro e; simp [resid, e] at hv
          have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
          have hu1 : resid u1 t1 ≠ nil := by intro e; simp [resid, e] at hu
          have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
          obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
          obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
          simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hc1, hc2, hR1, hR2, or_self,
            ite_false, reduceCtorEq, or_false, false_or]
          rw [E1, E2]
        | beta u1 u2 =>
          cases t1 with
          | lam t11 =>
            cases v1 with
            | lam v11 =>
              have hv1 : resid v11 t11 ≠ nil := by intro e; simp [resid, e] at hv
              have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
              have hu1 : resid u1 t11 ≠ nil := by intro e; simp [resid, e] at hu
              have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
              obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
              obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
              simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hc1, hc2, hR1, hR2, or_self,
                ite_false, reduceCtorEq, or_false, false_or]
              rw [resid_Subst hR2 hR1, E1, E2]
            | _ => simp [resid] at hv
          | _ => simp [resid] at hu
        | _ => simp [resid] at hu
      | beta v1 v2 =>
        cases t1 with
        | lam t11 =>
          cases u with
          | beta u1 u2 =>
            have hv1 : resid v1 t11 ≠ nil := by intro e; simp [resid, e] at hv
            have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
            have hu1 : resid u1 t11 ≠ nil := by intro e; simp [resid, e] at hu
            have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
            obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
            obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
            simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hc1, hc2, hR1, hR2, or_self,
              ite_false, reduceCtorEq, or_false, false_or]
            rw [resid_Subst hR2 hR1, E1, E2]
          | app u1 u2 =>
            cases u1 with
            | lam u11 =>
              have hv1 : resid v1 t11 ≠ nil := by intro e; simp [resid, e] at hv
              have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
              have hu1 : resid u11 t11 ≠ nil := by intro e; simp [resid, e] at hu
              have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
              obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
              obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
              simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hc1, hc2, hR1, hR2, or_self,
                ite_false, reduceCtorEq, or_false, false_or]
              rw [E1, E2]
            | _ => simp [resid] at hu
          | _ => simp [resid] at hu
        | _ => simp [resid] at hv
      | _ => simp [resid] at hv
    | beta t1 t2 =>
      cases v with
      | beta v1 v2 =>
        cases u with
        | beta u1 u2 =>
          have hv1 : resid v1 t1 ≠ nil := by intro e; simp [resid, e] at hv
          have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
          have hu1 : resid u1 t1 ≠ nil := by intro e; simp [resid, e] at hu
          have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
          obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
          obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
          simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, or_self, ite_false, reduceCtorEq, or_false, false_or]
          rw [resid_Subst hc2 hc1, resid_Subst hR2 hR1, E1, E2]
        | app u1 u2 =>
          cases u1 with
          | lam u11 =>
            have hv1 : resid v1 t1 ≠ nil := by intro e; simp [resid, e] at hv
            have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
            have hu1 : resid u11 t1 ≠ nil := by intro e; simp [resid, e] at hu
            have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
            obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
            obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
            simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hR1, hR2, or_self, ite_false, reduceCtorEq, or_false, false_or]
            rw [resid_Subst hc2 hc1, E1, E2]
          | _ => simp [resid] at hu
        | _ => simp [resid] at hu
      | app v1 v2 =>
        cases v1 with
        | lam v11 =>
          cases u with
          | beta u1 u2 =>
            have hv1 : resid v11 t1 ≠ nil := by intro e; simp [resid, e] at hv
            have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
            have hu1 : resid u1 t1 ≠ nil := by intro e; simp [resid, e] at hu
            have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
            obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
            obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
            simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, or_self, ite_false, reduceCtorEq, or_false, false_or]
            rw [resid_Subst hc2 hc1, resid_Subst hR2 hR1, E1, E2]
          | app u1 u2 =>
            cases u1 with
            | lam u11 =>
              have hv1 : resid v11 t1 ≠ nil := by intro e; simp [resid, e] at hv
              have hv2 : resid v2 t2 ≠ nil := by intro e; simp [resid, e] at hv
              have hu1 : resid u11 t1 ≠ nil := by intro e; simp [resid, e] at hu
              have hu2 : resid u2 t2 ≠ nil := by intro e; simp [resid, e] at hu
              obtain ⟨E1, hc1, hR1, a1, b1⟩ := step (by simp [size] at hs; omega) hv1 hu1
              obtain ⟨E2, hc2, hR2, a2, b2⟩ := step (by simp [size] at hs; omega) hv2 hu2
              simp only [resid, hv1, hv2, hu1, hu2, a1, a2, b1, b2, hR1, hR2, or_self, ite_false, reduceCtorEq, or_false, false_or]
              rw [resid_Subst hc2 hc1, E1, E2]
            | _ => simp [resid] at hu
          | _ => simp [resid] at hu
        | _ => simp [resid] at hv
      | _ => simp [resid] at hv

theorem Cube {t u v : MT} (H : resid (resid v t) (resid u t) ≠ nil) :
    resid (resid v t) (resid u t) = resid (resid v u) (resid t u) :=
  Cube_aux _ t u v le_rfl H

theorem resid_Src (t : MT) : Arr t → resid t (Src t) = t := by
  induction t with
  | nil => intro h; exact h.elim
  | var i => intro _; simp [resid, Src]
  | lam t ih => intro h; simp [resid, Src, ih h, Arr_ne_nil (show Arr t from h)]
  | app t u iht ihu =>
    intro h
    simp [resid, Src, iht h.1, ihu h.2, Arr_ne_nil h.1, Arr_ne_nil h.2]
  | beta t u iht ihu =>
    intro h
    simp [resid, Src, iht h.1, ihu h.2, Arr_ne_nil h.1, Arr_ne_nil h.2]

/-! ### de Vrijer's measure for finite developments -/

/-- Multiplicity of the variable `x` (the maximal number of copies along developments). -/
def mtp : ℕ → MT → ℕ
  | _, nil => 0
  | x, var z => if z = x then 1 else 0
  | x, lam t => mtp (x + 1) t
  | x, app t u => mtp x t + mtp x u
  | x, beta t u => mtp (x + 1) t + mtp x u * max 1 (mtp 0 t)

/-- Height: a bound on the length of developments. -/
def hgt : MT → ℕ
  | nil => 0
  | var _ => 0
  | lam t => hgt t
  | app t u => hgt t + hgt u
  | beta t u => hgt t + hgt u * max 1 (mtp 0 t) + 1

theorem mtp_Raise_lt (t : MT) : ∀ x d k, x < d → mtp x (Raise d k t) = mtp x t := by
  induction t with
  | nil => intros; rfl
  | var z => intro x d k h; simp only [Raise_var', mtp]; split_ifs <;> omega
  | lam t ih => intro x d k h; simp [mtp, ih (x + 1) (d + 1) k (by omega)]
  | app t u iht ihu => intro x d k h; simp [mtp, iht x d k h, ihu x d k h]
  | beta t u iht ihu =>
    intro x d k h
    simp [mtp, iht (x + 1) (d + 1) k (by omega), ihu x d k h, iht 0 (d + 1) k (by omega)]

theorem mtp_Raise (t : MT) : ∀ x d l k, l ≤ d → mtp (x + d + k) (Raise l k t) = mtp (x + d) t := by
  induction t with
  | nil => intros; rfl
  | var z => intro x d l k h; simp only [Raise_var', mtp]; split_ifs <;> omega
  | lam t ih =>
    intro x d l k h
    simp only [Raise, mtp]
    have := ih x (d + 1) (l + 1) k (by omega)
    rw [show x + (d + 1) + k = x + d + k + 1 by omega, show x + (d + 1) = x + d + 1 by omega] at this
    exact this
  | app t u iht ihu => intro x d l k h; simp [mtp, iht x d l k h, ihu x d l k h]
  | beta t u iht ihu =>
    intro x d l k h
    simp only [Raise, mtp]
    have h1 := iht x (d + 1) (l + 1) k (by omega)
    rw [show x + (d + 1) + k = x + d + k + 1 by omega, show x + (d + 1) = x + d + 1 by omega] at h1
    rw [h1, ihu x d l k h, mtp_Raise_lt t 0 (l + 1) k (by omega)]

theorem mtp_Raise_zero (u : MT) (k : ℕ) : mtp k (Raise 0 k u) = mtp 0 u := by
  have := mtp_Raise u 0 0 0 k (le_refl _)
  simpa using this

theorem mtp_Raise_self (t : MT) : ∀ l k, mtp l (Raise l (k + 1) t) = 0 := by
  induction t with
  | nil => intros; rfl
  | var z => intro l k; simp only [Raise_var', mtp]; split_ifs <;> omega
  | lam t ih => intro l k; simp [mtp, ih (l + 1) k]
  | app t u iht ihu => intro l k; simp [mtp, iht l k, ihu l k]
  | beta t u iht ihu => intro l k; simp [mtp, iht (l + 1) k, ihu l k]

theorem mtp_Subst_cancel (u t : MT) : ∀ k d, mtp k (Subst (d + 1 + k) u t) = mtp k t := by
  induction t with
  | nil => intros; rfl
  | var z =>
    intro k d
    simp only [Subst]
    split_ifs with h1 h2
    · simp only [mtp]; split_ifs <;> omega
    · subst h2
      have e : Raise 0 (d + 1 + k) u = Raise k (d + 1) (Raise 0 k u) := by
        have := Raise_plus u 0 k (d + 1); simpa [Nat.add_comm] using this
      rw [e, mtp_Raise_self]
      simp only [mtp]; split_ifs <;> omega
    · rfl
  | lam t ih =>
    intro k d
    simp only [Subst, mtp]
    have := ih (k + 1) d
    rwa [show d + 1 + (k + 1) = d + 1 + k + 1 by omega] at this
  | app t1 t2 ih1 ih2 => intro k d; simp [Subst, mtp, ih1 k d, ih2 k d]
  | beta t1 t2 ih1 ih2 =>
    intro k d
    simp only [Subst, mtp]
    have h1 := ih1 (k + 1) d
    rw [show d + 1 + (k + 1) = d + 1 + k + 1 by omega] at h1
    have h0 := ih1 0 (d + k + 1)
    rw [show d + k + 1 + 1 + 0 = d + 1 + k + 1 by omega] at h0
    rw [h1, ih2 k d, h0]

theorem mtp_Subst' (u t : MT) : ∀ x d, mtp (x + d + 1) (Subst d u t) =
    mtp (x + d + 2) t + mtp (x + 1) u * mtp d t := by
  induction t with
  | nil => intros; simp [Subst, mtp]
  | var z =>
    intro x d
    simp only [Subst]
    split_ifs with h1 h2
    · simp only [mtp]; split_ifs <;> first | omega | simp_all <;> omega
    · subst h2
      have := mtp_Raise u (x + 1) 0 0 d (le_refl _)
      simp only [Nat.add_zero] at this
      rw [show x + d + 1 = x + 1 + d by omega, this]
      simp [mtp]; omega
    · simp only [mtp]; split_ifs <;> first | omega | simp_all <;> omega
  | lam t ih =>
    intro x d
    simp only [Subst, mtp]
    have := ih x (d + 1)
    rw [show x + (d + 1) + 1 = x + d + 1 + 1 by omega,
      show x + (d + 1) + 2 = x + d + 2 + 1 by omega] at this
    exact this
  | app t1 t2 ih1 ih2 => intro x d; simp [Subst, mtp, ih1 x d, ih2 x d]; ring
  | beta t1 t2 ih1 ih2 =>
    intro x d
    simp only [Subst, mtp]
    have h1 := ih1 x (d + 1)
    rw [show x + (d + 1) + 1 = x + d + 1 + 1 by omega,
      show x + (d + 1) + 2 = x + d + 2 + 1 by omega] at h1
    have h0 := mtp_Subst_cancel u t1 0 d
    simp only [Nat.add_zero] at h0
    rw [h1, ih2 x d, h0]
    ring

theorem mtp_Subst_self (u t : MT) : ∀ k, mtp k (Subst k u t) = mtp (k + 1) t + mtp 0 u * mtp k t := by
  induction t with
  | nil => intros; simp [Subst, mtp]
  | var z =>
    intro k
    simp only [Subst]
    split_ifs with h1 h2
    · simp only [mtp]; split_ifs <;> first | omega | simp_all <;> omega
    · subst h2; rw [mtp_Raise_zero]; simp [mtp]
    · simp only [mtp]; split_ifs <;> first | omega | simp_all <;> omega
  | lam t ih => intro k; simp only [Subst, mtp]; rw [ih (k + 1)]
  | app t1 t2 ih1 ih2 => intro k; simp [Subst, mtp, ih1 k, ih2 k]; ring
  | beta t1 t2 ih1 ih2 =>
    intro k
    simp only [Subst, mtp]
    have h0 := mtp_Subst_cancel u t1 0 k
    simp only [Nat.add_zero] at h0
    rw [ih1 (k + 1), ih2 k, h0]
    ring

theorem mtp0_subst_le (u t : MT) : mtp 0 (Subst 0 u t) ≤ mtp 1 t + mtp 0 u * max 1 (mtp 0 t) := by
  rw [mtp_Subst_self]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (le_max_right _ _)) _

theorem hgt_Raise (t : MT) : ∀ l k, hgt (Raise l k t) = hgt t := by
  induction t with
  | nil => intros; rfl
  | var z => intro l k; simp [hgt]
  | lam t ih => intro l k; simp [hgt, ih]
  | app t u iht ihu => intro l k; simp [hgt, iht, ihu]
  | beta t u iht ihu => intro l k; simp [hgt, iht, ihu, mtp_Raise_lt t 0 (l + 1) k (by omega)]

theorem hgt_Subst (u t : MT) : ∀ k, hgt (Subst k u t) = hgt t + hgt u * mtp k t := by
  induction t with
  | nil => intros; simp [Subst, hgt, mtp]
  | var z =>
    intro k
    simp only [Subst]
    split_ifs with h1 h2
    · simp [hgt, mtp]; omega
    · subst h2; simp [hgt, mtp, hgt_Raise]
    · simp [hgt, mtp]; omega
  | lam t ih => intro k; simp only [Subst, hgt, mtp]; rw [ih (k + 1)]
  | app t1 t2 ih1 ih2 => intro k; simp [Subst, hgt, mtp, ih1 k, ih2 k]; ring
  | beta t1 t2 ih1 ih2 =>
    intro k
    simp only [Subst, hgt, mtp]
    have h0 := mtp_Subst_cancel u t1 0 k
    simp only [Nat.add_zero] at h0
    rw [ih1 (k + 1), ih2 k, h0]
    ring

end MT

end CiruelosLic.Marked

namespace CiruelosLic

/-! ## Chapter 0 (support): position and substitution lemmas for λ-terms

Shared lemmas used to discharge the orthogonality axioms of `lambdaRS`
(see `CiruelosLic.Chapter0`). -/

section LambdaLemmas

namespace LTerm

@[simp] theorem subAt_nil (t : LTerm) : subAt t [] = some t := by cases t <;> rfl

theorem subAt_append (t : LTerm) (q r : Pos) :
    subAt t (q ++ r) = (subAt t q).bind (fun v => subAt v r) := by
  induction q generalizing t with
  | nil => simp
  | cons i q ih =>
    rcases t with _ | t | ⟨t, s⟩ <;> rcases i with _ | _ | i <;> simp [subAt, ih]

theorem isRedexAt_iff (t : LTerm) (q : Pos) :
    isRedexAt t q = true ↔ ∃ u s, subAt t q = some (app (lam u) s) := by
  unfold isRedexAt
  cases h : subAt t q with
  | none => simp
  | some v => rcases v with _ | _ | ⟨_ | _ | _, _⟩ <;> simp [isRedex]

theorem isRedexAt_append (t : LTerm) (q r : Pos) :
    isRedexAt t (q ++ r) = true ↔ ∃ v, subAt t q = some v ∧ isRedexAt v r = true := by
  unfold isRedexAt
  rw [subAt_append]
  cases subAt t q <;> simp

@[simp] theorem isRedexAt_var (n : ℕ) (p : Pos) : isRedexAt (var n) p = false := by
  cases p <;> simp [isRedexAt, subAt, isRedex]

@[simp] theorem isRedexAt_lam_nil (t : LTerm) : isRedexAt (lam t) [] = false := by
  simp [isRedexAt, isRedex]

@[simp] theorem isRedexAt_lam_zero (t : LTerm) (p : Pos) :
    isRedexAt (lam t) (0 :: p) = isRedexAt t p := by simp [isRedexAt, subAt]

@[simp] theorem isRedexAt_lam_succ (t : LTerm) (i : ℕ) (p : Pos) :
    isRedexAt (lam t) ((i + 1) :: p) = false := by simp [isRedexAt, subAt]

@[simp] theorem isRedexAt_app_zero (t s : LTerm) (p : Pos) :
    isRedexAt (app t s) (0 :: p) = isRedexAt t p := by simp [isRedexAt, subAt]

@[simp] theorem isRedexAt_app_one (t s : LTerm) (p : Pos) :
    isRedexAt (app t s) (1 :: p) = isRedexAt s p := by simp [isRedexAt, subAt]

@[simp] theorem isRedexAt_app_succ_succ (t s : LTerm) (i : ℕ) (p : Pos) :
    isRedexAt (app t s) ((i + 2) :: p) = false := by simp [isRedexAt, subAt]

/-- Substitution preserves the redexes of the substituted-into term. -/
theorem isRedexAt_substAt : ∀ (u : LTerm) (k : ℕ) (s : LTerm) (r : Pos),
    isRedexAt u r = true → isRedexAt (substAt k s u) r = true
  | var n, k, s, r, h => by simp at h
  | lam t, k, s, [], h => by simp at h
  | lam t, k, s, 0 :: r, h => by
      simpa [substAt] using isRedexAt_substAt t (k + 1) s r (by simpa using h)
  | lam t, k, s, (i + 1) :: r, h => by simp at h
  | app t u, k, s, [], h => by
      rcases t with _ | _ | _ <;> simp_all [isRedexAt, subAt, isRedex, substAt]
  | app t u, k, s, 0 :: r, h => by
      simpa [substAt] using isRedexAt_substAt t k s r (by simpa using h)
  | app t u, k, s, 1 :: r, h => by
      simpa [substAt] using isRedexAt_substAt u k s r (by simpa using h)
  | app t u, k, s, (i + 2) :: r, h => by simp at h

/-- Shifting preserves redexes. -/
theorem isRedexAt_shift : ∀ (u : LTerm) (d c : ℕ) (r : Pos),
    isRedexAt u r = true → isRedexAt (shift d c u) r = true
  | var n, d, c, r, h => by simp at h
  | lam t, d, c, [], h => by simp at h
  | lam t, d, c, 0 :: r, h => by
      simpa [shift] using isRedexAt_shift t d (c + 1) r (by simpa using h)
  | lam t, d, c, (i + 1) :: r, h => by simp at h
  | app t u, d, c, [], h => by
      rcases t with _ | _ | _ <;> simp_all [isRedexAt, subAt, isRedex, shift]
  | app t u, d, c, 0 :: r, h => by
      simpa [shift] using isRedexAt_shift t d c r (by simpa using h)
  | app t u, d, c, 1 :: r, h => by
      simpa [shift] using isRedexAt_shift u d c r (by simpa using h)
  | app t u, d, c, (i + 2) :: r, h => by simp at h

/-- Each occurrence of the substituted variable carries a shifted copy of the argument. -/
theorem occs_subAt : ∀ (u : LTerm) (k : ℕ) (s : LTerm) (o : Pos), o ∈ occs u k →
    ∃ d, subAt (substAt k s u) o = some (shift d 0 s)
  | var n, k, s, o, h => by
      simp only [occs] at h
      split_ifs at h with hn
      · simp at h
        subst h hn
        exact ⟨n, by simp [substAt]⟩
      · simp at h
  | lam t, k, s, o, h => by
      simp only [occs, List.mem_map] at h
      obtain ⟨o', ho', rfl⟩ := h
      obtain ⟨d, hd⟩ := occs_subAt t (k + 1) s o' ho'
      exact ⟨d, by simpa [substAt, subAt] using hd⟩
  | app t u, k, s, o, h => by
      simp only [occs, List.mem_append, List.mem_map] at h
      rcases h with ⟨o', ho', rfl⟩ | ⟨o', ho', rfl⟩
      · obtain ⟨d, hd⟩ := occs_subAt t k s o' ho'
        exact ⟨d, by simpa [substAt, subAt] using hd⟩
      · obtain ⟨d, hd⟩ := occs_subAt u k s o' ho'
        exact ⟨d, by simpa [substAt, subAt] using hd⟩

/-- Contracting the redex at `q` leaves the contractum at `q`. -/
theorem subAt_contractAt : ∀ (t : LTerm) (q : Pos) (u s : LTerm),
    subAt t q = some (app (lam u) s) → subAt (contractAt t q) q = some (substAt 0 s u)
  | t, [], u, s, h => by
      simp at h; subst h; simp [contractAt]
  | var n, i :: q, u, s, h => by simp [subAt] at h
  | lam t, 0 :: q, u, s, h => by
      simpa [contractAt, subAt] using subAt_contractAt t q u s (by simpa [subAt] using h)
  | lam t, (i + 1) :: q, u, s, h => by simp [subAt] at h
  | app t t', 0 :: q, u, s, h => by
      simpa [contractAt, subAt] using subAt_contractAt t q u s (by simpa [subAt] using h)
  | app t t', 1 :: q, u, s, h => by
      simpa [contractAt, subAt] using subAt_contractAt t' q u s (by simpa [subAt] using h)
  | app t t', (i + 2) :: q, u, s, h => by simp [subAt] at h

/-- A redex not below the contracted one survives its contraction. -/
theorem isRedexAt_contractAt_of_not_prefix : ∀ (t : LTerm) (p q : Pos),
    isRedexAt t p = true → isRedexAt t q = true → ¬ q <+: p →
    isRedexAt (contractAt t q) p = true
  | var n, p, q, hp, hq, h => by simp at hp
  | lam t, p, [], hp, hq, h => by simp at hq
  | lam t, [], q, hp, hq, h => by simp at hp
  | lam t, 0 :: p, 0 :: q, hp, hq, h => by
      simp only [contractAt, isRedexAt_lam_zero] at hp hq ⊢
      exact isRedexAt_contractAt_of_not_prefix t p q hp hq (by simpa using h)
  | lam t, (i + 1) :: p, _, hp, hq, h => by simp at hp
  | lam t, _, (i + 1) :: q, hp, hq, h => by simp at hq
  | app t s, p, [], hp, hq, h => absurd (List.nil_prefix) h
  | app t s, [], 0 :: q, hp, hq, h => by
      have hq' : isRedexAt t q = true := by simpa using hq
      rcases t with _ | t | _
      · simp at hq'
      · rcases q with _ | ⟨_ | _, q⟩ <;> simp_all [contractAt, isRedexAt, subAt, isRedex]
      · simp_all [isRedexAt, subAt, isRedex]
  | app t s, [], 1 :: q, hp, hq, h => by
      simp only [contractAt]
      rcases t with _ | _ | _ <;> simp_all [isRedexAt, subAt, isRedex]
  | app t s, 0 :: p, 0 :: q, hp, hq, h => by
      simp only [contractAt, isRedexAt_app_zero] at hp hq ⊢
      exact isRedexAt_contractAt_of_not_prefix t p q hp hq (by simpa using h)
  | app t s, 0 :: p, 1 :: q, hp, hq, h => by simpa [contractAt] using hp
  | app t s, 1 :: p, 0 :: q, hp, hq, h => by simpa [contractAt] using hp
  | app t s, 1 :: p, 1 :: q, hp, hq, h => by
      simp only [contractAt, isRedexAt_app_one] at hp hq ⊢
      exact isRedexAt_contractAt_of_not_prefix s p q hp hq (by simpa using h)
  | app t s, (i + 2) :: p, _, hp, hq, h => by simp at hp
  | app t s, _, (i + 2) :: q, hp, hq, h => by simp at hq

/-- **Residuals are redexes of the contractum.** -/
theorem residuals_isRedexAt (t : LTerm) (q p : Pos)
    (hq : isRedexAt t q = true) (hp : isRedexAt t p = true) :
    ∀ c ∈ residuals t q p, isRedexAt (contractAt t q) c = true := by
  intro c hc
  by_cases hpq : p = q
  · simp [residuals, hpq] at hc
  by_cases hpre : q <+: p
  · obtain ⟨w, rfl⟩ := hpre
    obtain ⟨u, s, hsub⟩ := (isRedexAt_iff t q).1 hq
    obtain ⟨v, hv, hpw⟩ := (isRedexAt_append t q w).1 hp
    rw [hsub] at hv
    obtain rfl := Option.some.inj hv
    simp [residuals, hpq, hsub] at hc
    rcases w with _ | ⟨_ | _ | i, w⟩
    · exact absurd (List.append_nil q) hpq
    · rcases w with _ | ⟨_ | _ | j, r⟩
      · simp at hc
      · simp at hc hpw
        rw [hc]
        exact (isRedexAt_append _ q r).2
          ⟨substAt 0 s u, subAt_contractAt t q u s hsub, isRedexAt_substAt u 0 s r hpw⟩
      · simp at hpw
      · simp at hpw
    · simp at hc hpw
      obtain ⟨o, ho, rfl⟩ := hc
      obtain ⟨d, hd⟩ := occs_subAt u 0 s o ho
      refine (isRedexAt_append _ q _).2 ⟨substAt 0 s u, subAt_contractAt t q u s hsub, ?_⟩
      exact (isRedexAt_append _ o w).2 ⟨shift d 0 s, hd, isRedexAt_shift s d 0 w hpw⟩
    · simp at hc
  · simp [residuals, hpq, hpre] at hc
    rw [hc]
    exact isRedexAt_contractAt_of_not_prefix t p q hp hq hpre

/-! ### Term contexts

A context `C` with a hole at child `i` lifts positions, contractions, residuals and
developments from the subterm to `C t`. -/

/-- `C` is a one-hole context whose hole sits below child `i`. -/
structure Ctx (C : LTerm → LTerm) (i : ℕ) : Prop where
  sub : ∀ t p, subAt (C t) (i :: p) = subAt t p
  con : ∀ t p, contractAt (C t) (i :: p) = C (contractAt t p)

theorem ctx_lam : Ctx lam 0 := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
theorem ctx_appL (s : LTerm) : Ctx (fun t => app t s) 0 :=
  ⟨fun _ _ => rfl, fun t p => by simp [contractAt]⟩
theorem ctx_appR (t : LTerm) : Ctx (fun s => app t s) 1 :=
  ⟨fun _ _ => rfl, fun t p => by simp [contractAt]⟩

namespace Ctx
variable {C : LTerm → LTerm} {i : ℕ} (hC : Ctx C i)
include hC

theorem isRedexAt (t : LTerm) (p : Pos) :
    LTerm.isRedexAt (C t) (i :: p) = LTerm.isRedexAt t p := by
  simp [LTerm.isRedexAt, hC.sub]

theorem residuals_in (t : LTerm) (q p : Pos) :
    residuals (C t) (i :: q) (i :: p) = (residuals t q p).image (i :: ·) := by
  by_cases hpq : p = q
  · subst hpq; simp [residuals]
  by_cases hpre : q <+: p
  · have hpre' : (i :: q) <+: (i :: p) := by simpa using hpre
    have hne : ¬ i :: p = i :: q := by simpa using hpq
    simp only [residuals, hne, hpq, hpre, hpre', hC.sub, ite_true, ite_false, List.length_cons,
      List.drop_succ_cons]
    generalize subAt t q = x
    generalize p.drop q.length = w
    rcases x with _ | _ | _ | ⟨_ | _ | _, _⟩ <;> try simp
    rcases w with _ | ⟨_ | _ | _, _ | ⟨_ | _ | _, _⟩⟩ <;> simp <;> (ext; simp)
  · have hpre' : ¬ (i :: q) <+: (i :: p) := by simpa using hpre
    have hne : ¬ i :: p = i :: q := by simpa using hpq
    simp [residuals, hne, hpq, hpre, hpre']

omit hC in
theorem residuals_out (t : LTerm) (q p : Pos) (hp : ∀ p', p ≠ i :: p') :
    residuals (C t) (i :: q) p = {p} := by
  have h1 : p ≠ i :: q := hp q
  have h2 : ¬ (i :: q) <+: p := by
    intro h; obtain ⟨w, rfl⟩ := h; exact hp _ rfl
  simp [residuals, h1, h2]

theorem tgt_map (t : LTerm) (σ : List Pos) :
    lambdaRS.tgt (C t) (σ.map (i :: ·)) = C (lambdaRS.tgt t σ) := by
  induction σ generalizing t with
  | nil => rfl
  | cons a σ ih =>
    simp only [List.map_cons]
    show lambdaRS.tgt (LTerm.contractAt (C t) (i :: a)) _ = _
    rw [hC.con]; exact ih _

theorem resSet_in (A : Finset Pos) (t : LTerm) (a : Pos) :
    lambdaRS.resSet (C t) (A.image (i :: ·)) (i :: a) =
      (lambdaRS.resSet t A a).image (i :: ·) := by
  ext c
  simp only [ResidualSystem.resSet, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨m, ⟨x, hx, rfl⟩, hc⟩
    have : c ∈ residuals (C t) (i :: a) (i :: x) := hc
    rw [hC.residuals_in, Finset.mem_image] at this
    obtain ⟨c', hc', rfl⟩ := this
    exact ⟨c', ⟨x, hx, hc'⟩, rfl⟩
  · rintro ⟨c', ⟨m, hm, hc'⟩, rfl⟩
    refine ⟨i :: m, ⟨m, hm, rfl⟩, ?_⟩
    show _ ∈ residuals (C t) (i :: a) (i :: m)
    rw [hC.residuals_in]; exact Finset.mem_image_of_mem _ hc'

omit hC in
theorem resSet_out (E : Finset Pos) (hE : ∀ p ∈ E, ∀ p', p ≠ i :: p') (t : LTerm) (a : Pos) :
    lambdaRS.resSet (C t) E (i :: a) = E := by
  ext c
  simp only [ResidualSystem.resSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨m, hm, hc⟩
    have : c ∈ residuals (C t) (i :: a) m := hc
    rw [Ctx.residuals_out (C := C) (i := i) t a m (hE m hm)] at this
    simpa [(Finset.mem_singleton.1 this)] using hm
  · intro hc
    refine ⟨c, hc, ?_⟩
    show c ∈ residuals (C t) (i :: a) c
    rw [Ctx.residuals_out (C := C) (i := i) t a c (hE c hc)]; simp

theorem dev_in : ∀ (σ : List Pos) (t : LTerm) (A : Finset Pos),
    lambdaRS.IsDevelopment t A σ →
    lambdaRS.IsDevelopment (C t) (A.image (i :: ·)) (σ.map (i :: ·)) ∧
    lambdaRS.resSetDeriv (C t) (A.image (i :: ·)) (σ.map (i :: ·)) =
      (lambdaRS.resSetDeriv t A σ).image (i :: ·)
  | [], t, A, _ => ⟨trivial, rfl⟩
  | a :: σ, t, A, h => by
      obtain ⟨ha, haA, hrest⟩ := h
      obtain ⟨ih1, ih2⟩ := dev_in σ (LTerm.contractAt t a) (lambdaRS.resSet t A a) hrest
      have hc : LTerm.contractAt (C t) (i :: a) = C (LTerm.contractAt t a) := hC.con t a
      have hr := hC.resSet_in A t a
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · exact (isRedexAt hC t a).trans ha
      · exact Finset.mem_image_of_mem _ haA
      · show lambdaRS.IsDevelopment (LTerm.contractAt (C t) (i :: a)) _ _
        rw [hc, hr]; exact ih1
      · rw [List.map_cons, ResidualSystem.resSetDeriv_cons]
        show lambdaRS.resSetDeriv (LTerm.contractAt (C t) (i :: a)) _ _ = _
        rw [hc, hr, ih2]; rfl

omit hC in
theorem dev_out (E : Finset Pos) (hE : ∀ p ∈ E, ∀ p', p ≠ i :: p') (hC : Ctx C i) :
    ∀ (σ : List Pos) (t : LTerm), lambdaRS.resSetDeriv (C t) E (σ.map (i :: ·)) = E
  | [], t => rfl
  | a :: σ, t => by
      have hc : LTerm.contractAt (C t) (i :: a) = C (LTerm.contractAt t a) := hC.con t a
      rw [List.map_cons, ResidualSystem.resSetDeriv_cons]
      show lambdaRS.resSetDeriv (LTerm.contractAt (C t) (i :: a)) _ _ = _
      rw [hc, resSet_out E hE]
      exact dev_out E hE hC σ _

end Ctx

/-! ### Decomposing sets of redexes -/

theorem decomp_lam {t : LTerm} {M : Finset Pos} (h : ∀ a ∈ M, isRedexAt (lam t) a = true) :
    M = (subPos M 0).image (0 :: ·) := by
  ext a
  simp only [Finset.mem_image, mem_subPos]
  constructor
  · intro ha
    have := h a ha
    rcases a with _ | ⟨_ | i, p⟩
    · simp at this
    · exact ⟨p, ha, rfl⟩
    · simp at this
  · rintro ⟨p, hp, rfl⟩; exact hp

theorem decomp_app {t s : LTerm} {M : Finset Pos} (h : ∀ a ∈ M, isRedexAt (app t s) a = true) :
    M = (subPos M 0).image (0 :: ·) ∪ (subPos M 1).image (1 :: ·) ∪ M.filter (· = []) := by
  ext a
  simp only [Finset.mem_union, Finset.mem_image, mem_subPos, Finset.mem_filter]
  constructor
  · intro ha
    have := h a ha
    rcases a with _ | ⟨_ | _ | i, p⟩
    · right; exact ⟨ha, rfl⟩
    · left; left; exact ⟨p, ha, rfl⟩
    · left; right; exact ⟨p, ha, rfl⟩
    · simp at this
  · rintro ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨hp, rfl⟩) <;> assumption

/-! ### The canonical development is complete -/

/-- Developing the left then the right part of an application (before any root step). -/
theorem app_phases (t s : LTerm) (A B E : Finset Pos) (hE : ∀ p ∈ E, p = [])
    (σt σs : List Pos)
    (ht : lambdaRS.IsDevelopment t A σt ∧ lambdaRS.resSetDeriv t A σt = ∅)
    (hs : lambdaRS.IsDevelopment s B σs ∧ lambdaRS.resSetDeriv s B σs = ∅) :
    lambdaRS.IsDevelopment (app t s) (A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ E)
        (σt.map (0 :: ·) ++ σs.map (1 :: ·)) ∧
    lambdaRS.resSetDeriv (app t s) (A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ E)
        (σt.map (0 :: ·) ++ σs.map (1 :: ·)) = E ∧
    lambdaRS.tgt (app t s) (σt.map (0 :: ·) ++ σs.map (1 :: ·)) =
      app (lambdaRS.tgt t σt) (lambdaRS.tgt s σs) := by
  have c0 := ctx_appL s
  have c1 := ctx_appR (lambdaRS.tgt t σt)
  have hB1 : ∀ p ∈ B.image (1 :: ·), ∀ p', p ≠ 0 :: p' := by
    intro p hp p'; obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hp; simp
  have hE0 : ∀ p ∈ E, ∀ p', p ≠ 0 :: p' := by intro p hp p'; simp [hE p hp]
  have hE1 : ∀ p ∈ E, ∀ p', p ≠ 1 :: p' := by intro p hp p'; simp [hE p hp]
  have hBE : ∀ p ∈ B.image (1 :: ·) ∪ E, ∀ p', p ≠ 0 :: p' := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    exacts [hB1 p h, hE0 p h]
  have d1 := c0.dev_in σt t A ht.1
  have o1 : lambdaRS.resSetDeriv (app t s) (B.image (1 :: ·)) (σt.map (0 :: ·)) =
      B.image (1 :: ·) := Ctx.dev_out _ hB1 c0 σt t
  have o1' : lambdaRS.resSetDeriv (app t s) E (σt.map (0 :: ·)) = E :=
    Ctx.dev_out _ hE0 c0 σt t
  have res1 : lambdaRS.resSetDeriv (app t s) (A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ E)
      (σt.map (0 :: ·)) = B.image (1 :: ·) ∪ E := by
    rw [ResidualSystem.resSetDeriv_union, ResidualSystem.resSetDeriv_union, o1, o1']
    have : lambdaRS.resSetDeriv (app t s) (A.image (0 :: ·)) (σt.map (0 :: ·)) = ∅ := by
      rw [show lambdaRS.resSetDeriv (app t s) (A.image (0 :: ·)) (σt.map (0 :: ·)) =
        (lambdaRS.resSetDeriv t A σt).image (0 :: ·) from d1.2, ht.2]; rfl
    rw [this]; simp
  have tgt1 : lambdaRS.tgt (app t s) (σt.map (0 :: ·)) = app (lambdaRS.tgt t σt) s :=
    c0.tgt_map t σt
  have d2 := c1.dev_in σs s B hs.1
  have o2 : lambdaRS.resSetDeriv (app (lambdaRS.tgt t σt) s) E (σs.map (1 :: ·)) = E :=
    Ctx.dev_out _ hE1 c1 σs s
  have res2 : lambdaRS.resSetDeriv (app (lambdaRS.tgt t σt) s) (B.image (1 :: ·) ∪ E)
      (σs.map (1 :: ·)) = E := by
    rw [ResidualSystem.resSetDeriv_union, o2]
    have : lambdaRS.resSetDeriv (app (lambdaRS.tgt t σt) s) (B.image (1 :: ·))
        (σs.map (1 :: ·)) = ∅ := by
      rw [show lambdaRS.resSetDeriv (app (lambdaRS.tgt t σt) s) (B.image (1 :: ·))
        (σs.map (1 :: ·)) = (lambdaRS.resSetDeriv s B σs).image (1 :: ·) from d2.2, hs.2]; rfl
    rw [this]; simp
  have tgt2 : lambdaRS.tgt (app (lambdaRS.tgt t σt) s) (σs.map (1 :: ·)) =
      app (lambdaRS.tgt t σt) (lambdaRS.tgt s σs) := c1.tgt_map s σs
  refine ⟨?_, ?_, ?_⟩
  · rw [ResidualSystem.isDevelopment_append]
    refine ⟨ResidualSystem.isDevelopment_mono (by
      intro x hx; simp only [Finset.mem_union]; left; left; exact hx) d1.1, ?_⟩
    rw [tgt1, res1]
    exact ResidualSystem.isDevelopment_mono (by
      intro x hx; simp only [Finset.mem_union]; left; exact hx) d2.1
  · rw [ResidualSystem.resSetDeriv_append, tgt1, res1, res2]
  · rw [ResidualSystem.tgt_append, tgt1, tgt2]

theorem dev_complete_aux : ∀ (t : LTerm) (M : Finset Pos),
    (∀ a ∈ M, isRedexAt t a = true) →
    lambdaRS.IsDevelopment t M (dev t M) ∧ lambdaRS.resSetDeriv t M (dev t M) = ∅
  | var n, M, h => by
      have : M = ∅ := Finset.eq_empty_of_forall_notMem (fun a ha => by simpa using h a ha)
      subst this; exact ⟨trivial, rfl⟩
  | lam t, M, h => by
      have hM := decomp_lam h
      have ih := dev_complete_aux t (subPos M 0) (fun a ha => by
        simpa using h (0 :: a) (mem_subPos.1 ha))
      have key := ctx_lam.dev_in _ t _ ih.1
      rw [← hM] at key
      have hd : dev (lam t) M = (dev t (subPos M 0)).map (0 :: ·) := rfl
      rw [hd]
      refine ⟨key.1, ?_⟩
      rw [show lambdaRS.resSetDeriv (lam t) M ((dev t (subPos M 0)).map (0 :: ·)) =
        (lambdaRS.resSetDeriv t (subPos M 0) (dev t (subPos M 0))).image (0 :: ·) from key.2, ih.2]
      rfl
  | app t s, M, h => by
      have hM := decomp_app h
      have ihA := dev_complete_aux t (subPos M 0) (fun a ha => by
        simpa using h (0 :: a) (mem_subPos.1 ha))
      have ihB := dev_complete_aux s (subPos M 1) (fun a ha => by
        simpa using h (1 :: a) (mem_subPos.1 ha))
      have hE : ∀ p ∈ M.filter (· = []), p = [] := fun p hp => (Finset.mem_filter.1 hp).2
      obtain ⟨P1, P2, P3⟩ := app_phases t s _ _ _ hE _ _ ihA ihB
      rw [← hM] at P1 P2
      have hd : dev (app t s) M = (dev t (subPos M 0)).map (0 :: ·) ++
          (dev s (subPos M 1)).map (1 :: ·) ++ (if [] ∈ M then [[]] else []) := rfl
      rw [hd]
      by_cases h0 : [] ∈ M
      · simp only [h0, ↓reduceIte]
        have hE' : M.filter (· = []) = {[]} := by ext a; simp; intro ha; subst ha; exact h0
        rw [hE'] at P2
        -- the root is a redex, so `t` is an abstraction, and so is its development target
        obtain ⟨u, s', hu⟩ := (isRedexAt_iff _ _).1 (h [] h0)
        simp at hu
        obtain ⟨rfl, rfl⟩ := hu
        have hσ : dev (lam u) (subPos M 0) = (dev u (subPos (subPos M 0) 0)).map (0 :: ·) := rfl
        have hlam : lambdaRS.tgt (lam u) (dev (lam u) (subPos M 0)) =
            lam (lambdaRS.tgt u (dev u (subPos (subPos M 0) 0))) := by
          rw [hσ]; exact ctx_lam.tgt_map _ _
        rw [hlam] at P3
        refine ⟨?_, ?_⟩
        · rw [ResidualSystem.isDevelopment_append, P3, P2]
          refine ⟨P1, ?_, by simp, trivial⟩
          show isRedexAt (app _ _) [] = true
          simp [isRedexAt, subAt, isRedex]
        · rw [ResidualSystem.resSetDeriv_append, P3, P2]
          show lambdaRS.resSet _ _ [] = ∅
          ext c
          simp [ResidualSystem.resSet]
          simp [residuals]
      · simp only [h0, ↓reduceIte, List.append_nil]
        have hE' : M.filter (· = []) = ∅ := by
          ext a; simp; intro ha hne; subst hne; exact h0 ha
        rw [hE'] at P2
        exact ⟨P1, P2⟩

end LTerm

end LambdaLemmas

/-! ## Background: from positional residuals to marked terms

`mark t M` is the marked term obtained from `t` by marking the redexes at the positions of `M`.
Residuation of marked terms computes positional residuals:
`mark t M \ mark t {b} = mark (t contracted at b) (M / b)`. -/

section Bridge

open LTerm Marked Marked.MT

namespace Bridge

/-- The marked term with marks at the positions of `M`. -/
def mark : LTerm → Finset Pos → MT
  | .var n, _ => .var n
  | .lam t, M => .lam (mark t (subPos M 0))
  | .app (.lam u) s, M =>
      if [] ∈ M then .beta (mark u (subPos (subPos M 0) 0)) (mark s (subPos M 1))
      else .app (.lam (mark u (subPos (subPos M 0) 0))) (mark s (subPos M 1))
  | .app t s, M => .app (mark t (subPos M 0)) (mark s (subPos M 1))

/-- Unmarked terms. -/
abbrev ofL (t : LTerm) : MT := mark t ∅

@[simp] theorem subPos_empty (i : ℕ) : subPos (∅ : Finset Pos) i = ∅ := by
  ext; simp

theorem mark_app_of_not_mem {t s : LTerm} {M : Finset Pos} (h : [] ∉ M) :
    mark (.app t s) M = .app (mark t (subPos M 0)) (mark s (subPos M 1)) := by
  cases t <;> simp [mark, h]

theorem mark_app_nonlam {t s : LTerm} (ht : ∀ u, t ≠ .lam u) (M : Finset Pos) :
    mark (.app t s) M = .app (mark t (subPos M 0)) (mark s (subPos M 1)) := by
  cases t with
  | lam u => exact absurd rfl (ht u)
  | _ => rfl

theorem Src_mark : ∀ (t : LTerm) (M : Finset Pos), Src (mark t M) = ofL t
  | .var n, M => by simp [mark, Src]
  | .lam t, M => by simp [mark, Src, Src_mark t]
  | .app (.lam u) s, M => by
    by_cases h : [] ∈ M <;> simp [mark, h, Src, Src_mark u, Src_mark s]
  | .app (.var n) s, M => by
    unfold ofL
    rw [mark_app_nonlam (t := .var n) (by simp) M, mark_app_nonlam (t := .var n) (by simp) ∅]
    simp only [Src, Src_mark s, Src_mark (.var n), subPos_empty]
  | .app (.app a b) s, M => by
    unfold ofL
    rw [mark_app_nonlam (t := .app a b) (by simp) M, mark_app_nonlam (t := .app a b) (by simp) ∅]
    simp only [Src, Src_mark s, Src_mark (.app a b), subPos_empty]

theorem Arr_mark : ∀ (t : LTerm) (M : Finset Pos), Arr (mark t M)
  | .var n, M => by simp [mark, Arr]
  | .lam t, M => by simp [mark, Arr, Arr_mark t]
  | .app (.lam u) s, M => by
    by_cases h : [] ∈ M <;> simp [mark, h, Arr, Arr_mark u, Arr_mark s]
  | .app (.var n) s, M => by
    rw [mark_app_nonlam (t := .var n) (by simp)]; exact ⟨Arr_mark _ _, Arr_mark s _⟩
  | .app (.app a b) s, M => by
    rw [mark_app_nonlam (t := .app a b) (by simp)]; exact ⟨Arr_mark _ _, Arr_mark s _⟩

/-- Shifting indices commutes with marking. -/
theorem mark_shift : ∀ (s : LTerm) (d c : ℕ) (P : Finset Pos),
    mark (LTerm.shift d c s) P = Raise c d (mark s P)
  | .var n, d, c, P => by
    simp only [LTerm.shift]
    split_ifs with h <;> simp [mark] <;> omega
  | .lam t, d, c, P => by simp [LTerm.shift, mark, mark_shift t]
  | .app (.lam b) u, d, c, P => by
    by_cases h : [] ∈ P <;> simp [LTerm.shift, mark, h, mark_shift b, mark_shift u]
  | .app (.var n) u, d, c, P => by
    have h1 : ∀ x, LTerm.shift d c (.var n) ≠ .lam x := by
      intro x; simp only [LTerm.shift]; split_ifs <;> simp
    show mark (.app (LTerm.shift d c (.var n)) (LTerm.shift d c u)) P = _
    rw [mark_app_nonlam h1, mark_app_nonlam (t := .var n) (by simp), mark_shift (.var n),
      mark_shift u]
    rfl
  | .app (.app a b) u, d, c, P => by
    show mark (.app (LTerm.shift d c (.app a b)) (LTerm.shift d c u)) P = _
    rw [mark_app_nonlam (t := LTerm.shift d c (.app a b)) (by simp [LTerm.shift]),
      mark_app_nonlam (t := .app a b) (by simp), mark_shift (.app a b), mark_shift u]
    rfl

/-- Positions of the substituted term: marks of the body, and marks of the argument copied at
every occurrence of the substituted variable. -/
def substSet (u : LTerm) (k : ℕ) (R P : Finset Pos) : Finset Pos :=
  R ∪ ((occs u k).toFinset ×ˢ P).image (fun x => x.1 ++ x.2)

theorem mem_substSet {u : LTerm} {k : ℕ} {R P : Finset Pos} {x : Pos} :
    x ∈ substSet u k R P ↔ x ∈ R ∨ ∃ o ∈ occs u k, ∃ p ∈ P, x = o ++ p := by
  simp only [substSet, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    List.mem_toFinset, Prod.exists]
  constructor
  · rintro (h | ⟨o, p, ⟨ho, hp⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨o, ho, p, hp, rfl⟩
  · rintro (h | ⟨o, ho, p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨o, p, ⟨ho, hp⟩, rfl⟩

theorem subPos_substSet_lam (u0 : LTerm) (k : ℕ) (R P : Finset Pos) :
    subPos (substSet (.lam u0) k R P) 0 = substSet u0 (k + 1) (subPos R 0) P := by
  ext x
  simp only [mem_subPos, mem_substSet, occs, List.mem_map]
  constructor
  · rintro (h | ⟨o, ⟨o', ho', rfl⟩, p, hp, he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨o', ho', p, hp, by simpa using he⟩
  · rintro (h | ⟨o, ho, p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨0 :: o, ⟨o, ho, rfl⟩, p, hp, rfl⟩

theorem subPos_substSet_app (u1 u2 : LTerm) (k : ℕ) (R P : Finset Pos) (i : ℕ) (hi : i = 0 ∨ i = 1) :
    subPos (substSet (.app u1 u2) k R P) i =
      substSet (if i = 0 then u1 else u2) k (subPos R i) P := by
  ext x
  simp only [mem_subPos, mem_substSet, occs, List.mem_append, List.mem_map]
  rcases hi with rfl | rfl
  · simp only [if_true]
    constructor
    · rintro (h | ⟨o, (⟨o', ho', rfl⟩ | ⟨o', ho', rfl⟩), p, hp, he⟩)
      · exact Or.inl h
      · exact Or.inr ⟨o', ho', p, hp, by simpa using he⟩
      · simp at he
    · rintro (h | ⟨o, ho, p, hp, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨0 :: o, Or.inl ⟨o, ho, rfl⟩, p, hp, rfl⟩
  · simp only [show (1 : ℕ) ≠ 0 by omega, if_false]
    constructor
    · rintro (h | ⟨o, (⟨o', ho', rfl⟩ | ⟨o', ho', rfl⟩), p, hp, he⟩)
      · exact Or.inl h
      · simp at he
      · exact Or.inr ⟨o', ho', p, hp, by simpa using he⟩
    · rintro (h | ⟨o, ho, p, hp, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨1 :: o, Or.inr ⟨o, ho, rfl⟩, p, hp, rfl⟩

theorem nil_mem_substSet_app {u1 u2 : LTerm} {k : ℕ} {R P : Finset Pos} :
    [] ∈ substSet (.app u1 u2) k R P ↔ [] ∈ R := by
  rw [mem_substSet]
  constructor
  · rintro (h | ⟨o, ho, p, _, he⟩)
    · exact h
    · simp only [occs, List.mem_append, List.mem_map] at ho
      rcases ho with ⟨o', _, rfl⟩ | ⟨o', _, rfl⟩ <;> simp at he
  · exact Or.inl

theorem subPos_redexes {t : LTerm} {R : Finset Pos} {i : ℕ}
    (hR : ∀ r ∈ R, isRedexAt t r = true) (C : LTerm) (hC : ∀ p, isRedexAt t (i :: p) = isRedexAt C p) :
    ∀ r ∈ subPos R i, isRedexAt C r = true := by
  intro r hr
  rw [← hC]; exact hR _ (mem_subPos.mp hr)

/-- **Substitution and marking.** -/
theorem mark_substAt (s : LTerm) (P : Finset Pos) : ∀ (u : LTerm) (k : ℕ) (R : Finset Pos),
    (∀ r ∈ R, isRedexAt u r = true) →
    mark (substAt k s u) (substSet u k R P) = Subst k (mark s P) (mark u R)
  | .var n, k, R, hR => by
    have hR0 : R = ∅ := by
      ext r; simp only [Finset.notMem_empty, iff_false]; intro hr; simpa using hR r hr
    subst hR0
    by_cases hnk : n = k
    · subst hnk
      have : substSet (.var n) n ∅ P = P := by
        ext x; simp [mem_substSet, occs]
      rw [this]
      simp [substAt, mark, Subst, mark_shift]
    · have : substSet (.var n) k ∅ P = ∅ := by
        ext x; simp [mem_substSet, occs, hnk]
      rw [this]
      simp only [substAt, Subst, mark]
      split_ifs <;> first | omega | rfl
  | .lam u0, k, R, hR => by
    have hR' := subPos_redexes hR u0 (fun p => LTerm.isRedexAt_lam_zero u0 p)
    simp only [substAt, mark, Subst]
    rw [subPos_substSet_lam, mark_substAt s P u0 (k + 1) (subPos R 0) hR']
  | .app (.lam u1) u2, k, R, hR => by
    have hR0 := subPos_redexes hR (.lam u1) (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hR00 := subPos_redexes hR0 u1 (fun p => LTerm.isRedexAt_lam_zero u1 p)
    have hR1 := subPos_redexes hR u2 (fun p => LTerm.isRedexAt_app_one _ _ p)
    have e1 := mark_substAt s P u1 (k + 1) _ hR00
    have e2 := mark_substAt s P u2 k _ hR1
    have q0 := subPos_substSet_app (.lam u1) u2 k R P 0 (Or.inl rfl)
    have q1 := subPos_substSet_app (.lam u1) u2 k R P 1 (Or.inr rfl)
    simp only [if_true, show (1 : ℕ) ≠ 0 by omega, if_false] at q0 q1
    have q00 : subPos (subPos (substSet (.app (.lam u1) u2) k R P) 0) 0 =
        substSet u1 (k + 1) (subPos (subPos R 0) 0) P := by
      rw [q0, subPos_substSet_lam]
    by_cases h : [] ∈ R
    · have h' : [] ∈ substSet (.app (.lam u1) u2) k R P := nil_mem_substSet_app.2 h
      simp only [substAt, mark, h, h', if_true, Subst, q00, q1, e1, e2]
    · have h' : [] ∉ substSet (.app (.lam u1) u2) k R P := fun hh => h (nil_mem_substSet_app.1 hh)
      simp only [substAt, mark, h, h', if_false, Subst, q00, q1, e1, e2]
  | .app (.var n) u2, k, R, hR => by
    have h : [] ∉ R := fun hh => by simpa [isRedexAt, subAt, isRedex] using hR _ hh
    have h' : [] ∉ substSet (.app (.var n) u2) k R P := fun hh => h (nil_mem_substSet_app.1 hh)
    have hR0 := subPos_redexes hR (.var n) (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hR1 := subPos_redexes hR u2 (fun p => LTerm.isRedexAt_app_one _ _ p)
    have q0 := subPos_substSet_app (.var n) u2 k R P 0 (Or.inl rfl)
    have q1 := subPos_substSet_app (.var n) u2 k R P 1 (Or.inr rfl)
    simp only [if_true, show (1 : ℕ) ≠ 0 by omega, if_false] at q0 q1
    show mark (.app (substAt k s (.var n)) (substAt k s u2)) _ = _
    rw [mark_app_of_not_mem h', mark_app_nonlam (t := .var n) (by simp) R, q0, q1,
      mark_substAt s P (.var n) k _ hR0, mark_substAt s P u2 k _ hR1]
    rfl
  | .app (.app a b) u2, k, R, hR => by
    have h : [] ∉ R := fun hh => by simpa [isRedexAt, subAt, isRedex] using hR _ hh
    have h' : [] ∉ substSet (.app (.app a b) u2) k R P := fun hh => h (nil_mem_substSet_app.1 hh)
    have hR0 := subPos_redexes hR (.app a b) (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hR1 := subPos_redexes hR u2 (fun p => LTerm.isRedexAt_app_one _ _ p)
    have q0 := subPos_substSet_app (.app a b) u2 k R P 0 (Or.inl rfl)
    have q1 := subPos_substSet_app (.app a b) u2 k R P 1 (Or.inr rfl)
    simp only [if_true, show (1 : ℕ) ≠ 0 by omega, if_false] at q0 q1
    show mark (.app (substAt k s (.app a b)) (substAt k s u2)) _ = _
    rw [mark_app_of_not_mem h', mark_app_nonlam (t := .app a b) (by simp) R, q0, q1,
      mark_substAt s P (.app a b) k _ hR0, mark_substAt s P u2 k _ hR1]
    rfl

/-! ### Positional residual sets, decomposed -/

theorem resSet_root {u s : LTerm} {M : Finset Pos} :
    lambdaRS.resSet (.app (.lam u) s) M [] =
      substSet u 0 (subPos (subPos M 0) 0) (subPos M 1) := by
  ext x
  simp only [ResidualSystem.resSet, Finset.mem_biUnion, mem_substSet, mem_subPos]
  constructor
  · rintro ⟨m, hm, hx⟩
    change x ∈ residuals (.app (.lam u) s) [] m at hx
    rcases m with _ | ⟨i, m⟩
    · simp [residuals] at hx
    rcases i with _ | _ | i
    · rcases m with _ | ⟨j, m⟩
      · simp [residuals, subAt] at hx
      rcases j with _ | j
      · simp [residuals, subAt] at hx; subst hx; exact Or.inl hm
      · simp [residuals, subAt] at hx
    · simp [residuals, subAt] at hx
      obtain ⟨o, ho, rfl⟩ := hx
      exact Or.inr ⟨o, ho, m, hm, by simp⟩
    · simp [residuals, subAt] at hx
  · rintro (h | ⟨o, ho, p, hp, rfl⟩)
    · exact ⟨0 :: 0 :: x, h, by change x ∈ residuals _ [] _; simp [residuals, subAt]⟩
    · refine ⟨1 :: p, hp, ?_⟩
      change o ++ p ∈ residuals _ [] _
      simp only [residuals, subAt]
      simp
      first | exact ho | exact ⟨o, ho, rfl⟩

theorem resSet_lam {t0 : LTerm} {M : Finset Pos} (hM : ∀ a ∈ M, isRedexAt (.lam t0) a = true)
    (b : Pos) :
    lambdaRS.resSet (.lam t0) M (0 :: b) = (lambdaRS.resSet t0 (subPos M 0) b).image (0 :: ·) := by
  conv_lhs => rw [decomp_lam hM]
  exact ctx_lam.resSet_in _ t0 b

theorem resSet_app0 {t1 s : LTerm} {M : Finset Pos} (hM : ∀ a ∈ M, isRedexAt (.app t1 s) a = true)
    (b : Pos) :
    lambdaRS.resSet (.app t1 s) M (0 :: b) =
      (lambdaRS.resSet t1 (subPos M 0) b).image (0 :: ·) ∪ (subPos M 1).image (1 :: ·) ∪
        M.filter (· = []) := by
  conv_lhs => rw [decomp_app hM]
  rw [ResidualSystem.resSet_union, ResidualSystem.resSet_union, (ctx_appL s).resSet_in,
    Ctx.resSet_out (C := fun t => LTerm.app t s) (i := 0) _ (by simp) t1 b,
    Ctx.resSet_out (C := fun t => LTerm.app t s) (i := 0) _
      (by intro p hp p'; simp at hp; simp [hp.2]) t1 b]

theorem resSet_app1 {t1 s : LTerm} {M : Finset Pos} (hM : ∀ a ∈ M, isRedexAt (.app t1 s) a = true)
    (b : Pos) :
    lambdaRS.resSet (.app t1 s) M (1 :: b) =
      (subPos M 0).image (0 :: ·) ∪ (lambdaRS.resSet s (subPos M 1) b).image (1 :: ·) ∪
        M.filter (· = []) := by
  conv_lhs => rw [decomp_app hM]
  rw [ResidualSystem.resSet_union, ResidualSystem.resSet_union, (ctx_appR t1).resSet_in,
    Ctx.resSet_out (C := fun x => LTerm.app t1 x) (i := 1) _ (by simp) s b,
    Ctx.resSet_out (C := fun x => LTerm.app t1 x) (i := 1) _
      (by intro p hp p'; simp at hp; simp [hp.2]) s b]

theorem subPos_decomp (A B : Finset Pos) (M : Finset Pos) :
    subPos (A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ M.filter (· = [])) 0 = A ∧
    subPos (A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ M.filter (· = [])) 1 = B ∧
    ([] ∈ A.image (0 :: ·) ∪ B.image (1 :: ·) ∪ M.filter (· = []) ↔ [] ∈ M) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x; simp
  · ext x; simp
  · simp

@[simp] theorem subPos_singleton_self (i : ℕ) (b : Pos) : subPos ({i :: b} : Finset Pos) i = {b} := by
  ext; simp
@[simp] theorem subPos_singleton_ne {i j : ℕ} (h : i ≠ j) (b : Pos) :
    subPos ({i :: b} : Finset Pos) j = ∅ := by
  ext x; simp only [mem_subPos, Finset.mem_singleton, List.cons.injEq, Finset.notMem_empty,
    iff_false, not_and]
  intro e; exact absurd e.symm h
@[simp] theorem subPos_singleton_nil (i : ℕ) : subPos ({[]} : Finset Pos) i = ∅ := by
  ext; simp
@[simp] theorem subPos_image_self (A : Finset Pos) (i : ℕ) : subPos (A.image (i :: ·)) i = A := by
  ext; simp

theorem mark_ne_nil (t : LTerm) (M : Finset Pos) : mark t M ≠ .nil := Arr_ne_nil (Arr_mark t M)

theorem resid_mark_ofL (t : LTerm) (M : Finset Pos) : resid (mark t M) (ofL t) = mark t M := by
  have := resid_Src _ (Arr_mark t M)
  rwa [Src_mark] at this

/-- **Bridge theorem**: residuation of marked terms computes positional residuals. -/
theorem resid_mark : ∀ (t : LTerm) (b : Pos) (M : Finset Pos), isRedexAt t b = true →
    (∀ a ∈ M, isRedexAt t a = true) →
    resid (mark t M) (mark t {b}) = mark (contractAt t b) (lambdaRS.resSet t M b)
  | .var n, b, M, hb, _ => by simp at hb
  | .lam t0, [], M, hb, _ => by simp [isRedexAt, subAt, isRedex] at hb
  | .lam t0, (i + 1) :: b, M, hb, _ => by simp at hb
  | .lam t0, 0 :: b, M, hb, hM => by
    have hb' : isRedexAt t0 b = true := by simpa using hb
    have hM0 := subPos_redexes hM t0 (fun p => LTerm.isRedexAt_lam_zero t0 p)
    have e := resid_mark t0 b (subPos M 0) hb' hM0
    rw [show contractAt (.lam t0) (0 :: b) = .lam (contractAt t0 b) from ctx_lam.con t0 b,
      resSet_lam hM]
    simp only [mark, subPos_singleton_self, subPos_image_self, resid, e, mark_ne_nil, ite_false]
  | .app (.lam u) s, [], M, _, hM => by
    have hM00 := subPos_redexes (subPos_redexes hM (.lam u)
      (fun p => LTerm.isRedexAt_app_zero _ _ p)) u (fun p => LTerm.isRedexAt_lam_zero u p)
    rw [resSet_root, show contractAt (.app (.lam u) s) [] = substAt 0 s u from rfl,
      mark_substAt s (subPos M 1) u 0 _ hM00]
    by_cases h : [] ∈ M <;>
      simp [mark, h, resid, resid_mark_ofL, mark_ne_nil]
  | .app (.var n) s, [], M, hb, _ => by simp [isRedexAt, subAt, isRedex] at hb
  | .app (.app a c) s, [], M, hb, _ => by simp [isRedexAt, subAt, isRedex] at hb
  | .app t1 s, 0 :: b, M, hb, hM => by
    have hb' : isRedexAt t1 b = true := by simpa using hb
    have hM0 := subPos_redexes hM t1 (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hM1 := subPos_redexes hM s (fun p => LTerm.isRedexAt_app_one _ _ p)
    rw [show contractAt (.app t1 s) (0 :: b) = .app (contractAt t1 b) s from (ctx_appL s).con t1 b,
      resSet_app0 hM]
    obtain ⟨d0, d1, dn⟩ := subPos_decomp (lambdaRS.resSet t1 (subPos M 0) b) (subPos M 1) M
    have hsb : mark (.app t1 s) {0 :: b} = .app (mark t1 {b}) (ofL s) := by
      rw [mark_app_of_not_mem (by simp)]; simp
    rw [hsb]
    by_cases hr : [] ∈ M
    · obtain ⟨u, rfl⟩ : ∃ u, t1 = .lam u := by
        have := hM _ hr
        cases t1 <;> simp_all [isRedexAt, subAt, isRedex]
      rcases b with _ | ⟨j, b⟩
      · simp [isRedexAt, subAt, isRedex] at hb'
      rcases j with _ | j
      · have hb'' : isRedexAt u b = true := by simpa using hb'
        have hM00 := subPos_redexes hM0 u (fun p => LTerm.isRedexAt_lam_zero u p)
        have e := resid_mark u b (subPos (subPos M 0) 0) hb'' hM00
        rw [show contractAt (.lam u) (0 :: b) = .lam (contractAt u b) from ctx_lam.con u b,
          resSet_lam hM0] at *
        simp only [mark, hr, ite_true, dn.mpr hr, d0, d1, subPos_singleton_self,
          subPos_image_self, resid, e, resid_mark_ofL, mark_ne_nil, or_self, ite_false]
      · simp at hb'
    · have e := resid_mark t1 b (subPos M 0) hb' hM0
      have hr' : [] ∉ (lambdaRS.resSet t1 (subPos M 0) b).image (0 :: ·) ∪
          (subPos M 1).image (1 :: ·) ∪ M.filter (· = []) := fun hh => hr (dn.mp hh)
      rw [mark_app_of_not_mem hr, mark_app_of_not_mem hr', d0, d1]
      simp only [resid, e, resid_mark_ofL, mark_ne_nil, or_self, ite_false]
  | .app t1 s, 1 :: b, M, hb, hM => by
    have hb' : isRedexAt s b = true := by simpa using hb
    have hM0 := subPos_redexes hM t1 (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hM1 := subPos_redexes hM s (fun p => LTerm.isRedexAt_app_one _ _ p)
    have e := resid_mark s b (subPos M 1) hb' hM1
    rw [show contractAt (.app t1 s) (1 :: b) = .app t1 (contractAt s b) from (ctx_appR t1).con s b,
      resSet_app1 hM]
    obtain ⟨d0, d1, dn⟩ := subPos_decomp (subPos M 0) (lambdaRS.resSet s (subPos M 1) b) M
    have hsb : mark (.app t1 s) {1 :: b} = .app (ofL t1) (mark s {b}) := by
      rw [mark_app_of_not_mem (by simp)]; simp
    rw [hsb]
    by_cases hr : [] ∈ M
    · obtain ⟨u, rfl⟩ : ∃ u, t1 = .lam u := by
        have := hM _ hr
        cases t1 <;> simp_all [isRedexAt, subAt, isRedex]
      simp only [mark, hr, ite_true, dn.mpr hr, d0, d1, subPos_empty, resid, e, resid_mark_ofL,
        mark_ne_nil, or_self, ite_false]
    · have hr' : [] ∉ (subPos M 0).image (0 :: ·) ∪
          (lambdaRS.resSet s (subPos M 1) b).image (1 :: ·) ∪ M.filter (· = []) :=
        fun hh => hr (dn.mp hh)
      rw [mark_app_of_not_mem hr, mark_app_of_not_mem hr', d0, d1]
      simp only [resid, e, resid_mark_ofL, mark_ne_nil, or_self, ite_false]
  | .app t1 s, (i + 2) :: b, M, hb, _ => by simp at hb

/-! ### Marked residuals along complete developments -/

theorem subPos_mono {P Q : Finset Pos} (h : P ⊆ Q) (i : ℕ) : subPos P i ⊆ subPos Q i := by
  intro x hx; rw [mem_subPos] at hx ⊢; exact h hx

/-- Residuating by a term with more marks leaves only the target. -/
theorem resid_mark_sub : ∀ (u : LTerm) (Q N : Finset Pos), Q ⊆ N →
    resid (mark u Q) (mark u N) = Trg (mark u N)
  | .var n, Q, N, _ => by simp [mark, resid, Trg]
  | .lam t, Q, N, h => by
    simp [mark, resid, Trg, resid_mark_sub t _ _ (subPos_mono h 0), mark_ne_nil,
      Arr_ne_nil (Arr_Trg _ (Arr_mark t (subPos N 0)))]
  | .app (.lam u) s, Q, N, h => by
    have e1 := resid_mark_sub u _ _ (subPos_mono (subPos_mono h 0) 0)
    have e2 := resid_mark_sub s _ _ (subPos_mono h 1)
    have n1 := Arr_ne_nil (Arr_Trg _ (Arr_mark u (subPos (subPos N 0) 0)))
    have n2 := Arr_ne_nil (Arr_Trg _ (Arr_mark s (subPos N 1)))
    by_cases hN : [] ∈ N <;> by_cases hQ : [] ∈ Q
    · simp [mark, hN, hQ, resid, Trg, e1, e2, n1, n2]
    · simp [mark, hN, hQ, resid, Trg, e1, e2, n1, n2]
    · exact absurd (h hQ) hN
    · simp [mark, hN, hQ, resid, Trg, e1, e2, n1, n2]
  | .app (.var n) s, Q, N, h => by
    rw [mark_app_nonlam (t := .var n) (by simp) Q, mark_app_nonlam (t := .var n) (by simp) N]
    have e2 := resid_mark_sub s _ _ (subPos_mono h 1)
    have n2 := Arr_ne_nil (Arr_Trg _ (Arr_mark s (subPos N 1)))
    simp [mark, resid, Trg, e2, n2]
  | .app (.app a c) s, Q, N, h => by
    rw [mark_app_nonlam (t := .app a c) (by simp) Q, mark_app_nonlam (t := .app a c) (by simp) N]
    have e1 := resid_mark_sub (.app a c) _ _ (subPos_mono h 0)
    have e2 := resid_mark_sub s _ _ (subPos_mono h 1)
    have n1 := Arr_ne_nil (Arr_Trg _ (Arr_mark (.app a c) (subPos N 0)))
    have n2 := Arr_ne_nil (Arr_Trg _ (Arr_mark s (subPos N 1)))
    simp only [resid, e1, e2, n1, n2, or_self, ite_false, Trg]

theorem resSet_redexes {u : LTerm} {P : Finset Pos} {c : Pos} (hc : isRedexAt u c = true)
    (hP : ∀ a ∈ P, isRedexAt u a = true) :
    ∀ a ∈ lambdaRS.resSet u P c, isRedexAt (contractAt u c) a = true := by
  intro a ha
  obtain ⟨m, hm, ham⟩ := Finset.mem_biUnion.mp ha
  exact residuals_isRedexAt u c m hc (hP m hm) a ham

theorem resSetDeriv_redexes : ∀ (σ : List Pos) {u : LTerm} {P : Finset Pos},
    lambdaRS.Valid u σ → (∀ a ∈ P, isRedexAt u a = true) →
    ∀ a ∈ lambdaRS.resSetDeriv u P σ, isRedexAt (lambdaRS.tgt u σ) a = true
  | [], u, P, _, hP => hP
  | c :: σ, u, P, ⟨hc, hσ⟩, hP => resSetDeriv_redexes σ hσ (resSet_redexes hc hP)

/-- Marked residuals along a complete development. -/
theorem mark_resSetDeriv : ∀ (σ : List Pos) {u : LTerm} {N P : Finset Pos},
    (∀ a ∈ N, isRedexAt u a = true) → (∀ a ∈ P, isRedexAt u a = true) →
    lambdaRS.IsCompleteDevelopment u N σ →
    mark (lambdaRS.tgt u σ) (lambdaRS.resSetDeriv u P σ) = resid (mark u P) (mark u N)
  | [], u, N, P, _, _, hσ => by
    have hN : N = ∅ := hσ.2
    subst hN
    exact (resid_mark_ofL u P).symm
  | c :: σ, u, N, P, hN, hP, hσ => by
    obtain ⟨⟨hc, hcN, hdev⟩, hcomp⟩ := hσ
    have ih := mark_resSetDeriv σ (resSet_redexes hc hN) (resSet_redexes hc hP) ⟨hdev, hcomp⟩
    change mark (lambdaRS.tgt (contractAt u c) σ)
      (lambdaRS.resSetDeriv (contractAt u c) (lambdaRS.resSet u P c) σ) = _
    rw [ih, ← resid_mark u c P hc hP, ← resid_mark u c N hc hN]
    have h1 : resid (mark u P) (mark u {c}) ≠ .nil :=
      Con_iff.2 ⟨Arr_mark _ _, Arr_mark _ _, by rw [Src_mark, Src_mark]⟩
    have h2 : resid (mark u N) (mark u {c}) ≠ .nil :=
      Con_iff.2 ⟨Arr_mark _ _, Arr_mark _ _, by rw [Src_mark, Src_mark]⟩
    rw [Cube (Con_resid_resid h1 h2), resid_mark_sub u {c} N (by simpa using hcN)]
    have h3 : resid (mark u P) (mark u N) ≠ .nil :=
      Con_iff.2 ⟨Arr_mark _ _, Arr_mark _ _, by rw [Src_mark, Src_mark]⟩
    rw [← Src_resid h3, resid_Src _ (Arr_resid h3)]

/-- The target of a complete development is the target of the marked term. -/
theorem ofL_tgt {σ : List Pos} {u : LTerm} {N : Finset Pos} (hN : ∀ a ∈ N, isRedexAt u a = true)
    (hσ : lambdaRS.IsCompleteDevelopment u N σ) :
    ofL (lambdaRS.tgt u σ) = Trg (mark u N) := by
  have := mark_resSetDeriv σ hN hN hσ
  rw [hσ.2, resid_self _ (Arr_mark u N)] at this
  exact this

theorem ofL_app (t s : LTerm) : ofL (.app t s) = MT.app (ofL t) (ofL s) := by
  show mark _ ∅ = _
  rw [mark_app_of_not_mem (by simp)]; simp

theorem ofL_lam (t : LTerm) : ofL (.lam t) = MT.lam (ofL t) := by
  show mark _ ∅ = _; simp [mark]

theorem ofL_var (n : ℕ) : ofL (.var n) = MT.var n := rfl

theorem ofL_inj : ∀ {t t' : LTerm}, ofL t = ofL t' → t = t' := by
  intro t
  induction t with
  | var n => intro t' h; cases t' <;> simp_all [ofL_var, ofL_lam, ofL_app]
  | lam t ih =>
    intro t' h
    cases t' with
    | lam t' => simp only [ofL_lam, MT.lam.injEq] at h; rw [ih h]
    | _ => simp [ofL_var, ofL_lam, ofL_app] at h
  | app t s iht ihs =>
    intro t' h
    cases t' with
    | app t' s' =>
      simp only [ofL_app, MT.app.injEq] at h; rw [iht h.1, ihs h.2]
    | _ => simp [ofL_var, ofL_lam, ofL_app] at h

theorem mark_inj_set : ∀ (u : LTerm) {P Q : Finset Pos}, (∀ a ∈ P, isRedexAt u a = true) →
    (∀ a ∈ Q, isRedexAt u a = true) → mark u P = mark u Q → P = Q
  | .var n, P, Q, hP, hQ, _ => by
    have h1 : P = ∅ := by
      ext r; simp only [Finset.notMem_empty, iff_false]; intro hr; simpa using hP r hr
    have h2 : Q = ∅ := by
      ext r; simp only [Finset.notMem_empty, iff_false]; intro hr; simpa using hQ r hr
    rw [h1, h2]
  | .lam t, P, Q, hP, hQ, h => by
    simp only [mark, MT.lam.injEq] at h
    have := mark_inj_set t (subPos_redexes hP t (fun p => LTerm.isRedexAt_lam_zero t p))
      (subPos_redexes hQ t (fun p => LTerm.isRedexAt_lam_zero t p)) h
    rw [decomp_lam hP, decomp_lam hQ, this]
  | .app (.lam u) s, P, Q, hP, hQ, h => by
    have hP0 := subPos_redexes hP (.lam u) (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hQ0 := subPos_redexes hQ (.lam u) (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hP00 := subPos_redexes hP0 u (fun p => LTerm.isRedexAt_lam_zero u p)
    have hQ00 := subPos_redexes hQ0 u (fun p => LTerm.isRedexAt_lam_zero u p)
    have hP1 := subPos_redexes hP s (fun p => LTerm.isRedexAt_app_one _ _ p)
    have hQ1 := subPos_redexes hQ s (fun p => LTerm.isRedexAt_app_one _ _ p)
    have key : ([] ∈ P ↔ [] ∈ Q) ∧ mark u (subPos (subPos P 0) 0) = mark u (subPos (subPos Q 0) 0) ∧
        mark s (subPos P 1) = mark s (subPos Q 1) := by
      by_cases h1 : [] ∈ P <;> by_cases h2 : [] ∈ Q <;> simp_all [mark]
    have e00 := mark_inj_set u hP00 hQ00 key.2.1
    have e1 := mark_inj_set s hP1 hQ1 key.2.2
    have e0 : subPos P 0 = subPos Q 0 := by
      rw [decomp_lam hP0, decomp_lam hQ0, e00]
    rw [decomp_app hP, decomp_app hQ, e0, e1]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, rfl⟩; exact ⟨key.1.mp hx, rfl⟩
    · rintro ⟨hx, rfl⟩; exact ⟨key.1.mpr hx, rfl⟩
  | .app (.var n) s, P, Q, hP, hQ, h => by
    have nP : [] ∉ P := fun hh => by simpa [isRedexAt, subAt, isRedex] using hP _ hh
    have nQ : [] ∉ Q := fun hh => by simpa [isRedexAt, subAt, isRedex] using hQ _ hh
    rw [mark_app_of_not_mem nP, mark_app_of_not_mem nQ, MT.app.injEq] at h
    have e0 := mark_inj_set (.var n) (subPos_redexes hP _ (fun p => LTerm.isRedexAt_app_zero _ _ p))
      (subPos_redexes hQ _ (fun p => LTerm.isRedexAt_app_zero _ _ p)) h.1
    have e1 := mark_inj_set s (subPos_redexes hP s (fun p => LTerm.isRedexAt_app_one _ _ p))
      (subPos_redexes hQ s (fun p => LTerm.isRedexAt_app_one _ _ p)) h.2
    rw [decomp_app hP, decomp_app hQ, e0, e1]
    congr 1
    ext x; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, rfl⟩; exact absurd hx nP
    · rintro ⟨hx, rfl⟩; exact absurd hx nQ
  | .app (.app a c) s, P, Q, hP, hQ, h => by
    have nP : [] ∉ P := fun hh => by simpa [isRedexAt, subAt, isRedex] using hP _ hh
    have nQ : [] ∉ Q := fun hh => by simpa [isRedexAt, subAt, isRedex] using hQ _ hh
    rw [mark_app_of_not_mem nP, mark_app_of_not_mem nQ, MT.app.injEq] at h
    have e0 := mark_inj_set (.app a c)
      (subPos_redexes hP _ (fun p => LTerm.isRedexAt_app_zero _ _ p))
      (subPos_redexes hQ _ (fun p => LTerm.isRedexAt_app_zero _ _ p)) h.1
    have e1 := mark_inj_set s (subPos_redexes hP s (fun p => LTerm.isRedexAt_app_one _ _ p))
      (subPos_redexes hQ s (fun p => LTerm.isRedexAt_app_one _ _ p)) h.2
    rw [decomp_app hP, decomp_app hQ, e0, e1]
    congr 1
    ext x; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, rfl⟩; exact absurd hx nP
    · rintro ⟨hx, rfl⟩; exact absurd hx nQ

theorem coinitial_marks (u : LTerm) (P Q : Finset Pos) : resid (mark u P) (mark u Q) ≠ .nil :=
  Con_iff.2 ⟨Arr_mark _ _, Arr_mark _ _, by rw [Src_mark, Src_mark]⟩

/-- **Semantic orthogonality** of β-reduction (Lévy's cube lemma, positional form). -/
theorem semantic_orthogonality (t : LTerm) (a b : Pos) (ha : isRedexAt t a = true)
    (hb : isRedexAt t b = true) :
    ∃ σ τ, lambdaRS.IsCompleteDevelopment (lambdaRS.contract t b) (lambdaRS.res t b a) σ ∧
      lambdaRS.IsCompleteDevelopment (lambdaRS.contract t a) (lambdaRS.res t a b) τ ∧
      lambdaRS.tgt (lambdaRS.contract t b) σ = lambdaRS.tgt (lambdaRS.contract t a) τ ∧
      ∀ c, lambdaRS.isStep t c →
        lambdaRS.resSetDeriv t {c} (a :: τ) = lambdaRS.resSetDeriv t {c} (b :: σ) := by
  have hNa : ∀ x ∈ lambdaRS.res t b a, isRedexAt (contractAt t b) x = true :=
    residuals_isRedexAt t b a hb ha
  have hNb : ∀ x ∈ lambdaRS.res t a b, isRedexAt (contractAt t a) x = true :=
    residuals_isRedexAt t a b ha hb
  have hσ := dev_complete_aux (contractAt t b) _ hNa
  have hτ := dev_complete_aux (contractAt t a) _ hNb
  have htgt : lambdaRS.tgt (lambdaRS.contract t b) (lambdaRS.dev (contractAt t b) (lambdaRS.res t b a)) =
      lambdaRS.tgt (lambdaRS.contract t a) (lambdaRS.dev (contractAt t a) (lambdaRS.res t a b)) := by
    have hsa : ∀ x ∈ ({a} : Finset Pos), isRedexAt t x = true := by simpa using ha
    have hsb : ∀ x ∈ ({b} : Finset Pos), isRedexAt t x = true := by simpa using hb
    have e1 := ofL_tgt hNa hσ
    have e2 := ofL_tgt hNb hτ
    have r1 := resid_mark t b {a} hb hsa
    have r2 := resid_mark t a {b} ha hsb
    rw [ResidualSystem.resSet_singleton] at r1 r2
    change ofL (lambdaRS.tgt (contractAt t b) _) = Trg (mark (contractAt t b) (residuals t b a)) at e1
    change ofL (lambdaRS.tgt (contractAt t a) _) = Trg (mark (contractAt t a) (residuals t a b)) at e2
    apply ofL_inj
    change ofL (lambdaRS.tgt (contractAt t b) _) = ofL (lambdaRS.tgt (contractAt t a) _)
    rw [e1, e2, ← r1, ← r2]
    have hc := Con_resid_resid (coinitial_marks t {b} {b}) (coinitial_marks t {a} {b})
    have hcube := Cube hc
    have s1 := Src_resid hc
    have s2 := Src_resid (hcube ▸ hc)
    rw [hcube] at s1
    rw [← s1, s2]
  refine ⟨_, _, hσ, hτ, htgt, ?_⟩
  · intro c hc
    have hsc : ∀ x ∈ ({c} : Finset Pos), isRedexAt t x = true := by simpa using hc
    have hPa : ∀ x ∈ lambdaRS.resSet t {c} a, isRedexAt (contractAt t a) x = true :=
      resSet_redexes ha hsc
    have hPb : ∀ x ∈ lambdaRS.resSet t {c} b, isRedexAt (contractAt t b) x = true :=
      resSet_redexes hb hsc
    have m1 := mark_resSetDeriv _ hNb hPa hτ
    have m2 := mark_resSetDeriv _ hNa hPb hσ
    have ra := resid_mark t a {c} ha hsc
    have rb := resid_mark t b {c} hb hsc
    have hsa : ∀ x ∈ ({a} : Finset Pos), isRedexAt t x = true := by simpa using ha
    have hsb : ∀ x ∈ ({b} : Finset Pos), isRedexAt t x = true := by simpa using hb
    have r1 := resid_mark t b {a} hb hsa
    have r2 := resid_mark t a {b} ha hsb
    rw [ResidualSystem.resSet_singleton] at r1 r2
    change mark _ _ = resid (mark (contractAt t a) (lambdaRS.resSet t {c} a))
      (mark (contractAt t a) (residuals t a b)) at m1
    change mark _ _ = resid (mark (contractAt t b) (lambdaRS.resSet t {c} b))
      (mark (contractAt t b) (residuals t b a)) at m2
    rw [← ra, ← r2] at m1
    rw [← rb, ← r1] at m2
    have hcube := Cube (Con_resid_resid (coinitial_marks t {c} {a}) (coinitial_marks t {b} {a}))
    rw [hcube, ← m2] at m1
    change lambdaRS.resSetDeriv (contractAt t a) (lambdaRS.resSet t {c} a) _ =
      lambdaRS.resSetDeriv (contractAt t b) (lambdaRS.resSet t {c} b) _
    have hX := resSetDeriv_redexes _ (ResidualSystem.isDevelopment_valid hτ.1) hPa
    have hY := resSetDeriv_redexes _ (ResidualSystem.isDevelopment_valid hσ.1) hPb
    change lambdaRS.tgt (contractAt t b) _ = lambdaRS.tgt (contractAt t a) _ at htgt
    rw [← htgt] at m1 hX
    exact mark_inj_set _ hX hY m1

/-! ### Finite developments (de Vrijer) -/

theorem beta_bounds {X Y Z W : MT} (hZ : hgt Z ≤ hgt X) (hW : hgt W ≤ hgt Y)
    (hm : ∀ x, mtp x Z ≤ mtp x X) (hm' : ∀ x, mtp x W ≤ mtp x Y) :
    hgt (.beta Z W) ≤ hgt (.beta X Y) ∧ ∀ x, mtp x (.beta Z W) ≤ mtp x (.beta X Y) := by
  have hmax : max 1 (mtp 0 Z) ≤ max 1 (mtp 0 X) := max_le_max le_rfl (hm 0)
  refine ⟨?_, fun x => ?_⟩
  · simp only [hgt]
    have := Nat.mul_le_mul hW hmax
    omega
  · simp only [mtp]
    have := Nat.mul_le_mul (hm' x) hmax
    have := hm (x + 1)
    omega

/-- One development step decreases the height and does not increase multiplicities. -/
theorem dev_step_decreases : ∀ (w : LTerm) (c : Pos) (N : Finset Pos), isRedexAt w c = true →
    (∀ a ∈ N, isRedexAt w a = true) → c ∈ N →
    hgt (resid (mark w N) (mark w {c})) < hgt (mark w N) ∧
      ∀ x, mtp x (resid (mark w N) (mark w {c})) ≤ mtp x (mark w N)
  | .var n, c, N, hc, _, _ => by simp at hc
  | .lam t0, [], N, hc, _, _ => by simp [isRedexAt, subAt, isRedex] at hc
  | .lam t0, (i + 1) :: b, N, hc, _, _ => by simp at hc
  | .lam t0, 0 :: b, N, hc, hN, hcN => by
    have hb : isRedexAt t0 b = true := by simpa using hc
    have hN0 := subPos_redexes hN t0 (fun p => LTerm.isRedexAt_lam_zero t0 p)
    obtain ⟨h1, h2⟩ := dev_step_decreases t0 b (subPos N 0) hb hN0 (by simpa using hcN)
    simp only [mark, subPos_singleton_self, resid, resid_mark t0 b _ hb hN0, mark_ne_nil,
      ite_false, hgt, mtp]
    rw [← resid_mark t0 b _ hb hN0]
    exact ⟨h1, fun x => h2 (x + 1)⟩
  | .app (.lam u) s, [], N, _, hN, hcN => by
    set X := mark u (subPos (subPos N 0) 0)
    set Y := mark s (subPos N 1)
    have hm : mark (.app (.lam u) s) {[]} = .beta (ofL u) (ofL s) := by simp [mark]
    have hX : mark (.app (.lam u) s) N = .beta X Y := by simp [mark, hcN, X, Y]
    have hr : resid (.beta X Y) (.beta (ofL u) (ofL s)) = Subst 0 Y X := by
      simp only [resid, X, Y, resid_mark_ofL, mark_ne_nil, or_self, ite_false]
    rw [hm, hX, hr]
    refine ⟨?_, fun x => ?_⟩
    · rw [hgt_Subst]
      simp only [hgt]
      have := Nat.mul_le_mul_left (hgt Y) (le_max_right 1 (mtp 0 X))
      omega
    · rcases x with _ | x
      · simpa [mtp] using mtp0_subst_le Y X
      · have := mtp_Subst' Y X x 0
        simp only [Nat.add_zero] at this
        rw [this]
        simp only [mtp]
        have := Nat.mul_le_mul_left (mtp (x + 1) Y) (le_max_right 1 (mtp 0 X))
        rw [show x + 1 + 1 = x + 2 by omega]
        omega
  | .app (.var n) s, [], N, hc, _, _ => by simp [isRedexAt, subAt, isRedex] at hc
  | .app (.app a c) s, [], N, hc, _, _ => by simp [isRedexAt, subAt, isRedex] at hc
  | .app t1 s, 0 :: b, N, hc, hN, hcN => by
    have hb : isRedexAt t1 b = true := by simpa using hc
    have hN0 := subPos_redexes hN t1 (fun p => LTerm.isRedexAt_app_zero _ _ p)
    have hsb : mark (.app t1 s) {0 :: b} = .app (mark t1 {b}) (ofL s) := by
      rw [mark_app_of_not_mem (by simp)]; simp
    rw [hsb]
    by_cases hr : [] ∈ N
    · obtain ⟨u, rfl⟩ : ∃ u, t1 = .lam u := by
        have := hN _ hr
        cases t1 <;> simp_all [isRedexAt, subAt, isRedex]
      rcases b with _ | ⟨j, b⟩
      · simp [isRedexAt, subAt, isRedex] at hb
      rcases j with _ | j
      · have hb' : isRedexAt u b = true := by simpa using hb
        have hN00 := subPos_redexes hN0 u (fun p => LTerm.isRedexAt_lam_zero u p)
        obtain ⟨h1, h2⟩ := dev_step_decreases u b _ hb' hN00 (by simpa using hcN)
        simp only [mark, hr, ite_true, subPos_singleton_self, resid, resid_mark_ofL,
          mark_ne_nil, resid_mark u b _ hb' hN00, or_self, ite_false]
        rw [← resid_mark u b _ hb' hN00]
        obtain ⟨g1, g2⟩ := beta_bounds h1.le le_rfl h2 (fun _ => le_rfl)
        refine ⟨?_, g2⟩
        simp only [hgt]
        have := Nat.mul_le_mul_left (hgt (mark s (subPos N 1)))
          (max_le_max (le_refl 1) (h2 0))
        omega
      · simp at hb
    · have hb2 := dev_step_decreases t1 b (subPos N 0) hb hN0 (by simpa using hcN)
      rw [mark_app_of_not_mem hr]
      simp only [resid, resid_mark_ofL, mark_ne_nil, resid_mark t1 b _ hb hN0, or_self, ite_false,
        hgt, mtp]
      rw [← resid_mark t1 b _ hb hN0]
      exact ⟨by have := hb2.1; omega, fun x => by have := hb2.2 x; omega⟩
  | .app t1 s, 1 :: b, N, hc, hN, hcN => by
    have hb : isRedexAt s b = true := by simpa using hc
    have hN1 := subPos_redexes hN s (fun p => LTerm.isRedexAt_app_one _ _ p)
    obtain ⟨h1, h2⟩ := dev_step_decreases s b (subPos N 1) hb hN1 (by simpa using hcN)
    have hsb : mark (.app t1 s) {1 :: b} = .app (ofL t1) (mark s {b}) := by
      rw [mark_app_of_not_mem (by simp)]; simp
    rw [hsb]
    by_cases hr : [] ∈ N
    · obtain ⟨u, rfl⟩ : ∃ u, t1 = .lam u := by
        have := hN _ hr
        cases t1 <;> simp_all [isRedexAt, subAt, isRedex]
      simp only [mark, hr, ite_true, subPos_empty, resid, resid_mark_ofL, mark_ne_nil,
        resid_mark s b _ hb hN1, or_self, ite_false]
      rw [← resid_mark s b _ hb hN1]
      set X := mark u (subPos (subPos N 0) 0)
      refine ⟨?_, fun x => ?_⟩
      · simp only [hgt]
        have hpos : 0 < max 1 (mtp 0 X) := lt_of_lt_of_le Nat.one_pos (le_max_left _ _)
        have := Nat.mul_lt_mul_of_pos_right h1 hpos
        omega
      · simp only [mtp]
        have := Nat.mul_le_mul_right (max 1 (mtp 0 X)) (h2 x)
        omega
    · rw [mark_app_of_not_mem hr]
      simp only [resid, resid_mark_ofL, mark_ne_nil, resid_mark s b _ hb hN1, or_self, ite_false,
        hgt, mtp]
      rw [← resid_mark s b _ hb hN1]
      exact ⟨by omega, fun x => by have := h2 x; omega⟩
  | .app t1 s, (i + 2) :: b, N, hc, _, _ => by simp at hc

/-- Developments are bounded by the height of the marked term. -/
theorem dev_length_le : ∀ (σ : List Pos) {u : LTerm} {N : Finset Pos},
    (∀ a ∈ N, isRedexAt u a = true) → lambdaRS.IsDevelopment u N σ → σ.length ≤ hgt (mark u N)
  | [], _, _, _, _ => Nat.zero_le _
  | c :: σ, u, N, hN, ⟨hc, hcN, hdev⟩ => by
    have ih := dev_length_le σ (resSet_redexes hc hN) hdev
    have hdec := (dev_step_decreases u c N hc hN hcN).1
    rw [resid_mark u c N hc hN] at hdec
    change σ.length ≤ hgt (mark (contractAt u c) (lambdaRS.resSet u N c)) at ih
    simp only [List.length_cons]
    omega

/-- **Finite developments** for β-reduction. -/
theorem finite_developments (t : LTerm) (M : Finset Pos) (hM : ∀ a ∈ M, lambdaRS.isStep t a) :
    ¬ ∃ f : ℕ → Pos, ∀ n, lambdaRS.IsDevelopment t M (List.ofFn fun i : Fin n => f i) := by
  rintro ⟨f, hf⟩
  have := dev_length_le _ hM (hf (hgt (mark t M) + 1))
  simp at this

end Bridge

end Bridge

/-! ## Background results assumed by the thesis

This module records the external result the thesis cites without proof: orthogonality of
β-reduction (Melliès).  It is now proved: finite developments by de Vrijer's measure and
semantic orthogonality by Lévy's cube lemma, both on marked terms (`Chapter0Marked.lean`,
`Chapter0Bridge.lean`, following Huet's Coq development and Stark's Isabelle/AFP entry
`ResiduatedTransitionSystem`). -/

end CiruelosLic

namespace CiruelosLic.Background

open CiruelosLic LTerm

/-! ## Orthogonality of β-reduction, split by axiom

The thesis cites Melliès for orthogonality of the λ-calculus in
`document/02-preliminaries.tex` (the paragraph beginning "The λ-calculus is an
example of an orthogonal axiomatic rewrite system"); it supplies no proof.
`lambdaRS.Orthogonal` packages five obligations, stated separately below so they can be
discharged independently. -/

/-- Residuals of a redex after contracting a coinitial redex are redexes of the target. -/
theorem lambda_res_isStep :
    ∀ t a b, lambdaRS.isStep t a → lambdaRS.isStep t b →
      ∀ c ∈ lambdaRS.res t b a, lambdaRS.isStep (lambdaRS.contract t b) c :=
  fun t a b ha hb => LTerm.residuals_isRedexAt t b a hb ha

/-- **Autoerasure**: `R / R = ∅`. -/
theorem lambda_autoerasure :
    ∀ t a, lambdaRS.isStep t a → lambdaRS.res t a a = ∅ := by
  intro t a _
  simp [residuals]

/-- **Finite Developments**: no infinite development of a finite set of coinitial redexes.

Source: Melliès thesis, Axiome FD (§2.2, p. 17) and Théorème 3.2 (FD+, §3.4). The thesis proves
FD abstractly from axioms A, B, C, fd-1..fd-4 (§3.3) over a nesting relation `<` and a
"grip" relation `<<`, using a multiset-of-heights measure (Lemmes 3.10, 3.15, Cor. 3.16). For λ
it only sketches the check (§3.6.1: fd-2 left to the reader), so the λ-specific
verification is not in the thesis. -/
theorem lambda_finite_developments :
    ∀ t (M : Finset Pos), (∀ a ∈ M, lambdaRS.isStep t a) →
      ¬ ∃ f : ℕ → Pos, ∀ n,
        lambdaRS.IsDevelopment t M (List.ofFn fun i : Fin n => f i) :=
  fun t M hM => Bridge.finite_developments t M hM

/-- **Semantic Orthogonality** (Melliès thesis, Axiome PERM, §2.3, p. 17ff; the thesis
does not prove it for λ and defers to the literature, e.g. Huet–Lévy for first-order systems
and Ch. 7 for CRS): the residual square closes up to complete
developments with equal targets and equal residuals of every third step. -/
theorem lambda_semantic_orthogonality :
    ∀ t a b, lambdaRS.isStep t a → lambdaRS.isStep t b →
      ∃ σ τ, lambdaRS.IsCompleteDevelopment (lambdaRS.contract t b) (lambdaRS.res t b a) σ ∧
        lambdaRS.IsCompleteDevelopment (lambdaRS.contract t a) (lambdaRS.res t a b) τ ∧
        lambdaRS.tgt (lambdaRS.contract t b) σ = lambdaRS.tgt (lambdaRS.contract t a) τ ∧
        ∀ c, lambdaRS.isStep t c →
          lambdaRS.resSetDeriv t {c} (a :: τ) = lambdaRS.resSetDeriv t {c} (b :: σ) :=
  fun t a b ha hb => Bridge.semantic_orthogonality t a b ha hb

/-- The chosen canonical development `dev` is a complete development. -/
theorem lambda_dev_complete :
    ∀ t (M : Finset Pos), (∀ a ∈ M, lambdaRS.isStep t a) →
      lambdaRS.IsCompleteDevelopment t M (lambdaRS.dev t M) :=
  fun t M hM => LTerm.dev_complete_aux t M hM

/-- Orthogonality of beta reduction with the positional residuals and canonical
developments used here, assembled from the five obligations above. -/
theorem lambda_orthogonal : lambdaRS.Orthogonal where
  res_isStep := lambda_res_isStep
  autoerasure := lambda_autoerasure
  finite_developments := lambda_finite_developments
  semantic_orthogonality := lambda_semantic_orthogonality
  dev_complete := lambda_dev_complete

end CiruelosLic.Background

namespace CiruelosLic

/-! ## Chapter 1: the λ-calculus as an orthogonal rewrite system

Orthogonality of β-reduction, the derivation space `𝔻_λ(t)`, and Laneve's counterexample (derivation spaces of the λ-calculus are not lattices). -/

section Ch1Lambda

/-- The λ-calculus is an orthogonal axiomatic rewrite system [Melliès]. -/
theorem lambda_orthogonal : lambdaRS.Orthogonal := Background.lambda_orthogonal

instance : Fact lambdaRS.Orthogonal := ⟨lambda_orthogonal⟩

/-- The derivation space `𝔻_λ(t)`, an upper semilattice. -/
abbrev DSpaceLam (t : LTerm) : Type := lambdaRS.DSpace t

open LTerm ResidualSystem in
/-- Laneve's counterexample (Introduction / §3.4): derivation spaces of the λ-calculus are not
lattices in general. The witness is `(λx.(λy.a)(x Ω))(λz.b)` and the derivations `ST`, `R`. -/
theorem lambda_dspace_not_lattice :
    ∃ (t : LTerm) (a b : DSpaceLam t), ¬ ∃ c, IsGLB {a, b} c := by
  let r : lambdaRS.DerivFrom laneveTerm := ⟨laneveR, by
      unfold laneveR ResidualSystem.Valid
      exact ⟨by decide, trivial⟩⟩
  let st : lambdaRS.DerivFrom laneveTerm := ⟨laneveST, by
      unfold laneveST ResidualSystem.Valid
      exact ⟨by decide, by decide, trivial⟩⟩
  refine ⟨laneveTerm, DSpace.mk r, DSpace.mk st, ?_⟩
  rintro ⟨c, hc⟩
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep c
  have hR : lambdaRS.Prefix laneveTerm σ.val laneveR :=
    hc.1 (show DSpace.mk r ∈ {DSpace.mk r, DSpace.mk st} from Set.mem_insert _ _)
  have hST : lambdaRS.Prefix laneveTerm σ.val laneveST :=
    hc.1 (show DSpace.mk st ∈ {DSpace.mk r, DSpace.mk st} by simp)
  obtain ⟨n, hn⟩ := laneve_lower_shape σ.val σ.property hR hST
  let longer : lambdaRS.DerivFrom laneveTerm :=
    ⟨List.replicate (n + 1) laneveU, laneve_repeat_valid (n + 1)⟩
  have hlower : DSpace.mk longer ∈ lowerBounds {DSpace.mk r, DSpace.mk st} := by
    intro d hd
    rcases Set.mem_insert_iff.1 hd with rfl | hd
    · exact (laneve_repeat_lower (n + 1)).1
    · have hd' := Set.mem_singleton_iff.1 hd
      subst d
      exact (laneve_repeat_lower (n + 1)).2
  have hle : lambdaRS.Prefix laneveTerm (List.replicate (n + 1) laneveU) σ.val := hc.2 hlower
  rw [hn] at hle
  exact laneve_repeat_not_le lambda_orthogonal n hle

end Ch1Lambda

end CiruelosLic
