import Mathlib
import CiruelosLic.PreliminariesLambdaOrthogonality

/-!
# Chapter 2 (§§2.1–2.3): the distributive λ-calculus λ^dist

Types, syntax, typing, correctness and substitution, with the typing lemmas of the appendix.

Contents:
* Chapter 2: A distributive λ-calculus (λ^dist) — Definitions
* Chapter 2: A distributive λ-calculus (λ^dist) — Appendix
-/

namespace CiruelosLic

/-! ## Chapter 2: A distributive λ-calculus (λ^dist) — Definitions

### Representation choices

* **Binders** use de Bruijn indices: `lam ℓ t` binds index `0` in `t`, and the typing rule
  `Γ ⊕ x : M ⊢ t : σ` becomes `M :: Γ ⊢ t : σ` (see `Ctx.cons`).
* **Multisets inside types.** A type `M →ℓ σ` contains a multiset `M`. Lean can't nest an
  inductive type through `Multiset` (a quotient), so the domain is a `List Ty`. The typing rule
  `→I` always produces the *canonical* listing `Ty.canon M` of the multiset (sorted by a linear
  order on types, so it is computable), and `→E` matches arguments against the domain up to
  permutation. Hence every typable term has a unique type (`hasType_unique`), exactly as in the
  thesis, where types are built from multisets.
* **Typing contexts** really are multiset-valued: `Ctx = ℕ → Multiset Ty`.
* **Substitution** is defined both as the thesis' *partition-based* relation (`PSubst`) and its
  *type-directed* ("alternative") function (`DTerm.subst`), which agree under sequentiality. -/

section Ch2Defs

/-- Labels `ℒ`, a denumerable set. -/
abbrev Label := ℕ

/-! ## 2.1 Types -/

/-- Types: `τ ::= α^ℓ | M →ℓ τ`, where `M` is a (sequential, hence canonically listed) multiset. -/
inductive Ty
  | base (α : ℕ) (ℓ : Label)
  | arrow (dom : List Ty) (ℓ : Label) (cod : Ty)
  deriving Repr

namespace Ty

/-- The external label. -/
def label : Ty → Label
  | base _ ℓ => ℓ
  | arrow _ ℓ _ => ℓ

/-- `σ ⊴ τ`: `σ` occurs in `τ`. Reflexive–transitive closure of `τᵢ ⊴ [τ₁…τₙ] → σ` and
`σ ⊴ [τ₁…τₙ] → σ`. -/
inductive Occurs : Ty → Ty → Prop
  | refl (τ : Ty) : Occurs τ τ
  | dom {σ τ : Ty} {M : List Ty} {ℓ : Label} {ρ : Ty} : τ ∈ M → Occurs σ τ → Occurs σ (arrow M ℓ ρ)
  | cod {σ ρ : Ty} {M : List Ty} {ℓ : Label} : Occurs σ ρ → Occurs σ (arrow M ℓ ρ)

/-! ### A computable linear order on types

`deriving DecidableEq`/`Encodable` don't support nested inductives, so we serialize types
by hand. The order itself carries no meaning: it only picks a canonical listing of a multiset. -/

mutual
/-- Prefix-free serialization of a type. -/
def enc : Ty → List ℕ
  | base α ℓ => [0, α, ℓ]
  | arrow dom ℓ cod => [1, dom.length, ℓ] ++ encList dom ++ enc cod
/-- Serialization of a list of types (its length is stored by the enclosing `enc`). -/
def encList : List Ty → List ℕ
  | [] => []
  | d :: ds => enc d ++ encList ds
end

mutual
theorem enc_append_inj : ∀ (a b : Ty) (r r' : List ℕ), a.enc ++ r = b.enc ++ r' → a = b ∧ r = r'
  | base α ℓ, base β m, r, r', h => by simp_all [enc]
  | base _ _, arrow _ _ _, _, _, h => by simp [enc] at h
  | arrow _ _ _, base _ _, _, _, h => by simp [enc] at h
  | arrow ds ℓ c, arrow es m d, r, r', h => by
    simp only [enc, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
      true_and] at h
    obtain ⟨hlen, rfl, h⟩ := h
    obtain ⟨rfl, h⟩ := encList_append_inj ds es _ _ hlen h
    obtain ⟨rfl, rfl⟩ := enc_append_inj c d r r' (List.append_cancel_left h)
    exact ⟨rfl, rfl⟩
theorem encList_append_inj : ∀ (ds es : List Ty) (r r' : List ℕ), ds.length = es.length →
    encList ds ++ r = encList es ++ r' → ds = es ∧ r = r'
  | [], [], _, _, _, h => by simpa [encList] using h
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | d :: ds, e :: es, r, r', hl, h => by
    simp only [encList, List.append_assoc] at h
    obtain ⟨rfl, h⟩ := enc_append_inj d e _ _ h
    obtain ⟨rfl, rfl⟩ :=
      encList_append_inj ds es r r' (by simpa using hl) (List.append_cancel_left h)
    exact ⟨rfl, rfl⟩
end

theorem enc_injective : Function.Injective enc := fun a b h =>
  (enc_append_inj a b [] [] (by simpa using h)).1

/-- Types are linearly ordered (lexicographically on `enc`); this also gives `DecidableEq Ty`. -/
instance : LinearOrder Ty := LinearOrder.lift' enc enc_injective

/-- The canonical listing of a multiset of types: sorted. -/
def canon (M : Multiset Ty) : List Ty := M.sort (· ≤ ·)

@[simp] theorem coe_canon (M : Multiset Ty) : (canon M : Multiset Ty) = M := Multiset.sort_eq _ _

@[simp] theorem mem_canon {M : Multiset Ty} {τ : Ty} : τ ∈ canon M ↔ τ ∈ M := Multiset.mem_sort _

@[simp] theorem length_canon (M : Multiset Ty) : (canon M).length = Multiset.card M :=
  Multiset.length_sort _

@[simp] theorem canon_zero : canon 0 = [] := Multiset.sort_zero _

end Ty

/-- A multiset of types is *sequential*: external labels are pairwise distinct. -/
def SeqMS (M : Multiset Ty) : Prop := (M.map Ty.label).Nodup

/-! ## Typing contexts (Chapter 1, §"Typing") -/

/-- Typing contexts: total functions from (de Bruijn) variables to finite multisets of types.
Sum of contexts `Γ + Δ` is the pointwise sum (the `Pi` instance), `0` is the empty context. -/
abbrev Ctx := ℕ → Multiset Ty

namespace Ctx

/-- The context `x : M`. -/
def single (n : ℕ) (M : Multiset Ty) : Ctx := fun m => if m = n then M else 0

/-- `Γ ⊕ x : M` when `x` is the variable bound by a new binder: `M` at index `0`, `Γ` shifted. -/
def cons (M : Multiset Ty) (Γ : Ctx) : Ctx
  | 0 => M
  | n + 1 => Γ n

/-- A context is sequential if every `Γ(x)` is. -/
def Seq (Γ : Ctx) : Prop := ∀ n, SeqMS (Γ n)

/-- `σ ⊴ Γ`. -/
def Occurs (σ : Ty) (Γ : Ctx) : Prop := ∃ n, ∃ τ ∈ Γ n, Ty.Occurs σ τ

end Ctx

/-! ## 2.2 Syntax -/

/-- Distributive terms: `t ::= x^τ | λ^ℓ x. t | t [t₁, …, tₙ]`. -/
inductive DTerm
  | var (n : ℕ) (τ : Ty)
  | lam (ℓ : Label) (t : DTerm)
  | app (t : DTerm) (args : List DTerm)
  deriving Repr

namespace DTerm

/-- `s` is a sub-term of `t`. -/
inductive Sub : DTerm → DTerm → Prop
  | refl (t : DTerm) : Sub t t
  | lam {s t : DTerm} (ℓ : Label) : Sub s t → Sub s (.lam ℓ t)
  | fn {s t : DTerm} (ss : List DTerm) : Sub s t → Sub s (.app t ss)
  | arg {s u : DTerm} (t : DTerm) {ss : List DTerm} : u ∈ ss → Sub s u → Sub s (.app t ss)

/-- The labels decorating the λs of a term, one per λ (so repetitions are kept). -/
def lamLabels : DTerm → List Label
  | var _ _ => []
  | lam ℓ t => ℓ :: lamLabels t
  | app t ss => lamLabels t ++ ss.flatMap lamLabels

/-- The number of λs of a term, `d(t)` in the proof of termination. -/
def size : DTerm → ℕ
  | var _ _ => 0
  | lam _ t => size t + 1
  | app t ss => size t + (ss.map size).sum

/-- The types of the free occurrences of the variable `k`, `𝓜_x(t)`. -/
def occTypes : DTerm → ℕ → List Ty
  | var n τ, k => if n = k then [τ] else []
  | lam _ t, k => occTypes t (k + 1)
  | app t ss, k => occTypes t k ++ ss.flatMap (occTypes · k)

/-- The type of a term, computed syntactically. By `hasType_ty` this is *the* type of any
typable term. -/
def ty : DTerm → Ty
  | var _ τ => τ
  | lam ℓ t => .arrow (Ty.canon (occTypes t 0)) ℓ (ty t)
  | app t _ =>
    match ty t with
    | .arrow _ _ τ => τ
    | τ => τ

/-- The typing context of a term, computed syntactically (see `linearity`). -/
def ctx (t : DTerm) : Ctx := fun n => (t.occTypes n : Multiset Ty)

end DTerm

/-! ### Typing rules -/

mutual
/-- The distributive type system: rules `var`, `→I`, `→E`. -/
inductive HasType : Ctx → DTerm → Ty → Prop
  | var (n : ℕ) (τ : Ty) : HasType (Ctx.single n {τ}) (.var n τ) τ
  | lam {Γ : Ctx} {M : Multiset Ty} {σ : Ty} {t : DTerm} (ℓ : Label) :
      HasType (Ctx.cons M Γ) t σ → HasType Γ (.lam ℓ t) (.arrow (Ty.canon M) ℓ σ)
  | app {Γ : Ctx} {t : DTerm} {L : List Ty} {ℓ : Label} {τ : Ty}
      {Δs : List Ctx} {ss : List DTerm} {σs : List Ty} :
      HasType Γ t (.arrow L ℓ τ) → HasTypeMulti Δs ss σs → σs.Perm L →
      HasType (Γ + Δs.sum) (.app t ss) τ
/-- The judgment `[Γ₁, …, Γₙ] ⊢ [t₁, …, tₙ] : [τ₁, …, τₙ]` (rule `t-multi`). -/
inductive HasTypeMulti : List Ctx → List DTerm → List Ty → Prop
  | nil : HasTypeMulti [] [] []
  | cons {Γ : Ctx} {t : DTerm} {τ : Ty} {Δs ts τs} :
      HasType Γ t τ → HasTypeMulti Δs ts τs → HasTypeMulti (Γ :: Δs) (t :: ts) (τ :: τs)
end

namespace DTerm

/-- `t` is typable. -/
def Typable (t : DTerm) : Prop := ∃ Γ τ, HasType Γ t τ

end DTerm

/-! ### Correctness -/

/-- **Correct terms** (Definition "Correct term"): typable, plus
1. uniquely labeled lambdas;
2. sequential contexts;
3. sequential types. -/
structure Correct (t : DTerm) : Prop where
  typable : t.Typable
  uniquely_labeled : t.lamLabels.Nodup
  seq_ctx : ∀ s Γ τ, DTerm.Sub s t → HasType Γ s τ → Γ.Seq
  seq_ty : ∀ s Γ τ, DTerm.Sub s t → HasType Γ s τ → ∀ M ℓ ρ,
    (Ctx.Occurs (.arrow M ℓ ρ) Γ ∨ Ty.Occurs (.arrow M ℓ ρ) τ) → SeqMS (M : Multiset Ty)

/-- `𝒯^dist`: the set of correct terms. -/
def CTerm : Type := {t : DTerm // Correct t}

/-! ## 2.3 The calculus -/

namespace DTerm

/-- `shift d c t` adds `d` to every free index `≥ c`. -/
def shift (d : ℕ) : ℕ → DTerm → DTerm
  | c, var n τ => if n < c then var n τ else var (n + d) τ
  | c, lam ℓ t => lam ℓ (shift d (c + 1) t)
  | c, app t ss => app (shift d c t) (ss.map (shift d c))

/-- **Type-directed substitution** `t⟨k := s̄⟩` (the thesis' alternative definition): an
occurrence `k^τ` is replaced by the argument of `s̄` whose type is `τ`. The arguments live outside
the `k` binders crossed so far; indices above `k` are decremented. -/
def subst : DTerm → ℕ → List DTerm → DTerm
  | var n τ, k, ss =>
    if n < k then var n τ
    else if n = k then (((ss.find? fun s => decide (s.ty = τ))).map (shift k 0)).getD (var n τ)
    else var (n - 1) τ
  | lam ℓ t, k, ss => lam ℓ (subst t (k + 1) ss)
  | app t us, k, ss => app (subst t k ss) (us.map (subst · k ss))

end DTerm

mutual
/-- Resource-sensitive substitution, defined on raw terms. The application rule partitions
its arguments up to permutation; each argument is used exactly once. Unlike type-directed
lookup, this relation also handles repeated argument types. -/
inductive PSubst : DTerm → ℕ → List DTerm → DTerm → Prop
  | var_eq {s : DTerm} {Γ : Ctx} {τ : Ty} (k : ℕ) : HasType Γ s τ →
      PSubst (.var k τ) k [s] (s.shift k 0)
  | var_lt {n k : ℕ} (τ : Ty) : n < k → PSubst (.var n τ) k [] (.var n τ)
  | var_gt {n k : ℕ} (τ : Ty) : k < n → PSubst (.var n τ) k [] (.var (n - 1) τ)
  | lam {t u : DTerm} {k : ℕ} {ss : List DTerm} (ℓ : Label) :
      PSubst t (k + 1) ss u → PSubst (.lam ℓ t) k ss (.lam ℓ u)
  | app {t u : DTerm} {ts us ss ss₀ ss₁ : List DTerm} {k : ℕ} :
      PSubst t k ss₀ u → PSubstMulti ts k ss₁ us → (ss₀ ++ ss₁).Perm ss →
      PSubst (.app t ts) k ss (.app u us)
inductive PSubstMulti : List DTerm → ℕ → List DTerm → List DTerm → Prop
  | nil (k : ℕ) : PSubstMulti [] k [] []
  | cons {t u : DTerm} {ts us ss₀ ss₁ : List DTerm} {k : ℕ} :
      PSubst t k ss₀ u → PSubstMulti ts k ss₁ us →
      PSubstMulti (t :: ts) k (ss₀ ++ ss₁) (u :: us)
end

/-- One-hole contexts `C ::= □ | λ^ℓ x.C | C s̄ | t[s̄, C, ū]`. -/
inductive DCtx
  | hole
  | lam (ℓ : Label) (C : DCtx)
  | appL (C : DCtx) (ss : List DTerm)
  | appR (t : DTerm) (us : List DTerm) (C : DCtx) (vs : List DTerm)

namespace DCtx

/-- `C⟨t⟩` (capturing). -/
def plug : DCtx → DTerm → DTerm
  | hole, t => t
  | lam ℓ C, t => .lam ℓ (C.plug t)
  | appL C ss, t => .app (C.plug t) ss
  | appR t us C vs, s => .app t (us ++ C.plug s :: vs)

/-- Number of binders above the hole. -/
def depth : DCtx → ℕ
  | hole => 0
  | lam _ C => C.depth + 1
  | appL C _ => C.depth
  | appR _ _ C _ => C.depth

end DCtx

/-- The reduction relation `→ℓ` of λ^dist:
`C⟨(λ^ℓ x.t) s̄⟩ →ℓ C⟨t{x := s̄}⟩`. -/
inductive DStep : DTerm → Label → DTerm → Prop
  | beta (ℓ : Label) (t : DTerm) (ss : List DTerm) : DStep (.app (.lam ℓ t) ss) ℓ (t.subst 0 ss)
  | lam {t t' : DTerm} {ℓ : Label} (m : Label) : DStep t ℓ t' → DStep (.lam m t) ℓ (.lam m t')
  | appL {t t' : DTerm} {ℓ : Label} (ss : List DTerm) :
      DStep t ℓ t' → DStep (.app t ss) ℓ (.app t' ss)
  | appR {s s' : DTerm} {ℓ : Label} (t : DTerm) (us vs : List DTerm) :
      DStep s ℓ s' → DStep (.app t (us ++ s :: vs)) ℓ (.app t (us ++ s' :: vs))

/-- `→dist = ⋃ℓ →ℓ`. -/
def DRed (t u : DTerm) : Prop := ∃ ℓ, DStep t ℓ u

/-- Reduction restricted to correct terms. -/
def CRed (t u : CTerm) : Prop := DRed t.1 u.1

end Ch2Defs

/-! ## Chapter 2: A distributive λ-calculus (λ^dist) — Appendix

Auxiliary definitions and lemmas for Chapter 2:
* Structural induction `DTerm.ind`, type sequentiality `Ty.Sequential`, context operations
  (`Ctx.shift`, `Ctx.remove`, `Ctx.insert`).
* Unconditional syntactic typing determination (`hasType_ty`, `hasType_ctx`, `hasType_unique`).
* Partition-based substitution properties (`PSubst.exists`, `PSubst.occTypes`, `PSubst.inverse`),
  typing subject expansion (`subject_expansion`, `subject_expansion_subst`,
  `subject_expansion_typeDirected`), and counterexamples.
* Forward substitution typing and correctness, lambda conservation and size bounds.
* Substitution commutation and strong permutation, following the Chapter 2 appendices.
* Reduction/context correspondence and determinism by label. -/

section Ch2AppA

namespace Ty

/-- Every arrow domain occurring anywhere in this type is sequential. This does not
require all arrow labels in the type to be globally distinct. -/
def Sequential (τ : Ty) : Prop :=
  ∀ M ℓ ρ, Occurs (.arrow M ℓ ρ) τ → SeqMS (M : Multiset Ty)

theorem sequential_base (α : ℕ) (ℓ : Label) : Sequential (.base α ℓ) := by
  intro M m ρ h
  cases h

theorem Sequential.arrow {M : List Ty} {ℓ : Label} {ρ : Ty}
    (hM : SeqMS (M : Multiset Ty)) (hdom : ∀ τ ∈ M, Sequential τ)
    (hcod : Sequential ρ) : Sequential (.arrow M ℓ ρ) := by
  intro N m σ h
  cases h with
  | refl => exact hM
  | dom hm h => exact hdom _ hm _ _ _ h
  | cod h => exact hcod _ _ _ h

theorem Sequential.cod {M : List Ty} {ℓ : Label} {ρ : Ty}
    (h : Sequential (.arrow M ℓ ρ)) : Sequential ρ := by
  intro N m σ ho
  exact h _ _ _ (.cod ho)

end Ty

namespace Ctx

/-- Shift a context along the same insertion of indices as `DTerm.shift`. -/
def shift (d c : ℕ) (Γ : Ctx) : Ctx := fun n =>
  if n < c then Γ n else if n < c + d then 0 else Γ (n - d)

/-- Delete the variable at index `k`. -/
def remove (k : ℕ) (Γ : Ctx) : Ctx := fun n =>
  if n < k then Γ n else Γ (n + 1)

/-- Insert a variable with multiset `M` at index `k`. -/
def insert (k : ℕ) (M : Multiset Ty) (Γ : Ctx) : Ctx := fun n =>
  if n < k then Γ n else if n = k then M else Γ (n - 1)

@[simp] theorem shift_zero (d c : ℕ) : shift d c 0 = 0 := by
  funext n; simp [shift]

@[simp] theorem shift_add (d c : ℕ) (Γ Δ : Ctx) :
    shift d c (Γ + Δ) = shift d c Γ + shift d c Δ := by
  funext n; simp only [shift, Pi.add_apply]; split <;> simp_all
  split <;> simp_all

@[simp] theorem shift_sum (d c : ℕ) (Γs : List Ctx) :
    shift d c Γs.sum = (Γs.map (shift d c)).sum := by
  induction Γs with
  | nil => simp
  | cons Γ Γs ih => simp [ih]

@[simp] theorem shift_cons (d c : ℕ) (M : Multiset Ty) (Γ : Ctx) :
    shift d (c + 1) (cons M Γ) = cons M (shift d c Γ) := by
  funext n
  cases n with
  | zero => simp [shift, cons]
  | succ n =>
    simp only [shift, cons, Nat.add_lt_add_iff_right]
    split <;> rename_i h
    · simp
    · split <;> rename_i h'
      · simp [show n < c + d by omega]
      · have he : n + 1 - d = (n - d) + 1 := by omega
        simp [show ¬ n < c + d by omega, he]

@[simp] theorem shift_single (d c n : ℕ) (M : Multiset Ty) :
    shift d c (single n M) = single (if n < c then n else n + d) M := by
  funext m
  simp only [shift, single]
  split_ifs <;> first | rfl | omega

@[simp] theorem shift_succ_zero (k : ℕ) (Γ : Ctx) :
    shift (k + 1) 0 Γ = cons 0 (shift k 0 Γ) := by
  funext n
  cases n with
  | zero => simp [shift, cons]
  | succ n => simp [shift, cons, Nat.succ_sub_succ_eq_sub]

@[simp] theorem remove_zero (k : ℕ) : remove k 0 = 0 := by
  funext n; simp [remove]

@[simp] theorem remove_add (k : ℕ) (Γ Δ : Ctx) :
    remove k (Γ + Δ) = remove k Γ + remove k Δ := by
  funext n; simp [remove]; split <;> rfl

@[simp] theorem insert_remove (k : ℕ) (Γ : Ctx) : insert k (Γ k) (remove k Γ) = Γ := by
  funext n
  simp only [insert, remove]
  split <;> rename_i h
  · rfl
  · split <;> rename_i h'
    · subst n; rfl
    · have : n - 1 + 1 = n := by omega
      simp [show ¬ n - 1 < k by omega, this]

@[simp] theorem insert_zero (M : Multiset Ty) (Γ : Ctx) : insert 0 M Γ = cons M Γ := by
  funext n; cases n <;> simp [insert, cons]

@[simp] theorem shift_zero_cutoff (Γ : Ctx) : shift 0 0 Γ = Γ := by
  funext n; simp [shift]

@[simp] theorem remove_cons (k : ℕ) (M : Multiset Ty) (Γ : Ctx) :
    remove (k + 1) (cons M Γ) = cons M (remove k Γ) := by
  funext n; cases n <;> simp [remove, cons]

@[simp] theorem cons_add (M N : Multiset Ty) (Γ Δ : Ctx) :
    cons M Γ + cons N Δ = cons (M + N) (Γ + Δ) := by
  funext n; cases n <;> rfl

@[simp] theorem cons_zero : cons 0 0 = 0 := by
  funext n; cases n <;> rfl

@[simp] theorem remove_single (k n : ℕ) (M : Multiset Ty) (h : n ≠ k) :
    remove k (single n M) = single (if n < k then n else n - 1) M := by
  funext m
  simp only [remove, single]
  split <;> split <;> split <;> simp_all <;> omega

end Ctx

namespace DTerm

/-- Induction principle for `DTerm` (which is nested through `List`). -/
@[elab_as_elim]
theorem ind {P : DTerm → Prop}
    (var : ∀ n τ, P (.var n τ)) (lam : ∀ ℓ t, P t → P (.lam ℓ t))
    (app : ∀ t ss, P t → (∀ s ∈ ss, P s) → P (.app t ss)) : ∀ t, P t := by
  intro t
  induction t using DTerm.rec (motive_2 := fun ss => ∀ s ∈ ss, P s) with
  | var n τ => exact var n τ
  | lam ℓ t ih => exact lam ℓ t ih
  | app t ss ih ihs => exact app t ss ih ihs
  | nil => simp_all
  | cons s ss ih ihs =>
    rename_i x hx
    rcases List.mem_cons.1 hx with rfl | hx
    exacts [ih, ihs x hx]

end DTerm

/-! ### Unconditional typing determination -/

/-- For any typable term (without correctness assumptions), the context records the free
occurrence types of each variable. -/
theorem hasType_occTypes {Γ : Ctx} {t : DTerm} {τ : Ty} (h : HasType Γ t τ) (n : ℕ) :
    Γ n = (t.occTypes n : Multiset Ty) := by
  induction h using HasType.rec
    (motive_2 := fun Δs ts _ _ => ∀ n, Δs.sum n = ((ts.flatMap (DTerm.occTypes · n) : List Ty) : Multiset Ty))
    generalizing n with
  | var m σ =>
    simp only [Ctx.single, DTerm.occTypes]
    by_cases h : n = m
    · subst h; simp
    · simp [h, Ne.symm h]
  | lam ℓ _ ih => simpa [Ctx.cons, DTerm.occTypes] using ih (n + 1)
  | app _ _ _ ih ihs =>
    simp only [Pi.add_apply, DTerm.occTypes, ← Multiset.coe_add, ih n, ihs n]
  | nil => simp
  | cons _ _ ih ihs =>
    rename_i m
    simp [List.sum_cons, Pi.add_apply, ih m, ihs m]

/-- Every typing derivation gives the syntactically determined type. -/
theorem hasType_ty {Γ : Ctx} {t : DTerm} {τ : Ty} (h : HasType Γ t τ) :
    τ = t.ty := by
  induction h using HasType.rec (motive_2 := fun _ _ _ _ => True) with
  | var => rfl
  | @lam Γ M σ t ℓ h ih =>
    have hm := hasType_occTypes h 0
    change M = _ at hm
    simp only [DTerm.ty, ← ih, ← hm]
  | app _ _ _ ih _ => simp [DTerm.ty, ← ih]
  | nil => trivial
  | cons => trivial

/-- Every typing derivation gives the syntactically determined context. -/
theorem hasType_ctx {Γ : Ctx} {t : DTerm} {τ : Ty} (h : HasType Γ t τ) :
    Γ = t.ctx := funext (hasType_occTypes h)

/-- Typing is unique even without correctness. -/
theorem hasType_unique {Γ Γ' : Ctx} {t : DTerm} {τ τ' : Ty}
    (h : HasType Γ t τ) (h' : HasType Γ' t τ') : Γ = Γ' ∧ τ = τ' :=
  ⟨(hasType_ctx h).trans (hasType_ctx h').symm,
   (hasType_ty h).trans (hasType_ty h').symm⟩

/-- The computed type and context are those of the (unique) typing derivation. -/
theorem hasType_iff {Γ : Ctx} {t : DTerm} {τ : Ty} (ht : Correct t) :
    HasType Γ t τ ↔ Γ = t.ctx ∧ τ = t.ty := by
  constructor
  · intro h
    exact ⟨hasType_ctx h, hasType_ty h⟩
  · rintro ⟨rfl, rfl⟩
    obtain ⟨Δ, σ, h⟩ := ht.typable
    simpa only [hasType_ctx h, hasType_ty h] using h

namespace Ctx

/-- All types in a context have sequential arrow domains. -/
def TypesSequential (Γ : Ctx) : Prop := ∀ n τ, τ ∈ Γ n → τ.Sequential

theorem TypesSequential.add {Γ Δ : Ctx} (hΓ : Γ.TypesSequential)
    (hΔ : Δ.TypesSequential) : (Γ + Δ).TypesSequential := by
  intro n τ hm
  rcases Multiset.mem_add.mp hm with hm | hm
  · exact hΓ n τ hm
  · exact hΔ n τ hm

theorem typesSequential_zero : TypesSequential 0 := by simp [TypesSequential]

end Ctx

namespace Correct

theorem type_sequential {t : DTerm} (h : Correct t) {Γ : Ctx} {τ : Ty}
    (ht : HasType Γ t τ) : τ.Sequential := by
  intro M ℓ ρ ho
  exact h.seq_ty t Γ τ (.refl t) ht M ℓ ρ (.inr ho)

theorem context_typesSequential {t : DTerm} (h : Correct t) {Γ : Ctx} {τ : Ty}
    (ht : HasType Γ t τ) : Γ.TypesSequential := by
  intro n σ hm M ℓ ρ ho
  exact h.seq_ty t Γ τ (.refl t) ht M ℓ ρ (.inl ⟨n, σ, hm, ho⟩)

/-- A variable is correct exactly as far as the sequentiality of its annotated type allows. -/
theorem var (n : ℕ) {τ : Ty} (hτ : τ.Sequential) : Correct (.var n τ) := by
  refine ⟨⟨_, _, .var n τ⟩, by simp [DTerm.lamLabels], ?_, ?_⟩
  · intro s Γ σ hsub ht k
    cases hsub
    cases ht
    simp only [Ctx.single]
    split <;> simp [SeqMS]
  · intro s Γ σ hsub ht M ℓ ρ ho
    cases hsub
    cases ht
    rcases ho with ⟨k, υ, hm, ho⟩ | ho
    · by_cases hk : k = n
      · simp [Ctx.single, hk] at hm
        subst υ
        exact hτ M ℓ ρ ho
      · simp [Ctx.single, hk] at hm
    · exact hτ M ℓ ρ ho

end Correct

theorem HasTypeMulti.context_typesSequential {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) (hc : ∀ s ∈ ss, Correct s) : Γs.sum.TypesSequential := by
  induction ss generalizing Γs σs with
  | nil => cases hs; exact Ctx.typesSequential_zero
  | cons s ss ih =>
    cases hs with
    | cons h hs =>
      exact (hc s (by simp)).context_typesSequential h |>.add
        (ih hs (fun t ht => hc t (by simp [ht])))

/-- Correctness of an application follows from correct children, distinct lambda labels,
and sequentiality of the combined context. -/
theorem Correct.app {t : DTerm} {ss : List DTerm} {Γ : Ctx} {Δs : List Ctx}
    {L σs : List Ty} {ℓ : Label} {τ : Ty}
    (ht : HasType Γ t (.arrow L ℓ τ)) (hs : HasTypeMulti Δs ss σs) (hp : σs.Perm L)
    (hc : Correct t) (hcs : ∀ s ∈ ss, Correct s)
    (hlabels : (DTerm.app t ss).lamLabels.Nodup) (hctx : (Γ + Δs.sum).Seq) :
    Correct (.app t ss) := by
  have ha := HasType.app ht hs hp
  have hty := (hc.type_sequential ht).cod
  have hcts := (hc.context_typesSequential ht).add (hs.context_typesSequential hcs)
  refine ⟨⟨_, _, ha⟩, hlabels, ?_, ?_⟩
  · intro s Δ σ hsub h
    cases hsub with
    | refl => exact (hasType_unique h ha).1 ▸ hctx
    | fn _ hsub => exact hc.seq_ctx s Δ σ hsub h
    | arg _ hm hsub => exact (hcs _ hm).seq_ctx s Δ σ hsub h
  · intro s Δ σ hsub h M m ρ ho
    cases hsub with
    | refl =>
      obtain ⟨rfl, rfl⟩ := hasType_unique h ha
      rcases ho with ⟨n, υ, hm, ho⟩ | ho
      · exact hcts n υ hm M m ρ ho
      · exact hty M m ρ ho
    | fn _ hsub => exact hc.seq_ty s Δ σ hsub h M m ρ ho
    | arg _ hm hsub => exact (hcs _ hm).seq_ty s Δ σ hsub h M m ρ ho

namespace DTerm.Sub

theorem trans {s t u : DTerm} (hs : Sub s t) (ht : Sub t u) : Sub s u := by
  induction ht with
  | refl => exact hs
  | lam ℓ _ ih => exact .lam ℓ ih
  | fn ss _ ih => exact .fn ss ih
  | arg t hm _ ih => exact .arg t hm ih

theorem labels_arg {s : DTerm} {ss : List DTerm} (hm : s ∈ ss) :
    s.lamLabels.Sublist (ss.flatMap DTerm.lamLabels) := by
  induction ss with
  | nil => simp at hm
  | cons a ss ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact List.sublist_append_left _ _
    · exact (ih hm).trans (List.sublist_append_right _ _)

theorem lamLabels_sublist {s t : DTerm} (hs : Sub s t) :
    s.lamLabels.Sublist t.lamLabels := by
  induction hs with
  | refl => exact .refl _
  | lam ℓ _ ih => simpa only [DTerm.lamLabels] using ih.cons ℓ
  | fn ss _ ih => simpa only [DTerm.lamLabels] using ih.trans (List.sublist_append_left _ _)
  | arg t hm _ ih =>
    simpa only [DTerm.lamLabels] using
      ih.trans ((labels_arg hm).trans (List.sublist_append_right _ _))

end DTerm.Sub

theorem HasTypeMulti.typable_of_mem {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) {s : DTerm} (hm : s ∈ ss) : s.Typable := by
  induction ss generalizing Γs σs with
  | nil => simp at hm
  | cons t ss ih =>
    cases hs with
    | cons ht hs =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨_, _, ht⟩
      · exact ih hs hm

theorem DTerm.Sub.typable {s t : DTerm} (hs : Sub s t) (ht : t.Typable) : s.Typable := by
  induction hs with
  | refl => exact ht
  | lam ℓ _ ih =>
    obtain ⟨Γ, τ, h⟩ := ht
    cases h with
    | lam _ h => exact ih ⟨_, _, h⟩
  | fn ss _ ih =>
    obtain ⟨Γ, τ, h⟩ := ht
    cases h with
    | app h _ _ => exact ih ⟨_, _, h⟩
  | arg t hm _ ih =>
    obtain ⟨Γ, τ, h⟩ := ht
    cases h with
    | app _ hs _ => exact ih (hs.typable_of_mem hm)

theorem Correct.sub {s t : DTerm} (ht : Correct t) (hs : DTerm.Sub s t) : Correct s where
  typable := hs.typable ht.typable
  uniquely_labeled := hs.lamLabels_sublist.nodup ht.uniquely_labeled
  seq_ctx u Γ τ hu h := ht.seq_ctx u Γ τ (hu.trans hs) h
  seq_ty u Γ τ hu h M ℓ ρ ho := ht.seq_ty u Γ τ (hu.trans hs) h M ℓ ρ ho

/-! ### Shifting, partitioning, and typing subject expansion -/

/-- Typing is preserved by shifting free variables. -/
theorem HasType.shift {Γ : Ctx} {t : DTerm} {τ : Ty} (h : HasType Γ t τ)
    (d c : ℕ) : HasType (Γ.shift d c) (t.shift d c) τ := by
  induction h using HasType.rec
    (motive_2 := fun Δs ts σs _ => ∀ c,
      HasTypeMulti (Δs.map (Ctx.shift d c)) (ts.map (DTerm.shift d c)) σs)
    generalizing c with
  | var n τ =>
    simp only [DTerm.shift, Ctx.shift_single]
    split <;> exact HasType.var _ _
  | lam ℓ _ ih =>
    simpa only [DTerm.shift] using
      HasType.lam ℓ (by simpa only [Ctx.shift_cons] using ih (c + 1))
  | app _ _ hp ih ihs =>
    simpa only [DTerm.shift, Ctx.shift_add, Ctx.shift_sum] using
      HasType.app (ih c) (ihs c) hp
  | nil => exact HasTypeMulti.nil
  | cons _ _ ih ihs =>
    rename_i c
    exact HasTypeMulti.cons (ih c) (ihs c)

namespace HasTypeMulti

theorem append {Γs Δs : List Ctx} {ts ss : List DTerm} {τs σs : List Ty}
    (ht : HasTypeMulti Γs ts τs) (hs : HasTypeMulti Δs ss σs) :
    HasTypeMulti (Γs ++ Δs) (ts ++ ss) (τs ++ σs) := by
  induction ts generalizing Γs τs with
  | nil => cases ht; exact hs
  | cons t ts ih =>
    cases ht with
    | cons h ht => exact .cons h (ih ht)

/-- Reordering arguments also reorders their contexts and types. -/
theorem perm {Γs : List Ctx} {ts ss : List DTerm} {τs : List Ty}
    (ht : HasTypeMulti Γs ts τs) (hp : ts.Perm ss) :
    ∃ Δs σs, HasTypeMulti Δs ss σs ∧ Δs.Perm Γs ∧ σs.Perm τs := by
  induction hp generalizing Γs τs with
  | nil =>
    cases ht
    exact ⟨[], [], .nil, .nil, .nil⟩
  | cons t hp ih =>
    cases ht with
    | cons h hs =>
      obtain ⟨Δs, σs, h', hΔ, hσ⟩ := ih hs
      exact ⟨_ :: Δs, _ :: σs, .cons h h', hΔ.cons _, hσ.cons _⟩
  | swap t s ts =>
    cases ht with
    | cons h hs =>
      cases hs with
      | cons h' hs => exact ⟨_, _, .cons h' (.cons h hs), .swap .., .swap ..⟩
  | trans hp hp' ih ih' =>
    obtain ⟨Δs, σs, h, hΔ, hσ⟩ := ih ht
    obtain ⟨Ξs, ρs, h', hΞ, hρ⟩ := ih' h
    exact ⟨Ξs, ρs, h', hΞ.trans hΔ, hρ.trans hσ⟩

/-- The type list of a typed list is determined by its terms. -/
theorem types_eq {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) : σs = ss.map DTerm.ty := by
  induction ss generalizing Γs σs with
  | nil => cases hs; rfl
  | cons s ss ih =>
    cases hs with
    | cons h hs => simp only [List.map_cons, ← hasType_ty h, ← ih hs]

theorem perm_types {Γs : List Ctx} {ss : List DTerm} {σs τs : List Ty}
    (hs : HasTypeMulti Γs ss σs) (hp : σs.Perm τs) :
    ∃ Δs ts, HasTypeMulti Δs ts τs ∧ Δs.Perm Γs ∧ ts.Perm ss := by
  induction hp generalizing Γs ss with
  | nil => cases hs; exact ⟨[], [], .nil, .nil, .nil⟩
  | cons τ hp ih =>
    cases hs with
    | cons h hs =>
      obtain ⟨Δs, ts, h', hΔ, hts⟩ := ih hs
      exact ⟨_ :: Δs, _ :: ts, .cons h h', hΔ.cons _, hts.cons _⟩
  | swap σ τ τs =>
    cases hs with
    | cons h hs =>
      cases hs with
      | cons h' hs => exact ⟨_, _, .cons h' (.cons h hs), .swap .., .swap ..⟩
  | trans hp hp' ih ih' =>
    obtain ⟨Δs, ts, h, hΔ, hts⟩ := ih hs
    obtain ⟨Ξs, us, h', hΞ, hus⟩ := ih' h
    exact ⟨Ξs, us, h', hΞ.trans hΔ, hus.trans hts⟩

theorem split_types {Γs : List Ctx} {ss : List DTerm} (σs τs : List Ty)
    (hs : HasTypeMulti Γs ss (σs ++ τs)) :
    ∃ Γs₀ Γs₁ ss₀ ss₁, Γs = Γs₀ ++ Γs₁ ∧ ss = ss₀ ++ ss₁ ∧
      HasTypeMulti Γs₀ ss₀ σs ∧ HasTypeMulti Γs₁ ss₁ τs := by
  induction σs generalizing Γs ss with
  | nil => exact ⟨[], Γs, [], ss, rfl, rfl, .nil, hs⟩
  | cons σ σs ih =>
    cases hs with
    | cons h hs =>
      obtain ⟨Γs₀, Γs₁, ss₀, ss₁, rfl, rfl, h₀, h₁⟩ := ih hs
      exact ⟨_ :: Γs₀, Γs₁, _ :: ss₀, ss₁, rfl, rfl, .cons h h₀, h₁⟩

/-- Split resources by a multiset equation, without assuming distinct argument types. -/
theorem partition {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) (M N : Multiset Ty) (hm : (σs : Multiset Ty) = M + N) :
    ∃ Γs₀ Γs₁ ss₀ ss₁, HasTypeMulti Γs₀ ss₀ (Ty.canon M) ∧
      HasTypeMulti Γs₁ ss₁ (Ty.canon N) ∧ (Γs₀ ++ Γs₁).Perm Γs ∧ (ss₀ ++ ss₁).Perm ss := by
  have hp : σs.Perm ((Ty.canon M) ++ (Ty.canon N)) :=
    Multiset.coe_eq_coe.mp (by simpa only [← Multiset.coe_add, Ty.coe_canon] using hm)
  obtain ⟨Δs, ts, h, hΔ, hts⟩ := hs.perm_types hp
  obtain ⟨Γs₀, Γs₁, ss₀, ss₁, rfl, rfl, h₀, h₁⟩ := h.split_types (Ty.canon M) (Ty.canon N)
  exact ⟨Γs₀, Γs₁, ss₀, ss₁, h₀, h₁, hΔ, hts⟩

/-- A replacement preserving every typing can be made at any position of a typed list. -/
theorem replace {u v : DTerm}
    (h : ∀ {Γ τ}, HasType Γ u τ → HasType Γ v τ)
    {Γs : List Ctx} {τs : List Ty} (us vs : List DTerm)
    (ht : HasTypeMulti Γs (us ++ u :: vs) τs) :
    HasTypeMulti Γs (us ++ v :: vs) τs := by
  induction us generalizing Γs τs with
  | nil =>
    cases ht with
    | cons hu hs => exact .cons (h hu) hs
  | cons t ts ih =>
    cases ht with
    | cons ht hs => exact .cons ht (ih hs)

end HasTypeMulti

/-- Exact occurrence matching and typable arguments suffice to construct a partition
substitution on raw terms. Correctness of the body is not assumed or smuggled into this
construction: it must be established separately when needed. -/
theorem PSubst.exists {t : DTerm} {k : ℕ} {Δs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Δs ss σs)
    (hm : (σs : Multiset Ty) = (t.occTypes k : Multiset Ty)) :
    ∃ u, PSubst t k ss u := by
  induction t using DTerm.rec
    (motive_2 := fun ts => ∀ k {Δs ss σs}, HasTypeMulti Δs ss σs →
      (σs : Multiset Ty) = (ts.flatMap (DTerm.occTypes · k) : Multiset Ty) →
      ∃ us ss', PSubstMulti ts k ss' us ∧ ss'.Perm ss)
    generalizing k Δs ss σs with
  | var n τ =>
    by_cases hn : n = k
    · subst n
      have hσ : σs = [τ] := List.perm_singleton.mp
        (Multiset.coe_eq_coe.mp (by simpa [DTerm.occTypes] using hm))
      subst σs
      cases hs with
      | cons h hs =>
        cases hs
        exact ⟨_, .var_eq k h⟩
    · have hσ : σs = [] := by simpa [DTerm.occTypes, hn] using hm
      subst σs
      cases hs
      by_cases hlt : n < k
      · exact ⟨_, .var_lt τ hlt⟩
      · exact ⟨_, .var_gt τ (by omega)⟩
  | lam ℓ t ih =>
    obtain ⟨u, h⟩ := ih hs (by simpa only [DTerm.occTypes] using hm)
    exact ⟨_, .lam ℓ h⟩
  | app t ts ih ihs =>
    obtain ⟨Δs₀, Δs₁, ss₀, ss₁, h₀, h₁, _, hp⟩ := hs.partition
      (t.occTypes k : Multiset Ty) (ts.flatMap (DTerm.occTypes · k) : Multiset Ty)
      (by simpa only [DTerm.occTypes, ← Multiset.coe_add] using hm)
    obtain ⟨u, hu⟩ := ih h₀ (Ty.coe_canon _)
    obtain ⟨us, ss₁', hus, hperm⟩ := ihs k h₁ (Ty.coe_canon _)
    exact ⟨_, .app hu hus (((List.Perm.refl ss₀).append hperm).trans hp)⟩
  | nil =>
    rename_i k Δs ss σs hs hm
    have hσ : σs = [] := by simpa using hm
    subst σs
    cases hs
    exact ⟨[], [], .nil k, .nil⟩
  | cons t ts ih ihs =>
    rename_i k Δs ss σs hs hm
    obtain ⟨Δs₀, Δs₁, ss₀, ss₁, h₀, h₁, _, hp⟩ := hs.partition
      (t.occTypes k : Multiset Ty) (ts.flatMap (DTerm.occTypes · k) : Multiset Ty)
      (by simpa only [List.flatMap_cons, ← Multiset.coe_add] using hm)
    obtain ⟨u, hu⟩ := ih h₀ (Ty.coe_canon _)
    obtain ⟨us, ss₁', hus, hperm⟩ := ihs k h₁ (Ty.coe_canon _)
    exact ⟨_, _, .cons hu hus, ((List.Perm.refl ss₀).append hperm).trans hp⟩

/-- The substitution relation enforces the thesis' implicit resource-matching condition. -/
theorem PSubst.occTypes {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) :
    (t.occTypes k : Multiset Ty) = (ss.map DTerm.ty : Multiset Ty) := by
  induction h using PSubst.rec
    (motive_2 := fun ts k ss _ _ =>
      (ts.flatMap (DTerm.occTypes · k) : Multiset Ty) = (ss.map DTerm.ty : Multiset Ty)) with
  | var_eq k hs => simp [DTerm.occTypes, ← hasType_ty hs]
  | var_lt τ h => simp [DTerm.occTypes, Nat.ne_of_lt h]
  | var_gt τ h => simp [DTerm.occTypes, Ne.symm (Nat.ne_of_lt h)]
  | lam _ _ ih => simpa only [DTerm.occTypes] using ih
  | app _ _ hp ih ihs =>
    simp only [DTerm.occTypes, ← Multiset.coe_add, ih, ihs]
    exact Multiset.coe_eq_coe.mpr (by simpa using hp.map DTerm.ty)
  | nil => rfl
  | cons _ _ ih ihs => simp [← Multiset.coe_add, ih, ihs]

/-- Inverting a partition substitution reconstructs the body's typing and all consumed
arguments, with an exact decomposition of the resulting context. -/
theorem PSubst.inverse {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {ρ : Ty} (hu : HasType Γ u ρ) :
    ∃ Θ Δs σs, HasType Θ t ρ ∧ HasTypeMulti Δs ss σs ∧
      Θ k = (σs : Multiset Ty) ∧ Γ = Θ.remove k + Δs.sum.shift k 0 := by
  induction h using PSubst.rec
    (motive_2 := fun ts k ss us _ => ∀ {Γs ρs}, HasTypeMulti Γs us ρs →
      ∃ Θs Δs σs, HasTypeMulti Θs ts ρs ∧ HasTypeMulti Δs ss σs ∧
        Θs.sum k = (σs : Multiset Ty) ∧ Γs.sum = Θs.sum.remove k + Δs.sum.shift k 0)
    generalizing Γ ρ with
  | @var_eq s Δ τ k hs =>
    obtain ⟨hΓ, hρ⟩ := hasType_unique hu (hs.shift k 0)
    subst Γ
    subst ρ
    refine ⟨Ctx.single k {τ}, [Δ], [τ], .var k τ, .cons hs .nil, ?_, ?_⟩
    · simp [Ctx.single]
    · have hz : (Ctx.single k {τ}).remove k = 0 := by
        funext n
        simp only [Ctx.remove, Ctx.single, Pi.zero_apply]
        split_ifs <;> first | rfl | omega
      simp [hz]
  | @var_lt n k τ hlt =>
    cases hu
    refine ⟨Ctx.single n {τ}, [], [], .var n τ, .nil, ?_, ?_⟩
    · simp [Ctx.single, show k ≠ n by omega]
    · simp [Ctx.remove_single k n {τ} (by omega), hlt]
  | @var_gt n k τ hgt =>
    cases hu
    refine ⟨Ctx.single n {τ}, [], [], .var n τ, .nil, ?_, ?_⟩
    · simp [Ctx.single, show k ≠ n by omega]
    · simp [Ctx.remove_single k n {τ} (by omega), show ¬ n < k by omega]
  | @lam t u k ss ℓ h ih =>
    cases hu with
    | @lam Γ M ρ _ _ hu =>
      obtain ⟨Θ, Δs, σs, ht, hs, hm, he⟩ := ih hu
      let Θ' : Ctx := fun n => Θ (n + 1)
      have hzero : M = Θ 0 := by
        have := congrFun he 0
        simpa [Ctx.cons, Ctx.remove, Ctx.shift, -Ctx.shift_sum] using this
      have hcons : Θ = Ctx.cons M Θ' := by
        funext n
        cases n with
        | zero => exact hzero.symm
        | succ n => rfl
      refine ⟨Θ', Δs, σs, .lam ℓ (hcons ▸ ht), hs, hm, ?_⟩
      rw [hcons, Ctx.remove_cons, Ctx.shift_succ_zero, Ctx.cons_add] at he
      exact funext fun n => congrFun he (n + 1)
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    cases hu with
    | app hu hus hperm =>
      obtain ⟨Θ, Δs, σs, ht, hss, hm, he⟩ := ih hu
      obtain ⟨Θs, Ξs, τs, hts, hss', hm', he'⟩ := ihs hus
      obtain ⟨Ωs, υs, hss'', hΩ, hυ⟩ := (hss.append hss').perm hp
      refine ⟨Θ + Θs.sum, Ωs, υs, .app ht hts hperm, hss'', ?_, ?_⟩
      · simpa only [Pi.add_apply, hm, hm', Multiset.coe_add] using
          (Multiset.coe_eq_coe.mpr hυ).symm
      · rw [hΩ.sum_eq, List.sum_append, Ctx.shift_add, he, he', Ctx.remove_add]
        ac_rfl
  | nil k =>
    rename_i Γs ρs hu
    cases hu
    exact ⟨[], [], [], .nil, .nil, rfl, by simp⟩
  | @cons t u ts us ss₀ ss₁ k h hs ih ihs =>
    rename_i Γs ρs hu
    cases hu with
    | cons hu hus =>
      obtain ⟨Θ, Δs, σs, ht, hss, hm, he⟩ := ih hu
      obtain ⟨Θs, Ξs, τs, hts, hss', hm', he'⟩ := ihs hus
      refine ⟨Θ :: Θs, Δs ++ Ξs, σs ++ τs, .cons ht hts, hss.append hss', ?_, ?_⟩
      · simp only [List.sum_cons, Pi.add_apply, hm, hm', Multiset.coe_add]
      · simp only [List.sum_cons, List.sum_append, Ctx.remove_add, Ctx.shift_add]
        rw [he, he']
        ac_rfl

/-- Subject expansion at the contracted redex, without a correctness assumption. -/
theorem subject_expansion_beta {t u : DTerm} {ss : List DTerm} {Γ : Ctx} {τ : Ty}
    (ℓ : Label) (hs : PSubst t 0 ss u) (hu : HasType Γ u τ) :
    HasType Γ (.app (.lam ℓ t) ss) τ := by
  obtain ⟨Θ, Δs, σs, ht, hss, hm, he⟩ := hs.inverse hu
  have hbody : HasType (Ctx.cons (σs : Multiset Ty) (Θ.remove 0)) t τ := by
    rw [← Ctx.insert_zero, ← hm, Ctx.insert_remove]
    exact ht
  rw [he, Ctx.shift_zero_cutoff]
  exact .app (.lam ℓ hbody) hss (Multiset.coe_eq_coe.mp (Ty.coe_canon _).symm)

/-- Typing-preserving replacements remain so in any capturing one-hole context. -/
theorem DCtx.typing_mono (C : DCtx) {u v : DTerm}
    (h : ∀ {Γ τ}, HasType Γ u τ → HasType Γ v τ)
    {Γ : Ctx} {τ : Ty} (ht : HasType Γ (C.plug u) τ) :
    HasType Γ (C.plug v) τ := by
  induction C generalizing Γ τ with
  | hole => exact h ht
  | lam ℓ C ih =>
    cases ht with
    | lam _ ht => exact .lam ℓ (ih ht)
  | appL C ss ih =>
    cases ht with
    | app ht hs hp => exact .app (ih ht) hs hp
  | appR t us C vs ih =>
    cases ht with
    | app ht hs hp => exact .app ht (hs.replace (fun h => ih h) us vs) hp

/-- **Subject expansion** for partition-based substitution, including under binders and
in argument positions. This is a typing theorem on raw terms; it asserts no preservation
of correctness.

**Gap (imprecise, Lemma A.16).** `08-15-has-hnf-has-refinement.tex` (lines 22–26) leaves implicit that the arguments are typable and that their types match the occurrences of `x`, `T_x(t) = T(s⃗)` (in the thesis this hides in the partial operation `t{x := s⃗}`), and does not say which substitution is meant. With the type-directed substitution `DTerm.subst` the statement is false when `s⃗` has repeated types (`typeDirected_subject_expansion_counterexample`). We state it for the partition-based relation `PSubst`, which records the matching and typability, and show `PSubst` agrees with `DTerm.subst` under sequentiality (`PSubst.eq_subst`).

**Gap (proof gap, Lemma A.20).** `03-03-the-calculus.tex` (line 23) defines `t{x := s⃗}` only on correct terms, yet `refinement_substitution_inverse` invokes subject expansion in order to prove that `(λ^ℓ x. t')s⃗'` is correct, which is circular. Here subject expansion is a typing statement on raw terms, with no correctness hypothesis. -/
theorem subject_expansion {t u : DTerm} {ss : List DTerm} {Γ : Ctx} {τ : Ty}
    (C : DCtx) (ℓ : Label) (hs : PSubst t 0 ss u) (hu : HasType Γ (C.plug u) τ) :
    HasType Γ (C.plug (.app (.lam ℓ t) ss)) τ :=
  C.typing_mono (fun h => subject_expansion_beta ℓ hs h) hu

private theorem find_type {ss : List DTerm} {s : DTerm}
    (hnd : (ss.map DTerm.ty).Nodup) (hs : s ∈ ss) :
    ss.find? (fun t => decide (t.ty = s.ty)) = some s := by
  classical
  induction ss with
  | nil => simp at hs
  | cons t ts ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hs with rfl | hs
    · simp
    · have hne : t.ty ≠ s.ty := by
        intro he
        exact hnd.1 (List.mem_map.mpr ⟨s, hs, he.symm⟩)
      simp [hne, ih hnd.2 hs]

/-- Partition substitution agrees with type-directed lookup in any environment containing
its resources, provided the environment has distinct argument types. -/
theorem PSubst.eq_subst_of_subset {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) (env : List DTerm) (hsub : ss ⊆ env)
    (hnd : (env.map DTerm.ty).Nodup) : u = t.subst k env := by
  classical
  induction h using PSubst.rec
    (motive_2 := fun ts k ss us _ => ss ⊆ env →
      us = ts.map (fun t => t.subst k env)) with
  | @var_eq s Γ τ k hs =>
    have hm : s ∈ env := hsub (by simp)
    simp [DTerm.subst, hasType_ty hs, find_type hnd hm]
  | var_lt τ h => simp [DTerm.subst, h]
  | @var_gt n k τ h => simp [DTerm.subst, show ¬ n < k by omega,
      show ¬ n = k by omega]
  | lam ℓ h ih => simpa only [DTerm.subst] using congrArg (DTerm.lam ℓ) (ih hsub)
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    have h₀ : ss₀ ⊆ env := fun _ hm => hsub (hp.subset (List.mem_append_left _ hm))
    have h₁ : ss₁ ⊆ env := fun _ hm => hsub (hp.subset (List.mem_append_right _ hm))
    simp only [DTerm.subst, ih h₀, ihs h₁]
  | nil => rfl
  | @cons t u ts us ss₀ ss₁ k h hs ih ihs =>
    rename_i hsub
    have h₀ : ss₀ ⊆ env := fun _ hm => hsub (List.mem_append_left _ hm)
    have h₁ : ss₁ ⊆ env := fun _ hm => hsub (List.mem_append_right _ hm)
    simp only [List.map_cons, ih h₀, ihs h₁]

/-- Subject expansion for type-directed substitution with a sequential partition witness. -/
theorem subject_expansion_subst {t u : DTerm} {ss : List DTerm} {Γ : Ctx} {τ : Ty}
    (C : DCtx) (ℓ : Label) (hp : PSubst t 0 ss u)
    (hseq : SeqMS (ss.map DTerm.ty : Multiset Ty))
    (hu : HasType Γ (C.plug (t.subst 0 ss)) τ) :
    HasType Γ (C.plug (.app (.lam ℓ t) ss)) τ := by
  have he : u = t.subst 0 ss :=
    hp.eq_subst_of_subset ss (fun _ h => h)
      (List.Nodup.of_map (f := Ty.label) (by simpa [SeqMS] using hseq))
  exact subject_expansion C ℓ hp (he.symm ▸ hu)

/-- The type-directed typing expansion theorem with explicit, checkable resource
conditions. No partition witness or correctness assumption on the redex is needed. -/
theorem subject_expansion_typeDirected {t : DTerm} {ss : List DTerm} {Δs : List Ctx}
    {σs : List Ty} {Γ : Ctx} {τ : Ty} (C : DCtx) (ℓ : Label)
    (hs : HasTypeMulti Δs ss σs)
    (hm : (σs : Multiset Ty) = (t.occTypes 0 : Multiset Ty))
    (hseq : SeqMS (σs : Multiset Ty))
    (hu : HasType Γ (C.plug (t.subst 0 ss)) τ) :
    HasType Γ (C.plug (.app (.lam ℓ t) ss)) τ := by
  obtain ⟨u, hp⟩ := PSubst.exists hs hm
  apply subject_expansion_subst C ℓ hp _ hu
  simpa only [← hs.types_eq] using hseq

end Ch2AppA

end CiruelosLic
