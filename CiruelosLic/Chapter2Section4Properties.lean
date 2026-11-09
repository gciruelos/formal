import Mathlib
import CiruelosLic.Chapter2Section1Calculus

/-!
# Chapter 2 (§2.4): basic properties, termination and confluence

Contents:
* Chapter 2: Appendix (continued)
* Chapter 2: A distributive λ-calculus (λ^dist)
-/

namespace CiruelosLic

/-! ## Chapter 2: Appendix (continued)

Counterexamples, reduction and size helpers, substitution commutation, strong permutation. -/

section Ch2AppB

/-! ### Counterexamples -/

/-- The unrestricted type-directed analogue of subject expansion is false, even when the
body and arguments are typable and the argument types match all variable occurrences.
For `z[x][x]` and arguments `[a,b]` of the same type, lookup produces `z[a][a]`, whose
context cannot type the redex (it omits `b`). -/
theorem typeDirected_subject_expansion_counterexample :
    ∃ (t : DTerm) (ss : List DTerm) (Γ : Ctx) (τ : Ty),
      t.Typable ∧ (∀ s ∈ ss, s.Typable) ∧
      (t.occTypes 0 : Multiset Ty) = (ss.map DTerm.ty : Multiset Ty) ∧
      HasType Γ (t.subst 0 ss) τ ∧ ¬ HasType Γ (.app (.lam 4 t) ss) τ := by
  classical
  let τ := Ty.base 0 0
  let σ := Ty.base 1 1
  let ζ := Ty.arrow [τ] 2 (.arrow [τ] 3 σ)
  let t := DTerm.app (.app (.var 1 ζ) [.var 0 τ]) [.var 0 τ]
  let a := DTerm.var 1 τ
  let b := DTerm.var 2 τ
  let u := DTerm.app (.app (.var 0 ζ) [a]) [a]
  have ht : t.Typable := ⟨_, _,
    HasType.app (.app (.var 1 ζ) (.cons (.var 0 τ) .nil) (.refl _))
      (.cons (.var 0 τ) .nil) (.refl _)⟩
  have hu : HasType u.ctx u σ := by
    have h := HasType.app
      (HasType.app (.var 0 ζ) (.cons (.var 1 τ) .nil) (List.Perm.refl _))
      (.cons (.var 1 τ) .nil) (List.Perm.refl _)
    exact hasType_ctx h ▸ h
  have hsubst : t.subst 0 [a, b] = u := by
    simp [t, a, b, u, DTerm.subst, DTerm.ty, DTerm.shift]
  refine ⟨t, [a, b], u.ctx, σ, ht, ?_, ?_, hsubst ▸ hu, ?_⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨_, _, .var 1 τ⟩
    · exact ⟨_, _, .var 2 τ⟩
  · simp [t, a, b, DTerm.occTypes, DTerm.ty]
  · intro h
    have he := hasType_occTypes h 2
    simp [u, t, a, b, DTerm.ctx, DTerm.occTypes] at he

/-- Correctness permits repeated arrow labels: it controls domains, not global uniqueness
of type labels. Both arrows here have label `7`, but their domains are empty. -/
theorem correct_repeated_arrow_labels :
    Correct (.var 0 (.arrow [] 7 (.arrow [] 7 (.base 0 8)))) := by
  apply Correct.var
  apply Ty.Sequential.arrow (by simp [SeqMS]) (by simp)
  exact Ty.Sequential.arrow (by simp [SeqMS]) (by simp) (Ty.sequential_base 0 8)

/-- Typing subject expansion does not preserve correctness, even for exact resource
partitioning and a fresh lambda label. All old arrows in `ζ` have distinct labels (2 and 3),
but abstracting the two equal-labeled argument types introduces a nonsequential binder domain. -/
theorem correctness_subject_expansion_counterexample :
    ∃ (t u : DTerm) (ss : List DTerm) (Γ : Ctx) (τ : Ty) (ℓ : Label),
      PSubst t 0 ss u ∧ u = t.subst 0 ss ∧ HasType Γ u τ ∧ Correct u ∧ ℓ ∉ u.lamLabels ∧
      HasType Γ (.app (.lam ℓ t) ss) τ ∧ ¬ Correct (.app (.lam ℓ t) ss) := by
  let τ := Ty.base 0 0
  let υ := Ty.base 1 0
  let σ := Ty.base 2 1
  let ζ := Ty.arrow [τ] 2 (.arrow [υ] 3 σ)
  let t := DTerm.app (.app (.var 1 ζ) [.var 0 τ]) [.var 0 υ]
  let a := DTerm.app (.var 1 (.arrow [] 5 τ)) []
  let b := DTerm.app (.var 1 (.arrow [] 6 υ)) []
  let u := DTerm.app (.app (.var 0 ζ) [a]) [b]
  have hτ : τ.Sequential := Ty.sequential_base 0 0
  have hυ : υ.Sequential := Ty.sequential_base 1 0
  have hσ : σ.Sequential := Ty.sequential_base 2 1
  have hζ : ζ.Sequential := Ty.Sequential.arrow (by simp [SeqMS])
    (by simpa using hτ) (Ty.Sequential.arrow (by simp [SeqMS]) (by simpa using hυ) hσ)
  have ha : HasType (Ctx.single 1 {.arrow [] 5 τ}) a τ := by
    simpa using HasType.app (.var 1 (.arrow [] 5 τ)) .nil (List.Perm.refl [])
  have hb : HasType (Ctx.single 1 {.arrow [] 6 υ}) b υ := by
    simpa using HasType.app (.var 1 (.arrow [] 6 υ)) .nil (List.Perm.refl [])
  have ca : Correct a := by
    apply Correct.app (.var 1 (.arrow [] 5 τ)) .nil (.refl _)
      (Correct.var 1 (Ty.Sequential.arrow (by simp [SeqMS]) (by simp) hτ))
    · simp
    · simp [DTerm.lamLabels]
    · intro n
      simp only [List.sum_nil, add_zero, Ctx.single]
      split <;> simp [SeqMS]
  have cb : Correct b := by
    apply Correct.app (.var 1 (.arrow [] 6 υ)) .nil (.refl _)
      (Correct.var 1 (Ty.Sequential.arrow (by simp [SeqMS]) (by simp) hυ))
    · simp
    · simp [DTerm.lamLabels]
    · intro n
      simp only [List.sum_nil, add_zero, Ctx.single]
      split <;> simp [SeqMS]
  have hf := HasType.app (.var 0 ζ) (.cons ha .nil) (List.Perm.refl _)
  have hu := HasType.app hf (.cons hb .nil) (List.Perm.refl _)
  have cf : Correct (.app (.var 0 ζ) [a]) := by
    apply Correct.app (.var 0 ζ) (.cons ha .nil) (.refl _) (Correct.var 0 hζ)
    · intro s hs
      have : s = a := List.mem_singleton.mp hs
      subst s
      exact ca
    · simp [DTerm.lamLabels, a]
    · intro n
      rcases n with _ | _ | n <;> simp [Ctx.single, SeqMS, Ty.label]
  have cu : Correct u := by
    apply Correct.app hf (.cons hb .nil) (.refl _) cf
    · intro s hs
      have : s = b := List.mem_singleton.mp hs
      subst s
      exact cb
    · simp [DTerm.lamLabels, a, b]
    · intro n
      rcases n with _ | _ | _ | n <;> simp [Ctx.single, SeqMS, Ty.label]
  have hp : PSubst t 0 [a, b] u := by
    have hz : PSubst (.var 1 ζ) 0 [] (.var 0 ζ) := .var_gt ζ (by omega)
    have hsa : PSubst (.var 0 τ) 0 [a] a := by
      simpa [a, DTerm.shift] using PSubst.var_eq 0 ha
    have hsb : PSubst (.var 0 υ) 0 [b] b := by
      simpa [b, DTerm.shift] using PSubst.var_eq 0 hb
    exact .app (.app hz (.cons hsa (.nil 0)) (.refl _))
      (.cons hsb (.nil 0)) (.refl _)
  have he : u = t.subst 0 [a, b] :=
    hp.eq_subst_of_subset [a, b] (fun _ h => h) (by simp [a, b, DTerm.ty, τ, υ])
  refine ⟨t, u, [a, b], _, σ, 4, hp, he, hu, cu, ?_, subject_expansion_beta 4 hp hu, ?_⟩
  · simp [u, a, b, DTerm.lamLabels]
  · intro hc
    have ht := HasType.app
      (HasType.app (.var 1 ζ) (.cons (.var 0 τ) .nil) (List.Perm.refl _))
        (.cons (.var 0 υ) .nil) (List.Perm.refl _)
    have hseq := hc.seq_ctx t _ σ (.fn _ (.lam 4 (.refl t))) ht 0
    simp [Ctx.single, SeqMS, Ty.label, τ, υ] at hseq

/-- The correctness failure also occurs for the existing type-directed reduction itself;
it is not an artifact of extending substitution to a partition relation. -/
theorem correctness_dStep_expansion_counterexample :
    ∃ (t u : DTerm) (ℓ : Label) (Γ : Ctx) (τ : Ty),
      DStep t ℓ u ∧ HasType Γ u τ ∧ Correct u ∧ HasType Γ t τ ∧ ¬ Correct t := by
  obtain ⟨t, u, ss, Γ, τ, ℓ, _, he, hu, hc, _, ht, hn⟩ :=
    correctness_subject_expansion_counterexample
  refine ⟨_, u, ℓ, Γ, τ, ?_, hu, hc, ht, hn⟩
  simpa only [← he] using DStep.beta ℓ t ss

theorem DTerm.lamLabels_shift (t : DTerm) (d c : ℕ) :
    (t.shift d c).lamLabels = t.lamLabels := by
  induction t using DTerm.rec
    (motive_2 := fun ts => ∀ c,
      (ts.map (DTerm.shift d c)).flatMap DTerm.lamLabels = ts.flatMap DTerm.lamLabels)
    generalizing c with
  | var => simp only [DTerm.shift]; split <;> simp [DTerm.lamLabels]
  | lam ℓ t ih => simp [DTerm.shift, DTerm.lamLabels, ih]
  | app t ss ih ihs => simp [DTerm.shift, DTerm.lamLabels, ih, ihs]
  | nil => simp
  | cons t ts ih ihs =>
    rename_i c
    simp [ih c, ihs c]

/-- Partition substitution preserves every old lambda occurrence, without copying any. -/
theorem PSubst.lamLabels {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) :
    (u.lamLabels : Multiset Label) = (t.lamLabels : Multiset Label) +
      (ss.flatMap DTerm.lamLabels : Multiset Label) := by
  induction h using PSubst.rec
    (motive_2 := fun ts _ ss us _ =>
      (us.flatMap DTerm.lamLabels : Multiset Label) =
        (ts.flatMap DTerm.lamLabels : Multiset Label) +
        (ss.flatMap DTerm.lamLabels : Multiset Label)) with
  | var_eq k hs => simp [DTerm.lamLabels_shift, DTerm.lamLabels]
  | var_lt => simp [DTerm.lamLabels]
  | var_gt => simp [DTerm.lamLabels]
  | lam ℓ h ih =>
    simpa only [DTerm.lamLabels, ← Multiset.cons_coe, Multiset.cons_add] using
      congrArg (fun xs : Multiset Label => ℓ ::ₘ xs) ih
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    have hperm := Multiset.coe_eq_coe.mpr (hp.flatMap_right DTerm.lamLabels)
    simp only [List.flatMap_append, ← Multiset.coe_add] at hperm
    simp only [DTerm.lamLabels, ← Multiset.coe_add, ih, ihs]
    rw [← hperm]
    ac_rfl
  | nil => simp
  | cons h hs ih ihs =>
    simp only [List.flatMap_cons, List.flatMap_append, ← Multiset.coe_add, ih, ihs]
    ac_rfl

/-- Correctness of an abstraction follows from its correct body and fresh lambda label. -/
theorem Correct.lam {t : DTerm} {Γ : Ctx} {M : Multiset Ty} {τ : Ty} (ℓ : Label)
    (ht : HasType (Ctx.cons M Γ) t τ) (hc : Correct t)
    (hl : (ℓ :: t.lamLabels).Nodup) : Correct (.lam ℓ t) := by
  have ha := HasType.lam ℓ ht
  have hctx := hc.seq_ctx t _ τ (.refl t) ht
  have hct := hc.context_typesSequential ht
  have hty := Ty.Sequential.arrow (ℓ := ℓ) (M := Ty.canon M) (by simpa only [Ty.coe_canon, Ctx.cons] using hctx 0)
    (fun σ hm => hct 0 σ (by simpa only [Ty.mem_canon, Ctx.cons] using hm)) (hc.type_sequential ht)
  refine ⟨⟨_, _, ha⟩, by simpa only [DTerm.lamLabels] using hl, ?_, ?_⟩
  · intro s Δ σ hsub h n
    cases hsub with
    | refl => obtain ⟨rfl, rfl⟩ := hasType_unique h ha; exact hctx (n + 1)
    | lam _ hsub => exact hc.seq_ctx s Δ σ hsub h n
  · intro s Δ σ hsub h N m ρ ho
    cases hsub with
    | refl =>
      obtain ⟨rfl, rfl⟩ := hasType_unique h ha
      rcases ho with ⟨n, υ, hm, ho⟩ | ho
      · exact hct (n + 1) υ hm N m ρ ho
      · exact hty N m ρ ho
    | lam _ hsub => exact hc.seq_ty s Δ σ hsub h N m ρ ho

/-- Syntactically computed contexts coincide with the contexts of a multi-typing. -/
theorem HasTypeMulti.contexts_eq {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) : ss.map DTerm.ctx = Γs := by
  induction ss generalizing Γs σs with
  | nil => cases hs; rfl
  | cons s ss ih =>
    cases hs with
    | cons h hs => simp only [List.map_cons, ← hasType_ctx h, ih hs]

/-- Shifting preserves multi-typing. -/
theorem HasTypeMulti.shift {Γs : List Ctx} {ss : List DTerm} {σs : List Ty}
    (hs : HasTypeMulti Γs ss σs) (d c : ℕ) :
    HasTypeMulti (Γs.map (Ctx.shift d c)) (ss.map (DTerm.shift d c)) σs := by
  induction ss generalizing Γs σs with
  | nil => cases hs; exact .nil
  | cons s ss ih => cases hs with | cons h hs => exact .cons (h.shift d c) (ih hs)

/-- Shifting introduces only empty context entries. -/
theorem Ctx.Seq.shift {Γ : Ctx} (h : Γ.Seq) (d c : ℕ) : (Γ.shift d c).Seq := by
  intro n
  simp only [Ctx.shift]
  split
  · exact h n
  · split
    · simp [SeqMS]
    · exact h _

/-- Index shifting preserves all three correctness conditions. -/
theorem Correct.shift {t : DTerm} (hc : Correct t) (d c : ℕ) : Correct (t.shift d c) := by
  induction t using DTerm.ind generalizing c with
  | var n τ =>
    have hτ := hc.type_sequential (.var n τ)
    simp only [DTerm.shift]
    split <;> exact Correct.var _ hτ
  | lam ℓ t ih =>
    obtain ⟨Γ, τ, ht⟩ := hc.typable
    cases ht with
    | lam _ ht =>
      have hu := ht.shift d (c + 1)
      rw [Ctx.shift_cons] at hu
      simp only [DTerm.shift]

      exact Correct.lam ℓ hu (ih (hc.sub (.lam ℓ (.refl t))) (c + 1))
        (by simpa only [DTerm.lamLabels, DTerm.lamLabels_shift] using hc.uniquely_labeled)
  | app t ss ih ihs =>
    obtain ⟨Γ, τ, ht⟩ := hc.typable
    cases ht with
    | app ht hs hp =>
      simp only [DTerm.shift]

      apply Correct.app (ht.shift d c) (hs.shift d c) hp
        (ih (hc.sub (.fn ss (.refl t))) c)
      · intro s hm
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
        exact ihs s hs (hc.sub (.arg t hs (.refl s))) c
      · have hh := hc.uniquely_labeled
        rw [← DTerm.lamLabels_shift (.app t ss) d c] at hh
        simpa only [DTerm.shift] using hh
      · rw [← Ctx.shift_sum, ← Ctx.shift_add]
        exact (hc.seq_ctx _ _ _ (.refl _) (.app ht hs hp)).shift d c

/-- Forward typing for the resource partition substitution of `03-03-the-calculus.tex`. -/
theorem PSubst.typing {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {τ : Ty} (ht : HasType Γ t τ) :
    HasType (Γ.remove k + (ss.map DTerm.ctx).sum.shift k 0) u τ := by
  induction h using PSubst.rec
    (motive_2 := fun ts k ss us _ => ∀ {Γs τs}, HasTypeMulti Γs ts τs →
      ∃ Δs, HasTypeMulti Δs us τs ∧
        Δs.sum = Γs.sum.remove k + (ss.map DTerm.ctx).sum.shift k 0)
    generalizing Γ τ with
  | @var_eq s Δ τ k hs =>
    cases ht
    have hz : (Ctx.single k {τ}).remove k = 0 := by
      funext n; simp only [Ctx.remove, Ctx.single, Pi.zero_apply]
      split_ifs <;> first | rfl | omega
    simpa [hz, ← hasType_ctx hs] using hs.shift k 0
  | @var_lt n k τ hlt =>
    cases ht
    simpa [Ctx.remove_single k n {τ} (by omega), hlt] using HasType.var n τ
  | @var_gt n k τ hgt =>
    cases ht
    simpa [Ctx.remove_single k n {τ} (by omega), show ¬ n < k by omega] using HasType.var (n - 1) τ
  | lam ℓ _ ih =>
    cases ht with
    | lam _ ht =>
      have hu := ih ht
      rw [Ctx.remove_cons, Ctx.shift_succ_zero, Ctx.cons_add, add_zero] at hu
      exact HasType.lam ℓ hu
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    cases ht with
    | app ht hts hperm =>
      obtain ⟨Δs, hus, he⟩ := ihs hts
      have ha := HasType.app (ih ht) hus hperm
      have hp' := (hp.map DTerm.ctx).sum_eq
      simp only [List.map_append, List.sum_append] at hp'
      rw [he] at ha
      convert ha using 1
      rw [Ctx.remove_add, ← hp', Ctx.shift_add]
      ac_rfl
  | nil k =>
    rename_i Γs τs ht
    cases ht
    exact ⟨[], .nil, by simp⟩
  | cons _ _ ih ihs =>
    rename_i Γs τs ht
    cases ht with
    | cons ht hts =>
      obtain ⟨Δs, hus, he⟩ := ihs hts
      refine ⟨_ :: Δs, .cons (ih ht) hus, ?_⟩
      simp only [List.sum_cons, List.map_append, List.sum_append, Ctx.remove_add,
        Ctx.shift_add, he]
      ac_rfl

theorem PSubstMulti.typing {ts us : List DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubstMulti ts k ss us) {Γs : List Ctx} {τs : List Ty}
    (ht : HasTypeMulti Γs ts τs) :
    ∃ Δs, HasTypeMulti Δs us τs ∧
      Δs.sum = Γs.sum.remove k + (ss.map DTerm.ctx).sum.shift k 0 := by
  induction ts generalizing ss us Γs τs with
  | nil => cases h; cases ht; exact ⟨[], .nil, by simp⟩
  | cons t ts ih =>
    cases h with
    | cons h hs =>
      cases ht with
      | cons ht hts =>
        obtain ⟨Δs, hus, he⟩ := ih hs hts
        refine ⟨_ :: Δs, .cons (h.typing ht) hus, ?_⟩
        simp only [List.sum_cons, List.map_append, List.sum_append, Ctx.remove_add,
          Ctx.shift_add, he]
        ac_rfl

theorem SeqMS.of_le {M N : Multiset Ty} (h : M ≤ N) (hs : SeqMS N) : SeqMS M :=
  Multiset.nodup_of_le (Multiset.map_le_map h) hs

theorem Ctx.Seq.left {Γ Δ : Ctx} (h : (Γ + Δ).Seq) : Γ.Seq :=
  fun n => SeqMS.of_le (le_add_right le_rfl) (h n)

theorem Ctx.Seq.right {Γ Δ : Ctx} (h : (Γ + Δ).Seq) : Δ.Seq :=
  fun n => SeqMS.of_le (le_add_left le_rfl) (h n)

/-- Correctness of substitution: the resulting contexts are sequential and lambda
occurrences are distinct. These are the three checks in `08-03-subject-reduction.tex`. -/
theorem PSubst.correct {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) {Γ : Ctx} {τ : Ty} (ht : HasType Γ t τ)
    (hc : Correct t) (hcs : ∀ s ∈ ss, Correct s) (hl : u.lamLabels.Nodup)
    (hctx : (Γ.remove k + (ss.map DTerm.ctx).sum.shift k 0).Seq) : Correct u := by
  induction h using PSubst.rec
    (motive_2 := fun ts k ss us _ => ∀ {Γs τs}, HasTypeMulti Γs ts τs →
      (∀ t ∈ ts, Correct t) → (∀ s ∈ ss, Correct s) →
      (us.flatMap DTerm.lamLabels).Nodup →
      (Γs.sum.remove k + (ss.map DTerm.ctx).sum.shift k 0).Seq →
      ∀ u ∈ us, Correct u)
    generalizing Γ τ with
  | var_eq k hs => exact (hcs _ (by simp)).shift k 0
  | var_lt τ hlt => cases ht; exact Correct.var _ (hc.type_sequential (.var _ _))
  | var_gt τ hgt => cases ht; exact Correct.var _ (hc.type_sequential (.var _ _))
  | @lam t u k ss ℓ h ih =>
    cases ht with
    | lam _ ht =>
      have hu := h.typing ht
      rw [Ctx.remove_cons, Ctx.shift_succ_zero, Ctx.cons_add, add_zero] at hu
      simp only [DTerm.lamLabels] at hl
      apply Correct.lam ℓ hu _ hl
      apply ih ht (hc.sub (.lam ℓ (.refl t))) hcs (List.nodup_cons.mp hl).2
      intro n
      cases n with
      | zero =>
        simpa only [Ctx.remove_cons, Ctx.shift_succ_zero, Ctx.cons_add, add_zero, Ctx.cons] using
          hc.seq_ctx t _ _ (.lam ℓ (.refl t)) ht 0
      | succ n =>
        simpa only [Ctx.remove_cons, Ctx.shift_succ_zero, Ctx.cons_add, add_zero,
          Ctx.cons] using hctx n
  | @app t u ts us ss ss₀ ss₁ k h hs hp ih ihs =>
    cases ht with
    | @app Γ _ L m τ Γs _ σs ht hts hperm =>
      obtain ⟨Δs, hus, he⟩ := hs.typing hts
      have hu := h.typing ht
      have hsum : (Γ.remove k + (ss₀.map DTerm.ctx).sum.shift k 0) + Δs.sum =
          (Γ + Γs.sum).remove k + (ss.map DTerm.ctx).sum.shift k 0 := by
        rw [he, Ctx.remove_add, ← (hp.map DTerm.ctx).sum_eq,
          List.map_append, List.sum_append, Ctx.shift_add]
        ac_rfl
      have hctx' := hsum.symm ▸ hctx
      simp only [DTerm.lamLabels] at hl
      apply Correct.app hu hus hperm
      · exact ih ht (hc.sub (.fn ts (.refl t)))
          (fun s hm => hcs s (hp.subset (List.mem_append_left _ hm)))
          ((List.nodup_append.mp hl).1) hctx'.left
      · apply ihs hts (fun s hm => hc.sub (.arg t hm (.refl s)))
          (fun s hm => hcs s (hp.subset (List.mem_append_right _ hm)))
          ((List.nodup_append.mp hl).2.1)
        exact he ▸ hctx'.right
      · simpa only [DTerm.lamLabels] using hl
      · exact hctx'
  | nil => rename_i Γs τs ht hc hcs hl hctx u hu; cases ht; simp at hu
  | @cons t u ts us ss₀ ss₁ k h hs ih ihs =>
    rename_i Γs τs ht hc hcs hl hctx v hv
    cases ht with
    | @cons Γ _ σ Γs _ σs ht hts =>
      have he : (Γ.remove k + (ss₀.map DTerm.ctx).sum.shift k 0) +
          (Γs.sum.remove k + (ss₁.map DTerm.ctx).sum.shift k 0) =
          (Γ :: Γs).sum.remove k + ((ss₀ ++ ss₁).map DTerm.ctx).sum.shift k 0 := by
        simp only [List.sum_cons, Ctx.remove_add, List.map_append, List.sum_append,
          Ctx.shift_add]
        ac_rfl
      have hctx' := he.symm ▸ hctx
      simp only [List.flatMap_cons] at hl
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ih ht (hc _ (by simp)) (fun s hm => hcs s (by simp [hm]))
          (List.nodup_append.mp hl).1 hctx'.left
      · exact ihs hts (fun s hm => hc s (by simp [hm]))
          (fun s hm => hcs s (by simp [hm])) (List.nodup_append.mp hl).2.1 hctx'.right v hv

/-- Lambda counting is unchanged by index shifting. -/
theorem DTerm.size_shift (t : DTerm) (d c : ℕ) : (t.shift d c).size = t.size := by
  induction t using DTerm.rec
    (motive_2 := fun ts => ∀ c,
      ((ts.map (DTerm.shift d c)).map DTerm.size).sum = (ts.map DTerm.size).sum)
    generalizing c with
  | var => simp only [DTerm.shift]; split <;> simp [DTerm.size]
  | lam ℓ t ih => simp [DTerm.shift, DTerm.size, ih]
  | app t ts ih ihs => simp only [DTerm.shift, DTerm.size, ih, ihs]
  | nil => simp
  | cons t ts ih ihs => rename_i c; simpa only [List.map_cons, List.sum_cons, ih c] using congrArg (t.size + ·) (ihs c)

/-- The alternative substitution at a correct beta redex is an exact resource partition. -/
theorem Correct.beta_partition {ℓ : Label} {b : DTerm} {ss : List DTerm}
    (hc : Correct (.app (.lam ℓ b) ss)) : PSubst b 0 ss (b.subst 0 ss) := by
  obtain ⟨Γ, τ, ht⟩ := hc.typable
  cases ht with
  | @app Γ _ L m τ Δs _ σs hf hs hp =>
    cases hf with
    | @lam Γ M _ _ _ hb =>
      have hm := (Multiset.coe_eq_coe.mpr hp).trans (Ty.coe_canon M)
      have hocc := hasType_occTypes hb 0
      obtain ⟨u, hu⟩ := PSubst.exists (t := b) (k := 0) hs (hm.trans hocc)
      have hseq := hc.seq_ctx b _ _ (.fn ss (.lam ℓ (.refl b))) hb 0
      have hseq' : SeqMS (σs : Multiset Ty) := hm.symm ▸ hseq
      have hn : (ss.map DTerm.ty).Nodup := List.Nodup.of_map (f := Ty.label) (by
        simpa only [← hs.types_eq, SeqMS, Multiset.map_coe, Multiset.coe_nodup] using
          hseq')
      exact hu.eq_subst_of_subset ss (fun _ h => h) hn ▸ hu

/-- A step removes its lambda label and preserves every other lambda occurrence. -/
theorem DStep.lamLabels {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u) (hc : Correct t) :
    ℓ ::ₘ (u.lamLabels : Multiset Label) = (t.lamLabels : Multiset Label) := by
  induction h with
  | beta ℓ b ss =>
    have hh := hc.beta_partition.lamLabels
    simpa only [DTerm.lamLabels, ← Multiset.coe_add, ← Multiset.cons_coe,
      Multiset.cons_add] using congrArg (fun xs : Multiset Label => ℓ ::ₘ xs) hh
  | lam m h ih =>
    have hh := ih (hc.sub (.lam m (.refl _)))
    simp only [DTerm.lamLabels, ← Multiset.cons_coe]
    rw [Multiset.cons_swap, hh]
  | appL ss h ih =>
    have hh := ih (hc.sub (.fn ss (.refl _)))
    simp only [DTerm.lamLabels, ← Multiset.coe_add, ← Multiset.cons_add, hh]
  | @appR s s' ℓ t us vs h ih =>
    have hh := ih (hc.sub (.arg t (by simp) (.refl _)))
    simp only [DTerm.lamLabels, List.flatMap_append, List.flatMap_cons, ← Multiset.coe_add]
    calc
      _ = (t.lamLabels : Multiset Label) +
          ((us.flatMap DTerm.lamLabels : Multiset Label) +
            ((ℓ ::ₘ (s'.lamLabels : Multiset Label)) + (vs.flatMap DTerm.lamLabels : Multiset Label))) := by
              simp only [Multiset.cons_add, Multiset.add_cons]
      _ = _ := by rw [hh]

/-- Preservation of typing and correctness (`08-03-subject-reduction.tex`). -/
theorem DStep.subject_reduction {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u)
    (hc : Correct t) {Γ : Ctx} {τ : Ty} (ht : HasType Γ t τ) : HasType Γ u τ ∧ Correct u := by
  have hlabels : u.lamLabels.Nodup := by
    have hh := h.lamLabels hc
    have hn : (ℓ ::ₘ (u.lamLabels : Multiset Label)).Nodup := hh.symm ▸ hc.uniquely_labeled
    exact (Multiset.nodup_cons.mp hn).2
  induction h generalizing Γ τ with
  | beta ℓ b ss =>
    have hp := hc.beta_partition
    cases ht with
    | @app Γ _ L m τ Δs _ σs hf hs hperm =>
      cases hf with
      | @lam Γ M _ _ _ hb =>
        have he : (ss.map DTerm.ctx).sum = Δs.sum := congrArg List.sum hs.contexts_eq
        have hu := hp.typing hb
        simp only [he, Ctx.shift_zero_cutoff] at hu
        have hcctx := hc.seq_ctx _ _ _ (.refl _) (.app (.lam ℓ hb) hs hperm)
        refine ⟨hu, hp.correct hb (hc.sub (.fn ss (.lam ℓ (.refl b))))
          (fun s hm => hc.sub (.arg _ hm (.refl s))) hlabels ?_⟩
        simpa only [he, Ctx.shift_zero_cutoff, show (Ctx.cons M Γ).remove 0 = Γ from rfl] using hcctx
  | lam m h ih =>
    cases ht with
    | lam _ ht =>
      obtain ⟨hu, hcu⟩ := ih (hc.sub (.lam m (.refl _))) ht
        ((List.nodup_cons.mp (by simpa only [DTerm.lamLabels] using hlabels)).2)
      exact ⟨.lam m hu, Correct.lam m hu hcu (by simpa only [DTerm.lamLabels] using hlabels)⟩
  | appL ss h ih =>
    cases ht with
    | app ht hs hp =>
      obtain ⟨hu, hcu⟩ := ih (hc.sub (.fn ss (.refl _))) ht
        ((List.nodup_append.mp (by simpa only [DTerm.lamLabels] using hlabels)).1)
      exact ⟨.app hu hs hp, Correct.app hu hs hp hcu
        (fun s hm => hc.sub (.arg _ hm (.refl s))) hlabels
        (hc.seq_ctx _ _ _ (.refl _) (.app ht hs hp))⟩
  | @appR s s' ℓ t us vs h ih =>
    cases ht with
    | app ht hs hp =>
      have hcs := hc.sub (.arg t (by simp) (.refl s))
      obtain ⟨Ξ, σ, hv⟩ := hcs.typable
      have hlv := (DTerm.Sub.arg t (ss := us ++ s' :: vs) (by simp) (.refl s')).lamLabels_sublist.nodup hlabels
      obtain ⟨hu, hcu⟩ := ih hcs hv hlv
      have hus := HasTypeMulti.replace (fun hh => by
        obtain ⟨rfl, rfl⟩ := hasType_unique hh hv
        exact hu) us vs hs
      have ha := HasType.app ht hus hp
      refine ⟨ha, Correct.app ht hus hp (hc.sub (.fn _ (.refl t))) ?_ hlabels ?_⟩
      · intro s hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hc.sub (.arg t (by simp [hm]) (.refl s))
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact hcu
          · exact hc.sub (.arg t (by simp [hm]) (.refl s))
      · exact hc.seq_ctx _ _ _ (.refl _) (.app ht hs hp)

/-- The resource partition uses each argument exactly once (`08-05-termination.tex`). -/
theorem PSubst.size {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) : u.size = t.size + (ss.map DTerm.size).sum := by
  induction h using PSubst.rec
    (motive_2 := fun ts _ ss us _ => (us.map DTerm.size).sum =
      (ts.map DTerm.size).sum + (ss.map DTerm.size).sum) with
  | var_eq => simp [DTerm.size_shift, DTerm.size]
  | var_lt => simp [DTerm.size]
  | var_gt => simp [DTerm.size]
  | lam ℓ h ih => simp [DTerm.size, ih]; omega
  | app _ _ hp ih ihs =>
    have := (hp.map DTerm.size).sum_eq
    simp only [List.map_append, List.sum_append] at this
    simp only [DTerm.size, ih, ihs]
    omega
  | nil => simp
  | cons _ _ ih ihs => simp only [List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, ih, ihs]; omega

/-! ### Reduction and size helpers -/

namespace DTerm

/-- Inserting indices inside an already inserted gap just enlarges that gap. -/
theorem shift_gap (t : DTerm) (a b c d : ℕ) (hbc : b ≤ c) (hca : c ≤ b + a) :
    (t.shift a b).shift d c = t.shift (a + d) b := by
  induction t using DTerm.ind generalizing b c with
  | var n τ =>
    by_cases hn : n < b
    · simp [shift, hn, show n < c by omega]
    · simp only [shift, ite_eq_right hn, ite_eq_right (show ¬ n + a < c by omega)]
      congr 1; omega
  | lam ℓ t ih =>
    simp only [shift]
    rw [ih (b + 1) (c + 1) (by omega) (by omega)]
  | app t ts ih ihs =>
    simp only [shift, List.map_map]
    rw [ih b c hbc hca]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs b c hbc hca)

/-- Removing an index inside an inserted gap leaves a smaller gap. -/
theorem subst_shift_gap (t : DTerm) (d c i : ℕ) (ss : List DTerm)
    (hci : c ≤ i) (hid : i ≤ c + d) :
    (t.shift (d + 1) c).subst i ss = t.shift d c := by
  induction t using DTerm.ind generalizing c i with
  | var n τ =>
    by_cases hn : n < c
    · simp [shift, subst, hn, show n < i by omega]
    · simp only [shift, ite_eq_right hn, subst,
        ite_eq_right (show ¬ n + (d + 1) < i by omega),
        ite_eq_right (show ¬ n + (d + 1) = i by omega)]
      congr 1
  | lam ℓ t ih =>
    simp only [shift, subst]
    rw [ih (c + 1) (i + 1) (by omega) (by omega)]
  | app t ts ih ihs =>
    simp only [shift, subst, List.map_map]
    rw [ih c i hci hid]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs c i hci hid)

/-- Shifting below a substituted variable commutes with substitution. Arguments
are stored outside all crossed binders, as in the definition of `subst`. -/
theorem shift_subst (t : DTerm) (d c k : ℕ) (ss : List DTerm) (hck : c ≤ k) :
    (t.shift d c).subst (k + d) ss = (t.subst k ss).shift d c := by
  induction t using DTerm.ind generalizing c k with
  | var n τ =>
    by_cases hn : n < c
    · simp only [shift, ite_eq_left hn, subst, ite_eq_left (show n < k + d by omega),
        ite_eq_left (show n < k by omega)]
    · by_cases hnk : n < k
      · simp [shift, subst, hn, hnk, show n + d < k + d by omega]
      · by_cases he : n = k
        · subst n
          simp only [shift, ite_eq_right hn, subst, Nat.lt_irrefl, ↓reduceIte]
          cases hf : ss.find? (fun s => decide (s.ty = τ)) with
          | none => simp [shift, hn]
          | some s =>
            simp only [Option.map_some, Option.getD_some]
            exact (shift_gap s k 0 c d (by omega) (by omega)).symm
        · have hgt : k < n := by omega
          simp only [shift, ite_eq_right hn, subst,
            ite_eq_right (show ¬ n + d < k + d by omega),
            ite_eq_right (show ¬ n + d = k + d by omega), ite_eq_right (show ¬ n < k by omega),
            ite_eq_right he, ite_eq_right (show ¬ n - 1 < c by omega)]
          congr 1; omega
  | lam ℓ t ih =>
    simp only [shift, subst]
    rw [show k + d + 1 = (k + 1) + d by omega, ih (c + 1) (k + 1) (by omega)]
  | app t ts ih ihs =>
    simp only [shift, subst, List.map_map]
    rw [ih c k hck]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs c k hck)

/-- Every occurrence selected by the alternative substitution has a matching argument.
Unlike partition substitution, unused extra arguments are allowed. -/
def SubstDefined (t : DTerm) (k : ℕ) (ss : List DTerm) : Prop :=
  ∀ τ ∈ t.occTypes k, ∃ s ∈ ss, s.ty = τ

/-- With a type-preserving argument transformation, lookup commutes with `map`. -/
theorem find_type_map {ss : List DTerm} (f : DTerm → DTerm)
    (hf : ∀ s ∈ ss, (f s).ty = s.ty) (τ : Ty) :
    (ss.map f).find? (fun s => decide (s.ty = τ)) =
      (ss.find? (fun s => decide (s.ty = τ))).map f := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.find?_cons, hf s (by simp)]
    split
    · rfl
    · exact ih (fun u hu => hf u (by simp [hu]))

/-- Substitution commutation (`03-03-the-calculus.tex`, alternative substitution).
The first lookup must be defined, and substitution in the arguments must preserve
their types. There is no additional shift of `us`: arguments already live outside
all binders crossed by `subst`. -/
theorem subst_commute (t : DTerm) (i k : ℕ) (ss us : List DTerm)
    (hd : t.SubstDefined i ss)
    (ht : ∀ s ∈ ss, (s.subst k us).ty = s.ty) :
    (t.subst i ss).subst (i + k) us =
      (t.subst (i + k + 1) us).subst i (ss.map (·.subst k us)) := by
  induction t using DTerm.ind generalizing i with
  | var n τ =>
    by_cases hni : n < i
    · simp only [subst, ite_eq_left hni, ite_eq_left (show n < i + k by omega),
        ite_eq_left (show n < i + k + 1 by omega)]
    · by_cases he : n = i
      · subst n
        obtain ⟨s, hs, hty⟩ := hd τ (by simp [occTypes])
        have hf : (ss.find? (fun s => decide (s.ty = τ))).isSome :=
          by rw [List.isSome_find?]; exact List.any_eq_true.mpr ⟨s, hs, by simpa using hty⟩
        cases hfind : ss.find? (fun s => decide (s.ty = τ)) with
        | none => simp [hfind] at hf
        | some s =>
          simp only [subst, Nat.lt_irrefl, ↓reduceIte,
            ite_eq_left (show i < i + k + 1 by omega), find_type_map _ ht, hfind,
            Option.map_some, Option.getD_some]
          simpa only [Nat.zero_add, Nat.add_comm] using shift_subst s i 0 k us (Nat.zero_le k)
      · have hgt : i < n := by omega
        by_cases hnk : n = i + k + 1
        · subst n
          simp only [subst, ite_eq_right (show ¬ i + k + 1 < i by omega), ite_eq_right (by omega : ¬ i + k + 1 = i),
            show i + k + 1 - 1 = i + k by omega, Nat.lt_irrefl, ↓reduceIte]
          cases hfind : us.find? (fun s => decide (s.ty = τ)) with
          | none => simp [subst, show ¬ i + k + 1 < i by omega,
              show ¬ i + k + 1 = i by omega]
          | some s =>
            simp only [Option.map_some, Option.getD_some]
            exact (subst_shift_gap s (i + k) 0 i _ (Nat.zero_le i) (by omega)).symm
        · by_cases hlt : n < i + k + 1
          · simp only [subst, ite_eq_right hni, ite_eq_right he,
              ite_eq_left (show n - 1 < i + k by omega), ite_eq_left hlt]
          · simp only [subst, ite_eq_right hni, ite_eq_right he,
              ite_eq_right (show ¬ n - 1 < i + k by omega), ite_eq_right (show ¬ n - 1 = i + k by omega),
              ite_eq_right hlt, ite_eq_right hnk,
              ite_eq_right (show ¬ n - 1 < i by omega), ite_eq_right (show ¬ n - 1 = i by omega)]
  | lam ℓ t ih =>
    simpa only [subst, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (lam ℓ) (ih (i + 1) (by simpa only [SubstDefined, occTypes] using hd))
  | app t ts ih ihs =>
    simp only [SubstDefined, occTypes] at hd
    have hdt : t.SubstDefined i ss := fun τ hm => hd τ (List.mem_append_left _ hm)
    have hdts : ∀ s ∈ ts, s.SubstDefined i ss := fun s hs τ hm =>
      hd τ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, hm⟩))
    simp only [subst, List.map_map]
    rw [ih i hdt]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs i (hdts s hs))

end DTerm

/-- Regression witnesses for the former commutation statement. The first conjunct
shows why missing lookups must be excluded; the second refutes the extra shift even
when both original substitutions consume exactly their matching resources. -/
theorem DTerm.subst_commute_counterexamples :
    let x := DTerm.var 0 (.base 0 0)
    let y := DTerm.var 1 (.base 0 0)
    ((x.subst 0 []).subst 0 [y] ≠
      (x.subst 1 [y]).subst 0 []) ∧
    ((y.subst 0 []).subst 0 [x] ≠
      (y.subst 1 [x.shift 1 0]).subst 0 []) := by
  simp [DTerm.subst, DTerm.shift, DTerm.ty]

/-- Choose typed matching arguments for a list of occurrence types. -/
theorem HasTypeMulti.choose {σs : List Ty} {ss : List DTerm}
    (h : ∀ τ ∈ σs, ∃ s ∈ ss, ∃ Γ, HasType Γ s τ) :
    ∃ Γs ss', HasTypeMulti Γs ss' σs ∧ ∀ s ∈ ss', s ∈ ss := by
  induction σs with
  | nil => exact ⟨[], [], .nil, by simp⟩
  | cons τ σs ih =>
    obtain ⟨s, hs, Γ, ht⟩ := h τ (by simp)
    obtain ⟨Γs, ts, hts, hmem⟩ := ih (fun τ hm => h τ (by simp [hm]))
    refine ⟨Γ :: Γs, s :: ts, .cons ht hts, ?_⟩
    intro t hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hs
    · exact hmem t hm

theorem PSubst.defined {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) : t.SubstDefined k ss := by
  intro τ hm
  have hm' : τ ∈ (ss.map DTerm.ty : Multiset Ty) := h.occTypes ▸ hm
  obtain ⟨s, hs, he⟩ := List.mem_map.mp hm'
  exact ⟨s, hs, he⟩

/-- The alternative substitution can use a larger sequential list than the exact
partition. Only arguments matching actual occurrences are consumed. -/
theorem DTerm.partition_of_defined {t : DTerm} {k : ℕ} {ss : List DTerm}
    (hd : t.SubstDefined k ss) (hs : ∀ s ∈ ss, s.Typable)
    (hn : (ss.map DTerm.ty).Nodup) :
    ∃ ts, (∀ s ∈ ts, s ∈ ss) ∧ PSubst t k ts (t.subst k ss) := by
  obtain ⟨Γs, ts, hts, hmem⟩ := HasTypeMulti.choose (σs := t.occTypes k) (ss := ss) (by
    intro τ hm
    obtain ⟨s, hs', he⟩ := hd τ hm
    obtain ⟨Γ, σ, ht⟩ := hs s hs'
    exact ⟨s, hs', Γ, (he ▸ hasType_ty ht) ▸ ht⟩)
  obtain ⟨u, hp⟩ := PSubst.exists hts rfl
  exact ⟨ts, hmem, hp.eq_subst_of_subset ss hmem hn ▸ hp⟩

/-- Defined alternative substitution preserves the type even with unused extra arguments. -/
theorem HasType.subst_ty {t : DTerm} {Γ : Ctx} {τ : Ty} (ht : HasType Γ t τ)
    {k : ℕ} {ss : List DTerm} (hd : t.SubstDefined k ss)
    (hs : ∀ s ∈ ss, s.Typable) (hn : (ss.map DTerm.ty).Nodup) :
    (t.subst k ss).ty = t.ty := by
  obtain ⟨ts, _, hp⟩ := DTerm.partition_of_defined hd hs hn
  exact (hasType_ty (hp.typing ht)).symm.trans (hasType_ty ht)

/-- Reduction in the body survives substitution (`08-07-strong-permutation.tex`). -/
theorem DStep.subst {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u) (hc : Correct t)
    (k : ℕ) (ss : List DTerm) (hd : t.SubstDefined k ss)
    (hs : ∀ s ∈ ss, s.Typable) (hn : (ss.map DTerm.ty).Nodup) :
    DStep (t.subst k ss) ℓ (u.subst k ss) := by
  induction h generalizing k with
  | beta ℓ b ts =>
    have hp := hc.beta_partition
    have htype : ∀ s ∈ ts, (s.subst k ss).ty = s.ty := by
      intro s hm
      obtain ⟨Γ, τ, ht⟩ := (hc.sub (.arg _ hm (.refl s))).typable
      apply ht.subst_ty _ hs hn
      intro τ hτ
      apply hd τ
      simp only [DTerm.occTypes]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hm, hτ⟩)
    have he := b.subst_commute 0 k ts ss hp.defined htype
    simp only [Nat.zero_add] at he
    simp only [DTerm.subst]
    rw [he]
    exact DStep.beta ℓ (b.subst (k + 1) ss) (ts.map (·.subst k ss))
  | lam m h ih =>
    simp only [DTerm.subst]
    apply DStep.lam m (ih (hc.sub (.lam m (.refl _))) (k + 1) _)
    simpa only [DTerm.SubstDefined, DTerm.occTypes] using hd
  | appL ts h ih =>
    simp only [DTerm.subst]
    apply DStep.appL _ (ih (hc.sub (.fn ts (.refl _))) k _)
    intro τ hm
    exact hd τ (by simpa only [DTerm.occTypes] using List.mem_append_left _ hm)
  | @appR s s' ℓ t us vs h ih =>
    simp only [DTerm.subst, List.map_append, List.map_cons]
    apply DStep.appR _ _ _ (ih (hc.sub (.arg t (by simp) (.refl s))) k _)
    intro τ hm
    apply hd τ
    simp only [DTerm.occTypes]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, by simp, hm⟩)

namespace DTerm

/-- Commutation of two ordered index insertions. -/
theorem shift_shift (t : DTerm) (a b c d : ℕ) (hbc : b ≤ c) :
    (t.shift a b).shift d (c + a) = (t.shift d c).shift a b := by
  induction t using DTerm.ind generalizing b c with
  | var n τ =>
    by_cases hnb : n < b
    · simp [shift, hnb, show n < c by omega, show n < c + a by omega]
    · by_cases hnc : n < c
      · simp [shift, hnb, hnc, show n + a < c + a by omega]
      · simp only [shift, ite_eq_right hnb, ite_eq_right hnc,
          ite_eq_right (show ¬ n + a < c + a by omega),
          ite_eq_right (show ¬ n + d < b by omega)]
        congr 1; omega
  | lam ℓ t ih =>
    simp only [shift]
    rw [show c + a + 1 = (c + 1) + a by omega, ih (b + 1) (c + 1) (by omega)]
  | app t ts ih ihs =>
    simp only [shift, List.map_map]
    rw [ih b c hbc]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs b c hbc)

/-- Shifting above a substituted variable shifts its arguments too. -/
theorem subst_shift (t : DTerm) (k d c : ℕ) (ss : List DTerm)
    (hd : t.SubstDefined k ss) (ht : ∀ s ∈ ss, (s.shift d c).ty = s.ty) :
    (t.subst k ss).shift d (c + k) =
      (t.shift d (c + k + 1)).subst k (ss.map (DTerm.shift d c)) := by
  induction t using DTerm.ind generalizing k with
  | var n τ =>
    by_cases hnk : n < k
    · simp [subst, shift, hnk, show n < c + k by omega, show n < c + k + 1 by omega]
    · by_cases he : n = k
      · subst n
        simp only [subst, Nat.lt_irrefl, ↓reduceIte, shift,
          ite_eq_left (show k < c + k + 1 by omega), find_type_map _ ht]
        cases hf : ss.find? (fun s => decide (s.ty = τ)) with
        | none =>
          obtain ⟨s, hs, he⟩ := hd τ (by simp [occTypes])
          have hf' : (ss.find? (fun s => decide (s.ty = τ))).isSome := by
            rw [List.isSome_find?]
            exact List.any_eq_true.mpr ⟨s, hs, by simpa using he⟩
          simp [hf] at hf'
        | some s =>
          simp only [Option.map_some, Option.getD_some]
          exact shift_shift s k 0 c d (Nat.zero_le c)
      · by_cases hnc : n < c + k + 1
        · simp [subst, shift, hnk, he, hnc, show n - 1 < c + k by omega]
        · simp only [subst, ite_eq_right hnk, ite_eq_right he, shift,
            ite_eq_right (show ¬ n - 1 < c + k by omega), ite_eq_right hnc, subst,
            ite_eq_right (show ¬ n + d < k by omega),
            ite_eq_right (show ¬ n + d = k by omega)]
          congr 1; omega
  | lam ℓ t ih =>
    simpa only [subst, shift, Nat.add_assoc] using congrArg (lam ℓ) (ih (k + 1) (by simpa only [SubstDefined, occTypes] using hd))
  | app t ts ih ihs =>
    simp only [SubstDefined, occTypes] at hd
    have hdt : t.SubstDefined k ss := fun τ hm => hd τ (List.mem_append_left _ hm)
    have hdts : ∀ s ∈ ts, s.SubstDefined k ss := fun s hs τ hm =>
      hd τ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, hm⟩))
    simp only [subst, shift, List.map_map]
    rw [ih k hdt]
    congr 1
    exact List.map_congr_left (fun s hs => ihs s hs k (hdts s hs))

end DTerm

/-- Shifting a typed term leaves its type unchanged. -/
theorem HasType.shift_ty {Γ : Ctx} {t : DTerm} {τ : Ty} (ht : HasType Γ t τ)
    (d c : ℕ) : (t.shift d c).ty = t.ty :=
  (hasType_ty (ht.shift d c)).symm.trans (hasType_ty ht)

/-- Steps are stable under insertion of free-variable indices. -/
theorem DStep.shift {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u) (hc : Correct t)
    (d c : ℕ) : DStep (t.shift d c) ℓ (u.shift d c) := by
  induction h generalizing c with
  | beta ℓ b ss =>
    have ht : ∀ s ∈ ss, (s.shift d c).ty = s.ty := by
      intro s hm
      obtain ⟨Γ, τ, ht⟩ := (hc.sub (.arg _ hm (.refl s))).typable
      exact ht.shift_ty d c
    have he := b.subst_shift 0 d c ss hc.beta_partition.defined ht
    simp only [Nat.add_zero] at he
    simp only [DTerm.shift]
    rw [he]
    exact .beta ℓ _ _
  | lam m h ih => simpa only [DTerm.shift] using .lam m (ih (hc.sub (.lam m (.refl _))) (c + 1))
  | appL ss h ih => simpa only [DTerm.shift] using .appL _ (ih (hc.sub (.fn ss (.refl _))) c)
  | appR t us vs h ih =>
    simpa only [DTerm.shift, List.map_append, List.map_cons] using
      .appR _ _ _ (ih (hc.sub (.arg t (by simp) (.refl _))) c)

/-- A single labelled reduction in a list, retaining its occurrence. -/
inductive DListStep : List DTerm → Label → List DTerm → Prop
  | head {s s' : DTerm} {ss : List DTerm} {ℓ : Label} :
      DStep s ℓ s' → DListStep (s :: ss) ℓ (s' :: ss)
  | tail {s : DTerm} {ss ss' : List DTerm} {ℓ : Label} :
      DListStep ss ℓ ss' → DListStep (s :: ss) ℓ (s :: ss')

theorem DListStep.spec {ss ss' : List DTerm} {ℓ : Label} (h : DListStep ss ℓ ss') :
    ∃ us s s' vs, ss = us ++ s :: vs ∧ ss' = us ++ s' :: vs ∧ DStep s ℓ s' := by
  induction h with
  | head h => exact ⟨[], _, _, _, rfl, rfl, h⟩
  | tail h ih =>
    obtain ⟨us, s, s', vs, rfl, rfl, hs⟩ := ih
    exact ⟨_ :: us, s, s', vs, rfl, rfl, hs⟩

theorem DListStep.app {ss ss' : List DTerm} {ℓ : Label} (h : DListStep ss ℓ ss')
    (t : DTerm) : DStep (.app t ss) ℓ (.app t ss') := by
  obtain ⟨us, s, s', vs, rfl, rfl, hs⟩ := h.spec
  exact .appR t us vs hs

theorem DListStep.of_append {s s' : DTerm} {ℓ : Label} (h : DStep s ℓ s')
    (us vs : List DTerm) : DListStep (us ++ s :: vs) ℓ (us ++ s' :: vs) := by
  induction us with
  | nil => exact .head h
  | cons u us ih => exact .tail ih

/-- An application step contracts its root, its function, or one argument. -/
theorem DStep.app_cases {t u : DTerm} {ss : List DTerm} {ℓ : Label}
    (h : DStep (.app t ss) ℓ u) :
    (∃ b, t = .lam ℓ b ∧ u = b.subst 0 ss) ∨
      (∃ t', DStep t ℓ t' ∧ u = .app t' ss) ∨
      ∃ ss', DListStep ss ℓ ss' ∧ u = .app t ss' := by
  cases h with
  | beta ℓ b ss => exact .inl ⟨b, rfl, rfl⟩
  | appL _ h => exact .inr (.inl ⟨_, h, rfl⟩)
  | appR t us vs h => exact .inr (.inr ⟨_, DListStep.of_append h us vs, rfl⟩)

/-- A resource occurrence can be reduced once in the result of partition substitution. -/
theorem PSubst.step_resource [DecidableEq DTerm] {s s' : DTerm} {ℓ : Label} (hstep : DStep s ℓ s')
    (hc : Correct s) {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (hp : PSubst t k ss u) (hm : s ∈ ss) :
    ∃ v, DStep u ℓ v ∧ PSubst t k (s' :: ss.erase s) v := by
  classical
  induction hp using PSubst.rec
    (motive_2 := fun ts k ss us _ => s ∈ ss →
      ∃ rs vs, rs.Perm (s' :: ss.erase s) ∧ DListStep us ℓ vs ∧ PSubstMulti ts k rs vs) with
  | var_eq k ht =>
    have he := List.mem_singleton.mp hm
    subst he
    obtain ⟨ht', _⟩ := hstep.subject_reduction hc ht
    exact ⟨_, hstep.shift hc k 0, by simpa using PSubst.var_eq k ht'⟩
  | var_lt => simp at hm
  | var_gt => simp at hm
  | lam m hp ih =>
    obtain ⟨v, hv, hp'⟩ := ih hm
    exact ⟨_, .lam m hv, .lam m hp'⟩
  | @app t u ts us ss ss₀ ss₁ k hp hps hperm ih ihs =>
    have hm' := hperm.symm.subset hm
    by_cases hm₀ : s ∈ ss₀
    · obtain ⟨v, hv, hp'⟩ := ih hm₀
      refine ⟨_, .appL us hv, .app hp' hps ?_⟩
      simpa only [List.cons_append, List.erase_append_left ss₁ hm₀] using
        (hperm.erase s).cons s'
    · have hm₁ : s ∈ ss₁ := (List.mem_append.mp hm').resolve_left hm₀
      obtain ⟨rs, vs, hr, hv, hp'⟩ := ihs hm₁
      refine ⟨_, hv.app u, .app hp hp' ?_⟩
      exact ((List.Perm.refl ss₀).append hr).trans (List.perm_middle.trans (by
        simpa only [List.erase_append_right ss₁ hm₀] using (hperm.erase s).cons s'))
  | nil => rename_i hm; simp at hm
  | @cons t u ts us ss₀ ss₁ k hp hps ih ihs =>
    rename_i hm
    by_cases hm₀ : s ∈ ss₀
    · obtain ⟨v, hv, hp'⟩ := ih hm₀
      refine ⟨(s' :: ss₀.erase s) ++ ss₁, v :: us, ?_, .head hv, .cons hp' hps⟩
      simp only [List.erase_append_left ss₁ hm₀, List.cons_append]
      exact .refl _
    · have hm₁ : s ∈ ss₁ := (List.mem_append.mp hm).resolve_left hm₀
      obtain ⟨rs, vs, hr, hv, hp'⟩ := ihs hm₁
      refine ⟨ss₀ ++ rs, u :: vs, ?_, .tail hv, .cons hp hp'⟩
      exact ((List.Perm.refl ss₀).append hr).trans (by
        simpa only [List.erase_append_right ss₁ hm₀] using List.perm_middle)

theorem DListStep.types {ss ss' : List DTerm} {ℓ : Label} (h : DListStep ss ℓ ss')
    (hc : ∀ s ∈ ss, Correct s) : ss'.map DTerm.ty = ss.map DTerm.ty := by
  induction h with
  | @head s s' ss ℓ h =>
    obtain ⟨Γ, τ, ht⟩ := (hc s (by simp)).typable
    obtain ⟨hu, _⟩ := h.subject_reduction (hc s (by simp)) ht
    simp only [List.map_cons, (hasType_ty hu).symm.trans (hasType_ty ht)]
  | tail h ih =>
    simp only [List.map_cons, ih (fun s hs => hc s (by simp [hs]))]

/-- A step in one resource survives substitution exactly once
(`08-07-strong-permutation.tex`, reduction inside a substitution). -/
theorem DListStep.substitute {ss ss' : List DTerm} {ℓ : Label} (h : DListStep ss ℓ ss')
    (hc : ∀ s ∈ ss, Correct s) (hn : (ss.map DTerm.ty).Nodup)
    {t u : DTerm} {k : ℕ} (hp : PSubst t k ss u) :
    DStep u ℓ (t.subst k ss') := by
  classical
  have hn' : (ss'.map DTerm.ty).Nodup := h.types hc ▸ hn
  obtain ⟨us, s, s', vs, rfl, rfl, hs⟩ := h.spec
  obtain ⟨v, hv, hp'⟩ := hp.step_resource hs (hc s (by simp)) (by simp)
  have he : ((us ++ s :: vs).erase s).Perm (us ++ vs) := by
    simpa using (List.perm_middle (a := s) (l₁ := us) (l₂ := vs)).erase s
  have hperm : (s' :: (us ++ s :: vs).erase s).Perm (us ++ s' :: vs) :=
    (he.cons s').trans List.perm_middle.symm
  exact hp'.eq_subst_of_subset _ (fun _ hm => hperm.subset hm) hn' ▸ hv

/-- Lift a diamond argument on individual terms to one-step list reductions. -/
theorem DListStep.permutation {ss ss₁ ss₂ : List DTerm} {ℓ m : Label}
    (ih : ∀ s ∈ ss, ∀ {u v a b}, DStep s a u → DStep s b v →
      (a = b ∧ u = v) ∨ ∃ w, DStep u b w ∧ DStep v a w)
    (h₁ : DListStep ss ℓ ss₁) (h₂ : DListStep ss m ss₂) :
    (ℓ = m ∧ ss₁ = ss₂) ∨ ∃ ss₃, DListStep ss₁ m ss₃ ∧ DListStep ss₂ ℓ ss₃ := by
  induction h₁ generalizing ss₂ with
  | @head s u ts a h =>
    cases h₂ with
    | head h' =>
      rcases ih s (by simp) h h' with ⟨rfl, rfl⟩ | ⟨w, hu, hv⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨w :: ts, .head hu, .head hv⟩
    | tail h' => exact .inr ⟨_, .tail h', .head h⟩
  | @tail s ts us a h iht =>
    cases h₂ with
    | head h' => exact .inr ⟨_, .head h', .tail h⟩
    | tail h' =>
      rcases iht (fun t ht => ih t (by simp [ht])) h' with ⟨rfl, rfl⟩ | ⟨vs, hu, hv⟩
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨s :: vs, .tail hu, .tail hv⟩

/-- The two nested-redex cases of strong permutation: a step inside the beta body,
or inside one of its resources (`08-07-strong-permutation.tex`). -/
theorem DStep.beta_permutation {b v : DTerm} {ss : List DTerm} {ℓ m : Label}
    (hc : Correct (.app (.lam ℓ b) ss)) (h : DStep (.app (.lam ℓ b) ss) m v) :
    (ℓ = m ∧ b.subst 0 ss = v) ∨
      ∃ w, DStep (b.subst 0 ss) m w ∧ DStep v ℓ w := by
  have hp := hc.beta_partition
  have hb := hc.sub (.fn ss (.lam ℓ (.refl b)))
  have hs : ∀ s ∈ ss, Correct s := fun s hm => hc.sub (.arg _ hm (.refl s))
  obtain ⟨Γ, τ, ht⟩ := hb.typable
  have hseq : SeqMS (b.occTypes 0 : Multiset Ty) := by
    rw [← hasType_occTypes ht 0]
    exact hb.seq_ctx b Γ τ (.refl b) ht 0
  have hseq' : SeqMS (ss.map DTerm.ty : Multiset Ty) := hp.occTypes ▸ hseq
  have hn : (ss.map DTerm.ty).Nodup := List.Nodup.of_map (f := Ty.label)
    (by simpa only [SeqMS, Multiset.map_coe, Multiset.coe_nodup] using hseq')
  rcases h.app_cases with ⟨b', he, rfl⟩ | ⟨f, hf, rfl⟩ | ⟨ss', hss, rfl⟩
  · cases he
    exact .inl ⟨rfl, rfl⟩
  · cases hf with
    | lam _ hf =>
      exact .inr ⟨_, hf.subst hb 0 ss hp.defined
        (fun s hm => (hs s hm).typable) hn, .beta ℓ _ ss⟩
  · exact .inr ⟨_, hss.substitute hs hn hp, .beta ℓ b ss'⟩

/-- Strong permutation, with equality of the original steps allowed as a separate case.
The structural cases are exactly the context cases in `08-07-strong-permutation.tex`. -/
theorem DStep.permutation {t u v : DTerm} {ℓ m : Label} (hc : Correct t)
    (h₁ : DStep t ℓ u) (h₂ : DStep t m v) :
    (ℓ = m ∧ u = v) ∨ ∃ w, DStep u m w ∧ DStep v ℓ w := by
  induction t using DTerm.ind generalizing u v ℓ m with
  | var => cases h₁
  | lam a t ih =>
    cases h₁ with
    | lam _ h₁ =>
      cases h₂ with
      | lam _ h₂ =>
        rcases ih (hc.sub (.lam a (.refl t))) h₁ h₂ with ⟨rfl, rfl⟩ | ⟨w, hu, hv⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨.lam a w, .lam a hu, .lam a hv⟩
  | app t ss ih ihs =>
    rcases h₁.app_cases with ⟨b, rfl, rfl⟩ | ⟨t₁, ht₁, rfl⟩ | ⟨ss₁, hs₁, rfl⟩
    · exact DStep.beta_permutation hc h₂
    · rcases h₂.app_cases with ⟨b, rfl, rfl⟩ | ⟨t₂, ht₂, rfl⟩ | ⟨ss₂, hs₂, rfl⟩
      · rcases DStep.beta_permutation hc h₁ with ⟨he, hu⟩ | ⟨w, hu, hv⟩
        · exact .inl ⟨he.symm, hu.symm⟩
        · exact .inr ⟨w, hv, hu⟩
      · rcases ih (hc.sub (.fn ss (.refl t))) ht₁ ht₂ with ⟨rfl, rfl⟩ | ⟨w, hu, hv⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨.app w ss, .appL ss hu, .appL ss hv⟩
      · exact .inr ⟨.app t₁ ss₂, hs₂.app t₁, .appL ss₂ ht₁⟩
    · rcases h₂.app_cases with ⟨b, rfl, rfl⟩ | ⟨t₂, ht₂, rfl⟩ | ⟨ss₂, hs₂, rfl⟩
      · rcases DStep.beta_permutation hc h₁ with ⟨he, hu⟩ | ⟨w, hu, hv⟩
        · exact .inl ⟨he.symm, hu.symm⟩
        · exact .inr ⟨w, hv, hu⟩
      · exact .inr ⟨.app t₂ ss₁, .appL ss₁ ht₂, hs₁.app t₂⟩
      · rcases DListStep.permutation
          (fun s hm => ihs s hm (hc.sub (.arg t hm (.refl s)))) hs₁ hs₂ with
          ⟨rfl, rfl⟩ | ⟨ss₃, hu, hv⟩
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨.app t ss₃, hu.app t, hv.app t⟩

/-- Every step contracts a lambda present in its source, independently of typing. -/
theorem DStep.label_mem {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u) : ℓ ∈ t.lamLabels := by
  induction h with
  | beta => simp [DTerm.lamLabels]
  | lam _ _ ih => simp [DTerm.lamLabels, ih]
  | appL _ _ ih => simp [DTerm.lamLabels, ih]
  | @appR s s' ℓ t us vs h ih =>
    simp only [DTerm.lamLabels, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨s, by simp, ih⟩

/-- In a correct term, the target of a step is determined by its label. -/
theorem dStep_deterministic {t u u' : DTerm} {ℓ : Label} (ht : Correct t)
    (h : DStep t ℓ u) (h' : DStep t ℓ u') : u = u' := by
  rcases DStep.permutation ht h h' with ⟨_, he⟩ | ⟨v, hu, _⟩
  · exact he
  · have hn : (ℓ ::ₘ (u.lamLabels : Multiset Label)).Nodup :=
      (h.lamLabels ht).symm ▸ ht.uniquely_labeled
    exact False.elim ((Multiset.nodup_cons.mp hn).1 hu.label_mem)

/-- Substitution is linear: it neither erases nor duplicates λs (`08-05-termination.tex`). -/
theorem size_subst {Γ : Ctx} {t : DTerm} {τ : Ty} {Δs : List Ctx} {ss : List DTerm}
    {σs : List Ty} (ht : HasType (Ctx.cons (σs : Multiset Ty) Γ) t τ)
    (hs : HasTypeMulti Δs ss σs) (hseq : SeqMS (σs : Multiset Ty)) :
    (t.subst 0 ss).size = t.size + (ss.map DTerm.size).sum := by
  obtain ⟨u, hp⟩ := PSubst.exists (t := t) (k := 0) hs (by
    exact hasType_occTypes ht 0)
  have hn : (ss.map DTerm.ty).Nodup := List.Nodup.of_map (f := Ty.label)
    (by simpa only [← hs.types_eq, SeqMS, Multiset.map_coe, Multiset.coe_nodup] using hseq)
  rw [← hp.eq_subst_of_subset ss (fun _ h => h) hn]
  exact hp.size

/-- Each step consumes exactly one λ. -/
theorem size_dStep {t u : DTerm} {ℓ : Label} (ht : Correct t) (h : DStep t ℓ u) :
    u.size + 1 = t.size := by
  induction h with
  | beta ℓ t ss =>
    obtain ⟨Γ, τ, hh⟩ := ht.typable
    cases hh with
    | app hf hs hp =>
      cases hf with
      | @lam Γ M σ _ _ hb =>
        rename_i Δs σs
        have he : (σs : Multiset Ty) = M := by
          exact (Multiset.coe_eq_coe.mpr hp).trans (Ty.coe_canon M)
        have hb' := he.symm ▸ hb
        have hseq := ht.seq_ctx t _ _ (.fn ss (.lam ℓ (.refl t))) hb 0
        have hh := size_subst hb' hs (he.symm ▸ hseq)
        simp only [DTerm.size] at *
        omega
  | lam m h ih =>
    have hh := ih (ht.sub (.lam m (.refl _)))
    simp only [DTerm.size] at *; omega
  | appL ss h ih =>
    have hh := ih (ht.sub (.fn ss (.refl _)))
    simp only [DTerm.size] at *; omega
  | appR t us vs h ih =>
    have hh := ih (ht.sub (.arg t (by simp) (.refl _)))
    simp only [DTerm.size, List.map_append, List.map_cons, List.sum_append,
      List.sum_cons] at *
    omega

end Ch2AppB

/-! ## Chapter 2: A distributive λ-calculus (λ^dist)

Main-text results of Chapter 2:
* Unique typing (`unique_typing`).
* Agreement of partition-based and type-directed substitution (`PSubst.eq_subst`), typing of
  substitution (`subst_hasType`), and the substitution lemma (`subst_subst`).
* Linearity (`linearity`) and subject reduction (`subject_reduction`, `correct_of_dStep`).
* Termination (`termination`) and the λ-count bound (`size_le_of_reduces`).
* Strong permutation (`strong_permutation`) and confluence (`confluence`). -/

section Ch2Main

/-! ## 2.2 Unique typing -/

/-- **Unique typing**: a correct term has a unique type and typing context. -/
theorem unique_typing {Γ Γ' : Ctx} {t : DTerm} {τ τ' : Ty} (_ht : Correct t)
    (h : HasType Γ t τ) (h' : HasType Γ' t τ') : Γ = Γ' ∧ τ = τ' :=
  hasType_unique h h'

/-! ## 2.3 Substitution -/

/-- **Alternative substitution**: sequential argument types suffice for agreement of
partition-based and type-directed substitution. -/
theorem PSubst.eq_subst {t u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst t k ss u) (hseq : SeqMS (ss.map DTerm.ty : Multiset Ty)) :
    u = t.subst k ss := by
  apply h.eq_subst_of_subset ss (fun _ h => h)
  exact List.Nodup.of_map (f := Ty.label) (by simpa [SeqMS] using hseq)

/-- **Substitution is well defined** (typing): if `Γ ⊕ x : [σ̄] ⊢ t : τ` and `Δ̄ ⊢ s̄ : σ̄`
(with `[σ̄]` sequential), then `Γ + ΣΔ̄ ⊢ t{x := s̄} : τ`. -/
theorem subst_hasType {Γ : Ctx} {t : DTerm} {τ : Ty} {Δs : List Ctx} {ss : List DTerm}
    {σs : List Ty} (ht : HasType (Ctx.cons (σs : Multiset Ty) Γ) t τ)
    (hs : HasTypeMulti Δs ss σs) (hseq : SeqMS (σs : Multiset Ty)) :
    HasType (Γ + Δs.sum) (t.subst 0 ss) τ := by
  obtain ⟨u, hp⟩ := PSubst.exists (t := t) (k := 0) hs (hasType_occTypes ht 0)
  have hn : (ss.map DTerm.ty).Nodup := List.Nodup.of_map (f := Ty.label)
    (by simpa only [← hs.types_eq, SeqMS, Multiset.map_coe, Multiset.coe_nodup] using hseq)
  have hc := congrArg List.sum hs.contexts_eq
  have hu := hp.typing ht
  simpa only [hp.eq_subst_of_subset ss (fun _ h => h) hn, hc, Ctx.shift_zero_cutoff,
    show (Ctx.cons (σs : Multiset Ty) Γ).remove 0 = Γ from rfl] using hu

/-- **Substitution lemma** for the alternative substitution (`03-03-the-calculus.tex`).
Lookup is defined on the body, and substitution in the arguments preserves their types.
Arguments of `DTerm.subst` live outside all crossed binders, so `us` needs no extra shift. -/
theorem subst_subst (t : DTerm) (k : ℕ) (ss us : List DTerm)
    (hd : t.SubstDefined 0 ss) (ht : ∀ s ∈ ss, (s.subst k us).ty = s.ty) :
    (t.subst 0 ss).subst k us =
      (t.subst (k + 1) us).subst 0 (ss.map (·.subst k us)) := by
  simpa only [Nat.zero_add] using t.subst_commute 0 k ss us hd ht

/-! ## 2.4 Basic properties -/

/-- **Linearity**: the typing context of a term records exactly the types of the free
occurrences of each variable, `Γ(x) = [τ₁, …, τₙ]`. (This holds for any typable term.) -/
theorem linearity {Γ : Ctx} {t : DTerm} {τ : Ty} (h : HasType Γ t τ) (n : ℕ) :
    Γ n = (t.occTypes n : Multiset Ty) :=
  hasType_occTypes h n

/-- **Subject reduction**: types and contexts are preserved, and so is correctness. -/
theorem subject_reduction {Γ : Ctx} {t u : DTerm} {τ : Ty} {ℓ : Label}
    (ht : Correct t) (h : HasType Γ t τ) (hs : DStep t ℓ u) : HasType Γ u τ ∧ Correct u := by
  exact hs.subject_reduction ht h

theorem correct_of_dStep {t u : DTerm} {ℓ : Label} (ht : Correct t) (hs : DStep t ℓ u) :
    Correct u := by
  obtain ⟨Γ, τ, h⟩ := ht.typable
  exact (subject_reduction ht h hs).2

/-! ### Termination -/

/-- **Termination**: there is no infinite reduction sequence `t₀ → t₁ → t₂ → ⋯` from a correct
term. -/
theorem termination : ¬ ∃ f : ℕ → DTerm, Correct (f 0) ∧ ∀ n, DRed (f n) (f (n + 1)) := by
  rintro ⟨f, h0, hf⟩
  have hc : ∀ n, Correct (f n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => obtain ⟨ℓ, h⟩ := hf n; exact correct_of_dStep ih h
  have key : ∀ n, (f n).size + n = (f 0).size := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      obtain ⟨ℓ, h⟩ := hf n
      have := size_dStep (hc n) h
      omega
  have := key ((f 0).size + 1)
  omega

/-- Reduction never increases the number of λs. -/
theorem size_le_of_reduces {t u : DTerm} (ht : Correct t)
    (h : Relation.ReflTransGen DRed t u) : u.size ≤ t.size := by
  induction h with
  | refl => exact le_rfl
  | @tail b c hab hbc ih =>
    obtain ⟨ℓ, hs⟩ := hbc
    have hb : Correct b := by
      clear ih hs
      induction hab with
      | refl => exact ht
      | tail _ h ih' => obtain ⟨ℓ', h⟩ := h; exact correct_of_dStep ih' h
    have := size_dStep hb hs
    omega

/-! ### Confluence -/

/-- **Strong permutation** (diamond property): two different steps `t₀ →ℓ t₁` and `t₀ →ℓ' t₂`
can be closed by `t₁ →ℓ' t₃` and `t₂ →ℓ t₃`. -/
theorem strong_permutation {t₀ t₁ t₂ : DTerm} {ℓ ℓ' : Label} (h₀ : Correct t₀)
    (h₁ : DStep t₀ ℓ t₁) (h₂ : DStep t₀ ℓ' t₂) (hne : ℓ ≠ ℓ' ∨ t₁ ≠ t₂) :
    ∃ t₃, DStep t₁ ℓ' t₃ ∧ DStep t₂ ℓ t₃ := by
  rcases DStep.permutation h₀ h₁ h₂ with ⟨he, ht⟩ | h
  · exact False.elim (hne.elim (fun hn => hn he) (fun hn => hn ht))
  · exact h

/-- **Confluence** of λ^dist (a consequence of strong permutation, via sub-commutativity). -/
theorem confluence {t₀ t₁ t₂ : CTerm} (h₁ : Relation.ReflTransGen CRed t₀ t₁)
    (h₂ : Relation.ReflTransGen CRed t₀ t₂) :
    ∃ t₃, Relation.ReflTransGen CRed t₁ t₃ ∧ Relation.ReflTransGen CRed t₂ t₃ := by
  refine Relation.church_rosser (fun a b c hab hac => ?_) h₁ h₂
  obtain ⟨ℓ, hb⟩ := hab
  obtain ⟨ℓ', hc⟩ := hac
  by_cases hbc : ℓ ≠ ℓ' ∨ b.1 ≠ c.1
  · obtain ⟨d, hbd, hcd⟩ := strong_permutation a.2 hb hc hbc
    let d' : CTerm := ⟨d, correct_of_dStep b.2 hbd⟩
    exact ⟨d', Relation.ReflGen.single ⟨ℓ', hbd⟩, Relation.ReflTransGen.single ⟨ℓ, hcd⟩⟩
  · push Not at hbc
    obtain ⟨-, e⟩ := hbc
    have : b = c := Subtype.ext e
    subst this
    exact ⟨b, Relation.ReflGen.refl, Relation.ReflTransGen.refl⟩

end Ch2Main

end CiruelosLic
