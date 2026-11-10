import Mathlib
import CiruelosLic.Chapter4Section1SimulationExpansion

/-!
# Chapter 4: simulation, head normal forms and simulation residuals

Contents:
* Chapter 4: Simulation of the λ-calculus — Appendix (continued)
* Chapter 4: Simulation of the λ-calculus
-/

namespace CiruelosLic

/-! ## Chapter 4: Simulation of the λ-calculus — Appendix (continued)

Controlled subject expansion, free cuts, strong sequentiality, backwards simulation, and strong
head-normal-form refinements (`08-14-hnf-has-refinement.tex` and `08-15-has-hnf-has-refinement.tex`). -/

section Ch4AppendixCont

open LTerm DTerm
/-! ### Forward refinement and head normalization (`08-11`, `08-12`, `08-15`) -/

theorem Refines.shift {t : LTerm} {u : DTerm} (h : Refines t u) (d c : ℕ) :
    Refines (t.shift d c) (u.shift d c) := by
  induction h generalizing c with
  | var n τ => simp only [LTerm.shift, DTerm.shift]; split <;> exact .var _ _
  | lam ℓ h ih => simpa only [LTerm.shift, DTerm.shift] using Refines.lam ℓ (ih (c + 1))
  | app h hs ih ihs =>
    simp only [LTerm.shift, DTerm.shift]
    apply Refines.app (ih c)
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact ihs b hb c

/-- The substitution-refinement lemma is proved for resource partitions first; this
avoids assuming that raw type-directed lookup succeeds without typing premises. -/
theorem PSubst.refines {b u : DTerm} {k : ℕ} {ss : List DTerm}
    (h : PSubst b k ss u) {t s : LTerm} (hr : Refines t b)
    (hs : ∀ a ∈ ss, Refines s a) : Refines (LTerm.substAt k s t) u := by
  induction h using PSubst.rec
    (motive_2 := fun bs k ss us _ => ∀ t s : LTerm,
      (∀ b ∈ bs, Refines t b) → (∀ a ∈ ss, Refines s a) →
      ∀ a ∈ us, Refines (LTerm.substAt k s t) a) generalizing t s with
  | @var_eq a Γ τ k ht =>
    cases hr
    simpa only [LTerm.substAt, lt_self_iff_false, ↓reduceIte] using
      (hs a (by simp)).shift k 0
  | @var_lt n k τ hn => cases hr; simpa [LTerm.substAt, hn] using Refines.var n τ
  | @var_gt n k τ hn =>
    cases hr
    simpa [LTerm.substAt, show ¬ n < k by omega, show ¬ n = k by omega]
      using Refines.var (n - 1) τ
  | lam ℓ h ih =>
    cases hr with
    | lam _ hr => simpa only [LTerm.substAt] using Refines.lam ℓ (ih hr hs)
  | app h hm hp ih ihm =>
    cases hr with
    | app hr hrs =>
      simp only [LTerm.substAt]
      apply Refines.app (ih hr (fun a ha => hs a (hp.subset (List.mem_append_left _ ha))))
      exact ihm _ _ hrs (fun a ha => hs a (hp.subset (List.mem_append_right _ ha)))
  | nil => rename_i t s ht hs a ha; simp at ha
  | cons h hm ih ihm =>
    rename_i t s ht hs a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ih (ht _ (by simp)) (fun a ha => hs a (List.mem_append_left _ ha))
    · exact ihm t s (fun b hb => ht b (by simp [hb]))
        (fun a ha => hs a (List.mem_append_right _ ha)) a ha

theorem refinement_substitution {t s : LTerm} {b : DTerm} {ss : List DTerm}
    {ℓ : Label} (hr : Refines t b) (hs : ∀ a ∈ ss, Refines s a)
    (hc : Correct (.app (.lam ℓ b) ss)) : Refines (LTerm.substAt 0 s t) (b.subst 0 ss) := by
  obtain ⟨Γ, τ, ht⟩ := hc.typable
  cases ht with
  | app hf hm hp =>
    cases hf with
    | @lam Γ M τ b ℓ hb =>
      have hmatch : (_ : Multiset Ty) = (b.occTypes 0 : Multiset Ty) :=
        (Multiset.coe_eq_coe.mpr hp).trans (by simpa [Ctx.cons] using hasType_occTypes hb 0)
      obtain ⟨u, hu⟩ := PSubst.exists hm hmatch
      have hseq : SeqMS (ss.map DTerm.ty : Multiset Ty) := by
        rw [← hm.types_eq, hmatch]
        have he := hasType_occTypes hb 0
        change M = _ at he
        rw [← he]
        simpa [Ctx.cons] using
          hc.seq_ctx b _ _ (.fn ss (.lam ℓ (.refl b))) hb 0
      rw [← hu.eq_subst hseq]
      exact hu.refines hr hs

theorem DRed.reduces_plug {t u : DTerm} (h : Relation.ReflTransGen DRed t u) (C : DCtx) :
    Relation.ReflTransGen DRed (C.plug t) (C.plug u) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => obtain ⟨ℓ, hs⟩ := hs; exact ih.tail ⟨ℓ, hs.plug C⟩

theorem DRed.reduces_app_args {ss us : List DTerm}
    (h : List.Forall₂ (Relation.ReflTransGen DRed) ss us) (f : DTerm) (pre : List DTerm) :
    Relation.ReflTransGen DRed (.app f (pre ++ ss)) (.app f (pre ++ us)) := by
  induction h generalizing pre with
  | nil => exact .refl
  | @cons a b ss us hab h ih =>
    have h₁ := DRed.reduces_plug hab (.appR f pre .hole ss)
    have h₂ := ih (pre ++ [b])
    simp only [List.append_assoc, List.singleton_append] at h₂
    exact h₁.trans h₂

/-- Forward simulation, by the four context cases of `08-12-simulation.tex`.
Argument copies are reduced one at a time; empty argument lists require no steps. -/
theorem simulation_raw {t s : LTerm} (h : Beta t s) {u : DTerm}
    (hr : Refines t u) (hc : Correct u) :
    ∃ v, Relation.ReflTransGen DRed u v ∧ Refines s v := by
  induction h generalizing u with
  | beta t s =>
    cases hr with
    | app hf hs =>
      cases hf with
      | lam ℓ hf => exact ⟨_, .single ⟨ℓ, .beta ℓ _ _⟩, refinement_substitution hf hs hc⟩
  | lam h ih =>
    cases hr with
    | lam ℓ hr =>
      obtain ⟨v, hp, hv⟩ := ih hr (hc.sub (.lam ℓ (.refl _)))
      exact ⟨_, DRed.reduces_plug hp (.lam ℓ .hole), .lam ℓ hv⟩
  | appL s h ih =>
    cases hr with
    | @app _ _ f ss hf hs =>
      obtain ⟨v, hp, hv⟩ := ih hf (hc.sub (.fn ss (.refl _)))
      exact ⟨_, DRed.reduces_plug hp (.appL .hole ss), .app hv hs⟩
  | @appR t s s' h ih =>
    cases hr with
    | @app _ _ f ss hf hs =>
      have work : ∀ ts : List DTerm, (∀ a ∈ ts, Refines s a) →
          (∀ a ∈ ts, Correct a) → ∃ us, List.Forall₂
            (fun a b => Relation.ReflTransGen DRed a b ∧ Refines s' b) ts us := by
        intro ts
        induction ts with
        | nil => intro _ _; exact ⟨[], .nil⟩
        | cons a ts iht =>
          intro hr hc
          obtain ⟨b, hp, hb⟩ := ih (hr a (by simp)) (hc a (by simp))
          obtain ⟨bs, hbs⟩ := iht (fun a ha => hr a (by simp [ha]))
            (fun a ha => hc a (by simp [ha]))
          exact ⟨b :: bs, .cons ⟨hp, hb⟩ hbs⟩
      obtain ⟨us, hu⟩ := work ss hs (fun a ha => hc.sub (.arg f ha (.refl a)))
      have hp := hu.imp (fun _ _ h => h.1)
      refine ⟨.app f us, ?_, .app hf ?_⟩
      · simpa using DRed.reduces_app_args hp f []
      · clear hp hs hc
        induction hu with
        | nil => simp
        | cons h hu ih => simpa only [List.mem_cons, forall_eq_or_imp] using And.intro h.2 ih

theorem DRed.correct_reduces {t u : DTerm} (hc : Correct t)
    (h : Relation.ReflTransGen DRed t u) : Correct u := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => obtain ⟨ℓ, hs⟩ := hs; exact correct_of_dStep ih hs

theorem DRed.reduces_correct_terms {t u : DTerm} (h : Relation.ReflTransGen DRed t u)
    (ht : Correct t) (hu : Correct u) :
    Relation.ReflTransGen CRed (⟨t, ht⟩ : CTerm) (⟨u, hu⟩ : CTerm) := by
  induction h with
  | refl => exact .refl
  | @tail b c hp hs ih =>
    have hb := DRed.correct_reduces ht hp
    exact (ih hb).tail hs

/-- A head reduction always has a represented copy in a refinement: unlike a step
inside an erased argument, it consumes a lambda of the correct refining term. -/
theorem Refines.head_progress {t : LTerm} {u : DTerm} (hr : Refines t u)
    (hc : Correct u) : IsHNF t ∨
      ∃ s v ℓ, Beta t s ∧ DStep u ℓ v ∧ Refines s v := by
  induction t generalizing u with
  | var n => exact .inl (.head (.var n))
  | lam t ih =>
    cases hr with
    | lam ℓ hr =>
      rcases ih hr (hc.sub (.lam ℓ (.refl _))) with hn | ⟨s, v, m, hb, hd, hv⟩
      · exact .inl (.lam hn)
      · exact .inr ⟨.lam s, .lam ℓ v, m, .lam hb, .lam ℓ hd, .lam ℓ hv⟩
  | app t s ih _ =>
    cases hr with
    | @app _ _ f ss hf hs =>
      cases t with
      | lam b =>
        cases hf with
        | lam ℓ hf => exact .inr ⟨_, _, ℓ, .beta b s, .beta ℓ _ _,
            refinement_substitution hf hs hc⟩
      | var n => exact .inl (.head (.app s (.var n)))
      | app a b =>
        rcases ih hf (hc.sub (.fn ss (.refl f))) with hn | ⟨r, v, ℓ, hb, hd, hv⟩
        · cases hn with
          | head hh => exact .inl (.head (.app s hh))
        · exact .inr ⟨.app r s, .app v ss, ℓ, .appL s hb, .appL ss hd, .app hv hs⟩

/-- The forward implication uses induction on the number of lambdas in the refinement,
as in the head-reduction argument of `08-15-has-hnf-has-refinement.tex`. -/
theorem Refines.hasHNF {t : LTerm} {u : DTerm} (hr : Refines t u)
    (hc : Correct u) : t.HasHNF := by
  generalize he : u.size = n
  induction n using Nat.strong_induction_on generalizing t u with
  | ind n ih =>
    rcases hr.head_progress hc with hn | ⟨s, v, ℓ, hb, hd, hv⟩
    · exact ⟨t, .refl, hn⟩
    · have hsize := size_dStep hc hd
      obtain ⟨r, hp, hn⟩ := ih v.size (by omega) hv (correct_of_dStep hc hd) rfl
      exact ⟨r, (Relation.ReflTransGen.single (betaStep_iff_beta.mpr hb)).trans hp, hn⟩

/-! ### Named simulation traces

Keeping the contracted labels makes it possible to compare the constructive context
proof with the sorted canonical development used by `simTgt`.
-/

inductive DTrace : DTerm → List Label → DTerm → Prop
  | nil (t : DTerm) : DTrace t [] t
  | cons {t u v : DTerm} {ℓ : Label} {σ : List Label} :
      DStep t ℓ u → DTrace u σ v → DTrace t (ℓ :: σ) v

namespace DTrace

theorem append {t u v : DTerm} {σ τ : List Label} (h : DTrace t σ u)
    (k : DTrace u τ v) : DTrace t (σ ++ τ) v := by
  induction h with
  | nil => exact k
  | cons hs h ih => exact .cons hs (ih k)

theorem plug {t u : DTerm} {σ : List Label} (h : DTrace t σ u) (C : DCtx) :
    DTrace (C.plug t) σ (C.plug u) := by
  induction h with
  | nil => exact .nil _
  | cons hs h ih => exact .cons (hs.plug C) ih

theorem specification {t u : DTerm} {σ : List Label} (h : DTrace t σ u)
    (ht : Correct t) :
    distRS.Valid (⟨t, ht⟩ : CTerm) σ ∧
    (distRS.tgt (⟨t, ht⟩ : CTerm) σ).1 = u := by
  induction h with
  | nil => exact ⟨trivial, rfl⟩
  | @cons t v u ℓ σ hs h ih =>
    obtain ⟨hm, he⟩ := (dStep_iff_hasRedex ht).1 hs
    have hv := correct_of_dStep ht hs
    obtain ⟨hp, hu⟩ := ih hv
    have eq : distRS.contract (⟨t, ht⟩ : CTerm) ℓ = (⟨v, hv⟩ : CTerm) :=
      Subtype.ext he.symm
    refine ⟨⟨hm, eq.symm ▸ hp⟩, ?_⟩
    change (distRS.tgt (distRS.contract (⟨t, ht⟩ : CTerm) ℓ) σ).1 = u
    rw [eq]
    exact hu

end DTrace

@[simp] theorem simRes_app_zero (f : DTerm) (ss : List DTerm) (p : Pos) :
    simRes (.app f ss) (0 :: p) = simRes f p := by cases f <;> rfl

@[simp] theorem simRes_app_one (f : DTerm) (ss : List DTerm) (p : Pos) :
    simRes (.app f ss) (1 :: p) = (ss.map (simRes · p)).foldr (· ∪ ·) ∅ := by
  cases f <;> rfl

@[simp] theorem LTerm.contractAt_app_zero (f s : LTerm) (p : Pos) :
    contractAt (.app f s) (0 :: p) = .app (contractAt f p) s := by cases f <;> rfl

@[simp] theorem LTerm.contractAt_app_one (f s : LTerm) (p : Pos) :
    contractAt (.app f s) (1 :: p) = .app f (contractAt s p) := by cases f <;> rfl

theorem mem_fold_simRes {ss : List DTerm} {p : Pos} {ℓ : Label} :
    ℓ ∈ (ss.map (simRes · p)).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ ss, ℓ ∈ simRes a p := by
  induction ss with
  | nil => simp
  | cons a ss ih => simp [ih, or_and_right, exists_or]

/-- Every represented distributive redex comes from a beta-redex position in the
underlying pure term (`08-13-reverse-simulation.tex`). -/
theorem DStep.simulation_position {u v : DTerm} {ℓ : Label} (h : DStep u ℓ v)
    {t : LTerm} (hr : Refines t u) :
    ∃ p, isRedexAt t p = true ∧ ℓ ∈ simRes u p := by
  induction h generalizing t with
  | beta ℓ b ss =>
    cases hr with
    | app hf hs => cases hf with | lam _ hf => exact ⟨[], rfl, by simp [simRes]⟩
  | lam m h ih =>
    cases hr with
    | lam _ hr =>
      obtain ⟨p, hp, hm⟩ := ih hr
      exact ⟨0 :: p, by simpa only [isRedexAt, subAt] using hp, hm⟩
  | appL ss h ih =>
    cases hr with
    | app hf hs =>
      obtain ⟨p, hp, hm⟩ := ih hf
      exact ⟨0 :: p, by simpa only [isRedexAt, subAt] using hp, by simpa using hm⟩
  | appR f us vs h ih =>
    cases hr with
    | app hf hs =>
      obtain ⟨p, hp, hm⟩ := ih (hs _ (by simp))
      exact ⟨1 :: p, by simpa only [isRedexAt, subAt] using hp,
        by rw [simRes_app_one]; exact mem_fold_simRes.mpr ⟨_, by simp, hm⟩⟩

theorem simRes_isStep {u : DTerm} {p : Pos} {ℓ : Label} (h : ℓ ∈ simRes u p) :
    u.hasRedex ℓ = true := by
  induction p generalizing u with
  | nil =>
    cases u with
    | var => simp [simRes] at h
    | lam => simp [simRes] at h
    | app f ss => cases f <;> simp_all [simRes, DTerm.hasRedex, DTerm.isLamWith]
  | cons i p ih =>
    cases u with
    | var => simp [simRes] at h
    | lam m u =>
      cases i with
      | zero => simpa only [DTerm.hasRedex] using (ih (u := u) (by simpa only [simRes] using h))
      | succ i => simp [simRes] at h
    | app f ss =>
      cases i with
      | zero =>
        have hf := ih (u := f) (by simpa only [simRes_app_zero] using h)
        simp [DTerm.hasRedex, hf]
      | succ i =>
        cases i with
        | succ i => simp [simRes] at h
        | zero =>
          obtain ⟨a, ha, hm⟩ := mem_fold_simRes.mp (simRes_app_one f ss p ▸ h)
          have hm' := ih hm
          have hx : ss.any (DTerm.hasRedex · ℓ) = true := List.any_eq_true.mpr ⟨a, ha, hm'⟩
          simp [DTerm.hasRedex, hx]

/-- Every simulation image is the label of a lambda of its source. -/
theorem simRes_label_mem {u : DTerm} {p : Pos} {ℓ : Label} (h : ℓ ∈ simRes u p) :
    ℓ ∈ u.lamLabels := by
  obtain ⟨v, hv⟩ := DTerm.hasRedex_iff_step.mp (simRes_isStep h)
  exact hv.label_mem

private theorem simRes_root_unique {u : DTerm} {q : Pos} {ℓ : Label} (hc : Correct u)
    (hroot : ℓ ∈ simRes u []) (hq : ℓ ∈ simRes u q) : q = [] := by
  cases u with
  | var => simp [simRes] at hroot
  | lam => simp [simRes] at hroot
  | app f ss =>
    cases f with
    | var => simp [simRes] at hroot
    | app => simp [simRes] at hroot
    | lam m b =>
      have he : ℓ = m := by simpa only [simRes, Finset.mem_singleton] using hroot
      subst ℓ
      cases q with
      | nil => rfl
      | cons i q =>
        cases i with
        | zero =>
          have hh : m ∈ simRes (.lam m b) q := by simpa only [simRes_app_zero] using hq
          obtain ⟨v, hv⟩ := DTerm.hasRedex_iff_step.mp (simRes_isStep hh)
          exact False.elim (hv.label_ne_outer (hc.sub (.fn ss (.refl _))) rfl)
        | succ i =>
          cases i with
          | zero =>
            obtain ⟨s, hs, hm⟩ := mem_fold_simRes.mp (simRes_app_one _ _ _ ▸ hq)
            exact False.elim (hc.fn_arg_labels (by simp [DTerm.lamLabels]) hs (simRes_label_mem hm))
          | succ i => simp [simRes] at hq

/-- Different pure redex positions have disjoint simulation images (`08-19`). -/
theorem simRes_position_unique {u : DTerm} {p q : Pos} {ℓ : Label} (hc : Correct u)
    (hp : ℓ ∈ simRes u p) (hq : ℓ ∈ simRes u q) : p = q := by
  induction u using DTerm.ind generalizing p q with
  | var n τ => cases p <;> simp [simRes] at hp
  | lam m u ih =>
    cases p with
    | nil => simp [simRes] at hp
    | cons i p =>
      cases i with
      | succ i => simp [simRes] at hp
      | zero =>
        cases q with
        | nil => simp [simRes] at hq
        | cons j q =>
          cases j with
          | succ j => simp [simRes] at hq
          | zero =>
            exact congrArg (List.cons 0) (ih (hc.sub (.lam m (.refl u))) hp hq)
  | app f ss ih ihs =>
    cases p with
    | nil => exact (simRes_root_unique hc hp hq).symm
    | cons i p =>
      cases q with
      | nil => exact simRes_root_unique hc hq hp
      | cons j q =>
        cases i with
        | zero =>
          have hp' : ℓ ∈ simRes f p := by simpa only [simRes_app_zero] using hp
          cases j with
          | zero =>
            have hq' : ℓ ∈ simRes f q := by simpa only [simRes_app_zero] using hq
            exact congrArg (List.cons 0) (ih (hc.sub (.fn ss (.refl f))) hp' hq')
          | succ j =>
            cases j with
            | zero =>
              obtain ⟨s, hs, hq'⟩ := mem_fold_simRes.mp (simRes_app_one _ _ _ ▸ hq)
              exact False.elim (hc.fn_arg_labels (simRes_label_mem hp') hs (simRes_label_mem hq'))
            | succ j => simp [simRes] at hq
        | succ i =>
          cases i with
          | succ i => simp [simRes] at hp
          | zero =>
            obtain ⟨s, hs, hp'⟩ := mem_fold_simRes.mp (simRes_app_one _ _ _ ▸ hp)
            cases j with
            | zero =>
              have hq' : ℓ ∈ simRes f q := by simpa only [simRes_app_zero] using hq
              exact False.elim (hc.fn_arg_labels (simRes_label_mem hq') hs (simRes_label_mem hp'))
            | succ j =>
              cases j with
              | succ j => simp [simRes] at hq
              | zero =>
                obtain ⟨r, hr, hq'⟩ := mem_fold_simRes.mp (simRes_app_one _ _ _ ▸ hq)
                have hn := hc.uniquely_labeled
                rw [DTerm.lamLabels] at hn
                have he := unique_label_child (List.nodup_append.mp hn).2.1 hs hr
                  (simRes_label_mem hp') (simRes_label_mem hq')
                subst r
                exact congrArg (List.cons 1) (ihs s hs (hc.sub (.arg f hs (.refl s))) hp' hq')

theorem simulation_at_trace {p : Pos} {t : LTerm} {u : DTerm}
    (hr : Refines t u) (hc : Correct u) (hp : isRedexAt t p = true) :
    ∃ v σ, DTrace u σ v ∧ σ.toFinset = simRes u p ∧ Refines (contractAt t p) v := by
  induction p generalizing t u with
  | nil =>
    cases t with
    | var => simp [isRedexAt, subAt, isRedex] at hp
    | lam => simp [isRedexAt, subAt, isRedex] at hp
    | app t s =>
      cases t with
      | var => simp [isRedexAt, subAt, isRedex] at hp
      | app => simp [isRedexAt, subAt, isRedex] at hp
      | lam b =>
        cases hr with
        | app hf hs =>
          cases hf with
          | lam ℓ hf => exact ⟨_, [ℓ], .cons (.beta ℓ _ _) (.nil _), by simp [simRes],
              refinement_substitution hf hs hc⟩
  | cons i p ih =>
    cases t with
    | var => simp [isRedexAt, subAt] at hp
    | lam t =>
      cases i with
      | succ i => simp [isRedexAt, subAt] at hp
      | zero =>
        cases hr with
        | lam ℓ hr =>
          obtain ⟨v, σ, ht, he, hv⟩ := ih hr (hc.sub (.lam ℓ (.refl _)))
            (by simpa [isRedexAt, subAt] using hp)
          exact ⟨.lam ℓ v, σ, ht.plug (.lam ℓ .hole), he, .lam ℓ hv⟩
    | app t s =>
      cases hr with
      | @app _ _ f ss hf hs =>
        cases i with
        | zero =>
          obtain ⟨v, σ, ht, he, hv⟩ := ih hf (hc.sub (.fn ss (.refl _)))
            (by simpa [isRedexAt, subAt] using hp)
          exact ⟨.app v ss, σ, ht.plug (.appL .hole ss), by simpa using he,
            by simpa only [LTerm.contractAt_app_zero] using Refines.app hv hs⟩
        | succ i =>
          cases i with
          | succ i => simp [isRedexAt, subAt] at hp
          | zero =>
            have hp' : isRedexAt s p = true := by simpa [isRedexAt, subAt] using hp
            have work : ∀ ts pre : List DTerm, (∀ a ∈ ts, Refines s a) →
                (∀ a ∈ ts, Correct a) → ∃ us σ,
                DTrace (.app f (pre ++ ts)) σ (.app f (pre ++ us)) ∧
                σ.toFinset = (ts.map (simRes · p)).foldr (· ∪ ·) ∅ ∧
                ∀ a ∈ us, Refines (contractAt s p) a := by
              intro ts
              induction ts with
              | nil => intro pre _ _; exact ⟨[], [], .nil _, rfl, by simp⟩
              | cons a ts iht =>
                intro pre hr hc
                obtain ⟨b, σ, ht, he, hb⟩ := ih (hr a (by simp)) (hc a (by simp)) hp'
                obtain ⟨bs, τ, htt, het, hbs⟩ := iht (pre ++ [b])
                  (fun a ha => hr a (by simp [ha])) (fun a ha => hc a (by simp [ha]))
                simp only [List.append_assoc, List.singleton_append] at htt
                exact ⟨b :: bs, σ ++ τ, (ht.plug (.appR f pre .hole ts)).append htt,
                  by simp [he, het], by simpa only [List.mem_cons, forall_eq_or_imp] using (And.intro hb hbs)⟩
            obtain ⟨us, σ, ht, he, hv⟩ := work ss [] hs
              (fun a ha => hc.sub (.arg f ha (.refl a)))
            exact ⟨.app f us, σ, ht, by simpa using he,
              by simpa only [Nat.zero_add, LTerm.contractAt_app_one] using Refines.app hf hv⟩

theorem ResidualSystem.IsDevelopment.valid {R : ResidualSystem} {t : R.Obj}
    {M : Finset R.Adr} {σ : List R.Adr} (h : R.IsDevelopment t M σ) : R.Valid t σ := by
  induction σ generalizing t M with
  | nil => trivial
  | cons a σ ih => exact ⟨h.1, ih h.2.2⟩

/-- The constructive simulation trace and the canonical sorted development have the
same names and therefore the same target. -/
theorem simulation_canonical {t : LTerm} {u : CTerm} {p : Pos}
    (hr : Refines t u.1) (hp : lambdaRS.isStep t p) :
    Refines (contractAt t p) (simTgt u p).1 := by
  obtain ⟨v, σ, ht, he, hv⟩ := simulation_at_trace hr u.2 hp
  obtain ⟨hσ, htarget⟩ := ht.specification u.2
  have hm : ∀ m ∈ simRes u.1 p, distRS.isStep u m := fun m hm => simRes_isStep hm
  have hd := (distRS.orthogonal.dev_complete u _ hm).1.valid
  have hn : distRS.names (distRS.dev u (simRes u.1 p)) = distRS.names σ := by
    simpa only [distRS, distRS.names, Finset.sort_toFinset] using he.symm
  have eq := ResidualSystem.tgt_eq_of_permEq distRS.orthogonal hd hσ
    ((distRS.permEq_iff_names hd hσ).2 hn)
  change Refines (contractAt t p) (distRS.tgt u (distRS.dev u (simRes u.1 p))).1
  rw [eq]
  exact htarget.symm ▸ hv

theorem tgt_simDeriv (t' : CTerm) (σ : List Pos) :
    distRS.tgt t' (simDeriv t' σ) = simTgtDeriv t' σ := by
  induction σ generalizing t' with
  | nil => rfl
  | cons p σ ih => rw [simDeriv, ResidualSystem.tgt_append, simTgtDeriv, ← ih]; rfl

theorem distRS_completeDevelopment_names {t : CTerm} {M : Finset Label} {σ : List Label}
    (hM : ∀ a ∈ M, distRS.isStep t a) (h : distRS.IsCompleteDevelopment t M σ) :
    distRS.names σ = M := by
  have hv := ResidualSystem.isDevelopment_valid h.1
  have h1 := (distRS.residual_names hM hv).1
  rw [h.2] at h1
  exact Finset.Subset.antisymm (distRS.development_subset hM h.1) (Finset.sdiff_eq_empty_iff_subset.mp h1.symm)

theorem distRS_completeDevelopment_permEq {t : CTerm} {M : Finset Label} {σ τ : List Label}
    (hM : ∀ a ∈ M, distRS.isStep t a)
    (hσ : distRS.IsCompleteDevelopment t M σ) (hτ : distRS.IsCompleteDevelopment t M τ) :
    distRS.PermEq t σ τ := by
  have hvσ := ResidualSystem.isDevelopment_valid hσ.1
  have hvτ := ResidualSystem.isDevelopment_valid hτ.1
  rw [distRS.permEq_iff_names hvσ hvτ]
  rw [distRS_completeDevelopment_names hM hσ, distRS_completeDevelopment_names hM hτ]

/-! ### Simulation residuals and substitution (for the cube lemma) -/

theorem simRes_var (n : ℕ) (τ : Ty) (p : Pos) : simRes (.var n τ) p = ∅ := by
  cases p <;> simp [simRes]

theorem simRes_lam_zero (ℓ : Label) (u : DTerm) (p : Pos) :
    simRes (.lam ℓ u) (0 :: p) = simRes u p := by simp [simRes]

theorem simRes_shift (d : ℕ) (t : DTerm) : ∀ (c : ℕ) (p : Pos),
    simRes (t.shift d c) p = simRes t p := by
  induction t using DTerm.ind with
  | var n τ =>
    intro c p
    by_cases h : n < c <;> simp [DTerm.shift, h, simRes_var]
  | lam m t ih =>
    intro c p
    cases p with
    | nil => simp [simRes, DTerm.shift]
    | cons i p =>
      cases i with
      | zero => simp [DTerm.shift, simRes_lam_zero, ih]
      | succ i => simp [simRes, DTerm.shift]
  | app t ss ih ihs =>
    intro c p
    cases p with
    | nil =>
      cases t with
      | var n τ => by_cases h : n < c <;> simp [DTerm.shift, h, simRes]
      | lam m t => simp [simRes, DTerm.shift]
      | app t ss' => simp [simRes, DTerm.shift]
    | cons i p =>
      cases i with
      | zero => simp only [DTerm.shift, simRes_app_zero]; exact ih c p
      | succ i =>
        cases i with
        | zero =>
          simp only [DTerm.shift]
          rw [show (((0 : ℕ) + 1) :: p) = (1 :: p) from rfl, simRes_app_one, simRes_app_one]
          ext ℓ
          rw [mem_fold_simRes, mem_fold_simRes]
          constructor
          · rintro ⟨a, ha, hℓ⟩
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
            exact ⟨b, hb, by rwa [ihs b hb c p] at hℓ⟩
          · rintro ⟨b, hb, hℓ⟩
            exact ⟨b.shift d c, List.mem_map_of_mem hb, by rwa [ihs b hb c p]⟩
        | succ i => simp [DTerm.shift, simRes]

/-- Substitution does not move redexes of the body. -/
theorem simRes_subst_redex {b : LTerm} {b' : DTerm} (hr : Refines b b') :
    ∀ (r : Pos) (k : ℕ) (ss : List DTerm), isRedexAt b r = true →
      simRes (b'.subst k ss) r = simRes b' r := by
  induction hr with
  | var n τ => intro r k ss h; simp [isRedexAt, subAt] at h; cases r <;> simp [subAt, isRedex] at h
  | lam ℓ h ih =>
    intro r k ss hp
    rcases r with _ | ⟨i, r⟩
    · simp [isRedexAt, subAt, isRedex] at hp
    · rcases i with _ | i
      · simp only [isRedexAt_lam_zero] at hp
        simp only [DTerm.subst, simRes_lam_zero]
        exact ih r (k + 1) ss hp
      · simp at hp
  | @app t s t' ss' ht hs iht ihs =>
    intro r k ss hp
    rcases r with _ | ⟨i, r⟩
    · cases ht with
      | lam ℓ _ => simp [DTerm.subst, simRes]
      | _ => simp [isRedexAt, subAt, isRedex] at hp
    · rcases i with _ | _ | i
      · simp only [isRedexAt_app_zero] at hp
        simp only [DTerm.subst, simRes_app_zero]
        exact iht r k ss hp
      · replace hp : isRedexAt s r = true := by simpa using hp
        simp only [DTerm.subst]
        rw [show (((0 : ℕ) + 1) :: r) = (1 :: r) from rfl, simRes_app_one, simRes_app_one]
        ext ℓ
        rw [mem_fold_simRes, mem_fold_simRes]
        constructor
        · rintro ⟨a, ha, hℓ⟩
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
          exact ⟨c, hc, by rwa [ihs c hc r k ss hp] at hℓ⟩
        · rintro ⟨c, hc, hℓ⟩
          exact ⟨c.subst k ss, List.mem_map_of_mem hc, by rwa [ihs c hc r k ss hp]⟩
      · simp at hp

/-- The bag of a correct redex has exactly the types of the occurrences of the bound variable,
and these types are pairwise distinct. -/
theorem bag_types {ℓ : Label} {b' : DTerm} {ss : List DTerm}
    (hc : Correct (.app (.lam ℓ b') ss)) :
    (ss.map DTerm.ty : Multiset Ty) = (b'.occTypes 0 : Multiset Ty) ∧
      SeqMS (ss.map DTerm.ty : Multiset Ty) := by
  obtain ⟨Γ, τ, ht⟩ := hc.typable
  cases ht with
  | app hf hm hp =>
    cases hf with
    | @lam Γ M τ b ℓ hb =>
      have hmatch : (_ : Multiset Ty) = (b'.occTypes 0 : Multiset Ty) :=
        (Multiset.coe_eq_coe.mpr hp).trans (by simpa [Ctx.cons] using hasType_occTypes hb 0)
      refine ⟨by rw [← hm.types_eq]; exact hmatch, ?_⟩
      rw [← hm.types_eq, hmatch]
      have he := hasType_occTypes hb 0
      change M = _ at he
      rw [← he]
      simpa [Ctx.cons] using
        hc.seq_ctx b' _ _ (.fn ss (.lam ℓ (.refl b'))) hb 0

/-- In a bag with pairwise distinct types, lookup by type finds the element itself. -/
theorem find_ty_eq {ss : List DTerm} (hseq : SeqMS (ss.map DTerm.ty : Multiset Ty))
    {a : DTerm} (ha : a ∈ ss) : ss.find? (fun s => decide (s.ty = a.ty)) = some a := by
  have hnd : (ss.map (fun s => (s.ty).label)).Nodup := by
    simpa [SeqMS, List.map_map, Function.comp_def] using hseq
  cases hf : ss.find? (fun s => decide (s.ty = a.ty)) with
  | none =>
    have := List.find?_eq_none.mp hf a ha
    simp at this
  | some a' =>
    have ha' := List.mem_of_find?_eq_some hf
    have hty : a'.ty = a.ty := by simpa using List.find?_some hf
    have := List.inj_on_of_nodup_map hnd ha' ha (by rw [hty])
    rw [this]

/-- Every bag element chosen by the type of an occurrence ends up below that occurrence. -/
theorem subst_usage {b : LTerm} {b' : DTerm} (hr : Refines b b') :
    ∀ (k : ℕ) (ss : List DTerm) (τ : Ty) (a : DTerm) (r : Pos), τ ∈ b'.occTypes k →
      ss.find? (fun s => decide (s.ty = τ)) = some a →
      ∃ o ∈ occs b k, simRes a r ⊆ simRes (b'.subst k ss) (o ++ r) := by
  induction hr with
  | var n τ0 =>
    intro k ss τ a r hτ hf
    simp only [DTerm.occTypes] at hτ
    split_ifs at hτ with hn
    · have hτ' : τ = τ0 := by simpa using hτ
      subst hτ'; subst hn
      refine ⟨[], by simp [occs], ?_⟩
      simp [DTerm.subst, hf, simRes_shift]
    · simp at hτ
  | lam ℓ h ih =>
    intro k ss τ a r hτ hf
    simp only [DTerm.occTypes] at hτ
    obtain ⟨o, ho, hsub⟩ := ih (k + 1) ss τ a r hτ hf
    refine ⟨0 :: o, ?_, ?_⟩
    · simp only [occs, List.mem_map]; exact ⟨o, ho, rfl⟩
    · simp only [DTerm.subst, List.cons_append]
      rw [simRes_lam_zero]; exact hsub
  | @app t s f us ht hs iht ihs =>
    intro k ss τ a r hτ hf
    simp only [DTerm.occTypes, List.mem_append, List.mem_flatMap] at hτ
    rcases hτ with hτ | ⟨u, hu, hτ⟩
    · obtain ⟨o, ho, hsub⟩ := iht k ss τ a r hτ hf
      refine ⟨0 :: o, ?_, ?_⟩
      · simp only [occs, List.mem_append, List.mem_map]; exact Or.inl ⟨o, ho, rfl⟩
      · simp only [DTerm.subst, List.cons_append, simRes_app_zero]; exact hsub
    · obtain ⟨o, ho, hsub⟩ := ihs u hu k ss τ a r hτ hf
      refine ⟨1 :: o, ?_, ?_⟩
      · simp only [occs, List.mem_append, List.mem_map]; exact Or.inr ⟨o, ho, rfl⟩
      · intro ℓ hℓ
        simp only [DTerm.subst, List.cons_append]
        rw [show (1 : ℕ) = 0 + 1 from rfl, simRes_app_one]
        exact mem_fold_simRes.mpr ⟨u.subst k ss, List.mem_map_of_mem hu, hsub hℓ⟩

/-- Everything simulated below an occurrence comes from some bag element. -/
theorem subst_usage_sub {b : LTerm} {b' : DTerm} (hr : Refines b b') :
    ∀ (k : ℕ) (ss : List DTerm) (r : Pos), ∀ o ∈ occs b k, ∀ ℓ ∈ simRes (b'.subst k ss) (o ++ r),
      ∃ a ∈ ss, ℓ ∈ simRes a r := by
  induction hr with
  | var n τ0 =>
    intro k ss r o ho ℓ hℓ
    simp only [occs] at ho
    split_ifs at ho with hn
    · have : o = [] := by simpa using ho
      subst this; subst hn
      simp only [DTerm.subst, List.nil_append] at hℓ
      simp only [lt_self_iff_false, ↓reduceIte] at hℓ
      cases hf : ss.find? (fun s => decide (s.ty = τ0)) with
      | none => rw [hf] at hℓ; simp [simRes_var] at hℓ
      | some a =>
        rw [hf] at hℓ
        simp only [Option.map_some, Option.getD_some, simRes_shift] at hℓ
        exact ⟨a, List.mem_of_find?_eq_some hf, hℓ⟩
    · simp at ho
  | lam ℓ' h ih =>
    intro k ss r o ho ℓ hℓ
    simp only [occs, List.mem_map] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    simp only [DTerm.subst, List.cons_append] at hℓ
    rw [simRes_lam_zero] at hℓ
    exact ih (k + 1) ss r o' ho' ℓ hℓ
  | @app t s f us ht hs iht ihs =>
    intro k ss r o ho ℓ hℓ
    simp only [occs, List.mem_append, List.mem_map] at ho
    rcases ho with ⟨o', ho', rfl⟩ | ⟨o', ho', rfl⟩
    · simp only [DTerm.subst, List.cons_append, simRes_app_zero] at hℓ
      exact iht k ss r o' ho' ℓ hℓ
    · simp only [DTerm.subst, List.cons_append] at hℓ
      rw [show (1 : ℕ) = 0 + 1 from rfl, simRes_app_one] at hℓ
      obtain ⟨x, hx, hℓx⟩ := mem_fold_simRes.mp hℓ
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      exact ihs u hu k ss r o' ho' ℓ hℓx

/-- Root case of the cube lemma, redex inside the argument. -/
theorem cube_root_arg {b : LTerm} {b' : DTerm} {s : LTerm} {ss : List DTerm} {ℓ : Label}
    (hr : Refines b b') (hs : ∀ a ∈ ss, Refines s a)
    (hc : Correct (.app (.lam ℓ b') ss)) (r : Pos) :
    (ss.map (simRes · r)).foldr (· ∪ ·) ∅ =
      ((occs b 0).map (fun o => [] ++ o ++ r)).toFinset.biUnion (simRes (b'.subst 0 ss)) := by
  obtain ⟨hA, hseq⟩ := bag_types hc
  ext ℓ'
  rw [mem_fold_simRes, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hℓ⟩
    have hty : a.ty ∈ (b'.occTypes 0 : Multiset Ty) := by
      rw [← hA]; exact Multiset.mem_coe.mpr (List.mem_map_of_mem ha)
    obtain ⟨o, ho, hsub⟩ := subst_usage hr 0 ss a.ty a r (Multiset.mem_coe.mp hty)
      (find_ty_eq hseq ha)
    exact ⟨o ++ r, List.mem_toFinset.mpr (List.mem_map.mpr ⟨o, ho, by simp⟩), hsub hℓ⟩
  · rintro ⟨x, hx, hℓ⟩
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    simp only [List.nil_append] at hℓ
    exact subst_usage_sub hr 0 ss r o ho ℓ' hℓ

theorem fold_cube {p' : Pos} {X : Finset Pos} {ts us : List DTerm}
    (h : List.Forall₂ (fun a b => simRes a p' = X.biUnion (simRes b)) ts us) :
    (ts.map (simRes · p')).foldr (· ∪ ·) ∅ =
      X.biUnion (fun z => (us.map (simRes · z)).foldr (· ∪ ·) ∅) := by
  induction h with
  | nil => ext ℓ; simp
  | cons hab _ ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [hab, ih, ← Finset.biUnion_union]

/-- The cube property between a term, its refinement, the contracted position and the result. -/
def CubeProp (t : LTerm) (u : DTerm) (q : Pos) (v : DTerm) : Prop :=
  ∀ p, isRedexAt t p = true → p ≠ q → simRes u p = (residuals t q p).biUnion (simRes v)

theorem simRes_app_root (f : DTerm) (xs ys : List DTerm) :
    simRes (.app f xs) [] = simRes (.app f ys) [] := by
  cases f <;> simp [simRes]

theorem cube_root {b : LTerm} {s : LTerm} {b' : DTerm} {ss : List DTerm} {ℓ : Label}
    (hf : Refines b b') (hs : ∀ a ∈ ss, Refines s a)
    (hc : Correct (.app (.lam ℓ b') ss)) :
    CubeProp (.app (.lam b) s) (.app (.lam ℓ b') ss) [] (b'.subst 0 ss) := by
  intro p hp hne
  rcases p with _ | ⟨i, p⟩
  · exact absurd rfl hne
  rcases i with _ | _ | i
  · rcases p with _ | ⟨j, r⟩
    · simp [isRedexAt, subAt, isRedex] at hp
    rcases j with _ | j
    · simp only [isRedexAt_app_zero, isRedexAt_lam_zero] at hp
      have hres : residuals (.app (.lam b) s) [] (0 :: 0 :: r) = {r} := by
        simp [residuals, subAt]
      rw [hres, Finset.singleton_biUnion]
      rw [show (0 :: 0 :: r) = (0 :: (0 :: r)) from rfl, simRes_app_zero, simRes_lam_zero]
      exact (simRes_subst_redex hf r 0 ss hp).symm
    · simp at hp
  · replace hp : isRedexAt s p = true := by simpa using hp
    have hres : residuals (.app (.lam b) s) [] (1 :: p) =
        ((occs b 0).map (fun o => [] ++ o ++ p)).toFinset := by
      simp [residuals, subAt]
    rw [hres, show ((1 : ℕ) :: p) = (((0 : ℕ) + 1) :: p) from rfl, simRes_app_one]
    exact cube_root_arg hf hs hc p
  · simp at hp

theorem refines_lam_head {b : LTerm} {f : DTerm} (hf : Refines (.lam b) f) :
    ∃ ℓ f0, f = .lam ℓ f0 := by
  cases hf with
  | lam ℓ h => exact ⟨ℓ, _, rfl⟩

theorem isRedexAt_app_nil_lam {t1 s : LTerm} (h : isRedexAt (.app t1 s) [] = true) :
    ∃ b, t1 = .lam b := by
  cases t1 <;> simp_all [isRedexAt, subAt, isRedex]

theorem forall₂_right_mem {P : DTerm → Prop} {l : List DTerm} {l' : List DTerm}
    (h : List.Forall₂ (fun (_ : DTerm) b => P b) l l') : ∀ b ∈ l', P b := by
  induction h with
  | nil => simp
  | cons hab _ ih => intro b hb; rcases List.mem_cons.mp hb with rfl | hb; exact hab; exact ih b hb

/-- The constructive simulation trace also satisfies the cube equation (`08-16`). -/
theorem cube_trace {q : Pos} {t : LTerm} {u : DTerm}
    (hr : Refines t u) (hc : Correct u) (hq : isRedexAt t q = true) :
    ∃ v σ, DTrace u σ v ∧ σ.toFinset = simRes u q ∧ Refines (contractAt t q) v ∧
      (∀ ℓ u0, u = .lam ℓ u0 → ∃ v0, v = .lam ℓ v0) ∧ CubeProp t u q v := by
  induction q generalizing t u with
  | nil =>
    cases t with
    | var => simp [isRedexAt, subAt, isRedex] at hq
    | lam => simp [isRedexAt, subAt, isRedex] at hq
    | app t s =>
      cases t with
      | var => simp [isRedexAt, subAt, isRedex] at hq
      | app => simp [isRedexAt, subAt, isRedex] at hq
      | lam b =>
        cases hr with
        | app hf hs =>
          cases hf with
          | lam ℓ hf =>
            exact ⟨_, [ℓ], .cons (.beta ℓ _ _) (.nil _), by simp [simRes],
              refinement_substitution hf hs hc, (by intro ℓ' u0 h; cases h),
              cube_root hf hs hc⟩
  | cons i q ih =>
    cases t with
    | var => simp [isRedexAt, subAt] at hq
    | lam t0 =>
      cases i with
      | succ i => simp [isRedexAt, subAt] at hq
      | zero =>
        cases hr with
        | lam ℓ hr0 =>
          obtain ⟨v, σ, ht, he, hv, hlam, hcube⟩ := ih hr0 (hc.sub (.lam ℓ (.refl _)))
            (by simpa [isRedexAt, subAt] using hq)
          refine ⟨.lam ℓ v, σ, ht.plug (.lam ℓ .hole), he, .lam ℓ hv, ?_, ?_⟩
          · intro ℓ' u0' h; cases h; exact ⟨v, rfl⟩
          · intro p hp hne
            rcases p with _ | ⟨j, p⟩
            · simp [isRedexAt, subAt, isRedex] at hp
            rcases j with _ | j
            · replace hp : isRedexAt t0 p = true := by simpa using hp
              have hne' : p ≠ q := fun h => hne (by rw [h])
              rw [simRes_lam_zero, ctx_lam.residuals_in t0 q p, Finset.image_biUnion]
              simp only [simRes_lam_zero]
              exact hcube p hp hne'
            · simp at hp
    | app t1 s =>
      cases hr with
      | @app _ _ f ss hf hs =>
        cases i with
        | zero =>
          obtain ⟨v, σ, ht, he, hv, hlam, hcube⟩ := ih hf (hc.sub (.fn ss (.refl _)))
            (by simpa [isRedexAt, subAt] using hq)
          refine ⟨.app v ss, σ, ht.plug (.appL .hole ss), by simpa using he,
            by simpa only [LTerm.contractAt_app_zero] using Refines.app hv hs, ?_, ?_⟩
          · intro ℓ' u0 h; cases h
          · intro p hp hne
            rcases p with _ | ⟨j, p⟩
            · have hres : residuals (.app t1 s) (0 :: q) [] = {[]} :=
                LTerm.Ctx.residuals_out (C := fun t => LTerm.app t s) (i := 0) _ _ _ (by intro p'; simp)
              rw [hres, Finset.singleton_biUnion]
              obtain ⟨b, rfl⟩ := isRedexAt_app_nil_lam hp
              obtain ⟨ℓ', f0, rfl⟩ := refines_lam_head hf
              obtain ⟨v0, rfl⟩ := hlam ℓ' f0 rfl
              simp [simRes]
            rcases j with _ | _ | j
            · replace hp : isRedexAt t1 p = true := by simpa using hp
              have hne' : p ≠ q := fun h => hne (by rw [h])
              rw [simRes_app_zero, (ctx_appL s).residuals_in t1 q p, Finset.image_biUnion]
              simp only [simRes_app_zero]
              exact hcube p hp hne'
            · have hres : residuals (.app t1 s) (0 :: q) (1 :: p) = {1 :: p} :=
                LTerm.Ctx.residuals_out (C := fun t => LTerm.app t s) (i := 0) _ _ _ (by intro p'; simp)
              rw [hres, Finset.singleton_biUnion]
              rw [show ((1 : ℕ) :: p) = (((0 : ℕ) + 1) :: p) from rfl, simRes_app_one, simRes_app_one]
            · simp at hp
        | succ i =>
          cases i with
          | succ i => simp [isRedexAt, subAt] at hq
          | zero =>
            have hp' : isRedexAt s q = true := by simpa [isRedexAt, subAt] using hq
            have work : ∀ ts pre : List DTerm, (∀ a ∈ ts, Refines s a) →
                (∀ a ∈ ts, Correct a) → ∃ us σ,
                DTrace (.app f (pre ++ ts)) σ (.app f (pre ++ us)) ∧
                σ.toFinset = (ts.map (simRes · q)).foldr (· ∪ ·) ∅ ∧
                List.Forall₂ (fun a b => Refines (contractAt s q) b ∧ CubeProp s a q b) ts us := by
              intro ts
              induction ts with
              | nil => intro pre _ _; exact ⟨[], [], .nil _, rfl, .nil⟩
              | cons a ts iht =>
                intro pre hr hc
                obtain ⟨b, σ, ht, he, hb, _, hcb⟩ := ih (hr a (by simp)) (hc a (by simp)) hp'
                obtain ⟨bs, τ, htt, het, hbs⟩ := iht (pre ++ [b])
                  (fun a ha => hr a (by simp [ha])) (fun a ha => hc a (by simp [ha]))
                simp only [List.append_assoc, List.singleton_append] at htt
                exact ⟨b :: bs, σ ++ τ, (ht.plug (.appR f pre .hole ts)).append htt,
                  by simp [he, het], .cons ⟨hb, hcb⟩ hbs⟩
            obtain ⟨us, σ, ht, he, hF⟩ := work ss [] hs
              (fun a ha => hc.sub (.arg f ha (.refl a)))
            have hus : ∀ a ∈ us, Refines (contractAt s q) a :=
              forall₂_right_mem (hF.imp (fun a b h => h.1))
            refine ⟨.app f us, σ, ht, by simpa using he,
              by simpa only [Nat.zero_add, LTerm.contractAt_app_one] using Refines.app hf hus,
              ?_, ?_⟩
            · intro ℓ' u0 h; cases h
            · intro p hp hne
              rcases p with _ | ⟨j, p⟩
              · have hres : residuals (.app t1 s) (1 :: q) [] = {[]} :=
                  LTerm.Ctx.residuals_out (C := fun x => LTerm.app t1 x) (i := 1) _ _ _ (by intro p'; simp)
                rw [hres, Finset.singleton_biUnion]
                exact simRes_app_root f ss us
              rcases j with _ | _ | j
              · have hres : residuals (.app t1 s) (1 :: q) (0 :: p) = {0 :: p} :=
                  LTerm.Ctx.residuals_out (C := fun x => LTerm.app t1 x) (i := 1) _ _ _ (by intro p'; simp)
                rw [hres, Finset.singleton_biUnion]
                simp only [simRes_app_zero]
              · replace hp : isRedexAt s p = true := by simpa using hp
                have hne' : p ≠ q := fun h => hne (by rw [h])
                rw [(ctx_appR t1).residuals_in s q p, Finset.image_biUnion]
                rw [show ((1 : ℕ) :: p) = (((0 : ℕ) + 1) :: p) from rfl, simRes_app_one]
                have hF' := hF.imp (fun a b hab => hab.2 p hp hne')
                rw [fold_cube hF']
                apply Finset.biUnion_congr rfl
                intro z _
                rw [show (((0 : ℕ) + 1) :: z) = ((1 : ℕ) :: z) from rfl, simRes_app_one]
              · simp at hp

/-- The constructive trace reaches the canonical simulation residual. -/
theorem simTgt_eq_trace {u : CTerm} {q : Pos} {v : DTerm} {σ : List Label}
    (ht : DTrace u.1 σ v) (he : σ.toFinset = simRes u.1 q) : (simTgt u q).1 = v := by
  obtain ⟨hσ, htarget⟩ := ht.specification u.2
  have hm : ∀ m ∈ simRes u.1 q, distRS.isStep u m := fun m hm => simRes_isStep hm
  have hd := (distRS.orthogonal.dev_complete u _ hm).1.valid
  have hn : distRS.names (distRS.dev u (simRes u.1 q)) = distRS.names σ := by
    simpa only [distRS, distRS.names, Finset.sort_toFinset] using he.symm
  have eq := ResidualSystem.tgt_eq_of_permEq distRS.orthogonal hd hσ
    ((distRS.permEq_iff_names hd hσ).2 hn)
  change (distRS.tgt u (distRS.dev u (simRes u.1 q))).1 = v
  rw [eq]
  exact htarget

end Ch4AppendixCont

/-! ## Chapter 4: Simulation of the λ-calculus

Main-text results of Chapter 4:
* Refinements (`omega_not_refinable`).
* Simulation and reverse simulation (`simulation`, `reverse_simulation`).
* Head normal forms (`hnf_has_refinement`, `has_hnf_iff_refinable`).
* Simulation residuals, cube lemmas, compatibility, and algebraic simulation (`simRes_spec`,
  `simDeriv_valid`, `simTgtDeriv_append`, `simDeriv_append`, `basic_cube_lemma`,
  `simDeriv_of_completeDevelopment`, `compatibility`, `simDeriv_prefix`,
  `generalized_cube_lemma`, `algebraicSimulation`). -/

section Ch4Main

open LTerm DTerm

/-! ## 4.1 Refinements -/

/-- `Ω = (λx.xx)(λx.xx)` has no refinement. -/
theorem omega_not_refinable :
    ¬ ∃ t' : CTerm, Refines (.app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0))))
      t'.1 := by
  let δ : LTerm := .lam (.app (.var 0) (.var 0))
  let Ω : LTerm := .app δ δ
  have loop : ∀ s, BetaStep Ω s → s = Ω := by
    intro s hs
    dsimp [Ω, δ] at hs
    cases betaStep_iff_beta.mp hs with
    | beta => rfl
    | appL _ h =>
      cases h with
      | lam h =>
        cases h with
        | appL _ h => cases h
        | appR _ h => cases h
    | appR _ h =>
      cases h with
      | lam h =>
        cases h with
        | appL _ h => cases h
        | appR _ h => cases h
  rintro ⟨u, hr⟩
  obtain ⟨s, hp, hn⟩ := hr.hasHNF u.2
  have he : s = Ω := by
    clear hn
    induction hp with
    | refl => rfl
    | tail hp h ih => exact loop _ (ih ▸ h)
  subst s
  dsimp [Ω, δ] at hn
  cases hn with
  | head hh => cases hh with | app _ hh => cases hh

/-! ## 4.2 Simulation -/

/-- **Simulation**: if `t' ⋉ t →β s` then `t' ↠dist s'` for some `s' ⋉ s` (in fact by a
multistep). -/
theorem simulation {t s : LTerm} {t' : CTerm} (hr : Refines t t'.1) (h : BetaStep t s) :
    ∃ s' : CTerm, Relation.ReflTransGen CRed t' s' ∧ Refines s s'.1 := by
  obtain ⟨v, hp, hv⟩ := simulation_raw (betaStep_iff_beta.mp h) hr t'.2
  exact ⟨⟨v, DRed.correct_reduces t'.2 hp⟩, DRed.reduces_correct_terms hp _ _, hv⟩

/-- **Reverse simulation**: if `t ⋉ t' →dist s'` then `t →β s ⋉ s''` for some `s, s''`,
where the step `t' → s'` is contained in the multistep `t' ↠ s''`. -/
theorem reverse_simulation {t : LTerm} {t' s' : CTerm} {ℓ : Label} (hr : Refines t t'.1)
    (h : DStep t'.1 ℓ s'.1) :
    ∃ (s : LTerm) (s'' : CTerm) (M : Finset Label),
      BetaStep t s ∧ Refines s s''.1 ∧ ℓ ∈ M ∧ (∀ m ∈ M, distRS.isStep t' m) ∧
        distRS.tgt t' (distRS.dev t' M) = s'' := by
  obtain ⟨p, hp, hm⟩ := h.simulation_position hr
  exact ⟨contractAt t p, simTgt t' p, simRes t'.1 p, ⟨p, hp, rfl⟩,
    simulation_canonical hr hp, hm, fun _ ha => simRes_isStep ha, rfl⟩

/-! ## 4.3 Head normal forms -/

/-- Head normal forms are refinable. -/
theorem hnf_has_refinement {t : LTerm} (h : IsHNF t) : ∃ t' : CTerm, Refines t t'.1 := by
  obtain ⟨u, hr, hc, _⟩ := hnf_has_strong_refinement h
  exact ⟨⟨u, hc.correct⟩, hr⟩

/-- **Refinability characterizes head normalization.** The following are equivalent:
1. `t` has a refinement;
2. `t` has a refinement that reduces to `λ…λ. y^τ [] … []`;
3. `t` has a head normal form. -/
theorem has_hnf_iff_refinable (t : LTerm) :
    [∃ t' : CTerm, Refines t t'.1,
     ∃ t' : CTerm, Refines t t'.1 ∧
       ∃ u' : CTerm, Relation.ReflTransGen CRed t' u' ∧ IsEmptyHNF u'.1,
     t.HasHNF].TFAE := by
  tfae_have 1 → 3 := by
    rintro ⟨u, hr⟩
    exact hr.hasHNF u.2
  tfae_have 3 → 2 := by
    intro h
    obtain ⟨v, _, hr, n, hnf, hp⟩ := head_normalizing_has_strong_refinement h
    exact ⟨v, hr, n, hp, hnf⟩
  tfae_have 2 → 1 := by
    rintro ⟨v, hr, _⟩
    exact ⟨v, hr⟩
  tfae_finish

/-! ## 4.4 Simulation residuals -/

/-- The simulation residuals of a step are steps, and `t'/R ⋉ tgt(R)`. -/
theorem simRes_spec {t : LTerm} {t' : CTerm} {p : Pos} (hr : Refines t t'.1)
    (hp : lambdaRS.isStep t p) :
    (∀ ℓ ∈ simRes t'.1 p, distRS.isStep t' ℓ) ∧ Refines (contractAt t p) (simTgt t' p).1 := by
  exact ⟨fun _ hm => simRes_isStep hm, simulation_canonical hr hp⟩

theorem simDeriv_valid {t : LTerm} {t' : CTerm} {σ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) :
    distRS.Valid t' (simDeriv t' σ) ∧ Refines (lambdaRS.tgt t σ) (simTgtDeriv t' σ).1 := by
  induction σ generalizing t t' with
  | nil => exact ⟨trivial, hr⟩
  | cons p σ ih =>
    obtain ⟨hp, hσ⟩ := hσ
    obtain ⟨hm, hs⟩ := simRes_spec hr hp
    have hd := (distRS.orthogonal.dev_complete t' (simRes t'.1 p) hm).1.valid
    obtain ⟨hv, hr'⟩ := ih hs hσ
    exact ⟨(distRS.valid_append _ _ _).2 ⟨hd, hv⟩, hr'⟩

/-- **Simulation residuals and composition** (1): `t'/στ = (t'/σ)/τ`. -/
theorem simTgtDeriv_append (t' : CTerm) (σ τ : List Pos) :
    simTgtDeriv t' (σ ++ τ) = simTgtDeriv (simTgtDeriv t' σ) τ := by
  induction σ generalizing t' with
  | nil => rfl
  | cons p σ ih => exact ih _

/-- **Simulation residuals and composition** (2): `στ/t' = (σ/t')(τ/(t'/σ))`. -/
theorem simDeriv_append (t' : CTerm) (σ τ : List Pos) :
    simDeriv t' (σ ++ τ) = simDeriv t' σ ++ simDeriv (simTgtDeriv t' σ) τ := by
  induction σ generalizing t' with
  | nil => rfl
  | cons p σ ih => simp [simDeriv, simTgtDeriv, ih]

/-- **Basic cube lemma for simulation residuals**:
`(R/t')/(S/t') = (R/S)/(t'/S)` as sets of coinitial λ^dist-steps. -/
theorem basic_cube_lemma {t : LTerm} {t' : CTerm} {p q : Pos} (hr : Refines t t'.1)
    (hp : lambdaRS.isStep t p) (hq : lambdaRS.isStep t q) :
    distRS.resSetDeriv t' (simRes t'.1 p) (distRS.dev t' (simRes t'.1 q)) =
      (lambdaRS.res t q p).biUnion fun p' => simRes (simTgt t' q).1 p' := by
  by_cases hpq : p = q
  · subst hpq
    have hm : ∀ ℓ ∈ simRes t'.1 p, distRS.isStep t' ℓ := fun _ h => simRes_isStep h
    have hd := (distRS.orthogonal.dev_complete t' (simRes t'.1 p) hm).2
    rw [hd]
    have ha : lambdaRS.res t p p = ∅ := lambda_orthogonal.autoerasure t p hp
    rw [ha, Finset.biUnion_empty]
  · obtain ⟨v, σ, ht, he, hv, -, hcube⟩ := cube_trace hr t'.2 hq
    have hv' : (simTgt t' q).1 = v := simTgt_eq_trace ht he
    have hM : ∀ b ∈ simRes t'.1 p, distRS.isStep t' b := fun _ h => simRes_isStep h
    have hN : ∀ b ∈ simRes t'.1 q, distRS.isStep t' b := fun _ h => simRes_isStep h
    have hvd := ResidualSystem.dev_valid distRS.orthogonal hN
    rw [(distRS.residual_names hM hvd).1, distRS.names_dev]
    have hdisj : simRes t'.1 p \ simRes t'.1 q = simRes t'.1 p := by
      apply Finset.sdiff_eq_self_of_disjoint
      rw [Finset.disjoint_left]
      intro ℓ hℓp hℓq
      exact hpq (simRes_position_unique t'.2 hℓp hℓq)
    rw [hdisj, hv']
    exact hcube p hp hpq

/-- **Simulation residual of a development**: if `σ` is a complete development of `𝓜` then
`σ/t'` is a complete development of `𝓜/t'`. -/
theorem simDeriv_of_completeDevelopment {t : LTerm} {t' : CTerm} {M : Finset Pos}
    {σ : List Pos} (hr : Refines t t'.1) (hM : ∀ p ∈ M, lambdaRS.isStep t p)
    (hσ : lambdaRS.IsCompleteDevelopment t M σ) :
    distRS.IsCompleteDevelopment t' (M.biUnion fun p => simRes t'.1 p) (simDeriv t' σ) := by
  induction σ generalizing t t' M with
  | nil =>
    have hM0 : M = ∅ := hσ.2
    subst hM0
    exact ⟨trivial, rfl⟩
  | cons a σ ih =>
    obtain ⟨⟨ha, haM, hdev⟩, hres⟩ := hσ
    have hM' : ∀ p ∈ lambdaRS.resSet t M a, lambdaRS.isStep (lambdaRS.contract t a) p := by
      intro p hp
      obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp hp
      exact lambda_orthogonal.res_isStep t m a (hM m hm) ha p hpm
    have hIH := ih (t := lambdaRS.contract t a) (t' := simTgt t' a)
      (M := lambdaRS.resSet t M a) (simulation_canonical hr ha) hM' ⟨hdev, hres⟩
    have hS : ∀ p ∈ M, ∀ ℓ ∈ simRes t'.1 p, distRS.isStep t' ℓ := fun _ _ _ h => simRes_isStep h
    have hU : ∀ ℓ ∈ M.biUnion (fun p => simRes t'.1 p), distRS.isStep t' ℓ := by
      intro ℓ hℓ
      obtain ⟨p, hp, hℓp⟩ := Finset.mem_biUnion.mp hℓ
      exact hS p hp ℓ hℓp
    have hdS := distRS.orthogonal.dev_complete t' (simRes t'.1 a) (hS a haM)
    have hresU : distRS.resSetDeriv t' (M.biUnion fun p => simRes t'.1 p)
        (distRS.dev t' (simRes t'.1 a)) =
        (lambdaRS.resSet t M a).biUnion fun p' => simRes (simTgt t' a).1 p' := by
      rw [ResidualSystem.resSetDeriv_biUnion]
      have : ∀ p ∈ M, distRS.resSetDeriv t' (simRes t'.1 p) (distRS.dev t' (simRes t'.1 a)) =
          (lambdaRS.res t a p).biUnion fun p' => simRes (simTgt t' a).1 p' :=
        fun p hp => basic_cube_lemma hr (hM p hp) ha
      rw [Finset.biUnion_congr rfl this]
      unfold ResidualSystem.resSet
      rw [Finset.biUnion_biUnion]
    have hN : distRS.IsCompleteDevelopment (distRS.tgt t' (distRS.dev t' (simRes t'.1 a)))
        (distRS.resSetDeriv t' (M.biUnion fun p => simRes t'.1 p)
          (distRS.dev t' (simRes t'.1 a))) (simDeriv (simTgt t' a) σ) := by
      rw [hresU]; exact hIH
    have hunion := ResidualSystem.completeDevelopment_union hdS hN
    have hsub : simRes t'.1 a ∪ M.biUnion (fun p => simRes t'.1 p) =
        M.biUnion (fun p => simRes t'.1 p) :=
      Finset.union_eq_right.mpr (Finset.subset_biUnion_of_mem (fun p => simRes t'.1 p) haM)
    rw [hsub] at hunion
    exact hunion

theorem compatibility_permGen {t : lambdaRS.Obj} {σ τ : List lambdaRS.Adr}
    (h : ResidualSystem.PermGen lambdaRS t σ τ) :
    ∀ {t' : CTerm} (hr : Refines t t'.1),
      simTgtDeriv t' σ = simTgtDeriv t' τ ∧ distRS.PermEq t' (simDeriv t' σ) (simDeriv t' τ) := by
  induction h with
  | refl hσ =>
    intro t' hr
    exact ⟨rfl, ResidualSystem.prefix_refl distRS.orthogonal (simDeriv_valid hr hσ).1,
      ResidualSystem.prefix_refl distRS.orthogonal (simDeriv_valid hr hσ).1⟩
  | symm h ih =>
    intro t' hr
    obtain ⟨ht, hp⟩ := ih hr
    exact ⟨ht.symm, hp.2, hp.1⟩
  | trans h1 h2 ih1 ih2 =>
    intro t' hr
    obtain ⟨ht1, hp1⟩ := ih1 hr
    obtain ⟨ht2, hp2⟩ := ih2 hr
    have hv1 := (simDeriv_valid hr (h1.valid_left lambda_orthogonal)).1
    have hv2 := (simDeriv_valid hr (h1.valid_right lambda_orthogonal)).1
    have hv3 := (simDeriv_valid hr (h2.valid_right lambda_orthogonal)).1
    exact ⟨ht1.trans ht2,
      ResidualSystem.prefix_trans distRS.orthogonal hv1 hv2 hv3 hp1.1 hp2.1,
      ResidualSystem.prefix_trans distRS.orthogonal hv3 hv2 hv1 hp2.2 hp1.2⟩
  | append h1 h2 ih1 ih2 =>
    intro t' hr
    obtain ⟨ht1, hp1⟩ := ih1 hr
    have hr' : Refines (lambdaRS.tgt _ _) (simTgtDeriv t' _).1 :=
      (simDeriv_valid hr (h1.valid_left lambda_orthogonal)).2
    obtain ⟨ht2, hp2⟩ := ih2 hr'
    rw [simTgtDeriv_append, simTgtDeriv_append, ← ht1, ht2]
    refine ⟨rfl, ?_⟩
    rw [simDeriv_append, simDeriv_append, ← ht1]
    have hs1 := (simDeriv_valid hr (h1.valid_left lambda_orthogonal)).1
    have hs2 := (simDeriv_valid hr (h1.valid_right lambda_orthogonal)).1
    have ht1' := (simDeriv_valid hr' (h2.valid_left lambda_orthogonal)).1
    have ht2' := (simDeriv_valid hr' (h2.valid_right lambda_orthogonal)).1
    rw [distRS.permEq_iff_names ((distRS.valid_append _ _ _).2 ⟨hs1, by rw [tgt_simDeriv]; exact ht1'⟩)
      ((distRS.valid_append _ _ _).2 ⟨hs2, by rw [tgt_simDeriv, ← ht1]; exact ht2'⟩)]
    rw [distRS.names_append, distRS.names_append]
    have hn1 := (distRS.permEq_iff_names hs1 hs2).1 hp1
    have hn2 := (distRS.permEq_iff_names ht1' ht2').1 hp2
    rw [hn1, hn2]
  | @swap t a b ha hb =>
    intro t' hr
    have hc1 := ResidualSystem.swap_isCompleteDevelopment lambda_orthogonal ha hb
    have hc2 := ResidualSystem.swap_isCompleteDevelopment lambda_orthogonal hb ha
    have heq : ({b} ∪ {a} : Finset Pos) = {a} ∪ {b} := Finset.union_comm {b} {a}
    rw [heq] at hc2
    have hMs : ∀ p ∈ ({a} ∪ {b} : Finset Pos), lambdaRS.isStep t p := by
      intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact (Finset.mem_singleton.mp h) ▸ ha
      · exact (Finset.mem_singleton.mp h) ▸ hb
    have hd1 := simDeriv_of_completeDevelopment hr hMs hc1
    have hd2 := simDeriv_of_completeDevelopment hr hMs hc2
    have hM : ∀ ℓ ∈ ({a} ∪ {b} : Finset Pos).biUnion (fun p => simRes t'.1 p), distRS.isStep t' ℓ := by
      intro ℓ hℓ
      obtain ⟨p, hp, hℓp⟩ := Finset.mem_biUnion.mp hℓ
      exact simRes_isStep hℓp
    have hpe := distRS_completeDevelopment_permEq hM hd1 hd2
    have htg := ResidualSystem.tgt_eq_of_permEq distRS.orthogonal
      (ResidualSystem.isDevelopment_valid hd1.1) (ResidualSystem.isDevelopment_valid hd2.1) hpe
    rw [tgt_simDeriv, tgt_simDeriv] at htg
    exact ⟨htg, hpe⟩

/-- **Compatibility**: if `σ ≡ τ` then `t'/σ = t'/τ` and `σ/t' ≡ τ/t'`. -/
theorem compatibility {t : LTerm} {t' : CTerm} {σ τ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) (h : lambdaRS.PermEq t σ τ) :
    simTgtDeriv t' σ = simTgtDeriv t' τ ∧ distRS.PermEq t' (simDeriv t' σ) (simDeriv t' τ) :=
  compatibility_permGen ((ResidualSystem.permGen_iff_permEq lambda_orthogonal hσ hτ).2 h) hr

/-- **Simulation residuals and prefixes**: `σ ⊑ τ ⟹ σ/t' ⊑ τ/t'`. -/
theorem simDeriv_prefix {t : LTerm} {t' : CTerm} {σ τ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) (h : lambdaRS.Prefix t σ τ) :
    distRS.Prefix t' (simDeriv t' σ) (simDeriv t' τ) := by
  obtain ⟨ρ, hρ, he⟩ := (ResidualSystem.prefix_iff_exists lambda_orthogonal hσ hτ).1 h
  have hs := simDeriv_valid hr hσ
  have ht := simDeriv_valid hr hτ
  have hρ' := (simDeriv_valid hs.2 hρ).1
  apply (ResidualSystem.prefix_iff_exists distRS.orthogonal hs.1 ht.1).2
  refine ⟨simDeriv (simTgtDeriv t' σ) ρ, by simpa only [tgt_simDeriv] using hρ', ?_⟩
  rw [← simDeriv_append]
  exact (compatibility hr ((lambdaRS.valid_append _ _ _).2 ⟨hσ, hρ⟩) hτ he).2

/-! ### Names of simulation residuals (towards the generalized cube lemma) -/

theorem simNames_cons (t' : CTerm) (p : Pos) (σ : List Pos) :
    distRS.names (simDeriv t' (p :: σ)) =
      simRes t'.1 p ∪ distRS.names (simDeriv (simTgt t' p) σ) := by
  simp only [simDeriv]
  rw [distRS.names_append, distRS.names_dev t' (simRes t'.1 p)]

theorem simNames_append (t' : CTerm) (σ τ : List Pos) :
    distRS.names (simDeriv t' (σ ++ τ)) =
      distRS.names (simDeriv t' σ) ∪ distRS.names (simDeriv (simTgtDeriv t' σ) τ) := by
  rw [simDeriv_append, distRS.names_append]

/-- The set form of the basic cube lemma. -/
theorem cube_sets {t : LTerm} {t' : CTerm} {p q : Pos} (hr : Refines t t'.1)
    (hp : lambdaRS.isStep t p) (hq : lambdaRS.isStep t q) :
    (lambdaRS.res t q p).biUnion (fun p' => simRes (simTgt t' q).1 p') =
      simRes t'.1 p \ simRes t'.1 q := by
  rw [← basic_cube_lemma hr hp hq]
  have hM : ∀ b ∈ simRes t'.1 p, distRS.isStep t' b := fun _ h => simRes_isStep h
  have hN : ∀ b ∈ simRes t'.1 q, distRS.isStep t' b := fun _ h => simRes_isStep h
  have hv := ResidualSystem.dev_valid distRS.orthogonal hN
  rw [(distRS.residual_names hM hv).1, distRS.names_dev]

/-- The cube lemma for an arbitrary derivation. -/
theorem cube_gen : ∀ (ρ : List Pos) (p : Pos) {t : LTerm} {t' : CTerm},
    Refines t t'.1 → lambdaRS.isStep t p → lambdaRS.Valid t ρ →
      (lambdaRS.resSetDeriv t {p} ρ).biUnion (fun y => simRes (simTgtDeriv t' ρ).1 y) =
        simRes t'.1 p \ distRS.names (simDeriv t' ρ) := by
  intro ρ
  induction ρ with
  | nil =>
    intro p t t' hr hp _
    simp [ResidualSystem.resSetDeriv, simDeriv, simTgtDeriv, distRS.names]
  | cons q ρ ih =>
    intro p t t' hr hp hv
    obtain ⟨hq, hρ⟩ := hv
    have hr' := simulation_canonical hr hq
    have hres : ∀ z ∈ lambdaRS.res t q p, lambdaRS.isStep (lambdaRS.contract t q) z :=
      lambda_orthogonal.res_isStep t p q hp hq
    rw [simNames_cons]
    change (lambdaRS.resSetDeriv (lambdaRS.contract t q) (lambdaRS.resSet t {p} q) ρ).biUnion
      (fun y => simRes (simTgtDeriv (simTgt t' q) ρ).1 y) = _
    rw [ResidualSystem.resSet_singleton, ResidualSystem.resSetDeriv_eq_biUnion,
      Finset.biUnion_biUnion]
    have h1 : ∀ z ∈ lambdaRS.res t q p,
        (lambdaRS.resSetDeriv (lambdaRS.contract t q) {z} ρ).biUnion
          (fun y => simRes (simTgtDeriv (simTgt t' q) ρ).1 y) =
        simRes (simTgt t' q).1 z \ distRS.names (simDeriv (simTgt t' q) ρ) :=
      fun z hz => ih z hr' (hres z hz) hρ
    rw [Finset.biUnion_congr rfl h1]
    ext ℓ
    have hc := cube_sets hr hp hq
    have hmem : ℓ ∈ simRes t'.1 p \ (simRes t'.1 q ∪ distRS.names (simDeriv (simTgt t' q) ρ)) ↔
        ℓ ∈ (lambdaRS.res t q p).biUnion (fun p' => simRes (simTgt t' q).1 p') ∧
          ℓ ∉ distRS.names (simDeriv (simTgt t' q) ρ) := by
      rw [hc]; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
    rw [hmem]
    simp only [Finset.mem_biUnion, Finset.mem_sdiff]
    constructor
    · rintro ⟨z, hz, hℓ, hn⟩; exact ⟨⟨z, hz, hℓ⟩, hn⟩
    · rintro ⟨⟨z, hz, hℓ⟩, hn⟩; exact ⟨z, hz, hℓ, hn⟩

theorem simNames_complete {t : LTerm} {t' : CTerm} {M : Finset Pos} {δ : List Pos}
    (hr : Refines t t'.1) (hM : ∀ x ∈ M, lambdaRS.isStep t x)
    (hδ : lambdaRS.IsCompleteDevelopment t M δ) :
    distRS.names (simDeriv t' δ) = M.biUnion (fun x => simRes t'.1 x) := by
  have h := simDeriv_of_completeDevelopment hr hM hδ
  exact distRS_completeDevelopment_names
    (fun ℓ hℓ => by
      obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp hℓ
      exact simRes_isStep hx) h

/-- Names of the projection of a derivation over a complete development. -/
theorem single_gen : ∀ (σ : List Pos) {t : LTerm} {t' : CTerm} (M : Finset Pos) (δ : List Pos),
    Refines t t'.1 → lambdaRS.Valid t σ → (∀ x ∈ M, lambdaRS.isStep t x) →
    lambdaRS.IsCompleteDevelopment t M δ →
      distRS.names (simDeriv (simTgtDeriv t' δ) (lambdaRS.proj t σ δ)) =
        distRS.names (simDeriv t' σ) \ M.biUnion (fun x => simRes t'.1 x) := by
  intro σ
  induction σ with
  | nil =>
    intro t t' M δ _ _ _ _
    rw [ResidualSystem.proj_nil_left]
    simp [simDeriv, distRS.names]
  | cons p σ' ih =>
    intro t t' M δ hr hv hM hδ
    obtain ⟨hp, hσ'⟩ := hv
    have hvδ : lambdaRS.Valid t δ := ResidualSystem.isDevelopment_valid hδ.1
    have hvp : lambdaRS.Valid t [p] := ResidualSystem.valid_singleton hp
    rw [ResidualSystem.proj_cons_left lambda_orthogonal hp hσ' hvδ, simNames_append]
    -- part A
    have hA : distRS.names (simDeriv (simTgtDeriv t' δ) (lambdaRS.proj t [p] δ)) =
        simRes t'.1 p \ distRS.names (simDeriv t' δ) := by
      have hproj : lambdaRS.proj t [p] δ =
          lambdaRS.dev (lambdaRS.tgt t δ) (lambdaRS.resSetDeriv t {p} δ) := by
        simp [ResidualSystem.proj]
      rw [hproj]
      have hY : ∀ y ∈ lambdaRS.resSetDeriv t {p} δ, lambdaRS.isStep (lambdaRS.tgt t δ) y :=
        ResidualSystem.resSetDeriv_isStep lambda_orthogonal (by simpa using hp) hvδ
      have hrδ : Refines (lambdaRS.tgt t δ) (simTgtDeriv t' δ).1 := (simDeriv_valid hr hvδ).2
      rw [simNames_complete hrδ hY (lambda_orthogonal.dev_complete _ _ hY)]
      exact cube_gen δ p hr hp hvδ
    -- the names of the development
    have hU : distRS.names (simDeriv t' δ) = M.biUnion (fun x => simRes t'.1 x) :=
      simNames_complete hr hM hδ
    -- part B
    have hcomm := ResidualSystem.permGen_join_comm lambda_orthogonal hvδ hvp
    have hperm := (ResidualSystem.permGen_iff_permEq lambda_orthogonal (hcomm.valid_left lambda_orthogonal)
      (hcomm.valid_right lambda_orthogonal)).1 hcomm
    have htg := (compatibility hr (hcomm.valid_left lambda_orthogonal)
      (hcomm.valid_right lambda_orthogonal) hperm).1
    unfold ResidualSystem.join at htg
    rw [simTgtDeriv_append, simTgtDeriv_append] at htg
    have hr' := simulation_canonical hr hp
    have hcd : lambdaRS.IsCompleteDevelopment (lambdaRS.tgt t [p]) (lambdaRS.resSetDeriv t M [p])
        (lambdaRS.proj t δ [p]) :=
      ResidualSystem.proj_isCompleteDevelopment lambda_orthogonal hM hδ hvp
    have hM' : ∀ x ∈ lambdaRS.resSet t M p, lambdaRS.isStep (lambdaRS.contract t p) x := by
      intro x hx
      obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.mp hx
      exact lambda_orthogonal.res_isStep t m p (hM m hm) hp x hxm
    have hIH := ih (t := lambdaRS.contract t p) (t' := simTgt t' p) (lambdaRS.resSet t M p)
      (lambdaRS.proj t δ [p]) hr' hσ' hM' hcd
    rw [show simTgtDeriv (simTgtDeriv t' δ) (lambdaRS.proj t [p] δ) =
      simTgtDeriv (simTgt t' p) (lambdaRS.proj t δ [p]) from htg, hIH, hA, hU, simNames_cons]
    -- the union of simulated residuals
    have hU' : (lambdaRS.resSet t M p).biUnion (fun x => simRes (simTgt t' p).1 x) =
        M.biUnion (fun x => simRes t'.1 x) \ simRes t'.1 p := by
      ext ℓ
      simp only [ResidualSystem.resSet, Finset.mem_biUnion, Finset.mem_sdiff]
      constructor
      · rintro ⟨y, ⟨m, hm, hy⟩, hℓ⟩
        have := cube_sets (t' := t') hr (hM m hm) hp
        have hmem : ℓ ∈ simRes t'.1 m \ simRes t'.1 p := by
          rw [← this]; exact Finset.mem_biUnion.mpr ⟨y, hy, hℓ⟩
        rw [Finset.mem_sdiff] at hmem
        exact ⟨⟨m, hm, hmem.1⟩, hmem.2⟩
      · rintro ⟨⟨m, hm, hℓ⟩, hn⟩
        have := cube_sets (t' := t') hr (hM m hm) hp
        have hmem : ℓ ∈ (lambdaRS.res t p m).biUnion (fun x => simRes (simTgt t' p).1 x) := by
          rw [this]; exact Finset.mem_sdiff.mpr ⟨hℓ, hn⟩
        obtain ⟨y, hy, hℓy⟩ := Finset.mem_biUnion.mp hmem
        exact ⟨y, ⟨m, hm, hy⟩, hℓy⟩
    rw [hU']
    -- disjointness
    have hdis : Disjoint (simRes t'.1 p) (distRS.names (simDeriv (simTgt t' p) σ')) := by
      have hvs := (simDeriv_valid hr (show lambdaRS.Valid t (p :: σ') from ⟨hp, hσ'⟩)).1
      change distRS.Valid t' (distRS.dev t' (simRes t'.1 p) ++ simDeriv (simTgt t' p) σ') at hvs
      have := distRS.names_append_disjoint hvs
      rwa [distRS.names_dev] at this
    ext ℓ
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, fun h => h2 h⟩
      · refine ⟨Or.inr h1, fun h => h2 ⟨h, ?_⟩⟩
        intro hp'
        exact Finset.disjoint_left.mp hdis hp' h1
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, fun h => h2 h⟩
      · exact Or.inr ⟨h1, fun ⟨h, _⟩ => h2 h⟩

theorem gen_names : ∀ (τ : List Pos) {t : LTerm} {t' : CTerm} (σ : List Pos),
    Refines t t'.1 → lambdaRS.Valid t σ → lambdaRS.Valid t τ →
      distRS.names (simDeriv (simTgtDeriv t' τ) (lambdaRS.proj t σ τ)) =
        distRS.names (simDeriv t' σ) \ distRS.names (simDeriv t' τ) := by
  intro τ
  induction τ with
  | nil =>
    intro t t' σ hr hσ _
    rw [ResidualSystem.proj_nil_right lambda_orthogonal hσ]
    simp [simDeriv, distRS.names, simTgtDeriv]
  | cons q τ' ih =>
    intro t t' σ hr hσ hτ
    obtain ⟨hq, hτ'⟩ := hτ
    have hvq : lambdaRS.Valid t [q] := ResidualSystem.valid_singleton hq
    have hfull : lambdaRS.Valid t ([q] ++ τ') := ⟨hq, hτ'⟩
    have hpe := ResidualSystem.proj_append_right lambda_orthogonal (σ := σ) (τ := [q]) (ρ := τ')
      hσ hfull
    have hr' := simulation_canonical hr hq
    have hrb : Refines (lambdaRS.tgt t ([q] ++ τ')) (simTgtDeriv t' ([q] ++ τ')).1 :=
      (simDeriv_valid hr hfull).2
    have hv1 : lambdaRS.Valid (lambdaRS.tgt t ([q] ++ τ'))
        (lambdaRS.proj t σ ([q] ++ τ')) := ResidualSystem.proj_valid lambda_orthogonal hσ hfull
    have hv2 : lambdaRS.Valid (lambdaRS.tgt t ([q] ++ τ'))
        (lambdaRS.proj (lambdaRS.tgt t [q]) (lambdaRS.proj t σ [q]) τ') :=
      ResidualSystem.proj_valid lambda_orthogonal (ResidualSystem.proj_valid lambda_orthogonal hσ hvq) hτ'
    have hcomp := (compatibility hrb hv1 hv2 hpe).2
    have hn := (distRS.permEq_iff_names (simDeriv_valid hrb hv1).1 (simDeriv_valid hrb hv2).1).1 hcomp
    have hIH := ih (t := lambdaRS.contract t q) (t' := simTgt t' q) (lambdaRS.proj t σ [q]) hr'
      (ResidualSystem.proj_valid lambda_orthogonal hσ hvq) hτ'
    have hS := single_gen σ {q} [q] hr hσ (by simpa using hq)
      ((ResidualSystem.isCompleteDevelopment_singleton lambda_orthogonal hq).2 rfl)
    simp only [Finset.singleton_biUnion] at hS
    change distRS.names (simDeriv (simTgtDeriv t' ([q] ++ τ')) (lambdaRS.proj t σ ([q] ++ τ'))) = _
    rw [hn]
    change distRS.names (simDeriv (simTgtDeriv (simTgt t' q) τ')
      (lambdaRS.proj (lambdaRS.contract t q) (lambdaRS.proj t σ [q]) τ')) = _
    rw [hIH, simNames_cons]
    change distRS.names (simDeriv (simTgt t' q) (lambdaRS.proj t σ [q])) \ _ = _
    have hS' : distRS.names (simDeriv (simTgt t' q) (lambdaRS.proj t σ [q])) =
        distRS.names (simDeriv t' σ) \ simRes t'.1 q := hS
    rw [hS']
    ext ℓ
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto

/-- **Generalized cube lemma**: `(σ/t')/(τ/t') ≡ (σ/τ)/(t'/τ)`.

**Gap (proof gap, Lemma 4.19).** The TeX proof (`05-04-simulation-residuals.tex`, lines 353–407) first proves a partial result (2) for a single step `R` by induction on `σ`, then the general case by induction on `ρ = Rρ'`. Three steps fail. (i) Line 6 of the chain needs `(σ/R)/(t'/R) ≡ (σ/t')/(R/t')`, i.e. (2) with the roles swapped, which neither (2) nor the induction hypothesis provides. (ii) (2) is proved for one step but used for the set `R/σ` (a complete development), and its proof reads a family of per-residual derivations as one development without argument. (iii) Line 4 cites (2) for `(t'/σ)/(R/σ) = (t'/R)/(σ/R)`, which actually follows from item 1 of Compatibility. The underlying issue: projecting `Rρ'` over `τ` leaves `ρ'` to be projected over `τ/R`, a development of a set, so an induction on single steps does not close.

**Change (Lemma 4.19).** We prove the equivalent statement on names, `names((ρ/σ)/(t'/σ)) = names(ρ/t') \ names(σ/t')` (`gen_names`), in three claims: a step after a derivation (`cube_gen`, by induction using the basic cube lemma `cube_sets`); a derivation after a complete development of a set `M`, by induction on `ρ` generalizing over `M` (`single_gen`, with `simNames_complete`); and the statement itself, by induction on `σ`. The lemma then follows by `distRS.permEq_iff_names`. -/
theorem generalized_cube_lemma {t : LTerm} {t' : CTerm} {σ τ : List Pos} (hr : Refines t t'.1)
    (hσ : lambdaRS.Valid t σ) (hτ : lambdaRS.Valid t τ) :
    distRS.PermEq (simTgtDeriv t' τ) (distRS.proj t' (simDeriv t' σ) (simDeriv t' τ))
      (simDeriv (simTgtDeriv t' τ) (lambdaRS.proj t σ τ)) := by
  have hvσ := (simDeriv_valid hr hσ).1
  have hvτ := (simDeriv_valid hr hτ).1
  have hv1 := ResidualSystem.proj_valid distRS.orthogonal hvσ hvτ
  have hpj := ResidualSystem.proj_valid lambda_orthogonal hσ hτ
  have hv2 := (simDeriv_valid (simDeriv_valid hr hτ).2 hpj).1
  rw [← tgt_simDeriv] at hv2 ⊢
  rw [distRS.permEq_iff_names hv1 hv2, distRS.names_proj hvσ hvτ, tgt_simDeriv]
  exact (gen_names τ σ hr hσ hτ).symm

/-! ### Algebraic simulation -/

section AlgebraicSimulation

variable {t : LTerm} {t' : CTerm} (hr : Refines t t'.1)

/-- `σ ↦ σ/t'` on derivations. -/
def simDerivFrom (σ : LDeriv t) : distRS.DerivFrom t' :=
  ⟨simDeriv t' σ.1, (simDeriv_valid hr σ.2).1⟩

/-- `[σ] ↦ [σ/t']`, well defined by compatibility. -/
def algSim : DSpaceLam t → DSpaceDist t' :=
  Quotient.map (simDerivFrom hr) fun σ τ h => (compatibility hr σ.2 τ.2 h).2

theorem algSim_mk (σ : LDeriv t) :
    algSim hr (ResidualSystem.DSpace.mk σ) = ResidualSystem.DSpace.mk (simDerivFrom hr σ) := rfl

theorem algSim_bot : algSim hr ⊥ = ⊥ := rfl

theorem algSim_sup (x y : DSpaceLam t) : algSim hr (x ⊔ y) = algSim hr x ⊔ algSim hr y := by
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  rw [ResidualSystem.DSpace.mk_sup_mk, algSim_mk, algSim_mk, algSim_mk,
    ResidualSystem.DSpace.mk_sup_mk, ResidualSystem.DSpace.mk_eq_mk]
  change distRS.PermEq t'
    (simDeriv t' (lambdaRS.join t σ.1 τ.1))
    (distRS.join t' (simDeriv t' σ.1) (simDeriv t' τ.1))
  rw [ResidualSystem.join, simDeriv_append, ResidualSystem.join]
  have hs := (simDeriv_valid hr σ.2).1
  have ht := (simDeriv_valid hr τ.2).1
  have hc := generalized_cube_lemma hr τ.2 σ.2
  rw [← tgt_simDeriv] at hc
  have hp := ResidualSystem.proj_valid distRS.orthogonal ht hs
  have hl := (simDeriv_valid (simDeriv_valid hr σ.2).2
    (ResidualSystem.proj_valid lambda_orthogonal τ.2 σ.2)).1
  rw [← tgt_simDeriv] at hl
  rw [← tgt_simDeriv t' σ.1]
  exact ⟨(ResidualSystem.prefix_append_iff distRS.orthogonal hs hl hp).1 hc.2,
    (ResidualSystem.prefix_append_iff distRS.orthogonal hs hp hl).1 hc.1⟩

/-- **Corollary (Algebraic simulation)**: for `t' ⋉ t`, the map `𝔻_λ(t) → 𝔻^dist(t')`,
`[σ] ↦ [σ/t']` is a morphism of upper semilattices (with bottom). -/
def algebraicSimulation : SupBotHom (DSpaceLam t) (DSpaceDist t') where
  toFun := algSim hr
  map_sup' := algSim_sup hr
  map_bot' := algSim_bot hr

theorem algebraicSimulation_mono : Monotone (algebraicSimulation hr) :=
  OrderHomClass.mono (algebraicSimulation hr)

end AlgebraicSimulation

end Ch4Main

end CiruelosLic
