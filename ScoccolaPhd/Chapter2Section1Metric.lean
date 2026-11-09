import Mathlib

/-!
# Chapter 1 and §§2.1–2.3: metric spaces and monoidal categories

Contents:
* Chapter 1: Introduction
* Chapter 2.1–2.2: Extended pseudo metric spaces
* Chapter 2.3: Monoidal categories
-/

universe u v

namespace ScoccolaPhd

/-! ## Chapter 1: Introduction

Luis N. Scoccola, *Locally Persistent Categories and Metric Properties of Interleaving
Distances* (PhD thesis, Western University, 2020).

Chapter 1 (motivation, contributions, related work) contains no formal definitions or
theorems of its own. The statements it advertises (Theorems A–I) are stated in the chapters
where they are proved (Theorem A = 4.2.2, B = 4.1.4, C = 4.3.3, D = 4.4.2, E = 6.1.7,
F = 6.2.21, G = 5.1.11, H = 6.5.1, I = 6.7.2) and will be formalized with those chapters. -/

end ScoccolaPhd



namespace ScoccolaPhd

/-! ## Chapter 2.1–2.2: Extended pseudo metric spaces

An *extended pseudo metric space* (Definition 2.2.1) is Mathlib's `PseudoEMetricSpace`:
a distance `edist : P → P → ℝ≥0∞` that is reflexive, symmetric and satisfies the triangle
inequality. A *metric space* (Definition 2.2.3) is Mathlib's `MetricSpace`.

Includes proofs of compactness (2.2.12), completeness of pseudo retracts (2.2.17),
and the quotient metric specification (2.2.19). -/

section Metric

open scoped ENNReal NNReal Topology
open Set

/-! ### 2.2.1 Elementary notions -/

/-- Definition 2.2.1: ep metric spaces are `PseudoEMetricSpace`s. -/
abbrev EPMetricSpace := PseudoEMetricSpace

/-- Definition 2.2.4: a distance non-increasing (1-Lipschitz) map. -/
def IsDistNonIncreasing {P : Type u} {Q : Type v} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    (f : P → Q) : Prop :=
  ∀ p p', edist p p' ≥ edist (f p) (f p')

/-- Definition 2.2.6: a distance preserving map. -/
def IsDistPreserving {P : Type u} {Q : Type v} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    (f : P → Q) : Prop :=
  ∀ p p', edist p p' = edist (f p) (f p')

/-- Bundled ep metric spaces. -/
structure EPMet where
  carrier : Type u
  [str : PseudoEMetricSpace carrier]

attribute [instance] EPMet.str

instance : CoeSort EPMet.{u} (Type u) := ⟨EPMet.carrier⟩

/-- Definition 2.2.5: the category `epMet`, with distance non-increasing maps as morphisms. -/
instance : CategoryTheory.Category EPMet.{u} where
  Hom P Q := {f : P → Q // IsDistNonIncreasing f}
  id P := ⟨id, fun _ _ => le_rfl⟩
  comp f g := ⟨g.1 ∘ f.1, fun p p' => le_trans (g.2 _ _) (f.2 p p')⟩

/-! ### 2.2.2 Properties of a metric -/

section Properties

variable {P : Type u} [PseudoEMetricSpace P]

/-- Definition 2.2.7. -/
def IsCauchySequence (x : ℕ → P) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ n : ℕ, ∀ i j, n ≤ i → n ≤ j → edist (x i) (x j) < ε

/-- Definition 2.2.8: `l` is a limit of the sequence `x`. -/
def IsLimit (x : ℕ → P) (l : P) : Prop :=
  Filter.Tendsto (fun i => edist (x i) l) Filter.atTop (𝓝 0)

/-- Definition 2.2.8. -/
def IsConvergentSequence (x : ℕ → P) : Prop :=
  ∃ l, IsLimit x l

/-- Definition 2.2.9. -/
def IsCompleteEP (P : Type u) [PseudoEMetricSpace P] : Prop :=
  ∀ x : ℕ → P, IsCauchySequence x → IsConvergentSequence x

omit [PseudoEMetricSpace P] in
/-- Definitions 2.2.7–2.2.9 for a bare distance function `d`: `d` is complete if every
`d`-Cauchy sequence has a `d`-limit. -/
def IsCompleteDist (d : P → P → ℝ≥0∞) : Prop :=
  ∀ x : ℕ → P, (∀ ε : ℝ≥0∞, 0 < ε → ∃ n : ℕ, ∀ i j, n ≤ i → n ≤ j → d (x i) (x j) < ε) →
    ∃ l, Filter.Tendsto (fun i => d (x i) l) Filter.atTop (𝓝 0)

/-- Definition 2.2.10. -/
def IsTotallyBoundedEP (P : Type u) [PseudoEMetricSpace P] : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ s : Finset P, (univ : Set P) ⊆ ⋃ p ∈ s, Metric.eball p ε

/-- Definition 2.2.11: every sequence has a convergent subsequence. -/
def IsCompactEP (P : Type u) [PseudoEMetricSpace P] : Prop :=
  ∀ x : ℕ → P, ∃ φ : ℕ → ℕ, StrictMono φ ∧ IsConvergentSequence (x ∘ φ)

/-- Lemma 2.2.12. -/
theorem isCompactEP_iff_complete_and_totallyBounded :
    IsCompactEP P ↔ IsCompleteEP P ∧ IsTotallyBoundedEP P := by
  classical
  have hc : IsCompactEP P ↔ IsCompact (univ : Set P) := by
    rw [isCompact_iff_isSeqCompact]
    simp only [IsCompactEP, IsSeqCompact, IsConvergentSequence, IsLimit,
      ← tendsto_iff_edist_tendsto_0, mem_univ, forall_const, true_and]
    constructor
    · intro h x
      obtain ⟨φ, hφ, l, hl⟩ := h x
      exact ⟨l, φ, hφ, hl⟩
    · intro h x
      obtain ⟨l, φ, hφ, hl⟩ := h (x := x)
      exact ⟨φ, hφ, l, hl⟩
  have ht : IsTotallyBoundedEP P ↔ TotallyBounded (univ : Set P) := by
    rw [EMetric.totallyBounded_iff]
    constructor
    · intro h ε hε
      obtain ⟨s, hs⟩ := h ε hε
      exact ⟨s, s.finite_toSet, hs⟩
    · intro h ε hε
      obtain ⟨s, hs, hsub⟩ := h ε hε
      exact ⟨hs.toFinset, by simpa using hsub⟩
  have hcomplete : IsCompleteEP P ↔ CompleteSpace P := by
    constructor
    · intro h
      apply UniformSpace.complete_of_cauchySeq_tendsto
      intro x hx
      obtain ⟨l, hl⟩ := h x (by
        intro ε hε
        obtain ⟨n, hn⟩ := EMetric.cauchySeq_iff.mp hx ε hε
        exact ⟨n, fun i j hi hj => hn i hi j hj⟩)
      exact ⟨l, tendsto_iff_edist_tendsto_0.mpr hl⟩
    · intro h x hx
      have hx' : CauchySeq x := EMetric.cauchySeq_iff.mpr fun ε hε => by
        obtain ⟨n, hn⟩ := hx ε hε
        exact ⟨n, fun i hi j hj => hn i j hi hj⟩
      obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hx'
      exact ⟨l, tendsto_iff_edist_tendsto_0.mp hl⟩
  rw [hc, hcomplete, ht, isCompact_iff_totallyBounded_isComplete,
    ← completeSpace_iff_isComplete_univ, and_comm]

omit [PseudoEMetricSpace P] in
/-- Continuity of a path `f : ℝ → P` on `[a, b]` with respect to a distance function `d`. -/
def IsPathOn (d : P → P → ℝ≥0∞) (a b : ℝ) (f : ℝ → P) : Prop :=
  ∀ t ∈ Icc a b, ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc a b, |s - t| < δ →
    d (f s) (f t) < ε

omit [PseudoEMetricSpace P] in
/-- Definition 2.2.13: the length of a path `f : [a, b] → P` with respect to the distance
function `d`: the supremum of the sums `∑ d (f (y (i-1))) (f (y i))` over all finite
partitions `a = y₀ ≤ ⋯ ≤ y_N = b`. -/
noncomputable def pathLength (d : P → P → ℝ≥0∞) (a b : ℝ) (f : ℝ → P) : ℝ≥0∞ :=
  ⨆ (N : ℕ) (y : ℕ → ℝ) (_ : y 0 = a) (_ : y N = b) (_ : Monotone y),
    ∑ i ∈ Finset.range N, d (f (y i)) (f (y (i + 1)))

omit [PseudoEMetricSpace P] in
/-- Definition 2.2.14 for a distance function `d`: any two points at finite distance are
joined by a continuous path whose length equals their distance. -/
def IsGeodesicDist (d : P → P → ℝ≥0∞) : Prop :=
  ∀ p p' : P, d p p' < ∞ →
    ∃ (a b : ℝ) (f : ℝ → P), a ≤ b ∧ IsPathOn d a b f ∧ f a = p ∧ f b = p' ∧
      pathLength d a b f = d p p'

omit [PseudoEMetricSpace P] in
/-- Definition 2.2.15 for a distance function `d`: `d p p'` is the infimum of the lengths of
paths between `p` and `p'`. -/
def IsIntrinsicDist (d : P → P → ℝ≥0∞) : Prop :=
  ∀ p p' : P, d p p' =
    ⨅ (a : ℝ) (b : ℝ) (f : ℝ → P) (_ : a ≤ b) (_ : IsPathOn d a b f) (_ : f a = p)
      (_ : f b = p'), pathLength d a b f

/-- Definition 2.2.14. -/
abbrev IsGeodesicEP (P : Type u) [PseudoEMetricSpace P] : Prop := IsGeodesicDist (edist (α := P))

/-- Definition 2.2.15. -/
abbrev IsIntrinsicEP (P : Type u) [PseudoEMetricSpace P] : Prop := IsIntrinsicDist (edist (α := P))

/-- Definition 2.2.16: `P` is a pseudo retract of `Q`. -/
def IsPseudoRetract (P : Type u) (Q : Type v) [PseudoEMetricSpace P] [PseudoEMetricSpace Q] :
    Prop :=
  ∃ (s : P → Q) (r : Q → P), IsDistNonIncreasing s ∧ IsDistNonIncreasing r ∧
    ∀ p, edist p (r (s p)) = 0

/-- Lemma 2.2.17 (complete case). -/
theorem IsPseudoRetract.isCompleteEP {Q : Type v} [PseudoEMetricSpace Q]
    (h : IsPseudoRetract P Q) (hQ : IsCompleteEP Q) : IsCompleteEP P := by
  obtain ⟨s, r, hs, hr, hsr⟩ := h
  intro x hx
  have hc : IsCauchySequence (s ∘ x) := fun ε hε => by
    obtain ⟨n, hn⟩ := hx ε hε
    exact ⟨n, fun i j hi hj => lt_of_le_of_lt (hs _ _) (hn i j hi hj)⟩
  obtain ⟨l, hl⟩ := hQ _ hc
  refine ⟨r l, ?_⟩
  unfold IsLimit at hl ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _ => zero_le) ?_
  intro i
  calc edist (x i) (r l) ≤ edist (x i) (r (s (x i))) + edist (r (s (x i))) (r l) :=
        edist_triangle _ _ _
    _ ≤ 0 + edist (s (x i)) l := add_le_add (hsr _).le (hr _ _)
    _ = edist ((s ∘ x) i) l := by simp

omit [PseudoEMetricSpace P] in
lemma dist_le_pathLength (d : P → P → ℝ≥0∞) {a b : ℝ} {f : ℝ → P} (hab : a ≤ b) :
    d (f a) (f b) ≤ pathLength d a b f := by
  refine le_iSup_of_le 1 (le_iSup_of_le (fun n => if n = 0 then a else b) ?_)
  refine le_iSup_of_le (by simp) (le_iSup_of_le (by simp) (le_iSup_of_le ?_ ?_))
  · intro m n hmn
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all
  · simp

lemma edist_le_pathLength {a b : ℝ} {f : ℝ → P} (hab : a ≤ b) :
    edist (f a) (f b) ≤ pathLength (edist (α := P)) a b f :=
  dist_le_pathLength edist hab

lemma exists_path_of_edist_zero (p p' : P) (hp : edist p p' = 0) :
    ∃ f : ℝ → P, IsPathOn edist 0 1 f ∧ f 0 = p ∧ f 1 = p' ∧
      pathLength (edist (α := P)) 0 1 f = 0 := by
  let f : ℝ → P := fun t => if t < 1 then p else p'
  have hf0 : f 0 = p := by simp [f]
  have hf1 : f 1 = p' := by simp [f]
  have h_edist : ∀ s t, edist (f s) (f t) = 0 := by
    intro s t
    dsimp [f]
    by_cases hs : s < 1 <;> by_cases ht : t < 1 <;> simp [hs, ht, hp]
    · rw [edist_comm]; exact hp
  have h_path : IsPathOn edist 0 1 f := by
    intro t _ ε hε
    refine ⟨1, by norm_num, fun s _ _ => ?_⟩
    rw [h_edist s t]
    exact hε
  have h_len : pathLength (edist (α := P)) 0 1 f = 0 := by
    refine le_antisymm ?_ zero_le
    refine iSup_le fun N => iSup_le fun y => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => ?_
    simp [h_edist]
  exact ⟨f, h_path, hf0, hf1, h_len⟩

lemma exists_path_of_retract {Q : Type v} [PseudoEMetricSpace Q]
    (s : P → Q) (r : Q → P) (_hs : IsDistNonIncreasing s)
    (hr : IsDistNonIncreasing r) (hsr : ∀ p, edist p (r (s p)) = 0)
    (p p' : P) (a b : ℝ) (hab : a < b) (g : ℝ → Q) (hg : IsPathOn edist a b g)
    (hga : g a = s p) (hgb : g b = s p') :
    ∃ f : ℝ → P, IsPathOn edist a b f ∧ f a = p ∧ f b = p' ∧
      pathLength (edist (α := P)) a b f ≤ pathLength (edist (α := Q)) a b g := by
  let f : ℝ → P := fun t => if t ≤ a then p else if b ≤ t then p' else r (g t)
  have hfa : f a = p := by simp [f]
  have hfb : f b = p' := by
    have : ¬(b ≤ a) := not_le_of_gt hab
    simp [f, this]
  have h_close : ∀ t ∈ Icc a b, edist (f t) (r (g t)) = 0 ∧ edist (r (g t)) (f t) = 0 := by
    intro t ht
    dsimp [f]
    by_cases hta : t ≤ a
    · have heq : t = a := le_antisymm hta ht.1
      subst heq
      simp only [le_rfl, ↓reduceIte, hga]
      exact ⟨hsr p, by rw [edist_comm]; exact hsr p⟩
    · simp only [hta, ↓reduceIte]
      by_cases hbt : b ≤ t
      · have heq : t = b := le_antisymm ht.2 hbt
        subst heq
        simp only [le_rfl, ↓reduceIte, hgb]
        exact ⟨hsr p', by rw [edist_comm]; exact hsr p'⟩
      · simp only [hbt, ↓reduceIte]
        exact ⟨edist_self _, edist_self _⟩
  have h_dist : ∀ t1 ∈ Icc a b, ∀ t2 ∈ Icc a b, edist (f t1) (f t2) ≤ edist (g t1) (g t2) := by
    intro t1 ht1 t2 ht2
    obtain ⟨h1a, _⟩ := h_close t1 ht1
    obtain ⟨_, h2b⟩ := h_close t2 ht2
    calc edist (f t1) (f t2) ≤ edist (f t1) (r (g t1)) + edist (r (g t1)) (f t2) := edist_triangle _ _ _
      _ = edist (r (g t1)) (f t2) := by rw [h1a, zero_add]
      _ ≤ edist (r (g t1)) (r (g t2)) + edist (r (g t2)) (f t2) := edist_triangle _ _ _
      _ = edist (r (g t1)) (r (g t2)) := by rw [h2b, add_zero]
      _ ≤ edist (g t1) (g t2) := hr _ _
  have h_path : IsPathOn edist a b f := by
    intro t ht ε hε
    obtain ⟨δ, hδ, hgδ⟩ := hg t ht ε hε
    refine ⟨δ, hδ, fun t' ht' hdist => ?_⟩
    exact lt_of_le_of_lt (h_dist t' ht' t ht) (hgδ t' ht' hdist)
  have h_len : pathLength (edist (α := P)) a b f ≤ pathLength (edist (α := Q)) a b g := by
    refine iSup_le fun N => iSup_le fun y => iSup_le fun hy0 => iSup_le fun hyN =>
      iSup_le fun hmono => ?_
    have hy_mem : ∀ i ≤ N, y i ∈ Icc a b := by
      intro i hi
      have h0i : y 0 ≤ y i := hmono (Nat.zero_le i)
      have hiN : y i ≤ y N := hmono hi
      rw [hy0] at h0i; rw [hyN] at hiN
      exact ⟨h0i, hiN⟩
    calc ∑ i ∈ Finset.range N, edist (f (y i)) (f (y (i + 1)))
        ≤ ∑ i ∈ Finset.range N, edist (g (y i)) (g (y (i + 1))) :=
          Finset.sum_le_sum fun i hi => by
            rw [Finset.mem_range] at hi
            exact h_dist (y i) (hy_mem i (by omega)) (y (i + 1)) (hy_mem (i + 1) (by omega))
      _ ≤ pathLength (edist (α := Q)) a b g :=
          le_iSup_of_le N (le_iSup_of_le y (le_iSup_of_le hy0 (le_iSup_of_le hyN (le_iSup_of_le hmono le_rfl))))
  exact ⟨f, h_path, hfa, hfb, h_len⟩

/-- Lemma 2.2.17 (intrinsic case). -/
theorem IsPseudoRetract.isIntrinsicEP {Q : Type v} [PseudoEMetricSpace Q]
    (h : IsPseudoRetract P Q) (hQ : IsIntrinsicEP Q) : IsIntrinsicEP P := by
  obtain ⟨s, r, hs, hr, hsr⟩ := h
  have h_edist : ∀ p p' : P, edist (s p) (s p') = edist p p' := by
    intro p p'
    refine le_antisymm (hs p p') ?_
    calc edist p p' ≤ edist p (r (s p)) + edist (r (s p)) p' := edist_triangle _ _ _
      _ = edist (r (s p)) p' := by rw [hsr p, zero_add]
      _ ≤ edist (r (s p)) (r (s p')) + edist (r (s p')) p' := edist_triangle _ _ _
      _ = edist (r (s p)) (r (s p')) := by rw [edist_comm (r (s p')) p', hsr p', add_zero]
      _ ≤ edist (s p) (s p') := hr _ _
  intro p p'
  apply le_antisymm
  · refine le_iInf fun a => le_iInf fun b => le_iInf fun f => le_iInf fun hab =>
      le_iInf fun _ => le_iInf fun hfa => le_iInf fun hfb => ?_
    rw [← hfa, ← hfb]
    exact edist_le_pathLength hab
  · by_cases hp0 : edist p p' = 0
    · obtain ⟨f, hf_path, hf0, hf1, hf_len⟩ := exists_path_of_edist_zero p p' hp0
      have h01 : (0 : ℝ) ≤ 1 := by norm_num
      have : (⨅ (a : ℝ) (b : ℝ) (f : ℝ → P) (_ : a ≤ b) (_ : IsPathOn edist a b f)
          (_ : f a = p) (_ : f b = p'), pathLength edist a b f) ≤ 0 :=
        iInf_le_of_le 0 (iInf_le_of_le 1 (iInf_le_of_le f (iInf_le_of_le h01
          (iInf_le_of_le hf_path (iInf_le_of_le hf0 (iInf_le_of_le hf1 (le_of_eq hf_len)))))))
      exact this.trans (le_of_eq hp0.symm)
    · rw [← h_edist p p', hQ (s p) (s p')]
      refine le_iInf fun a => le_iInf fun b => le_iInf fun g => le_iInf fun hab =>
        le_iInf fun hg => le_iInf fun hga => le_iInf fun hgb => ?_
      have hlt : a < b := by
        by_contra h_not
        have hab_eq : a = b := le_antisymm hab (not_lt.mp h_not)
        subst hab_eq
        have h_eq : s p = s p' := by rw [← hga, ← hgb]
        have : edist (s p) (s p') = 0 := by rw [h_eq, edist_self]
        rw [h_edist] at this
        exact hp0 this
      obtain ⟨f, hf_path, hfa, hfb, hf_len⟩ :=
        exists_path_of_retract s r hs hr hsr p p' a b hlt g hg hga hgb
      exact le_trans (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le f (iInf_le_of_le hlt.le
        (iInf_le_of_le hf_path (iInf_le_of_le hfa (iInf_le_of_le hfb le_rfl))))))) hf_len

/-- Lemma 2.2.17 (geodesic case). -/
theorem IsPseudoRetract.isGeodesicEP {Q : Type v} [PseudoEMetricSpace Q]
    (h : IsPseudoRetract P Q) (hQ : IsGeodesicEP Q) : IsGeodesicEP P := by
  obtain ⟨s, r, hs, hr, hsr⟩ := h
  have h_edist : ∀ p p' : P, edist (s p) (s p') = edist p p' := by
    intro p p'
    refine le_antisymm (hs p p') ?_
    calc edist p p' ≤ edist p (r (s p)) + edist (r (s p)) p' := edist_triangle _ _ _
      _ = edist (r (s p)) p' := by rw [hsr p, zero_add]
      _ ≤ edist (r (s p)) (r (s p')) + edist (r (s p')) p' := edist_triangle _ _ _
      _ = edist (r (s p)) (r (s p')) := by rw [edist_comm (r (s p')) p', hsr p', add_zero]
      _ ≤ edist (s p) (s p') := hr _ _
  intro p p' hp
  by_cases hp0 : edist p p' = 0
  · obtain ⟨f, hf_path, hf0, hf1, hf_len⟩ := exists_path_of_edist_zero p p' hp0
    refine ⟨0, 1, f, by norm_num, hf_path, hf0, hf1, ?_⟩
    rw [hf_len, hp0]
  · have hQ_lt : edist (s p) (s p') < ∞ := by rw [h_edist]; exact hp
    obtain ⟨a, b, g, hab, hg, hga, hgb, hg_len⟩ := hQ (s p) (s p') hQ_lt
    have hlt : a < b := by
      by_contra h_not
      have hab_eq : a = b := le_antisymm hab (not_lt.mp h_not)
      subst hab_eq
      have h_eq : s p = s p' := by rw [← hga, ← hgb]
      have : edist (s p) (s p') = 0 := by rw [h_eq, edist_self]
      rw [h_edist] at this
      exact hp0 this
    obtain ⟨f, hf_path, hfa, hfb, hf_len⟩ :=
      exists_path_of_retract s r hs hr hsr p p' a b hlt g hg hga hgb
    refine ⟨a, b, f, hlt.le, hf_path, hfa, hfb, ?_⟩
    apply le_antisymm
    · rw [← h_edist p p', ← hg_len]
      exact hf_len
    · rw [← hfa, ← hfb]
      exact edist_le_pathLength hlt.le

end Properties

/-! ### 2.2.3 Quotients of metrics -/

section Quotients

/-- The axioms of Definition 2.2.1 for a bare distance function. -/
structure IsEPMetric {X : Type u} (d : X → X → ℝ≥0∞) : Prop where
  refl : ∀ x, d x x = 0
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- Definition 2.2.18: `d` is `R`-invariant. -/
def IsInvariant {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop) : Prop :=
  ∀ x x' y y', R x x' → R y y' → d x y = d x' y'

/-- Proposition 2.2.19 / Definition 2.2.20: the quotient ep metric `d / R`, the greatest
`R`-invariant ep metric below `d`. -/
noncomputable def quotientDist {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop)
    (x y : X) : ℝ≥0∞ :=
  ⨆ (d' : X → X → ℝ≥0∞) (_ : IsEPMetric d') (_ : ∀ a b, d' a b ≤ d a b)
    (_ : IsInvariant d' R), d' x y

/-- Proposition 2.2.19, condition (1) for `quotientDist`: `d/R ≤ d`. -/
theorem quotientDist_le {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop) (x y : X) :
    quotientDist d R x y ≤ d x y :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun h => iSup_le fun _ => h x y

/-- Proposition 2.2.19, condition (3) for `quotientDist`: any `R`-invariant ep metric below `d`
is below `d/R`. -/
theorem le_quotientDist {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop)
    (d' : X → X → ℝ≥0∞) (h1 : IsEPMetric d') (h2 : ∀ a b, d' a b ≤ d a b)
    (h3 : IsInvariant d' R) (x y : X) : d' x y ≤ quotientDist d R x y :=
  le_iSup_of_le d' (le_iSup_of_le h1 (le_iSup_of_le h2 (le_iSup_of_le h3 le_rfl)))

/-- Proposition 2.2.19, condition (2) for `quotientDist`: `d/R` is `R`-invariant. -/
theorem quotientDist_isInvariant {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop)
    (hR : Equivalence R) : IsInvariant (quotientDist d R) R := by
  have key : ∀ x x' y y', R x x' → R y y' →
      quotientDist d R x y ≤ quotientDist d R x' y' := by
    intro x x' y y' hx hy
    refine iSup_le fun d' => iSup_le fun h1 => iSup_le fun h2 => iSup_le fun h3 => ?_
    rw [h3 x x' y y' hx hy]
    exact le_quotientDist d R d' h1 h2 h3 x' y'
  intro x x' y y' hx hy
  exact le_antisymm (key x x' y y' hx hy) (key x' x y' y (hR.symm hx) (hR.symm hy))

/-- Proposition 2.2.19: the quotient `d / R` is an ep metric (a supremum of ep metrics). -/
theorem quotientDist_isEPMetric {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop) :
    IsEPMetric (quotientDist d R) where
  refl x := le_antisymm
    (iSup_le fun _ => iSup_le fun h1 => iSup_le fun _ => iSup_le fun _ => (h1.refl x).le)
    zero_le
  symm x y := le_antisymm
    (iSup_le fun d' => iSup_le fun h1 => iSup_le fun h2 => iSup_le fun h3 =>
      (h1.symm x y).le.trans (le_quotientDist d R d' h1 h2 h3 y x))
    (iSup_le fun d' => iSup_le fun h1 => iSup_le fun h2 => iSup_le fun h3 =>
      (h1.symm y x).le.trans (le_quotientDist d R d' h1 h2 h3 x y))
  triangle x y z := iSup_le fun d' => iSup_le fun h1 => iSup_le fun h2 => iSup_le fun h3 =>
    (h1.triangle x y z).trans (add_le_add (le_quotientDist d R d' h1 h2 h3 x y)
      (le_quotientDist d R d' h1 h2 h3 y z))

/-- The distance "infimum of the `a` for which `P x y a` holds" is an ep metric as soon as
`P` is reflexive at `0`, symmetric, and additive along composition. -/
theorem isEPMetric_iInf {X : Type u} (P : X → X → ℝ≥0 → Prop) (hrefl : ∀ x, P x x 0)
    (hsymm : ∀ x y a, P x y a → P y x a) (htrans : ∀ x y z a b, P x y a → P y z b → P x z (a + b)) :
    IsEPMetric (fun x y => ⨅ (a : ℝ≥0) (_ : P x y a), (a : ℝ≥0∞)) where
  refl x := le_antisymm (iInf₂_le_of_le 0 (hrefl x) (by simp)) zero_le
  symm x y := le_antisymm
    (le_iInf₂ fun a h => iInf₂_le_of_le a (hsymm _ _ _ h) le_rfl)
    (le_iInf₂ fun a h => iInf₂_le_of_le a (hsymm _ _ _ h) le_rfl)
  triangle x y z := by
    set D : X → X → ℝ≥0∞ := fun x y => ⨅ (a : ℝ≥0) (_ : P x y a), (a : ℝ≥0∞) with hD
    show D x z ≤ D x y + D y z
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hb
    have hb1 : D x y < ⊤ := lt_of_le_of_lt le_self_add hb
    have hb2 : D y z < ⊤ := lt_of_le_of_lt le_add_self hb
    have he : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := by simpa using hε.ne'
    have hne : (ε : ℝ≥0∞) / 2 ≠ 0 := he.ne'
    have pick : ∀ u v : X, D u v < ⊤ → ∃ a : ℝ≥0, P u v a ∧
        (a : ℝ≥0∞) < D u v + (ε : ℝ≥0∞) / 2 := by
      intro u v hlt
      have := ENNReal.lt_add_right hlt.ne hne
      rw [hD] at this ⊢
      simp only at this ⊢
      rw [iInf_lt_iff] at this
      obtain ⟨a, ha⟩ := this
      rw [iInf_lt_iff] at ha
      obtain ⟨h, hlt⟩ := ha
      exact ⟨a, h, hlt⟩
    obtain ⟨a, h₁, ha⟩ := pick x y hb1
    obtain ⟨b, h₂, hb'⟩ := pick y z hb2
    have h3 : D x z ≤ ((a + b : ℝ≥0) : ℝ≥0∞) :=
      iInf₂_le (a + b) (htrans _ _ _ _ _ h₁ h₂)
    calc D x z ≤ ((a + b : ℝ≥0) : ℝ≥0∞) := h3
      _ = (a : ℝ≥0∞) + b := by push_cast; rfl
      _ ≤ (D x y + (ε : ℝ≥0∞) / 2) + (D y z + (ε : ℝ≥0∞) / 2) := add_le_add ha.le hb'.le
      _ = D x y + D y z + (ε : ℝ≥0∞) := by rw [add_add_add_comm, ENNReal.add_halves]

/-- Proposition 2.2.19: `d / R` is an ep metric satisfying conditions (1)–(3). -/
theorem quotientDist_spec {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d)
    (R : X → X → Prop) (hR : Equivalence R) :
    IsEPMetric (quotientDist d R) ∧ (∀ x y, quotientDist d R x y ≤ d x y) ∧
      IsInvariant (quotientDist d R) R ∧
      ∀ d' : X → X → ℝ≥0∞, IsEPMetric d' → (∀ x y, d' x y ≤ d x y) → IsInvariant d' R →
        ∀ x y, d' x y ≤ quotientDist d R x y := by
  exact ⟨quotientDist_isEPMetric d R, quotientDist_le d R, quotientDist_isInvariant d R hR,
    fun d' h1 h2 h3 => le_quotientDist d R d' h1 h2 h3⟩

/-- Proposition 2.2.19 (uniqueness). -/
theorem quotientDist_unique {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d)
    (R : X → X → Prop) (hR : Equivalence R) (q : X → X → ℝ≥0∞) (hq : IsEPMetric q)
    (h1 : ∀ x y, q x y ≤ d x y) (h2 : IsInvariant q R)
    (h3 : ∀ d' : X → X → ℝ≥0∞, IsEPMetric d' → (∀ x y, d' x y ≤ d x y) → IsInvariant d' R →
        ∀ x y, d' x y ≤ q x y) :
    q = quotientDist d R := by
  obtain ⟨m1, m2, m3, m4⟩ := quotientDist_spec d hd R hR
  funext x y
  exact le_antisymm (m4 q hq h1 h2 x y) (h3 _ m1 m2 m3 x y)

/-- Lemma 2.2.21 (formula for the quotient): the infimum of `∑ d (y i) (y' i)` over chains
`p R y 0`, `y' i R y (i+1)`, `y' N R p'`. -/
noncomputable def chainDist {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop) (p p' : X) :
    ℝ≥0∞ :=
  ⨅ (N : ℕ) (y : ℕ → X) (y' : ℕ → X) (_ : R p (y 0)) (_ : ∀ i < N, R (y' i) (y (i + 1)))
    (_ : R (y' N) p'),
    ∑ i ∈ Finset.range (N + 1), d (y i) (y' i)

lemma chain_concat {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop) (hR : Equivalence R)
    (p p' p'' : X)
    (N1 : ℕ) (y1 y'1 : ℕ → X) (hy1_0 : R p (y1 0)) (hchain1 : ∀ i < N1, R (y'1 i) (y1 (i + 1)))
    (hy'1_N1 : R (y'1 N1) p')
    (N2 : ℕ) (y2 y'2 : ℕ → X) (hy2_0 : R p' (y2 0)) (hchain2 : ∀ i < N2, R (y'2 i) (y2 (i + 1)))
    (hy'2_N2 : R (y'2 N2) p'') :
    chainDist d R p p'' ≤
      (∑ i ∈ Finset.range (N1 + 1), d (y1 i) (y'1 i)) +
      (∑ j ∈ Finset.range (N2 + 1), d (y2 j) (y'2 j)) := by
  let N := N1 + N2 + 1
  let y : ℕ → X := fun i => if i ≤ N1 then y1 i else y2 (i - (N1 + 1))
  let y' : ℕ → X := fun i => if i ≤ N1 then y'1 i else y'2 (i - (N1 + 1))
  have hy0 : R p (y 0) := by
    change R p (if 0 ≤ N1 then y1 0 else y2 (0 - (N1 + 1)))
    simp [hy1_0]
  have hy'N : R (y' N) p'' := by
    change R (if N ≤ N1 then y'1 N else y'2 (N - (N1 + 1))) p''
    have : ¬(N ≤ N1) := by dsimp [N]; omega
    have hN2 : N - (N1 + 1) = N2 := by dsimp [N]; omega
    simp [this, hN2, hy'2_N2]
  have hchain : ∀ i < N, R (y' i) (y (i + 1)) := by
    intro i hi
    by_cases hi_lt : i < N1
    · have hi_le : i ≤ N1 := le_of_lt hi_lt
      have hi1_le : i + 1 ≤ N1 := hi_lt
      change R (if i ≤ N1 then y'1 i else _) (if i + 1 ≤ N1 then y1 (i + 1) else _)
      simp [hi_le, hi1_le, hchain1 i hi_lt]
    · by_cases hi_eq : i = N1
      · have heq : i = N1 := hi_eq
        change R (if i ≤ N1 then y'1 i else _) (if i + 1 ≤ N1 then y1 (i + 1) else _)
        simp [heq, hR.trans hy'1_N1 hy2_0]
      · have hi_gt : N1 < i := lt_of_le_of_ne (not_lt.mp hi_lt) (Ne.symm hi_eq)
        have hi_not : ¬(i ≤ N1) := not_le_of_gt hi_gt
        have hi1_not : ¬(i + 1 ≤ N1) := not_le_of_gt (by omega)
        change R (if i ≤ N1 then y'1 i else _) (if i + 1 ≤ N1 then y1 (i + 1) else _)
        have hsub : i + 1 - (N1 + 1) = (i - (N1 + 1)) + 1 := by omega
        have hj : i - (N1 + 1) < N2 := by dsimp [N] at hi; omega
        simp [hi_not, hi1_not, hsub, hchain2 (i - (N1 + 1)) hj]
  have hsum : ∑ i ∈ Finset.range (N + 1), d (y i) (y' i) =
      (∑ i ∈ Finset.range (N1 + 1), d (y1 i) (y'1 i)) +
      (∑ j ∈ Finset.range (N2 + 1), d (y2 j) (y'2 j)) := by
    have hsplit : N + 1 = (N1 + 1) + (N2 + 1) := by dsimp [N]; omega
    rw [hsplit, Finset.sum_range_add]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      have : i ≤ N1 := Nat.lt_succ_iff.mp hi
      change d (if i ≤ N1 then y1 i else _) (if i ≤ N1 then y'1 i else _) = _
      simp [this]
    · refine Finset.sum_congr rfl fun j _ => ?_
      have : ¬((N1 + 1 + j) ≤ N1) := by omega
      have hj : N1 + 1 + j - (N1 + 1) = j := by omega
      change d (if N1 + 1 + j ≤ N1 then _ else _) (if N1 + 1 + j ≤ N1 then _ else _) = _
      simp [this, hj]
  calc chainDist d R p p''
    _ ≤ ∑ i ∈ Finset.range (N + 1), d (y i) (y' i) :=
        iInf_le_of_le N (iInf_le_of_le y (iInf_le_of_le y'
          (iInf_le_of_le hy0 (iInf_le_of_le hchain (iInf_le_of_le hy'N le_rfl)))))
    _ = (∑ i ∈ Finset.range (N1 + 1), d (y1 i) (y'1 i)) +
        (∑ j ∈ Finset.range (N2 + 1), d (y2 j) (y'2 j)) := hsum

lemma chainDist_triangle {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop) (hR : Equivalence R) (x y z : X) :
    chainDist d R x z ≤ chainDist d R x y + chainDist d R y z := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hb
  have hb1 : chainDist d R x y < ⊤ := lt_of_le_of_lt le_self_add hb
  have hb2 : chainDist d R y z < ⊤ := lt_of_le_of_lt le_add_self hb
  have he : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := by simpa using hε.ne'
  have hne : (ε : ℝ≥0∞) / 2 ≠ 0 := he.ne'
  have pick : ∀ u v : X, chainDist d R u v < ⊤ →
      ∃ (N : ℕ) (yu y'u : ℕ → X) (h1 : R u (yu 0)) (h2 : ∀ i < N, R (y'u i) (yu (i + 1)))
        (h3 : R (y'u N) v),
        ∑ i ∈ Finset.range (N + 1), d (yu i) (y'u i) < chainDist d R u v + (ε : ℝ≥0∞) / 2 := by
    intro u v hlt
    have := ENNReal.lt_add_right hlt.ne hne
    dsimp [chainDist] at this ⊢
    rw [iInf_lt_iff] at this
    obtain ⟨N, hN⟩ := this
    rw [iInf_lt_iff] at hN
    obtain ⟨yu, hyu⟩ := hN
    rw [iInf_lt_iff] at hyu
    obtain ⟨y'u, hy'u⟩ := hyu
    rw [iInf_lt_iff] at hy'u
    obtain ⟨h1, hh1⟩ := hy'u
    rw [iInf_lt_iff] at hh1
    obtain ⟨h2, hh2⟩ := hh1
    rw [iInf_lt_iff] at hh2
    obtain ⟨h3, hlt3⟩ := hh2
    exact ⟨N, yu, y'u, h1, h2, h3, hlt3⟩
  obtain ⟨N1, y1, y'1, h1_0, h1_chain, h1_N, hlt1⟩ := pick x y hb1
  obtain ⟨N2, y2, y'2, h2_0, h2_chain, h2_N, hlt2⟩ := pick y z hb2
  have hconcat := chain_concat d R hR x y z N1 y1 y'1 h1_0 h1_chain h1_N N2 y2 y'2 h2_0 h2_chain h2_N
  calc chainDist d R x z
    _ ≤ (∑ i ∈ Finset.range (N1 + 1), d (y1 i) (y'1 i)) + (∑ j ∈ Finset.range (N2 + 1), d (y2 j) (y'2 j)) := hconcat
    _ ≤ (chainDist d R x y + (ε : ℝ≥0∞) / 2) + (chainDist d R y z + (ε : ℝ≥0∞) / 2) := add_le_add hlt1.le hlt2.le
    _ = chainDist d R x y + chainDist d R y z + (ε : ℝ≥0∞) := by rw [add_add_add_comm, ENNReal.add_halves]

lemma chainDist_refl {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d) (R : X → X → Prop) (hR : Equivalence R) (x : X) :
    chainDist d R x x = 0 := by
  refine le_antisymm ?_ zero_le
  refine iInf_le_of_le 0 (iInf_le_of_le (fun _ => x) (iInf_le_of_le (fun _ => x)
    (iInf_le_of_le (hR.refl x) (iInf_le_of_le (fun i hi => False.elim (Nat.not_lt_zero i hi))
      (iInf_le_of_le (hR.refl x) ?_)))))
  simp [hd.refl x]

lemma chainDist_symm {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d) (R : X → X → Prop) (hR : Equivalence R) (x y : X) :
    chainDist d R x y = chainDist d R y x := by
  have hle : ∀ u v : X, chainDist d R u v ≤ chainDist d R v u := by
    intro u v
    refine le_iInf fun N => le_iInf fun y_seq => le_iInf fun y'_seq => le_iInf fun hy0 =>
      le_iInf fun hchain => le_iInf fun hy'N => ?_
    let z : ℕ → X := fun i => y'_seq (N - i)
    let z' : ℕ → X := fun i => y_seq (N - i)
    have hz0 : R u (z 0) := by
      change R u (y'_seq (N - 0))
      rw [Nat.sub_zero]
      exact hR.symm hy'N
    have hz'N : R (z' N) v := by
      change R (y_seq (N - N)) v
      rw [Nat.sub_self]
      exact hR.symm hy0
    have hz_chain : ∀ i < N, R (z' i) (z (i + 1)) := by
      intro i hi
      change R (y_seq (N - i)) (y'_seq (N - (i + 1)))
      have hstep := hchain (N - 1 - i) (by omega)
      have h1 : N - 1 - i + 1 = N - i := by omega
      have h2 : N - 1 - i = N - (i + 1) := by omega
      rw [h1] at hstep
      rw [← h2]
      exact hR.symm hstep
    have hsum : ∑ i ∈ Finset.range (N + 1), d (z i) (z' i) = ∑ i ∈ Finset.range (N + 1), d (y_seq i) (y'_seq i) := by
      have h_rev := Finset.sum_range_reflect (fun i => d (y_seq i) (y'_seq i)) (N + 1)
      have h_sub : ∀ j ∈ Finset.range (N + 1), N + 1 - 1 - j = N - j := fun _ _ => by omega
      have h_eq : (∑ j ∈ Finset.range (N + 1), d (y_seq (N + 1 - 1 - j)) (y'_seq (N + 1 - 1 - j))) =
          ∑ j ∈ Finset.range (N + 1), d (y_seq (N - j)) (y'_seq (N - j)) :=
        Finset.sum_congr rfl fun j hj => by rw [h_sub j hj]
      rw [← h_rev, h_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      change d (y'_seq (N - i)) (y_seq (N - i)) = d (y_seq (N - i)) (y'_seq (N - i))
      rw [hd.symm]
    calc chainDist d R u v
      _ ≤ ∑ i ∈ Finset.range (N + 1), d (z i) (z' i) :=
          iInf_le_of_le N (iInf_le_of_le z (iInf_le_of_le z'
            (iInf_le_of_le hz0 (iInf_le_of_le hz_chain (iInf_le_of_le hz'N le_rfl)))))
      _ = ∑ i ∈ Finset.range (N + 1), d (y_seq i) (y'_seq i) := hsum
  exact le_antisymm (hle x y) (hle y x)

lemma chainDist_isEPMetric {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d) (R : X → X → Prop) (hR : Equivalence R) :
    IsEPMetric (chainDist d R) where
  refl := chainDist_refl d hd R hR
  symm := chainDist_symm d hd R hR
  triangle := chainDist_triangle d R hR

lemma chainDist_le {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop) (hR : Equivalence R) (x y : X) :
    chainDist d R x y ≤ d x y := by
  refine iInf_le_of_le 0 (iInf_le_of_le (fun _ => x) (iInf_le_of_le (fun _ => y)
    (iInf_le_of_le (hR.refl x) (iInf_le_of_le (fun i hi => False.elim (Nat.not_lt_zero i hi))
      (iInf_le_of_le (hR.refl y) ?_)))))
  simp

lemma chainDist_isInvariant {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop) (hR : Equivalence R) :
    IsInvariant (chainDist d R) R := by
  have key : ∀ x x' y y', R x x' → R y y' → chainDist d R x y ≤ chainDist d R x' y' := by
    intro x x' y y' hx hy
    refine le_iInf fun N => le_iInf fun y_seq => le_iInf fun y'_seq => le_iInf fun hy0 =>
      le_iInf fun hchain => le_iInf fun hy'N => ?_
    refine iInf_le_of_le N (iInf_le_of_le y_seq (iInf_le_of_le y'_seq ?_))
    refine iInf_le_of_le (hR.trans hx hy0) (iInf_le_of_le hchain (iInf_le_of_le (hR.trans hy'N (hR.symm hy)) le_rfl))
  intro x x' y y' hx hy
  exact le_antisymm (key x x' y y' hx hy) (key x' x y' y (hR.symm hx) (hR.symm hy))

lemma le_chainDist_aux {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop) (hR : Equivalence R)
    (d' : X → X → ℝ≥0∞) (hd' : IsEPMetric d') (hd'le : ∀ a b, d' a b ≤ d a b)
    (hd'inv : IsInvariant d' R) :
    ∀ (N : ℕ) (y y' : ℕ → X), (∀ i < N, R (y' i) (y (i + 1))) →
      d' (y 0) (y' N) ≤ ∑ i ∈ Finset.range (N + 1), d (y i) (y' i) := by
  intro N
  induction' N with n ih
  · intro y y' _
    rw [show 0 + 1 = 1 by rfl, Finset.sum_range_one]
    exact hd'le (y 0) (y' 0)
  · intro y y' hRchain
    rw [Finset.sum_range_succ]
    have hstep : R (y' n) (y (n + 1)) := hRchain n (Nat.lt_succ_self n)
    have hd'_eq : d' (y' n) (y' (n + 1)) = d' (y (n + 1)) (y' (n + 1)) :=
      hd'inv (y' n) (y (n + 1)) (y' (n + 1)) (y' (n + 1)) hstep (hR.refl _)
    calc d' (y 0) (y' (n + 1)) ≤ d' (y 0) (y' n) + d' (y' n) (y' (n + 1)) :=
          hd'.triangle _ _ _
      _ = d' (y 0) (y' n) + d' (y (n + 1)) (y' (n + 1)) := by rw [hd'_eq]
      _ ≤ (∑ i ∈ Finset.range (n + 1), d (y i) (y' i)) + d (y (n + 1)) (y' (n + 1)) :=
          add_le_add (ih y y' (fun i hi => hRchain i (Nat.lt_succ_of_lt hi))) (hd'le _ _)

lemma le_chainDist {X : Type u} (d : X → X → ℝ≥0∞) (R : X → X → Prop) (hR : Equivalence R)
    (d' : X → X → ℝ≥0∞) (hd' : IsEPMetric d') (hd'le : ∀ a b, d' a b ≤ d a b)
    (hd'inv : IsInvariant d' R) (p p' : X) :
    d' p p' ≤ chainDist d R p p' := by
  refine le_iInf fun N => le_iInf fun y => le_iInf fun y' => le_iInf fun hy0 =>
    le_iInf fun hchain => le_iInf fun hy'N => ?_
  have h1 : d' p p' = d' (y 0) (y' N) := hd'inv p (y 0) p' (y' N) hy0 (hR.symm hy'N)
  rw [h1]
  exact le_chainDist_aux d R hR d' hd' hd'le hd'inv N y y' hchain

/-- Lemma 2.2.21. -/
theorem quotientDist_eq_chainDist {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d)
    (hint : IsIntrinsicDist d) (R : X → X → Prop) (hR : Equivalence R) :
    quotientDist d R = chainDist d R := by
  have _ := hint
  refine (quotientDist_unique d hd R hR (chainDist d R)
    (chainDist_isEPMetric d hd R hR)
    (chainDist_le d R hR)
    (chainDist_isInvariant d R hR)
    (fun d' hd' hd'le hd'inv x y => le_chainDist d R hR d' hd' hd'le hd'inv x y)).symm

/-- A type synonym carrying the (pseudo) extended metric `d`. -/
def WithDist {X : Type u} (_d : X → X → ℝ≥0∞) (_hd : IsEPMetric _d) : Type u := X

noncomputable instance {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d) :
    PseudoEMetricSpace (WithDist d hd) where
  edist := d
  edist_self := hd.refl
  edist_comm := hd.symm
  edist_triangle := hd.triangle

theorem edist_withDist {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d) (x y : X) :
    edist (show WithDist d hd from x) (show WithDist d hd from y) = d x y := rfl

theorem pathLength_eq_eVariationOn {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d)
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → X) :
    pathLength d a b f = eVariationOn (fun t => (show WithDist d hd from f t)) (Icc a b) := by
  apply le_antisymm
  · refine iSup_le fun N => iSup_le fun y => iSup_le fun h0 => iSup_le fun hN => iSup_le fun hm => ?_
    refine le_iSup_of_le ⟨N, fun i => y (min i N), ?_, ?_⟩ ?_
    · intro i j hij; exact hm (min_le_min_right N hij)
    · intro i
      refine ⟨?_, ?_⟩
      · rw [← h0]; exact hm (Nat.zero_le _)
      · rw [← hN]; exact hm (min_le_right _ _)
    · refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i < N := Finset.mem_range.1 hi
      have : min (i + 1) N = i + 1 := min_eq_left hi'
      simp only [this, min_eq_left hi'.le]
      exact (hd.symm _ _).le
  · refine iSup_le fun p => ?_
    obtain ⟨n, u, hum, hu⟩ := p
    let y : ℕ → ℝ := fun j => if j = 0 then a else if j ≤ n + 1 then u (j - 1) else b
    have hy0 : y 0 = a := by simp [y]
    have hyN : y (n + 2) = b := by simp [y]
    have hym : Monotone y := by
      have hu0 : a ≤ u 0 := (hu 0).1
      have hun : ∀ i, u i ≤ b := fun i => (hu i).2
      have hua : ∀ i, a ≤ u i := fun i => (hu i).1
      refine monotone_nat_of_le_succ fun j => ?_
      by_cases hj0 : j = 0
      · subst hj0; simp [y, hua]
      · by_cases hj : j + 1 ≤ n + 1
        · have : j ≤ n + 1 := by omega
          simp only [y, hj0, this, hj, if_true, if_false, Nat.succ_ne_zero]
          exact hum (by omega)
        · by_cases hj' : j ≤ n + 1
          · simp only [y, hj0, hj', hj, if_true, if_false, Nat.succ_ne_zero]
            exact hun _
          · simp [y, hj0, hj', hj]
    refine le_iSup_of_le (n + 2) (le_iSup_of_le y (le_iSup_of_le hy0 (le_iSup_of_le hyN
      (le_iSup_of_le hym ?_))))
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    refine le_trans ?_ (le_trans (le_add_right le_rfl) (le_add_right le_rfl))
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i < n := Finset.mem_range.1 hi
    have e1 : y (i + 1) = u i := by simp [y]; omega
    have e2 : y (i + 1 + 1) = u (i + 1) := by
      have : i + 1 + 1 ≤ n + 1 := by omega
      simp [y, this]
    show d (f (u (i + 1))) (f (u i)) ≤ d (f (y (i + 1))) (f (y (i + 1 + 1)))
    rw [e1, e2]
    exact (hd.symm _ _).le

theorem glue_pathLength {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d)
    {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e) (f g : ℝ → X) (hfg : d (f b) (g c) = 0) :
    pathLength d a (b + (e - c)) (fun t => if t ≤ b then f t else g (t - b + c)) ≤
      pathLength d a b f + pathLength d c e g := by
  set h : ℝ → X := fun t => if t ≤ b then f t else g (t - b + c) with hh
  have hbe : b ≤ b + (e - c) := by linarith
  rw [pathLength_eq_eVariationOn d hd (hab.trans hbe), pathLength_eq_eVariationOn d hd hab,
    pathLength_eq_eVariationOn d hd hce]
  have hsplit := eVariationOn.Icc_add_Icc (fun t => (show WithDist d hd from h t))
    (s := (univ : Set ℝ)) hab hbe (mem_univ b)
  simp only [univ_inter] at hsplit
  rw [← hsplit]
  refine add_le_add (le_of_eq ?_) ?_
  · exact eVariationOn.eq_of_eqOn fun t ht => by simp [hh, ht.2]; rfl
  · have h1 : eVariationOn (fun t => (show WithDist d hd from h t)) (Icc b (b + (e - c))) =
        eVariationOn (fun t => (show WithDist d hd from g (t - b + c))) (Icc b (b + (e - c))) := by
      refine eVariationOn.eq_of_edist_zero_on fun t ht => ?_
      by_cases htb : t ≤ b
      · have : t = b := le_antisymm htb ht.1
        subst this
        simp only [hh, le_refl, if_true, sub_self, zero_add]
        exact hfg
      · simp only [hh, htb, if_false]
        exact hd.refl _
    rw [h1]
    have h2 := eVariationOn.comp_eq_of_monotoneOn (fun t => (show WithDist d hd from g t))
      (fun t : ℝ => t - b + c) (t := Icc b (b + (e - c)))
      (fun x _ y _ hxy => by simpa using hxy)
    have h3 : (fun t : ℝ => t - b + c) '' Icc b (b + (e - c)) = Icc c e := by
      ext z; constructor
      · rintro ⟨t, ht, rfl⟩; constructor <;> linarith [ht.1, ht.2]
      · intro hz; exact ⟨z + b - c, ⟨by linarith [hz.1], by linarith [hz.2]⟩, by ring⟩
    rw [h3] at h2
    exact le_of_eq h2

theorem glue_isPathOn {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d)
    {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e) (f g : ℝ → X)
    (hf : IsPathOn d a b f) (hg : IsPathOn d c e g) (hfg : d (f b) (g c) = 0) :
    IsPathOn d a (b + (e - c)) (fun t => if t ≤ b then f t else g (t - b + c)) := by
  set h : ℝ → X := fun t => if t ≤ b then f t else g (t - b + c) with hh
  intro t ht ε hε
  by_cases htb : t < b
  · obtain ⟨δ, hδ, hδ'⟩ := hf t ⟨ht.1, htb.le⟩ ε hε
    refine ⟨min δ (b - t), lt_min hδ (by linarith), fun s hs hst => ?_⟩
    have hsb : s ≤ b := by
      have := (lt_min_iff.1 hst |> fun _ => abs_lt.1 (lt_of_lt_of_le hst (min_le_right _ _)))
      linarith [this.2]
    have h1 : h s = f s := by simp [hh, hsb]
    have h2 : h t = f t := by simp [hh, htb.le]
    rw [h1, h2]
    exact hδ' s ⟨hs.1, hsb⟩ (lt_of_lt_of_le hst (min_le_left _ _))
  · by_cases htb' : t = b
    · subst htb'
      obtain ⟨δ1, hδ1, hδ1'⟩ := hf t ⟨hab, le_rfl⟩ ε hε
      obtain ⟨δ2, hδ2, hδ2'⟩ := hg c ⟨le_rfl, hce⟩ ε hε
      refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun s hs hst => ?_⟩
      have h2 : h t = f t := by simp [hh]
      rw [h2]
      by_cases hsb : s ≤ t
      · have h1 : h s = f s := by simp [hh, hsb]
        rw [h1]
        exact hδ1' s ⟨hs.1, hsb⟩ (lt_of_lt_of_le hst (min_le_left _ _))
      · have h1 : h s = g (s - t + c) := by simp [hh, hsb]
        rw [h1]
        have hs' : s - t + c ∈ Icc c e := ⟨by linarith [not_le.1 hsb], by linarith [hs.2]⟩
        have habs : |s - t + c - c| < δ2 := by
          have : s - t + c - c = s - t := by ring
          rw [this]; exact lt_of_lt_of_le hst (min_le_right _ _)
        calc d (g (s - t + c)) (f t) ≤ d (g (s - t + c)) (g c) + d (g c) (f t) := hd.triangle _ _ _
          _ = d (g (s - t + c)) (g c) := by rw [hd.symm (g c) (f t), hfg, add_zero]
          _ < ε := hδ2' _ hs' habs
    · have htb2 : b < t := lt_of_le_of_ne (not_lt.1 htb) (Ne.symm htb')
      have ht' : t - b + c ∈ Icc c e := ⟨by linarith, by linarith [ht.2]⟩
      obtain ⟨δ, hδ, hδ'⟩ := hg (t - b + c) ht' ε hε
      refine ⟨min δ (t - b), lt_min hδ (by linarith), fun s hs hst => ?_⟩
      have hsb : b < s := by
        have := abs_lt.1 (lt_of_lt_of_le hst (min_le_right _ _))
        linarith [this.1]
      have h1 : h s = g (s - b + c) := by simp [hh, not_le.2 hsb]
      have h2 : h t = g (t - b + c) := by simp [hh, not_le.2 htb2]
      rw [h1, h2]
      have hs' : s - b + c ∈ Icc c e := ⟨by linarith, by linarith [hs.2]⟩
      refine hδ' _ hs' ?_
      have : s - b + c - (t - b + c) = s - t := by ring
      rw [this]; exact lt_of_lt_of_le hst (min_le_left _ _)

/-- `p` and `q` are joined by a path of length at most `c`, up to distance `0` at the ends. -/
def Reach {X : Type u} (d : X → X → ℝ≥0∞) (c : ℝ≥0∞) (p q : X) : Prop :=
  ∃ (a b : ℝ) (f : ℝ → X), a < b ∧ IsPathOn d a b f ∧ d (f a) p = 0 ∧ d (f b) q = 0 ∧
    pathLength d a b f ≤ c

theorem Reach.mono {X : Type u} {d : X → X → ℝ≥0∞} {c c' : ℝ≥0∞} {p q : X} (h : Reach d c p q)
    (hc : c ≤ c') : Reach d c' p q := by
  obtain ⟨a, b, f, hab, hf, h1, h2, h3⟩ := h
  exact ⟨a, b, f, hab, hf, h1, h2, h3.trans hc⟩

theorem Reach.zero {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d) {p q : X}
    (hpq : d p q = 0) : Reach d 0 p q := by
  refine ⟨0, 1, fun _ => p, zero_lt_one, ?_, hd.refl p, hpq, ?_⟩
  · intro t _ ε hε
    exact ⟨1, one_pos, fun s _ _ => by rw [hd.refl]; exact hε⟩
  · refine le_of_eq (le_antisymm (iSup_le fun N => iSup_le fun y => iSup_le fun _ =>
      iSup_le fun _ => iSup_le fun _ => ?_) zero_le)
    simp [hd.refl]

theorem Reach.trans {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d) {c c' : ℝ≥0∞}
    {p q r : X} (h1 : Reach d c p q) (h2 : Reach d c' q r) : Reach d (c + c') p r := by
  obtain ⟨a, b, f, hab, hf, hfa, hfb, hfl⟩ := h1
  obtain ⟨c0, e, g, hce, hg, hgc, hge, hgl⟩ := h2
  have hfg : d (f b) (g c0) = 0 := by
    refine le_antisymm ?_ zero_le
    calc d (f b) (g c0) ≤ d (f b) q + d q (g c0) := hd.triangle _ _ _
      _ = 0 := by rw [hfb, hd.symm q (g c0), hgc, add_zero]
  refine ⟨a, b + (e - c0), fun t => if t ≤ b then f t else g (t - b + c0), by linarith,
    glue_isPathOn d hd hab.le hce.le f g hf hg hfg, ?_, ?_, ?_⟩
  · simp [hab.le, hfa]
  · by_cases hee : b + (e - c0) ≤ b
    · have : e = c0 := by linarith
      subst this
      simp only [hee, if_true]
      refine le_antisymm ?_ zero_le
      calc d (f (b + (e - e))) r ≤ d (f (b + (e - e))) (g e) + d (g e) r := hd.triangle _ _ _
        _ = 0 := by
            have : b + (e - e) = b := by ring
            rw [this, hfg, hge, add_zero]
    · simp only [hee, if_false]
      have : b + (e - c0) - b + c0 = e := by ring
      rw [this]; exact hge
  · exact (glue_pathLength d hd hab.le hce.le f g hfg).trans (add_le_add hfl hgl)

theorem Reach.ofPath {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d) {a b : ℝ} {f : ℝ → X}
    (hab : a ≤ b) (hf : IsPathOn d a b f) : Reach d (pathLength d a b f) (f a) (f b) := by
  have hfg : d (f b) ((fun _ : ℝ => f b) 0) = 0 := hd.refl _
  have hg : IsPathOn d 0 1 (fun _ : ℝ => f b) := fun t _ ε hε =>
    ⟨1, one_pos, fun s _ _ => by rw [hd.refl]; exact hε⟩
  have hgl : pathLength d 0 1 (fun _ : ℝ => f b) = 0 := by
    refine le_antisymm (iSup_le fun N => iSup_le fun y => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun _ => ?_) zero_le
    simp [hd.refl]
  refine ⟨a, b + (1 - 0), fun t => if t ≤ b then f t else (fun _ : ℝ => f b) (t - b + 0),
    by linarith, glue_isPathOn d hd hab zero_le_one f _ hf hg hfg, ?_, ?_, ?_⟩
  · simp [hab]; exact hd.refl _
  · have : ¬ (b + (1 - 0) ≤ b) := by linarith
    simp only [this, if_false]; exact hd.refl _
  · refine (glue_pathLength d hd hab zero_le_one f (fun _ : ℝ => f b) hfg).trans ?_
    rw [hgl, add_zero]

/-- Fix the endpoints of a path exactly. -/
theorem Reach.exact {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d) {c : ℝ≥0∞} {p q : X}
    (h : Reach d c p q) :
    ∃ (a b : ℝ) (f : ℝ → X), a ≤ b ∧ IsPathOn d a b f ∧ f a = p ∧ f b = q ∧
      pathLength d a b f ≤ c := by
  obtain ⟨a, b, f, hab, hf, hfa, hfb, hl⟩ := h
  let g : ℝ → X := fun t => if t = a then p else if t = b then q else f t
  have hga : g a = p := by simp [g]
  have hgb : g b = q := by simp [g, hab.ne']
  have hgf : ∀ t ∈ Icc a b, d (g t) (f t) = 0 := by
    intro t ht
    by_cases ht0 : t = a
    · subst ht0; simp only [g, if_true]; rw [hd.symm]; exact hfa
    · by_cases ht1 : t = b
      · subst ht1; simp only [g, ht0, if_false, if_true]; rw [hd.symm]; exact hfb
      · simp only [g, ht0, ht1, if_false]; exact hd.refl _
  have hgg : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, d (g s) (g t) = d (f s) (f t) := by
    intro s hs t ht
    apply le_antisymm
    · calc d (g s) (g t) ≤ d (g s) (f s) + d (f s) (g t) := hd.triangle _ _ _
        _ ≤ d (g s) (f s) + (d (f s) (f t) + d (f t) (g t)) :=
            add_le_add le_rfl (hd.triangle _ _ _)
        _ = d (f s) (f t) := by rw [hgf s hs, hd.symm (f t) (g t), hgf t ht]; simp
    · calc d (f s) (f t) ≤ d (f s) (g s) + d (g s) (f t) := hd.triangle _ _ _
        _ ≤ d (f s) (g s) + (d (g s) (g t) + d (g t) (f t)) :=
            add_le_add le_rfl (hd.triangle _ _ _)
        _ = d (g s) (g t) := by rw [hd.symm (f s) (g s), hgf s hs, hgf t ht]; simp
  refine ⟨a, b, g, hab.le, ?_, hga, hgb, ?_⟩
  · intro t ht ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hf t ht ε hε
    exact ⟨δ, hδ, fun s hs hst => by rw [hgg s hs t ht]; exact hδ' s hs hst⟩
  · refine le_trans (le_of_eq ?_) hl
    rw [pathLength_eq_eVariationOn d hd hab.le, pathLength_eq_eVariationOn d hd hab.le]
    exact eVariationOn.eq_of_edist_zero_on fun t ht => hgf t ht

theorem isPathOn_mono {X : Type u} {d d' : X → X → ℝ≥0∞} (hdd : ∀ x y, d x y ≤ d' x y)
    {a b : ℝ} {f : ℝ → X} (h : IsPathOn d' a b f) : IsPathOn d a b f := fun t ht ε hε => by
  obtain ⟨δ, hδ, hδ'⟩ := h t ht ε hε
  exact ⟨δ, hδ, fun s hs hst => (hdd _ _).trans_lt (hδ' s hs hst)⟩

theorem pathLength_mono' {X : Type u} {d d' : X → X → ℝ≥0∞} (hdd : ∀ x y, d x y ≤ d' x y)
    {a b : ℝ} {f : ℝ → X} : pathLength d a b f ≤ pathLength d' a b f :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
    Finset.sum_le_sum fun _ _ => hdd _ _

theorem reach_chain {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d) (p p' : X) (N : ℕ)
    (y y' : ℕ → X) (c : ℕ → ℝ≥0∞) (h0 : d p (y 0) = 0) (hi : ∀ i < N, d (y' i) (y (i + 1)) = 0)
    (hN : d (y' N) p' = 0) (hp : ∀ i ≤ N, Reach d (c i) (y i) (y' i)) :
    Reach d (∑ i ∈ Finset.range (N + 1), c i) p p' := by
  have key : ∀ k ≤ N, Reach d (∑ i ∈ Finset.range (k + 1), c i) p (y' k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have := (Reach.zero d hd h0).trans d hd (hp 0 (Nat.zero_le _))
      simpa using this
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := h1.trans d hd (Reach.zero d hd (hi k (by omega)))
      have h3 := h2.trans d hd (hp (k + 1) hk)
      rw [Finset.sum_range_succ _ (k + 1)]
      simpa [add_assoc] using h3
  have := (key N le_rfl).trans d hd (Reach.zero d hd hN)
  simpa using this

/-- Proposition 2.2.22: any quotient of an intrinsic ep metric is intrinsic. -/
theorem quotientDist_isIntrinsic {X : Type u} (d : X → X → ℝ≥0∞) (hd : IsEPMetric d)
    (hint : IsIntrinsicDist d) (R : X → X → Prop) (hR : Equivalence R) :
    IsIntrinsicDist (quotientDist d R) := by
  have hQ : IsEPMetric (quotientDist d R) := quotientDist_isEPMetric d R
  have hle : ∀ x y, quotientDist d R x y ≤ d x y := quotientDist_le d R
  have hinv := quotientDist_isInvariant d R hR
  have hR0 : ∀ x y, R x y → quotientDist d R x y = 0 := by
    intro x y hxy
    rw [hinv x y y y hxy (hR.refl y)]
    exact hQ.refl y
  intro p p'
  apply le_antisymm
  · refine le_iInf fun a => le_iInf fun b => le_iInf fun f => le_iInf fun hab => le_iInf fun _ =>
      le_iInf fun hfa => le_iInf fun hfb => ?_
    rw [← hfa, ← hfb]
    exact dist_le_pathLength (quotientDist d R) hab
  · by_cases htop : quotientDist d R p p' = ∞
    · rw [htop]; exact le_top
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε0 : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
    have hε2 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := ENNReal.half_pos hε0
    have hc := congrFun (congrFun (quotientDist_eq_chainDist d hd hint R hR) p) p'
    have hlt : chainDist d R p p' < chainDist d R p p' + (ε : ℝ≥0∞) / 2 := by
      rw [← hc]; exact ENNReal.lt_add_right htop hε2.ne'
    have hcd : chainDist d R p p' < ∞ := by rw [← hc]; exact lt_top_iff_ne_top.2 htop
    have hlt' := hlt
    unfold chainDist at hlt'
    simp only [iInf_lt_iff] at hlt'
    obtain ⟨N, y, y', h0, hi, hN, hsum0⟩ := hlt'
    have hsum : ∑ i ∈ Finset.range (N + 1), d (y i) (y' i) <
        chainDist d R p p' + (ε : ℝ≥0∞) / 2 := hsum0
    have hfin : ∑ i ∈ Finset.range (N + 1), d (y i) (y' i) ≠ ∞ := by
      refine ne_top_of_lt (hsum.trans (ENNReal.add_lt_top.2 ⟨?_, ?_⟩))
      · exact hcd
      · exact ENNReal.div_lt_top (by simp) (by norm_num)
    have hterm : ∀ i ≤ N, d (y i) (y' i) ≠ ∞ := fun i hiN =>
      ne_top_of_le_ne_top hfin (Finset.single_le_sum (f := fun i => d (y i) (y' i))
        (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hiN)))
    set δ : ℝ≥0∞ := ((ε : ℝ≥0∞) / 2) / ((N : ℝ≥0∞) + 1) with hδ
    have hN1 : ((N : ℝ≥0∞) + 1) ≠ 0 := by positivity
    have hN1' : ((N : ℝ≥0∞) + 1) ≠ ∞ := by simp
    have hδ0 : δ ≠ 0 := by
      refine (ENNReal.div_pos hε2.ne' hN1').ne'
    have hpiece : ∀ i ≤ N, Reach (quotientDist d R) (d (y i) (y' i) + δ) (y i) (y' i) := by
      intro i hiN
      have h1 : ⨅ (a : ℝ) (b : ℝ) (f : ℝ → X) (_ : a ≤ b) (_ : IsPathOn d a b f) (_ : f a = y i)
          (_ : f b = y' i), pathLength d a b f < d (y i) (y' i) + δ := by
        rw [← hint (y i) (y' i)]; exact ENNReal.lt_add_right (hterm i hiN) hδ0
      simp only [iInf_lt_iff] at h1
      obtain ⟨a, b, f, hab, hf, hfa, hfb, hl⟩ := h1
      have := Reach.ofPath (quotientDist d R) hQ hab (isPathOn_mono hle hf)
      rw [hfa, hfb] at this
      exact this.mono ((pathLength_mono' hle).trans hl.le)
    have hreach := reach_chain (quotientDist d R) hQ p p' N y y' (fun i => d (y i) (y' i) + δ)
      (hR0 _ _ h0) (fun i hi' => hR0 _ _ (hi i hi')) (hR0 _ _ hN) hpiece
    obtain ⟨a, b, f, hab, hf, hfa, hfb, hl⟩ := hreach.exact (quotientDist d R) hQ
    have hsumδ : ∑ i ∈ Finset.range (N + 1), (d (y i) (y' i) + δ) =
        ∑ i ∈ Finset.range (N + 1), d (y i) (y' i) + (ε : ℝ≥0∞) / 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hδ]
      congr 1
      push_cast
      exact ENNReal.mul_div_cancel hN1 hN1'
    refine le_trans (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le f (iInf_le_of_le hab
      (iInf_le_of_le hf (iInf_le_of_le hfa (iInf_le_of_le hfb le_rfl))))))) ?_
    refine hl.trans ?_
    rw [hsumδ]
    calc ∑ i ∈ Finset.range (N + 1), d (y i) (y' i) + (ε : ℝ≥0∞) / 2
        ≤ (quotientDist d R p p' + (ε : ℝ≥0∞) / 2) + (ε : ℝ≥0∞) / 2 :=
          add_le_add (by rw [← hc] at hsum; exact hsum.le) le_rfl
      _ = quotientDist d R p p' + ε := by rw [add_assoc, ENNReal.add_halves]


end Quotients

/-! ### 2.2.4 The Gromov–Hausdorff distance -/

section GromovHausdorff

/-- The open `ε`-neighbourhood `Aᵋ = {p | ∃ a ∈ A, d a p < ε}`. -/
def neighbourhood {P : Type u} [PseudoEMetricSpace P] (A : Set P) (ε : ℝ≥0∞) : Set P :=
  {p | ∃ a ∈ A, edist a p < ε}

/-- Definition 2.2.23: the Hausdorff distance between subsets. -/
noncomputable def hausdorffDist {P : Type u} [PseudoEMetricSpace P] (A B : Set P) : ℝ≥0∞ :=
  sInf {ε | B ⊆ neighbourhood A ε ∧ A ⊆ neighbourhood B ε}

/-- Definition 2.2.24: the Gromov–Hausdorff distance, the infimum over distance preserving
inclusions into a common space. -/
noncomputable def gromovHausdorff (P : Type u) (Q : Type u) [PseudoEMetricSpace P]
    [PseudoEMetricSpace Q] : ℝ≥0∞ :=
  sInf {r | ∃ (Z : Type u) (_ : PseudoEMetricSpace Z) (i : P → Z) (j : Q → Z),
    IsDistPreserving i ∧ IsDistPreserving j ∧ r = hausdorffDist (range i) (range j)}

/-- Glued distance on the disjoint sum `Sum X Y` with cross-distance `c`. -/
def sumDist {X Y : Type u} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (c : X → Y → ℝ≥0∞) : Sum X Y → Sum X Y → ℝ≥0∞
  | Sum.inl x₁, Sum.inl x₂ => edist x₁ x₂
  | Sum.inr y₁, Sum.inr y₂ => edist y₁ y₂
  | Sum.inl x, Sum.inr y => c x y
  | Sum.inr y, Sum.inl x => c x y

theorem sumDist_isEPMetric {X Y : Type u} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (c : X → Y → ℝ≥0∞)
    (H1 : ∀ x₁ x₂ y, c x₁ y ≤ edist x₁ x₂ + c x₂ y)
    (H2 : ∀ x y₁ y₂, c x y₂ ≤ c x y₁ + edist y₁ y₂)
    (H3 : ∀ x₁ x₂ y, edist x₁ x₂ ≤ c x₁ y + c x₂ y)
    (H4 : ∀ x y₁ y₂, edist y₁ y₂ ≤ c x y₁ + c x y₂) :
    IsEPMetric (sumDist c) where
  refl := by
    rintro (x | y)
    · exact edist_self x
    · exact edist_self y
  symm := by
    rintro (x₁ | y₁) (x₂ | y₂)
    · exact edist_comm x₁ x₂
    · rfl
    · rfl
    · exact edist_comm y₁ y₂
  triangle := by
    rintro (x₁ | y₁) (x₂ | y₂) (x₃ | y₃)
    · exact edist_triangle x₁ x₂ x₃
    · exact H1 x₁ x₂ y₃
    · exact H3 x₁ x₃ y₂
    · exact H2 x₁ y₂ y₃
    · calc c x₃ y₁ ≤ edist x₃ x₂ + c x₂ y₁ := H1 x₃ x₂ y₁
        _ = c x₂ y₁ + edist x₂ x₃ := by rw [edist_comm x₃ x₂, add_comm]
    · exact H4 x₂ y₁ y₃
    · calc c x₃ y₁ ≤ c x₃ y₂ + edist y₂ y₁ := H2 x₃ y₂ y₁
        _ = edist y₁ y₂ + c x₃ y₂ := by rw [edist_comm y₂ y₁, add_comm]
    · exact edist_triangle y₁ y₂ y₃

noncomputable def glueDist {Q Z₁ Z₂ : Type u} [PseudoEMetricSpace Z₁] [PseudoEMetricSpace Z₂]
    (j₁ : Q → Z₁) (i₂ : Q → Z₂) (a : Z₁) (b : Z₂) : ℝ≥0∞ :=
  ⨅ q : Q, edist a (j₁ q) + edist (i₂ q) b

theorem glueDist_H1 {Q Z₁ Z₂ : Type u} [PseudoEMetricSpace Q] [PseudoEMetricSpace Z₁] [PseudoEMetricSpace Z₂]
    [Nonempty Q] (j₁ : Q → Z₁) (i₂ : Q → Z₂) (a₁ a₂ : Z₁) (b : Z₂) :
    glueDist j₁ i₂ a₁ b ≤ edist a₁ a₂ + glueDist j₁ i₂ a₂ b := by
  unfold glueDist
  rw [ENNReal.add_iInf]
  refine le_iInf fun q => ?_
  refine (iInf_le _ q).trans ?_
  calc edist a₁ (j₁ q) + edist (i₂ q) b
    _ ≤ (edist a₁ a₂ + edist a₂ (j₁ q)) + edist (i₂ q) b :=
        add_le_add (edist_triangle a₁ a₂ (j₁ q)) le_rfl
    _ = edist a₁ a₂ + (edist a₂ (j₁ q) + edist (i₂ q) b) := add_assoc _ _ _

theorem glueDist_H2 {Q Z₁ Z₂ : Type u} [PseudoEMetricSpace Q] [PseudoEMetricSpace Z₁] [PseudoEMetricSpace Z₂]
    [Nonempty Q] (j₁ : Q → Z₁) (i₂ : Q → Z₂) (a : Z₁) (b₁ b₂ : Z₂) :
    glueDist j₁ i₂ a b₂ ≤ glueDist j₁ i₂ a b₁ + edist b₁ b₂ := by
  unfold glueDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun q => ?_
  refine (iInf_le _ q).trans ?_
  calc edist a (j₁ q) + edist (i₂ q) b₂
    _ ≤ edist a (j₁ q) + (edist (i₂ q) b₁ + edist b₁ b₂) :=
        add_le_add le_rfl (edist_triangle (i₂ q) b₁ b₂)
    _ = (edist a (j₁ q) + edist (i₂ q) b₁) + edist b₁ b₂ := (add_assoc _ _ _).symm

theorem glueDist_H3 {Q Z₁ Z₂ : Type u} [PseudoEMetricSpace Q] [PseudoEMetricSpace Z₁] [PseudoEMetricSpace Z₂]
    [Nonempty Q] (j₁ : Q → Z₁) (i₂ : Q → Z₂) (hj₁ : IsDistPreserving j₁) (hi₂ : IsDistPreserving i₂)
    (a₁ a₂ : Z₁) (b : Z₂) :
    edist a₁ a₂ ≤ glueDist j₁ i₂ a₁ b + glueDist j₁ i₂ a₂ b := by
  unfold glueDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun q₁ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun q₂ => ?_
  have hq : edist (j₁ q₁) (j₁ q₂) ≤ edist (i₂ q₁) b + edist (i₂ q₂) b := by
    rw [← hj₁ q₁ q₂, hi₂ q₁ q₂]
    calc edist (i₂ q₁) (i₂ q₂) ≤ edist (i₂ q₁) b + edist b (i₂ q₂) := edist_triangle _ _ _
      _ = edist (i₂ q₁) b + edist (i₂ q₂) b := by rw [edist_comm b]
  calc edist a₁ a₂ ≤ edist a₁ (j₁ q₁) + edist (j₁ q₁) a₂ := edist_triangle _ _ _
    _ ≤ edist a₁ (j₁ q₁) + (edist (j₁ q₁) (j₁ q₂) + edist (j₁ q₂) a₂) :=
        add_le_add le_rfl (edist_triangle _ _ _)
    _ = edist a₁ (j₁ q₁) + edist (j₁ q₁) (j₁ q₂) + edist a₂ (j₁ q₂) := by
        rw [edist_comm (j₁ q₂) a₂]; ring
    _ ≤ edist a₁ (j₁ q₁) + (edist (i₂ q₁) b + edist (i₂ q₂) b) + edist a₂ (j₁ q₂) :=
        add_le_add (add_le_add le_rfl hq) le_rfl
    _ = (edist a₁ (j₁ q₁) + edist (i₂ q₁) b) + (edist a₂ (j₁ q₂) + edist (i₂ q₂) b) := by ring

theorem glueDist_H4 {Q Z₁ Z₂ : Type u} [PseudoEMetricSpace Q] [PseudoEMetricSpace Z₁] [PseudoEMetricSpace Z₂]
    [Nonempty Q] (j₁ : Q → Z₁) (i₂ : Q → Z₂) (hj₁ : IsDistPreserving j₁) (hi₂ : IsDistPreserving i₂)
    (a : Z₁) (b₁ b₂ : Z₂) :
    edist b₁ b₂ ≤ glueDist j₁ i₂ a b₁ + glueDist j₁ i₂ a b₂ := by
  unfold glueDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun q₁ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun q₂ => ?_
  have hq : edist (i₂ q₁) (i₂ q₂) ≤ edist a (j₁ q₁) + edist a (j₁ q₂) := by
    rw [← hi₂ q₁ q₂, hj₁ q₁ q₂]
    calc edist (j₁ q₁) (j₁ q₂) ≤ edist (j₁ q₁) a + edist a (j₁ q₂) := edist_triangle _ _ _
      _ = edist a (j₁ q₁) + edist a (j₁ q₂) := by rw [edist_comm (j₁ q₁) a]
  calc edist b₁ b₂ ≤ edist b₁ (i₂ q₁) + edist (i₂ q₁) b₂ := edist_triangle _ _ _
    _ ≤ edist b₁ (i₂ q₁) + (edist (i₂ q₁) (i₂ q₂) + edist (i₂ q₂) b₂) :=
        add_le_add le_rfl (edist_triangle _ _ _)
    _ = edist (i₂ q₁) (i₂ q₂) + (edist (i₂ q₁) b₁ + edist (i₂ q₂) b₂) := by
        rw [edist_comm b₁ (i₂ q₁)]; ring
    _ ≤ (edist a (j₁ q₁) + edist a (j₁ q₂)) + (edist (i₂ q₁) b₁ + edist (i₂ q₂) b₂) :=
        add_le_add hq le_rfl
    _ = (edist a (j₁ q₁) + edist (i₂ q₁) b₁) + (edist a (j₁ q₂) + edist (i₂ q₂) b₂) := by ring

theorem gromovHausdorff_le_add_of_eps
    {P Q S : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q] [PseudoEMetricSpace S]
    [Nonempty Q]
    {Z₁ : Type u} [PseudoEMetricSpace Z₁] (i₁ : P → Z₁) (j₁ : Q → Z₁)
    (hi₁ : IsDistPreserving i₁) (hj₁ : IsDistPreserving j₁)
    {Z₂ : Type u} [PseudoEMetricSpace Z₂] (i₂ : Q → Z₂) (j₂ : S → Z₂)
    (hi₂ : IsDistPreserving i₂) (hj₂ : IsDistPreserving j₂)
    {ε₁ ε₂ : ℝ≥0∞}
    (h1 : range j₁ ⊆ neighbourhood (range i₁) ε₁ ∧ range i₁ ⊆ neighbourhood (range j₁) ε₁)
    (h2 : range j₂ ⊆ neighbourhood (range i₂) ε₂ ∧ range i₂ ⊆ neighbourhood (range j₂) ε₂) :
    gromovHausdorff P S ≤ ε₁ + ε₂ := by
  have H1 := glueDist_H1 j₁ i₂
  have H2 := glueDist_H2 j₁ i₂
  have H3 := glueDist_H3 j₁ i₂ hj₁ hi₂
  have H4 := glueDist_H4 j₁ i₂ hj₁ hi₂
  have hmet : IsEPMetric (sumDist (glueDist j₁ i₂)) :=
    sumDist_isEPMetric (glueDist j₁ i₂) H1 H2 H3 H4
  let Z := WithDist (sumDist (glueDist j₁ i₂)) hmet
  let I₁ : P → Z := fun p => Sum.inl (i₁ p)
  let J₂ : S → Z := fun s => Sum.inr (j₂ s)
  have hI₁ : IsDistPreserving I₁ := fun p p' => by
    change edist p p' = sumDist (glueDist j₁ i₂) (Sum.inl (i₁ p)) (Sum.inl (i₁ p'))
    simp only [sumDist]
    exact hi₁ p p'
  have hJ₂ : IsDistPreserving J₂ := fun s s' => by
    change edist s s' = sumDist (glueDist j₁ i₂) (Sum.inr (j₂ s)) (Sum.inr (j₂ s'))
    simp only [sumDist]
    exact hj₂ s s'
  have h_range_J₂ : range J₂ ⊆ neighbourhood (range I₁) (ε₁ + ε₂) := by
    rintro z ⟨s, rfl⟩
    obtain ⟨_, ⟨q, rfl⟩, hq_dist⟩ : ∃ x ∈ range i₂, edist x (j₂ s) < ε₂ := h2.1 ⟨s, rfl⟩
    obtain ⟨_, ⟨p, rfl⟩, hp_dist⟩ : ∃ x ∈ range i₁, edist x (j₁ q) < ε₁ := h1.1 ⟨q, rfl⟩
    refine ⟨I₁ p, ⟨p, rfl⟩, ?_⟩
    change sumDist (glueDist j₁ i₂) (Sum.inl (i₁ p)) (Sum.inr (j₂ s)) < ε₁ + ε₂
    simp only [sumDist]
    refine ((iInf_le (fun q' => edist (i₁ p) (j₁ q') + edist (i₂ q') (j₂ s)) q).trans_lt ?_)
    exact ENNReal.add_lt_add hp_dist hq_dist
  have h_range_I₁ : range I₁ ⊆ neighbourhood (range J₂) (ε₁ + ε₂) := by
    rintro z ⟨p, rfl⟩
    obtain ⟨_, ⟨q, rfl⟩, hq_dist⟩ : ∃ x ∈ range j₁, edist x (i₁ p) < ε₁ := h1.2 ⟨p, rfl⟩
    obtain ⟨_, ⟨s, rfl⟩, hs_dist⟩ : ∃ x ∈ range j₂, edist x (i₂ q) < ε₂ := h2.2 ⟨q, rfl⟩
    refine ⟨J₂ s, ⟨s, rfl⟩, ?_⟩
    change sumDist (glueDist j₁ i₂) (Sum.inr (j₂ s)) (Sum.inl (i₁ p)) < ε₁ + ε₂
    simp only [sumDist]
    rw [edist_comm] at hq_dist hs_dist
    refine ((iInf_le (fun q' => edist (i₁ p) (j₁ q') + edist (i₂ q') (j₂ s)) q).trans_lt ?_)
    exact ENNReal.add_lt_add hq_dist hs_dist
  have h_hd : hausdorffDist (range I₁) (range J₂) ≤ ε₁ + ε₂ :=
    sInf_le ⟨h_range_J₂, h_range_I₁⟩
  refine le_trans ?_ h_hd
  exact sInf_le ⟨Z, inferInstance, I₁, J₂, hI₁, hJ₂, rfl⟩

theorem gromovHausdorff_eq_top_of_empty_right {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    (hP : Nonempty P) (hQ : IsEmpty Q) : gromovHausdorff P Q = ∞ := by
  unfold gromovHausdorff
  have hset : {r : ℝ≥0∞ | ∃ (Z : Type u) (_ : PseudoEMetricSpace Z) (i : P → Z) (j : Q → Z),
      IsDistPreserving i ∧ IsDistPreserving j ∧ r = hausdorffDist (range i) (range j)} ⊆ {∞} := by
    rintro r ⟨Z, _, i, j, _, _, rfl⟩
    simp only [Set.mem_singleton_iff]
    unfold hausdorffDist
    have h_emp : {ε | range j ⊆ neighbourhood (range i) ε ∧ range i ⊆ neighbourhood (range j) ε} = ∅ := by
      ext ε
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, h2⟩
      obtain ⟨p⟩ := hP
      have hp : i p ∈ range i := ⟨p, rfl⟩
      have := h2 hp
      obtain ⟨_, ⟨q, rfl⟩, -⟩ := this
      exact (IsEmpty.false q).elim
    rw [h_emp, sInf_empty]
  refine le_antisymm ?_ (le_sInf fun r hr => by have := hset hr; aesop)
  by_cases h_non : {r : ℝ≥0∞ | ∃ (Z : Type u) (_ : PseudoEMetricSpace Z) (i : P → Z) (j : Q → Z),
      IsDistPreserving i ∧ IsDistPreserving j ∧ r = hausdorffDist (range i) (range j)}.Nonempty
  · obtain ⟨r, hr⟩ := h_non
    have : r = ∞ := hset hr
    subst this
    exact sInf_le hr
  · have : {r : ℝ≥0∞ | ∃ (Z : Type u) (_ : PseudoEMetricSpace Z) (i : P → Z) (j : Q → Z),
      IsDistPreserving i ∧ IsDistPreserving j ∧ r = hausdorffDist (range i) (range j)} = ∅ :=
      Set.not_nonempty_iff_eq_empty.1 h_non
    rw [this, sInf_empty]

theorem gromovHausdorff_eq_top_of_empty_left {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    (hP : IsEmpty P) (hQ : Nonempty Q) : gromovHausdorff P Q = ∞ := by
  unfold gromovHausdorff
  have hset : {r : ℝ≥0∞ | ∃ (Z : Type u) (_ : PseudoEMetricSpace Z) (i : P → Z) (j : Q → Z),
      IsDistPreserving i ∧ IsDistPreserving j ∧ r = hausdorffDist (range i) (range j)} ⊆ {∞} := by
    rintro r ⟨Z, _, i, j, _, _, rfl⟩
    simp only [Set.mem_singleton_iff]
    unfold hausdorffDist
    have h_emp : {ε | range j ⊆ neighbourhood (range i) ε ∧ range i ⊆ neighbourhood (range j) ε} = ∅ := by
      ext ε
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, -⟩
      obtain ⟨q⟩ := hQ
      have hq : j q ∈ range j := ⟨q, rfl⟩
      have := h1 hq
      obtain ⟨_, ⟨p, rfl⟩, -⟩ := this
      exact (IsEmpty.false p).elim
    rw [h_emp, sInf_empty]
  refine le_antisymm ?_ (le_sInf fun r hr => by have := hset hr; aesop)
  by_cases h_non : {r : ℝ≥0∞ | ∃ (Z : Type u) (_ : PseudoEMetricSpace Z) (i : P → Z) (j : Q → Z),
      IsDistPreserving i ∧ IsDistPreserving j ∧ r = hausdorffDist (range i) (range j)}.Nonempty
  · obtain ⟨r, hr⟩ := h_non
    have : r = ∞ := hset hr
    subst this
    exact sInf_le hr
  · have : {r : ℝ≥0∞ | ∃ (Z : Type u) (_ : PseudoEMetricSpace Z) (i : P → Z) (j : Q → Z),
      IsDistPreserving i ∧ IsDistPreserving j ∧ r = hausdorffDist (range i) (range j)} = ∅ :=
      Set.not_nonempty_iff_eq_empty.1 h_non
    rw [this, sInf_empty]

/-- The Gromov–Hausdorff distance is an ep metric on ep metric spaces. -/
theorem gromovHausdorff_triangle (P Q S : Type u) [PseudoEMetricSpace P]
    [PseudoEMetricSpace Q] [PseudoEMetricSpace S] :
    gromovHausdorff P S ≤ gromovHausdorff P Q + gromovHausdorff Q S := by
  by_cases hPQ_top : gromovHausdorff P Q = ∞
  · rw [hPQ_top, top_add]; exact le_top
  by_cases hQS_top : gromovHausdorff Q S = ∞
  · rw [hQS_top, add_top]; exact le_top
  by_cases hQ : Nonempty Q
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε0 : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
    set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 4 with hδ
    have hδ0 : δ ≠ 0 := by
      rw [hδ]
      exact (ENNReal.div_pos hε0 (by norm_num)).ne'
    have hltPQ : gromovHausdorff P Q < gromovHausdorff P Q + δ :=
      ENNReal.lt_add_right hPQ_top hδ0
    have hltQS : gromovHausdorff Q S < gromovHausdorff Q S + δ :=
      ENNReal.lt_add_right hQS_top hδ0
    unfold gromovHausdorff at hltPQ hltQS
    simp only [sInf_lt_iff] at hltPQ hltQS
    obtain ⟨r₁, ⟨Z₁, _, i₁, j₁, hi₁, hj₁, rfl⟩, hr₁⟩ := hltPQ
    obtain ⟨r₂, ⟨Z₂, _, i₂, j₂, hi₂, hj₂, rfl⟩, hr₂⟩ := hltQS
    have hr₁_fin : hausdorffDist (range i₁) (range j₁) ≠ ∞ := ne_top_of_lt hr₁
    have hr₂_fin : hausdorffDist (range i₂) (range j₂) ≠ ∞ := ne_top_of_lt hr₂
    have hlt_hd1 : hausdorffDist (range i₁) (range j₁) < hausdorffDist (range i₁) (range j₁) + δ :=
      ENNReal.lt_add_right hr₁_fin hδ0
    have hlt_hd2 : hausdorffDist (range i₂) (range j₂) < hausdorffDist (range i₂) (range j₂) + δ :=
      ENNReal.lt_add_right hr₂_fin hδ0
    unfold hausdorffDist at hlt_hd1 hlt_hd2
    simp only [sInf_lt_iff] at hlt_hd1 hlt_hd2
    obtain ⟨ε₁, hε₁_mem, hε₁⟩ := hlt_hd1
    obtain ⟨ε₂, hε₂_mem, hε₂⟩ := hlt_hd2
    have h_le := gromovHausdorff_le_add_of_eps i₁ j₁ hi₁ hj₁ i₂ j₂ hi₂ hj₂ hε₁_mem hε₂_mem
    refine h_le.trans ?_
    calc ε₁ + ε₂ ≤ (hausdorffDist (range i₁) (range j₁) + δ) + (hausdorffDist (range i₂) (range j₂) + δ) :=
        add_le_add hε₁.le hε₂.le
      _ = (hausdorffDist (range i₁) (range j₁) + hausdorffDist (range i₂) (range j₂)) + (δ + δ) := by ring
      _ ≤ ((gromovHausdorff P Q + δ) + (gromovHausdorff Q S + δ)) + (δ + δ) :=
        add_le_add (add_le_add hr₁.le hr₂.le) le_rfl
      _ = gromovHausdorff P Q + gromovHausdorff Q S + (δ + δ + δ + δ) := by ring
      _ = gromovHausdorff P Q + gromovHausdorff Q S + ε := by
        rw [hδ]
        have h4 : (ε : ℝ≥0∞) / 4 + (ε : ℝ≥0∞) / 4 + (ε : ℝ≥0∞) / 4 + (ε : ℝ≥0∞) / 4 = 4 * ((ε : ℝ≥0∞) / 4) := by ring
        rw [h4, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  · have hQemp : IsEmpty Q := not_nonempty_iff.1 hQ
    by_cases hP : Nonempty P
    · have : gromovHausdorff P Q = ∞ := gromovHausdorff_eq_top_of_empty_right hP hQemp
      exact (hPQ_top this).elim
    · have hPemp : IsEmpty P := not_nonempty_iff.1 hP
      by_cases hS : Nonempty S
      · have : gromovHausdorff Q S = ∞ := gromovHausdorff_eq_top_of_empty_left hQemp hS
        exact (hQS_top this).elim
      · have hSemp : IsEmpty S := not_nonempty_iff.1 hS
        have : gromovHausdorff P S = 0 := by
          unfold gromovHausdorff
          refine le_antisymm ?_ zero_le
          have hr : (0 : ℝ≥0∞) ∈ {r : ℝ≥0∞ | ∃ (Z : Type u) (_ : PseudoEMetricSpace Z) (i : P → Z) (j : S → Z),
              IsDistPreserving i ∧ IsDistPreserving j ∧ r = hausdorffDist (range i) (range j)} := by
            refine ⟨P, inferInstance, id, fun s => (IsEmpty.false s).elim, fun p => (IsEmpty.false p).elim,
              fun s => (IsEmpty.false s).elim, ?_⟩
            have h1 : range (id : P → P) = ∅ := range_eq_empty_iff.2 hPemp
            have h2 : range (fun s : S => (IsEmpty.false s).elim : S → P) = ∅ := range_eq_empty_iff.2 hSemp
            rw [h1, h2]
            unfold hausdorffDist
            have : {ε : ℝ≥0∞ | ∅ ⊆ neighbourhood (∅ : Set P) ε ∧ ∅ ⊆ neighbourhood (∅ : Set P) ε} = Set.univ := by
              ext ε; simp
            rw [this, sInf_univ]
            rfl
          exact sInf_le hr
        rw [this]
        exact zero_le

/-- Definition 2.2.25: a correspondence between sets. -/
def IsCorrespondence {X Y : Type u} (R : Set (X × Y)) : Prop :=
  (∀ x, ∃ y, (x, y) ∈ R) ∧ (∀ y, ∃ x, (x, y) ∈ R)

/-- Definition 2.2.26: the distortion of a correspondence. -/
noncomputable def distortion {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    (R : Set (P × Q)) : ℝ≥0∞ :=
  ⨆ (p : P) (q : Q) (p' : P) (q' : Q) (_ : (p, q) ∈ R) (_ : (p', q') ∈ R),
    (edist p p' - edist q q') ⊔ (edist q q' - edist p p')

noncomputable def corrGlueDist {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    (R : Set (P × Q)) (r : ℝ≥0∞) (p : P) (q : Q) : ℝ≥0∞ :=
  ⨅ (pair : P × Q) (_ : pair ∈ R), edist p pair.1 + edist q pair.2 + r

theorem edist_le_edist_add_distortion {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    {R : Set (P × Q)} {p p' : P} {q q' : Q} (h : (p, q) ∈ R) (h' : (p', q') ∈ R) :
    edist p p' ≤ edist q q' + distortion R := by
  have h_le : edist p p' - edist q q' ≤ distortion R := by
    unfold distortion
    refine le_trans (le_sup_left (b := edist q q' - edist p p')) ?_
    exact le_iSup_of_le p (le_iSup_of_le q (le_iSup_of_le p' (le_iSup_of_le q'
      (le_iSup_of_le h (le_iSup_of_le h' le_rfl)))))
  rw [tsub_le_iff_right] at h_le
  rw [add_comm]
  exact h_le

theorem edist_le_edist_add_distortion' {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    {R : Set (P × Q)} {p p' : P} {q q' : Q} (h : (p, q) ∈ R) (h' : (p', q') ∈ R) :
    edist q q' ≤ edist p p' + distortion R := by
  have h_le : edist q q' - edist p p' ≤ distortion R := by
    unfold distortion
    refine le_trans (le_sup_right (a := edist p p' - edist q q')) ?_
    exact le_iSup_of_le p (le_iSup_of_le q (le_iSup_of_le p' (le_iSup_of_le q'
      (le_iSup_of_le h (le_iSup_of_le h' le_rfl)))))
  rw [tsub_le_iff_right] at h_le
  rw [add_comm]
  exact h_le

theorem corrGlueDist_H1 {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    (R : Set (P × Q)) (r : ℝ≥0∞) (p₁ p₂ : P) (q : Q) :
    corrGlueDist R r p₁ q ≤ edist p₁ p₂ + corrGlueDist R r p₂ q := by
  unfold corrGlueDist
  rw [ENNReal.add_iInf]
  refine le_iInf fun pair => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hpair => ?_
  refine (iInf_le_of_le pair (iInf_le _ hpair)).trans ?_
  calc edist p₁ pair.1 + edist q pair.2 + r
      ≤ (edist p₁ p₂ + edist p₂ pair.1) + edist q pair.2 + r :=
        add_le_add (add_le_add (edist_triangle p₁ p₂ pair.1) le_rfl) le_rfl
    _ = edist p₁ p₂ + (edist p₂ pair.1 + edist q pair.2 + r) := by ring

theorem corrGlueDist_H2 {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    (R : Set (P × Q)) (r : ℝ≥0∞) (p : P) (q₁ q₂ : Q) :
    corrGlueDist R r p q₂ ≤ corrGlueDist R r p q₁ + edist q₁ q₂ := by
  unfold corrGlueDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun pair => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hpair => ?_
  refine (iInf_le_of_le pair (iInf_le _ hpair)).trans ?_
  calc edist p pair.1 + edist q₂ pair.2 + r
      ≤ edist p pair.1 + (edist q₂ q₁ + edist q₁ pair.2) + r :=
        add_le_add (add_le_add le_rfl (edist_triangle q₂ q₁ pair.2)) le_rfl
    _ = (edist p pair.1 + edist q₁ pair.2 + r) + edist q₁ q₂ := by
        rw [edist_comm q₂ q₁]; ring

theorem corrGlueDist_H3 {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    (R : Set (P × Q)) (p₁ p₂ : P) (q : Q) :
    edist p₁ p₂ ≤ corrGlueDist R (distortion R / 2) p₁ q + corrGlueDist R (distortion R / 2) p₂ q := by
  unfold corrGlueDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun pair₁ => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hpair₁ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun pair₂ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hpair₂ => ?_
  have hq : edist pair₁.1 pair₂.1 ≤ edist q pair₁.2 + edist q pair₂.2 + distortion R := by
    calc edist pair₁.1 pair₂.1 ≤ edist pair₁.2 pair₂.2 + distortion R :=
        edist_le_edist_add_distortion hpair₁ hpair₂
      _ ≤ (edist pair₁.2 q + edist q pair₂.2) + distortion R :=
        add_le_add (edist_triangle pair₁.2 q pair₂.2) le_rfl
      _ = edist q pair₁.2 + edist q pair₂.2 + distortion R := by rw [edist_comm pair₁.2 q]
  calc edist p₁ p₂ ≤ edist p₁ pair₁.1 + edist pair₁.1 p₂ := edist_triangle _ _ _
    _ ≤ edist p₁ pair₁.1 + (edist pair₁.1 pair₂.1 + edist pair₂.1 p₂) := add_le_add le_rfl (edist_triangle _ _ _)
    _ = edist p₁ pair₁.1 + edist pair₂.1 p₂ + edist pair₁.1 pair₂.1 := by ring
    _ ≤ edist p₁ pair₁.1 + edist p₂ pair₂.1 + (edist q pair₁.2 + edist q pair₂.2 + distortion R) := by
      rw [edist_comm pair₂.1 p₂]
      exact add_le_add le_rfl hq
    _ = (edist p₁ pair₁.1 + edist q pair₁.2 + distortion R / 2) +
        (edist p₂ pair₂.1 + edist q pair₂.2 + distortion R / 2) := by
      have hd : distortion R = distortion R / 2 + distortion R / 2 := (ENNReal.add_halves _).symm
      nth_rw 1 [hd]
      ring

theorem corrGlueDist_H4 {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    (R : Set (P × Q)) (p : P) (q₁ q₂ : Q) :
    edist q₁ q₂ ≤ corrGlueDist R (distortion R / 2) p q₁ + corrGlueDist R (distortion R / 2) p q₂ := by
  unfold corrGlueDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun pair₁ => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hpair₁ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun pair₂ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hpair₂ => ?_
  have hp : edist pair₁.2 pair₂.2 ≤ edist p pair₁.1 + edist p pair₂.1 + distortion R := by
    calc edist pair₁.2 pair₂.2 ≤ edist pair₁.1 pair₂.1 + distortion R :=
        edist_le_edist_add_distortion' hpair₁ hpair₂
      _ ≤ (edist pair₁.1 p + edist p pair₂.1) + distortion R :=
        add_le_add (edist_triangle pair₁.1 p pair₂.1) le_rfl
      _ = edist p pair₁.1 + edist p pair₂.1 + distortion R := by rw [edist_comm pair₁.1 p]
  calc edist q₁ q₂ ≤ edist q₁ pair₁.2 + edist pair₁.2 q₂ := edist_triangle _ _ _
    _ ≤ edist q₁ pair₁.2 + (edist pair₁.2 pair₂.2 + edist pair₂.2 q₂) := add_le_add le_rfl (edist_triangle _ _ _)
    _ = edist q₁ pair₁.2 + edist pair₂.2 q₂ + edist pair₁.2 pair₂.2 := by ring
    _ ≤ edist q₁ pair₁.2 + edist q₂ pair₂.2 + (edist p pair₁.1 + edist p pair₂.1 + distortion R) := by
      rw [edist_comm pair₂.2 q₂]
      exact add_le_add le_rfl hp
    _ = (edist p pair₁.1 + edist q₁ pair₁.2 + distortion R / 2) +
        (edist p pair₂.1 + edist q₂ pair₂.2 + distortion R / 2) := by
      have hd : distortion R = distortion R / 2 + distortion R / 2 := (ENNReal.add_halves _).symm
      nth_rw 1 [hd]
      ring

theorem two_mul_gromovHausdorff_le_distortion
    {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q]
    {R : Set (P × Q)} (hR : IsCorrespondence R) :
    2 * gromovHausdorff P Q ≤ distortion R := by
  by_cases hdis : distortion R = ∞
  · rw [hdis]; exact le_top
  by_cases hP : Nonempty P
  · have hdis2_lt : distortion R / 2 < ∞ := by
      exact ENNReal.div_lt_top hdis (by norm_num)
    have hGH_le_half : gromovHausdorff P Q ≤ distortion R / 2 := by
      refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
      have hδ0 : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hδ.ne'
      set ε : ℝ≥0∞ := distortion R / 2 + (δ : ℝ≥0∞) with hε_def
      have hlt_ε : distortion R / 2 < ε := ENNReal.lt_add_right hdis2_lt.ne hδ0
      have H1 := corrGlueDist_H1 R (distortion R / 2)
      have H2 := corrGlueDist_H2 R (distortion R / 2)
      have H3 := corrGlueDist_H3 R
      have H4 := corrGlueDist_H4 R
      have hmet : IsEPMetric (sumDist (corrGlueDist R (distortion R / 2))) :=
        sumDist_isEPMetric (corrGlueDist R (distortion R / 2)) H1 H2 H3 H4
      let Z := WithDist (sumDist (corrGlueDist R (distortion R / 2))) hmet
      let I : P → Z := fun p => Sum.inl p
      let J : Q → Z := fun q => Sum.inr q
      have hI : IsDistPreserving I := fun p p' => by
        change edist p p' = sumDist (corrGlueDist R (distortion R / 2)) (Sum.inl p) (Sum.inl p')
        simp only [sumDist]
      have hJ : IsDistPreserving J := fun q q' => by
        change edist q q' = sumDist (corrGlueDist R (distortion R / 2)) (Sum.inr q) (Sum.inr q')
        simp only [sumDist]
      have h_range_J : range J ⊆ neighbourhood (range I) ε := by
        rintro z ⟨q, rfl⟩
        obtain ⟨p, hpq⟩ := hR.2 q
        refine ⟨I p, ⟨p, rfl⟩, ?_⟩
        change sumDist (corrGlueDist R (distortion R / 2)) (Sum.inl p) (Sum.inr q) < ε
        simp only [sumDist]
        refine ((iInf_le_of_le (p, q) (iInf_le _ hpq)).trans_lt ?_)
        simp only [edist_self, zero_add]
        exact hlt_ε
      have h_range_I : range I ⊆ neighbourhood (range J) ε := by
        rintro z ⟨p, rfl⟩
        obtain ⟨q, hpq⟩ := hR.1 p
        refine ⟨J q, ⟨q, rfl⟩, ?_⟩
        change sumDist (corrGlueDist R (distortion R / 2)) (Sum.inr q) (Sum.inl p) < ε
        simp only [sumDist]
        refine ((iInf_le_of_le (p, q) (iInf_le _ hpq)).trans_lt ?_)
        simp only [edist_self, zero_add]
        exact hlt_ε
      have h_hd : hausdorffDist (range I) (range J) ≤ ε :=
        sInf_le ⟨h_range_J, h_range_I⟩
      refine le_trans ?_ h_hd
      exact sInf_le ⟨Z, inferInstance, I, J, hI, hJ, rfl⟩
    calc 2 * gromovHausdorff P Q = gromovHausdorff P Q + gromovHausdorff P Q := by ring
      _ ≤ distortion R / 2 + distortion R / 2 := add_le_add hGH_le_half hGH_le_half
      _ = distortion R := ENNReal.add_halves _
  · have hPemp : IsEmpty P := not_nonempty_iff.1 hP
    have hQemp : IsEmpty Q := by
      refine ⟨fun q => ?_⟩
      obtain ⟨p, -⟩ := hR.2 q
      exact (IsEmpty.false p).elim
    have hGH0 : gromovHausdorff P Q = 0 := by
      unfold gromovHausdorff
      refine le_antisymm ?_ zero_le
      have hr : (0 : ℝ≥0∞) ∈ {r : ℝ≥0∞ | ∃ (Z : Type u) (_ : PseudoEMetricSpace Z) (i : P → Z) (j : Q → Z),
          IsDistPreserving i ∧ IsDistPreserving j ∧ r = hausdorffDist (range i) (range j)} := by
        refine ⟨P, inferInstance, id, fun q => (IsEmpty.false q).elim, fun p => (IsEmpty.false p).elim,
          fun q => (IsEmpty.false q).elim, ?_⟩
        have h1 : range (id : P → P) = ∅ := range_eq_empty_iff.2 hPemp
        have h2 : range (fun q : Q => (IsEmpty.false q).elim : Q → P) = ∅ := range_eq_empty_iff.2 hQemp
        rw [h1, h2]
        unfold hausdorffDist
        have : {ε : ℝ≥0∞ | ∅ ⊆ neighbourhood (∅ : Set P) ε ∧ ∅ ⊆ neighbourhood (∅ : Set P) ε} = Set.univ := by
          ext ε; simp
        rw [this, sInf_univ]
        rfl
      exact sInf_le hr
    rw [hGH0, mul_zero]
    exact zero_le

theorem sInf_distortion_le_two_mul_gromovHausdorff
    {P Q : Type u} [PseudoEMetricSpace P] [PseudoEMetricSpace Q] :
    sInf {r | ∃ R : Set (P × Q), IsCorrespondence R ∧ r = distortion R} ≤
      2 * gromovHausdorff P Q := by
  by_cases hGH : gromovHausdorff P Q = ∞
  · rw [hGH]
    have : (2 : ℝ≥0∞) * ∞ = ∞ := by simp
    rw [this]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 4 with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    exact (ENNReal.div_pos hε0 (by norm_num)).ne'
  have hlt : gromovHausdorff P Q < gromovHausdorff P Q + δ :=
    ENNReal.lt_add_right hGH hδ0
  unfold gromovHausdorff at hlt
  simp only [sInf_lt_iff] at hlt
  obtain ⟨r_hd, ⟨Z, _, i, j, hi, hj, rfl⟩, hr_hd⟩ := hlt
  set r : ℝ≥0∞ := gromovHausdorff P Q + δ with hr_def
  have h_hd_lt_r : hausdorffDist (range i) (range j) < r := hr_hd
  unfold hausdorffDist at h_hd_lt_r
  simp only [sInf_lt_iff] at h_hd_lt_r
  obtain ⟨r', ⟨hj_sub, hi_sub⟩, hr'_lt⟩ := h_hd_lt_r
  set R : Set (P × Q) := {pair | edist (i pair.1) (j pair.2) < r}
  have hR : IsCorrespondence R := by
    constructor
    · intro p
      have hip : i p ∈ range i := ⟨p, rfl⟩
      obtain ⟨_, ⟨q, rfl⟩, hdist⟩ := hi_sub hip
      refine ⟨q, ?_⟩
      change edist (i p) (j q) < r
      rw [edist_comm]
      exact hdist.trans_le hr'_lt.le
    · intro q
      have hjq : j q ∈ range j := ⟨q, rfl⟩
      obtain ⟨_, ⟨p, rfl⟩, hdist⟩ := hj_sub hjq
      refine ⟨p, ?_⟩
      change edist (i p) (j q) < r
      exact hdist.trans_le hr'_lt.le
  have h_dist : distortion R ≤ 2 * r := by
    unfold distortion
    refine iSup_le fun p => iSup_le fun q => iSup_le fun p' => iSup_le fun q' =>
      iSup_le fun hpq => iSup_le fun hp'q' => ?_
    change edist (i p) (j q) < r at hpq
    change edist (i p') (j q') < r at hp'q'
    refine sup_le ?_ ?_
    · rw [tsub_le_iff_right, add_comm]
      have h1 : edist p p' = edist (i p) (i p') := hi p p'
      have h2 : edist q q' = edist (j q) (j q') := hj q q'
      rw [h1, h2]
      have ht1 : edist (i p) (i p') ≤ edist (i p) (j q) + edist (j q) (i p') :=
        edist_triangle _ _ _
      have ht2 : edist (j q) (i p') ≤ edist (j q) (j q') + edist (j q') (i p') :=
        edist_triangle _ _ _
      calc edist (i p) (i p') ≤ edist (i p) (j q) + (edist (j q) (j q') + edist (j q') (i p')) :=
          ht1.trans (add_le_add le_rfl ht2)
        _ = edist (j q) (j q') + (edist (i p) (j q) + edist (i p') (j q')) := by
          rw [edist_comm (j q') (i p')]; ring
        _ ≤ edist (j q) (j q') + (r + r) :=
          add_le_add le_rfl (add_le_add hpq.le hp'q'.le)
        _ = edist (j q) (j q') + 2 * r := by
          have : r + r = 2 * r := by ring
          rw [this]
    · rw [tsub_le_iff_right, add_comm]
      have h1 : edist p p' = edist (i p) (i p') := hi p p'
      have h2 : edist q q' = edist (j q) (j q') := hj q q'
      rw [h1, h2]
      have ht1 : edist (j q) (j q') ≤ edist (j q) (i p) + edist (i p) (j q') :=
        edist_triangle _ _ _
      have ht2 : edist (i p) (j q') ≤ edist (i p) (i p') + edist (i p') (j q') :=
        edist_triangle _ _ _
      calc edist (j q) (j q') ≤ edist (j q) (i p) + (edist (i p) (i p') + edist (i p') (j q')) :=
          ht1.trans (add_le_add le_rfl ht2)
        _ = edist (i p) (i p') + (edist (i p) (j q) + edist (i p') (j q')) := by
          rw [edist_comm (j q) (i p)]; ring
        _ ≤ edist (i p) (i p') + (r + r) :=
          add_le_add le_rfl (add_le_add hpq.le hp'q'.le)
        _ = edist (i p) (i p') + 2 * r := by
          have : r + r = 2 * r := by ring
          rw [this]
  have h_mem : distortion R ∈ {r | ∃ R : Set (P × Q), IsCorrespondence R ∧ r = distortion R} :=
    ⟨R, hR, rfl⟩
  refine (sInf_le h_mem).trans ?_
  refine h_dist.trans ?_
  rw [hr_def]
  calc 2 * (gromovHausdorff P Q + δ) = 2 * gromovHausdorff P Q + 2 * δ := by ring
    _ ≤ 2 * gromovHausdorff P Q + ε := by
      refine add_le_add le_rfl ?_
      rw [hδ]
      calc (2 : ℝ≥0∞) * ((ε : ℝ≥0∞) / 4) = (ε : ℝ≥0∞) / 4 + (ε : ℝ≥0∞) / 4 := by ring
        _ ≤ ((ε : ℝ≥0∞) / 4 + (ε : ℝ≥0∞) / 4) + ((ε : ℝ≥0∞) / 4 + (ε : ℝ≥0∞) / 4) := le_self_add
        _ = 4 * ((ε : ℝ≥0∞) / 4) := by ring
        _ = (ε : ℝ≥0∞) := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- Theorem 2.2.27: `2 d_GH = inf dist R` over correspondences. -/
theorem two_mul_gromovHausdorff_eq (P Q : Type u) [MetricSpace P] [MetricSpace Q] :
    2 * gromovHausdorff P Q = sInf {r | ∃ R : Set (P × Q), IsCorrespondence R ∧
      r = distortion R} := by
  refine le_antisymm ?_ sInf_distortion_le_two_mul_gromovHausdorff
  refine le_sInf fun r hr => ?_
  obtain ⟨R, hR, rfl⟩ := hr
  exact two_mul_gromovHausdorff_le_distortion hR

end GromovHausdorff

end Metric

/-! ## Chapter 2.3: Monoidal categories

Every notion of this section is already in Mathlib, so we only record the dictionary.
The coherence diagrams (triangle, pentagon, hexagon, associativity/unitality of lax
monoidal functors, monoidal natural transformations) are fields of the Mathlib structures.

| Thesis                                 | Mathlib                                         |
|----------------------------------------|-------------------------------------------------|
| Def 2.3.1 monoidal category            | `CategoryTheory.MonoidalCategory`               |
| Def 2.3.2 lax monoidal functor         | `CategoryTheory.Functor.LaxMonoidal`            |
| Def 2.3.2 strong monoidal functor      | `CategoryTheory.Functor.Monoidal`               |
| Def 2.3.3 monoidal natural transf.     | `CategoryTheory.NatTrans.IsMonoidal`            |
| Def 2.3.4 symmetric monoidal category  | `CategoryTheory.SymmetricCategory`              |
| Def 2.3.5 closed symmetric monoidal    | `SymmetricCategory` + `MonoidalClosed`          | -/

section Monoidal

open CategoryTheory MonoidalCategory

/-- Definition 2.3.5: a closed symmetric monoidal category is a symmetric monoidal category in
which every `- ⊗ x` has a right adjoint `[x, -]` (`ihom x` in Mathlib). -/
abbrev IsClosedSymmetricMonoidal (V : Type u) [Category.{v} V] [MonoidalCategory V]
    [SymmetricCategory V] : Type _ :=
  MonoidalClosed V

end Monoidal

end ScoccolaPhd
