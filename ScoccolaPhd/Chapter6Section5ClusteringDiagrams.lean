import Mathlib
import ScoccolaPhd.Chapter6Section1DissimilarityFiltrations

/-!
# §§6.5–6.6: kernel density and hierarchical clustering

Contents:
* Chapter 6.5: Stability of the kernel density filtration
* Chapter 6.6: The correspondence-interleaving distance on hierarchical clusterings
-/

universe u v

namespace ScoccolaPhd

/-! ## Chapter 6.5: Stability of the kernel density filtration

Kernels, compact metric probability spaces and the Gromov–Hausdorff–Prokhorov distance are
defined concretely (the Prokhorov distance is Mathlib's `levyProkhorovEDist`).  Weighted
dissimilarity spaces `WDiss` form a category (the `(0, 0)`-morphisms); the locally bi-persistent
structure is stated to exist, and the kernel density filtration is given by its objects.

The target `Diss^{ℝ × ℝᵒᵖ}_v` of the filtration needs the `n`-parameter version of Section 5.1.2
(Remark 5.1.10, not formalized); its locally persistent structure `LD` is therefore a hypothesis,
to be thought of as the one obtained by change of enrichment along `v = (1, 1, 1)` (the hom-sets
are not recorded here).  Corollary 6.5.2 (persistent homology) is omitted.

The uniform kernel, weighted category, its pullbacks and locally bi-persistent structure,
and the metric-probability-space construction are proved. The remaining analytic and stability
results are open. -/

section KernelDensity

open CategoryTheory CategoryTheory.Limits MeasureTheory
open scoped NNReal ENNReal

open LPCat

/-! ### 6.5.1 The Gromov–Hausdorff–Prokhorov metric -/

/-- A compact metric probability space. -/
structure CompactMPS where
  carrier : Type u
  [metric : MetricSpace carrier]
  [meas : MeasurableSpace carrier]
  [borel : BorelSpace carrier]
  μ : Measure carrier
  [prob : IsProbabilityMeasure μ]
  [compact : CompactSpace carrier]

attribute [instance] CompactMPS.metric CompactMPS.meas CompactMPS.borel CompactMPS.prob
  CompactMPS.compact

/-- Definition 6.5.4: the Gromov–Hausdorff–Prokhorov distance,
`inf_{i, j} max (d_H(i X, j Y), d_P(i_* μ_X, j_* μ_Y))` over isometric embeddings into a common
metric space `Z`. -/
noncomputable def ghpDist (X Y : CompactMPS.{u}) : ℝ≥0∞ :=
  ⨅ (Z : Type u) (_ : MetricSpace Z) (_ : MeasurableSpace Z) (_ : BorelSpace Z)
    (i : X.carrier → Z) (j : Y.carrier → Z) (_ : Isometry i) (_ : Isometry j),
    max (Metric.hausdorffEDist (Set.range i) (Set.range j))
      (levyProkhorovEDist (X.μ.map i) (Y.μ.map j))

/-! ### 6.5.2 The kernel density filtration -/

/-- Definition 6.5.5: a kernel is a non-increasing right-continuous `K : ℝ≥0 → ℝ≥0` with
`0 < ∫ K < ∞`. -/
structure Kernel where
  toFun : ℝ≥0 → ℝ≥0
  anti : Antitone toFun
  rightCont : ∀ r, ContinuousWithinAt toFun (Set.Ici r) r
  integral_pos : 0 < ∫⁻ r in Set.Ici (0 : ℝ), (toFun r.toNNReal : ℝ≥0∞)
  integral_lt_top : (∫⁻ r in Set.Ici (0 : ℝ), (toFun r.toNNReal : ℝ≥0∞)) < ∞

private theorem uniformKernel_integral :
    (∫⁻ r in Set.Ici (0 : ℝ),
      ((if r.toNNReal < 1 then 1 else 0 : ℝ≥0) : ℝ≥0∞)) = 1 := by
  have hfun : (fun r : ℝ => ((if r.toNNReal < 1 then 1 else 0 : ℝ≥0) : ℝ≥0∞)) =
      (Set.Iio (1 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext r
    have hr : r.toNNReal < 1 ↔ r < 1 := by
      by_cases h : 0 ≤ r
      · simp [Real.toNNReal_lt_iff_lt_coe h]
      · simp [Real.toNNReal_of_nonpos (le_of_not_ge h), lt_trans (lt_of_not_ge h) zero_lt_one]
    simp [hr, Set.indicator_apply, apply_ite]
  rw [hfun, lintegral_indicator measurableSet_Iio]
  simp [Measure.restrict_apply, measurableSet_Iio, Set.Iio_inter_Ici, Real.volume_Ico]

/-- Example 6.5.6: the uniform kernel `1_{r < 1}`. -/
noncomputable def Kernel.uniform : Kernel where
  toFun r := if r < 1 then 1 else 0
  anti a b h := by
    by_cases hb : b < 1
    · simp [hb, lt_of_le_of_lt h hb]
    · simp [hb]
  rightCont r := by
    by_cases hr : r < 1
    · apply ContinuousWithinAt.congr_of_eventuallyEq (continuousWithinAt_const (b := (1 : ℝ≥0)))
      · filter_upwards [eventually_lt_nhds hr |>.filter_mono nhdsWithin_le_nhds] with s hs
        simp [hs]
      · simp [hr]
    · apply ContinuousWithinAt.congr_of_eventuallyEq (continuousWithinAt_const (b := (0 : ℝ≥0)))
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp [not_lt.mpr ((le_of_not_gt hr).trans hs)]
      · simp [hr]
  integral_pos := by rw [uniformKernel_integral]; exact zero_lt_one
  integral_lt_top := by rw [uniformKernel_integral]; exact ENNReal.one_lt_top

/-- Lemma 6.5.8: `K⁻¹ (t) = min {u | K u ≤ t}`. -/
noncomputable def Kernel.inv (K : Kernel) (t : ℝ≥0) : ℝ≥0 := sInf {u | K.toFun u ≤ t}

/-- Definition 6.5.9: a weighted dissimilarity space: a dissimilarity space with a function
`M x r` (the measure of the ball of radius `r` around `x`) that is monotone in `r`. -/
structure WDiss where
  carrier : Type u
  d : carrier → carrier → ℝ≥0∞
  M : carrier → ℝ≥0 → ℝ≥0
  mono : ∀ x, Monotone (M x)

/-- The underlying dissimilarity space. -/
def WDiss.toDiss (X : WDiss.{u}) : Diss.{u} := ⟨X.carrier, X.d⟩

/-- Example 6.5.10: a compact metric probability space as a weighted dissimilarity space,
`M x r = μ (B (x, r))`. -/
noncomputable def CompactMPS.toWDiss (X : CompactMPS.{u}) : WDiss.{u} where
  carrier := X.carrier
  d x y := edist x y
  M x r := (X.μ (Metric.ball x r)).toNNReal
  mono x a b h := by
    exact ENNReal.toNNReal_mono (measure_ne_top _ _)
      (measure_mono (Metric.ball_subset_ball h))

/-- Definition 6.5.11: the `(ε, δ)`-morphisms of `wDiss`: maps with `d_X + ε ≥ d_Y ∘ f` and
`M_X (x, r) ≤ M_Y (f x, r + ε) + δ`. -/
def WDissHom (X Y : WDiss.{u}) (ε δ : ℝ≥0) : Type u :=
  {f : X.carrier → Y.carrier // (∀ x x', Y.d (f x) (f x') ≤ X.d x x' + ε) ∧
    ∀ x (r : ℝ≥0), X.M x r ≤ Y.M (f x) (r + ε) + δ}

/-- The category of weighted dissimilarity spaces and `(0, 0)`-morphisms. -/
instance : Category.{u} WDiss.{u} where
  Hom X Y := WDissHom X Y 0 0
  id X := ⟨id, by simp⟩
  comp f g := ⟨g.1 ∘ f.1, by
    constructor
    · intro x x'
      simpa using (g.2.1 (f.1 x) (f.1 x')).trans (by simpa using f.2.1 x x')
    · intro x r
      have hf : _ ≤ _ := f.2.2 x r
      have hg : _ ≤ _ := g.2.2 (f.1 x) r
      simp only [add_zero] at hf hg ⊢
      exact hf.trans hg⟩

/-- Definition 6.5.11: the locally bi-persistent structure on `wDiss`. -/
def wDissLQPCat : LQPCat (ℝ≥0 × ℝ≥0) WDiss.{u} where
  hom := fun X Y q => WDissHom X Y q.1 q.2
  homZero := Equiv.refl _
  comp := fun {X Y Z ε δ} g f => ⟨g.1 ∘ f.1, by
    constructor
    · intro x x'
      calc
        Z.d (g.1 (f.1 x)) (g.1 (f.1 x')) ≤ Y.d (f.1 x) (f.1 x') + δ.1 := g.2.1 _ _
        _ ≤ (X.d x x' + ε.1) + δ.1 := add_le_add (f.2.1 _ _) le_rfl
        _ = X.d x x' + ((ε + δ).1 : ℝ≥0∞) := by simp [ENNReal.coe_add, add_assoc]
    · intro x r
      calc
        X.M x r ≤ Y.M (f.1 x) (r + ε.1) + ε.2 := f.2.2 _ _
        _ ≤ (Z.M (g.1 (f.1 x)) ((r + ε.1) + δ.1) + δ.2) + ε.2 :=
          add_le_add (g.2.2 _ _) le_rfl
        _ = Z.M (g.1 (f.1 x)) (r + (ε + δ).1) + (ε + δ).2 := by
          simp [add_assoc, add_comm, add_left_comm]⟩
  S := fun {X Y ε δ} h f => ⟨f.1, by
    constructor
    · intro x x'
      exact (f.2.1 x x').trans (add_le_add le_rfl (by exact_mod_cast h.1))
    · intro x r
      exact (f.2.2 x r).trans (add_le_add (Y.mono _ (add_le_add le_rfl h.1)) h.2)⟩
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl
  S_refl := fun _ => rfl
  S_trans := fun _ _ _ => rfl
  comp_S := fun _ _ _ _ => rfl
  homZero_comp := fun _ _ => rfl

/-- Definition 6.5.11: `wDiss` is a locally bi-persistent category. -/
theorem exists_wDiss_lqpcat :
    ∃ L : LQPCat (ℝ≥0 × ℝ≥0) WDiss.{u}, ∀ (X Y : WDiss.{u}) (ε δ : ℝ≥0),
      L.hom X Y (ε, δ) = WDissHom X Y ε δ :=
  ⟨wDissLQPCat, fun _ _ _ _ => rfl⟩

/-- Definition 6.5.14: acyclic morphisms of weighted dissimilarity spaces: surjective, distance
preserving and weight preserving. -/
def acyclicWDiss : MorphismProperty WDiss.{u} :=
  fun X Y f => Function.Surjective f.1 ∧ (∀ x x', Y.d (f.1 x) (f.1 x') = X.d x x') ∧
    ∀ x r, X.M x r = Y.M (f.1 x) r

instance : acyclicWDiss.{u}.IsMultiplicative where
  id_mem _ := ⟨Function.surjective_id, fun _ _ => rfl, fun _ _ => rfl⟩
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1,
    fun x y => by dsimp [CategoryStruct.comp]; rw [hg.2.1, hf.2.1],
    fun x r => by dsimp [CategoryStruct.comp]; rw [hf.2.2, hg.2.2]⟩

/-- Lemma 6.5.15: the underlying category of `wDiss` has pullbacks, and acyclic morphisms are
stable under pullback. -/
theorem wDiss_hasPullbacks : Limits.HasPullbacks WDiss.{u} := by
  have : ∀ {X Y Z : WDiss.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g) := by
    intro X Y Z f g
    let P : WDiss.{u} :=
      { carrier := {p : X.carrier × Y.carrier // f.1 p.1 = g.1 p.2}
        d := fun p q => max (X.d p.1.1 q.1.1) (Y.d p.1.2 q.1.2)
        M := fun p r => min (X.M p.1.1 r) (Y.M p.1.2 r)
        mono := fun p a b h => min_le_min (X.mono _ h) (Y.mono _ h) }
    let pX : P ⟶ X := ⟨fun p => p.1.1, by
      constructor
      · intro p q; simp [P]
      · intro p r; simp [P]⟩
    let pY : P ⟶ Y := ⟨fun p => p.1.2, by
      constructor
      · intro p q; simp [P]
      · intro p r; simp [P]⟩
    let c : PullbackCone f g := PullbackCone.mk pX pY (by
      apply Subtype.ext
      funext p
      exact p.2)
    refine ⟨⟨c, PullbackCone.isLimitAux' c fun s => ?_⟩⟩
    let l : s.pt ⟶ P := ⟨fun x => ⟨((s.fst).1 x, (s.snd).1 x),
      congrFun (congrArg Subtype.val s.condition) x⟩, by
      constructor
      · intro x y
        simpa [P] using max_le (s.fst.2.1 x y) (s.snd.2.1 x y)
      · intro x r
        simpa [P] using le_min (s.fst.2.2 x r) (s.snd.2.2 x r)⟩
    refine ⟨l, rfl, rfl, ?_⟩
    intro m hmX hmY
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact Prod.ext (congrFun (congrArg Subtype.val hmX) x)
      (congrFun (congrArg Subtype.val hmY) x)
  exact Limits.hasPullbacks_of_hasLimit_cospan WDiss

private def wDissPow (q : ℝ≥0 × ℝ≥0) : WDiss.{u} ⥤ WDiss.{u} where
  obj Y :=
    { carrier := Y.carrier
      d := fun y y' => Y.d y y' - q.1
      M := fun y s => Y.M y (s + q.1) + q.2
      mono := fun y _ _ h => add_le_add (Y.mono _ (add_le_add h le_rfl)) le_rfl }
  map {Y Y'} f := ⟨f.1, by
    constructor
    · intro y y'
      simpa using tsub_le_tsub_right (by simpa using f.2.1 y y') (q.1 : ℝ≥0∞)
    · intro y s
      have h := f.2.2 y (s + q.1)
      simp only [add_zero] at h ⊢
      exact add_le_add h le_rfl⟩
  map_id _ := rfl
  map_comp _ _ := rfl

private def wDissQPowered : QPoweredByRepresentables wDissLQPCat.{u} where
  pow := wDissPow
  powIso X Y q r :=
    { toFun := fun u => ⟨u.1, by
        constructor
        · intro x x'
          have h1 := u.2.1 x x'
          dsimp [wDissPow] at h1
          rw [tsub_le_iff_right] at h1
          exact h1.trans (le_of_eq (by simp [ENNReal.coe_add, add_assoc, add_comm, add_left_comm]))
        · intro x s
          have h2 := u.2.2 x s
          dsimp [wDissPow] at h2
          exact h2.trans (le_of_eq (by simp [add_assoc, add_comm, add_left_comm]))⟩
      invFun := fun v => ⟨v.1, by
        constructor
        · intro x x'
          dsimp [wDissPow]
          rw [tsub_le_iff_right]
          exact (v.2.1 x x').trans (le_of_eq (by
            simp [ENNReal.coe_add, add_assoc, add_comm, add_left_comm]))
        · intro x s
          dsimp [wDissPow]
          exact (v.2.2 x s).trans (le_of_eq (by simp [add_assoc, add_comm, add_left_comm]))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  powIso_S _ _ := rfl
  powIso_x _ _ := rfl
  powIso_y _ _ := rfl

private theorem wDissPow_preservesPullbacks (q : ℝ≥0 × ℝ≥0) :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan (wDissPow.{u} q) := by
  constructor
  intro K
  let X := K.obj Limits.WalkingCospan.left
  let Y := K.obj Limits.WalkingCospan.right
  let Z := K.obj Limits.WalkingCospan.one
  let f : X ⟶ Z := K.map Limits.WalkingCospan.Hom.inl
  let g : Y ⟶ Z := K.map Limits.WalkingCospan.Hom.inr
  let P : WDiss.{u} :=
    { carrier := {p : X.carrier × Y.carrier // f.1 p.1 = g.1 p.2}
      d := fun p q' => max (X.d p.1.1 q'.1.1) (Y.d p.1.2 q'.1.2)
      M := fun p r => min (X.M p.1.1 r) (Y.M p.1.2 r)
      mono := fun p a b h => min_le_min (X.mono _ h) (Y.mono _ h) }
  let pX : P ⟶ X := ⟨fun p => p.1.1, by constructor <;> intros <;> simp [P]⟩
  let pY : P ⟶ Y := ⟨fun p => p.1.2, by constructor <;> intros <;> simp [P]⟩
  let c : Limits.PullbackCone f g := Limits.PullbackCone.mk pX pY (by
    apply Subtype.ext; funext p; exact p.2)
  have hc : Limits.IsLimit c := Limits.PullbackCone.isLimitAux' c fun s => by
    let l : s.pt ⟶ P := ⟨fun x => ⟨(s.fst.1 x, s.snd.1 x),
      congrFun (congrArg Subtype.val s.condition) x⟩, by
      constructor
      · intro x y; simpa [P] using max_le (s.fst.2.1 x y) (s.snd.2.1 x y)
      · intro x r; simpa [P] using le_min (s.fst.2.2 x r) (s.snd.2.2 x r)⟩
    refine ⟨l, rfl, rfl, fun {m} hmX hmY => ?_⟩
    apply Subtype.ext; funext x; apply Subtype.ext
    exact Prod.ext (congrFun (congrArg Subtype.val hmX) x)
      (congrFun (congrArg Subtype.val hmY) x)
  haveI : Limits.PreservesLimit (Limits.cospan f g) (wDissPow q) := by
    refine Limits.preservesLimit_of_preserves_limit_cone hc ?_
    refine Limits.IsLimit.mk ?_ ?_ ?_
    · intro s
      refine ⟨fun x => ⟨((s.π.app Limits.WalkingCospan.left).1 x,
          (s.π.app Limits.WalkingCospan.right).1 x), ?_⟩, ?_⟩
      · have hL := congrFun (congrArg Subtype.val (s.w Limits.WalkingCospan.Hom.inl)) x
        have hR := congrFun (congrArg Subtype.val (s.w Limits.WalkingCospan.Hom.inr)) x
        exact hL.trans hR.symm
      · constructor
        · intro x y
          have hx : X.d ((s.π.app Limits.WalkingCospan.left).1 x)
              ((s.π.app Limits.WalkingCospan.left).1 y) - q.1 ≤ s.pt.d x y := by
            simpa [wDissPow] using (s.π.app Limits.WalkingCospan.left).2.1 x y
          have hy : Y.d ((s.π.app Limits.WalkingCospan.right).1 x)
              ((s.π.app Limits.WalkingCospan.right).1 y) - q.1 ≤ s.pt.d x y := by
            simpa [wDissPow] using (s.π.app Limits.WalkingCospan.right).2.1 x y
          dsimp [wDissPow, P]
          rw [add_zero, tsub_le_iff_right]
          exact max_le (tsub_le_iff_right.mp hx) (tsub_le_iff_right.mp hy)
        · intro x r
          have hx : s.pt.M x r ≤ X.M ((s.π.app Limits.WalkingCospan.left).1 x) (r + q.1) + q.2 := by
            simpa [wDissPow] using (s.π.app Limits.WalkingCospan.left).2.2 x r
          have hy : s.pt.M x r ≤ Y.M ((s.π.app Limits.WalkingCospan.right).1 x) (r + q.1) + q.2 := by
            simpa [wDissPow] using (s.π.app Limits.WalkingCospan.right).2.2 x r
          dsimp [wDissPow, P]
          rw [add_zero]
          have hmin : ∀ a b c : ℝ≥0, min (a + c) (b + c) ≤ min a b + c := fun a b c => by
            rcases le_total a b with h | h
            · simp [min_eq_left h, min_eq_left (add_le_add h le_rfl)]
            · simp [min_eq_right h, min_eq_right (add_le_add h le_rfl)]
          exact (le_min (by simpa [add_assoc] using hx) (by simpa [add_assoc] using hy)).trans (hmin _ _ _)
    · intro s j
      rcases j with (_ | _ | _)
      · apply Subtype.ext; funext x
        have hL := congrFun (congrArg Subtype.val (s.w Limits.WalkingCospan.Hom.inl)) x
        have hR := congrFun (congrArg Subtype.val (s.w Limits.WalkingCospan.Hom.inr)) x
        have h1 := congrFun (congrArg Subtype.val (c.w Limits.WalkingCospan.Hom.inl))
          (⟨((s.π.app Limits.WalkingCospan.left).1 x, (s.π.app Limits.WalkingCospan.right).1 x),
            hL.trans hR.symm⟩ : P.carrier)
        exact h1.symm.trans hL
      · rfl
      · rfl
    · intro s m hm
      apply Subtype.ext; funext x; apply Subtype.ext
      exact Prod.ext
        (congrFun (congrArg Subtype.val (hm Limits.WalkingCospan.left)) x)
        (congrFun (congrArg Subtype.val (hm Limits.WalkingCospan.right)) x)
  exact Limits.preservesLimit_of_iso_diagram (wDissPow q) (Limits.diagramIsoCospan K).symm

/-- Lemma 6.5.17: acyclic morphisms of `wDiss` are stable under weighted pullback (for the
locally persistent structure `L` obtained by change of enrichment along `(1, 1)`).

**Change.** Specializes the locally bi-persistent structure from an arbitrary `LW` satisfying
`hLW` to `wDissLQPCat`, so that `exists_powered_of_changeOfEnrichment` applies. -/
theorem isStableUnderWeightedPullbacks_acyclicWDiss
    (L : LPCat WDiss.{u}) (hL : IsChangeOfEnrichment (pairFamily (1, 1)) wDissLQPCat L) :
    @IsStableUnderWeightedPullbacks WDiss _ L acyclicWDiss := by
  letI := L
  haveI : Limits.HasPullbacks WDiss.{u} := wDiss_hasPullbacks
  obtain ⟨P, hP⟩ := exists_powered_of_changeOfEnrichment (pairFamily (1, 1))
    (pairFamily_additive (1, 1)) wDissLQPCat wDissQPowered L hL
  letI : PoweredByRepresentables WDiss.{u} := P
  have hpres : ∀ ε, Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (PoweredByRepresentables.pow (C := WDiss.{u}) ε) := by
    intro ε
    rw [hP ε]
    exact wDissPow_preservesPullbacks _
  haveI : acyclicWDiss.{u}.IsStableUnderBaseChange := by
    refine ⟨fun {X Y P Z} {f g f' g'} hsq hg => ?_⟩
    let P' : WDiss.{u} :=
      { carrier := {p : X.carrier × Y.carrier // f.1 p.1 = g.1 p.2}
        d := fun p q => max (X.d p.1.1 q.1.1) (Y.d p.1.2 q.1.2)
        M := fun p r => min (X.M p.1.1 r) (Y.M p.1.2 r)
        mono := fun p a b h => min_le_min (X.mono _ h) (Y.mono _ h) }
    let pX : P' ⟶ X := ⟨fun p => p.1.1, by constructor <;> intros <;> simp [P']⟩
    let pY : P' ⟶ Y := ⟨fun p => p.1.2, by constructor <;> intros <;> simp [P']⟩
    let c' : Limits.PullbackCone g f := Limits.PullbackCone.mk pY pX (by
      apply Subtype.ext; funext p; exact p.2.symm)
    have hc' : Limits.IsLimit c' := Limits.PullbackCone.isLimitAux' c' fun s => by
      let l : s.pt ⟶ P' := ⟨fun x => ⟨(s.snd.1 x, s.fst.1 x),
        (congrFun (congrArg Subtype.val s.condition) x).symm⟩, by
        constructor
        · intro x y; simpa [P'] using max_le (s.snd.2.1 x y) (s.fst.2.1 x y)
        · intro x r; simpa [P'] using le_min (s.snd.2.2 x r) (s.fst.2.2 x r)⟩
      refine ⟨l, rfl, rfl, fun {m} hmY hmX => ?_⟩
      apply Subtype.ext; funext x; apply Subtype.ext
      exact Prod.ext (congrFun (congrArg Subtype.val hmX) x)
        (congrFun (congrArg Subtype.val hmY) x)
    let iso : P ≅ P' := hsq.isLimit.conePointUniqueUpToIso hc'
    have hcomp : iso.hom ≫ pX = g' :=
      hsq.isLimit.conePointUniqueUpToIso_hom_comp hc' Limits.WalkingCospan.right
    have hiso : acyclicWDiss iso.hom := by
      refine ⟨fun p' => ⟨iso.inv.1 p', congrFun (congrArg Subtype.val iso.inv_hom_id) p'⟩,
        fun p q => le_antisymm ?_ ?_, fun p r => le_antisymm ?_ ?_⟩
      · simpa using iso.hom.2.1 p q
      · have h1 := iso.inv.2.1 (iso.hom.1 p) (iso.hom.1 q)
        simp only [ENNReal.coe_zero, add_zero] at h1
        have hp : iso.inv.1 (iso.hom.1 p) = p := congrFun (congrArg Subtype.val iso.hom_inv_id) p
        have hq : iso.inv.1 (iso.hom.1 q) = q := congrFun (congrArg Subtype.val iso.hom_inv_id) q
        rwa [hp, hq] at h1
      · simpa using iso.hom.2.2 p r
      · have h2 := iso.inv.2.2 (iso.hom.1 p) r
        simp only [add_zero] at h2
        have hp : iso.inv.1 (iso.hom.1 p) = p := congrFun (congrArg Subtype.val iso.hom_inv_id) p
        rwa [hp] at h2
    have hpX : acyclicWDiss pX := by
      refine ⟨fun x => ?_, fun p q => ?_, fun p r => ?_⟩
      · obtain ⟨y, hy⟩ := hg.1 (f.1 x)
        exact ⟨⟨(x, y), hy.symm⟩, rfl⟩
      · dsimp [P', pX]
        have hle : Y.d p.1.2 q.1.2 ≤ X.d p.1.1 q.1.1 := by
          rw [← hg.2.1 p.1.2 q.1.2, ← p.2, ← q.2]
          simpa using f.2.1 p.1.1 q.1.1
        exact (max_eq_left hle).symm
      · dsimp [P', pX]
        have hle : X.M p.1.1 r ≤ Y.M p.1.2 r := by
          rw [hg.2.2 p.1.2 r, ← p.2]
          simpa using f.2.2 p.1.1 r
        exact min_eq_left hle
    rw [← hcomp]
    exact ⟨hpX.1.comp hiso.1, fun a b => by
      change X.d (pX.1 (iso.hom.1 a)) (pX.1 (iso.hom.1 b)) = P.d a b
      rw [hpX.2.1, hiso.2.1],
      fun a r => by
      change P.M a r = X.M (pX.1 (iso.hom.1 a)) r
      rw [hiso.2.2, hpX.2.2]⟩
  refine @isStableUnderWeightedPullbacks_of_powered WDiss.{u} _ L acyclicWDiss.{u} P _
    hpres _ (fun ε a b f hf => ?_)
  rw [hP ε]
  refine ⟨hf.1, fun y y' => ?_, fun y s => ?_⟩
  · dsimp [wDissQPowered, wDissPow]
    rw [hf.2.1 y y']
  · dsimp [wDissQPowered, wDissPow]
    rw [hf.2.2 y (s + ((pairFamily (1, 1)).toFun ε).1)]

/-- Definition 6.5.18: `Y` is bounded with constant `B`. -/
def WDiss.IsBoundedBy (Y : WDiss.{u}) (B : ℝ≥0) : Prop := ∀ y r, Y.M y r ≤ B

/-- The full subcategory `wDiss_B` of weighted dissimilarity spaces bounded by `B`. -/
def WDissBounded (B : ℝ≥0) : Type (u + 1) := {Y : WDiss.{u} // Y.IsBoundedBy B}

/-- The local density estimate `(M_X * K_s)(x) = ∫₀^∞ M_X (x, s K⁻¹ (t)) dt`
(Lemma 6.5.8). -/
noncomputable def WDiss.density (X : WDiss.{u}) (K : Kernel) (s : ℝ) (x : X.carrier) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), (X.M x (s.toNNReal * K.inv t.toNNReal) : ℝ≥0∞)

/-- The object `X[s,k]` of the kernel density filtration, as a dissimilarity space. -/
noncomputable def WDiss.kdfObj (X : WDiss.{u}) (K : Kernel) (s k : ℝ) : Diss.{u} :=
  ⟨{x : X.carrier // k ≤ 0 ∨ (0 < s ∧ ENNReal.ofReal k ≤ X.density K s x)},
    fun a b => X.d a.1 b.1⟩

theorem WDiss.density_mono (X : WDiss.{u}) (K : Kernel) {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) (x : X.carrier) :
    X.density K s₁ x ≤ X.density K s₂ x := by
  dsimp [WDiss.density]
  apply lintegral_mono
  intro t
  apply ENNReal.coe_le_coe.2
  apply X.mono x
  gcongr

/-- The kernel density filtration as a functor `ℝ × ℝᵒᵖ ⥤ Diss`. -/
noncomputable def kdfFunctor (K : Kernel) (X : WDiss.{u}) : ℝ × ℝᵒᵖ ⥤ Diss.{u} where
  obj sk := X.kdfObj K sk.1 sk.2.unop
  map {sk₁ sk₂} f :=
    ⟨fun p => ⟨p.1, by
      obtain ⟨hs, hk⟩ := f
      have hs_le : sk₁.1 ≤ sk₂.1 := leOfHom hs
      have hk_le : sk₂.2.unop ≤ sk₁.2.unop := leOfHom hk.unop
      by_cases h : sk₂.2.unop ≤ 0
      · exact Or.inl h
      · have hk1_pos : 0 < sk₁.2.unop := lt_of_lt_of_le (not_le.mp h) hk_le
        have hp2 : 0 < sk₁.1 ∧ ENNReal.ofReal sk₁.2.unop ≤ X.density K sk₁.1 p.1 := by
          cases p.2 with
          | inl hle => exact False.elim ((not_le.mpr hk1_pos) hle)
          | inr hpos => exact hpos
        refine Or.inr ⟨hp2.1.trans_le hs_le, ?_⟩
        exact (ENNReal.ofReal_le_ofReal hk_le).trans
          (hp2.2.trans (WDiss.density_mono X K hs_le p.1))⟩,
     fun a b => le_rfl⟩
  map_id := by
    intro sk
    apply Subtype.ext
    funext p
    apply Subtype.ext
    rfl
  map_comp := by
    intro sk₁ sk₂ sk₃ f g
    apply Subtype.ext
    funext p
    apply Subtype.ext
    rfl

/-- Lemma 6.5.21: the kernel density filtration is a functor `wDiss_B → Diss^{ℝ × ℝᵒᵖ}`
sending acyclic morphisms to (levelwise) acyclic morphisms. -/
theorem exists_kdf_functor (K : Kernel) (B : ℝ≥0) :
    ∃ F : WDissBounded.{u} B → (ℝ × ℝᵒᵖ ⥤ Diss.{u}),
      (∀ X s k, ((F X).obj (s, Opposite.op k)) = (X.1.kdfObj K s k)) :=
  ⟨fun X => kdfFunctor K X.1, fun _ _ _ => rfl⟩

/-- Objectwise acyclic natural transformations of diagrams `J ⥤ Diss`. -/
def levelwiseProp' {J : Type} [Category J] (W : MorphismProperty Diss.{u}) :
    MorphismProperty (J ⥤ Diss.{u}) := fun _ _ α => ∀ j, W (α.app j)

/-- Theorem 6.5.22: the kernel density filtration is uniformly continuous for the quotient
interleaving distance on `wDiss_B` and the Gromov–Hausdorff-interleaving distance on
`Diss^{ℝ × ℝᵒᵖ}_v` (with locally persistent structure `LD`); for the uniform kernel it is
1-Lipschitz. -/
theorem kdf_uniformContinuous (K : Kernel) (B : ℝ≥0) [LPCat WDiss.{u}]
    [LPCat (ℝ × ℝᵒᵖ ⥤ Diss.{u})]
    (F : WDissBounded.{u} B → (ℝ × ℝᵒᵖ ⥤ Diss.{u}))
    (hF : ∀ X s k, ((F X).obj (s, Opposite.op k)) = (X.1.kdfObj K s k)) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ X Y : WDissBounded.{u} B,
      quotientInterleavingDist acyclicWDiss X.1 Y.1 < δ →
        quotientInterleavingDist (levelwiseProp' (J := ℝ × ℝᵒᵖ) acyclicDiss) (F X) (F Y) ≤ ε := by
  sorry

/-- Theorem 6.5.23: for compact metric probability spaces,
`(d_I^{wDiss_{(1,1)}})/≃ (X, Y) ≤ 2 d_GHP (X, Y)`.

**Change.** Specializes `LW` to `wDissLQPCat` (as in `isStableUnderWeightedPullbacks_acyclicWDiss`)
so `IsChangeOfEnrichment` determines composition and units. -/
theorem quotientInterleavingDist_wDiss_le_ghp (L : LPCat WDiss.{u})
    (hL : IsChangeOfEnrichment (pairFamily (1, 1)) wDissLQPCat L)
    (X Y : CompactMPS.{u}) :
    @quotientInterleavingDist WDiss _ L acyclicWDiss X.toWDiss Y.toWDiss ≤ 2 * ghpDist X Y := by
  letI := L
  rw [quotientInterleavingDist_eq_inf_acyclicCover (isStableUnderWeightedPullbacks_acyclicWDiss L hL)]
  rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  unfold ghpDist
  refine le_iInf fun Z => le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
    le_iInf fun i => le_iInf fun j => le_iInf fun hi => le_iInf fun hj => ?_
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_comm]
  set M := max (Metric.hausdorffEDist (Set.range i) (Set.range j))
    (levyProkhorovEDist (X.μ.map i) (Y.μ.map j))
  by_cases hM : M = ⊤
  · rw [hM, ENNReal.mul_top (by norm_num)]; exact le_top
  have hInf : 2 * M = ⨅ (ε : ℝ≥0) (_ : M < ε), (2 * ε : ℝ≥0∞) := by
    apply le_antisymm
    · exact le_iInf₂ fun ε hε => by gcongr
    · rw [← ENNReal.coe_toNNReal hM]
      refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
      have hδ : (2 : ℝ≥0∞) * (↑M.toNNReal + ↑(η / 3)) ≤ 2 * ↑M.toNNReal + ↑η := by
        norm_cast; linarith
      refine iInf₂_le_of_le (M.toNNReal + η / 3) (by
        rw [← ENNReal.coe_toNNReal hM, ENNReal.coe_lt_coe]
        exact lt_add_of_pos_right _ (by positivity)) hδ
  rw [hInf]
  refine le_iInf₂ fun ε hε => ?_
  have hH : Metric.hausdorffEDist (Set.range i) (Set.range j) < ε :=
    lt_of_le_of_lt (le_max_left _ _) hε
  have hP : levyProkhorovEDist (X.μ.map i) (Y.μ.map j) < ε :=
    lt_of_le_of_lt (le_max_right _ _) hε
  let R : Set (X.carrier × Y.carrier) := {p | edist (i p.1) (j p.2) < ε}
  let R_X : WDiss.{u} :=
    { carrier := R
      d := fun p q => edist p.1.1 q.1.1
      M := fun p r => (X.μ (Metric.ball p.1.1 r)).toNNReal
      mono := fun p a b h => ENNReal.toNNReal_mono (measure_ne_top _ _)
        (measure_mono (Metric.ball_subset_ball h)) }
  let R_Y : WDiss.{u} :=
    { carrier := R
      d := fun p q => edist p.1.2 q.1.2
      M := fun p r => (Y.μ (Metric.ball p.1.2 r)).toNNReal
      mono := fun p a b h => ENNReal.toNNReal_mono (measure_ne_top _ _)
        (measure_mono (Metric.ball_subset_ball h)) }
  let a : R_X ⟶ X.toWDiss := ⟨fun p => p.1.1, by constructor <;> intros <;> simp [R_X, CompactMPS.toWDiss]⟩
  let b : R_Y ⟶ Y.toWDiss := ⟨fun p => p.1.2, by constructor <;> intros <;> simp [R_Y, CompactMPS.toWDiss]⟩
  have ha : acyclicWDiss a := by
    refine ⟨fun x => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    obtain ⟨z, ⟨y, rfl⟩, hz⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt (Set.mem_range_self x) hH
    exact ⟨⟨(x, y), hz⟩, rfl⟩
  have hb : acyclicWDiss b := by
    refine ⟨fun y => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    have hH' : Metric.hausdorffEDist (Set.range j) (Set.range i) < ε := by
      rwa [Metric.hausdorffEDist_comm]
    obtain ⟨z, ⟨x, rfl⟩, hz⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt (Set.mem_range_self y) hH'
    exact ⟨⟨(x, y), by change edist (i x) (j y) < ε; rwa [edist_comm]⟩, rfl⟩
  have hI : @IsInterleaved WDiss _ L R_X R_Y (2 * ε) := by
    obtain ⟨e, he0, hecomp, heS⟩ := hL
    have hpair : (pairFamily (1, 1)).toFun (2 * ε) = (2 * ε, 2 * ε) := by
      simp [pairFamily]
    let hφ_w : WDissHom R_X R_Y (2 * ε) (2 * ε) := ⟨id, by
      constructor
      · intro p q
        calc edist p.1.2 q.1.2
            = edist (j p.1.2) (j q.1.2) := (hj.edist_eq _ _).symm
          _ ≤ edist (j p.1.2) (i p.1.1) + edist (i p.1.1) (i q.1.1) + edist (i q.1.1) (j q.1.2) :=
              edist_triangle4 _ _ _ _
          _ ≤ ε + edist p.1.1 q.1.1 + ε := by
              refine add_le_add (add_le_add ?_ (hi.edist_eq _ _).le) q.2.le
              rw [edist_comm]; exact p.2.le
          _ = edist p.1.1 q.1.1 + ((2 * ε : ℝ≥0) : ℝ≥0∞) := by
              push_cast; ring
      · intro p r
        by_cases hr : (r : ℝ) ≤ 0
        · have hr0 : r = 0 := NNReal.eq (le_antisymm hr r.coe_nonneg)
          simp [R_X, hr0]
        · have hr_pos : 0 < (r : ℝ) := lt_of_not_ge hr
          have hball_mble : MeasurableSet (Metric.ball (i p.1.1) (r : ℝ)) :=
            Metric.isOpen_ball.measurableSet
          have hpre_i : i ⁻¹' Metric.ball (i p.1.1) (r : ℝ) = Metric.ball p.1.1 (r : ℝ) := by
            ext x; simp [Metric.mem_ball, hi.dist_eq]
          have hpre_j : j ⁻¹' Metric.ball (j p.1.2) ((r + 2 * ε : ℝ≥0) : ℝ) =
              Metric.ball p.1.2 ((r + 2 * ε : ℝ≥0) : ℝ) := by
            ext y; simp [Metric.mem_ball, hj.dist_eq]
          have hmap_i : X.μ (Metric.ball p.1.1 (r : ℝ)) =
              (X.μ.map i) (Metric.ball (i p.1.1) (r : ℝ)) := by
            rw [Measure.map_apply hi.continuous.measurable hball_mble, hpre_i]
          have hmap_j : Y.μ (Metric.ball p.1.2 ((r + 2 * ε : ℝ≥0) : ℝ)) =
              (Y.μ.map j) (Metric.ball (j p.1.2) ((r + 2 * ε : ℝ≥0) : ℝ)) := by
            rw [Measure.map_apply hj.continuous.measurable Metric.isOpen_ball.measurableSet, hpre_j]
          have hsub : Metric.thickening (ε : ℝ≥0∞).toReal (Metric.ball (i p.1.1) (r : ℝ)) ⊆
              Metric.ball (j p.1.2) ((r + 2 * ε : ℝ≥0) : ℝ) := by
            intro z hz
            obtain ⟨w, hw_ball, hw_dist⟩ :=
              (Metric.mem_thickening_iff_exists_edist_lt _ _).mp hz
            have hw_lt : edist z w < ε := by
              simpa [ENNReal.coe_toReal] using hw_dist
            have hball_lt : edist w (i p.1.1) < r := by
              rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hr_pos]
              exact hw_ball
            have htri : edist z (j p.1.2) < ((r + 2 * ε : ℝ≥0) : ℝ≥0∞) := by
              calc edist z (j p.1.2)
                  ≤ edist z w + edist w (i p.1.1) + edist (i p.1.1) (j p.1.2) :=
                    edist_triangle4 _ _ _ _
                _ < ε + r + ε := ENNReal.add_lt_add (ENNReal.add_lt_add hw_lt hball_lt) p.2
                _ = ((r + 2 * ε : ℝ≥0) : ℝ≥0∞) := by
                    push_cast; ring
            rw [Metric.mem_ball, dist_edist]
            exact ENNReal.toReal_lt_of_lt_ofReal (by rw [ENNReal.ofReal_coe_nnreal]; exact htri)
          have hmeas : X.μ (Metric.ball p.1.1 (r : ℝ)) ≤
              Y.μ (Metric.ball p.1.2 ((r + 2 * ε : ℝ≥0) : ℝ)) + ((2 * ε : ℝ≥0) : ℝ≥0∞) := by
            rw [hmap_i, hmap_j]
            refine (left_measure_le_of_levyProkhorovEDist_lt hP hball_mble).trans ?_
            exact add_le_add (measure_mono hsub) (ENNReal.coe_le_coe.mpr (by
              rw [two_mul]; exact le_self_add))
          have hnn := ENNReal.toNNReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.coe_ne_top⟩) hmeas
          rw [ENNReal.toNNReal_add (measure_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe] at hnn
          exact hnn⟩
    let hψ_w : WDissHom R_Y R_X (2 * ε) (2 * ε) := ⟨id, by
      constructor
      · intro p q
        calc edist p.1.1 q.1.1
            = edist (i p.1.1) (i q.1.1) := (hi.edist_eq _ _).symm
          _ ≤ edist (i p.1.1) (j p.1.2) + edist (j p.1.2) (j q.1.2) + edist (j q.1.2) (i q.1.1) :=
              edist_triangle4 _ _ _ _
          _ ≤ ε + edist p.1.2 q.1.2 + ε := by
              refine add_le_add (add_le_add p.2.le (hj.edist_eq _ _).le) ?_
              rw [edist_comm]; exact q.2.le
          _ = edist p.1.2 q.1.2 + ((2 * ε : ℝ≥0) : ℝ≥0∞) := by
              push_cast; ring
      · intro p r
        by_cases hr : (r : ℝ) ≤ 0
        · have hr0 : r = 0 := NNReal.eq (le_antisymm hr r.coe_nonneg)
          simp [R_Y, hr0]
        · have hr_pos : 0 < (r : ℝ) := lt_of_not_ge hr
          have hball_mble : MeasurableSet (Metric.ball (j p.1.2) (r : ℝ)) :=
            Metric.isOpen_ball.measurableSet
          have hpre_j : j ⁻¹' Metric.ball (j p.1.2) (r : ℝ) = Metric.ball p.1.2 (r : ℝ) := by
            ext y; simp [Metric.mem_ball, hj.dist_eq]
          have hpre_i : i ⁻¹' Metric.ball (i p.1.1) ((r + 2 * ε : ℝ≥0) : ℝ) =
              Metric.ball p.1.1 ((r + 2 * ε : ℝ≥0) : ℝ) := by
            ext x; simp [Metric.mem_ball, hi.dist_eq]
          have hmap_j : Y.μ (Metric.ball p.1.2 (r : ℝ)) =
              (Y.μ.map j) (Metric.ball (j p.1.2) (r : ℝ)) := by
            rw [Measure.map_apply hj.continuous.measurable hball_mble, hpre_j]
          have hmap_i : X.μ (Metric.ball p.1.1 ((r + 2 * ε : ℝ≥0) : ℝ)) =
              (X.μ.map i) (Metric.ball (i p.1.1) ((r + 2 * ε : ℝ≥0) : ℝ)) := by
            rw [Measure.map_apply hi.continuous.measurable Metric.isOpen_ball.measurableSet, hpre_i]
          have hsub : Metric.thickening (ε : ℝ≥0∞).toReal (Metric.ball (j p.1.2) (r : ℝ)) ⊆
              Metric.ball (i p.1.1) ((r + 2 * ε : ℝ≥0) : ℝ) := by
            intro z hz
            obtain ⟨w, hw_ball, hw_dist⟩ :=
              (Metric.mem_thickening_iff_exists_edist_lt _ _).mp hz
            have hw_lt : edist z w < ε := by
              simpa [ENNReal.coe_toReal] using hw_dist
            have hball_lt : edist w (j p.1.2) < r := by
              rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hr_pos]
              exact hw_ball
            have htri : edist z (i p.1.1) < ((r + 2 * ε : ℝ≥0) : ℝ≥0∞) := by
              calc edist z (i p.1.1)
                  ≤ edist z w + edist w (j p.1.2) + edist (j p.1.2) (i p.1.1) :=
                    edist_triangle4 _ _ _ _
                _ < ε + r + ε := ENNReal.add_lt_add (ENNReal.add_lt_add hw_lt hball_lt)
                    (by rw [edist_comm]; exact p.2)
                _ = ((r + 2 * ε : ℝ≥0) : ℝ≥0∞) := by
                    push_cast; ring
            rw [Metric.mem_ball, dist_edist]
            exact ENNReal.toReal_lt_of_lt_ofReal (by rw [ENNReal.ofReal_coe_nnreal]; exact htri)
          have hmeas : Y.μ (Metric.ball p.1.2 (r : ℝ)) ≤
              X.μ (Metric.ball p.1.1 ((r + 2 * ε : ℝ≥0) : ℝ)) + ((2 * ε : ℝ≥0) : ℝ≥0∞) := by
            rw [hmap_j, hmap_i]
            refine (right_measure_le_of_levyProkhorovEDist_lt hP hball_mble).trans ?_
            exact add_le_add (measure_mono hsub) (ENNReal.coe_le_coe.mpr (by
              rw [two_mul]; exact le_self_add))
          have hnn := ENNReal.toNNReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.coe_ne_top⟩) hmeas
          rw [ENNReal.toNNReal_add (measure_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe] at hnn
          exact hnn⟩
    have hcast_id : ∀ (q : ℝ≥0 × ℝ≥0) (hq : (2 * ε, 2 * ε) = q) (a b : WDiss.{u})
        (f : WDissHom a b (2 * ε) (2 * ε)) (g : a.carrier → b.carrier) (hf : f.1 = g),
        (cast (congrArg (fun p : ℝ≥0 × ℝ≥0 => WDissHom a b p.1 p.2) hq) f).1 = g := by
      rintro _ rfl _ _ f g hf; exact hf
    have hcomp_val : ∀ {a b c : WDiss.{u}} {q₁ q₂ : ℝ≥0 × ℝ≥0}
        (g : wDissLQPCat.hom b c q₂) (f : wDissLQPCat.hom a b q₁),
        (wDissLQPCat.comp g f).1 = g.1 ∘ f.1 := fun _ _ => rfl
    have hS_val : ∀ {a b : WDiss.{u}} {q₁ q₂ : ℝ≥0 × ℝ≥0} (h : q₁ ≤ q₂)
        (f : wDissLQPCat.hom a b q₁), (wDissLQPCat.S h f).1 = f.1 := fun _ _ => rfl
    let φ_q : wDissLQPCat.hom R_X R_Y ((pairFamily (1, 1)).toFun (2 * ε)) :=
      cast (congrArg (fun q => WDissHom R_X R_Y q.1 q.2) hpair.symm) hφ_w
    let ψ_q : wDissLQPCat.hom R_Y R_X ((pairFamily (1, 1)).toFun (2 * ε)) :=
      cast (congrArg (fun q => WDissHom R_Y R_X q.1 q.2) hpair.symm) hψ_w
    let φ : L.hom R_X R_Y (2 * ε) := cast (e R_X R_Y (2 * ε)).symm φ_q
    let ψ : L.hom R_Y R_X (2 * ε) := cast (e R_Y R_X (2 * ε)).symm ψ_q
    refine ⟨⟨φ, ψ, ?_, ?_⟩⟩
    · apply (Equiv.cast (e R_X R_X (2 * ε + 2 * ε))).injective
      simp only [Equiv.cast_apply, φ, ψ]
      rw [hecomp]
      have h_lhs : (wDissLQPCat.S ((pairFamily (1, 1)).superadd (2 * ε) (2 * ε))
          (wDissLQPCat.comp (cast (e R_Y R_X (2 * ε)) (cast (e R_Y R_X (2 * ε)).symm ψ_q))
            (cast (e R_X R_Y (2 * ε)) (cast (e R_X R_Y (2 * ε)).symm φ_q)))).1 = id := by
        rw [cast_cast, cast_eq, cast_cast, cast_eq, hS_val, hcomp_val]
        have h1 : ψ_q.1 = id := hcast_id _ hpair.symm R_Y R_X hψ_w id rfl
        have h2 : φ_q.1 = id := hcast_id _ hpair.symm R_X R_Y hφ_w id rfl
        rw [h1, h2]
        rfl
      have h_rhs : (cast (e R_X R_X (2 * ε + 2 * ε))
          (L.S (bot_le : (0 : ℝ≥0) ≤ 2 * ε + 2 * ε) (L.homZero (𝟙 R_X)))).1 = id := by
        rw [heS R_X R_X 0 (2 * ε + 2 * ε) bot_le (L.homZero (𝟙 R_X)), he0]
        rfl
      exact Subtype.ext (h_lhs.trans h_rhs.symm)
    · apply (Equiv.cast (e R_Y R_Y (2 * ε + 2 * ε))).injective
      simp only [Equiv.cast_apply, φ, ψ]
      rw [hecomp]
      have h_lhs : (wDissLQPCat.S ((pairFamily (1, 1)).superadd (2 * ε) (2 * ε))
          (wDissLQPCat.comp (cast (e R_X R_Y (2 * ε)) (cast (e R_X R_Y (2 * ε)).symm φ_q))
            (cast (e R_Y R_X (2 * ε)) (cast (e R_Y R_X (2 * ε)).symm ψ_q)))).1 = id := by
        rw [cast_cast, cast_eq, cast_cast, cast_eq, hS_val, hcomp_val]
        have h1 : φ_q.1 = id := hcast_id _ hpair.symm R_X R_Y hφ_w id rfl
        have h2 : ψ_q.1 = id := hcast_id _ hpair.symm R_Y R_X hψ_w id rfl
        rw [h1, h2]
        rfl
      have h_rhs : (cast (e R_Y R_Y (2 * ε + 2 * ε))
          (L.S (bot_le : (0 : ℝ≥0) ≤ 2 * ε + 2 * ε) (L.homZero (𝟙 R_Y)))).1 = id := by
        rw [heS R_Y R_Y 0 (2 * ε + 2 * ε) bot_le (L.homZero (𝟙 R_Y)), he0]
        rfl
      exact Subtype.ext (h_lhs.trans h_rhs.symm)
  refine iInf₂_le_of_le (2 * ε) ⟨R_X, R_Y, a, b, ha, hb, hI⟩ ?_
  push_cast; exact le_rfl

end KernelDensity

/-! ## Chapter 6.6: The correspondence-interleaving distance on hierarchical clusterings

Clusterings, hierarchical clusterings (with a sign vector `v ∈ {−1, 1}ⁿ`, encoded as
`v : Fin n → Bool` with `true` meaning covariant) and the correspondence-interleaving distance
are defined concretely.  The category `hCl_v` of hierarchical clusterings has a concrete
category structure (its `0`-morphisms); its locally persistent structure is stated to exist.

Omitted from 6.6.3: the comparison with the Carlsson–Mémoli distance on dendrograms and with
the merge distortion metric of [EBW15] (merge functions, cluster trees).

Density-clustering stability and the acyclic-morphism laws are proved. The structural
lemma, completeness and the correspondence-distance comparison remain open. -/

section Clustering

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

open LPCat

/-- Definition 6.6.1: a clustering of `X` is a set of non-empty disjoint subsets. -/
structure Clustering (X : Type u) where
  clusters : Set (Set X)
  nonempty : ∀ A ∈ clusters, A.Nonempty
  disjoint : ∀ A ∈ clusters, ∀ B ∈ clusters, A ≠ B → Disjoint A B

/-- Definition 6.6.2: `S ≼ T` if every cluster of `S` lies inside a cluster of `T`. -/
instance {X : Type u} : LE (Clustering X) := ⟨fun S T => ∀ A ∈ S.clusters, ∃ B ∈ T.clusters, A ⊆ B⟩

/-- The positive part `ℝⁿ_{>0}` of `ℝⁿ`. -/
def PosRn (n : ℕ) : Type := {r : Fin n → ℝ // ∀ i, 0 < r i}

/-- Definition 6.6.6: the order on `ℝ^v_{>0}`: covariant (`v i = true`) or contravariant
coordinates. -/
def vLE {n : ℕ} (v : Fin n → Bool) (r r' : PosRn n) : Prop :=
  ∀ i, if v i then r.1 i ≤ r'.1 i else r'.1 i ≤ r.1 i

/-- Definition 6.6.7: a `v`-hierarchical clustering of `X`. -/
structure HierClustering {n : ℕ} (v : Fin n → Bool) (X : Type u) where
  H : PosRn n → Clustering X
  mono : ∀ r r', vLE v r r' → H r ≤ H r'

/-- Notation 6.6.8: `r' = r + v ε`. -/
def IsShift {n : ℕ} (v : Fin n → Bool) (ε : Fin n → ℝ≥0) (r r' : PosRn n) : Prop :=
  ∀ i, r'.1 i = r.1 i + if v i then (ε i : ℝ) else -(ε i : ℝ)

/-- Definition 6.6.9: `H` and `E` are `ε`-interleaved. -/
def HierClustering.IsInterleaved {n : ℕ} {v : Fin n → Bool} {X : Type u}
    (H E : HierClustering v X) (ε : Fin n → ℝ≥0) : Prop :=
  ∀ r r' : PosRn n, IsShift v ε r r' → H.H r ≤ E.H r' ∧ E.H r ≤ H.H r'

/-- Definition 6.6.11: `H` and `E` are `ε`-interleaved with respect to the relation `R`, i.e.
`π_X^* H` and `π_Y^* E` are `ε`-interleaved clusterings of `R`. -/
def HierClustering.IsInterleavedWrt {n : ℕ} {v : Fin n → Bool} {X Y : Type u}
    (H : HierClustering v X) (E : HierClustering v Y) (R : Set (X × Y)) (ε : Fin n → ℝ≥0) :
    Prop :=
  ∀ r r' : PosRn n, IsShift v ε r r' →
    (∀ A ∈ (H.H r).clusters, (∃ p ∈ R, p.1 ∈ A) → ∃ B ∈ (E.H r').clusters, ∀ p ∈ R, p.1 ∈ A → p.2 ∈ B) ∧
    (∀ B ∈ (E.H r).clusters, (∃ p ∈ R, p.2 ∈ B) → ∃ A ∈ (H.H r').clusters, ∀ p ∈ R, p.2 ∈ B → p.1 ∈ A)

/-- Definition 6.6.12: the correspondence-interleaving distance. -/
noncomputable def corrInterleavingDist {n : ℕ} {v : Fin n → Bool} {X Y : Type u}
    (H : HierClustering v X) (E : HierClustering v Y) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (R : Set (X × Y)) (_ : (∀ x, ∃ y, (x, y) ∈ R) ∧ ∀ y, ∃ x, (x, y) ∈ R)
    (_ : H.IsInterleavedWrt E R (fun _ => ε)), (ε : ℝ≥0∞)

/-- Example 6.6.4: the contravariant hierarchical clustering of a density `f` whose clusters at
level `r` are the connected components of `{f ≥ r}`. -/
def densityClustering {E : Type u} [TopologicalSpace E] (f : E → ℝ≥0) : HierClustering (n := 1)
    (fun _ => false) E where
  H r := ⟨{A | ∃ x, (r.1 0 : ℝ).toNNReal ≤ f x ∧
      A = connectedComponentIn {y | (r.1 0 : ℝ).toNNReal ≤ f y} x},
    by
      rintro A ⟨x, hx, rfl⟩
      exact connectedComponentIn_nonempty_iff.mpr hx,
    by
      rintro A ⟨x, hx, rfl⟩ B ⟨y, hy, rfl⟩ hne
      by_contra h
      obtain ⟨z, hz1, hz2⟩ := Set.not_disjoint_iff.1 h
      exact hne ((connectedComponentIn_eq hz1).trans (connectedComponentIn_eq hz2).symm)⟩
  mono := by
    intro r r' hr A hA
    obtain ⟨x, hx, rfl⟩ := hA
    have hr0 : r'.1 0 ≤ r.1 0 := by
      have := hr 0
      dsimp [vLE] at this
      exact this
    have hsub : {y | (r.1 0 : ℝ).toNNReal ≤ f y} ⊆ {y | (r'.1 0 : ℝ).toNNReal ≤ f y} := by
      intro y hy
      dsimp at hy ⊢
      exact (Real.toNNReal_le_toNNReal hr0).trans hy
    have hx' : (r'.1 0 : ℝ).toNNReal ≤ f x := hsub hx
    refine ⟨connectedComponentIn {y | (r'.1 0 : ℝ).toNNReal ≤ f y} x, ⟨x, hx', rfl⟩, ?_⟩
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx)
      ((connectedComponentIn_subset _ _).trans hsub)

/-- Proposition 6.6.10: if `‖f - g‖_∞ < ε`, the density clusterings are `ε`-interleaved. -/
theorem densityClustering_interleaved {E : Type u} [TopologicalSpace E] (f g : E → ℝ≥0)
    (ε : ℝ≥0) (h : ∀ x, ((f x - g x) ⊔ (g x - f x)) < ε) :
    (densityClustering f).IsInterleaved (densityClustering g) (fun _ => ε) := by
  have hfg : ∀ x, f x - g x ≤ ε := fun x => (le_sup_left.trans_lt (h x)).le
  have hgf : ∀ x, g x - f x ≤ ε := fun x => (le_sup_right.trans_lt (h x)).le
  have hstep : ∀ (f₁ f₂ : E → ℝ≥0) (h₁₂ : ∀ x, f₁ x - f₂ x ≤ ε) (r r' : PosRn 1)
      (hshift : IsShift (fun _ => false) (fun _ => ε) r r'),
      (densityClustering f₁).H r ≤ (densityClustering f₂).H r' := by
    intro f₁ f₂ h₁₂ r r' hshift A hA
    obtain ⟨x, hx, rfl⟩ := hA
    have hr' : r'.1 0 = r.1 0 - (ε : ℝ) := by
      have hs := hshift 0
      dsimp at hs
      linarith
    have hsub : {y | (r.1 0 : ℝ).toNNReal ≤ f₁ y} ⊆ {y | (r'.1 0 : ℝ).toNNReal ≤ f₂ y} := by
      intro y hy
      dsimp at hy ⊢
      have h1 : f₁ y ≤ f₂ y + ε := by rw [add_comm]; exact tsub_le_iff_right.mp (h₁₂ y)
      have h2 : r.1 0 ≤ (f₁ y : ℝ) := (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.2 hy)
      have h3 : r'.1 0 ≤ (f₂ y : ℝ) := by
        have h4 : (f₁ y : ℝ) ≤ (f₂ y : ℝ) + (ε : ℝ) := by
          exact_mod_cast h1
        linarith
      have h5 : (r'.1 0).toNNReal ≤ (f₂ y : ℝ).toNNReal :=
        (Real.toNNReal_le_toNNReal_iff (by positivity)).2 h3
      rwa [Real.toNNReal_coe] at h5
    have hx' : (r'.1 0 : ℝ).toNNReal ≤ f₂ x := hsub hx
    refine ⟨connectedComponentIn {y | (r'.1 0 : ℝ).toNNReal ≤ f₂ y} x, ⟨x, hx', rfl⟩, ?_⟩
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx)
      ((connectedComponentIn_subset _ _).trans hsub)
  intro r r' hshift
  exact ⟨hstep f g hfg r r' hshift, hstep g f hgf r r' hshift⟩

/-! ### 6.6.2 The locally persistent category of hierarchical clusterings -/

/-- Objects of `hCl_v`: a set with a `v`-hierarchical clustering. -/
structure HCl {n : ℕ} (v : Fin n → Bool) where
  carrier : Type u
  H : HierClustering v carrier

/-- `ε`-morphisms of `hCl_v`: maps `ψ` with `H_X(r) ≼ ψ^*(H_Y)(r + v ε)`. -/
def HClHom {n : ℕ} {v : Fin n → Bool} (X Y : HCl.{u} v) (ε : Fin n → ℝ≥0) : Type u :=
  {ψ : X.carrier → Y.carrier // ∀ r r' : PosRn n, IsShift v ε r r' →
    ∀ A ∈ (X.H.H r).clusters, ∃ B ∈ (Y.H.H r').clusters, ψ '' A ⊆ B}

/-- The underlying category of `hCl_v` has the `0`-morphisms. -/
instance {n : ℕ} (v : Fin n → Bool) : Category.{u} (HCl.{u} v) where
  Hom X Y := HClHom X Y (fun _ => 0)
  id X := ⟨id, by
    intro r r' hshift A hA
    have hr : r = r' := by
      apply Subtype.ext
      funext i
      have h := hshift i
      dsimp at h
      split_ifs at h <;> {
        simp only [add_zero, neg_zero] at h
        exact h.symm
      }
    subst hr
    refine ⟨A, hA, by simp⟩⟩
  comp f g := ⟨g.1 ∘ f.1, by
    intro r r' hshift A hA
    have hr : r = r' := by
      apply Subtype.ext
      funext i
      have h := hshift i
      dsimp at h
      split_ifs at h <;> {
        simp only [add_zero, neg_zero] at h
        exact h.symm
      }
    subst hr
    have hshift_id : IsShift v (fun _ => 0) r r := by
      intro i
      split_ifs <;> simp
    obtain ⟨B, hB, hAB⟩ := f.2 r r hshift_id A hA
    obtain ⟨C, hC, hBC⟩ := g.2 r r hshift_id B hB
    refine ⟨C, hC, ?_⟩
    rw [Set.image_comp]
    exact (Set.image_mono hAB).trans hBC⟩
  id_comp _ := Subtype.ext rfl
  comp_id _ := Subtype.ext rfl
  assoc _ _ _ := Subtype.ext rfl

/-- The locally persistent structure on `hCl_v` (change of enrichment along `δ ↦ (δ, …, δ)`):
`Hom(X, Y)_δ = HClHom X Y (δ, …, δ)`. -/
theorem exists_hCl_lpcat {n : ℕ} (v : Fin n → Bool) :
    ∃ L : LPCat (HCl.{u} v), ∀ (X Y : HCl.{u} v) (δ : ℝ≥0), L.hom X Y δ = HClHom X Y (fun _ => δ) := by
  let comp_hom : ∀ {X Y Z : HCl.{u} v} {ε δ : ℝ≥0},
      HClHom Y Z (fun _ => δ) → HClHom X Y (fun _ => ε) → HClHom X Z (fun _ => ε + δ) :=
    fun {X Y Z ε δ} g f => ⟨g.1 ∘ f.1, fun r r'' hshift A hA => by
      have hr'_pos : ∀ i, 0 < r.1 i + if v i then (ε : ℝ) else -(ε : ℝ) := by
        intro i
        have hs := hshift i
        dsimp at hs
        split_ifs at hs ⊢ with hvi
        · have : 0 ≤ (ε : ℝ) := NNReal.coe_nonneg ε
          linarith [r.2 i]
        · have h2 : 0 < r''.1 i := r''.2 i
          have hδ : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg δ
          linarith
      let r' : PosRn n := ⟨fun i => r.1 i + if v i then (ε : ℝ) else -(ε : ℝ), hr'_pos⟩
      have hshift1 : IsShift v (fun _ => ε) r r' := fun _ => rfl
      have hshift2 : IsShift v (fun _ => δ) r' r'' := by
        intro i
        have hs := hshift i
        dsimp [r'] at hs ⊢
        split_ifs at hs ⊢ with hvi
        · linarith
        · linarith
      obtain ⟨B, hB, hAB⟩ := f.2 r r' hshift1 A hA
      obtain ⟨C, hC, hBC⟩ := g.2 r' r'' hshift2 B hB
      refine ⟨C, hC, ?_⟩
      rw [Set.image_comp]
      exact (Set.image_mono hAB).trans hBC⟩
  let S_hom : ∀ {X Y : HCl.{u} v} {ε δ : ℝ≥0},
      ε ≤ δ → HClHom X Y (fun _ => ε) → HClHom X Y (fun _ => δ) :=
    fun {X Y ε δ} hle f => ⟨f.1, fun r r'' hshift A hA => by
      have hr'_pos : ∀ i, 0 < r.1 i + if v i then (ε : ℝ) else -(ε : ℝ) := by
        intro i
        have hs := hshift i
        dsimp at hs
        split_ifs at hs ⊢ with hvi
        · have : 0 ≤ (ε : ℝ) := NNReal.coe_nonneg ε
          linarith [r.2 i]
        · have h2 : 0 < r''.1 i := r''.2 i
          have hle' : (ε : ℝ) ≤ (δ : ℝ) := NNReal.coe_le_coe.mpr hle
          linarith
      let r' : PosRn n := ⟨fun i => r.1 i + if v i then (ε : ℝ) else -(ε : ℝ), hr'_pos⟩
      have hshift1 : IsShift v (fun _ => ε) r r' := fun _ => rfl
      have hvLE : vLE v r' r'' := by
        intro i
        have hs := hshift i
        dsimp [vLE, r'] at hs ⊢
        split_ifs at hs ⊢ with hvi
        · have hle' : (ε : ℝ) ≤ (δ : ℝ) := NNReal.coe_le_coe.mpr hle
          linarith
        · have hle' : (ε : ℝ) ≤ (δ : ℝ) := NNReal.coe_le_coe.mpr hle
          linarith
      obtain ⟨B, hB, hAB⟩ := f.2 r r' hshift1 A hA
      obtain ⟨C, hC, hBC⟩ := Y.H.mono r' r'' hvLE B hB
      exact ⟨C, hC, hAB.trans hBC⟩⟩
  let L : LPCat (HCl.{u} v) := {
    hom := fun X Y δ => HClHom X Y (fun _ => δ)
    homZero := Equiv.refl _
    comp := comp_hom
    S := S_hom
    id_comp := fun _ => Subtype.ext rfl
    comp_id := fun _ => Subtype.ext rfl
    assoc := fun _ _ _ => Subtype.ext rfl
    S_refl := fun _ => Subtype.ext rfl
    S_trans := fun _ _ _ => Subtype.ext rfl
    comp_S := fun _ _ _ _ => Subtype.ext rfl
    homZero_comp := fun _ _ => Subtype.ext rfl
  }
  exact ⟨L, fun _ _ _ => rfl⟩

/-- Acyclic morphisms of `hCl_v`: surjective maps with `ψ^*(H_Y) = H_X`. -/
def acyclicHCl {n : ℕ} (v : Fin n → Bool) : MorphismProperty (HCl.{u} v) :=
  fun X Y ψ => Function.Surjective ψ.1 ∧ ∀ r : PosRn n, ∀ A : Set X.carrier,
    A ∈ (X.H.H r).clusters ↔ ∃ B ∈ (Y.H.H r).clusters, A = ψ.1 ⁻¹' B

/-- Acyclic clustering morphisms contain identities and are closed under composition. -/
instance {n : ℕ} (v : Fin n → Bool) : (acyclicHCl.{u} v).IsMultiplicative where
  id_mem X := by
    constructor
    · exact Function.surjective_id
    · intro r A
      change A ∈ (X.H.H r).clusters ↔ ∃ B ∈ (X.H.H r).clusters, A = id ⁻¹' B
      simp
  comp_mem f g hf hg := by
    constructor
    · exact hg.1.comp hf.1
    · intro r A
      rw [hf.2 r A]
      constructor
      · rintro ⟨B, hB, rfl⟩
        obtain ⟨C, hC, rfl⟩ := (hg.2 r B).mp hB
        exact ⟨C, hC, rfl⟩
      · rintro ⟨C, hC, rfl⟩
        exact ⟨g.1 ⁻¹' C, (hg.2 r _).mpr ⟨C, hC, rfl⟩, rfl⟩

/-- Lemma 6.6.13: `hCl_v` is copowered and powered by representables, its underlying category
has pullbacks, binary products and sequential limits (hence it admits weighted pullbacks,
weighted sequential limits and terminal midpoints), and acyclic morphisms are closed under
weighted pullbacks. -/
theorem hCl_structure {n : ℕ} (v : Fin n → Bool) (L : LPCat (HCl.{u} v))
    (hL : ∀ (X Y : HCl.{u} v) (δ : ℝ≥0), L.hom X Y δ = HClHom X Y (fun _ => δ)) :
    Nonempty (@PoweredByRepresentables (HCl.{u} v) _ L) ∧
    Nonempty (@CopoweredByRepresentables (HCl.{u} v) _ L) ∧ HasPullbacks (HCl.{u} v) ∧
    HasBinaryProducts (HCl.{u} v) ∧ HasLimitsOfShape ℕᵒᵖ (HCl.{u} v) ∧
    @HasWeightedSeqLimits (HCl.{u} v) _ L ∧ @HasTerminalMidpoints (HCl.{u} v) _ L ∧
    @IsStableUnderWeightedPullbacks (HCl.{u} v) _ L (acyclicHCl v) := by
  sorry

/-- Theorem 6.6.14: the quotient interleaving distance on `hCl_v` is intrinsic and complete, and
is an infimum over interleavings of acyclic covers. -/
theorem hCl_quotientInterleavingDist_spec {n : ℕ} (v : Fin n → Bool) (L : LPCat (HCl.{u} v))
    (hL : ∀ (X Y : HCl.{u} v) (δ : ℝ≥0), L.hom X Y δ = HClHom X Y (fun _ => δ)) :
    @IsIntrinsicDist (HCl.{u} v) (@quotientInterleavingDist _ _ L (acyclicHCl v)) ∧
    @IsCompleteDist (HCl.{u} v) (@quotientInterleavingDist _ _ L (acyclicHCl v)) ∧
    ∀ X Y : HCl.{u} v, @quotientInterleavingDist _ _ L (acyclicHCl v) X Y =
      ⨅ (δ : ℝ≥0) (_ : ∃ (X' Y' : HCl.{u} v) (a : X' ⟶ X) (b : Y' ⟶ Y),
        acyclicHCl v a ∧ acyclicHCl v b ∧ @IsInterleaved _ _ L X' Y' δ), (δ : ℝ≥0∞) := by
  refine ⟨?_, ?_, ?_⟩
  · exact @quotientInterleavingDistOf_intrinsic _ _ L
      (@admitsCoherentFactorizations_of_midpoints _ _ L
        (hCl_structure v L hL).2.2.2.2.2.2.1) _
      (weaklyEquivalent_equivalence _)
  · sorry
  · intro X Y
    exact @quotientInterleavingDist_eq_inf_acyclicCover _ _ L (acyclicHCl v) _
      (hCl_structure v L hL).2.2.2.2.2.2.2 X Y

/-- Theorem 6.6.15: the quotient interleaving distance on `hCl_v` is the
correspondence-interleaving distance. -/
theorem hCl_quotientInterleavingDist_eq {n : ℕ} (v : Fin n → Bool) (L : LPCat (HCl.{u} v))
    (hL : ∀ (X Y : HCl.{u} v) (δ : ℝ≥0), L.hom X Y δ = HClHom X Y (fun _ => δ))
    (X Y : HCl.{u} v) :
    @quotientInterleavingDist _ _ L (acyclicHCl v) X Y = corrInterleavingDist X.H Y.H := by
  sorry

end Clustering

end ScoccolaPhd
