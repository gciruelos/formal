import ScoccolaPhd.Chapter5Section2Flows

/-!
# Sequential-limit preservation does not imply flow completeness

A counterexample to Theorem 5.2.20 and Proposition 5.2.21 as printed in Scoccola's
thesis. Objects are sets labelled by strictly positive real numbers. The weak power
at error `ε` allows a label to move within `ε`, and preserves sequential limits.
Singleton labels `1/(n+1)` form a Cauchy sequence with no interleaving-distance limit.

This does not refute Cruz's stronger preservation hypothesis: the thickening
functor fails to preserve a terminal object. See `5-2-21-weak-power-completeness-counterexample.md`.
All counterexample proofs are independent of the completeness statements being tested.
-/
open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal Topology
namespace ScoccolaPhd.FlowCompletenessCounterexample
open LPCat

/-- Positive-real-labelled sets used to audit Theorem 5.2.20. -/
structure Marked where
  carrier : Type
  label : carrier → ℝ
  positive : ∀ x, 0 < label x

instance : Category Marked where
  Hom X Y := {f : X.carrier → Y.carrier // ∀ x, Y.label (f x) = X.label x}
  id X := ⟨id, fun _ => rfl⟩
  comp f g := ⟨g.1 ∘ f.1, fun x => (g.2 _).trans (f.2 x)⟩

instance : LPCat Marked where
  hom X Y ε := {f : X.carrier → Y.carrier // ∀ x, edist (X.label x) (Y.label (f x)) ≤ ε}
  homZero :=
    { toFun := fun f => ⟨f.1, fun x => by rw [f.2 x]; simp⟩
      invFun := fun f => ⟨f.1, fun x => (edist_eq_zero.mp (le_antisymm (f.2 x) bot_le)).symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  comp {X Y Z ε δ} g f := ⟨g.1 ∘ f.1, fun x =>
    (edist_triangle (X.label x) (Y.label (f.1 x)) (Z.label (g.1 (f.1 x)))).trans
      ((add_le_add (f.2 x) (g.2 (f.1 x))).trans_eq (by simp [ENNReal.coe_add]))⟩
  S h f := ⟨f.1, fun x => (f.2 x).trans (ENNReal.coe_le_coe.mpr h)⟩
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl
  S_refl := fun _ => rfl
  S_trans := fun _ _ _ => rfl
  comp_S := fun _ _ _ _ => rfl
  homZero_comp := fun _ _ => rfl

/-- The underlying-set functor used to construct sequential limits. -/
def forgetLabels : Marked ⥤ Type where
  obj X := X.carrier
  map f := TypeCat.ofHom f.1

/-- The weak power that allows labels to move by at most `ε`. -/
def thickening (ε : ℝ≥0) : Marked ⥤ Marked where
  obj X :=
    { carrier := {p : ℝ × X.carrier // 0 < p.1 ∧ edist p.1 (X.label p.2) ≤ ε}
      label p := p.1.1
      positive p := p.2.1 }
  map {X Y} f := ⟨fun p => ⟨(p.1.1, f.1 p.1.2), p.2.1, by simpa [f.2] using p.2.2⟩,
    fun _ => rfl⟩

/-- The weak power structure in the counterexample to Proposition 5.2.21. -/
noncomputable def weakPowers : WeakPowerStructure Marked where
  pow := thickening
  wp X Y ε δ f := ⟨fun x => (f.1 x).1.2, fun x => by
    calc
      edist (X.label x) (Y.label (f.1 x).1.2) ≤
          edist (X.label x) (f.1 x).1.1 + edist (f.1 x).1.1 (Y.label (f.1 x).1.2) :=
        edist_triangle _ _ _
      _ ≤ (δ : ℝ≥0∞) + ε := add_le_add (f.2 x) (f.1 x).2.2
      _ = _ := by simp [add_comm]⟩
  wp_zero X Y ε := by
    constructor
    · intro f g h
      apply Subtype.ext
      funext x
      apply Subtype.ext
      apply Prod.ext
      · have hf : X.label x = (f.1 x).1.1 := edist_eq_zero.mp (le_antisymm (f.2 x) bot_le)
        have hg : X.label x = (g.1 x).1.1 := edist_eq_zero.mp (le_antisymm (g.2 x) bot_le)
        exact hf.symm.trans hg
      · exact congrFun (congrArg Subtype.val h) x
    · intro f
      refine ⟨⟨fun x => ⟨(X.label x, f.1 x), X.positive x, by simpa using f.2 x⟩,
        fun x => by simp [thickening]⟩, rfl⟩
  wp_S := fun _ _ => rfl
  wp_x := fun _ _ => rfl
  wp_y := fun _ _ => rfl

/-- The underlying inverse limit, labelled using its zeroth projection. -/
noncomputable def threadObject (D : ℕᵒᵖ ⥤ Marked) : Marked where
  carrier := limit (D ⋙ forgetLabels)
  label x := (D.obj (Opposite.op 0)).label (limit.π (D ⋙ forgetLabels) (Opposite.op 0) x)
  positive x := (D.obj (Opposite.op 0)).positive _

/-- All components of a compatible thread have the same label. -/
lemma thread_label (D : ℕᵒᵖ ⥤ Marked) (n : ℕ) (x : (threadObject D).carrier) :
    (D.obj (Opposite.op n)).label (limit.π (D ⋙ forgetLabels) (Opposite.op n) x) =
      (threadObject D).label x := by
  have h := ConcreteCategory.congr_hom (limit.w (D ⋙ forgetLabels) (homOfLE (Nat.zero_le n)).op) x
  exact ((D.map (homOfLE (Nat.zero_le n)).op).2 _).symm.trans (congrArg _ h)

/-- The sequential limit cone for labelled sets. -/
noncomputable def threadCone (D : ℕᵒᵖ ⥤ Marked) : Cone D where
  pt := threadObject D
  π :=
    { app n := ⟨limit.π (D ⋙ forgetLabels) n, thread_label D n.unop⟩
      naturality := fun _ _ f => Subtype.ext (congrArg (fun g : _ ⟶ _ => (g : _ → _)) (limit.w (D ⋙ forgetLabels) f)).symm }

/-- The thread cone has the labelled-set universal property. -/
noncomputable def threadConeIsLimit (D : ℕᵒᵖ ⥤ Marked) : Limits.IsLimit (threadCone D) where
  lift s := ⟨limit.lift (D ⋙ forgetLabels) (forgetLabels.mapCone s), fun x => by
    change (D.obj (Opposite.op 0)).label (limit.π (D ⋙ forgetLabels) (Opposite.op 0) (limit.lift (D ⋙ forgetLabels) (forgetLabels.mapCone s) x)) = s.pt.label x
    have h : limit.π (D ⋙ forgetLabels) (Opposite.op 0)
        (limit.lift (D ⋙ forgetLabels) (forgetLabels.mapCone s) x) =
        (s.π.app (Opposite.op 0)).1 x :=
      ConcreteCategory.congr_hom (limit.lift_π (forgetLabels.mapCone s) (Opposite.op 0)) x
    exact (congrArg (D.obj (Opposite.op 0)).label h).trans ((s.π.app (Opposite.op 0)).2 x)⟩
  fac s n := Subtype.ext (congrArg (fun g : _ ⟶ _ => (g : _ → _)) (limit.lift_π (forgetLabels.mapCone s) n))
  uniq s m hm := by
    apply Subtype.ext
    have h : TypeCat.ofHom m.1 = limit.lift (D ⋙ forgetLabels) (forgetLabels.mapCone s) := by
      apply limit.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact (congrFun (congrArg Subtype.val (hm n)) x).trans
        (ConcreteCategory.congr_hom (limit.lift_π (forgetLabels.mapCone s) n) x).symm
    exact congrArg (fun g : _ ⟶ _ => (g : _ → _)) h

noncomputable instance : HasLimitsOfShape ℕᵒᵖ Marked where
  has_limit D := ⟨⟨threadCone D, threadConeIsLimit D⟩⟩

/-- Forget the moved label in a cone over a thickened inverse sequence. -/
noncomputable def unlabelCone (D : ℕᵒᵖ ⥤ Marked) (ε : ℝ≥0)
    (s : Cone (D ⋙ thickening ε)) : Cone (D ⋙ forgetLabels) where
  pt := s.pt.carrier
  π :=
    { app n := TypeCat.ofHom (fun x => ((s.π.app n).1 x).1.2)
      naturality := by
        intro n m f
        apply ConcreteCategory.hom_ext
        intro x
        exact (congrArg (fun g => (g.1 x).1.2) (s.w f)).symm }

set_option maxHeartbeats 1000000 in
/-- Thickening preserves the labelled sequential limit cone. -/
noncomputable def thickeningConeIsLimit (D : ℕᵒᵖ ⥤ Marked) (ε : ℝ≥0) :
    Limits.IsLimit ((thickening ε).mapCone (threadCone D)) where
  lift s := ⟨fun x => ⟨(s.pt.label x, limit.lift (D ⋙ forgetLabels) (unlabelCone D ε s) x),
    s.pt.positive x, by
      change edist (s.pt.label x) ((threadObject D).label _) ≤ ε
      change edist (s.pt.label x) ((D.obj (Opposite.op 0)).label (limit.π (D ⋙ forgetLabels) (Opposite.op 0) (limit.lift (D ⋙ forgetLabels) (unlabelCone D ε s) x))) ≤ ε
      have hh : limit.π (D ⋙ forgetLabels) (Opposite.op 0)
          (limit.lift (D ⋙ forgetLabels) (unlabelCone D ε s) x) =
          ((s.π.app (Opposite.op 0)).1 x).1.2 :=
        ConcreteCategory.congr_hom (limit.lift_π (unlabelCone D ε s) (Opposite.op 0)) x
      have h0 : ((s.π.app (Opposite.op 0)).1 x).1.1 = s.pt.label x :=
        (s.π.app (Opposite.op 0)).2 x
      exact (congrArg₂ edist h0.symm (congrArg (D.obj (Opposite.op 0)).label hh)).trans_le
        (((s.π.app (Opposite.op 0)).1 x).2.2)⟩, fun _ => rfl⟩
  fac s n := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    apply Prod.ext
    · exact ((s.π.app n).2 x).symm
    · exact ConcreteCategory.congr_hom (limit.lift_π (unlabelCone D ε s) n) x
  uniq s m hm := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    apply Prod.ext
    · exact m.2 x
    · have h : TypeCat.ofHom (fun x => (m.1 x).1.2) = limit.lift (D ⋙ forgetLabels) (unlabelCone D ε s) := by
        apply limit.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro y
        have hn := congrArg (fun g => (g.1 y).1.2) (hm n)
        have hh : limit.π (D ⋙ forgetLabels) n
            (limit.lift (D ⋙ forgetLabels) (unlabelCone D ε s) y) =
            ((s.π.app n).1 y).1.2 :=
          ConcreteCategory.congr_hom (limit.lift_π (unlabelCone D ε s) n) y
        exact hn.trans hh.symm
      exact ConcreteCategory.congr_hom h x

noncomputable instance (ε : ℝ≥0) : PreservesLimitsOfShape ℕᵒᵖ (thickening ε) where
  preservesLimit {D} := preservesLimit_of_preserves_limit_cone (threadConeIsLimit D)
    (thickeningConeIsLimit D ε)
open LPCat

/-- A singleton carrying one strictly positive label. -/
def point (a : ℝ) (ha : 0 < a) : Marked := ⟨PUnit, fun _ => a, fun _ => ha⟩

/-- Singletons have interleaving distance at most their label distance. -/
lemma point_dist_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    interleavingDist (point a ha) (point b hb) ≤ edist a b := by
  let δ : ℝ≥0 := ⟨dist a b, dist_nonneg⟩
  have hd : edist a b = (δ : ℝ≥0∞) := by
    rw [edist_dist]
    exact ENNReal.ofReal_coe_nnreal (p := δ)
  rw [hd]
  refine iInf₂_le_of_le δ ⟨⟨⟨fun _ => PUnit.unit, fun _ => by change edist a b ≤ δ; exact hd.le⟩,
    ⟨fun _ => PUnit.unit, fun _ => by change edist b a ≤ δ; rw [edist_comm]; exact hd.le⟩, ?_, ?_⟩⟩ le_rfl
  · apply Subtype.ext; funext x; cases x; rfl
  · apply Subtype.ext; funext x; cases x; rfl

/-- Every point of a proposed limit bounds its distance from a labelled singleton. -/
lemma point_label_le_dist (X : Marked) (x : X.carrier) (a : ℝ) (ha : 0 < a) :
    edist a (X.label x) ≤ interleavingDist (point a ha) X := by
  refine le_iInf₂ fun δ h => ?_
  obtain ⟨⟨f, g, hfg, hgf⟩⟩ := h
  exact (edist_comm _ _).le.trans (g.2 x)

/-- Singleton labels approaching the excluded label zero. -/
noncomputable def singletonSequence (n : ℕ) : Marked :=
  point (1 / ((n : ℝ) + 1)) (by positivity)

/-- The singleton sequence is Cauchy for the interleaving distance. -/
lemma singletonSequence_cauchy :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ i j, N ≤ i → N ≤ j →
      interleavingDist (singletonSequence i) (singletonSequence j) < ε := by
  have hc : CauchySeq (fun n : ℕ => (1 / ((n : ℝ) + 1))) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).cauchySeq
  rw [EMetric.cauchySeq_iff] at hc
  intro ε hε
  obtain ⟨N, hN⟩ := hc ε hε
  refine ⟨N, fun i j hi hj => ?_⟩
  exact (point_dist_le _ _ _ _).trans_lt (hN i hi j hj)

/-- The labelled-set interleaving distance is not complete. -/
lemma not_complete : ¬ IsCompleteDist (interleavingDist (C := Marked)) := by
  intro hcomplete
  obtain ⟨L, hL⟩ := hcomplete singletonSequence singletonSequence_cauchy
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hL.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < (1 : ℝ≥0) by norm_num)))
  have hpair : IsInterleaved (singletonSequence N) L 1 := isInterleaved_of_dist_lt (hN N le_rfl)
  obtain ⟨I⟩ := hpair
  let x : L.carrier := I.f.1 PUnit.unit
  have he : Filter.Tendsto (fun n : ℕ => edist (1 / ((n : ℝ) + 1)) (L.label x))
      Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
      (fun _ => bot_le) (fun n => point_label_le_dist L x _ _)
  have ha : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) Filter.atTop (𝓝 (L.label x)) :=
    tendsto_iff_edist_tendsto_0.mpr he
  have hz := tendsto_nhds_unique ha (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact (ne_of_gt (L.positive x)) hz

/-- The flow induced by the explicit weak power structure. -/
noncomputable def counterexampleFlow : Flow Marked :=
  letI := weakPowers
  powFlow

/-- Every flow functor preserves sequential limits. -/
lemma counterexampleFlow_preserves (ε : ℝ≥0) :
    PreservesLimitsOfShape ℕᵒᵖ (counterexampleFlow.T.obj ε) := by
  change PreservesLimitsOfShape ℕᵒᵖ (thickening ε)
  infer_instance

/-- The flow distance is not complete, despite sequential-limit preservation. -/
lemma counterexampleFlow_not_complete : ¬ IsCompleteDist counterexampleFlow.interleavingDist := by
  letI := weakPowers
  have hd : counterexampleFlow.interleavingDist = interleavingDist (C := Marked) :=
    funext fun x => funext fun y => powFlow_interleavingDist x y
  rw [hd]
  exact not_complete
/-- The counterexample does not satisfy the proved strong-flow specialization. -/
lemma counterexampleFlow_not_strong : ¬ counterexampleFlow.IsStrong := by
  intro h
  exact counterexampleFlow_not_complete
    (counterexampleFlow.interleavingDist_complete_of_strong h counterexampleFlow_preserves)

/-- The weak powers satisfy the printed hypothesis of Proposition 5.2.21. -/
lemma weakPowers_preserve_sequential_limits (ε : ℝ≥0) :
    PreservesLimitsOfShape ℕᵒᵖ (weakPowers.pow ε) := by
  change PreservesLimitsOfShape ℕᵒᵖ (thickening ε)
  infer_instance

/-- A checked counterexample to the sequential-preservation version of Theorem 5.2.20. -/
theorem flow_counterexample : HasLimitsOfShape ℕᵒᵖ Marked ∧
    (∀ ε, PreservesLimitsOfShape ℕᵒᵖ (counterexampleFlow.T.obj ε)) ∧
    ¬ IsCompleteDist counterexampleFlow.interleavingDist :=
  ⟨inferInstance, counterexampleFlow_preserves, counterexampleFlow_not_complete⟩

/-- A checked counterexample to the sequential-preservation version of Proposition 5.2.21. -/
theorem weak_power_counterexample : HasLimitsOfShape ℕᵒᵖ Marked ∧
    (∀ ε, PreservesLimitsOfShape ℕᵒᵖ (weakPowers.pow ε)) ∧
    ¬ IsCompleteDist (LPCat.interleavingDist (C := Marked)) :=
  ⟨inferInstance, weakPowers_preserve_sequential_limits, not_complete⟩


/-- The terminal labelled set, with one point at every positive label. -/
def terminalMarked : Marked :=
  ⟨{r : ℝ // 0 < r}, Subtype.val, Subtype.property⟩

/-- Label-preserving maps into `terminalMarked` are unique. -/
noncomputable def terminalMarkedIsTerminal : Limits.IsTerminal terminalMarked :=
  Limits.IsTerminal.ofUniqueHom
    (fun X => ⟨fun x => ⟨X.label x, X.positive x⟩, fun _ => rfl⟩)
    (fun X f => by
      apply Subtype.ext
      funext x
      exact Subtype.ext (f.2 x))

/-- Thickening does not preserve this terminal object. -/
lemma thickening_terminal_not_terminal : ¬ Nonempty (Limits.IsTerminal ((thickening 1).obj terminalMarked)) := by
  rintro ⟨h⟩
  let f : point 1 (by norm_num) ⟶ (thickening 1).obj terminalMarked :=
    ⟨fun _ => ⟨(1, ⟨1, by norm_num⟩), by norm_num, by simp [terminalMarked]⟩, fun _ => rfl⟩
  let g : point 1 (by norm_num) ⟶ (thickening 1).obj terminalMarked :=
    ⟨fun _ => ⟨(1, ⟨2, by norm_num⟩), by norm_num,
      by change edist (1 : ℝ) 2 ≤ (1 : ℝ≥0); norm_num [edist_dist, Real.dist_eq]⟩, fun _ => rfl⟩
  have heq : (1 : ℝ) = 2 := congrArg (fun k => (k.1 PUnit.unit).1.2.1) (h.hom_ext f g)
  norm_num at heq

/-- The counterexample does not satisfy the stronger preservation hypothesis of Cruz. -/
lemma thickening_not_preserves_all_limits : ¬ PreservesLimits (thickening 1) := by
  intro h
  letI := h
  exact thickening_terminal_not_terminal
    ⟨terminalMarkedIsTerminal.isTerminalObj (thickening 1) terminalMarked⟩
end ScoccolaPhd.FlowCompletenessCounterexample
