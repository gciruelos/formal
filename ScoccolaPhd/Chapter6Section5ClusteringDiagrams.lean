import Mathlib
import ScoccolaPhd.Chapter6Section1DissimilarityFiltrations

/-!
# §§6.5–6.9: kernel density, clustering, persistent sets, diagrams

Contents:
* Chapter 6.5: Stability of the kernel density filtration
* Chapter 6.6: The correspondence-interleaving distance on hierarchical clusterings
* Chapter 6.7: The interleaving distance on persistent sets
* Chapter 6.8–6.9: Mémoli's `d_F`; persistence diagrams
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

/-- Definition 6.5.11: `wDiss` is a locally bi-persistent category. -/
theorem exists_wDiss_lqpcat :
    ∃ L : LQPCat (ℝ≥0 × ℝ≥0) WDiss.{u}, ∀ (X Y : WDiss.{u}) (ε δ : ℝ≥0),
      L.hom X Y (ε, δ) = WDissHom X Y ε δ := by
  let L : LQPCat (ℝ≥0 × ℝ≥0) WDiss.{u} :=
    { hom := fun X Y q => WDissHom X Y q.1 q.2
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
      homZero_comp := fun _ _ => rfl }
  exact ⟨L, fun _ _ _ _ => rfl⟩

/-- Definition 6.5.14: acyclic morphisms of weighted dissimilarity spaces: surjective, distance
preserving and weight preserving. -/
def acyclicWDiss : MorphismProperty WDiss.{u} :=
  fun X Y f => Function.Surjective f.1 ∧ (∀ x x', Y.d (f.1 x) (f.1 x') = X.d x x') ∧
    ∀ x r, X.M x r = Y.M (f.1 x) r

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

/-- Lemma 6.5.17: acyclic morphisms of `wDiss` are stable under weighted pullback (for the
locally persistent structure `L` obtained by change of enrichment along `(1, 1)`). -/
theorem isStableUnderWeightedPullbacks_acyclicWDiss (LW : LQPCat (ℝ≥0 × ℝ≥0) WDiss.{u})
    (hLW : ∀ (X Y : WDiss.{u}) (ε δ : ℝ≥0), LW.hom X Y (ε, δ) = WDissHom X Y ε δ)
    (L : LPCat WDiss.{u}) (hL : IsChangeOfEnrichment (pairFamily (1, 1)) LW L) :
    @IsStableUnderWeightedPullbacks WDiss _ L acyclicWDiss := by
  sorry

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
`(d_I^{wDiss_{(1,1)}})/≃ (X, Y) ≤ 2 d_GHP (X, Y)`. -/
theorem quotientInterleavingDist_wDiss_le_ghp (L : LPCat WDiss.{u})
    (LW : LQPCat (ℝ≥0 × ℝ≥0) WDiss.{u})
    (hLW : ∀ (X Y : WDiss.{u}) (ε δ : ℝ≥0), LW.hom X Y (ε, δ) = WDissHom X Y ε δ)
    (hL : IsChangeOfEnrichment (pairFamily (1, 1)) LW L)
    (X Y : CompactMPS.{u}) :
    @quotientInterleavingDist WDiss _ L acyclicWDiss X.toWDiss Y.toWDiss ≤ 2 * ghpDist X Y := by
  sorry

end KernelDensity

/-! ## Chapter 6.6: The correspondence-interleaving distance on hierarchical clusterings

Clusterings, hierarchical clusterings (with a sign vector `v ∈ {−1, 1}ⁿ`, encoded as
`v : Fin n → Bool` with `true` meaning covariant) and the correspondence-interleaving distance
are defined concretely.  The category `hCl_v` of hierarchical clusterings has a concrete
category structure (its `0`-morphisms); its locally persistent structure is stated to exist.

Omitted from 6.6.3: the comparison with the Carlsson–Mémoli distance on dendrograms and with
the merge distortion metric of [EBW15] (merge functions, cluster trees).

Statements only (with the definitions); all proofs are `sorry`. -/

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
  · sorry
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

/-! ## Chapter 6.7: The interleaving distance on persistent sets

`Set^ℝ` carries the locally persistent structure of persistent objects.  The full subcategory
of right continuous, q-tame persistent sets is `RTSet`; its locally persistent structure is
stated to exist.  Ultra metric spaces and their single-linkage persistent sets (Section 6.7.2)
are defined concretely.

Omitted: Proposition 6.7.4 (weighted sequential limits "of morphisms that are part of an
interleaving"), Definition 6.7.8 (dendrograms) and the embedding of dendrograms.

Statements only (with the definitions); all proofs are `sorry`. -/

section PersistentSets

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

open LPCat

/-- Theorem 6.7.1: the interleaving distance on `Set^ℝ` is intrinsic and complete. -/
theorem persistentSet_intrinsic_complete :
    @IsIntrinsicDist (ℝ ⥤ Type u) (@interleavingDist (ℝ ⥤ Type u) _ (persistentLPCat (Type u))) ∧
    @IsCompleteDist (ℝ ⥤ Type u) (@interleavingDist (ℝ ⥤ Type u) _ (persistentLPCat (Type u))) := by
  exact ⟨persistent_intrinsic (Type u), (persistent_complete (Type u)).2⟩

/-- The full subcategory `Set^ℝ_{righ,tame}` of right continuous and q-tame persistent sets. -/
structure RTSet where
  X : ℝ ⥤ Type u
  rightContinuous : IsRightContinuous X
  qtame : IsQTameSet X

instance : Category.{u} RTSet.{u} where
  Hom A B := A.X ⟶ B.X
  id A := 𝟙 A.X
  comp f g := f ≫ g

/-- The locally persistent structure on `Set^ℝ_{righ,tame}`, induced from that of
`Set^ℝ`: `Hom(A, B)_ε = Nat(A, B^ε)`. -/
theorem exists_rtSet_lpcat :
    ∃ L : LPCat RTSet.{u}, ∀ (A B : RTSet.{u}) (ε : ℝ≥0),
      L.hom A B ε = (A.X ⟶ shift (ε : ℝ) B.X) := by
  let P : LPCat (ℝ ⥤ Type u) := persistentLPCat (Type u)
  let L : LPCat RTSet.{u} := {
    hom := fun A B ε => P.hom A.X B.X ε
    homZero := P.homZero
    comp := P.comp
    S := P.S
    id_comp := P.id_comp
    comp_id := P.comp_id
    assoc := P.assoc
    S_refl := P.S_refl
    S_trans := P.S_trans
    comp_S := P.comp_S
    homZero_comp := P.homZero_comp
  }
  exact ⟨L, fun A B ε => rfl⟩

/-- Proposition 6.7.3: `Set^ℝ_{righ,tame}` is copowered and powered by representables and has
binary products, pullbacks and terminal midpoints. -/
theorem rtSet_structure (L : LPCat RTSet.{u})
    (hL : ∀ (A B : RTSet.{u}) (ε : ℝ≥0), L.hom A B ε = (A.X ⟶ shift (ε : ℝ) B.X)) :
    Nonempty (@PoweredByRepresentables RTSet.{u} _ L) ∧
    Nonempty (@CopoweredByRepresentables RTSet.{u} _ L) ∧ HasBinaryProducts RTSet.{u} ∧
    HasPullbacks RTSet.{u} ∧ @HasTerminalMidpoints RTSet.{u} _ L := by
  sorry

/-- Theorem 6.7.5: the interleaving distance on right continuous, q-tame persistent sets is
complete and geodesic, and persistent sets at distance zero are isomorphic. -/
theorem rtSet_geodesic_complete (L : LPCat RTSet.{u})
    (hL : ∀ (A B : RTSet.{u}) (ε : ℝ≥0), L.hom A B ε = (A.X ⟶ shift (ε : ℝ) B.X)) :
    @IsGeodesicDist RTSet.{u} (@interleavingDist RTSet.{u} _ L) ∧
    @IsCompleteDist RTSet.{u} (@interleavingDist RTSet.{u} _ L) ∧
    ∀ A B : RTSet.{u}, @interleavingDist RTSet.{u} _ L A B = 0 → Nonempty (A ≅ B) := by
  sorry

/-! ### 6.7.2 Persistent sets and ultra metric spaces -/

/-- Definition 6.7.9: an extended ultra metric space: an extended metric space (only equal
points are at distance `0`) with the ultrametric inequality. -/
structure UltraMet where
  carrier : Type u
  [metric : EMetricSpace carrier]
  ultra : ∀ x y z : carrier, edist x z ≤ max (edist x y) (edist y z)

attribute [instance] UltraMet.metric

/-- The category of extended ultra metric spaces and distance non-increasing maps. -/
instance : Category.{u} UltraMet.{u} where
  Hom X Y := {f : X.carrier → Y.carrier // IsDistNonIncreasing f}
  id X := ⟨id, fun _ _ => le_rfl⟩
  comp f g := ⟨g.1 ∘ f.1, fun p p' => le_trans (g.2 _ _) (f.2 p p')⟩

/-- The single-linkage equivalence relation `x ∼_r y ⟺ d x y ≤ r` of an ultra metric space. -/
def UltraMet.slSetoid (X : UltraMet.{u}) (r : ℝ≥0) : Setoid X.carrier where
  r x y := edist x y ≤ r
  iseqv :=
    ⟨fun x => by simp, fun h => by simpa [edist_comm] using h,
      fun h h' => ((X.ultra _ _ _).trans (max_le h h'))⟩

/-- The persistent set of single-linkage clusters of an ultrametric space. -/
def UltraMet.singleLinkage (X : UltraMet.{u}) : ℝ≥0 ⥤ Type u where
  obj r := Quotient (X.slSetoid r)
  map {r s} h := TypeCat.ofHom (@Quotient.map _ _ (X.slSetoid r) (X.slSetoid s) id
    (fun _ _ hxy => hxy.trans (ENNReal.coe_le_coe.mpr (leOfHom h))))
  map_id := by intro r; ext q; induction q using Quotient.inductionOn with | _ x => rfl
  map_comp := by intro r s t f g; ext q; induction q using Quotient.inductionOn with | _ x => rfl

/-- Single linkage sends non-expanding maps to natural transformations. -/
def singleLinkageFunctor : UltraMet.{u} ⥤ (ℝ≥0 ⥤ Type u) where
  obj X := X.singleLinkage
  map {X Y} f := {
    app := fun r => TypeCat.ofHom (@Quotient.map _ _ (X.slSetoid r) (Y.slSetoid r) f.1
      (fun _ _ h => (f.2 _ _).trans h))
    naturality := by
      intro r s h
      ext q
      induction q using Quotient.inductionOn with | _ x => rfl
  }
  map_id := by
    intro X
    ext r q
    induction q using Quotient.inductionOn with | _ x => rfl
  map_comp := by
    intro X Y Z f g
    ext r q
    induction q using Quotient.inductionOn with | _ x => rfl

/-- `X ∈ Set^{ℝ≥0}` is separated if `X r → lim_{r' > r} X r'` is injective. -/
def IsSeparated (X : ℝ≥0 ⥤ Type u) : Prop :=
  ∀ (r : ℝ≥0) (a b : X.obj r), (∀ r' (h : r < r'), X.map (homOfLE h.le) a = X.map (homOfLE h.le) b) →
    a = b

/-- `X ∈ Set^{ℝ≥0}` is flabby if all structure maps are surjective. -/
def IsFlabby (X : ℝ≥0 ⥤ Type u) : Prop :=
  ∀ (r s : ℝ≥0) (h : r ≤ s), Function.Surjective (X.map (homOfLE h))

/-- Theorem 6.7.10 ([Ack13]): single linkage `X ↦ (r ↦ X/∼_r)` is an equivalence between
extended ultra metric spaces and flabby, separated persistent sets; and `X` is complete iff
`SL X` is right continuous. -/
theorem singleLinkage_equivalence :
    ∃ SL : UltraMet.{u} ⥤ (ℝ≥0 ⥤ Type u),
      (∀ X r, (SL.obj X).obj r = Quotient (X.slSetoid r)) ∧ SL.Full ∧ SL.Faithful ∧
      (∀ F : ℝ≥0 ⥤ Type u, (∃ X, Nonempty (SL.obj X ≅ F)) ↔ IsFlabby F ∧ IsSeparated F) ∧
      (∀ X, IsCompleteEP X.carrier ↔ IsRightContinuous (SL.obj X)) := by
  refine ⟨singleLinkageFunctor, (fun _ _ => rfl), ?_⟩
  sorry

/-- Theorem 6.7.11: under the correspondence of Theorem 6.7.10, an extended ultra metric space
is totally bounded iff its single-linkage persistent set is q-tame, and compact iff q-tame and
right continuous. -/
theorem singleLinkage_compact (SL : UltraMet.{u} ⥤ (ℝ≥0 ⥤ Type u))
    (hSL : ∀ X r, (SL.obj X).obj r = Quotient (X.slSetoid r))
    (hSLmap : ∀ (X : UltraMet.{u}) (r s : ℝ≥0) (h : r ≤ s) (x : X.carrier),
      (SL.obj X).map (homOfLE h) (cast (hSL X r).symm (Quotient.mk (X.slSetoid r) x)) =
        cast (hSL X s).symm (Quotient.mk (X.slSetoid s) x))
    (X : UltraMet.{u}) :
    (IsTotallyBoundedEP X.carrier ↔ IsQTameSet (SL.obj X)) ∧
    (IsCompactEP X.carrier ↔ IsQTameSet (SL.obj X) ∧ IsRightContinuous (SL.obj X)) := by
  sorry

end PersistentSets

/-! ## Chapter 6.8–6.9: Mémoli's `d_F`; persistence diagrams

6.8: finite filtered simplicial complexes `ffsCpx` form a locally persistent category (given
here concretely).  Remark 6.8.9 (comparison with the homotopy interleaving distance through
geometric realization) is omitted.

6.9: persistence diagrams and the locally persistent categories `PD^p_q`.  The extended-real
distance `|x - x'|` on `[-∞, ∞]` is taken to be `0` if `x = x'`, `∞` if exactly one is infinite
(or they are opposite infinities) and the usual absolute value otherwise.

The locally persistent structure of `ffsCpx` and the acyclic-cover formula are proved;
the remaining constructions and comparisons are open. -/

section SimplicialAndDiagrams

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

open LPCat

/-! ### 6.8 Mémoli's `d_F` distance -/

/-- A finite filtered simplicial complex: a finite set with a function `F : P(X) → ℝ` respecting
inclusions. -/
structure FFSCpx where
  carrier : Type
  [fin : Fintype carrier]
  F : Finset carrier → ℝ
  mono : ∀ σ τ, σ ⊆ τ → F σ ≤ F τ

attribute [instance] FFSCpx.fin

open scoped Classical in
/-- Morphisms of `ffsCpx` of degree `ε`: maps with `F_X σ ≤ F_Y (f σ) + ε` for all `σ`. -/
def FFSCpxHom (X Y : FFSCpx) (ε : ℝ≥0) : Type :=
  {f : X.carrier → Y.carrier // ∀ σ, X.F σ ≤ Y.F (σ.image f) + ε}

open scoped Classical in
/-- The underlying category of `ffsCpx`: the `0`-morphisms. -/
instance : Category.{0} FFSCpx where
  Hom X Y := FFSCpxHom X Y 0
  id X := ⟨id, fun σ => by simp⟩
  comp {X Y Z} f g := ⟨g.1 ∘ f.1, fun σ => by
    have h1 := f.2 σ
    have h2 := g.2 (σ.image f.1)
    rw [Finset.image_image] at h2
    simp only [NNReal.coe_zero, add_zero] at h1 h2 ⊢
    exact h1.trans h2⟩

open scoped Classical in
/-- The locally persistent structure of `ffsCpx`: `Hom(X, Y)_ε = FFSCpxHom X Y ε`. -/
noncomputable def ffsCpxLPCat : LPCat FFSCpx where
  hom := FFSCpxHom
  homZero := Equiv.refl _
  comp := fun {X Y Z ε δ} g f => ⟨g.1 ∘ f.1, fun σ => by
    have hf := f.2 σ
    have hg := g.2 (σ.image f.1)
    rw [Finset.image_image] at hg
    push_cast
    linarith⟩
  S := fun {X Y ε δ} h f => ⟨f.1, fun σ =>
    (f.2 σ).trans (add_le_add_right (NNReal.coe_le_coe.mpr h) _)⟩
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl
  S_refl := fun _ => rfl
  S_trans := fun _ _ _ => rfl
  comp_S := fun _ _ _ _ => rfl
  homZero_comp := fun _ _ => rfl

/-- The locally persistent structure of `ffsCpx`: `Hom(X, Y)_ε = FFSCpxHom X Y ε`. -/
theorem exists_ffsCpx_lpcat :
    ∃ L : LPCat FFSCpx, ∀ (X Y : FFSCpx) (ε : ℝ≥0), L.hom X Y ε = FFSCpxHom X Y ε :=
  ⟨ffsCpxLPCat, fun _ _ _ => rfl⟩

open scoped Classical in
/-- Acyclic morphisms of `ffsCpx`: surjective maps with `F_X σ = F_Y (f σ)`. -/
def acyclicFFSCpx : MorphismProperty FFSCpx :=
  fun X Y f => Function.Surjective f.1 ∧ ∀ σ, X.F σ = Y.F (σ.image f.1)

open scoped Classical in
/-- Mémoli's distance [Mé17]:
`d_F (X, Y) = inf max_σ |f^* F_X (σ) - g^* F_Y (σ)|` over finite `Z` and surjections
`f : Z → X`, `g : Z → Y`. -/
noncomputable def ffsCpxDist (X Y : FFSCpx) : ℝ≥0∞ :=
  ⨅ (Z : Type) (_ : Fintype Z) (f : Z → X.carrier) (g : Z → Y.carrier)
    (_ : Function.Surjective f) (_ : Function.Surjective g),
    ⨆ σ : Finset Z, ENNReal.ofReal |X.F (σ.image f) - Y.F (σ.image g)|

section ffs

variable (L : LPCat FFSCpx) (hL : L = ffsCpxLPCat)

include hL

open scoped Classical in
/-- Lemma 6.8.1: `ffsCpx` is copowered and powered by representables (powers `F_{Y^ε} = F_Y + ε`,
copowers `F_{ε·X} = F_X - ε`).

**Note.** The hypothesis `hL` pins the locally persistent structure to
the canonical `ffsCpxLPCat` of `exists_ffsCpx_lpcat` (an arbitrary structure with the same
hom-sets could have a different composition). -/
theorem ffsCpx_powered :
    Nonempty (@PoweredByRepresentables FFSCpx _ L) ∧ Nonempty (@CopoweredByRepresentables FFSCpx _ L) := by
  subst hL
  letI : LPCat FFSCpx := ffsCpxLPCat
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · exact
    { pow := fun ε =>
        { obj := fun Y => ⟨Y.carrier, fun σ => Y.F σ + ε, fun σ τ h => add_le_add_left (Y.mono σ τ h) _⟩
          map := fun {Y Y'} f => ⟨f.1, fun σ => by
            have := f.2 σ
            push_cast at this ⊢
            linarith⟩
          map_id := fun _ => Subtype.ext rfl
          map_comp := fun _ _ => Subtype.ext rfl }
      powIso := fun x y ε r =>
        { toFun := fun f => ⟨f.1, fun σ => by
            have := f.2 σ
            change x.F σ ≤ y.F (σ.image f.1) + ε + r at this
            push_cast
            linarith⟩
          invFun := fun f => ⟨f.1, fun σ => by
            have := f.2 σ
            change x.F σ ≤ y.F (σ.image f.1) + (ε + r : ℝ≥0) at this
            change x.F σ ≤ y.F (σ.image f.1) + ε + r
            push_cast at this
            linarith⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext rfl }
      powIso_S := fun _ _ => Subtype.ext rfl
      powIso_x := fun _ _ => Subtype.ext rfl
      powIso_y := fun _ _ => Subtype.ext rfl }
  · exact
    { copow := fun ε =>
        { obj := fun X => ⟨X.carrier, fun σ => X.F σ - ε, fun σ τ h => sub_le_sub_right (X.mono σ τ h) _⟩
          map := fun {X X'} f => ⟨f.1, fun σ => by
            have := f.2 σ
            push_cast at this ⊢
            linarith⟩
          map_id := fun _ => Subtype.ext rfl
          map_comp := fun _ _ => Subtype.ext rfl }
      copowIso := fun x y ε r =>
        { toFun := fun f => ⟨f.1, fun σ => by
            have := f.2 σ
            change x.F σ - ε ≤ y.F (σ.image f.1) + r at this
            push_cast
            linarith⟩
          invFun := fun f => ⟨f.1, fun σ => by
            have := f.2 σ
            change x.F σ ≤ y.F (σ.image f.1) + (ε + r : ℝ≥0) at this
            change x.F σ - ε ≤ y.F (σ.image f.1) + r
            push_cast at this
            linarith⟩
          left_inv := fun _ => Subtype.ext rfl
          right_inv := fun _ => Subtype.ext rfl }
      copowIso_S := fun _ _ => Subtype.ext rfl
      copowIso_x := fun _ _ => Subtype.ext rfl
      copowIso_y := fun _ _ => Subtype.ext rfl }

/-- Lemma 6.8.2 and Corollary 6.8.3: the underlying category has binary products and pullbacks;
hence `ffsCpx` admits weighted pullbacks and terminal midpoints. -/
theorem ffsCpx_limits :
    HasBinaryProducts FFSCpx ∧ HasPullbacks FFSCpx ∧ @HasTerminalMidpoints FFSCpx _ L := by
  sorry

/-- Lemma 6.8.4: acyclic morphisms of `ffsCpx` are stable under weighted pullback. -/
theorem isStableUnderWeightedPullbacks_acyclicFFSCpx :
    @IsStableUnderWeightedPullbacks FFSCpx _ L acyclicFFSCpx := by
  sorry

/-- Theorem 6.8.5. -/
theorem ffsCpx_quotientInterleavingDist_spec (X Y : FFSCpx) :
    @quotientInterleavingDist FFSCpx _ L acyclicFFSCpx X Y =
      ⨅ (δ : ℝ≥0) (_ : ∃ (X' Y' : FFSCpx) (a : X' ⟶ X) (b : Y' ⟶ Y),
        acyclicFFSCpx a ∧ acyclicFFSCpx b ∧ @IsInterleaved _ _ L X' Y' δ), (δ : ℝ≥0∞) := by
  classical
  letI := L
  letI : acyclicFFSCpx.IsMultiplicative :=
    { id_mem := fun X => ⟨Function.surjective_id, fun σ => by
        change X.F σ = X.F (σ.image id)
        simp⟩
      comp_mem := fun {X Y Z} f g hf hg => ⟨hg.1.comp hf.1, fun σ => by
        change X.F σ = Z.F (σ.image (g.1 ∘ f.1))
        rw [hf.2 σ, hg.2 (σ.image f.1), Finset.image_image]⟩ }
  exact quotientInterleavingDist_eq_inf_acyclicCover
    (isStableUnderWeightedPullbacks_acyclicFFSCpx L hL) X Y

/-- Lemma 6.8.6: `(d_I)/≃` reflects quotient interleavings. -/
theorem ffsCpx_reflects : @ReflectsQuotientInterleavings FFSCpx _ L acyclicFFSCpx := by
  sorry

/-- Theorem 6.8.7: `(d_I)/≃` is geodesic, and two complexes at distance `0` are weakly
equivalent. -/
theorem ffsCpx_geodesic :
    @IsGeodesicDist FFSCpx (@quotientInterleavingDist FFSCpx _ L acyclicFFSCpx) ∧
    ∀ X Y : FFSCpx, @quotientInterleavingDist FFSCpx _ L acyclicFFSCpx X Y = 0 →
      WeaklyEquivalent acyclicFFSCpx X Y := by
  classical
  letI := L
  letI : acyclicFFSCpx.IsMultiplicative :=
    { id_mem := fun X => ⟨Function.surjective_id, fun σ => by
        change X.F σ = X.F (σ.image id)
        simp⟩
      comp_mem := fun {X Y Z} f g hf hg => ⟨hg.1.comp hf.1, fun σ => by
        change X.F σ = Z.F (σ.image (g.1 ∘ f.1))
        rw [hf.2 σ, hg.2 (σ.image f.1), Finset.image_image]⟩ }
  refine ⟨quotientInterleavingDist_geodesic acyclicFFSCpx
    (admitsCoherentFactorizations_of_midpoints (ffsCpx_limits L hL).2.2)
    (isStableUnderWeightedPullbacks_acyclicFFSCpx L hL) (ffsCpx_reflects L hL), ?_⟩
  intro X Y h
  obtain ⟨X', Y', a, b, ha, hb, hi⟩ := exists_acyclicCover
    (isStableUnderWeightedPullbacks_acyclicFFSCpx L hL)
    (ffsCpx_reflects L hL X Y 0 (by simpa using h))
  obtain ⟨i⟩ := isInterleaved_zero_iff.mp hi
  have hiso : acyclicFFSCpx i.hom := by
    have hleft : Function.LeftInverse i.inv.1 i.hom.1 := by
      intro x
      have h := congrArg (fun f : X' ⟶ X' => f.1 x) i.hom_inv_id
      exact h
    have hright : Function.RightInverse i.inv.1 i.hom.1 := by
      intro x
      have h := congrArg (fun f : Y' ⟶ Y' => f.1 x) i.inv_hom_id
      exact h
    refine ⟨hright.surjective, fun σ => le_antisymm ?_ ?_⟩
    · simpa using i.hom.2 σ
    · have h := i.inv.2 (σ.image i.hom.1)
      have heq : (σ.image i.hom.1).image i.inv.1 = σ := by
        rw [Finset.image_image]
        have hid : i.inv.1 ∘ i.hom.1 = id := funext hleft
        rw [hid, Finset.image_id]
      simpa [heq] using h
  exact weaklyEquivalent_of_span ⟨X', a, i.hom ≫ b, ha,
    MorphismProperty.comp_mem _ _ _ hiso hb⟩

/-- Proposition 6.8.8: `(d_I)/≃ = d_F`. -/
theorem ffsCpx_quotientInterleavingDist_eq (X Y : FFSCpx) :
    @quotientInterleavingDist FFSCpx _ L acyclicFFSCpx X Y = ffsCpxDist X Y := by
  sorry

end ffs

/-! ### 6.9 Persistence diagrams -/

/-- The distance `|x - x'|` on `[-∞, ∞]`. -/
noncomputable def ereal_absDist (x y : EReal) : ℝ≥0∞ :=
  if x = y then 0 else if x = ⊥ ∨ x = ⊤ ∨ y = ⊥ ∨ y = ⊤ then ∞ else ENNReal.ofReal |x.toReal - y.toReal|

/-- Definition 6.9.1: the half plane `H_q = {(x, y) ∈ [-∞, ∞]² | x ≤ y}`. -/
def Hq : Type := {p : EReal × EReal // p.1 ≤ p.2}

/-- The distance `d_{H_q}` for `q ∈ [1, ∞]`. -/
noncomputable def Hq.dist (q : ℝ≥0∞) (a b : Hq) : ℝ≥0∞ :=
  if q = ∞ then max (ereal_absDist a.1.1 b.1.1) (ereal_absDist a.1.2 b.1.2)
  else (ereal_absDist a.1.1 b.1.1 ^ q.toReal + ereal_absDist a.1.2 b.1.2 ^ q.toReal) ^ (1 / q.toReal)

/-- The diagonal `Δ ⊆ H_q`. -/
def Hq.diagonal : Set Hq := {a | a.1.1 = a.1.2}

/-- Definition 6.9.2: a persistence diagram: a set `X` with `ψ : X → H_q` such that the
off-diagonal part is countable and each diagonal point has countably infinite fibre. -/
structure PersDiag where
  carrier : Type u
  ψ : carrier → Hq
  countable_offDiag : (ψ ⁻¹' Hq.diagonalᶜ).Countable
  fibres : ∀ d ∈ Hq.diagonal, (ψ ⁻¹' {d}).Countable ∧ (ψ ⁻¹' {d}).Infinite

/-- Definition 6.9.3: the `p`-distortion `dist_p f` of a map `f : X → Y` (with `q`). -/
noncomputable def PersDiag.distortion (p q : ℝ≥0∞) {X Y : PersDiag.{u}} (f : X.carrier → Y.carrier) :
    ℝ≥0∞ :=
  if p = ∞ then ⨆ x, Hq.dist q (X.ψ x) (Y.ψ (f x))
  else (∑' x, Hq.dist q (X.ψ x) (Y.ψ (f x)) ^ p.toReal) ^ (1 / p.toReal)

/-- The underlying category of `PD^p_q`: injective maps commuting with `ψ`. -/
instance : Category.{u} PersDiag.{u} where
  Hom X Y := {f : X.carrier → Y.carrier // Function.Injective f ∧ ∀ x, Y.ψ (f x) = X.ψ x}
  id X := ⟨id, Function.injective_id, fun _ => rfl⟩
  comp f g := ⟨g.1 ∘ f.1, g.2.1.comp f.2.1, fun x => by simp [g.2.2, f.2.2]⟩

/-! Metric facts about `Hq.dist` and the `p`-distortion, used to build `PD^p_q`. -/

theorem ereal_absDist_self (x : EReal) : ereal_absDist x x = 0 := by simp [ereal_absDist]

theorem ereal_absDist_comm (x y : EReal) : ereal_absDist x y = ereal_absDist y x := by
  unfold ereal_absDist
  by_cases h : x = y
  · subst h; rfl
  · have h' : ¬ y = x := fun e => h e.symm
    simp only [h, h', if_false, abs_sub_comm]
    congr 1
    simp only [eq_iff_iff]
    tauto

theorem ereal_absDist_eq_zero {x y : EReal} (h : ereal_absDist x y = 0) : x = y := by
  by_contra hne
  unfold ereal_absDist at h
  rw [if_neg hne] at h
  split_ifs at h with h1
  · exact ENNReal.top_ne_zero h
  · rw [ENNReal.ofReal_eq_zero, abs_nonpos_iff, sub_eq_zero] at h
    push_neg at h1
    obtain ⟨a1, a2, a3, a4⟩ := h1
    apply hne
    have hx : x = ((x.toReal : ℝ) : EReal) := (EReal.coe_toReal a2 a1).symm
    have hy : y = ((y.toReal : ℝ) : EReal) := (EReal.coe_toReal a4 a3).symm
    rw [hx, hy, h]

theorem ereal_absDist_triangle (x y z : EReal) :
    ereal_absDist x z ≤ ereal_absDist x y + ereal_absDist y z := by
  by_cases hxz : x = z
  · subst hxz; simp [ereal_absDist_self]
  by_cases hxy : x = y
  · subst hxy; simp [ereal_absDist_self]
  by_cases hyz : y = z
  · subst hyz; simp [ereal_absDist_self]
  by_cases hinf : x = ⊥ ∨ x = ⊤ ∨ y = ⊥ ∨ y = ⊤ ∨ z = ⊥ ∨ z = ⊤
  · have : ereal_absDist x y = ⊤ ∨ ereal_absDist y z = ⊤ := by
      rcases hinf with h | h | h | h | h | h
      · left; unfold ereal_absDist; rw [if_neg hxy, if_pos (Or.inl h)]
      · left; unfold ereal_absDist; rw [if_neg hxy, if_pos (Or.inr (Or.inl h))]
      · left; unfold ereal_absDist; rw [if_neg hxy, if_pos (Or.inr (Or.inr (Or.inl h)))]
      · left; unfold ereal_absDist; rw [if_neg hxy, if_pos (Or.inr (Or.inr (Or.inr h)))]
      · right; unfold ereal_absDist; rw [if_neg hyz, if_pos (Or.inr (Or.inr (Or.inl h)))]
      · right; unfold ereal_absDist; rw [if_neg hyz, if_pos (Or.inr (Or.inr (Or.inr h)))]
    rcases this with h | h <;> simp [h]
  · push_neg at hinf
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hinf
    simp only [ereal_absDist, hxz, hxy, hyz, if_false, a1, a2, a3, a4, a5, a6, or_self]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    exact abs_sub_le _ _ _

theorem tsum_Lp_add_le {ι : Type*} (f g : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  set A := (∑' i, f i ^ p) ^ (1 / p)
  set B := (∑' i, g i ^ p) ^ (1 / p)
  have key : ∀ s : Finset ι, ∑ i ∈ s, (f i + g i) ^ p ≤ (A + B) ^ p := by
    intro s
    have h1 := ENNReal.Lp_add_le s f g hp
    have h2 : (∑ i ∈ s, f i ^ p) ^ (1 / p) ≤ A :=
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by positivity)
    have h3 : (∑ i ∈ s, g i ^ p) ^ (1 / p) ≤ B :=
      ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by positivity)
    have h4 := h1.trans (add_le_add h2 h3)
    calc ∑ i ∈ s, (f i + g i) ^ p = ((∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
      _ ≤ (A + B) ^ p := ENNReal.rpow_le_rpow h4 hp0.le
  have : ∑' i, (f i + g i) ^ p ≤ (A + B) ^ p := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le key
  calc (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ ((A + B) ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow this (by positivity)
    _ = A + B := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

theorem toReal_ge_one {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞) : 1 ≤ q.toReal := by
  have := ENNReal.toReal_mono hqt hq
  simpa using this

theorem Hq.dist_self (q : ℝ≥0∞) (hq : 1 ≤ q) (a : Hq) : Hq.dist q a a = 0 := by
  unfold Hq.dist
  rw [ereal_absDist_self, ereal_absDist_self]
  split_ifs with h
  · simp
  · have h1 := toReal_ge_one hq h
    have h0 : (0 : ℝ) < q.toReal := lt_of_lt_of_le one_pos h1
    rw [ENNReal.zero_rpow_of_pos h0]
    simp [h0]

theorem Hq.dist_eq_zero (q : ℝ≥0∞) (hq : 1 ≤ q) {a b : Hq} (h : Hq.dist q a b = 0) : a = b := by
  unfold Hq.dist at h
  have key : ereal_absDist a.1.1 b.1.1 = 0 ∧ ereal_absDist a.1.2 b.1.2 = 0 := by
    split_ifs at h with hq'
    · simpa using h
    · have h1 := toReal_ge_one hq hq'
      have h0 : (0 : ℝ) < q.toReal := lt_of_lt_of_le one_pos h1
      have hpos : 0 < 1 / q.toReal := by positivity
      rw [ENNReal.rpow_eq_zero_iff] at h
      rcases h with ⟨h, _⟩ | ⟨_, h⟩
      · have := add_eq_zero.mp h
        refine ⟨?_, ?_⟩
        · exact (ENNReal.rpow_eq_zero_iff_of_pos h0).mp this.1
        · exact (ENNReal.rpow_eq_zero_iff_of_pos h0).mp this.2
      · exact absurd h (not_lt.mpr hpos.le)
  exact Subtype.ext (Prod.ext (ereal_absDist_eq_zero key.1) (ereal_absDist_eq_zero key.2))

theorem Hq.dist_triangle (q : ℝ≥0∞) (hq : 1 ≤ q) (a b c : Hq) :
    Hq.dist q a c ≤ Hq.dist q a b + Hq.dist q b c := by
  have t1 := ereal_absDist_triangle a.1.1 b.1.1 c.1.1
  have t2 := ereal_absDist_triangle a.1.2 b.1.2 c.1.2
  unfold Hq.dist
  split_ifs with hq'
  · refine max_le ?_ ?_
    · exact t1.trans (add_le_add (le_max_left _ _) (le_max_left _ _))
    · exact t2.trans (add_le_add (le_max_right _ _) (le_max_right _ _))
  · have h1 := toReal_ge_one hq hq'
    have h0 : (0 : ℝ) < q.toReal := lt_of_lt_of_le one_pos h1
    set x := ereal_absDist a.1.1 b.1.1
    set y := ereal_absDist a.1.2 b.1.2
    set x' := ereal_absDist b.1.1 c.1.1
    set y' := ereal_absDist b.1.2 c.1.2
    have hmono : (ereal_absDist a.1.1 c.1.1 ^ q.toReal + ereal_absDist a.1.2 c.1.2 ^ q.toReal) ^ (1 / q.toReal)
        ≤ ((x + x') ^ q.toReal + (y + y') ^ q.toReal) ^ (1 / q.toReal) :=
      ENNReal.rpow_le_rpow (add_le_add (ENNReal.rpow_le_rpow t1 h0.le) (ENNReal.rpow_le_rpow t2 h0.le))
        (by positivity)
    refine hmono.trans ?_
    have := ENNReal.Lp_add_le (Finset.univ : Finset Bool) (fun i => if i then x else y)
      (fun i => if i then x' else y') h1
    simpa [Fintype.sum_bool, add_comm] using this

theorem PersDiag.distortion_comp_le (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q) {X Y Z : PersDiag.{u}}
    (f : X.carrier → Y.carrier) (g : Y.carrier → Z.carrier) (hf : Function.Injective f) :
    PersDiag.distortion p q (X := X) (Y := Z) (g ∘ f) ≤
      PersDiag.distortion p q (X := X) (Y := Y) f + PersDiag.distortion p q (X := Y) (Y := Z) g := by
  have tri : ∀ x, Hq.dist q (X.ψ x) (Z.ψ (g (f x))) ≤
      Hq.dist q (X.ψ x) (Y.ψ (f x)) + Hq.dist q (Y.ψ (f x)) (Z.ψ (g (f x))) :=
    fun x => Hq.dist_triangle q hq _ _ _
  unfold PersDiag.distortion
  split_ifs with hp'
  · refine iSup_le fun x => (tri x).trans (add_le_add
      (le_iSup (fun x => Hq.dist q (X.ψ x) (Y.ψ (f x))) x)
      (le_iSup (fun y => Hq.dist q (Y.ψ y) (Z.ψ (g y))) (f x)))
  · have h1 := toReal_ge_one hp hp'
    have h0 : (0 : ℝ) < p.toReal := lt_of_lt_of_le one_pos h1
    calc (∑' x, Hq.dist q (X.ψ x) (Z.ψ ((g ∘ f) x)) ^ p.toReal) ^ (1 / p.toReal)
        ≤ (∑' x, (Hq.dist q (X.ψ x) (Y.ψ (f x)) + Hq.dist q (Y.ψ (f x)) (Z.ψ (g (f x)))) ^ p.toReal) ^ (1 / p.toReal) :=
          ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun x => ENNReal.rpow_le_rpow (tri x) h0.le)
            (by positivity)
      _ ≤ (∑' x, Hq.dist q (X.ψ x) (Y.ψ (f x)) ^ p.toReal) ^ (1 / p.toReal) +
            (∑' x, Hq.dist q (Y.ψ (f x)) (Z.ψ (g (f x))) ^ p.toReal) ^ (1 / p.toReal) :=
          tsum_Lp_add_le _ _ h1
      _ ≤ _ := by
          refine add_le_add le_rfl (ENNReal.rpow_le_rpow ?_ (by positivity))
          exact ENNReal.tsum_comp_le_tsum_of_injective hf
            (fun y => Hq.dist q (Y.ψ y) (Z.ψ (g y)) ^ p.toReal)

theorem PersDiag.distortion_eq_zero_of_psi (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q)
    {X Y : PersDiag.{u}} (f : X.carrier → Y.carrier) (h : ∀ x, Y.ψ (f x) = X.ψ x) :
    PersDiag.distortion p q (X := X) (Y := Y) f = 0 := by
  unfold PersDiag.distortion
  have hz : ∀ x, Hq.dist q (X.ψ x) (Y.ψ (f x)) = 0 := fun x => by
    rw [h x]; exact Hq.dist_self q hq _
  split_ifs with hp'
  · simp [hz]
  · have h1 := toReal_ge_one hp hp'
    have h0 : (0 : ℝ) < p.toReal := lt_of_lt_of_le one_pos h1
    simp [hz, ENNReal.zero_rpow_of_pos h0, h0]

theorem PersDiag.psi_of_distortion_le_zero (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q)
    {X Y : PersDiag.{u}} (f : X.carrier → Y.carrier)
    (h : PersDiag.distortion p q (X := X) (Y := Y) f ≤ 0) : ∀ x, Y.ψ (f x) = X.ψ x := by
  intro x
  unfold PersDiag.distortion at h
  have hx : Hq.dist q (X.ψ x) (Y.ψ (f x)) = 0 := by
    split_ifs at h with hp'
    · exact le_antisymm ((le_iSup (fun x => Hq.dist q (X.ψ x) (Y.ψ (f x))) x).trans h) bot_le
    · have h1 := toReal_ge_one hp hp'
      have h0 : (0 : ℝ) < p.toReal := lt_of_lt_of_le one_pos h1
      have hpos : 0 < 1 / p.toReal := by positivity
      have h' : (∑' x, Hq.dist q (X.ψ x) (Y.ψ (f x)) ^ p.toReal) = 0 := by
        have h2 := le_antisymm h bot_le
        rcases (ENNReal.rpow_eq_zero_iff.mp h2) with ⟨h3, _⟩ | ⟨_, h3⟩
        · exact h3
        · exact absurd h3 (not_lt.mpr hpos.le)
      have := (ENNReal.tsum_eq_zero.mp h') x
      exact (ENNReal.rpow_eq_zero_iff_of_pos h0).mp this
  exact (Hq.dist_eq_zero q hq hx).symm


/-- Definition 6.9.4 (the structure): the locally persistent category `PD^p_q` of persistence diagrams:
`Hom(X, Y)_ε = {f : X → Y injective | dist_p f ≤ ε}`. -/
noncomputable def pdLPCat (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q) : LPCat PersDiag.{u} where
  hom := fun X Y ε => {f : X.carrier → Y.carrier // Function.Injective f ∧
    PersDiag.distortion p q (X := X) (Y := Y) f ≤ ε}
  homZero := fun {X Y} => {
    toFun := fun f => ⟨f.1, f.2.1, by
      have := (PersDiag.distortion_eq_zero_of_psi p q hp hq (X := X) (Y := Y) f.1 f.2.2).le
      simpa using this⟩
    invFun := fun s => ⟨s.1, s.2.1, PersDiag.psi_of_distortion_le_zero p q hp hq s.1 (by
      simpa using s.2.2)⟩
    left_inv := fun f => Subtype.ext rfl
    right_inv := fun s => Subtype.ext rfl }
  comp := fun {X Y Z ε δ} g f => ⟨g.1 ∘ f.1, g.2.1.comp f.2.1,
    (PersDiag.distortion_comp_le p q hp hq f.1 g.1 f.2.1).trans (by
      push_cast; exact add_le_add f.2.2 g.2.2)⟩
  S := fun {X Y ε δ} h f => ⟨f.1, f.2.1, f.2.2.trans (by exact_mod_cast h)⟩
  id_comp := fun f => Subtype.ext rfl
  comp_id := fun f => Subtype.ext rfl
  assoc := fun f g h => Subtype.ext rfl
  S_refl := fun f => Subtype.ext rfl
  S_trans := fun h₁ h₂ f => Subtype.ext rfl
  comp_S := fun hε hδ f g => Subtype.ext rfl
  homZero_comp := fun f g => Subtype.ext rfl

/-- Definition 6.9.4: the locally persistent category `PD^p_q` of persistence diagrams:
`Hom(X, Y)_ε = {f : X → Y injective | dist_p f ≤ ε}`. -/
theorem exists_pd_lpcat (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∃ L : LPCat PersDiag.{u}, ∀ (X Y : PersDiag.{u}) (ε : ℝ≥0),
      L.hom X Y ε = {f : X.carrier → Y.carrier // Function.Injective f ∧
        PersDiag.distortion p q (X := X) (Y := Y) f ≤ ε} :=
  ⟨pdLPCat p q hp hq, fun _ _ _ => rfl⟩

/-- The `ℓ^p[ℓ^q]` matching (Wasserstein) distance:
`inf_{bijections e} max (dist_p e, dist_p e⁻¹)`. -/
noncomputable def matchingDist (p q : ℝ≥0∞) (X Y : PersDiag.{u}) : ℝ≥0∞ :=
  ⨅ e : X.carrier ≃ Y.carrier, max (PersDiag.distortion p q (X := X) (Y := Y) e)
    (PersDiag.distortion p q (X := Y) (Y := X) e.symm)

/-- Proposition 6.9.5: the interleaving distance of `PD^p_q` is the `ℓ^p[ℓ^q]` matching
distance.

**Note.** Describing the hom-sets does not determine the locally
persistent structure (the composition could differ), so Lean states the result for the canonical
structure `pdLPCat` of Definition 6.9.4 (composition of maps). -/
theorem pd_interleavingDist_eq_matchingDist (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (X Y : PersDiag.{u}) :
    @interleavingDist PersDiag.{u} _ (pdLPCat p q hp hq) X Y = matchingDist p q X Y := by
  letI := pdLPCat p q hp hq
  apply le_antisymm
  · refine le_iInf fun e => ?_
    by_cases hm : max (PersDiag.distortion p q (X := X) (Y := Y) e)
        (PersDiag.distortion p q (X := Y) (Y := X) e.symm) = ⊤
    · rw [hm]; exact le_top
    · lift max (PersDiag.distortion p q (X := X) (Y := Y) e)
        (PersDiag.distortion p q (X := Y) (Y := X) e.symm) to ℝ≥0 using hm with δ hδ
      refine iInf₂_le_of_le δ ?_ le_rfl
      refine ⟨⟨⟨e, e.injective, (le_max_left _ _).trans hδ.symm.le⟩,
        ⟨e.symm, e.symm.injective, (le_max_right _ _).trans hδ.symm.le⟩, ?_, ?_⟩⟩
      · exact Subtype.ext (funext fun x => e.symm_apply_apply x)
      · exact Subtype.ext (funext fun y => e.apply_symm_apply y)
  · refine le_iInf₂ fun δ hδ => ?_
    obtain ⟨⟨f, g, hfg1, hfg2⟩⟩ := hδ
    let e : X.carrier ≃ Y.carrier :=
      { toFun := f.1
        invFun := g.1
        left_inv := fun x => congrFun (congrArg Subtype.val hfg1) x
        right_inv := fun y => congrFun (congrArg Subtype.val hfg2) y }
    exact (iInf_le _ e).trans (max_le f.2.2 g.2.2)

end SimplicialAndDiagrams

end ScoccolaPhd
