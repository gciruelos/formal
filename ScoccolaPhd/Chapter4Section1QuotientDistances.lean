import Mathlib
import ScoccolaPhd.Chapter3Section2PowersLimits

/-!
# §§4.1–4.5: the quotient interleaving distance

Contents:
* Chapter 4.1–4.2: Characterization of the quotient interleaving distance; stability
* Chapter 4.3–4.5: Complete, intrinsic and geodesic interleaving distances
-/

universe u v u' v' w

namespace ScoccolaPhd

/-! ## Chapter 4.1–4.2: Characterization of the quotient interleaving distance; stability

Proved: Theorem 4.1.4, Lemma 4.2.1, Theorem 4.2.2 (Theorem A) and Theorem 4.2.3;
Lemma 4.1.5 is `sorry`. -/

section Quotient

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

open LPCat

section Characterization

variable {C : Type u} [Category.{v} C] [LPCat C] (W : MorphismProperty C)

/-- Definition 4.1.1: `x` and `y` are `δ`-quotient interleaved. -/
def IsQuotientInterleaved (x y : C) (δ : ℝ≥0) : Prop :=
  ∃ x' y' : C, WeaklyEquivalent W x' x ∧ WeaklyEquivalent W y' y ∧ IsInterleaved x' y' δ

/-- `x` and `y` are connected by a span of acyclic morphisms `x ← c → y`. -/
def Span (x y : C) : Prop := ∃ (c : C) (e : c ⟶ x) (g : c ⟶ y), W e ∧ W g

variable {W}

theorem Span.symm {x y : C} (h : Span W x y) : Span W y x := by
  obtain ⟨c, e, g, he, hg⟩ := h
  exact ⟨c, g, e, hg, he⟩

theorem Span.refl [W.IsMultiplicative] (x : C) : Span W x x :=
  ⟨x, 𝟙 x, 𝟙 x, MorphismProperty.id_mem _ _, MorphismProperty.id_mem _ _⟩

theorem span_trans [W.IsMultiplicative] (hW : IsStableUnderWeightedPullbacks W) {x y z : C}
    (h₁ : Span W x y) (h₂ : Span W y z) : Span W x z := by
  obtain ⟨c, e, f, he, hf⟩ := h₁
  obtain ⟨c', e', f', he', hf'⟩ := h₂
  obtain ⟨⟨P⟩, hP⟩ := hW (homZero f) e' he'
  have h1 : W P.j := hP P
  have h2 : W (homZero.symm P.f) := (hW (homZero e') f hf).2 P.swap0
  exact ⟨P.p, P.j ≫ e, homZero.symm P.f ≫ f', MorphismProperty.comp_mem _ _ _ h1 he,
    MorphismProperty.comp_mem _ _ _ h2 hf'⟩

theorem span_of_weaklyEquivalent [W.IsMultiplicative]
    (hW : IsStableUnderWeightedPullbacks W) {x y : C} (h : WeaklyEquivalent W x y) :
    Span W x y := by
  induction h with
  | rel a b hab =>
    obtain ⟨f, hf⟩ := hab
    exact ⟨a, 𝟙 a, f, MorphismProperty.id_mem _ _, hf⟩
  | refl a => exact Span.refl a
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact span_trans hW ih₁ ih₂

theorem weaklyEquivalent_of_span {x y : C} (h : Span W x y) : WeaklyEquivalent W x y := by
  obtain ⟨c, e, g, he, hg⟩ := h
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨e, he⟩))
    (Relation.EqvGen.rel _ _ ⟨g, hg⟩)

/-- Pulling an interleaving back along an acyclic morphism (Proposition 3.2.11). -/
theorem pull_interleaving (hW : IsStableUnderWeightedPullbacks W) {c x y : C} (e : c ⟶ x)
    (he : W e) {δ : ℝ≥0} (h : IsInterleaved x y δ) :
    ∃ (y' : C) (v : y' ⟶ y), W v ∧ IsInterleaved c y' δ := by
  obtain ⟨⟨f, g, hp⟩⟩ := h
  obtain ⟨⟨P⟩, hP⟩ := hW g e he
  obtain ⟨g', ⟨hg', _⟩, _⟩ := P.interleaving f ⟨hp.2, hp.1⟩
  exact ⟨P.p, P.j, hP P, ⟨⟨g', P.f, hg'.2, hg'.1⟩⟩⟩

theorem IsQuotientInterleaved.symm {x y : C} {δ : ℝ≥0} (h : IsQuotientInterleaved W x y δ) :
    IsQuotientInterleaved W y x δ := by
  obtain ⟨x', y', hx, hy, h⟩ := h
  exact ⟨y', x', hy, hx, h.symm⟩

theorem IsQuotientInterleaved.of_rel {x x₂ y y₂ : C} {δ : ℝ≥0}
    (hx : WeaklyEquivalent W x x₂) (hy : WeaklyEquivalent W y y₂)
    (h : IsQuotientInterleaved W x₂ y₂ δ) : IsQuotientInterleaved W x y δ := by
  have hE : Equivalence (WeaklyEquivalent W) := weaklyEquivalent_equivalence W
  obtain ⟨x', y', hx', hy', h⟩ := h
  exact ⟨x', y', hE.trans hx' (hE.symm hx), hE.trans hy' (hE.symm hy), h⟩

theorem isQuotientInterleaved_trans [W.IsMultiplicative]
    (hW : IsStableUnderWeightedPullbacks W) {x y z : C} {δ₁ δ₂ : ℝ≥0}
    (h₁ : IsQuotientInterleaved W x y δ₁) (h₂ : IsQuotientInterleaved W y z δ₂) :
    IsQuotientInterleaved W x z (δ₁ + δ₂) := by
  have hE : Equivalence (WeaklyEquivalent W) := weaklyEquivalent_equivalence W
  obtain ⟨x', y', hx', hy', hxy⟩ := h₁
  obtain ⟨y'', z', hy'', hz', hyz⟩ := h₂
  obtain ⟨c, e₁, e₂, he₁, he₂⟩ :=
    span_of_weaklyEquivalent hW (hE.trans hy' (hE.symm hy''))
  obtain ⟨x'', v₁, hv₁, hcx⟩ := pull_interleaving hW e₁ he₁ hxy.symm
  obtain ⟨z'', v₂, hv₂, hcz⟩ := pull_interleaving hW e₂ he₂ hyz
  exact ⟨x'', z'', hE.trans (Relation.EqvGen.rel _ _ ⟨v₁, hv₁⟩) hx',
    hE.trans (Relation.EqvGen.rel _ _ ⟨v₂, hv₂⟩) hz', hcx.symm.trans hcz⟩

/-- The infimum of the `δ` such that `x` and `y` are `δ`-quotient interleaved. -/
noncomputable def qiDist (W : MorphismProperty C) (x y : C) : ℝ≥0∞ :=
  ⨅ (δ : ℝ≥0) (_ : IsQuotientInterleaved W x y δ), (δ : ℝ≥0∞)

theorem qiDist_le_of_rel {x x₂ y y₂ : C} (hx : WeaklyEquivalent W x x₂)
    (hy : WeaklyEquivalent W y y₂) : qiDist W x y ≤ qiDist W x₂ y₂ :=
  le_iInf₂ fun δ h => iInf₂_le_of_le δ (h.of_rel hx hy) le_rfl

theorem qiDist_isEPMetric [W.IsMultiplicative] (hW : IsStableUnderWeightedPullbacks W) :
    IsEPMetric (qiDist W (C := C)) :=
  isEPMetric_iInf (fun x y a => IsQuotientInterleaved W x y a)
    (fun x => ⟨x, x, Relation.EqvGen.refl _, Relation.EqvGen.refl _, IsInterleaved.refl x⟩)
    (fun _ _ _ h => h.symm) (fun _ _ _ _ _ h₁ h₂ => isQuotientInterleaved_trans hW h₁ h₂)

theorem qiDist_le_interleavingDist (x y : C) :
    qiDist W x y ≤ interleavingDist x y :=
  le_iInf₂ fun δ h => iInf₂_le_of_le δ ⟨x, y, Relation.EqvGen.refl _,
    Relation.EqvGen.refl _, h⟩ le_rfl

/-- Theorem 4.1.4 (first equality): the quotient interleaving distance is the infimum of the
`δ` such that `x` and `y` are `δ`-quotient interleaved. -/
theorem quotientInterleavingDist_eq_inf_quotientInterleaved [W.IsMultiplicative]
    (hW : IsStableUnderWeightedPullbacks W) (x y : C) :
    quotientInterleavingDist W x y =
      ⨅ (δ : ℝ≥0) (_ : IsQuotientInterleaved W x y δ), (δ : ℝ≥0∞) := by
  have hE : Equivalence (WeaklyEquivalent W) := weaklyEquivalent_equivalence W
  apply le_antisymm
  · refine le_iInf₂ fun δ h => ?_
    obtain ⟨x', y', hx', hy', h⟩ := h
    calc quotientInterleavingDist W x y
        = quotientDist interleavingDist (WeaklyEquivalent W) x' y' :=
          quotientDist_isInvariant _ _ hE x x' y y' (hE.symm hx') (hE.symm hy')
      _ ≤ interleavingDist x' y' := quotientDist_le _ _ _ _
      _ ≤ δ := iInf₂_le_of_le δ h le_rfl
  · exact le_quotientDist _ _ (qiDist W) (qiDist_isEPMetric hW) (qiDist_le_interleavingDist)
      (fun x x' y y' hx hy => le_antisymm (qiDist_le_of_rel hx hy)
        (qiDist_le_of_rel (hE.symm hx) (hE.symm hy))) x y

theorem exists_acyclicCover [W.IsMultiplicative] (hW : IsStableUnderWeightedPullbacks W)
    {x y : C} {δ : ℝ≥0} (h : IsQuotientInterleaved W x y δ) :
    ∃ (x' y' : C) (u : x' ⟶ x) (v : y' ⟶ y), W u ∧ W v ∧ IsInterleaved x' y' δ := by
  obtain ⟨x', y', hx', hy', h⟩ := h
  obtain ⟨c₁, e₁, k₁, he₁, hk₁⟩ := span_of_weaklyEquivalent hW hx'
  obtain ⟨c₂, e₂, k₂, he₂, hk₂⟩ := span_of_weaklyEquivalent hW hy'
  obtain ⟨y₁, v₁, hv₁, h₁⟩ := pull_interleaving hW e₁ he₁ h
  obtain ⟨q, s₁, s₂, hs₁, hs₂⟩ := span_trans hW
    (⟨y₁, 𝟙 y₁, v₁, MorphismProperty.id_mem _ _, hv₁⟩ : Span W y₁ y')
    (⟨c₂, e₂, 𝟙 c₂, he₂, MorphismProperty.id_mem _ _⟩ : Span W y' c₂)
  obtain ⟨c₁', w, hw, h₂⟩ := pull_interleaving hW s₁ hs₁ h₁.symm
  exact ⟨c₁', q, w ≫ k₁, s₂ ≫ k₂, MorphismProperty.comp_mem _ _ _ hw hk₁,
    MorphismProperty.comp_mem _ _ _ hs₂ hk₂, h₂.symm⟩

/-- Theorem 4.1.4 (second equality): ... equals the infimum of the `δ` such that there are
acyclic `x' → x`, `y' → y` with `x'`, `y'` `δ`-interleaved. -/
theorem quotientInterleavingDist_eq_inf_acyclicCover [W.IsMultiplicative]
    (hW : IsStableUnderWeightedPullbacks W) (x y : C) :
    quotientInterleavingDist W x y =
      ⨅ (δ : ℝ≥0) (_ : ∃ (x' y' : C) (u : x' ⟶ x) (v : y' ⟶ y),
        W u ∧ W v ∧ IsInterleaved x' y' δ), (δ : ℝ≥0∞) := by
  rw [quotientInterleavingDist_eq_inf_quotientInterleaved hW]
  apply le_antisymm
  · refine le_iInf₂ fun δ h => iInf₂_le_of_le δ ?_ le_rfl
    obtain ⟨x', y', u, v, hu, hv, h⟩ := h
    exact ⟨x', y', Relation.EqvGen.rel _ _ ⟨u, hu⟩, Relation.EqvGen.rel _ _ ⟨v, hv⟩, h⟩
  · exact le_iInf₂ fun δ h => iInf₂_le_of_le δ (exists_acyclicCover hW h) le_rfl

/-- Lemma 4.1.5: if `C` is powered by representables, has pullbacks, powers preserve them,
and `W` is stable under powers by representables and under pullbacks, then `W` is stable
under weighted pullbacks. -/
theorem isStableUnderWeightedPullbacks_of_powered [PoweredByRepresentables C] [HasPullbacks C]
    (hpres : ∀ ε, PreservesLimitsOfShape WalkingCospan
      (PoweredByRepresentables.pow (C := C) ε))
    [W.IsStableUnderBaseChange]
    (hpow : ∀ ε {a b : C} (f : a ⟶ b), W f → W ((PoweredByRepresentables.pow ε).map f)) :
    IsStableUnderWeightedPullbacks W := by
  intro a b c ε h k hk
  refine ⟨exists_weightedPullback hpres h k, fun P => ?_⟩
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback P.isPullback.flip (hpow ε k hk)

end Characterization

section Stability

/-- Lemma 4.2.1: a distance non-increasing map sending `R`-related to `R'`-related points
is distance non-increasing for the quotient ep metrics. -/
theorem quotientDist_map_le {X : Type u} {X' : Type u'} (d : X → X → ℝ≥0∞)
    (d' : X' → X' → ℝ≥0∞) (hd : IsEPMetric d) (hd' : IsEPMetric d') (f : X → X')
    (hf : ∀ x y, d' (f x) (f y) ≤ d x y) (R : X → X → Prop) (R' : X' → X' → Prop)
    (hR : Equivalence R) (hR' : Equivalence R') (hfR : ∀ x y, R x y → R' (f x) (f y)) :
    ∀ x y, quotientDist d' R' (f x) (f y) ≤ quotientDist d R x y := by
  intro x y
  refine le_quotientDist d R (fun a b => quotientDist d' R' (f a) (f b)) ?_ ?_ ?_ x y
  · have hq := quotientDist_isEPMetric d' R'
    exact ⟨fun a => hq.refl _, fun a b => hq.symm _ _, fun a b c => hq.triangle _ _ _⟩
  · exact fun a b => (quotientDist_le d' R' _ _).trans (hf a b)
  · intro a a' b b' ha hb
    exact quotientDist_isInvariant d' R' hR' _ _ _ _ (hfR _ _ ha) (hfR _ _ hb)

variable {C : Type u} [Category.{v} C] [LPCat C] {D : Type u'} [Category.{v'} D] [LPCat D]

/-- Theorem 4.2.2 (Theorem A for related objects): a locally persistent functor mapping
`W`-related objects to `W'`-related objects is distance non-increasing for the quotient
interleaving distances. -/
theorem LPFunctor.quotientInterleavingDist_le (F : LPFunctor C D) (W : MorphismProperty C)
    (W' : MorphismProperty D) [W.IsMultiplicative] [W'.IsMultiplicative]
    (hF : ∀ x y, WeaklyEquivalent W x y →
      WeaklyEquivalent W' (F.toFunctor.obj x) (F.toFunctor.obj y)) (x y : C) :
    quotientInterleavingDist W' (F.toFunctor.obj x) (F.toFunctor.obj y) ≤
      quotientInterleavingDist W x y := by
  exact quotientDist_map_le _ _ interleavingDist_isEPMetric interleavingDist_isEPMetric
    F.toFunctor.obj (fun a b => F.interleavingDist_le a b) _ _
    (weaklyEquivalent_equivalence W) (weaklyEquivalent_equivalence W') hF x y

/-- Theorem A (4.2.2, acyclic-morphism form): a locally persistent functor mapping acyclic
morphisms to acyclic morphisms is 1-Lipschitz for the quotient interleaving distances. -/
theorem LPFunctor.quotientInterleavingDist_le_of_acyclic (F : LPFunctor C D)
    (W : MorphismProperty C) (W' : MorphismProperty D) [W.IsMultiplicative]
    [W'.IsMultiplicative] (hF : ∀ ⦃x y : C⦄ (f : x ⟶ y), W f → W' (F.toFunctor.map f))
    (x y : C) :
    quotientInterleavingDist W' (F.toFunctor.obj x) (F.toFunctor.obj y) ≤
      quotientInterleavingDist W x y := by
  refine F.quotientInterleavingDist_le W W' (fun a b hab => ?_) x y
  induction hab with
  | rel a b h =>
    obtain ⟨f, hf⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨F.toFunctor.map f, hF f hf⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Theorem 4.2.3 (1-Lipschitz case): if `W` is stable under weighted pullbacks and
`f : obj C → P` sends `W`-related objects to points at distance 0 and is distance
non-increasing for the interleaving distance, it is so for the quotient interleaving
distance. -/
theorem lipschitz_quotientInterleavingDist (W : MorphismProperty C) [W.IsMultiplicative]
    (hW : IsStableUnderWeightedPullbacks W) {P : Type u'} [PseudoEMetricSpace P] (f : C → P)
    (hf₀ : ∀ x y, WeaklyEquivalent W x y → edist (f x) (f y) = 0)
    (hf : ∀ x y, edist (f x) (f y) ≤ interleavingDist x y) (x y : C) :
    edist (f x) (f y) ≤ quotientInterleavingDist W x y := by
  refine le_quotientDist _ _ (fun a b => edist (f a) (f b))
    ⟨fun a => edist_self _, fun a b => edist_comm _ _, fun a b c => edist_triangle _ _ _⟩ hf ?_ x y
  intro a a' b b' ha hb
  have e₁ := hf₀ _ _ ha
  have e₂ := hf₀ _ _ hb
  apply le_antisymm
  · calc edist (f a) (f b) ≤ edist (f a) (f a') + edist (f a') (f b') + edist (f b') (f b) :=
          edist_triangle4 _ _ _ _
      _ = edist (f a') (f b') := by rw [e₁, edist_comm (f b'), e₂]; simp
  · calc edist (f a') (f b') ≤ edist (f a') (f a) + edist (f a) (f b) + edist (f b) (f b') :=
          edist_triangle4 _ _ _ _
      _ = edist (f a) (f b) := by rw [edist_comm, e₁, e₂]; simp

/-- Theorem 4.2.3 (uniformly continuous case). -/
theorem uniformContinuous_quotientInterleavingDist (W : MorphismProperty C)
    [W.IsMultiplicative] (hW : IsStableUnderWeightedPullbacks W) {P : Type u'}
    [PseudoEMetricSpace P] (f : C → P)
    (hf₀ : ∀ x y, WeaklyEquivalent W x y → edist (f x) (f y) = 0)
    (hf : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x y, interleavingDist x y < δ →
      edist (f x) (f y) < ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x y, quotientInterleavingDist W x y < δ →
      edist (f x) (f y) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  rw [quotientInterleavingDist_eq_inf_quotientInterleaved hW, iInf_lt_iff] at hxy
  obtain ⟨r, hr⟩ := hxy
  rw [iInf_lt_iff] at hr
  obtain ⟨⟨x', y', hx, hy, hint⟩, hlt⟩ := hr
  have hd : interleavingDist x' y' < δ := lt_of_le_of_lt (iInf₂_le r hint) hlt
  calc edist (f x) (f y) ≤ edist (f x) (f x') + edist (f x') (f y') + edist (f y') (f y) :=
        edist_triangle4 _ _ _ _
    _ = edist (f x') (f y') := by rw [edist_comm, hf₀ _ _ hx, hf₀ _ _ hy]; simp
    _ < ε := hfδ _ _ hd

end Stability

end Quotient

/-! ## Chapter 4.3–4.5: Complete, intrinsic and geodesic interleaving distances

Proved: Theorem 4.3.1 and Corollary 4.3.2 (Theorem 4.3.3 is in `QuotientComplete.lean`).
The 4.4–4.5 statements are `sorry`.
Proposition 4.5.12 (finitely presented multi-persistent modules) is omitted. -/

section Distances

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal Topology

open LPCat

variable {C : Type u} [Category.{v} C] [LPCat C]

/-- Shifting preserves interleavings. -/
theorem IsInterleavingPair.S {x y : C} {δ δ' : ℝ≥0} (h : δ ≤ δ') {f : hom x y δ}
    {g : hom y x δ} (hp : IsInterleavingPair f g) :
    IsInterleavingPair (LPCat.S h f) (LPCat.S h g) := by
  obtain ⟨h₁, h₂⟩ := hp
  constructor
  · rw [LPCat.comp_S h h f g, h₁, LPCat.S_trans]
  · rw [LPCat.comp_S h h g f, h₂, LPCat.S_trans]

theorem IsInterleaved.mono {x y : C} {δ δ' : ℝ≥0} (hle : δ ≤ δ') (h : IsInterleaved x y δ) :
    IsInterleaved x y δ' := by
  obtain ⟨⟨f, g, hp⟩⟩ := h
  exact ⟨⟨LPCat.S hle f, LPCat.S hle g, IsInterleavingPair.S hle hp⟩⟩

theorem isInterleaved_of_dist_lt {x y : C} {ε : ℝ≥0} (h : interleavingDist x y < ε) :
    IsInterleaved x y ε := by
  unfold interleavingDist at h
  rw [iInf_lt_iff] at h
  obtain ⟨δ, hδ⟩ := h
  rw [iInf_lt_iff] at hδ
  obtain ⟨hi, hlt⟩ := hδ
  exact IsInterleaved.mono (by exact_mod_cast hlt.le) (show IsInterleaved x y δ from hi)

/-! ### 4.3 Complete interleaving distances -/

/-- Theorem 4.3.1: if `C` admits weighted sequential limits, `d_I` is complete. -/
theorem interleavingDist_complete (h : HasWeightedSeqLimits C) :
    IsCompleteDist (interleavingDist (C := C)) := by
  intro x hx
  have hE := interleavingDist_isEPMetric (C := C)
  let ε : ℕ → ℝ≥0 := fun k => 2⁻¹ ^ k
  have hεpos : ∀ k, (0 : ℝ≥0∞) < (ε k : ℝ≥0∞) := fun k => by
    simp [ε, pow_pos]
  choose M hM using fun k => hx _ (hεpos k)
  let N : ℕ → ℕ := fun k => k + (Finset.range (k + 1)).sup M
  have hN : ∀ k, M k ≤ N k := fun k =>
    le_add_left (Finset.le_sup (f := M) (Finset.mem_range.2 (Nat.lt_succ_self k)))
  have hN' : ∀ k, M k ≤ N (k + 1) := fun k =>
    le_add_left (Finset.le_sup (f := M) (Finset.mem_range.2 (by omega)))
  have hpair : ∀ k, IsInterleaved (x (N (k + 1))) (x (N k)) (ε k) := fun k =>
    isInterleaved_of_dist_lt (hM k _ _ (hN' k) (hN k))
  let I : ∀ k, Interleaving (x (N (k + 1))) (x (N k)) (ε k) (ε k) := fun k => (hpair k).some
  have hsum : HasSum ε (1 - 2⁻¹)⁻¹ := NNReal.hasSum_geometric (by norm_num)
  let D : SeqDiagram C := ⟨(1 - 2⁻¹)⁻¹, ε, hsum, fun k => x (N k), fun k => (I k).f⟩
  obtain ⟨L⟩ := h D
  obtain ⟨k, ⟨hk, _⟩, _⟩ := L.interleaving ε hsum.summable (fun i => (I i).g)
    (fun i => (I i).isPair)
  have hint : ∀ i, IsInterleaved L.l (x (N i)) (tailSum ε i) := fun i => ⟨⟨L.g i, k i, hk i⟩⟩
  have hdist : ∀ i, interleavingDist (x (N i)) L.l ≤ (tailSum ε i : ℝ≥0∞) := fun i => by
    rw [(hE.symm _ _)]
    exact iInf₂_le (tailSum ε i) (hint i)
  have htail : Filter.Tendsto (fun i => tailSum ε i) Filter.atTop (𝓝 0) := by
    have := NNReal.tendsto_sum_nat_add ε
    simpa [tailSum, add_comm] using this
  refine ⟨L.l, ?_⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro r hr
  have hr2 : (0 : ℝ≥0∞) < r / 2 := ENNReal.half_pos hr.ne'
  obtain ⟨N0, hN0⟩ := hx _ hr2
  have hev : ∀ᶠ i in Filter.atTop, (tailSum ε i : ℝ≥0∞) < r / 2 := by
    have := (ENNReal.tendsto_coe.2 htail)
    exact this.eventually (gt_mem_nhds (by simpa using hr2))
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 hev
  refine Filter.eventually_atTop.2 ⟨N0, fun i hi => ?_⟩
  set kk := max k0 N0
  have hNk : N0 ≤ N kk := le_trans (le_max_right _ _) (Nat.le_add_right _ _)
  calc interleavingDist (x i) L.l
      ≤ interleavingDist (x i) (x (N kk)) + interleavingDist (x (N kk)) L.l :=
        hE.triangle _ _ _
    _ ≤ r / 2 + r / 2 := add_le_add (hN0 _ _ hi hNk).le
        ((hdist kk).trans (hk0 kk (le_max_left _ _)).le)
    _ = r := ENNReal.add_halves r

/-- Corollary 4.3.2: for `D` with sequential limits, the locally persistent category `D^ℝ`
has weighted sequential limits and its interleaving distance is complete. -/
theorem persistent_complete (D : Type u) [Category.{v} D] [HasLimitsOfShape ℕᵒᵖ D] :
    @HasWeightedSeqLimits (ℝ ⥤ D) _ (persistentLPCat D) ∧
      @IsCompleteDist (ℝ ⥤ D) (@interleavingDist (ℝ ⥤ D) _ (persistentLPCat D)) := by
  letI := persistentLPCat D
  exact ⟨persistent_hasWeightedSeqLimits, interleavingDist_complete persistent_hasWeightedSeqLimits⟩

/-- A class `W` of morphisms is closed under sequential limits (Section 2.1): the induced
morphism from the limit of a sequential diagram of morphisms in `W` to each object is in
`W`. -/
def IsClosedUnderSequentialLimits (W : MorphismProperty C) : Prop :=
  ∀ (X : ℕᵒᵖ ⥤ C) (c : Cone X), CategoryTheory.Limits.IsLimit c → (∀ {i j : ℕᵒᵖ} (f : i ⟶ j), W (X.map f)) →
    ∀ n, W (c.π.app n)

-- Theorem C (4.3.3) `quotientInterleavingDist_complete` is proved in
-- `Chapter4QuotientComplete.lean`.

/-! ### 4.4 Intrinsic interleaving distances -/

/-- Definition 4.4.1: a coherent factorization of an `ε`-interleaving: objects `z r` for
`r ∈ [0, ε]` and interleavings `f_{r,r'} : z r ↔_{r'-r} z r' : g_{r,r'}`.

**Gap (imprecise).** Definition 4.4.1 requires `z 0 = x` and `z ε = y` on the nose, which fails
for `ε = 0` between distinct isomorphic objects, and midpoint constructions only produce
endpoint isomorphisms (`0`-interleavings). Furthermore, the composition identities
`f_{r',r''} ∘ f_{r,r'} = f_{r,r''}` are neither used in Theorem 4.4.2 nor proved in the thesis
for terminal midpoints (the thesis on p. 78 asserts without proof that midpoints give coherent
factorizations; see also p. 64). We formalize the factorization with endpoint `0`-interleavings
and interleaving pairs `(f_{r,r'}, g_{r,r'})`. -/
structure CoherentFactorization (C : Type u) [Category.{v} C] [LPCat C] (ε : ℝ≥0) where
  z : Set.Icc (0 : ℝ≥0) ε → C
  f : ∀ r r' : Set.Icc (0 : ℝ≥0) ε, r ≤ r' → hom (z r) (z r') ((r' : ℝ≥0) - r)
  g : ∀ r r' : Set.Icc (0 : ℝ≥0) ε, r ≤ r' → hom (z r') (z r) ((r' : ℝ≥0) - r)
  pair : ∀ r r' h, IsInterleavingPair (f r r' h) (g r r' h)

/-- The endpoint `0 ∈ [0, ε]`. -/
def lo (ε : ℝ≥0) : Set.Icc (0 : ℝ≥0) ε := ⟨0, le_rfl, zero_le⟩

/-- The endpoint `ε ∈ [0, ε]`. -/
def hi (ε : ℝ≥0) : Set.Icc (0 : ℝ≥0) ε := ⟨ε, zero_le, le_rfl⟩

theorem lo_le_hi (ε : ℝ≥0) : lo ε ≤ hi ε := by
  show (0 : ℝ≥0) ≤ ε
  exact zero_le

/-- `C` admits coherent factorizations of every interleaving: for every `0 < ε` and
`ε`-interleaving `(f, g)` between `x` and `y`, there is a coherent factorization `F`
whose endpoints are `0`-interleaved with `x` and `y`. -/
def AdmitsCoherentFactorizations (C : Type u) [Category.{v} C] [LPCat C] : Prop :=
  ∀ {x y : C} {ε : ℝ≥0} (hε : 0 < ε) (f : hom x y ε) (g : hom y x ε), IsInterleavingPair f g →
    ∃ F : CoherentFactorization C ε,
      IsInterleaved x (F.z (lo ε)) 0 ∧ IsInterleaved (F.z (hi ε)) y 0

theorem interleavingDist_le_of_isInterleaved {x y : C} {δ : ℝ≥0} (h : IsInterleaved x y δ) :
    interleavingDist x y ≤ δ := iInf₂_le δ h

/-- Clamping a real number into `[0, δ]`. -/
noncomputable def clampIcc (δ : ℝ≥0) (t : ℝ) : Set.Icc (0 : ℝ≥0) δ :=
  ⟨(Set.projIcc (0 : ℝ) δ δ.2 t : ℝ).toNNReal, zero_le,
    Real.toNNReal_le_iff_le_coe.2 (Set.projIcc (0 : ℝ) δ δ.2 t).2.2⟩

theorem clampIcc_zero (δ : ℝ≥0) : clampIcc δ 0 = lo δ := by
  apply Subtype.ext
  simp [clampIcc, lo, Set.projIcc]

theorem clampIcc_self (δ : ℝ≥0) : clampIcc δ δ = hi δ := by
  apply Subtype.ext
  simp [clampIcc, hi, Set.projIcc]

theorem edist_clampIcc (δ : ℝ≥0) (t t' : ℝ) :
    edist (clampIcc δ t) (clampIcc δ t') ≤ ENNReal.ofReal |t - t'| := by
  rw [Subtype.edist_eq, edist_dist, NNReal.dist_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have h0 := Set.abs_projIcc_sub_projIcc (a := (0 : ℝ)) (b := δ) δ.2 (c := t) (d := t')
  have e : ∀ u : ℝ, (((Set.projIcc (0 : ℝ) δ δ.2 u : ℝ).toNNReal : ℝ≥0) : ℝ) =
      Set.projIcc (0 : ℝ) δ δ.2 u := fun u => Real.coe_toNNReal _ (Set.projIcc (0 : ℝ) δ δ.2 u).2.1
  simp only [clampIcc, e]
  exact h0

/-- Theorem D (4.4.2): if `C` admits coherent factorizations, every `δ`-interleaving between
`x` and `y` induces a distance non-increasing map `[0, δ] → (obj C, d_I)` from `x` to `y`;
in particular `d_I` is intrinsic. -/
theorem exists_path_of_coherentFactorizations (h : AdmitsCoherentFactorizations C)
    {x y : C} {δ : ℝ≥0} (hδ : 0 < δ) (hxy : IsInterleaved x y δ) :
    ∃ φ : Set.Icc (0 : ℝ≥0) δ → C, φ (lo δ) = x ∧ φ (hi δ) = y ∧
      ∀ r r', interleavingDist (φ r) (φ r') ≤ edist r r' := by
  obtain ⟨⟨f, g, hp⟩⟩ := hxy
  obtain ⟨F, hx, hy⟩ := h hδ f g hp
  have hE := interleavingDist_isEPMetric (C := C)
  have key : ∀ r r' : Set.Icc (0 : ℝ≥0) δ, r ≤ r' →
      interleavingDist (F.z r) (F.z r') ≤ edist r r' := by
    intro r r' hr
    refine (interleavingDist_le_of_isInterleaved
      ⟨⟨F.f r r' hr, F.g r r' hr, F.pair r r' hr⟩⟩).trans ?_
    have hr' : (r : ℝ≥0) ≤ r' := hr
    rw [Subtype.edist_eq, edist_nndist, NNReal.nndist_eq, tsub_eq_zero_of_le hr', zero_max]
  have key_all : ∀ r r' : Set.Icc (0 : ℝ≥0) δ,
      interleavingDist (F.z r) (F.z r') ≤ edist r r' := by
    intro r r'
    rcases le_total r r' with hr | hr
    · exact key r r' hr
    · rw [hE.symm, edist_comm]; exact key r' r hr
  let φ : Set.Icc (0 : ℝ≥0) δ → C := fun r =>
    if r = lo δ then x
    else if r = hi δ then y
    else F.z r
  have hφ0 : φ (lo δ) = x := by simp [φ]
  have hlo_ne_hi : lo δ ≠ hi δ := by
    intro heq
    have : (lo δ : ℝ≥0) = (hi δ : ℝ≥0) := congr_arg Subtype.val heq
    change (0 : ℝ≥0) = δ at this
    exact hδ.ne' this.symm
  have hφ1 : φ (hi δ) = y := by simp [φ, hlo_ne_hi.symm]
  have hdist_φ_F : ∀ r, interleavingDist (φ r) (F.z r) = 0 := by
    intro r
    dsimp [φ]
    split_ifs with hr0 hr1
    · subst hr0
      exact le_antisymm (interleavingDist_le_of_isInterleaved hx) bot_le
    · subst hr1
      have : interleavingDist (F.z (hi δ)) y = 0 :=
        le_antisymm (interleavingDist_le_of_isInterleaved hy) bot_le
      rw [hE.symm, this]
    · exact hE.refl _
  have hdist_F_φ : ∀ r, interleavingDist (F.z r) (φ r) = 0 := by
    intro r; rw [hE.symm, hdist_φ_F]
  refine ⟨φ, hφ0, hφ1, fun r r' => ?_⟩
  calc interleavingDist (φ r) (φ r')
      ≤ interleavingDist (φ r) (F.z r) + interleavingDist (F.z r) (φ r') :=
        hE.triangle _ _ _
    _ = interleavingDist (F.z r) (φ r') := by rw [hdist_φ_F, zero_add]
    _ ≤ interleavingDist (F.z r) (F.z r') + interleavingDist (F.z r') (φ r') :=
        hE.triangle _ _ _
    _ = interleavingDist (F.z r) (F.z r') := by rw [hdist_F_φ, add_zero]
    _ ≤ edist r r' := key_all r r'

lemma exists_short_path (h : AdmitsCoherentFactorizations C)
    {p p' : C} {δ : ℝ≥0} (hδ : 0 < δ) (hint : IsInterleaved p p' δ) :
    ∃ f : ℝ → C, IsPathOn (interleavingDist (C := C)) 0 δ f ∧ f 0 = p ∧ f δ = p' ∧
      pathLength (interleavingDist (C := C)) 0 δ f ≤ δ := by
  obtain ⟨φ, hφ0, hφ1, hφ⟩ := exists_path_of_coherentFactorizations h hδ hint
  let f : ℝ → C := fun t => φ (clampIcc δ t)
  have hf : ∀ s t, interleavingDist (f s) (f t) ≤ ENNReal.ofReal |s - t| :=
    fun s t => (hφ _ _).trans (edist_clampIcc δ s t)
  have hpath : IsPathOn (interleavingDist (C := C)) 0 δ f := by
    intro t _ ε hε
    obtain ⟨η, hη, hηε⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ ε := by
      refine ⟨(min ε 1).toReal, ?_, ?_⟩
      · exact ENNReal.toReal_pos (by simp [hε.ne']) (by simp)
      · rw [ENNReal.ofReal_toReal (by simp)]; exact min_le_left _ _
    refine ⟨η, hη, fun s _ hs => ?_⟩
    calc interleavingDist (f s) (f t) ≤ ENNReal.ofReal |s - t| := hf s t
      _ < ENNReal.ofReal η := (ENNReal.ofReal_lt_ofReal_iff hη).2 hs
      _ ≤ ε := hηε
  have hlen : pathLength (interleavingDist (C := C)) 0 δ f ≤ δ := by
    refine iSup_le fun N => iSup_le fun y => iSup_le fun hy0 => iSup_le fun hyN =>
      iSup_le fun hmono => ?_
    calc ∑ i ∈ Finset.range N, interleavingDist (f (y i)) (f (y (i + 1)))
        ≤ ∑ i ∈ Finset.range N, ENNReal.ofReal (y (i + 1) - y i) := by
          refine Finset.sum_le_sum fun i _ => (hf _ _).trans ?_
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hmono (Nat.le_succ i)))]
      _ = ENNReal.ofReal (y N - y 0) := by
          rw [← ENNReal.ofReal_sum_of_nonneg
            (fun i _ => sub_nonneg.2 (hmono (Nat.le_succ i))), Finset.sum_range_sub (fun i => y i)]
      _ = δ := by rw [hy0, hyN]; simp
  refine ⟨f, hpath, ?_, ?_, hlen⟩
  · show φ (clampIcc δ 0) = p
    rw [clampIcc_zero]; exact hφ0
  · show φ (clampIcc δ δ) = p'
    rw [clampIcc_self]; exact hφ1

lemma path_le_of_isInterleaved (h : AdmitsCoherentFactorizations C)
    {p p' : C} {δ : ℝ≥0} (hδ : 0 < δ) (hint : IsInterleaved p p' δ) :
    (⨅ (a : ℝ) (b : ℝ) (f : ℝ → C) (_ : a ≤ b) (_ : IsPathOn interleavingDist a b f)
      (_ : f a = p) (_ : f b = p'), pathLength interleavingDist a b f) ≤ (δ : ℝ≥0∞) := by
  obtain ⟨f, hpath, h0, h1, hlen⟩ := exists_short_path h hδ hint
  exact iInf_le_of_le 0 (iInf_le_of_le δ (iInf_le_of_le f (iInf_le_of_le δ.2
    (iInf_le_of_le hpath (iInf_le_of_le h0 (iInf_le_of_le h1 hlen))))))

lemma interleavingDist_le_pathLength {a b : ℝ} {f : ℝ → C} (hab : a ≤ b) :
    interleavingDist (f a) (f b) ≤ pathLength (interleavingDist (C := C)) a b f := by
  refine le_iSup_of_le 1 (le_iSup_of_le (fun n => if n = 0 then a else b) ?_)
  refine le_iSup_of_le (by simp) (le_iSup_of_le (by simp) (le_iSup_of_le ?_ ?_))
  · intro m n hmn
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all
  · simp

lemma le_of_forall_pos {L : ℝ≥0∞} (h : ∀ ε : ℝ≥0, 0 < ε → L ≤ (ε : ℝ≥0∞)) : L ≤ 0 :=
  ENNReal.le_of_forall_pos_le_add fun ε hε _ => by simpa using h ε hε

/-- Theorem 4.4.2 (intrinsic part). -/
theorem interleavingDist_intrinsic (h : AdmitsCoherentFactorizations C) :
    IsIntrinsicDist (interleavingDist (C := C)) := by
  intro p p'
  apply le_antisymm
  · refine le_iInf fun a => le_iInf fun b => le_iInf fun f => le_iInf fun hab => le_iInf fun _ =>
      le_iInf fun hfa => le_iInf fun hfb => ?_
    rw [← hfa, ← hfb]
    refine le_iSup_of_le 1 (le_iSup_of_le (fun n => if n = 0 then a else b) ?_)
    refine le_iSup_of_le (by simp) (le_iSup_of_le (by simp) (le_iSup_of_le ?_ ?_))
    · intro m n hmn
      by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all
    · simp
  · unfold interleavingDist
    refine le_iInf fun δ => le_iInf fun hδ => ?_
    by_cases hδ0 : δ = 0
    · subst hδ0
      apply le_of_forall_pos
      intro ε hε
      exact path_le_of_isInterleaved h hε (IsInterleaved.mono zero_le hδ)
    · have hδ_pos : 0 < δ := lt_of_le_of_ne zero_le (Ne.symm hδ0)
      exact path_le_of_isInterleaved h hδ_pos hδ

/-- Proposition 3.2.18 consequence: terminal midpoints give coherent factorizations. -/
theorem admitsCoherentFactorizations_of_midpoints (h : HasTerminalMidpoints C) :
    AdmitsCoherentFactorizations C := by
  intro x y ε _ f g hfg
  have h_add (r : Set.Icc (0 : ℝ≥0) ε) : (r : ℝ≥0) + (ε - (r : ℝ≥0)) = ε :=
    add_tsub_cancel_of_le r.2.2
  let M (r : Set.Icc (0 : ℝ≥0) ε) : TerminalMidpoint f g (r : ℝ≥0) (ε - (r : ℝ≥0)) (h_add r) :=
    (h f g hfg (r : ℝ≥0) (ε - (r : ℝ≥0)) (h_add r)).some
  have h_comp (r r' : Set.Icc (0 : ℝ≥0) ε) (hr : r ≤ r') :
      ∃! jk : hom (M r).z (M r').z ((r' : ℝ≥0) - (r : ℝ≥0)) ×
              hom (M r').z (M r).z ((r' : ℝ≥0) - (r : ℝ≥0)),
        IsInterleavingPair jk.1 jk.2 ∧ Commutes jk.2 (M r).a (M r').a ∧ Commutes jk.1 (M r').b (M r).b := by
    have hr_nn : (r : ℝ≥0) ≤ (r' : ℝ≥0) := hr
    have hr_sub : ε - (r' : ℝ≥0) ≤ ε - (r : ℝ≥0) := tsub_le_tsub_left hr_nn ε
    exact TerminalMidpoint.compare hr_nn hr_sub (M r) (M r')
  let jk (r r' : Set.Icc (0 : ℝ≥0) ε) (hr : r ≤ r') := (h_comp r r' hr).exists.choose
  let F : CoherentFactorization C ε := {
    z := fun r => (M r).z
    f := fun r r' hr => (jk r r' hr).1
    g := fun r r' hr => (jk r r' hr).2
    pair := fun r r' hr => (h_comp r r' hr).exists.choose_spec.1
  }
  refine ⟨F, ?_, ?_⟩
  · obtain ⟨cd, ⟨hpair_c, -, -, -⟩, -⟩ := TerminalMidpoint.factor (M (lo ε)) hfg
    exact ⟨⟨cd.1, (M (lo ε)).a, hpair_c⟩⟩
  · obtain ⟨cd, ⟨-, hpair_d, -, -⟩, -⟩ := TerminalMidpoint.factor (M (hi ε)) hfg
    have hδ0 : ε - ((hi ε : Set.Icc (0 : ℝ≥0) ε) : ℝ≥0) = 0 := tsub_self ε
    let b_hi : hom (M (hi ε)).z y 0 := S (le_of_eq hδ0) (M (hi ε)).b
    let d_hi : hom y (M (hi ε)).z 0 := S (le_of_eq hδ0) cd.2
    have hpair_hi : IsInterleavingPair b_hi d_hi := IsInterleavingPair.S (le_of_eq hδ0) hpair_d
    exact ⟨⟨b_hi, d_hi, hpair_hi⟩⟩

/-- Corollary 4.4.3. -/
theorem interleavingDist_intrinsic_of_midpoints (h : HasTerminalMidpoints C) :
    IsIntrinsicDist (interleavingDist (C := C)) :=
  interleavingDist_intrinsic (admitsCoherentFactorizations_of_midpoints h)

/-- Corollary 4.4.4: for `D` with pullbacks and binary products, the interleaving distance on
`D^ℝ` is intrinsic. -/
theorem persistent_intrinsic (D : Type u) [Category.{v} D] [HasPullbacks D]
    [HasBinaryProducts D] :
    @IsIntrinsicDist (ℝ ⥤ D) (@interleavingDist (ℝ ⥤ D) _ (persistentLPCat D)) := by
  letI : LPCat (ℝ ⥤ D) := persistentLPCat D
  letI : PoweredByRepresentables (ℝ ⥤ D) := persistentPowered D
  exact interleavingDist_intrinsic_of_midpoints
    (hasTerminalMidpoints_of_powered (fun ε => inferInstanceAs
      (PreservesLimitsOfShape _ ((Functor.whiskeringLeft ℝ ℝ D).obj _)))
      (fun ε => inferInstanceAs
      (PreservesLimitsOfShape _ ((Functor.whiskeringLeft ℝ ℝ D).obj _))))

/-- Corollary 4.4.5: if `C` admits coherent factorizations of interleavings, every quotient
interleaving distance `d_Q` is intrinsic. -/
theorem quotientInterleavingDistOf_intrinsic (h : AdmitsCoherentFactorizations C)
    (R : C → C → Prop) (hR : Equivalence R) :
    IsIntrinsicDist (quotientInterleavingDistOf R) :=
  quotientDist_isIntrinsic _ interleavingDist_isEPMetric (interleavingDist_intrinsic h) R hR

/-! ### 4.5 Geodesic interleaving distances -/

/-- Definition 4.5.1: `d_I` reflects interleavings. -/
def ReflectsInterleavings (C : Type u) [Category.{v} C] [LPCat C] : Prop :=
  ∀ (x y : C) (δ : ℝ≥0), interleavingDist x y = δ → IsInterleaved x y δ

/-- Theorem 4.5.2. -/
theorem interleavingDist_geodesic (h : AdmitsCoherentFactorizations C)
    (hr : ReflectsInterleavings C) : IsGeodesicDist (interleavingDist (C := C)) := by
  intro p p' hfin
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0, interleavingDist p p' = δ := ⟨_, (ENNReal.coe_toNNReal hfin.ne).symm⟩
  have hint := hr p p' δ hδ
  by_cases hδ0 : δ = 0
  · subst hδ0
    have h0 : interleavingDist p p' = 0 := by simpa using hδ
    have hs : ∀ s t : ℝ, interleavingDist (C := C) (if s = 1 then p' else p) (if t = 1 then p' else p) = 0 := by
      have hE := interleavingDist_isEPMetric (C := C)
      intro s t
      by_cases hs : s = 1 <;> by_cases ht : t = 1 <;> simp [hs, ht, h0, hE.symm p' p, hE.refl]
    refine ⟨0, 1, fun t => if t = 1 then p' else p, zero_le_one, ?_, by simp, by simp, ?_⟩
    · intro t _ ε hε
      exact ⟨1, one_pos, fun s _ _ => by rw [hs]; exact hε⟩
    · rw [h0]
      refine le_antisymm (iSup_le fun N => iSup_le fun y => iSup_le fun _ => iSup_le fun _ =>
        iSup_le fun _ => ?_) zero_le
      simp [hs]
  · have hδ_pos : 0 < δ := lt_of_le_of_ne zero_le (Ne.symm hδ0)
    obtain ⟨f, hpath, h0, h1, hlen⟩ := exists_short_path h hδ_pos hint
    refine ⟨0, δ, f, δ.2, hpath, h0, h1, le_antisymm ?_ ?_⟩
    · rw [hδ]; exact hlen
    · have h1' : f ((δ : ℝ≥0) : ℝ) = p' := h1
      have := interleavingDist_le_pathLength (C := C) (f := f) (a := 0) (b := ((δ : ℝ≥0) : ℝ)) δ.2
      rw [h0, h1', hδ] at this
      rw [hδ]; exact this

/-- Definition 4.5.4 (`Set`): `X : P ⥤ Set` is q-tame if every non-identity structure map
has finite image. -/
def IsQTameSet {P : Type*} [Preorder P] (X : P ⥤ Type w) : Prop :=
  ∀ (r s : P) (h : r < s), (Set.range (X.map (homOfLE h.le))).Finite

/-- Definition 4.5.4 (`Top`): `X : P ⥤ Top` is q-tame if every non-identity structure map has
compact image. -/
def IsQTameTop {P : Type*} [Preorder P] (X : P ⥤ TopCat.{w}) : Prop :=
  ∀ (r s : P) (h : r < s), IsCompact (Set.range (fun a => (X.map (homOfLE h.le)).hom a))

/-- Definition 4.5.6: a compatible family for `X` is a choice `x r ∈ X r` with
`φ_{r,s}(x r) = x s` for `r ≤ s`.

**Gap (typo).** The thesis writes `s ≤ r`; for the posets `(ℕ, ≥)` of Proposition 4.5.7
this is the same condition. -/
def IsCompatibleFamily {P : Type*} [Preorder P] (X : P ⥤ Type w) (x : ∀ r, X.obj r) : Prop :=
  ∀ (r s : P) (h : r ≤ s), X.map (homOfLE h) (x r) = x s

section Stone
variable {T : ℕ → Type*} [∀ n, TopologicalSpace (T n)] [∀ n, CompactSpace (T n)]

/-- Stone's theorem for towers of compact spaces with closed maps (Prop 4.5.7), in sequential form. -/
theorem exists_compatible_tower (f : ∀ n, T (n + 1) → T n)
    (hcl : ∀ n, IsClosedMap (f n)) (hne : ∀ n, Nonempty (T n)) :
    ∃ x : ∀ n, T n, ∀ n, f n (x (n + 1)) = x n := by
  classical
  let fib (W : Set (Σ n, T n)) (n : ℕ) : Set (T n) := {t | (⟨n, t⟩ : Σ n, T n) ∈ W}
  let S : Set (Set (Σ n, T n)) := {W | (∀ n, IsClosed (fib W n)) ∧ (∀ n, (fib W n).Nonempty) ∧
    ∀ n, f n '' fib W (n + 1) ⊆ fib W n}
  have hS : ∃ m ∈ S, ∀ a ∈ S, a ⊆ m → a = m := by
    suffices h : ∃ m, Minimal (fun x => x ∈ S) m from
      h.elim fun m hm => ⟨m, hm.1, fun a ha has => (hm.eq_of_ge ha has).symm⟩
    refine zorn_superset S ?_
    intro c hcS hchain
    by_cases hc0 : c.Nonempty
    · refine ⟨⋂₀ c, ⟨?_, ?_, ?_⟩, fun s hs => Set.sInter_subset_of_mem hs⟩
      · intro n
        have : fib (⋂₀ c) n = ⋂ W : c, fib W.1 n := by
          ext t; simp [fib]
        rw [this]
        exact isClosed_iInter fun W => (hcS W.2).1 n
      · intro n
        have : fib (⋂₀ c) n = ⋂ W : c, fib W.1 n := by
          ext t; simp [fib]
        rw [this]
        have : Nonempty c := hc0.to_subtype
        refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_
          (fun W => (hcS W.2).2.1 n) (fun W => ((hcS W.2).1 n).isCompact)
          (fun W => (hcS W.2).1 n)
        intro A B
        rcases hchain.total A.2 B.2 with h | h
        · exact ⟨A, le_rfl, fun t ht => h ht⟩
        · exact ⟨B, fun t ht => h ht, le_rfl⟩
      · intro n t ht
        obtain ⟨s, hs, rfl⟩ := ht
        show (⟨n, f n s⟩ : Σ n, T n) ∈ ⋂₀ c
        intro W hW
        exact (hcS hW).2.2 n ⟨s, by simpa [fib] using (show (⟨n+1, s⟩ : Σ n, T n) ∈ W from hs W hW), rfl⟩
    · refine ⟨Set.univ, ⟨?_, ?_, ?_⟩, fun s hs => ?_⟩
      · intro n; simp [fib]
      · intro n; obtain ⟨t⟩ := hne n; exact ⟨t, by simp [fib]⟩
      · intro n; simp [fib]
      · exact absurd ⟨s, hs⟩ hc0
  obtain ⟨m, ⟨hm1, hm2, hm3⟩, hmin⟩ := hS
  have key : ∀ n, f n '' fib m (n + 1) = fib m n := by
    let a : Set (Σ n, T n) := {p | p.2 ∈ f p.1 '' fib m (p.1 + 1)}
    have hfa : ∀ n, fib a n = f n '' fib m (n + 1) := fun n => rfl
    have ha : a ∈ S := by
      refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
      · rw [hfa]; exact hcl n _ (hm1 _)
      · rw [hfa]; exact (hm2 _).image _
      · rw [hfa, hfa]
        exact Set.image_mono (hm3 _)
    have hsub : a ⊆ m := by
      rintro ⟨n, t⟩ ht
      exact hm3 n ht
    have := hmin a ha hsub
    intro n
    rw [← hfa, this]
  have step : ∀ n (t : fib m n), ∃ s : fib m (n + 1), f n s.1 = t.1 := by
    intro n t
    have : t.1 ∈ f n '' fib m (n + 1) := by rw [key]; exact t.2
    obtain ⟨s, hs, hst⟩ := this
    exact ⟨⟨s, hs⟩, hst⟩
  choose g hg using step
  let x : ∀ n, fib m n := fun n =>
    Nat.rec (motive := fun n => fib m n) ⟨(hm2 0).some, (hm2 0).some_mem⟩
      (fun n xn => g n xn) n
  exact ⟨fun n => (x n).1, fun n => hg n (x n)⟩
end Stone

/-- A family compatible with the adjacent structure maps of a functor `ℕᵒᵈ ⥤ Top` is compatible
with all structure maps. -/
theorem isCompatibleFamily_of_adjacent (X : ℕᵒᵈ ⥤ TopCat.{w}) (x : ∀ n, X.obj (OrderDual.toDual n))
    (hx : ∀ n, (X.map (homOfLE (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from
      Nat.le_succ n))).hom (x (n + 1)) = x n) :
    IsCompatibleFamily (X ⋙ forget TopCat) (fun r => x (OrderDual.ofDual r)) := by
  intro r s h
  have key : ∀ (d b : ℕ) (h : OrderDual.toDual (b + d) ≤ OrderDual.toDual b),
      (X.map (homOfLE h)).hom (x (b + d)) = x b := by
    intro d
    induction d with
    | zero =>
      intro b h
      have : homOfLE h = 𝟙 _ := rfl
      simp [this]
    | succ d ih =>
      intro b h
      have h1 : OrderDual.toDual (b + (d + 1)) ≤ OrderDual.toDual (b + d) := Nat.le_succ _
      have h2 : OrderDual.toDual (b + d) ≤ OrderDual.toDual b := Nat.le_add_right _ _
      have : homOfLE h = homOfLE h1 ≫ homOfLE h2 := rfl
      rw [this, X.map_comp]
      change (X.map (homOfLE h2)).hom ((X.map (homOfLE h1)).hom (x (b + (d + 1)))) = x b
      exact (congrArg (X.map (homOfLE h2)).hom (hx (b + d))).trans (ih b h2)
  obtain ⟨a, rfl⟩ : ∃ a, r = OrderDual.toDual a := ⟨OrderDual.ofDual r, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b, s = OrderDual.toDual b := ⟨OrderDual.ofDual s, rfl⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (OrderDual.toDual_le_toDual.1 h)
  subst hd
  exact key _ _ h

/-- Proposition 4.5.7 (Stone): an objectwise compact, objectwise non-empty functor
`(ℕ, ≥) → Top` with closed structure morphisms admits a compatible family. -/
theorem exists_compatibleFamily_of_compact (X : ℕᵒᵈ ⥤ TopCat.{w})
    (hc : ∀ n, CompactSpace (X.obj n))
    (hcl : ∀ (r s : ℕᵒᵈ) (h : r ≤ s), IsClosedMap (X.map (homOfLE h)).hom)
    (hne : ∀ n, Nonempty (X.obj n)) :
    ∃ x : ∀ n, X.obj n, IsCompatibleFamily (X ⋙ forget TopCat) x := by
  let T : ℕ → Type w := fun n => X.obj (OrderDual.toDual n)
  haveI : ∀ n, CompactSpace (T n) := fun n => hc _
  obtain ⟨x, hx⟩ := exists_compatible_tower (T := T)
    (fun n => (X.map (homOfLE (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from
      Nat.le_succ n))).hom) (fun n => hcl _ _ _) (fun n => hne _)
  exact ⟨fun r => x (OrderDual.ofDual r), isCompatibleFamily_of_adjacent X x hx⟩

/-- Definition 4.5.8: a closed subfunctor of `X : P ⥤ Top`. -/
structure ClosedSubfunctor {P : Type*} [Preorder P] (X : P ⥤ TopCat.{w}) where
  carrier : ∀ r, Set (X.obj r)
  isClosed : ∀ r, IsClosed (carrier r)
  map_mem : ∀ (r s : P) (h : r ≤ s) (a : X.obj r), a ∈ carrier r →
    (X.map (homOfLE h)).hom a ∈ carrier s

/-- Proposition 4.5.9: a q-tame functor `(ℕ, ≥) → Top` with closed structure morphisms that
is objectwise non-empty admits a compatible family. -/
theorem exists_compatibleFamily_of_qtame (X : ℕᵒᵈ ⥤ TopCat.{w}) (hq : IsQTameTop X)
    (hcl : ∀ (r s : ℕᵒᵈ) (h : r ≤ s), IsClosedMap (X.map (homOfLE h)).hom)
    (hne : ∀ n, Nonempty (X.obj n)) :
    ∃ x : ∀ n, X.obj n, IsCompatibleFamily (X ⋙ forget TopCat) x := by
  let T : ℕ → Type w := fun n => X.obj (OrderDual.toDual n)
  let φ : ∀ n, T (n + 1) → T n := fun n => (X.map (homOfLE (show OrderDual.toDual (n + 1) ≤
    OrderDual.toDual n from Nat.le_succ n))).hom
  have hφcl : ∀ n, IsClosedMap (φ n) := fun n => hcl _ _ _
  let R : ∀ n, Set (T n) := fun n => Set.range (φ n)
  have hRc : ∀ n, IsCompact (R n) := fun n =>
    hq (OrderDual.toDual (n + 1)) (OrderDual.toDual n) (by
      exact OrderDual.toDual_lt_toDual.2 (Nat.lt_succ_self n))
  have hRcl : ∀ n, IsClosed (R n) := fun n => (hφcl n).isClosed_range
  have hmaps : ∀ n (y : R (n + 1)), φ n y.1 ∈ R n := fun n y => ⟨y.1, rfl⟩
  let ψ : ∀ n, R (n + 1) → R n := fun n y => ⟨φ n y.1, hmaps n y⟩
  haveI : ∀ n, CompactSpace (R n) := fun n => isCompact_iff_compactSpace.1 (hRc n)
  obtain ⟨x, hx⟩ := exists_compatible_tower (T := fun n => R n) ψ (by
    intro n C hC
    have h1 : IsClosed (Subtype.val '' C) := (hRcl (n + 1)).isClosedEmbedding_subtypeVal.isClosedMap C hC
    have h2 : IsClosed (φ n '' (Subtype.val '' C)) := hφcl n _ h1
    have : ψ n '' C = Subtype.val ⁻¹' (φ n '' (Subtype.val '' C)) := by
      ext ⟨t, ht⟩
      constructor
      · rintro ⟨y, hy, hyt⟩
        exact ⟨y.1, ⟨y, hy, rfl⟩, by simpa [ψ] using congrArg Subtype.val hyt⟩
      · rintro ⟨u, ⟨y, hy, rfl⟩, hu⟩
        exact ⟨y, hy, Subtype.ext hu⟩
    rw [this]; exact h2.preimage continuous_subtype_val)
    (fun n => by obtain ⟨t⟩ := hne (OrderDual.toDual (n + 1)); exact ⟨⟨φ n t, t, rfl⟩⟩)
  exact ⟨fun r => (x (OrderDual.ofDual r)).1,
    isCompatibleFamily_of_adjacent X (fun n => (x n).1) (fun n => congrArg Subtype.val (hx n))⟩

/-- Lemma 4.5.13: a closed subfunctor `Y` of a q-tame `X : (ℕ, ≥) → Top` with closed structure
morphisms is q-tame with closed structure morphisms (images of closed subsets of `Y(n+1)`
are closed, and the image of `Y(n+1)` in `Y(n)` is compact). -/
theorem ClosedSubfunctor.qtame_closed (X : ℕᵒᵈ ⥤ TopCat.{w}) (hq : IsQTameTop X)
    (hcl : ∀ (r s : ℕᵒᵈ) (h : r ≤ s), IsClosedMap (X.map (homOfLE h)).hom)
    (Y : ClosedSubfunctor X) (n : ℕ)
    (h : OrderDual.toDual (n + 1) ≤ OrderDual.toDual n) :
    (∀ A : Set (X.obj (OrderDual.toDual (n + 1))), A ⊆ Y.carrier _ → IsClosed A →
      IsClosed ((X.map (homOfLE h)).hom '' A)) ∧
    IsCompact ((X.map (homOfLE h)).hom '' Y.carrier (OrderDual.toDual (n + 1))) := by
  constructor
  · intro A _ hA
    exact hcl _ _ h A hA
  · have hYc : IsClosed (Y.carrier (OrderDual.toDual (n + 1))) := Y.isClosed _
    have hcl' : IsClosed ((X.map (homOfLE h)).hom '' Y.carrier (OrderDual.toDual (n + 1))) :=
      hcl _ _ h _ hYc
    refine (hq (OrderDual.toDual (n + 1)) (OrderDual.toDual n)
      (OrderDual.toDual_lt_toDual.2 (Nat.lt_succ_self n))).of_isClosed_subset hcl' ?_
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩

/-- The topological data of Proposition 4.5.11 on a persistent set `X : ℝ≥0 ⥤ Set`: a
topology on each `X δ` making the structure maps continuous and closed, and `X` q-tame. -/
structure TopologizedPersistentSet (X : ℝ≥0 ⥤ Type w) where
  top : ∀ r, TopologicalSpace (X.obj r)
  continuous : ∀ {r s : ℝ≥0} (h : r ≤ s), @Continuous _ _ (top r) (top s) (X.map (homOfLE h))
  isClosedMap : ∀ {r s : ℝ≥0} (h : r ≤ s), @IsClosedMap _ _ (top r) (top s) (X.map (homOfLE h))
  qtame : ∀ {r s : ℝ≥0} (h : r < s),
    @IsCompact _ (top s) (Set.range (X.map (homOfLE h.le)))

/-- Definition 4.5.10: the persistent set of interleavings `I(x, y) : ℝ≥0 ⥤ Set`. -/
def interleavingFunctor (x y : C) : ℝ≥0 ⥤ Type v where
  obj δ := {p : hom x y δ × hom y x δ // IsInterleavingPair p.1 p.2}
  map {δ δ'} h := TypeCat.ofHom fun p =>
    ⟨(LPCat.S (leOfHom h) p.1.1, LPCat.S (leOfHom h) p.1.2), IsInterleavingPair.S (leOfHom h) p.2⟩
  map_id := by
    intro δ; ext p
    all_goals exact S_refl _
  map_comp := by
    intro a b c h₁ h₂; ext p
    all_goals exact (S_trans _ _ _).symm

/-- Right continuity yields an element at `δ` from a compatible family along a sequence
decreasing to `δ`. -/
theorem nonempty_of_rightContinuous_seq (F : ℝ≥0 ⥤ Type w) (hF : IsRightContinuous F)
    (δ : ℝ≥0) (s : ℕ → ℝ≥0) (hs : ∀ n, δ < s n) (hanti : Antitone s)
    (hlim : ∀ r, δ < r → ∃ n, s n ≤ r) (z : ∀ n, F.obj (s n))
    (hz : ∀ n m (h : n ≤ m), F.map (homOfLE (hanti h)) (z m) = z n) :
    Nonempty (F.obj δ) := by
  classical
  let w : ∀ j : {r' : ℝ≥0 // δ < r'}, F.obj j.1 := fun j =>
    F.map (homOfLE (Nat.find_spec (hlim j.1 j.2))) (z (Nat.find (hlim j.1 j.2)))
  have claim : ∀ (j : {r' : ℝ≥0 // δ < r'}) n, (hn : s n ≤ j.1) →
      F.map (homOfLE hn) (z n) = w j := by
    intro j n hn
    have key : ∀ n m, n ≤ m → (hm : s m ≤ j.1) → (hn : s n ≤ j.1) →
        F.map (homOfLE hm) (z m) = F.map (homOfLE hn) (z n) := by
      intro n m hnm hm hn
      rw [← hz n m hnm, ← types_comp_apply (F.map _) (F.map _), ← F.map_comp]
      rfl
    rcases le_total n (Nat.find (hlim j.1 j.2)) with h | h
    · exact (key n _ h (Nat.find_spec (hlim j.1 j.2)) hn).symm
    · exact key _ n h hn (Nat.find_spec (hlim j.1 j.2))
  let L := Types.Limit.mk (upperSet δ ⋙ F) w (by
    intro j j' f
    obtain ⟨n, hn⟩ := hlim j.1 j.2
    have hnj' : s (Nat.find (hlim j.1 j.2)) ≤ j'.1 :=
      (Nat.find_spec (hlim j.1 j.2)).trans (leOfHom f)
    have h1 := claim j' _ hnj'
    have : (upperSet δ ⋙ F).map f (w j) = F.map (homOfLE hnj') (z (Nat.find (hlim j.1 j.2))) := by
      change F.map (homOfLE (leOfHom f)) (F.map _ _) = _
      rw [← types_comp_apply (F.map _) (F.map _), ← F.map_comp]
      rfl
    rw [this, h1])
  haveI := hF δ
  exact ⟨inv (limit.lift (upperSet δ ⋙ F) (Limits.Cone.mk (F.obj δ)
      { app := fun s => F.map (homOfLE (le_of_lt s.2))
        naturality := by
          first
          | done
          | (intros
             simp only [Functor.comp_map, Functor.const_obj_map]
             erw [Category.id_comp, ← Functor.map_comp]) })) L⟩

/-- The common argument of Propositions 4.5.11 and Theorem 4.5.18: a right continuous,
q-tame, closed persistent set which is non-empty above `δ` is non-empty at `δ`. -/
theorem nonempty_of_topologized_rc {F0 : ℝ≥0 ⥤ Type w} (hrc : IsRightContinuous F0)
    (T : TopologizedPersistentSet F0) (δ : ℝ≥0)
    (hne0 : ∀ r, δ < r → Nonempty (F0.obj r)) : Nonempty (F0.obj δ) := by
  let I := F0
  let s : ℕ → ℝ≥0 := fun n => δ + ((n : ℝ≥0) + 1)⁻¹
  have hs : ∀ n, δ < s n := fun n => lt_add_of_pos_right _ (by positivity)
  have hanti : Antitone s := fun n m h => by
    have : ((m : ℝ≥0) + 1)⁻¹ ≤ ((n : ℝ≥0) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by gcongr)
    show δ + _ ≤ δ + _
    gcongr
  have hlim : ∀ r, δ < r → ∃ n, s n ≤ r := by
    intro r hr
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < (r - δ : ℝ≥0) by
      exact_mod_cast tsub_pos_of_lt hr)
    refine ⟨n, ?_⟩
    have : ((n : ℝ≥0) + 1)⁻¹ ≤ r - δ := by
      rw [← NNReal.coe_le_coe]; push_cast
      rw [← one_div]; exact hn.le
    calc s n = δ + ((n : ℝ≥0) + 1)⁻¹ := rfl
      _ ≤ δ + (r - δ) := by gcongr
      _ = r := add_tsub_cancel_of_le hr.le
  -- the functor `ℕᵒᵈ ⥤ Top`
  let F : ℝ≥0 ⥤ TopCat.{w} :=
    { obj := fun r => letI := T.top r; TopCat.of (I.obj r)
      map := fun {r r'} h => by
        letI := T.top r; letI := T.top r'
        exact TopCat.ofHom ⟨fun a => I.map h a, T.continuous (leOfHom h)⟩
      map_id := fun r => by
        ext a
        change I.map (𝟙 r) a = a
        rw [I.map_id]; rfl
      map_comp := fun f g => by
        ext a
        change I.map (f ≫ g) a = I.map g (I.map f a)
        rw [I.map_comp]; rfl }
  let G : ℕᵒᵈ ⥤ ℝ≥0 :=
    { obj := fun n => s (OrderDual.ofDual n)
      map := fun {a b} h => homOfLE (hanti (OrderDual.toDual_le_toDual.1 (leOfHom h)))
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  let Xt : ℕᵒᵈ ⥤ TopCat.{w} := G ⋙ F
  have hne : ∀ n, Nonempty (Xt.obj n) := by
    intro n
    exact (hne0 _ (hs _)).elim fun a => ⟨a⟩
  have hq : IsQTameTop Xt := by
    intro r r' h
    have hlt : G.obj r < G.obj r' := by
      have h' : OrderDual.ofDual r' < OrderDual.ofDual r := h
      show δ + ((OrderDual.ofDual r : ℕ) + 1 : ℝ≥0)⁻¹ < δ + ((OrderDual.ofDual r' : ℕ) + 1 : ℝ≥0)⁻¹
      refine add_lt_add_right (inv_strictAnti₀ (by positivity) ?_) δ
      exact_mod_cast Nat.succ_lt_succ h'
    exact T.qtame hlt
  have hcl : ∀ (r r' : ℕᵒᵈ) (h : r ≤ r'), IsClosedMap (Xt.map (homOfLE h)).hom :=
    fun r r' h => T.isClosedMap (leOfHom (G.map (homOfLE h)))
  obtain ⟨xf, hxf⟩ := exists_compatibleFamily_of_qtame Xt hq hcl hne
  exact nonempty_of_rightContinuous_seq I hrc δ s hs hanti hlim
    (fun n => xf (OrderDual.toDual n)) (fun n m h => hxf (OrderDual.toDual m)
      (OrderDual.toDual n) (OrderDual.toDual_le_toDual.2 h))


/-- Proposition 4.5.11: if `I(x, y)` is right continuous and admits a topology making it
q-tame with continuous closed structure maps, and `d_I(x, y) = δ`, then `x` and `y` are
`δ`-interleaved. -/
theorem isInterleaved_of_dist_eq (x y : C) (hrc : IsRightContinuous (interleavingFunctor x y))
    (T : TopologizedPersistentSet (interleavingFunctor x y)) (δ : ℝ≥0)
    (hd : interleavingDist x y = δ) : IsInterleaved x y δ := by
  obtain ⟨⟨⟨f, g⟩, hp⟩⟩ := nonempty_of_topologized_rc hrc T δ (fun r hr => by
    have hlt : interleavingDist x y < (r : ℝ≥0∞) := by
      rw [hd]; exact_mod_cast hr
    obtain ⟨⟨f, g, hp⟩⟩ := isInterleaved_of_dist_lt hlt
    exact ⟨⟨(f, g), hp⟩⟩)
  exact ⟨⟨f, g, hp⟩⟩

/-- Theorem 4.5.14: topologies on the hom-persistent sets. -/
structure TopologizedHoms (C : Type u) [Category.{v} C] [LPCat C] where
  T : ∀ x y : C, TopologizedPersistentSet (homFunctor x y)
  t1 : ∀ (x y : C) (ε : ℝ≥0), @T1Space _ ((T x y).top ε)
  comp_continuous : ∀ (x y z : C) (ε δ : ℝ≥0),
    letI : TopologicalSpace (hom y z δ) := (T y z).top δ
    letI : TopologicalSpace (hom x y ε) := (T x y).top ε
    letI : TopologicalSpace (hom x z (ε + δ)) := (T x z).top (ε + δ)
    Continuous (fun p : hom y z δ × hom x y ε => comp p.1 p.2)
  /-- **Gap (missing hypothesis, Theorem 4.5.14).** The thesis deduces that the structure maps
  of `H(δ) = Hom(x, y)_δ × Hom(y, x)_δ` are closed from the same fact for each factor; but a
  product of closed maps need not be closed (a closed map to a point from a non-compact space,
  times an identity).  We assume it. -/
  prod_closed : ∀ (x y : C) {ε δ : ℝ≥0} (h : ε ≤ δ),
    letI : TopologicalSpace (hom x y ε) := (T x y).top ε
    letI : TopologicalSpace (hom y x ε) := (T y x).top ε
    letI : TopologicalSpace (hom x y δ) := (T x y).top δ
    letI : TopologicalSpace (hom y x δ) := (T y x).top δ
    IsClosedMap (fun p : hom x y ε × hom y x ε => (S h p.1, S h p.2))

namespace TopologizedHoms

variable (TH : TopologizedHoms C) (x y : C)

/-- The topology on `I(x, y)_r`, induced from `Hom(x, y)_r × Hom(y, x)_r`. -/
def ilTop (r : ℝ≥0) : TopologicalSpace ((interleavingFunctor x y).obj r) :=
  letI : TopologicalSpace (hom x y r) := (TH.T x y).top r
  letI : TopologicalSpace (hom y x r) := (TH.T y x).top r
  TopologicalSpace.induced
    (fun p : {p : hom x y r × hom y x r // IsInterleavingPair p.1 p.2} => p.1) inferInstance

theorem isClosed_interleavings (r : ℝ≥0) :
    letI : TopologicalSpace (hom x y r) := (TH.T x y).top r
    letI : TopologicalSpace (hom y x r) := (TH.T y x).top r
    IsClosed {p : hom x y r × hom y x r | IsInterleavingPair p.1 p.2} := by
  letI : TopologicalSpace (hom x y r) := (TH.T x y).top r
  letI : TopologicalSpace (hom y x r) := (TH.T y x).top r
  have h1 : IsClosed {p : hom x y r × hom y x r | comp p.2 p.1 = S zero_le (idHom x)} := by
    letI : TopologicalSpace (hom x x (r + r)) := (TH.T x x).top (r + r)
    exact (@isClosed_singleton (hom x x (r + r)) _ (TH.t1 x x (r + r))
      (S zero_le (idHom x))).preimage
      ((TH.comp_continuous x y x r r).comp continuous_swap)
  have h2 : IsClosed {p : hom x y r × hom y x r | comp p.1 p.2 = S zero_le (idHom y)} := by
    letI : TopologicalSpace (hom y y (r + r)) := (TH.T y y).top (r + r)
    exact (@isClosed_singleton (hom y y (r + r)) _ (TH.t1 y y (r + r))
      (S zero_le (idHom y))).preimage
      (TH.comp_continuous y x y r r)
  exact h1.inter h2

/-- The inclusion `I(x, y)_r ⊆ Hom(x, y)_r × Hom(y, x)_r`. -/
def ilVal (r : ℝ≥0) (p : (interleavingFunctor x y).obj r) : hom x y r × hom y x r := p.1

theorem ilVal_injective (r : ℝ≥0) : Function.Injective (ilVal x y r) :=
  fun _ _ h => Subtype.ext h

theorem ilVal_map (r s : ℝ≥0) (h : r ≤ s) (p : (interleavingFunctor x y).obj r) :
    ilVal x y s ((interleavingFunctor x y).map (homOfLE h) p) = (S h (ilVal x y r p).1, S h (ilVal x y r p).2) :=
  rfl

theorem ilVal_isClosedEmbedding (r : ℝ≥0) :
    letI : TopologicalSpace (hom x y r) := (TH.T x y).top r
    letI : TopologicalSpace (hom y x r) := (TH.T y x).top r
    letI : TopologicalSpace ((interleavingFunctor x y).obj r) := ilTop TH x y r
    Topology.IsClosedEmbedding (ilVal x y r) := by
  letI : TopologicalSpace (hom x y r) := (TH.T x y).top r
  letI : TopologicalSpace (hom y x r) := (TH.T y x).top r
  letI : TopologicalSpace ((interleavingFunctor x y).obj r) := ilTop TH x y r
  refine ⟨⟨⟨rfl⟩, ilVal_injective x y r⟩, ?_⟩
  have : Set.range (ilVal x y r) = {p : hom x y r × hom y x r | IsInterleavingPair p.1 p.2} := by
    ext p
    exact ⟨fun ⟨q, hq⟩ => hq ▸ q.2, fun hp => ⟨⟨p, hp⟩, rfl⟩⟩
  rw [this]
  exact TH.isClosed_interleavings x y r

/-- The topologized persistent set of interleavings (proof of Theorem 4.5.14). -/
def toTopologized : TopologizedPersistentSet (interleavingFunctor x y) where
  top := ilTop TH x y
  continuous := by
    intro r s h
    letI : TopologicalSpace (hom x y r) := (TH.T x y).top r
    letI : TopologicalSpace (hom y x r) := (TH.T y x).top r
    letI : TopologicalSpace (hom x y s) := (TH.T x y).top s
    letI : TopologicalSpace (hom y x s) := (TH.T y x).top s
    letI : TopologicalSpace ((homFunctor x y).obj r) := (TH.T x y).top r
    letI : TopologicalSpace ((homFunctor y x).obj r) := (TH.T y x).top r
    letI : TopologicalSpace ((homFunctor x y).obj s) := (TH.T x y).top s
    letI : TopologicalSpace ((homFunctor y x).obj s) := (TH.T y x).top s
    letI : TopologicalSpace ((interleavingFunctor x y).obj r) := ilTop TH x y r
    letI : TopologicalSpace ((interleavingFunctor x y).obj s) := ilTop TH x y s
    refine continuous_induced_rng.2 ?_
    exact (Continuous.prodMap ((TH.T x y).continuous h) ((TH.T y x).continuous h)).comp
      continuous_induced_dom
  isClosedMap := by
    intro r s h C hC
    letI : TopologicalSpace (hom x y r) := (TH.T x y).top r
    letI : TopologicalSpace (hom y x r) := (TH.T y x).top r
    letI : TopologicalSpace (hom x y s) := (TH.T x y).top s
    letI : TopologicalSpace (hom y x s) := (TH.T y x).top s
    letI : TopologicalSpace ((interleavingFunctor x y).obj r) := ilTop TH x y r
    letI : TopologicalSpace ((interleavingFunctor x y).obj s) := ilTop TH x y s
    have e1 : IsClosed (ilVal x y r '' C) :=
      (ilVal_isClosedEmbedding TH x y r).isClosedMap C hC
    have e2 := TH.prod_closed x y (h) _ e1
    have e3 : (interleavingFunctor x y).map (homOfLE (h)) '' C =
        ilVal x y s ⁻¹' ((fun p : hom x y r × hom y x r => (S (h) p.1, S (h) p.2)) ''
          (ilVal x y r '' C)) := by
      ext q
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨ilVal x y r c, ⟨c, hc, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨c, hc, rfl⟩, hq⟩
        refine ⟨c, hc, ilVal_injective x y s ?_⟩
        exact hq
    rw [e3]
    exact e2.preimage (ilVal_isClosedEmbedding TH x y s).continuous
  qtame := by
    intro r s h
    letI : TopologicalSpace (hom x y r) := (TH.T x y).top r
    letI : TopologicalSpace (hom y x r) := (TH.T y x).top r
    letI : TopologicalSpace (hom x y s) := (TH.T x y).top s
    letI : TopologicalSpace (hom y x s) := (TH.T y x).top s
    letI : TopologicalSpace ((interleavingFunctor x y).obj r) := ilTop TH x y r
    letI : TopologicalSpace ((interleavingFunctor x y).obj s) := ilTop TH x y s
    letI : TopologicalSpace ((homFunctor x y).obj s) := (TH.T x y).top s
    letI : TopologicalSpace ((homFunctor y x).obj s) := (TH.T y x).top s
    have hemb := ilVal_isClosedEmbedding TH x y s
    rw [hemb.isInducing.isCompact_iff]
    have e : ilVal x y s '' Set.range ((interleavingFunctor x y).map (homOfLE h.le)) =
        (fun p : hom x y r × hom y x r => (S h.le p.1, S h.le p.2)) '' Set.range (ilVal x y r) := by
      ext q
      constructor
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        exact ⟨ilVal x y r c, ⟨c, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        exact ⟨_, ⟨c, rfl⟩, rfl⟩
    rw [e]
    have hcl : IsClosed ((fun p : hom x y r × hom y x r => (S h.le p.1, S h.le p.2)) ''
        Set.range (ilVal x y r)) :=
      TH.prod_closed x y h.le _ (ilVal_isClosedEmbedding TH x y r).isClosed_range
    refine ((TH.T x y).qtame h).prod ((TH.T y x).qtame h) |>.of_isClosed_subset hcl ?_
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨⟨c.1.1, rfl⟩, ⟨c.1.2, rfl⟩⟩

end TopologizedHoms

section RightContinuity

variable {F : ℝ≥0 ⥤ Type w}

theorem rc_inj (hF : IsRightContinuous F) (r : ℝ≥0) (a b : F.obj r)
    (h : ∀ s : {s : ℝ≥0 // r < s}, F.map (homOfLE s.2.le) a = F.map (homOfLE s.2.le) b) :
    a = b := by
  have hinj := ((isIso_iff_bijective _).1 (hF r)).1
  apply hinj
  apply Types.limit_ext
  intro s
  simp only [← ConcreteCategory.comp_apply, Limits.limit.lift_π]
  exact h s

theorem rc_surj (hF : IsRightContinuous F) (r : ℝ≥0) (z : ∀ s : {s : ℝ≥0 // r < s}, F.obj s.1)
    (hz : ∀ (s s' : {s : ℝ≥0 // r < s}) (h : s.1 ≤ s'.1), F.map (homOfLE h) (z s) = z s') :
    ∃ a : F.obj r, ∀ s : {s : ℝ≥0 // r < s}, F.map (homOfLE s.2.le) a = z s := by
  have hsurj := ((isIso_iff_bijective _).1 (hF r)).2
  obtain ⟨a, ha⟩ := hsurj (Types.Limit.mk (upperSet r ⋙ F) z (fun s s' f => hz s s' (leOfHom f)))
  refine ⟨a, fun s => ?_⟩
  have := congrArg (Limits.limit.π (upperSet r ⋙ F) s) ha
  simp only [← ConcreteCategory.comp_apply, Limits.limit.lift_π] at this
  exact this.trans (Types.Limit.π_mk (upperSet r ⋙ F) z _ s)

end RightContinuity

theorem interleavingFunctor_rightContinuous
    (hrc : ∀ x y : C, IsRightContinuous (homFunctor x y)) (x y : C) :
    IsRightContinuous (interleavingFunctor x y) := by
  intro r
  rw [isIso_iff_bijective]
  constructor
  · intro p q hpq
    have hs : ∀ s : {s : ℝ≥0 // r < s}, (interleavingFunctor x y).map (homOfLE s.2.le) p =
        (interleavingFunctor x y).map (homOfLE s.2.le) q := by
      intro s
      have := congrArg (Limits.limit.π (upperSet r ⋙ interleavingFunctor x y) s) hpq
      simp only [← ConcreteCategory.comp_apply, Limits.limit.lift_π] at this
      exact this
    have h1 : p.1.1 = q.1.1 := rc_inj (hrc x y) r _ _ fun s => congrArg (fun u => u.1.1) (hs s)
    have h2 : p.1.2 = q.1.2 := rc_inj (hrc y x) r _ _ fun s => congrArg (fun u => u.1.2) (hs s)
    exact Subtype.ext (Prod.ext h1 h2)
  · intro ℓ
    let w : ∀ s : {s : ℝ≥0 // r < s}, (interleavingFunctor x y).obj s.1 :=
      fun s => Limits.limit.π (upperSet r ⋙ interleavingFunctor x y) s ℓ
    have hw : ∀ (s s' : {s : ℝ≥0 // r < s}) (h : s.1 ≤ s'.1),
        (interleavingFunctor x y).map (homOfLE h) (w s) = w s' := by
      intro s s' h
      exact Limits.limit.w_apply (upperSet r ⋙ interleavingFunctor x y) (homOfLE h : s ⟶ s') ℓ
    obtain ⟨f, hf⟩ := rc_surj (hrc x y) r (fun s => (w s).1.1)
      (fun s s' h => congrArg (fun u => u.1.1) (hw s s' h))
    obtain ⟨g, hg⟩ := rc_surj (hrc y x) r (fun s => (w s).1.2)
      (fun s s' h => congrArg (fun u => u.1.2) (hw s s' h))
    have half : ∀ t : {t : ℝ≥0 // r + r < t}, r < t.1 / 2 ∧ t.1 / 2 + t.1 / 2 = t.1 := by
      intro t
      have ht := t.2
      refine ⟨?_, ?_⟩
      · rw [← NNReal.coe_lt_coe] at ht ⊢; push_cast at ht ⊢; linarith
      · apply NNReal.eq; push_cast; ring
    have hpx : comp g f = S zero_le (idHom x) := by
      refine rc_inj (hrc x x) (r + r) _ _ ?_
      rintro ⟨t, ht⟩
      obtain ⟨hs, hts⟩ := half ⟨t, ht⟩
      have hsx := (w ⟨t / 2, hs⟩).2.1
      have e1 : (w ⟨t / 2, hs⟩).1.1 = S hs.le f := (hf ⟨t / 2, hs⟩).symm
      have e2 : (w ⟨t / 2, hs⟩).1.2 = S hs.le g := (hg ⟨t / 2, hs⟩).symm
      change S ht.le (comp g f) = S ht.le (S zero_le (idHom x))
      calc S ht.le (comp g f)
          = S (le_of_eq hts) (S (add_le_add hs.le hs.le) (comp g f)) := (S_trans _ _ _).symm
        _ = S (le_of_eq hts) (comp (S hs.le g) (S hs.le f)) := congrArg (S (le_of_eq hts)) (comp_S hs.le hs.le f g).symm
        _ = S (le_of_eq hts) (comp (w ⟨t / 2, hs⟩).1.2 (w ⟨t / 2, hs⟩).1.1) := by rw [e1, e2]
        _ = S (le_of_eq hts) (S zero_le (idHom x)) := by rw [hsx]
        _ = S ht.le (S zero_le (idHom x)) := by rw [S_trans, S_trans]
    have hpy : comp f g = S zero_le (idHom y) := by
      refine rc_inj (hrc y y) (r + r) _ _ ?_
      rintro ⟨t, ht⟩
      obtain ⟨hs, hts⟩ := half ⟨t, ht⟩
      have hsy := (w ⟨t / 2, hs⟩).2.2
      have e1 : (w ⟨t / 2, hs⟩).1.1 = S hs.le f := (hf ⟨t / 2, hs⟩).symm
      have e2 : (w ⟨t / 2, hs⟩).1.2 = S hs.le g := (hg ⟨t / 2, hs⟩).symm
      change S ht.le (comp f g) = S ht.le (S zero_le (idHom y))
      calc S ht.le (comp f g)
          = S (le_of_eq hts) (S (add_le_add hs.le hs.le) (comp f g)) := (S_trans _ _ _).symm
        _ = S (le_of_eq hts) (comp (S hs.le f) (S hs.le g)) := congrArg (S (le_of_eq hts)) (comp_S hs.le hs.le g f).symm
        _ = S (le_of_eq hts) (comp (w ⟨t / 2, hs⟩).1.1 (w ⟨t / 2, hs⟩).1.2) := by rw [e1, e2]
        _ = S (le_of_eq hts) (S zero_le (idHom y)) := by rw [hsy]
        _ = S ht.le (S zero_le (idHom y)) := by rw [S_trans, S_trans]
    let e : (interleavingFunctor x y).obj r := ⟨(f, g), hpx, hpy⟩
    refine ⟨e, ?_⟩
    apply Types.limit_ext
    intro s
    simp only [← ConcreteCategory.comp_apply, Limits.limit.lift_π]
    exact Subtype.ext (Prod.ext (hf s) (hg s))

/-- Theorem 4.5.14: if all `Hom(x, y)` are right continuous and carry such topologies, then
`d_I` reflects interleavings. -/
theorem reflectsInterleavings_of_topologized (hrc : ∀ x y : C, IsRightContinuous (homFunctor x y))
    (T : TopologizedHoms C) : ReflectsInterleavings C := by
  intro x y δ hd
  exact isInterleaved_of_dist_eq x y (interleavingFunctor_rightContinuous hrc x y)
    (T.toTopologized x y) δ hd

/-- Definition 4.5.15: `d_Q` reflects quotient interleavings. -/
def ReflectsQuotientInterleavings (W : MorphismProperty C) : Prop :=
  ∀ (x y : C) (δ : ℝ≥0), quotientInterleavingDist W x y = δ → IsQuotientInterleaved W x y δ

theorem dist_le_pathLength_gen {P : Type*} (d : P → P → ℝ≥0∞) {a b : ℝ} {f : ℝ → P}
    (hab : a ≤ b) : d (f a) (f b) ≤ pathLength d a b f := by
  refine le_iSup_of_le 1 (le_iSup_of_le (fun n => if n = 0 then a else b) ?_)
  refine le_iSup_of_le (by simp) (le_iSup_of_le (by simp) (le_iSup_of_le ?_ ?_))
  · intro m n hmn
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all
  · simp

theorem pathLength_mono {P : Type*} {d d' : P → P → ℝ≥0∞} (hdd : ∀ x y, d x y ≤ d' x y)
    {a b : ℝ} {f : ℝ → P} : pathLength d a b f ≤ pathLength d' a b f :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ =>
    Finset.sum_le_sum fun _ _ => hdd _ _

/-- Theorem 4.5.16. -/
theorem quotientInterleavingDist_geodesic (W : MorphismProperty C) [W.IsMultiplicative]
    (h : AdmitsCoherentFactorizations C) (hW : IsStableUnderWeightedPullbacks W)
    (hr : ReflectsQuotientInterleavings W) : IsGeodesicDist (quotientInterleavingDist W) := by
  intro x y hfin
  have hE := quotientInterleavingDist_isEPMetric W
  have hinv : IsInvariant (quotientInterleavingDist W) (WeaklyEquivalent W) :=
    quotientDist_isInvariant interleavingDist (WeaklyEquivalent W)
      (weaklyEquivalent_equivalence W)
  have hle : ∀ a b, quotientInterleavingDist W a b ≤ interleavingDist a b :=
    fun a b => quotientDist_le interleavingDist (WeaklyEquivalent W) a b
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0, quotientInterleavingDist W x y = δ :=
    ⟨_, (ENNReal.coe_toNNReal hfin.ne).symm⟩
  by_cases hδ0 : δ = 0
  · subst hδ0
    have h0 : quotientInterleavingDist W x y = 0 := by simpa using hδ
    have hs : ∀ s t : ℝ, quotientInterleavingDist W (if s = 1 then y else x)
        (if t = 1 then y else x) = 0 := by
      intro s t
      by_cases hs : s = 1 <;> by_cases ht : t = 1 <;>
        simp [hs, ht, h0, hE.symm y x, hE.refl]
    refine ⟨0, 1, fun t => if t = 1 then y else x, zero_le_one, ?_, by simp, by simp, ?_⟩
    · intro t _ ε hε
      exact ⟨1, one_pos, fun s _ _ => by rw [hs]; exact hε⟩
    · rw [h0]
      refine le_antisymm (iSup_le fun N => iSup_le fun y => iSup_le fun _ => iSup_le fun _ =>
        iSup_le fun _ => ?_) zero_le
      simp [hs]
  · have hδ_pos : 0 < δ := lt_of_le_of_ne zero_le (Ne.symm hδ0)
    obtain ⟨x', y', hx', hy', hint⟩ := hr x y δ hδ
    obtain ⟨f, hpath, h0, h1, hlen⟩ := exists_short_path h hδ_pos hint
    let g : ℝ → C := fun t => if t = 0 then x else if t = (δ : ℝ) then y else f t
    have hg0 : g 0 = x := by simp [g]
    have hgδ : g (δ : ℝ) = y := by simp [g, hδ0]
    have hgf : ∀ t, WeaklyEquivalent W (g t) (f t) := by
      intro t
      by_cases ht0 : t = 0
      · subst ht0
        rw [hg0, h0]
        exact (weaklyEquivalent_equivalence W).symm hx'
      · by_cases htδ : t = (δ : ℝ)
        · subst htδ
          rw [hgδ, h1]
          exact (weaklyEquivalent_equivalence W).symm hy'
        · show WeaklyEquivalent W (if t = 0 then x else if t = (δ : ℝ) then y else f t) _
          rw [if_neg ht0, if_neg htδ]
          exact (weaklyEquivalent_equivalence W).refl _
    have hgg : ∀ s t, quotientInterleavingDist W (g s) (g t) =
        quotientInterleavingDist W (f s) (f t) := fun s t => hinv _ _ _ _ (hgf s) (hgf t)
    have hpathQ : IsPathOn (quotientInterleavingDist W) 0 δ g := by
      intro t ht ε hε
      obtain ⟨η, hη, hηs⟩ := hpath t ht ε hε
      refine ⟨η, hη, fun s hs hst => ?_⟩
      rw [hgg]
      exact (hle _ _).trans_lt (hηs s hs hst)
    have hlenQ : pathLength (quotientInterleavingDist W) 0 δ g ≤ δ := by
      refine le_trans (le_of_eq ?_) ((pathLength_mono hle).trans hlen)
      unfold pathLength
      simp only [hgg]
    refine ⟨0, δ, g, δ.2, hpathQ, hg0, hgδ, ?_⟩
    rw [hδ]
    refine le_antisymm hlenQ ?_
    have := dist_le_pathLength_gen (quotientInterleavingDist W) (f := g) (a := 0) (b := (δ : ℝ)) δ.2
    rw [hg0, hgδ, hδ] at this
    exact this

/-- The data of an element of `QI(x, y)_δ` (Definition 4.5.17). -/
@[ext]
structure QuotientInterleavingData (W : MorphismProperty C) (x y : C) (δ : ℝ≥0) where
  x' : C
  y' : C
  u : x' ⟶ x
  v : y' ⟶ y
  hu : W u
  hv : W v
  f : hom x' y' δ
  g : hom y' x' δ
  pair : IsInterleavingPair f g

/-- Definition 4.5.17: the persistent set of quotient interleavings `QI(x, y)`. -/
def quotientInterleavingFunctor (W : MorphismProperty C) (x y : C) :
    ℝ≥0 ⥤ Type (max u v) where
  obj δ := QuotientInterleavingData W x y δ
  map {δ δ'} h := TypeCat.ofHom fun q =>
    { q with f := LPCat.S (leOfHom h) q.f, g := LPCat.S (leOfHom h) q.g,
             pair := IsInterleavingPair.S (leOfHom h) q.pair }
  map_id := by
    intro δ; apply ConcreteCategory.hom_ext; intro q
    obtain ⟨x', y', u, v, hu, hv, f, g, pr⟩ := q
    change QuotientInterleavingData.mk x' y' u v hu hv (S _ f) (S _ g) _ = _
    simp only [S_refl]
    rfl
  map_comp := by
    intro a b c h₁ h₂; apply ConcreteCategory.hom_ext; intro q
    obtain ⟨x', y', u, v, hu, hv, f, g, pr⟩ := q
    change QuotientInterleavingData.mk x' y' u v hu hv (S _ f) (S _ g) _ =
      QuotientInterleavingData.mk x' y' u v hu hv (S _ (S _ f)) (S _ (S _ g)) _
    simp only [S_trans]

/-- Theorem 4.5.18: the analogue of Proposition 4.5.11 for quotient interleavings.

**Gap (missing hypothesis).** The thesis states this for a relative locally persistent category,
but the persistent set `QI(x, y)` is only defined (Definition 4.5.17) when `W` is stable under
weighted pullbacks, which the proof also uses (through Section 4.1).  We assume it. -/
theorem exists_acyclic_cover_of_dist_eq (W : MorphismProperty C) [W.IsMultiplicative]
    (hW : IsStableUnderWeightedPullbacks W)
    (x y : C) (hrc : IsRightContinuous (quotientInterleavingFunctor W x y))
    (T : TopologizedPersistentSet (quotientInterleavingFunctor W x y)) (δ : ℝ≥0)
    (hd : quotientInterleavingDist W x y = δ) :
    ∃ (x' y' : C) (u : x' ⟶ x) (v : y' ⟶ y), W u ∧ W v ∧ IsInterleaved x' y' δ := by
  obtain ⟨q⟩ := nonempty_of_topologized_rc hrc T δ (fun r hr => by
    have hlt : quotientInterleavingDist W x y < (r : ℝ≥0∞) := by
      rw [hd]; exact_mod_cast hr
    rw [quotientInterleavingDist_eq_inf_acyclicCover hW x y] at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨δ', ⟨x', y', u, v, hu, hv, hint⟩, hlt'⟩ := hlt
    obtain ⟨⟨f, g, hp⟩⟩ := IsInterleaved.mono (by exact_mod_cast hlt'.le : δ' ≤ r) hint
    exact ⟨⟨x', y', u, v, hu, hv, f, g, hp⟩⟩)
  exact ⟨q.x', q.y', q.u, q.v, q.hu, q.hv, ⟨⟨q.f, q.g, q.pair⟩⟩⟩

end Distances

end ScoccolaPhd
