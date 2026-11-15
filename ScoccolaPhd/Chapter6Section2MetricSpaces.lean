import ScoccolaPhd.Chapter6Section1DissimilarityFiltrations

/-!
# §6.2.2: the Gromov–Hausdorff distance on metric spaces

Metric spaces as a relative locally persistent subcategory of dissimilarity spaces,
and the metric-space statements of Theorem 6.2.20.
-/
universe u v w
namespace ScoccolaPhd
open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal Topology
open LPCat
set_option backward.isDefEq.respectTransparency false

/-! ### 6.2.2 The Gromov–Hausdorff distance on metric spaces -/

/-- The ep metric space as a dissimilarity space. -/
def EPMet.toDiss (P : EPMet.{u}) : Diss.{u} := ⟨P.carrier, edist⟩

/-- The locally persistent structure on `epMet` (Example 3.1.4), chosen via
`exists_lpcat_epMet` (the canonical structure `epMetLPCatStd`, with composition of maps). -/
instance epMetLPCat : LPCat EPMet.{u} := epMetLPCatStd

/-- Acyclic morphisms of ep metric spaces: those that are acyclic in `Diss`. -/
def acyclicEPMet : MorphismProperty EPMet.{u} :=
  fun P Q f => acyclicDiss (X := P.toDiss) (Y := Q.toDiss) ⟨f.1, fun x x' => f.2 x x'⟩

/-- An ep metric space from a distance function that is an ep metric. -/
noncomputable def epMetOfDist {X : Type u} (d : X → X → ℝ≥0∞) (h : IsEPMetric d) : EPMet.{u} :=
  @EPMet.mk X
    { edist := d
      edist_self := h.refl
      edist_comm := h.symm
      edist_triangle := h.triangle }

/-- Lemma 6.2.13: a dissimilarity space weakly equivalent to an ep metric space is an ep
metric space. -/
theorem isEPMetric_of_weaklyEquivalent (P : EPMet.{u}) (X : Diss.{u})
    (h : WeaklyEquivalent acyclicDiss P.toDiss X) : IsEPMetric X.d := by
  have forward : ∀ {A B : Diss.{u}} (f : A ⟶ B), acyclicDiss f →
      IsEPMetric A.d → IsEPMetric B.d := by
    intro A B f hf hA
    refine ⟨?_, ?_, ?_⟩
    · intro b
      obtain ⟨a, rfl⟩ := hf.1 b
      rw [hf.2, hA.refl]
    · intro b b'
      obtain ⟨a, rfl⟩ := hf.1 b
      obtain ⟨a', rfl⟩ := hf.1 b'
      rw [hf.2, hf.2, hA.symm]
    · intro b b' b''
      obtain ⟨a, rfl⟩ := hf.1 b
      obtain ⟨a', rfl⟩ := hf.1 b'
      obtain ⟨a'', rfl⟩ := hf.1 b''
      simpa only [hf.2] using hA.triangle a a' a''
  have backward : ∀ {A B : Diss.{u}} (f : A ⟶ B), acyclicDiss f →
      IsEPMetric B.d → IsEPMetric A.d := by
    intro A B f hf hB
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rw [← hf.2, hB.refl]
    · intro a a'
      rw [← hf.2, ← hf.2, hB.symm]
    · intro a a' a''
      simpa only [hf.2] using hB.triangle (f.1 a) (f.1 a') (f.1 a'')
  have transport : ∀ A B : Diss.{u}, WeaklyEquivalent acyclicDiss A B →
      (IsEPMetric A.d ↔ IsEPMetric B.d) := by
    intro A B h
    induction h with
    | rel A B h =>
      obtain ⟨f, hf⟩ := h
      exact ⟨forward f hf, backward f hf⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (transport P.toDiss X h).mp
    (show IsEPMetric (edist (α := P.carrier)) from ⟨edist_self, edist_comm, edist_triangle⟩)

/-- Lemma 6.2.13 (compact case). -/
theorem compact_of_weaklyEquivalent (P : EPMet.{u}) (X : EPMet.{u}) [CompactSpace P.carrier]
    (h : WeaklyEquivalent acyclicDiss P.toDiss X.toDiss) : CompactSpace X.carrier := by
  classical
  let K : Diss.{u} → Prop := fun A => ∀ x : ℕ → A.carrier,
    ∃ (φ : ℕ → ℕ) (l : A.carrier), StrictMono φ ∧
      Filter.Tendsto (fun n => A.d (x (φ n)) l) Filter.atTop (𝓝 0)
  have transport : ∀ A B : Diss.{u}, WeaklyEquivalent acyclicDiss A B → (K A ↔ K B) := by
    intro A B h
    induction h with
    | rel A B h =>
      obtain ⟨f, hf⟩ := h
      constructor
      · intro hA x
        let y : ℕ → A.carrier := fun n => (hf.1 (x n)).choose
        have hy : ∀ n, f.1 (y n) = x n := fun n => (hf.1 (x n)).choose_spec
        obtain ⟨φ, l, hφ, hl⟩ := hA y
        refine ⟨φ, f.1 l, hφ, ?_⟩
        simpa only [← hy, hf.2] using hl
      · intro hB x
        obtain ⟨φ, l, hφ, hl⟩ := hB (f.1 ∘ x)
        obtain ⟨a, rfl⟩ := hf.1 l
        refine ⟨φ, a, hφ, ?_⟩
        simpa only [Function.comp_apply, hf.2] using hl
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hP : K P.toDiss := by
    intro x
    obtain ⟨l, _, φ, hφ, hl⟩ := (isCompact_univ : IsCompact (Set.univ : Set P.carrier)).isSeqCompact
      (fun n => Set.mem_univ (x n))
    exact ⟨φ, l, hφ, tendsto_iff_edist_tendsto_0.mp hl⟩
  have hX := (transport P.toDiss X.toDiss h).mp hP
  apply isCompact_univ_iff.mp
  rw [isCompact_iff_isSeqCompact]
  intro x _
  obtain ⟨φ, l, hφ, hl⟩ := hX x
  exact ⟨l, Set.mem_univ l, φ, hφ, tendsto_iff_edist_tendsto_0.mpr hl⟩

/-! Helpers for Proposition 6.2.18: the interpolating metrics `((ε - r)/ε) d_P + (r/ε) f*d_Q`. -/

theorem interp_step_up {a b : ℝ≥0∞} {A B T E : ℝ≥0} (hb : b ≤ a + E) :
    (A : ℝ≥0∞) * a + ((B + T : ℝ≥0) : ℝ≥0∞) * b ≤
      ((A + T : ℝ≥0) : ℝ≥0∞) * a + (B : ℝ≥0∞) * b + ((T * E : ℝ≥0) : ℝ≥0∞) := by
  push_cast
  calc (A : ℝ≥0∞) * a + ((B : ℝ≥0∞) + T) * b
      = (A : ℝ≥0∞) * a + (B : ℝ≥0∞) * b + (T : ℝ≥0∞) * b := by ring
    _ ≤ (A : ℝ≥0∞) * a + (B : ℝ≥0∞) * b + (T : ℝ≥0∞) * (a + E) := by gcongr
    _ = ((A : ℝ≥0∞) + T) * a + (B : ℝ≥0∞) * b + (T : ℝ≥0∞) * E := by ring

theorem interp_step_down {a b : ℝ≥0∞} {A B T E : ℝ≥0} (ha : a ≤ b + E) :
    ((A + T : ℝ≥0) : ℝ≥0∞) * a + (B : ℝ≥0∞) * b ≤
      (A : ℝ≥0∞) * a + ((B + T : ℝ≥0) : ℝ≥0∞) * b + ((T * E : ℝ≥0) : ℝ≥0∞) := by
  push_cast
  calc ((A : ℝ≥0∞) + T) * a + (B : ℝ≥0∞) * b
      = (A : ℝ≥0∞) * a + (B : ℝ≥0∞) * b + (T : ℝ≥0∞) * a := by ring
    _ ≤ (A : ℝ≥0∞) * a + (B : ℝ≥0∞) * b + (T : ℝ≥0∞) * (b + E) := by gcongr
    _ = (A : ℝ≥0∞) * a + ((B : ℝ≥0∞) + T) * b + (T : ℝ≥0∞) * E := by ring

theorem interp_isEPMetric {X : Type u} {dP dQ : X → X → ℝ≥0∞} (hP : IsEPMetric dP)
    (hQ : IsEPMetric dQ) (A B : ℝ≥0) :
    IsEPMetric (fun p p' => (A : ℝ≥0∞) * dP p p' + (B : ℝ≥0∞) * dQ p p') where
  refl x := by simp [hP.refl, hQ.refl]
  symm x y := by simp [hP.symm x y, hQ.symm x y]
  triangle x y z := by
    calc (A : ℝ≥0∞) * dP x z + (B : ℝ≥0∞) * dQ x z
        ≤ (A : ℝ≥0∞) * (dP x y + dP y z) + (B : ℝ≥0∞) * (dQ x y + dQ y z) := by
          gcongr
          · exact hP.triangle x y z
          · exact hQ.triangle x y z
      _ = _ := by ring

theorem coeff_split {ε r r' : ℝ≥0} (hε : 0 < ε) (hr : r ≤ r') (hr' : r' ≤ ε) :
    (ε - r) / ε = (ε - r') / ε + (r' - r) / ε ∧ r' / ε = r / ε + (r' - r) / ε ∧
      (r' - r) / ε * ε = r' - r := by
  refine ⟨?_, ?_, div_mul_cancel₀ _ hε.ne'⟩
  · rw [← add_div, tsub_add_tsub_cancel hr' hr]
  · rw [← add_div, add_tsub_cancel_of_le hr]

/-- The convex interpolation of metrics in Proposition 6.2.18. -/
noncomputable def epMetInterp (P Q : EPMet.{u}) {δ : ℝ≥0} (f : hom P Q δ)
    (ε : ℝ≥0) (r : Set.Icc (0 : ℝ≥0) ε) : EPMet.{u} :=
  epMetOfDist (fun x y => (((ε - r.1) / ε : ℝ≥0) : ℝ≥0∞) * edist x y +
    ((r.1 / ε : ℝ≥0) : ℝ≥0∞) * edist (f.1 x) (f.1 y))
    (interp_isEPMetric (dP := fun x y : P.carrier => edist x y)
      (dQ := fun x y => edist (f.1 x) (f.1 y)) ⟨edist_self, edist_comm, edist_triangle⟩
      ⟨fun _ => edist_self _, fun _ _ => edist_comm _ _, fun _ _ _ => edist_triangle _ _ _⟩ _ _)

/-- The interpolating objects in Proposition 6.2.18, with an additional object property. -/
theorem epMet_factorization_with {x y : EPMet.{u}} {ε : ℝ≥0} (hε : 0 < ε)
    (f : hom x y ε) (g : hom y x ε) (hpair : IsInterleavingPair f g)
    (S : EPMet.{u} → Prop) (hS : ∀ r : Set.Icc (0 : ℝ≥0) ε, S (epMetInterp x y f ε r)) :
    ∃ F : CoherentFactorization EPMet.{u} ε,
      IsInterleaved x (F.z (lo ε)) 0 ∧ IsInterleaved (F.z (hi ε)) y 0 ∧ ∀ r, S (F.z r) := by
  have hgf : ∀ p, g.1 (f.1 p) = p := fun p => congrFun (congrArg Subtype.val hpair.1) p
  have hfg : ∀ q, f.1 (g.1 q) = q := fun q => congrFun (congrArg Subtype.val hpair.2) q
  let dP : x.carrier → x.carrier → ℝ≥0∞ := fun p p' => edist p p'
  let dQ : x.carrier → x.carrier → ℝ≥0∞ := fun p p' => edist (f.1 p) (f.1 p')
  have hP : IsEPMetric dP := ⟨fun a => edist_self a, fun a b => edist_comm a b,
    fun a b c => edist_triangle a b c⟩
  have hQ : IsEPMetric dQ := ⟨fun a => edist_self _, fun a b => edist_comm _ _,
    fun a b c => edist_triangle _ _ _⟩
  have hb : ∀ p p', dQ p p' ≤ dP p p' + ε := fun p p' => f.2 p p'
  have ha : ∀ p p', dP p p' ≤ dQ p p' + ε := by
    intro p p'
    have := g.2 (f.1 p) (f.1 p')
    rwa [hgf, hgf] at this
  let d : ℝ≥0 → x.carrier → x.carrier → ℝ≥0∞ := fun r p p' =>
    (((ε - r) / ε : ℝ≥0) : ℝ≥0∞) * dP p p' + ((r / ε : ℝ≥0) : ℝ≥0∞) * dQ p p'
  let z : Set.Icc (0 : ℝ≥0) ε → EPMet.{u} := fun r =>
    epMetOfDist (d r.1) (interp_isEPMetric hP hQ _ _)
  have hup : ∀ (r r' : Set.Icc (0 : ℝ≥0) ε), r ≤ r' → ∀ p p',
      d r'.1 p p' ≤ d r.1 p p' + (((r' : ℝ≥0) - r : ℝ≥0) : ℝ≥0∞) := by
    intro r r' h p p'
    obtain ⟨h1, h2, h3⟩ := coeff_split hε h r'.2.2
    have := interp_step_up (A := (ε - r') / ε) (B := r / ε) (T := (r' - r) / ε) (E := ε)
      (hb p p')
    simp only [d]
    rw [h1, h2]
    rw [h3] at this
    exact this
  have hdown : ∀ (r r' : Set.Icc (0 : ℝ≥0) ε), r ≤ r' → ∀ p p',
      d r.1 p p' ≤ d r'.1 p p' + (((r' : ℝ≥0) - r : ℝ≥0) : ℝ≥0∞) := by
    intro r r' h p p'
    obtain ⟨h1, h2, h3⟩ := coeff_split hε h r'.2.2
    have := interp_step_down (A := (ε - r') / ε) (B := r / ε) (T := (r' - r) / ε) (E := ε)
      (ha p p')
    simp only [d]
    rw [h1, h2]
    rw [h3] at this
    exact this
  have hd0 : ∀ p p', d 0 p p' = dP p p' := by
    intro p p'
    simp [d, div_self hε.ne']
  have hdε : ∀ p p', d ε p p' = dQ p p' := by
    intro p p'
    simp [d, div_self hε.ne']
  refine ⟨{ z := z
            f := fun r r' h => ⟨id, fun p p' => hup r r' h p p'⟩
            g := fun r r' h => ⟨id, fun p p' => hdown r r' h p p'⟩
            pair := fun r r' h => ⟨Subtype.ext rfl, Subtype.ext rfl⟩ }, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨id, fun p p' => ?_⟩, ⟨id, fun p p' => ?_⟩, Subtype.ext rfl, Subtype.ext rfl⟩⟩
    · exact (hd0 p p').le.trans le_self_add
    · exact (hd0 p p').symm.le.trans le_self_add
  · refine ⟨⟨⟨f.1, fun p p' => ?_⟩, ⟨g.1, fun q q' => ?_⟩, Subtype.ext (funext hgf),
      Subtype.ext (funext hfg)⟩⟩
    · exact (hdε p p').symm.le.trans le_self_add
    · refine ((hdε (g.1 q) (g.1 q')).trans ?_).le.trans le_self_add
      change edist (f.1 (g.1 q)) (f.1 (g.1 q')) = edist q q'
      rw [hfg, hfg]


  · intro r; exact hS r

/-- **Proposition 6.2.18.** Metric spaces admit coherent factorizations of interleavings. -/
theorem epMet_admitsCoherentFactorizations : AdmitsCoherentFactorizations EPMet.{u} := by
  intro x y ε hε f g hp
  obtain ⟨F, hx, hy, _⟩ := epMet_factorization_with hε f g hp (fun _ => True) (fun _ => trivial)
  exact ⟨F, hx, hy⟩

/-- The inclusion into dissimilarity spaces, used in Theorem 6.2.20. -/
def epMetToDiss : LPFunctor EPMet.{u} Diss.{u} where
  toFunctor := {
    obj := EPMet.toDiss
    map := fun f => ⟨f.1, f.2⟩
    map_id := fun _ => Subtype.ext rfl
    map_comp := fun _ _ => Subtype.ext rfl }
  map := fun f => ⟨f.1, f.2⟩
  map_zero := fun _ => Subtype.ext rfl
  map_comp := fun _ _ => Subtype.ext rfl
  map_S := fun _ _ => Subtype.ext rfl

/-- Acyclic metric maps are closed under identities and composition, used in Theorem 6.2.20. -/
instance : acyclicEPMet.{u}.IsMultiplicative where
  id_mem P := ⟨Function.surjective_id, fun _ _ => rfl⟩
  comp_mem f g hf hg := ⟨hg.1.comp hf.1, fun x y => (hg.2 _ _).trans (hf.2 x y)⟩

/-- The inclusion of metric spaces preserves quotient interleaving distance, using
Lemma 6.2.13 and the acyclic-cover formula of Theorem 6.2.11. -/
theorem epMet_quotientDist_eq_diss (P Q : EPMet.{u}) :
    quotientInterleavingDist acyclicEPMet P Q =
      quotientInterleavingDist acyclicDiss P.toDiss Q.toDiss := by
  apply le_antisymm
  · rw [(Diss.quotientInterleavingDist_spec).2.2]
    refine le_iInf₂ fun δ h => ?_
    obtain ⟨X, Y, a, b, ha, hb, ⟨f, g, hfg⟩⟩ := h
    have hX := isEPMetric_of_weaklyEquivalent P X (Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ ⟨a, ha⟩))
    have hY := isEPMetric_of_weaklyEquivalent Q Y (Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ ⟨b, hb⟩))
    let X' := epMetOfDist X.d hX
    let Y' := epMetOfDist Y.d hY
    let a' : X' ⟶ P := ⟨a.1, a.2⟩
    let b' : Y' ⟶ Q := ⟨b.1, b.2⟩
    have ha' : WeaklyEquivalent acyclicEPMet X' P := Relation.EqvGen.rel _ _ ⟨a', ha⟩
    have hb' : WeaklyEquivalent acyclicEPMet Y' Q := Relation.EqvGen.rel _ _ ⟨b', hb⟩
    have hI : IsInterleaved X' Y' δ := ⟨⟨⟨f.1, f.2⟩, ⟨g.1, g.2⟩,
      Subtype.ext (congrArg Subtype.val hfg.1), Subtype.ext (congrArg Subtype.val hfg.2)⟩⟩
    calc quotientInterleavingDist acyclicEPMet P Q =
        quotientInterleavingDist acyclicEPMet X' Y' :=
          quotientDist_isInvariant _ _ (weaklyEquivalent_equivalence _) _ _ _ _
            (Relation.EqvGen.symm _ _ ha') (Relation.EqvGen.symm _ _ hb')
      _ ≤ interleavingDist X' Y' := quotientDist_le _ _ _ _
      _ ≤ δ := interleavingDist_le_of_isInterleaved hI
  · exact epMetToDiss.quotientInterleavingDist_le_of_acyclic acyclicEPMet acyclicDiss
      (fun {_ _} _ h => h) P Q

/-- Approximate correspondences with metric spaces force the dissimilarity axioms in
Theorem 6.2.20. The three error bounds are respectively ε, 2ε and 3ε. -/
theorem Diss.metric_defect_bounds {X : Diss.{u}} {Y : EPMet.{u}} {ε : ℝ≥0}
    (h : quotientInterleavingDist acyclicDiss X Y.toDiss < ε) :
    (∀ x, X.d x x ≤ ε) ∧
    (∀ x y, X.d x y ≤ X.d y x + (2 * ε : ℝ≥0)) ∧
    (∀ x y z, X.d x z ≤ X.d x y + X.d y z + (3 * ε : ℝ≥0)) := by
  rw [(Diss.quotientInterleavingDist_spec).2.2] at h
  obtain ⟨δ, hδ⟩ := iInf_lt_iff.mp h
  obtain ⟨⟨A, B, a, b, ha, hb, ⟨f, g, hfg⟩⟩, hδε⟩ := iInf_lt_iff.mp hδ
  have hle : δ ≤ ε := by exact_mod_cast hδε.le
  have hgf : ∀ x, g.1 (f.1 x) = x := fun x => congrFun (congrArg Subtype.val hfg.1) x
  let q (x : X.carrier) : Y.carrier := b.1 (f.1 (ha.1 x).choose)
  have hd (x y : X.carrier) : X.d x y ≤ edist (q x) (q y) + ε ∧
      edist (q x) (q y) ≤ X.d x y + ε := by
    let x' := (ha.1 x).choose
    let y' := (ha.1 y).choose
    have hx : a.1 x' = x := (ha.1 x).choose_spec
    have hy : a.1 y' = y := (ha.1 y).choose_spec
    have hu := f.2 x' y'
    have hv := g.2 (f.1 x') (f.1 y')
    rw [hgf, hgf] at hv
    rw [← hb.2] at hu hv
    rw [← ha.2 x' y', hx, hy] at hu hv
    exact ⟨hv.trans (add_le_add le_rfl (show (δ : ℝ≥0∞) ≤ ε by exact_mod_cast hle)),
      hu.trans (add_le_add le_rfl (show (δ : ℝ≥0∞) ≤ ε by exact_mod_cast hle))⟩
  refine ⟨fun x => by simpa using (hd x x).1, ?_, ?_⟩
  · intro x y
    calc X.d x y ≤ edist (q x) (q y) + ε := (hd x y).1
      _ = edist (q y) (q x) + ε := by rw [edist_comm]
      _ ≤ X.d y x + ε + ε := add_le_add (hd y x).2 le_rfl
      _ = _ := by push_cast; ring
  · intro x y z
    calc X.d x z ≤ edist (q x) (q z) + ε := (hd x z).1
      _ ≤ edist (q x) (q y) + edist (q y) (q z) + ε := add_le_add (edist_triangle _ _ _) le_rfl
      _ ≤ (X.d x y + ε) + (X.d y z + ε) + ε := add_le_add (add_le_add (hd x y).2 (hd y z).2) le_rfl
      _ = _ := by push_cast; ring

/-- The class of metric dissimilarities is closed for the quotient interleaving distance,
the limiting-metric assertion in Proposition 6.2.15 used by Theorem 6.2.20. -/
theorem Diss.isEPMetric_of_approximation (X : Diss.{u})
    (hX : ∀ ε : ℝ≥0, 0 < ε → ∃ Y : EPMet.{u},
      quotientInterleavingDist acyclicDiss X Y.toDiss < ε) : IsEPMetric X.d := by
  have hb (ε : ℝ≥0) (hε : 0 < ε) := (hX ε hε).choose_spec
  refine ⟨?_, ?_, ?_⟩
  · intro x
    apply le_antisymm _ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    simpa using (Diss.metric_defect_bounds (hb ε hε)).1 x
  · intro x y
    suffices hh : ∀ x y, X.d x y ≤ X.d y x from le_antisymm (hh x y) (hh y x)
    intro x y
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hh := (Diss.metric_defect_bounds (hb (ε / 2) (by positivity))).2.1 x y
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)] using hh
  · intro x y z
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hh := (Diss.metric_defect_bounds (hb (ε / 3) (by positivity))).2.2 x y z
    simpa only [mul_div_cancel₀ _ (by norm_num : (3 : ℝ≥0) ≠ 0)] using hh

/-- The completeness step of Theorem 6.2.20, passing the triangle inequality to a
limit in dissimilarity spaces as in Proposition 6.2.15. -/
theorem epMet_quotientDist_complete : IsCompleteDist (quotientInterleavingDist acyclicEPMet.{u}) := by
  intro x hx
  have hx' : ∀ ε : ℝ≥0∞, 0 < ε → ∃ n, ∀ i j, n ≤ i → n ≤ j →
      quotientInterleavingDist acyclicDiss (x i).toDiss (x j).toDiss < ε := by
    simpa only [← epMet_quotientDist_eq_diss] using hx
  obtain ⟨Z, hZ⟩ := (Diss.quotientInterleavingDist_spec).2.1 (fun n => (x n).toDiss) hx'
  have hm : IsEPMetric Z.d := by
    apply Z.isEPMetric_of_approximation
    intro ε hε
    have hev := hZ.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < (ε : ℝ≥0∞) by exact_mod_cast hε))
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
    refine ⟨x n, ?_⟩
    rw [show quotientInterleavingDist acyclicDiss Z (x n).toDiss =
      quotientInterleavingDist acyclicDiss (x n).toDiss Z from
        (quotientDist_isEPMetric _ _).symm _ _]
    exact hn n le_rfl
  let L := epMetOfDist Z.d hm
  refine ⟨L, ?_⟩
  have hL : L.toDiss = Z := by cases Z; rfl
  simpa only [epMet_quotientDist_eq_diss, hL] using hZ

/-- Comparing the two presentations of distortion, used in Theorem 6.2.20. -/
theorem EPMet.diss_distortion_eq (P Q : EPMet.{u}) (R : Set (P.carrier × Q.carrier)) :
    @Diss.distortion P.toDiss Q.toDiss R = distortion R := by
  apply le_antisymm
  · refine iSup₂_le fun p hp => iSup₂_le fun q hq => ?_
    exact le_iSup_of_le p.1 (le_iSup_of_le p.2 (le_iSup_of_le q.1
      (le_iSup_of_le q.2 (le_iSup_of_le hp (le_iSup_of_le hq le_rfl)))))
  · refine iSup_le fun p => iSup_le fun q => iSup_le fun p' => iSup_le fun q' =>
      iSup_le fun hp => iSup_le fun hq => ?_
    exact le_iSup_of_le (p, q) (le_iSup_of_le hp (le_iSup_of_le (p', q')
      (le_iSup_of_le hq le_rfl)))

/-- The correspondence formula for metric spaces, used in Theorem 6.2.20. -/
theorem epMet_quotientDist_eq_gh (P Q : EPMet.{u}) :
    quotientInterleavingDist acyclicEPMet P Q = 2 * gromovHausdorff P Q := by
  rw [epMet_quotientDist_eq_diss, Diss.quotientInterleavingDist_eq_two_mul_gromovHausdorff]
  unfold Diss.gromovHausdorff
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  simp_rw [EPMet.diss_distortion_eq]
  change (⨅ (R : Set (P.carrier × Q.carrier)) (_ : IsCorrespondence R), distortion R) =
    2 * gromovHausdorff P.carrier Q.carrier
  apply le_antisymm
  · refine le_trans (le_sInf fun r hr => ?_) sInf_distortion_le_two_mul_gromovHausdorff
    obtain ⟨R, hR, rfl⟩ := hr
    exact iInf₂_le R hR
  · exact le_iInf₂ fun R hR => two_mul_gromovHausdorff_le_distortion hR

/-- Pointwise choices of two legs covering both spaces, used in Lemma 6.2.19. -/
abbrev CorrChoices (P Q : EPMet.{u}) := (P.carrier → Q.carrier) × (Q.carrier → P.carrier)

/-- The pairs selected by the two legs, used in Lemma 6.2.19. -/
def corrChoicePair {P Q : EPMet.{u}} (p : CorrChoices P Q) : P.carrier ⊕ Q.carrier → P.carrier × Q.carrier
  | Sum.inl x => (x, p.1 x)
  | Sum.inr y => (p.2 y, y)

/-- A distortion bound written as closed pointwise conditions, used in Lemma 6.2.19. -/
def corrChoiceBound (P Q : EPMet.{u}) (δ : ℝ≥0∞) : Set (CorrChoices P Q) :=
  {p | ∀ i j, edist (corrChoicePair p i).1 (corrChoicePair p j).1 ≤
      edist (corrChoicePair p i).2 (corrChoicePair p j).2 + δ ∧
    edist (corrChoicePair p i).2 (corrChoicePair p j).2 ≤
      edist (corrChoicePair p i).1 (corrChoicePair p j).1 + δ}

/-- The conditions bounding distortion are closed, as in Lemma 6.2.19. -/
theorem corrChoiceBound_closed (P Q : EPMet.{u}) (δ : ℝ≥0∞) : IsClosed (corrChoiceBound P Q δ) := by
  have hc (i : P.carrier ⊕ Q.carrier) : Continuous (fun p : CorrChoices P Q => corrChoicePair p i) := by
    cases i with
    | inl x => exact continuous_const.prodMk ((continuous_apply x).comp continuous_fst)
    | inr y => exact ((continuous_apply y).comp continuous_snd).prodMk continuous_const
  simp only [corrChoiceBound, Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  exact (isClosed_le (((hc i).fst).edist ((hc j).fst))
    ((((hc i).snd).edist ((hc j).snd)).add continuous_const)).inter
    (isClosed_le (((hc i).snd).edist ((hc j).snd))
      ((((hc i).fst).edist ((hc j).fst)).add continuous_const))

/-- The correspondence expression for metric-space Gromov–Hausdorff distance,
used in Lemma 6.2.19. -/
theorem EPMet.two_mul_gh_eq_inf (P Q : EPMet.{u}) :
    2 * gromovHausdorff P.carrier Q.carrier =
      ⨅ (R : Set (P.carrier × Q.carrier)) (_ : IsCorrespondence R), distortion R := by
  rw [← epMet_quotientDist_eq_gh P Q, epMet_quotientDist_eq_diss,
    Diss.quotientInterleavingDist_eq_two_mul_gromovHausdorff]
  unfold Diss.gromovHausdorff
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  simp_rw [EPMet.diss_distortion_eq]
  rfl

/-- Approximate correspondences provide nonempty pointwise choice spaces, used in
Lemma 6.2.19. -/
theorem corrChoiceBound_nonempty (P Q : EPMet.{u}) {δ : ℝ≥0∞}
    (hδ : 2 * gromovHausdorff P.carrier Q.carrier < δ) : (corrChoiceBound P Q δ).Nonempty := by
  classical
  rw [P.two_mul_gh_eq_inf Q] at hδ
  obtain ⟨R, hR⟩ := iInf_lt_iff.mp hδ
  obtain ⟨hc, hd⟩ := iInf_lt_iff.mp hR
  choose f hf using hc.1
  choose g hg using hc.2
  have hp (i) : corrChoicePair (f, g) i ∈ R := by
    cases i with
    | inl x => exact hf x
    | inr y => exact hg y
  refine ⟨(f, g), fun i j => ?_⟩
  have hh : (edist (corrChoicePair (f, g) i).1 (corrChoicePair (f, g) j).1 -
      edist (corrChoicePair (f, g) i).2 (corrChoicePair (f, g) j).2) ⊔
      (edist (corrChoicePair (f, g) i).2 (corrChoicePair (f, g) j).2 -
        edist (corrChoicePair (f, g) i).1 (corrChoicePair (f, g) j).1) ≤ δ := by
    exact (show _ ≤ @Diss.distortion P.toDiss Q.toDiss R from
      le_iSup_of_le _ (le_iSup_of_le (hp i) (le_iSup_of_le _ (le_iSup_of_le (hp j) le_rfl)))).trans
      ((P.diss_distortion_eq Q R).trans_le hd.le)
  exact ⟨tsub_le_iff_left.mp (le_sup_left.trans hh), tsub_le_iff_left.mp (le_sup_right.trans hh)⟩

/-- Compactness realizes the optimal distortion bound. This is the compactness assertion
of Lemma 6.2.19, with the two choice functions topologized pointwise. -/
theorem corrChoiceBound_optimal (P Q : EPMet.{u}) [CompactSpace P.carrier] [CompactSpace Q.carrier]
    (hfin : gromovHausdorff P.carrier Q.carrier < ⊤) :
    (corrChoiceBound P Q (2 * gromovHausdorff P.carrier Q.carrier)).Nonempty := by
  classical
  let δ := 2 * gromovHausdorff P.carrier Q.carrier
  have hd : δ ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hfin.ne
  let e (n : ℕ) : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹
  have hepos n : 0 < e n := by dsimp [e]; positivity
  have hanti : Antitone e := by intro n m h; dsimp [e]; exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ h)
  let K n := corrChoiceBound P Q (δ + e n)
  have hn n : (K n).Nonempty := corrChoiceBound_nonempty P Q
    (ENNReal.lt_add_right hd (by exact_mod_cast (hepos n).ne'))
  have hcl n : IsClosed (K n) := corrChoiceBound_closed P Q _
  have hmono {a b : ℝ≥0∞} (hab : a ≤ b) : corrChoiceBound P Q a ⊆ corrChoiceBound P Q b := by
    intro p hp i j
    exact ⟨(hp i j).1.trans (add_le_add le_rfl hab),
      (hp i j).2.trans (add_le_add le_rfl hab)⟩
  have hdir : Directed (· ⊇ ·) K := by
    intro n m
    exact ⟨max n m, hmono (add_le_add le_rfl (by exact_mod_cast hanti (le_max_left n m))),
      hmono (add_le_add le_rfl (by exact_mod_cast hanti (le_max_right n m)))⟩
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K hdir hn
    (fun n => (hcl n).isCompact) hcl
  refine ⟨p, fun i j => ⟨?_, ?_⟩⟩
  all_goals
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨n, hnε⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε by exact_mod_cast hε)
    have he : (e n : ℝ≥0∞) ≤ ε := by
      exact_mod_cast (show e n ≤ ε by rw [← NNReal.coe_le_coe]; simpa [e, one_div] using hnε.le)
    have hh := (Set.mem_iInter.mp hp n) i j
    first
    | exact hh.1.trans (by dsimp [K] at *; rw [add_assoc]; gcongr)
    | exact hh.2.trans (by dsimp [K] at *; rw [add_assoc]; gcongr)

/-- Closing a correspondence preserves its distortion bound, used in Lemma 6.2.19
and the compact interpolation of Theorem 6.2.20. -/
theorem correspondence_closure_bound (P Q : EPMet.{u}) {R : Set (P.carrier × Q.carrier)} {δ : ℝ≥0∞}
    (hR : IsCorrespondence R) (hd : distortion R ≤ δ) :
    IsCorrespondence (closure R) ∧ distortion (closure R) ≤ δ := by
  refine ⟨⟨fun x => let ⟨y, hy⟩ := hR.1 x; ⟨y, subset_closure hy⟩,
    fun y => let ⟨x, hx⟩ := hR.2 y; ⟨x, subset_closure hx⟩⟩, ?_⟩
  let S : Set ((P.carrier × Q.carrier) × (P.carrier × Q.carrier)) :=
    {p | edist p.1.1 p.2.1 ≤ edist p.1.2 p.2.2 + δ ∧
      edist p.1.2 p.2.2 ≤ edist p.1.1 p.2.1 + δ}
  have hl : Continuous (fun p : (P.carrier × Q.carrier) × (P.carrier × Q.carrier) =>
      edist p.1.1 p.2.1) := by fun_prop
  have hr : Continuous (fun p : (P.carrier × Q.carrier) × (P.carrier × Q.carrier) =>
      edist p.1.2 p.2.2) := by fun_prop
  have hs : IsClosed S := (isClosed_le hl (hr.add continuous_const)).inter
    (isClosed_le hr (hl.add continuous_const))
  have hb : R ×ˢ R ⊆ S := by
    rintro ⟨p, q⟩ ⟨hp, hq⟩
    have hh : _ ≤ δ := (show _ ≤ @Diss.distortion P.toDiss Q.toDiss R from
      le_iSup_of_le p (le_iSup_of_le hp (le_iSup_of_le q (le_iSup_of_le hq le_rfl)))).trans
      ((P.diss_distortion_eq Q R).trans_le hd)
    exact ⟨tsub_le_iff_left.mp (le_sup_left.trans hh), tsub_le_iff_left.mp (le_sup_right.trans hh)⟩
  have hc : closure R ×ˢ closure R ⊆ S := by
    rw [← closure_prod_eq]
    exact closure_minimal hb hs
  rw [← P.diss_distortion_eq Q]
  refine iSup₂_le fun p hp => iSup₂_le fun q hq => ?_
  have hh : (p, q) ∈ S := hc (show (p, q) ∈ closure R ×ˢ closure R from ⟨hp, hq⟩)
  exact sup_le (tsub_le_iff_left.mpr hh.1) (tsub_le_iff_left.mpr hh.2)

/-- An optimal compact correspondence, the concrete content of Lemma 6.2.19. -/
theorem EPMet.exists_optimal_compact_correspondence (P Q : EPMet.{u})
    [CompactSpace P.carrier] [CompactSpace Q.carrier]
    (hfin : gromovHausdorff P.carrier Q.carrier < ⊤) :
    ∃ R : Set (P.carrier × Q.carrier), IsCompact R ∧ IsCorrespondence R ∧
      distortion R ≤ 2 * gromovHausdorff P.carrier Q.carrier := by
  obtain ⟨p, hp⟩ := corrChoiceBound_optimal P Q hfin
  let R := Set.range (corrChoicePair p)
  have hR : IsCorrespondence R := ⟨fun x => ⟨p.1 x, Sum.inl x, rfl⟩,
    fun y => ⟨p.2 y, Sum.inr y, rfl⟩⟩
  have hd : distortion R ≤ 2 * gromovHausdorff P.carrier Q.carrier := by
    rw [← P.diss_distortion_eq Q]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact sup_le (tsub_le_iff_left.mpr (hp i j).1) (tsub_le_iff_left.mpr (hp i j).2)
  exact ⟨closure R, isClosed_closure.isCompact, correspondence_closure_bound P Q hR hd⟩

/-- Continuous images of a compact parameter space give compact interpolating metrics.
Used for the repaired compact assertion of Proposition 6.2.18. -/
theorem compact_interpolated_metric {Z : Type u} [PseudoEMetricSpace Z] [CompactSpace Z]
    (P Q : EPMet.{u}) (a : Z → P.carrier) (b : Z → Q.carrier)
    (ha : Continuous a) (hb : Continuous b) (A B : ℝ≥0) (hA : A ≤ 1) (hB : B ≤ 1) :
    let M := epMetOfDist (fun x y => (A : ℝ≥0∞) * edist (a x) (a y) +
      (B : ℝ≥0∞) * edist (b x) (b y))
      (interp_isEPMetric (dP := fun x y => edist (a x) (a y))
        (dQ := fun x y => edist (b x) (b y))
        ⟨fun _ => edist_self _, fun _ _ => edist_comm _ _, fun _ _ _ => edist_triangle _ _ _⟩
        ⟨fun _ => edist_self _, fun _ _ => edist_comm _ _, fun _ _ _ => edist_triangle _ _ _⟩ A B)
    @CompactSpace M.carrier M.str.toUniformSpace.toTopologicalSpace := by
  have hsub (x : ℕ → Z) : ∃ (φ : ℕ → ℕ) (z : Z), StrictMono φ ∧
      Filter.Tendsto (fun n => a (x (φ n))) Filter.atTop (𝓝 (a z)) ∧
      Filter.Tendsto (fun n => b (x (φ n))) Filter.atTop (𝓝 (b z)) := by
    obtain ⟨z, _, φ, hφ, hz⟩ := isSeqCompact_univ (fun n => Set.mem_univ (x n))
    exact ⟨φ, z, hφ, ha.continuousAt.tendsto.comp hz, hb.continuousAt.tendsto.comp hz⟩
  intro M
  letI : PseudoEMetricSpace M.carrier := M.str
  apply isCompact_univ_iff.mp
  apply isCompact_iff_isSeqCompact.mpr
  intro x _
  obtain ⟨φ, z, hφ, haz, hbz⟩ := hsub x
  refine ⟨z, Set.mem_univ _, φ, hφ, ?_⟩
  apply tendsto_iff_edist_tendsto_0.mpr
  have hpa := tendsto_iff_edist_tendsto_0.mp haz
  have hpb := tendsto_iff_edist_tendsto_0.mp hbz
  have hsum : Filter.Tendsto (fun n => edist (a (x (φ n))) (a z) + edist (b (x (φ n))) (b z))
      Filter.atTop (𝓝 0) := by simpa using hpa.add hpb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  change (A : ℝ≥0∞) * edist (a (x (φ n))) (a z) +
      (B : ℝ≥0∞) * edist (b (x (φ n))) (b z) ≤ _
  calc _ ≤ 1 * edist (a (x (φ n))) (a z) + 1 * edist (b (x (φ n))) (b z) := by
        gcongr <;> exact_mod_cast ‹_ ≤ (1 : ℝ≥0)›
    _ = _ := by simp

/-- Compact correspondences yield compact coherent interpolations with acyclic endpoint
covers. This repairs the compactness argument in Proposition 6.2.18. -/
theorem compact_correspondence_factorization (P Q : EPMet.{u})
    {ε : ℝ≥0} (hε : 0 < ε) (R : Set (P.carrier × Q.carrier))
    (hc : IsCompact R) (hR : IsCorrespondence R) (hd : distortion R ≤ ε) :
    ∃ F : CoherentFactorization EPMet.{u} ε,
      IsQuotientInterleaved acyclicEPMet P (F.z (lo ε)) 0 ∧
      IsQuotientInterleaved acyclicEPMet (F.z (hi ε)) Q 0 ∧
      ∀ r, CompactSpace (F.z r).carrier := by
  letI : CompactSpace R := isCompact_iff_compactSpace.mp hc
  let dP : R → R → ℝ≥0∞ := fun x y => edist x.1.1 y.1.1
  let dQ : R → R → ℝ≥0∞ := fun x y => edist x.1.2 y.1.2
  have hp : IsEPMetric dP := ⟨fun _ => edist_self _, fun _ _ => edist_comm _ _, fun _ _ _ => edist_triangle _ _ _⟩
  have hq : IsEPMetric dQ := ⟨fun _ => edist_self _, fun _ _ => edist_comm _ _, fun _ _ _ => edist_triangle _ _ _⟩
  let P' := epMetOfDist dP hp
  let Q' := epMetOfDist dQ hq
  have hb (x y : R) : dP x y ≤ dQ x y + ε ∧ dQ x y ≤ dP x y + ε := by
    have hh : (dP x y - dQ x y) ⊔ (dQ x y - dP x y) ≤ ε :=
      (show _ ≤ @Diss.distortion P.toDiss Q.toDiss R from
        le_iSup_of_le x.1 (le_iSup_of_le x.2 (le_iSup_of_le y.1 (le_iSup_of_le y.2 le_rfl)))).trans
        ((P.diss_distortion_eq Q R).trans_le hd)
    exact ⟨tsub_le_iff_left.mp (le_sup_left.trans hh), tsub_le_iff_left.mp (le_sup_right.trans hh)⟩
  let f : hom P' Q' ε := ⟨id, fun x y => (hb x y).2⟩
  let g : hom Q' P' ε := ⟨id, fun x y => (hb x y).1⟩
  have hfg : IsInterleavingPair f g := ⟨Subtype.ext rfl, Subtype.ext rfl⟩
  have hcompact (r : Set.Icc (0 : ℝ≥0) ε) :
      @CompactSpace (epMetInterp P' Q' f ε r).carrier
        (epMetInterp P' Q' f ε r).str.toUniformSpace.toTopologicalSpace := by
    exact compact_interpolated_metric P Q (fun x : R => x.1.1) (fun x : R => x.1.2)
      (continuous_fst.comp continuous_subtype_val) (continuous_snd.comp continuous_subtype_val)
      ((ε - r.1) / ε) (r.1 / ε) (by exact (div_le_one hε).mpr tsub_le_self)
      (by exact (div_le_one hε).mpr r.2.2)
  obtain ⟨F, hP, hQ, hF⟩ := epMet_factorization_with hε f g hfg
    (fun Z => @CompactSpace Z.carrier Z.str.toUniformSpace.toTopologicalSpace) hcompact
  let a : P' ⟶ P := ⟨fun x => x.1.1, fun _ _ => le_rfl⟩
  let b : Q' ⟶ Q := ⟨fun x => x.1.2, fun _ _ => le_rfl⟩
  have ha : WeaklyEquivalent acyclicEPMet P' P := Relation.EqvGen.rel _ _ ⟨a,
    ⟨fun x => let ⟨y, hy⟩ := hR.1 x; ⟨⟨(x, y), hy⟩, rfl⟩, fun _ _ => rfl⟩⟩
  have hb : WeaklyEquivalent acyclicEPMet Q' Q := Relation.EqvGen.rel _ _ ⟨b,
    ⟨fun y => let ⟨x, hx⟩ := hR.2 y; ⟨⟨(x, y), hx⟩, rfl⟩, fun _ _ => rfl⟩⟩
  exact ⟨F, ⟨P', F.z (lo ε), ha, Relation.EqvGen.refl _, hP⟩,
    ⟨F.z (hi ε), Q', Relation.EqvGen.refl _, hb, hQ⟩, hF⟩

/-- **Proposition 6.2.18 (compact case, repaired).** A compact factorization exists with
quotient-interleaved endpoints.

**Gap (proof gap, Proposition 6.2.18).** The source's convex interpolation on the graph of
an interleaving bijection need not be compact: swapping `1/2` and `3/4` in `[0,1]` gives
a discontinuous bijection. Its graph closure is compact and has the same distortion bound,
but its endpoint projections are surjective isometries, not necessarily bijections.

Lean records the quotient `0`-interleavings supplied by these acyclic projections;
the stronger ordinary `0`-interleaving conclusion is not established by this argument. -/
theorem epMet_coherentFactorizations_compact {P Q : EPMet.{u}} {ε : ℝ≥0} (hε : 0 < ε)
    (f : hom P Q ε) (g : hom Q P ε) (hfg : IsInterleavingPair f g) [CompactSpace P.carrier]
    [CompactSpace Q.carrier] :
    ∃ F : CoherentFactorization EPMet.{u} ε,
      IsQuotientInterleaved acyclicEPMet P (F.z (lo ε)) 0 ∧
      IsQuotientInterleaved acyclicEPMet (F.z (hi ε)) Q 0 ∧
      ∀ r, CompactSpace (F.z r).carrier := by
  have hgf : ∀ x, g.1 (f.1 x) = x := fun x => congrFun (congrArg Subtype.val hfg.1) x
  have hfg' : ∀ y, f.1 (g.1 y) = y := fun y => congrFun (congrArg Subtype.val hfg.2) y
  let R : Set (P.carrier × Q.carrier) := Set.range (fun x => (x, f.1 x))
  have hR : IsCorrespondence R := ⟨fun x => ⟨f.1 x, x, rfl⟩,
    fun y => ⟨g.1 y, g.1 y, by simp only [hfg']⟩⟩
  have hd : distortion R ≤ ε := by
    rw [← P.diss_distortion_eq Q]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have h := g.2 (f.1 a) (f.1 b)
    rw [hgf, hgf] at h
    exact sup_le (tsub_le_iff_left.mpr h) (tsub_le_iff_left.mpr (f.2 a b))
  have hc := correspondence_closure_bound P Q hR hd
  exact compact_correspondence_factorization P Q hε (closure R) isClosed_closure.isCompact hc.1 hc.2

/-- **Theorem 6.2.20.** The quotient interleaving distance of metric spaces is `2 d_GH`,
intrinsic and complete.

Proves only the non-compact part here (the compact part is in
`epMetc_gromovHausdorff`), and establishes the limiting metric by passing the metric-defect
bounds to zero along the complete quotient distance on dissimilarity spaces, implementing the
metric limit argument of Proposition 6.2.15 without reconstructing its weighted limit. -/
theorem epMet_quotientInterleavingDist :
    (∀ P Q : EPMet.{u}, quotientInterleavingDist acyclicEPMet P Q = 2 * gromovHausdorff P Q) ∧
      IsIntrinsicDist (quotientInterleavingDist acyclicEPMet.{u}) ∧
      IsCompleteDist (quotientInterleavingDist acyclicEPMet.{u}) :=
  ⟨epMet_quotientDist_eq_gh, quotientInterleavingDistOf_intrinsic epMet_admitsCoherentFactorizations _
    (weaklyEquivalent_equivalence _), epMet_quotientDist_complete⟩

/-- Quotient interleavings bound the quotient distance, used in the compact case of
Theorem 6.2.20. -/
theorem epMet_quotientDist_le_of_pair {P Q : EPMet.{u}} {δ : ℝ≥0}
    (h : IsQuotientInterleaved acyclicEPMet P Q δ) : quotientInterleavingDist acyclicEPMet P Q ≤ δ := by
  obtain ⟨P', Q', hP, hQ, hI⟩ := h
  calc quotientInterleavingDist acyclicEPMet P Q = quotientInterleavingDist acyclicEPMet P' Q' :=
        quotientDist_isInvariant _ _ (weaklyEquivalent_equivalence _) _ _ _ _
          (Relation.EqvGen.symm _ _ hP) (Relation.EqvGen.symm _ _ hQ)
    _ ≤ interleavingDist P' Q' := quotientDist_le _ _ _ _
    _ ≤ δ := interleavingDist_le_of_isInterleaved hI

/-- The endpoint-patching and length argument of Theorem 4.5.16, used for compact
metric correspondences in Theorem 6.2.20. -/
theorem geodesic_of_short_curves {X : Type w} {d : X → X → ℝ≥0∞} (hE : IsEPMetric d)
    (hc : ∀ p q, d p q < ⊤ → ∃ δ : ℝ≥0, d p q = δ ∧
      ∃ φ : Set.Icc (0 : ℝ≥0) δ → X, d p (φ (lo δ)) = 0 ∧ d (φ (hi δ)) q = 0 ∧
        ∀ r s, d (φ r) (φ s) ≤ edist r s) : IsGeodesicDist d := by
  intro p q hpq
  obtain ⟨δ, hδ, φ, h0, h1, hφ⟩ := hc p q hpq
  by_cases hz : δ = 0
  · subst δ
    have hzero : d p q = 0 := by simpa using hδ
    let f : ℝ → X := fun t => if t = 1 then q else p
    have hf (s t : ℝ) : d (f s) (f t) = 0 := by
      dsimp [f]
      split_ifs <;> first | exact hE.refl _ | exact hzero | simpa only [hE.symm] using hzero
    refine ⟨0, 1, f, zero_le_one, ?_, by simp [f], by simp [f], ?_⟩
    · intro t _ ε hε
      exact ⟨1, one_pos, fun s _ _ => by rw [hf]; exact hε⟩
    · rw [hzero]
      apply le_antisymm _ bot_le
      exact iSup_le fun N => iSup_le fun y => iSup_le fun _ => iSup_le fun _ =>
        iSup_le fun _ => by simp [hf]
  · have hpos : 0 < δ := pos_iff_ne_zero.mpr hz
    let ψ (r : Set.Icc (0 : ℝ≥0) δ) := if r = lo δ then p else if r = hi δ then q else φ r
    have hlohi : lo δ ≠ hi δ := by intro h; exact hz (congrArg Subtype.val h).symm
    have hψ0 : ψ (lo δ) = p := by simp [ψ]
    have hψ1 : ψ (hi δ) = q := by simp [ψ, hlohi.symm]
    have hzφ r : d (ψ r) (φ r) = 0 := by
      dsimp [ψ]
      split_ifs with h h
      · subst r; exact h0
      · subst r; rw [hE.symm]; exact h1
      · exact hE.refl _
    have hψ r s : d (ψ r) (ψ s) ≤ edist r s := by
      calc d (ψ r) (ψ s) ≤ d (ψ r) (φ r) + (d (φ r) (φ s) + d (φ s) (ψ s)) :=
          (hE.triangle _ _ _).trans (add_le_add le_rfl (hE.triangle _ _ _))
        _ = d (φ r) (φ s) := by rw [hzφ, hE.symm (φ s), hzφ]; simp
        _ ≤ _ := hφ r s
    let f : ℝ → X := fun t => ψ (clampIcc δ t)
    have hf s t : d (f s) (f t) ≤ ENNReal.ofReal |s - t| :=
      (hψ _ _).trans (edist_clampIcc δ s t)
    have hf0 : f 0 = p := by dsimp [f]; rw [clampIcc_zero]; exact hψ0
    have hf1 : f δ = q := by dsimp [f]; rw [clampIcc_self]; exact hψ1
    refine ⟨0, δ, f, δ.coe_nonneg, ?_, hf0, hf1, le_antisymm ?_ ?_⟩
    · intro t _ ε hε
      let η := (min ε 1).toReal
      have hη : 0 < η := ENNReal.toReal_pos (by simp [hε.ne']) (by simp)
      refine ⟨η, hη, fun s _ hs => ?_⟩
      exact (hf s t).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hη).mpr hs) |>.trans_le
        (by dsimp [η]; rw [ENNReal.ofReal_toReal (by simp)]; exact min_le_left _ _)
    · rw [hδ]
      refine iSup_le fun N => iSup_le fun y => iSup_le fun hy0 => iSup_le fun hyN =>
        iSup_le fun hm => ?_
      calc ∑ i ∈ Finset.range N, d (f (y i)) (f (y (i + 1))) ≤
          ∑ i ∈ Finset.range N, ENNReal.ofReal (y (i + 1) - y i) := by
            apply Finset.sum_le_sum
            intro i _
            refine (hf (y i) (y (i + 1))).trans ?_
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hm (Nat.le_succ i)))]
        _ = ENNReal.ofReal (y N - y 0) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hm (Nat.le_succ i))), Finset.sum_range_sub]
        _ = δ := by rw [hy0, hyN]; simp
    · have h := dist_le_pathLength_gen d (f := f) δ.coe_nonneg
      simpa only [hf0, hf1] using h

/-- The compact quotient distance is geodesic, using an optimal compact correspondence
and its convex interpolation, as in Theorem 6.2.20. -/
theorem epMetc_quotientDist_geodesic :
    IsGeodesicDist (fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} =>
      quotientInterleavingDist acyclicEPMet P.1 Q.1) := by
  let d := fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} => quotientInterleavingDist acyclicEPMet P.1 Q.1
  have hE : IsEPMetric d := ⟨fun P => (quotientDist_isEPMetric _ _).refl _,
    fun P Q => (quotientDist_isEPMetric _ _).symm _ _,
    fun P Q R => (quotientDist_isEPMetric _ _).triangle _ _ _⟩
  apply geodesic_of_short_curves hE
  intro P Q hfin
  letI := P.2
  letI := Q.2
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0, d P Q = δ := ⟨_, (ENNReal.coe_toNNReal hfin.ne).symm⟩
  refine ⟨δ, hδ, ?_⟩
  by_cases hz : δ = 0
  · exact ⟨fun _ => P, hE.refl P, by simpa only [hz, ENNReal.coe_zero] using hδ,
      fun _ _ => (hE.refl P).le.trans bot_le⟩
  · have hδpos : 0 < δ := pos_iff_ne_zero.mpr hz
    have hgh : gromovHausdorff P.1.carrier Q.1.carrier < ⊤ := by
      have : gromovHausdorff P.1.carrier Q.1.carrier ≤ d P Q := by
        rw [show d P Q = 2 * gromovHausdorff P.1.carrier Q.1.carrier from epMet_quotientDist_eq_gh _ _, two_mul]
        exact le_self_add
      exact this.trans_lt hfin
    obtain ⟨R, hc, hR, hd⟩ := P.1.exists_optimal_compact_correspondence Q.1 hgh
    obtain ⟨F, hP, hQ, hF⟩ := compact_correspondence_factorization P.1 Q.1 hδpos R hc hR
      (by simpa only [← epMet_quotientDist_eq_gh, ← hδ] using hd)
    refine ⟨fun r => ⟨F.z r, hF r⟩, le_antisymm (epMet_quotientDist_le_of_pair hP) bot_le,
      le_antisymm (epMet_quotientDist_le_of_pair hQ) bot_le, ?_⟩
    have hk (r s : Set.Icc (0 : ℝ≥0) δ) (hrs : r ≤ s) :
        quotientInterleavingDist acyclicEPMet (F.z r) (F.z s) ≤ edist r s := by
      refine (quotientDist_le _ _ _ _).trans ((interleavingDist_le_of_isInterleaved
        ⟨⟨F.f r s hrs, F.g r s hrs, F.pair r s hrs⟩⟩).trans ?_)
      have hrs' : (r : ℝ≥0) ≤ s := hrs
      rw [Subtype.edist_eq, edist_nndist, NNReal.nndist_eq, tsub_eq_zero_of_le hrs', zero_max]
    intro r s
    rcases le_total r s with h | h
    · exact hk r s h
    · change quotientInterleavingDist acyclicEPMet (F.z r) (F.z s) ≤ edist r s
      rw [show quotientInterleavingDist acyclicEPMet (F.z r) (F.z s) =
        quotientInterleavingDist acyclicEPMet (F.z s) (F.z r) from
          (quotientDist_isEPMetric _ _).symm _ _, edist_comm]
      exact hk s r h

/-- Scaling the distance scales path length, used to pass from `2 d_GH` to `d_GH`
in Theorem 6.2.20. -/
theorem pathLength_const_mul {X : Type w} (d : X → X → ℝ≥0∞) (c : ℝ≥0∞) (a b : ℝ) (f : ℝ → X) :
    pathLength (fun x y => c * d x y) a b f = c * pathLength d a b f := by
  simp only [pathLength, ENNReal.mul_iSup, Finset.mul_sum]

/-- The geodesic assertion in the compact case of Theorem 6.2.20. -/
theorem epMetc_gh_geodesic :
    IsGeodesicDist (fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} => gromovHausdorff P.1 Q.1) := by
  let d := fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} => quotientInterleavingDist acyclicEPMet P.1 Q.1
  have hhalf : (fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} => gromovHausdorff P.1 Q.1) =
      fun P Q => (2 : ℝ≥0∞)⁻¹ * d P Q := by
    funext P Q
    dsimp [d]
    rw [epMet_quotientDist_eq_gh, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  intro P Q hpq
  obtain ⟨a, b, f, hab, hpath, h0, h1, hlen⟩ := epMetc_quotientDist_geodesic P Q
    (by dsimp [d]; rw [epMet_quotientDist_eq_gh]; exact ENNReal.mul_lt_top (by norm_num) hpq)
  refine ⟨a, b, f, hab, ?_, h0, h1, ?_⟩
  · intro t ht ε hε
    obtain ⟨δ, hδ, hd⟩ := hpath t ht ε hε
    refine ⟨δ, hδ, fun s hs hst => ?_⟩
    exact (show gromovHausdorff (f s).1 (f t).1 ≤ d (f s) (f t) by
      dsimp [d]; rw [epMet_quotientDist_eq_gh, two_mul]; exact le_self_add).trans_lt (hd s hs hst)
  · rw [hhalf, pathLength_const_mul, hlen]

/-- Finite compatible strings in the compact-correspondence construction of the metric
limit in Theorem 6.2.20. -/
def MetricPrefix (P : ℕ → EPMet.{u}) (R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier)) (n : ℕ) :=
  {p : ∀ i : Fin (n + 1), (P i.1).carrier // ∀ i : Fin n, (p i.castSucc, p i.succ) ∈ R i.1}

/-- Dropping the last coordinate of a compatible string, used in Theorem 6.2.20. -/
def MetricPrefix.drop {P : ℕ → EPMet.{u}} {R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier)}
    {n : ℕ} (p : MetricPrefix P R (n + 1)) : MetricPrefix P R n :=
  ⟨fun i => p.1 i.castSucc, fun i => p.2 i.castSucc⟩

/-- Extending a compatible string by one coordinate, used in Theorem 6.2.20. -/
def MetricPrefix.snoc {P : ℕ → EPMet.{u}} {R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier)}
    {n : ℕ} (p : MetricPrefix P R n) (y : (P (n + 1)).carrier)
    (hy : (p.1 (Fin.last n), y) ∈ R n) : MetricPrefix P R (n + 1) := by
  let q : ∀ i : Fin (n + 2), (P i.1).carrier := Fin.snoc p.1 y
  refine ⟨q, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [q] using hy
  · change (q j.castSucc.castSucc, q j.succ.castSucc) ∈ R j.1
    simpa only [q, Fin.snoc_castSucc] using p.2 j

/-- The finite restriction maps are surjective, used in Theorem 6.2.20. -/
theorem MetricPrefix.drop_surjective {P : ℕ → EPMet.{u}} {R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier)}
    (hR : ∀ n, IsCorrespondence (R n)) (n : ℕ) : Function.Surjective (@MetricPrefix.drop P R n) := by
  intro p
  obtain ⟨y, hy⟩ := (hR n).1 (p.1 (Fin.last n))
  exact ⟨p.snoc y hy, Subtype.ext (funext fun i => by simp [MetricPrefix.drop, MetricPrefix.snoc])⟩

/-- Any point extends to a finite string ending at it, used in Theorem 6.2.20. -/
theorem MetricPrefix.exists_last {P : ℕ → EPMet.{u}} {R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier)}
    (hR : ∀ n, IsCorrespondence (R n)) (n : ℕ) (y : (P n).carrier) :
    ∃ p : MetricPrefix P R n, p.1 (Fin.last n) = y := by
  induction n with
  | zero => exact ⟨⟨Fin.cons y (fun i => Fin.elim0 i), fun i => Fin.elim0 i⟩, rfl⟩
  | succ n ih =>
      obtain ⟨x, hx⟩ := (hR n).2 y
      obtain ⟨p, hp⟩ := ih x
      exact ⟨p.snoc y (by rwa [hp]), by simp [MetricPrefix.snoc]⟩

/-- Infinite compatible strings, the compact parameter space for the metric limit in
Theorem 6.2.20. -/
abbrev MetricThreads (P : ℕ → EPMet.{u}) (R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier)) :=
  {p : ∀ n, (P n).carrier // ∀ n, (p n, p (n + 1)) ∈ R n}

/-- Each coordinate projection of the string space is surjective, used in Theorem 6.2.20. -/
theorem MetricThreads.projection_surjective {P : ℕ → EPMet.{u}}
    {R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier)} (hR : ∀ n, IsCorrespondence (R n))
    (n : ℕ) : Function.Surjective (fun p : MetricThreads P R => p.1 n) := by
  intro y
  obtain ⟨p, hp⟩ := MetricPrefix.exists_last hR n y
  let D : ℕᵒᵖ ⥤ Diss.{u} := Functor.ofOpSequence
    (X := fun n => ⟨MetricPrefix P R n, fun _ _ => 0⟩)
    (fun _ => ⟨MetricPrefix.drop, by intro x y; exact le_rfl⟩)
  have hs (k : ℕ) : Function.Surjective (D.map (homOfLE (Nat.le_succ k)).op).1 := by
    dsimp only [D]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact MetricPrefix.drop_surjective hR k
  obtain ⟨z, hz, hzn⟩ := Diss.exists_compatible_of_surj D hs n p
  have hdrop (k : ℕ) : MetricPrefix.drop (z (Opposite.op (k + 1))) = z (Opposite.op k) := by
    have h := hz (homOfLE (Nat.le_succ k)).op
    simpa only [D, Functor.ofOpSequence_map_homOfLE_succ] using h
  let q : MetricThreads P R := ⟨fun k => (z (Opposite.op k)).1 (Fin.last k), by
    intro k
    have hh := (z (Opposite.op (k + 1))).2 (Fin.last k)
    have he := congrArg (fun t : MetricPrefix P R k => t.1 (Fin.last k)) (hdrop k)
    change (z (Opposite.op (k + 1))).1 (Fin.last k).castSucc = (z (Opposite.op k)).1 (Fin.last k) at he
    rwa [he] at hh⟩
  exact ⟨q, by change (z (Opposite.op n)).1 (Fin.last n) = y; rw [hzn, hp]⟩

/-- Closed correspondences make the string space compact, as in the corrected limiting
argument for the compact case of Theorem 6.2.20. -/
theorem MetricThreads.compact {P : ℕ → EPMet.{u}} [∀ n, CompactSpace (P n).carrier]
    {R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier)} (hR : ∀ n, IsClosed (R n)) :
    CompactSpace (MetricThreads P R) := by
  have hcl : IsClosed {p : ∀ n, (P n).carrier | ∀ n, (p n, p (n + 1)) ∈ R n} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun n => (hR n).preimage
      ((continuous_apply n).prodMk (continuous_apply (n + 1)))
  exact isCompact_iff_compactSpace.mp hcl.isCompact

/-- The limiting distance on compatible strings, used in Proposition 6.2.15 and
Theorem 6.2.20. -/
noncomputable def metricThreadDist {P : ℕ → EPMet.{u}}
    {R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier)} (ε : ℕ → ℝ≥0)
    (p q : MetricThreads P R) : ℝ≥0∞ :=
  ⨆ n, edist (p.1 n) (q.1 n) - tailSum ε n

/-- The uniform error bound for the limiting distance, used in Theorem 6.2.20. -/
theorem metricThreadDist_bounds {P : ℕ → EPMet.{u}}
    {R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier)} (ε : ℕ → ℝ≥0) (hε : Summable ε)
    (hR : ∀ n, distortion (R n) ≤ ε n) (p q : MetricThreads P R) (n : ℕ) :
    metricThreadDist ε p q ≤ edist (p.1 n) (q.1 n) + tailSum ε n ∧
      edist (p.1 n) (q.1 n) ≤ metricThreadDist ε p q + tailSum ε n := by
  have hstep k : edist (p.1 k) (q.1 k) ≤ edist (p.1 (k + 1)) (q.1 (k + 1)) + ε k ∧
      edist (p.1 (k + 1)) (q.1 (k + 1)) ≤ edist (p.1 k) (q.1 k) + ε k := by
    have hh : _ ≤ (ε k : ℝ≥0∞) := (show _ ≤ @Diss.distortion (P k).toDiss (P (k + 1)).toDiss (R k) from
      le_iSup_of_le _ (le_iSup_of_le (p.2 k) (le_iSup_of_le _ (le_iSup_of_le (q.2 k) le_rfl)))).trans
        (((P k).diss_distortion_eq (P (k + 1)) (R k)).trans_le (hR k))
    exact ⟨tsub_le_iff_left.mp (le_sup_left.trans hh), tsub_le_iff_left.mp (le_sup_right.trans hh)⟩
  have ha : Monotone (fun k => edist (p.1 k) (q.1 k) - (tailSum ε k : ℝ≥0∞)) := by
    apply monotone_nat_of_le_succ
    intro k
    rw [tailSum_succ hε k]
    push_cast
    calc _ ≤ (edist (p.1 (k + 1)) (q.1 (k + 1)) + ε k) - (ε k + tailSum ε (k + 1)) :=
          tsub_le_tsub_right (hstep k).1 _
      _ = _ := by rw [tsub_add_eq_tsub_tsub, ENNReal.add_sub_cancel_right (ENNReal.coe_ne_top)]
  have hb : Antitone (fun k => edist (p.1 k) (q.1 k) + (tailSum ε k : ℝ≥0∞)) := by
    apply antitone_nat_of_succ_le
    intro k
    calc _ ≤ edist (p.1 k) (q.1 k) + ε k + tailSum ε (k + 1) := add_le_add (hstep k).2 le_rfl
      _ = _ := by rw [tailSum_succ hε k]; push_cast; ring
  constructor
  · apply iSup_le
    intro k
    rcases le_total k n with h | h
    · exact (ha h).trans (tsub_le_self.trans le_self_add)
    · exact tsub_le_self.trans (le_self_add.trans (hb h))
  · exact (tsub_le_iff_right.mp (le_iSup (fun k => edist (p.1 k) (q.1 k) - (tailSum ε k : ℝ≥0∞)) n))

/-- A surjective approximate distance-preserving map bounds quotient distance. Used for
the coordinate projections in the compact limit construction of Theorem 6.2.20. -/
theorem Diss.quotientDist_le_of_surjective {X Y : Diss.{u}} (f : X.carrier → Y.carrier)
    (hf : Function.Surjective f) (ε : ℝ≥0)
    (hd : ∀ x y, X.d x y ≤ Y.d (f x) (f y) + ε ∧ Y.d (f x) (f y) ≤ X.d x y + ε) :
    quotientInterleavingDist acyclicDiss X Y ≤ ε := by
  let R : Set (X.carrier × Y.carrier) := Set.range (fun x => (x, f x))
  have hR : Diss.IsCorrespondence R := ⟨fun x => ⟨f x, x, rfl⟩,
    fun y => let ⟨x, hx⟩ := hf y; ⟨x, x, by simp only [hx]⟩⟩
  rw [Diss.quotientInterleavingDist_eq_two_mul_gromovHausdorff]
  unfold Diss.gromovHausdorff
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  refine iInf₂_le_of_le R hR (iSup₂_le fun p hp => iSup₂_le fun q hq => ?_)
  obtain ⟨x, rfl⟩ := hp
  obtain ⟨y, rfl⟩ := hq
  exact sup_le (tsub_le_iff_left.mpr (hd x y).1) (tsub_le_iff_left.mpr (hd x y).2)

/-- Closed compact correspondences produce a compact metric limit. The uniform metric
bounds are the argument of Proposition 6.2.15; compactness follows from the compact
space of compatible strings, rather than from compactness of unrelated metrics on a set. -/
theorem metricThreadLimit (P : ℕ → EPMet.{u}) [∀ n, CompactSpace (P n).carrier]
    (R : ∀ n, Set ((P n).carrier × (P (n + 1)).carrier))
    (hclosed : ∀ n, IsClosed (R n)) (hR : ∀ n, IsCorrespondence (R n))
    (ε : ℕ → ℝ≥0) (hε : Summable ε) (hd : ∀ n, distortion (R n) ≤ ε n) :
    ∃ Z : EPMet.{u}, (@CompactSpace Z.carrier Z.str.toUniformSpace.toTopologicalSpace) ∧
      ∀ n, quotientInterleavingDist acyclicEPMet Z (P n) ≤ tailSum ε n := by
  let T : TopologicalSpace (MetricThreads P R) := inferInstance
  haveI : CompactSpace (MetricThreads P R) := MetricThreads.compact hclosed
  have hc : @IsCompact (MetricThreads P R) T Set.univ := isCompact_univ
  let D : Diss.{u} := ⟨MetricThreads P R, metricThreadDist ε⟩
  have hdist n : quotientInterleavingDist acyclicDiss D (P n).toDiss ≤ tailSum ε n :=
    Diss.quotientDist_le_of_surjective (X := D) (Y := (P n).toDiss) (fun p : MetricThreads P R => p.1 n) (MetricThreads.projection_surjective hR n) _
      (fun p q => metricThreadDist_bounds ε hε hd p q n)
  have ht : Filter.Tendsto (fun n => tailSum ε n) Filter.atTop (𝓝 0) := by
    have h := NNReal.tendsto_sum_nat_add ε
    simpa only [tailSum, add_comm] using h
  have hte := ENNReal.tendsto_coe.mpr ht
  have hm : IsEPMetric D.d := by
    apply D.isEPMetric_of_approximation
    intro η hη
    have hev := hte.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < η by exact_mod_cast hη))
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
    exact ⟨P n, (hdist n).trans_lt (hn n le_rfl)⟩
  let Z := epMetOfDist D.d hm
  have hZD : Z.toDiss = D := by rfl
  have hcont : @Continuous (MetricThreads P R) Z.carrier T Z.str.toUniformSpace.toTopologicalSpace (fun p => p) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply (@tendsto_iff_edist_tendsto_0 Z.carrier (MetricThreads P R) Z.str
      (@nhds (MetricThreads P R) T p) (fun p => p) p).mpr
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    have hhalf : (0 : ℝ≥0∞) < η / 2 := ENNReal.half_pos hη.ne'
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (hte.eventually (gt_mem_nhds hhalf))
    have hcoord : Filter.Tendsto (fun q : MetricThreads P R => edist (q.1 n) (p.1 n))
        (@nhds (MetricThreads P R) T p) (𝓝 0) :=
      tendsto_iff_edist_tendsto_0.mp (((continuous_apply n).comp continuous_subtype_val).continuousAt.tendsto)
    filter_upwards [(ENNReal.tendsto_nhds_zero.mp hcoord) (η / 2) hhalf] with q hq
    change metricThreadDist ε q p ≤ η
    exact ((metricThreadDist_bounds ε hε hd q p n).1.trans
      (add_le_add hq (hn n le_rfl).le)).trans_eq (ENNReal.add_halves η)
  have hcompact : @CompactSpace Z.carrier Z.str.toUniformSpace.toTopologicalSpace := by
    apply isCompact_univ_iff.mp
    have hi := hc.image hcont
    have he : (fun p : MetricThreads P R => (p : Z.carrier)) '' Set.univ = Set.univ := by
      ext p
      constructor
      · intro _; exact Set.mem_univ _
      · intro _; exact ⟨p, Set.mem_univ _, rfl⟩
    rwa [he] at hi
  exact ⟨Z, hcompact, fun n => by simpa only [epMet_quotientDist_eq_diss, hZD] using hdist n⟩

/-- Compactness of metric limits in Theorem 6.2.20, constructed from a rapidly Cauchy
sequence of optimal closed correspondences. -/
theorem epMetc_quotientDist_complete :
    IsCompleteDist (fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} =>
      quotientInterleavingDist acyclicEPMet P.1 Q.1) := by
  have hE : IsEPMetric (fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} =>
      quotientInterleavingDist acyclicEPMet P.1 Q.1) :=
    ⟨fun P => (quotientDist_isEPMetric _ _).refl _, fun P Q => (quotientDist_isEPMetric _ _).symm _ _,
      fun P Q R => (quotientDist_isEPMetric _ _).triangle _ _ _⟩
  apply isCompleteDist_of_fast hE
  intro x hx
  let P n := (x n).1
  letI : ∀ n, CompactSpace (P n).carrier := fun n => (x n).2
  let ε : ℕ → ℝ≥0 := fun n => (2⁻¹ : ℝ≥0) ^ n
  have hε : Summable ε := (NNReal.hasSum_geometric (by norm_num : (2⁻¹ : ℝ≥0) < 1)).summable
  have hc n : ∃ R : Set ((P n).carrier × (P (n + 1)).carrier), IsClosed R ∧
      IsCorrespondence R ∧ distortion R ≤ ε n := by
    have hq : quotientInterleavingDist acyclicEPMet (P n) (P (n + 1)) < ε n := by
      rw [show quotientInterleavingDist acyclicEPMet (P n) (P (n + 1)) =
        quotientInterleavingDist acyclicEPMet (x (n + 1)).1 (x n).1 from (quotientDist_isEPMetric _ _).symm _ _]
      exact hx n
    have hgh : gromovHausdorff (P n).carrier (P (n + 1)).carrier < ⊤ := by
      have hle : gromovHausdorff (P n).carrier (P (n + 1)).carrier ≤
          quotientInterleavingDist acyclicEPMet (P n) (P (n + 1)) := by
        rw [epMet_quotientDist_eq_gh, two_mul]; exact le_self_add
      exact hle.trans_lt (hq.trans (ENNReal.coe_lt_top))
    obtain ⟨R, _, hR, hd⟩ := (P n).exists_optimal_compact_correspondence (P (n + 1)) hgh
    have hb := correspondence_closure_bound (P n) (P (n + 1)) hR hd
    exact ⟨closure R, isClosed_closure, hb.1, hb.2.trans (by rwa [← epMet_quotientDist_eq_gh] ) |>.trans hq.le⟩
  choose R hclosed hR hd using hc
  obtain ⟨Z, hZ, hz⟩ := metricThreadLimit P R hclosed hR ε hε hd
  refine ⟨⟨Z, hZ⟩, fun n => ?_⟩
  rw [show quotientInterleavingDist acyclicEPMet (x n).1 Z = quotientInterleavingDist acyclicEPMet Z (x n).1
    from (quotientDist_isEPMetric _ _).symm _ _]
  exact hz n

/-- The completeness assertion for compact spaces in Theorem 6.2.20, rescaling the
complete quotient distance by one half. -/
theorem epMetc_gh_complete :
    IsCompleteDist (fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} => gromovHausdorff P.1 Q.1) := by
  intro x hx
  have hq : ∀ η : ℝ≥0∞, 0 < η → ∃ n, ∀ i j, n ≤ i → n ≤ j →
      quotientInterleavingDist acyclicEPMet (x i).1 (x j).1 < η := by
    intro η hη
    obtain ⟨n, hn⟩ := hx (η / 2) (ENNReal.half_pos hη.ne')
    refine ⟨n, fun i j hi hj => ?_⟩
    rw [epMet_quotientDist_eq_gh]
    calc 2 * gromovHausdorff (x i).1 (x j).1 < 2 * (η / 2) := by
          rw [mul_comm (2 : ℝ≥0∞), mul_comm (2 : ℝ≥0∞)]
          exact ENNReal.mul_lt_mul_left (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)
            (hn i j hi hj)
      _ = η := ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

  obtain ⟨L, hL⟩ := epMetc_quotientDist_complete x hq
  refine ⟨L, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL (fun _ => bot_le)
  intro n
  change gromovHausdorff (x n).1 L.1 ≤ quotientInterleavingDist acyclicEPMet (x n).1 L.1
  rw [epMet_quotientDist_eq_gh, two_mul]
  exact le_self_add

/-- Zero Gromov–Hausdorff distance between compact separated spaces realizes an isometry,
the last assertion of Theorem 6.2.20. -/
theorem epMetc_isometry_of_gh_zero (P Q : EPMet.{u}) [CompactSpace P.carrier] [CompactSpace Q.carrier]
    [T0Space P.carrier] [T0Space Q.carrier] (h0 : gromovHausdorff P.carrier Q.carrier = 0) :
    Nonempty (P.carrier ≃ᵢ Q.carrier) := by
  classical
  obtain ⟨R, _, hR, hd⟩ := P.exists_optimal_compact_correspondence Q (by rw [h0]; exact ENNReal.zero_lt_top)
  have he (p q : P.carrier × Q.carrier) (hp : p ∈ R) (hq : q ∈ R) : edist p.1 q.1 = edist p.2 q.2 := by
    have hh : _ ≤ (0 : ℝ≥0∞) := (show _ ≤ @Diss.distortion P.toDiss Q.toDiss R from
      le_iSup_of_le p (le_iSup_of_le hp (le_iSup_of_le q (le_iSup_of_le hq le_rfl)))).trans
      ((P.diss_distortion_eq Q R).trans_le (by simpa only [h0, mul_zero] using hd))
    have hxy : P.toDiss.d p.1 q.1 = Q.toDiss.d p.2 q.2 :=
      le_antisymm (by simpa only [add_zero] using tsub_le_iff_left.mp (le_sup_left.trans hh))
        (by simpa only [add_zero] using tsub_le_iff_left.mp (le_sup_right.trans hh))
    exact hxy
  choose f hf using hR.1
  have hi : Isometry f := fun x y => (he (x, f x) (y, f y) (hf x) (hf y)).symm
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Inseparable.eq
    apply EMetric.inseparable_iff.mpr
    rw [← hi x y, hxy, edist_self]
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hR.2 y
    refine ⟨x, ?_⟩
    apply Inseparable.eq
    apply EMetric.inseparable_iff.mpr
    have hh := he (x, f x) (x, y) (hf x) hx
    simpa only [edist_self] using hh.symm
  exact ⟨{ toEquiv := Equiv.ofBijective f ⟨hinj, hs⟩, isometry_toFun := hi }⟩

/-- **Theorem 6.2.20 (compact case).** On compact metric spaces, `d_GH` is geodesic and
complete, and distance zero gives an isometry for separated spaces.

**Gap (proof gap, Proposition 6.2.15).** The source infers compactness merely from uniform
convergence of metrics on a fixed underlying set. This does not establish completeness
of the limiting metric. Lean instead builds the limit on a compact space of compatible
strings in closed correspondences and proves continuity into the limiting metric.

Realizes an optimal compact correspondence by Tychonoff compactness of two
pointwise choice functions (implementing Lemma 6.2.19) and proves geodesicness/completeness
directly for `gromovHausdorff` (having already established `quotientInterleavingDist = 2 * d_GH`
in `epMet_quotientDist_eq_gh`, using `epMet` covers which remain compact by Lemma 6.2.13); its
convex interpolation has acyclic endpoint covers, and quotient `0`-interleavings suffice for
Theorem 4.5.16. Expresses "(non-pseudo) metric spaces" using `[T0Space]`. -/
theorem epMetc_gromovHausdorff :
    IsGeodesicDist (fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} =>
      gromovHausdorff P.1 Q.1) ∧
    IsCompleteDist (fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} =>
      gromovHausdorff P.1 Q.1) ∧
    ∀ (P Q : EPMet.{u}) [CompactSpace P.carrier] [CompactSpace Q.carrier]
      [T0Space P.carrier] [T0Space Q.carrier], gromovHausdorff P Q = 0 →
        Nonempty (P.carrier ≃ᵢ Q.carrier) := by
  exact ⟨epMetc_gh_geodesic, epMetc_gh_complete, fun P Q => epMetc_isometry_of_gh_zero P Q⟩

/-- Proposition 6.2.21 (universal property of `d_GH`): a function `f` out of ep metric spaces
into an ep metric space `Z` is uniformly continuous for `d_GH` if it is uniformly continuous
for the sup distance between ep metrics on a fixed set, and constant on acyclic covers.

States and proves only the uniform-continuity assertion; omits the second
sentence of Proposition 6.2.21 ("If above we can take `δ = cε`, then `f` is `2c`-Lipschitz"). -/
theorem gromovHausdorff_universal {Z : Type v} [PseudoEMetricSpace Z] (f : EPMet.{u} → Z)
    (hmetric : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ (X : Type u) (d₁ d₂ : X → X → ℝ≥0∞)
      (h₁ : IsEPMetric d₁) (h₂ : IsEPMetric d₂),
      (∀ x y, (d₁ x y - d₂ x y) ⊔ (d₂ x y - d₁ x y) ≤ δ) →
        edist (f (epMetOfDist d₁ h₁)) (f (epMetOfDist d₂ h₂)) ≤ ε)
    (hacyclic : ∀ (P Q : EPMet.{u}) (a : P ⟶ Q), acyclicEPMet.{u} a → edist (f P) (f Q) = 0) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ P Q : EPMet.{u},
      gromovHausdorff P Q < δ → edist (f P) (f Q) ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hmetric ε hε
  refine ⟨min (δ / 2) 1, lt_min (ENNReal.div_pos hδ_pos.ne' (by norm_num)) one_pos, ?_⟩
  intro P Q hPQ
  have h2PQ : 2 * gromovHausdorff P Q < δ := by
    have hlt : gromovHausdorff P Q < δ / 2 := lt_of_lt_of_le hPQ (min_le_left _ _)
    calc 2 * gromovHausdorff P Q = gromovHausdorff P Q + gromovHausdorff P Q := two_mul _
      _ < δ / 2 + δ / 2 := ENNReal.add_lt_add hlt hlt
      _ = 2 * (δ / 2) := (two_mul _).symm
      _ ≤ δ := ENNReal.mul_div_le
  have hsInf : sInf {r | ∃ R : Set (P.carrier × Q.carrier), IsCorrespondence R ∧ r = distortion R} < δ :=
    lt_of_le_of_lt sInf_distortion_le_two_mul_gromovHausdorff h2PQ
  obtain ⟨r, ⟨R, hR, rfl⟩, hdist⟩ := sInf_lt_iff.mp hsInf
  let d₁ : R → R → ℝ≥0∞ := fun p q => edist p.1.1 q.1.1
  let d₂ : R → R → ℝ≥0∞ := fun p q => edist p.1.2 q.1.2
  have h₁ : IsEPMetric d₁ :=
    ⟨fun p => edist_self p.1.1, fun p q => edist_comm p.1.1 q.1.1,
     fun p q s => edist_triangle p.1.1 q.1.1 s.1.1⟩
  have h₂ : IsEPMetric d₂ :=
    ⟨fun p => edist_self p.1.2, fun p q => edist_comm p.1.2 q.1.2,
     fun p q s => edist_triangle p.1.2 q.1.2 s.1.2⟩
  have hdist_le : ∀ x y : R, (d₁ x y - d₂ x y) ⊔ (d₂ x y - d₁ x y) ≤ δ := by
    intro x y
    refine sup_le ?_ ?_
    · exact le_trans (tsub_le_iff_left.mpr (by
        simpa [d₁, d₂, add_comm] using edist_le_edist_add_distortion x.2 y.2)) hdist.le
    · exact le_trans (tsub_le_iff_left.mpr (by
        simpa [d₁, d₂, add_comm] using edist_le_edist_add_distortion' x.2 y.2)) hdist.le
  let P' := epMetOfDist d₁ h₁
  let Q' := epMetOfDist d₂ h₂
  let a : P' ⟶ P := ⟨fun p => p.1.1, fun _ _ => le_rfl⟩
  let b : Q' ⟶ Q := ⟨fun p => p.1.2, fun _ _ => le_rfl⟩
  have ha : acyclicEPMet a := ⟨fun x => let ⟨y, hy⟩ := hR.1 x; ⟨⟨(x, y), hy⟩, rfl⟩, fun _ _ => rfl⟩
  have hb : acyclicEPMet b := ⟨fun y => let ⟨x, hx⟩ := hR.2 y; ⟨⟨(x, y), hx⟩, rfl⟩, fun _ _ => rfl⟩
  have h1 : edist (f P) (f P') = 0 := by
    rw [edist_comm]
    exact hacyclic P' P a ha
  have h2 : edist (f Q') (f Q) = 0 := hacyclic Q' Q b hb
  have h12 : edist (f P') (f Q') ≤ ε := hδ R d₁ d₂ h₁ h₂ hdist_le
  calc edist (f P) (f Q) ≤ edist (f P) (f P') + edist (f P') (f Q) := edist_triangle _ _ _
    _ ≤ edist (f P) (f P') + (edist (f P') (f Q') + edist (f Q') (f Q)) :=
        add_le_add le_rfl (edist_triangle _ _ _)
    _ = edist (f P') (f Q') := by rw [h1, h2, zero_add, add_zero]
    _ ≤ ε := h12

/-- Definition 6.2.22: a pseudo isometry is a map `f : P → Q` that is an isometry onto the
associated separated metric spaces.

Unfolds the source's condition ("`f̄ : P̄ → Q̄` is an isometry" on Kolmogorov
quotients) into the equivalent explicit condition: distance preserving and surjective up to
distance zero. -/
def IsPseudoIsometry {P Q : EPMet.{u}} (f : P ⟶ Q) : Prop :=
  (∀ p p', edist (f.1 p) (f.1 p') = edist p p') ∧ ∀ q, ∃ p, edist (f.1 p) q = 0

/-! Helpers for Lemma 6.2.23: acyclic morphisms induce isometries of Kolmogorov quotients. -/

private def KRel (P Q : EPMet.{u}) : Prop :=
  Nonempty (SeparationQuotient P.carrier ≃ᵢ SeparationQuotient Q.carrier)

private theorem KRel_equiv : Equivalence KRel.{u} where
  refl _ := ⟨IsometryEquiv.refl _⟩
  symm := fun ⟨e⟩ => ⟨e.symm⟩
  trans := fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩

private theorem KRel_of_acyclic {P Q : EPMet.{u}} (f : P ⟶ Q) (hf : acyclicEPMet f) : KRel P Q := by
  obtain ⟨hs, hd⟩ := hf
  have hd' : ∀ x x' : P.carrier, edist (f.1 x) (f.1 x') = edist x x' := hd
  let g : SeparationQuotient P.carrier → SeparationQuotient Q.carrier :=
    SeparationQuotient.lift (fun a => SeparationQuotient.mk (f.1 a)) (by
      intro x y hxy
      rw [EMetric.inseparable_iff] at hxy
      apply Inseparable.eq
      rw [EMetric.inseparable_iff]
      change edist (SeparationQuotient.mk (f.1 x)) (SeparationQuotient.mk (f.1 y)) = 0
      rw [SeparationQuotient.edist_mk, hd', hxy])
  have hg : Isometry g := by
    intro x y
    obtain ⟨a, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk y
    change edist (SeparationQuotient.mk (f.1 a)) (SeparationQuotient.mk (f.1 b)) =
      edist (SeparationQuotient.mk a) (SeparationQuotient.mk b)
    rw [SeparationQuotient.edist_mk, SeparationQuotient.edist_mk, hd']
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk y
    obtain ⟨a, rfl⟩ := hs b
    exact ⟨SeparationQuotient.mk a, rfl⟩
  exact ⟨{ toEquiv := Equiv.ofBijective g ⟨hg.injective, hsurj⟩, isometry_toFun := hg }⟩

/-- the Kolmogorov quotient as an ep metric space -/
private def Kolm (P : EPMet.{u}) : EPMet.{u} := EPMet.mk (SeparationQuotient P.carrier)

private theorem acyclic_mk (P : EPMet.{u}) {A : EPMet.{u}} (e : A.carrier ≃ᵢ P.carrier) :
    ∃ f : A ⟶ Kolm P, acyclicEPMet f := by
  refine ⟨⟨fun a => SeparationQuotient.mk (e a), fun a a' => ?_⟩, ?_, ?_⟩
  · change edist (SeparationQuotient.mk (e a)) (SeparationQuotient.mk (e a')) ≤ edist a a'
    rw [SeparationQuotient.edist_mk]
    exact (e.isometry a a').le
  · intro y
    obtain ⟨b, rfl⟩ := SeparationQuotient.surjective_mk y
    refine ⟨e.symm b, ?_⟩
    change SeparationQuotient.mk (e (e.symm b)) = _
    rw [IsometryEquiv.apply_symm_apply]
  · intro (a : A.carrier) (a' : A.carrier)
    have h := SeparationQuotient.edist_mk (e a) (e a')
    have h2 : edist (e a) (e a') = edist a a' := e.isometry a a'
    exact h.trans h2

private noncomputable def toKolm (P : EPMet.{u}) [T0Space P.carrier] : P.carrier ≃ᵢ SeparationQuotient P.carrier where
  toEquiv := Equiv.ofBijective SeparationQuotient.mk
    ⟨fun x y h => (SeparationQuotient.mk_eq_mk.mp h).eq, SeparationQuotient.surjective_mk⟩
  isometry_toFun := fun x y => (SeparationQuotient.edist_mk x y).symm

/-- Lemma 6.2.23: two (non-pseudo) ep metric spaces are isometric iff they are connected by a
zig-zag of acyclic morphisms.

Specializes the source's conditions (1) (`P̄ ≅ Q̄` on Kolmogorov quotients) and (3)
(zig-zag of `acyclicDiss`) to `[T0Space]` spaces (`P ≅ Q`) and `acyclicEPMet` (equivalent by
Lemma 6.2.13), and omits condition (2) (zig-zag of pseudo isometries) from the statement. -/
theorem isometric_iff_weaklyEquivalent (P Q : EPMet.{u}) [T0Space P.carrier] [T0Space Q.carrier] :
    Nonempty (P.carrier ≃ᵢ Q.carrier) ↔ WeaklyEquivalent acyclicEPMet.{u} P Q := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨f, hf⟩ := acyclic_mk P (IsometryEquiv.refl P.carrier)
    obtain ⟨g, hg⟩ := acyclic_mk P e.symm
    have h1 : Relation.EqvGen (fun a b : EPMet.{u} => ∃ f : a ⟶ b, acyclicEPMet f) P (Kolm P) :=
      Relation.EqvGen.rel _ _ ⟨f, hf⟩
    have h2 : Relation.EqvGen (fun a b : EPMet.{u} => ∃ f : a ⟶ b, acyclicEPMet f) Q (Kolm P) :=
      Relation.EqvGen.rel _ _ ⟨g, hg⟩
    exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.symm _ _ h2)
  · intro h
    have hK : KRel P Q := by
      induction h with
      | rel a b hab => obtain ⟨f, hf⟩ := hab; exact KRel_of_acyclic f hf
      | refl a => exact KRel_equiv.refl a
      | symm a b _ ih => exact KRel_equiv.symm ih
      | trans a b c _ _ ih1 ih2 => exact KRel_equiv.trans ih1 ih2
    obtain ⟨e⟩ := hK
    exact ⟨(toKolm P).trans (e.trans (toKolm Q).symm)⟩


end ScoccolaPhd
