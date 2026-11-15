import ScoccolaPhd.Chapter6Section5ClusteringDiagrams

/-!
# §6.5: stability of the kernel density filtration

Theorem 6.5.22 and its metric-probability-space consequence, Theorem 6.5.1.
The canonical target is iterated persistence with second coordinate `t = -k`.
Both time coordinates and spatial distortion shift by the same amount.
`kdfCurried_uncurry` identifies this with the product-indexed filtration.
-/
open CategoryTheory CategoryTheory.Limits MeasureTheory
open scoped NNReal ENNReal
namespace ScoccolaPhd
open LPCat
universe u v

/-- The diagonal change of enrichment, used to fix the structures in Theorem 6.5.22. -/
def diagonalLPCat {C : Type u} [Category.{v} C] (L : LQPCat (ℝ≥0 × ℝ≥0) C) : LPCat C where
  hom X Y ε := L.hom X Y (ε, ε)
  homZero := L.homZero
  comp := L.comp
  S h := L.S ⟨h, h⟩
  id_comp := L.id_comp
  comp_id := L.comp_id
  assoc := L.assoc
  S_refl := L.S_refl
  S_trans := fun _ _ _ => L.S_trans _ _ _
  comp_S := fun _ _ _ _ => L.comp_S _ _ _ _
  homZero_comp := L.homZero_comp

/-- The canonical weighted-space structure along `(1, 1)` for Theorem 6.5.22. -/
def wDissLPCat : LPCat WDiss.{u} := diagonalLPCat wDissLQPCat

/-- Density-threshold and spatial-error shifts for the target of Theorem 6.5.22. -/
def kdfInnerLPCat : LPCat (ℝ ⥤ Diss.{u}) := diagonalLPCat (persistentLQPCat Diss.{u})

/-- The canonical target structure along `(1, 1, 1)` in Theorem 6.5.22. -/
def kdfLPCat : LPCat (ℝ ⥤ ℝ ⥤ Diss.{u}) :=
  letI := kdfInnerLPCat.{u}
  diagonalLPCat (persistentLQPCat (ℝ ⥤ Diss.{u}))

/-- The density estimate gives the shifted vertex inclusion used in Theorem 6.5.22. -/
lemma kdf_shift_mem {X Y : WDiss.{u}} (K : Kernel) (B δ η a : ℝ≥0)
    (hB : X.IsBoundedBy B) (ha : 0 < a) (haK : a ≤ K.toFun 0)
    (hδη : δ ≤ η * K.inv a) (herr : δ * a + B * (K.toFun 0 - a) ≤ η)
    (f : WDissHom X Y δ δ) (s k : ℝ) (x : X.carrier)
    (hx : k ≤ 0 ∨ (0 < s ∧ ENNReal.ofReal k ≤ X.density K s x)) :
    k - (η : ℝ) ≤ 0 ∨ (0 < s + (η : ℝ) ∧
      ENNReal.ofReal (k - η) ≤ Y.density K (s + η) (f.1 x)) := by
  by_cases hk : k - (η : ℝ) ≤ 0
  · exact Or.inl hk
  obtain ⟨hs, hx⟩ := hx.resolve_left (fun h => hk (by linarith [η.coe_nonneg]))
  refine Or.inr ⟨by linarith [η.coe_nonneg], ?_⟩
  rw [ENNReal.ofReal_sub _ η.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  apply tsub_le_iff_right.mpr
  calc
    ENNReal.ofReal k ≤ X.density K s x := hx
    _ ≤ Y.density K (s + η) (f.1 x) + (δ * a + B * (K.toFun 0 - a) : ℝ≥0) :=
      WDiss.density_morphism_le K B δ η a hB ha haK hδη f s hs.le x
    _ ≤ _ := add_le_add le_rfl (ENNReal.coe_le_coe.mpr herr)

/-- The kernel density filtration with coordinates `(s, t)`, where `t = -k`. -/
noncomputable def kdfCurried (K : Kernel) (X : WDiss.{u}) : ℝ ⥤ ℝ ⥤ Diss.{u} where
  obj s :=
    { obj := fun t => X.kdfObj K s (-t)
      map := fun {t t'} h => ⟨fun p => ⟨p.1, by
        have hk : -t' ≤ -t := neg_le_neg (leOfHom h)
        rcases p.2 with hp | ⟨hs, hp⟩
        · exact Or.inl (hk.trans hp)
        · exact Or.inr ⟨hs, (ENNReal.ofReal_le_ofReal hk).trans hp⟩⟩, fun _ _ => le_rfl⟩
      map_id := by intros; rfl
      map_comp := by intros; rfl }
  map {s s'} h :=
    { app := fun t => ⟨fun p => ⟨p.1, by
        rcases p.2 with hp | ⟨hs, hp⟩
        · exact Or.inl hp
        · exact Or.inr ⟨hs.trans_le (leOfHom h), hp.trans (X.density_mono K (leOfHom h) p.1)⟩⟩,
          fun _ _ => le_rfl⟩
      naturality := by intros; rfl }
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- An approximate weighted map induces a shifted filtration map in Theorem 6.5.22. -/
noncomputable def kdfApproxMap {X Y : WDiss.{u}} (K : Kernel) (B δ η a : ℝ≥0)
    (hB : X.IsBoundedBy B) (ha : 0 < a) (haK : a ≤ K.toFun 0)
    (hδη : δ ≤ η * K.inv a) (herr : δ * a + B * (K.toFun 0 - a) ≤ η)
    (hδ : δ ≤ η) (f : WDissHom X Y δ δ) :
    @hom (ℝ ⥤ ℝ ⥤ Diss.{u}) _ kdfLPCat (kdfCurried K X) (kdfCurried K Y) η := by
  refine ⟨fun s => ⟨fun t => ⟨fun p => ⟨f.1 p.1, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simpa only [neg_add, sub_eq_add_neg] using
      kdf_shift_mem K B δ η a hB ha haK hδη herr f s (-t) p.1 p.2
  · intro p q
    exact (f.2.1 _ _).trans (add_le_add le_rfl (ENNReal.coe_le_coe.mpr hδ))
  · intro t t' ht
    apply Subtype.ext
    funext p
    apply Subtype.ext
    rfl
  · intro s s' hs
    apply Subtype.ext
    funext t
    apply Subtype.ext
    funext p
    apply Subtype.ext
    rfl

/-- The explicit diagonal structure is change of enrichment along `(1, 1)`. -/
lemma diagonalLPCat_changeOfEnrichment {C : Type u} [Category.{v} C] (L : LQPCat (ℝ≥0 × ℝ≥0) C) :
    IsChangeOfEnrichment (pairFamily (1, 1)) L (diagonalLPCat L) := by
  let φ : SuperlinearFamily (ℝ≥0 × ℝ≥0) :=
    { toFun := fun ε => (ε, ε)
      mono := fun _ _ h => ⟨h, h⟩
      map_zero := rfl
      superadd := fun _ _ => le_rfl }
  have hφ : pairFamily (1, 1) = φ := by
    dsimp [pairFamily, φ]
    congr 1
    funext ε
    simp
  rw [hφ]
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro X Y f
    exact (L.S_refl _).symm
  · intro X Y Z ε δ g f
    exact (L.S_refl _).symm
  · intro X Y ε δ h f
    rfl

/-- The density estimate sends interleavings to interleavings in Theorem 6.5.22. -/
lemma kdf_maps_interleavings {X Y : WDiss.{u}} (K : Kernel) (B δ η a : ℝ≥0)
    (hX : X.IsBoundedBy B) (hY : Y.IsBoundedBy B) (ha : 0 < a) (haK : a ≤ K.toFun 0)
    (hδη : δ ≤ η * K.inv a) (herr : δ * a + B * (K.toFun 0 - a) ≤ η)
    (hδ : δ ≤ η) (h : @IsInterleaved WDiss.{u} _ wDissLPCat X Y δ) :
    @IsInterleaved (ℝ ⥤ ℝ ⥤ Diss.{u}) _ kdfLPCat (kdfCurried K X) (kdfCurried K Y) η := by
  letI := wDissLPCat.{u}
  letI := kdfLPCat.{u}
  obtain ⟨⟨f, g, hfg, hgf⟩⟩ := h
  refine ⟨⟨kdfApproxMap K B δ η a hX ha haK hδη herr hδ f,
    kdfApproxMap K B δ η a hY ha haK hδη herr hδ g, ?_, ?_⟩⟩
  · apply Subtype.ext
    funext s
    apply Subtype.ext
    funext t
    apply Subtype.ext
    funext p
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val hfg) p.1
  · apply Subtype.ext
    funext s
    apply Subtype.ext
    funext t
    apply Subtype.ext
    funext p
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val hgf) p.1

/-- Ordinary weighted maps do not decrease density, used in Lemma 6.5.21. -/
lemma WDiss.density_map_le {X Y : WDiss.{u}} (K : Kernel) (f : X ⟶ Y) (s : ℝ) (x : X.carrier) :
    X.density K s x ≤ Y.density K s (f.1 x) := by
  apply lintegral_mono
  intro t
  exact ENNReal.coe_le_coe.mpr (by simpa using f.2.2 x (s.toNNReal * K.inv t.toNNReal))

/-- **Lemma 6.5.21 (morphisms).** The natural map of kernel density filtrations. -/
noncomputable def kdfMap {X Y : WDiss.{u}} (K : Kernel) (f : X ⟶ Y) :
    kdfCurried K X ⟶ kdfCurried K Y where
  app s :=
    { app := fun t => ⟨fun p => ⟨f.1 p.1, by
        rcases p.2 with hp | ⟨hs, hp⟩
        · exact Or.inl hp
        · exact Or.inr ⟨hs, hp.trans (WDiss.density_map_le K f s p.1)⟩⟩, fun p q => by
          simpa only [kdfCurried, WDiss.kdfObj, ENNReal.coe_zero, add_zero] using f.2.1 p.1 q.1⟩
      naturality := by intros; rfl }
  naturality := by intros; rfl

/-- **Lemma 6.5.21 (functor).** Kernel density filtration on weighted spaces. -/
noncomputable def kdfCurriedFunctor (K : Kernel) : WDiss.{u} ⥤ (ℝ ⥤ ℝ ⥤ Diss.{u}) where
  obj := kdfCurried K
  map := kdfMap K
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Levelwise acyclic maps in the iterated-persistence target of Theorem 6.5.22. -/
def kdfAcyclic : MorphismProperty (ℝ ⥤ ℝ ⥤ Diss.{u}) :=
  levelwiseProp (levelwiseProp acyclicDiss)

/-- **Lemma 6.5.21 (acyclic maps).** Kernel density filtrations preserve acyclic maps. -/
lemma kdfMap_acyclic {X Y : WDiss.{u}} (K : Kernel) (f : X ⟶ Y) (hf : acyclicWDiss f) :
    kdfAcyclic (kdfMap K f) := by
  intro s t
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hf.1 y.1
    have heq : X.density K s x = Y.density K s y.1 := by
      apply lintegral_congr
      intro r
      rw [hf.2.2 x _, hx]
    refine ⟨⟨x, ?_⟩, ?_⟩
    · rcases y.2 with hy | ⟨hs, hy⟩
      · exact Or.inl hy
      · exact Or.inr ⟨hs, heq.symm ▸ hy⟩
    · exact Subtype.ext hx
  · intro p q
    exact hf.2.1 p.1 q.1

/-- The kernel height is positive, used to choose the modulus in Theorem 6.5.22. -/
lemma Kernel.zero_pos (K : Kernel) : 0 < K.toFun 0 := by
  by_contra h
  have hz : ∀ u, K.toFun u = 0 := fun u => le_antisymm
    ((K.anti (show 0 ≤ u from zero_le)).trans (le_of_not_gt h)) zero_le
  have hi : (∫⁻ r in Set.Ici (0 : ℝ), (K.toFun r.toNNReal : ℝ≥0∞)) = 0 := by simp [hz]
  exact (ne_of_gt K.integral_pos) hi

/-- The positive modulus obtained by cutting off a short layer tail in Theorem 6.5.22. -/
lemma kdf_modulus (K : Kernel) (B η : ℝ≥0) (hη : 0 < η) :
    ∃ a δ : ℝ≥0, 0 < a ∧ a < K.toFun 0 ∧ 0 < δ ∧ δ ≤ η ∧
      δ ≤ η * K.inv a ∧ δ * a + B * (K.toFun 0 - a) ≤ η := by
  have hK := Kernel.zero_pos K
  let r : ℝ≥0 := min (K.toFun 0 / 2) (η / (2 * (B + 1)))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrK : r ≤ K.toFun 0 / 2 := min_le_left _ _
  have hrη : r ≤ η / (2 * (B + 1)) := min_le_right _ _
  have hrK' : r ≤ K.toFun 0 := hrK.trans (by exact div_le_self (zero_le) (by norm_num))
  let a : ℝ≥0 := K.toFun 0 - r
  have ha : 0 < a := tsub_pos_iff_lt.mpr (by nlinarith [hrK])
  have haK : a < K.toFun 0 := tsub_lt_self hK hr
  have htail : B * (K.toFun 0 - a) ≤ η / 2 := by
    have hrη' := (le_div_iff₀ (show 0 < 2 * (B + 1) by positivity)).mp hrη
    dsimp [a]
    rw [tsub_tsub_cancel_of_le hrK']
    nlinarith
  have hq : 0 < K.inv a := K.inv_pos ha haK
  let δ : ℝ≥0 := min η (min (η * K.inv a) (η / (2 * (a + 1))))
  have hδ : 0 < δ := lt_min hη (lt_min (mul_pos hη hq) (by positivity))
  have hδη : δ ≤ η := min_le_left _ _
  have hδq : δ ≤ η * K.inv a := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ * a ≤ η / 2 := by
    have hh : δ ≤ η / (2 * (a + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (show 0 < 2 * (a + 1) by positivity)).mp hh
    nlinarith
  refine ⟨a, δ, ha, haK, hδ, hδη, hδq, ?_⟩
  nlinarith

/-- A quantitative quotient-distance estimate for Theorem 6.5.22. -/
lemma kdf_quotient_bound (K : Kernel) (B δ η a : ℝ≥0)
    (ha : 0 < a) (haK : a ≤ K.toFun 0)
    (hδη : δ ≤ η * K.inv a) (herr : δ * a + B * (K.toFun 0 - a) ≤ η)
    (hδ : δ ≤ η) (X Y : WDissBounded.{u} B)
    (hxy : @quotientInterleavingDist WDiss.{u} _ wDissLPCat acyclicWDiss X.1 Y.1 < δ) :
    @quotientInterleavingDist (ℝ ⥤ ℝ ⥤ Diss.{u}) _ kdfLPCat kdfAcyclic
      (kdfCurried K X.1) (kdfCurried K Y.1) ≤ η := by
  letI := wDissLPCat.{u}
  letI := kdfLPCat.{u}
  have hW : IsStableUnderWeightedPullbacks acyclicWDiss := isStableUnderWeightedPullbacks_acyclicWDiss wDissLPCat (diagonalLPCat_changeOfEnrichment wDissLQPCat)
  rw [quotientInterleavingDist_eq_inf_acyclicCover hW, iInf_lt_iff] at hxy
  obtain ⟨r, hr⟩ := hxy
  rw [iInf_lt_iff] at hr
  obtain ⟨⟨X', Y', f, g, hf, hg, hint⟩, hr⟩ := hr
  have hrδ : r ≤ δ := ENNReal.coe_le_coe.mp hr.le
  have hX : X'.IsBoundedBy B := fun x r => (hf.2.2 x r).trans_le (X.2 _ _)
  have hY : Y'.IsBoundedBy B := fun y r => (hg.2.2 y r).trans_le (Y.2 _ _)
  have hout := kdf_maps_interleavings K B r η a hX hY ha haK (hrδ.trans hδη)
    ((add_le_add (mul_le_mul_of_nonneg_right hrδ (show 0 ≤ a from zero_le)) le_rfl).trans herr)
    (hrδ.trans hδ) hint
  have hrelX : WeaklyEquivalent kdfAcyclic (kdfCurried K X') (kdfCurried K X.1) :=
    Relation.EqvGen.rel _ _ ⟨kdfMap K f, kdfMap_acyclic K f hf⟩
  have hrelY : WeaklyEquivalent kdfAcyclic (kdfCurried K Y') (kdfCurried K Y.1) :=
    Relation.EqvGen.rel _ _ ⟨kdfMap K g, kdfMap_acyclic K g hg⟩
  calc
    quotientInterleavingDist kdfAcyclic (kdfCurried K X.1) (kdfCurried K Y.1) =
        quotientInterleavingDist kdfAcyclic (kdfCurried K X') (kdfCurried K Y') :=
      (quotientDist_isInvariant interleavingDist (WeaklyEquivalent kdfAcyclic)
        (weaklyEquivalent_equivalence _) _ _ _ _ hrelX hrelY).symm
    _ ≤ interleavingDist (kdfCurried K X') (kdfCurried K Y') := quotientDist_le _ _ _ _
    _ ≤ η := iInf₂_le_of_le η hout le_rfl

/-- **Theorem 6.5.22.** Uniform continuity on bounded weighted dissimilarity spaces.

Uses the repaired finite-layer density from `WDiss.density`, the actual
filtration functor, and explicit canonical persistent structures (`wDissLPCat` and
`kdfLPCat`). Writes the target as iterated persistence (`ℝ ⥤ ℝ ⥤ Diss`) with second
coordinate `t = -k`; `kdfCurried_uncurry` identifies it with the product-indexed filtration
after that coordinate change. The domain is unchanged, and `CompactMPS.density_eq_untruncated`
proves the downstream metric-probability-space filtration is unchanged. The uniform-kernel
clause is separated into `kdf_uniformKernel_lipschitz` (without the bound `B`). See
[`6-5-22-density-repair.md`](6-5-22-density-repair.md). -/
theorem kdf_uniformContinuous (K : Kernel) (B : ℝ≥0) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ X Y : WDissBounded.{u} B,
      @quotientInterleavingDist WDiss.{u} _ wDissLPCat acyclicWDiss X.1 Y.1 < δ →
        @quotientInterleavingDist (ℝ ⥤ ℝ ⥤ Diss.{u}) _ kdfLPCat kdfAcyclic
          (kdfCurried K X.1) (kdfCurried K Y.1) ≤ ε := by
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hη' : 0 < η := ENNReal.coe_pos.mp hη
  obtain ⟨a, δ, ha, haK, hδ, hδη, hδq, herr⟩ := kdf_modulus K B η hη'
  refine ⟨δ, ENNReal.coe_pos.mpr hδ, fun X Y hxy => ?_⟩
  exact (kdf_quotient_bound K B δ η a ha haK.le hδq herr hδη X Y hxy).trans hηε.le
/-- The uniform inverse kernel below height one, used in Theorem 6.5.22. -/
lemma Kernel.uniform_inv {t : ℝ≥0} (ht : t < 1) : Kernel.uniform.inv t = 1 := by
  have he : {u | Kernel.uniform.toFun u ≤ t} = Set.Ici 1 := by
    ext u
    by_cases hu : u < 1
    · simp [Kernel.uniform, hu, ht.not_ge, hu.not_ge]
    · simp [Kernel.uniform, hu, le_of_not_gt hu]
  rw [Kernel.inv, he, csInf_Ici]

/-- For the uniform kernel the repaired density is ball mass at the bandwidth. -/
lemma WDiss.uniform_density (X : WDiss.{u}) (s : ℝ) (x : X.carrier) :
    X.density Kernel.uniform s x = (X.M x s.toNNReal : ℝ≥0∞) := by
  unfold WDiss.density
  have hne : ∀ᵐ t : ℝ, t ≠ 1 := by simp [ae_iff]
  have he : (fun t : ℝ => (X.M x (s.toNNReal * Kernel.uniform.inv t.toNNReal) : ℝ≥0∞)) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) (Kernel.uniform.toFun 0 : ℝ))]
      fun _ => (X.M x s.toNNReal : ℝ≥0∞) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae hne] with t ht hne
    have ht1 : t.toNNReal < 1 := by
      apply Real.toNNReal_lt_iff_lt_coe ht.1.le |>.mpr
      have htle : t ≤ 1 := by simpa [Kernel.uniform] using ht.2
      exact lt_of_le_of_ne htle hne
    rw [Kernel.uniform_inv ht1, mul_one]
  rw [lintegral_congr_ae he]
  simp [lintegral_const, Real.volume_Ioc, Kernel.uniform]

/-- The exact density estimate for the uniform-kernel clause of Theorem 6.5.22. -/
lemma WDiss.uniform_density_morphism_le {X Y : WDiss.{u}} (δ : ℝ≥0) (f : WDissHom X Y δ δ)
    (s : ℝ) (hs : 0 ≤ s) (x : X.carrier) :
    X.density Kernel.uniform s x ≤ Y.density Kernel.uniform (s + δ) (f.1 x) + δ := by
  rw [WDiss.uniform_density, WDiss.uniform_density]
  have hh := ENNReal.coe_le_coe.mpr (f.2.2 x s.toNNReal)
  simpa [Real.toNNReal_add hs δ.coe_nonneg] using hh

/-- The vertex inclusion for the uniform-kernel clause of Theorem 6.5.22. -/
lemma kdf_uniform_shift_mem {X Y : WDiss.{u}} (δ : ℝ≥0) (f : WDissHom X Y δ δ)
    (s k : ℝ) (x : X.carrier)
    (hx : k ≤ 0 ∨ (0 < s ∧ ENNReal.ofReal k ≤ X.density Kernel.uniform s x)) :
    k - (δ : ℝ) ≤ 0 ∨ (0 < s + (δ : ℝ) ∧
      ENNReal.ofReal (k - δ) ≤ Y.density Kernel.uniform (s + δ) (f.1 x)) := by
  by_cases hk : k - (δ : ℝ) ≤ 0
  · exact Or.inl hk
  obtain ⟨hs, hx⟩ := hx.resolve_left (fun h => hk (by linarith [δ.coe_nonneg]))
  refine Or.inr ⟨by linarith [δ.coe_nonneg], ?_⟩
  rw [ENNReal.ofReal_sub _ δ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  exact tsub_le_iff_right.mpr (hx.trans (WDiss.uniform_density_morphism_le δ f s hs.le x))

/-- The uniform kernel preserves the error of an approximate weighted map. -/
noncomputable def kdfUniformApproxMap {X Y : WDiss.{u}} (δ : ℝ≥0) (f : WDissHom X Y δ δ) :
    @hom (ℝ ⥤ ℝ ⥤ Diss.{u}) _ kdfLPCat (kdfCurried Kernel.uniform X)
      (kdfCurried Kernel.uniform Y) δ := by
  refine ⟨fun s => ⟨fun t => ⟨fun p => ⟨f.1 p.1, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simpa only [neg_add, sub_eq_add_neg] using kdf_uniform_shift_mem δ f s (-t) p.1 p.2
  · intro p q
    exact f.2.1 _ _
  · intro t t' ht
    apply Subtype.ext
    funext p
    apply Subtype.ext
    rfl
  · intro s s' hs
    apply Subtype.ext
    funext t
    apply Subtype.ext
    funext p
    apply Subtype.ext
    rfl

/-- The uniform kernel preserves interleaving parameters in Theorem 6.5.22. -/
lemma kdf_uniform_maps_interleavings {X Y : WDiss.{u}} (δ : ℝ≥0)
    (h : @IsInterleaved WDiss.{u} _ wDissLPCat X Y δ) :
    @IsInterleaved (ℝ ⥤ ℝ ⥤ Diss.{u}) _ kdfLPCat
      (kdfCurried Kernel.uniform X) (kdfCurried Kernel.uniform Y) δ := by
  letI := wDissLPCat.{u}
  letI := kdfLPCat.{u}
  obtain ⟨⟨f, g, hfg, hgf⟩⟩ := h
  refine ⟨⟨kdfUniformApproxMap δ f, kdfUniformApproxMap δ g, ?_, ?_⟩⟩
  · apply Subtype.ext
    funext s
    apply Subtype.ext
    funext t
    apply Subtype.ext
    funext p
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val hfg) p.1
  · apply Subtype.ext
    funext s
    apply Subtype.ext
    funext t
    apply Subtype.ext
    funext p
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val hgf) p.1

/-- **Theorem 6.5.22 (uniform kernel).** The filtration is 1-Lipschitz, without a mass bound.

Generalized from `WDissBounded B` to all of `WDiss`, using `kdfCurried` on
`ℝ ⥤ ℝ ⥤ Diss` with `t = -k` and canonical structures `wDissLPCat`, `kdfLPCat`. -/
theorem kdf_uniformKernel_lipschitz (X Y : WDiss.{u}) :
    @quotientInterleavingDist (ℝ ⥤ ℝ ⥤ Diss.{u}) _ kdfLPCat kdfAcyclic
      (kdfCurried Kernel.uniform X) (kdfCurried Kernel.uniform Y) ≤
      @quotientInterleavingDist WDiss.{u} _ wDissLPCat acyclicWDiss X Y := by
  letI := wDissLPCat.{u}
  letI := kdfLPCat.{u}
  have hW : IsStableUnderWeightedPullbacks acyclicWDiss :=
    isStableUnderWeightedPullbacks_acyclicWDiss wDissLPCat (diagonalLPCat_changeOfEnrichment wDissLQPCat)
  rw [quotientInterleavingDist_eq_inf_acyclicCover hW]
  refine le_iInf₂ fun r ⟨X', Y', f, g, hf, hg, hint⟩ => ?_
  have hout := kdf_uniform_maps_interleavings r hint
  have hrelX : WeaklyEquivalent kdfAcyclic (kdfCurried Kernel.uniform X')
      (kdfCurried Kernel.uniform X) :=
    Relation.EqvGen.rel _ _ ⟨kdfMap Kernel.uniform f, kdfMap_acyclic Kernel.uniform f hf⟩
  have hrelY : WeaklyEquivalent kdfAcyclic (kdfCurried Kernel.uniform Y')
      (kdfCurried Kernel.uniform Y) :=
    Relation.EqvGen.rel _ _ ⟨kdfMap Kernel.uniform g, kdfMap_acyclic Kernel.uniform g hg⟩
  calc
    quotientInterleavingDist kdfAcyclic (kdfCurried Kernel.uniform X)
        (kdfCurried Kernel.uniform Y) = quotientInterleavingDist kdfAcyclic
          (kdfCurried Kernel.uniform X') (kdfCurried Kernel.uniform Y') :=
      (quotientDist_isInvariant interleavingDist (WeaklyEquivalent kdfAcyclic)
        (weaklyEquivalent_equivalence _) _ _ _ _ hrelX hrelY).symm
    _ ≤ interleavingDist (kdfCurried Kernel.uniform X') (kdfCurried Kernel.uniform Y') :=
      quotientDist_le _ _ _ _
    _ ≤ r := iInf₂_le_of_le r hout le_rfl

/-- The index change `(s, t) ↦ (s, -t)` used for Theorem 6.5.22. -/
def kdfParameters : ℝ × ℝ ⥤ ℝ × ℝᵒᵖ where
  obj st := (st.1, Opposite.op (-st.2))
  map h := (h.1, (homOfLE (neg_le_neg (leOfHom h.2))).op)

/-- The iterated filtration is exactly the product filtration after the index change. -/
lemma kdfCurried_uncurry (K : Kernel) (X : WDiss.{u}) :
    Functor.uncurry.obj (kdfCurried K X) = kdfParameters ⋙ kdfFunctor K X := by
  rfl

/-- Ball mass is at most one, used for the downstream Theorem 6.5.1. -/
lemma CompactMPS.toWDiss_bounded (X : CompactMPS.{u}) : X.toWDiss.IsBoundedBy 1 := by
  intro x r
  change (X.μ (Metric.ball x (r : ℝ))).toNNReal ≤ 1
  have h : X.μ (Metric.ball x (r : ℝ)) ≤ 1 := by simpa using (measure_mono (Set.subset_univ _) : X.μ (Metric.ball x (r : ℝ)) ≤ X.μ Set.univ)
  simpa using ENNReal.toNNReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) h

/-- **Theorem 6.5.1 (Theorem H).** Uniform continuity of the kernel density filtration
for the Gromov–Hausdorff–Prokhorov distance.

Uses the iterated-persistence target `kdfCurried` on `ℝ ⥤ ℝ ⥤ Diss` with
`t = -k` and canonical structures (`kdfLPCat`, `kdfAcyclic`); the uniform-kernel 2-Lipschitz
clause is stated separately in `kdf_ghp_uniformKernel_lipschitz`. -/
theorem kdf_ghp_uniformContinuous (K : Kernel) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ X Y : CompactMPS.{u},
      ghpDist X Y < δ →
        @quotientInterleavingDist (ℝ ⥤ ℝ ⥤ Diss.{u}) _ kdfLPCat kdfAcyclic
          (kdfCurried K X.toWDiss) (kdfCurried K Y.toWDiss) ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := kdf_uniformContinuous.{u} K 1 ε hε
  obtain ⟨γ, hγ, hγδ⟩ := ENNReal.exists_nnreal_pos_mul_lt (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hδ.ne'
  refine ⟨γ, ENNReal.coe_pos.mpr hγ, fun X Y hxy => ?_⟩
  apply hmod ⟨X.toWDiss, CompactMPS.toWDiss_bounded X⟩ ⟨Y.toWDiss, CompactMPS.toWDiss_bounded Y⟩
  calc
    _ ≤ 2 * ghpDist X Y := quotientInterleavingDist_wDiss_le_ghp wDissLPCat
      (diagonalLPCat_changeOfEnrichment wDissLQPCat) X Y
    _ ≤ 2 * (γ : ℝ≥0∞) := mul_le_mul_of_nonneg_left hxy.le (by positivity)
    _ < δ := by simpa [mul_comm] using hγδ

/-- **Theorem 6.5.1 (uniform kernel).** The filtration is 2-Lipschitz for the
Gromov–Hausdorff–Prokhorov distance.

States the uniform-kernel clause separately from `kdf_ghp_uniformContinuous`,
using `kdfCurried` on `ℝ ⥤ ℝ ⥤ Diss` with `t = -k`. -/
theorem kdf_ghp_uniformKernel_lipschitz (X Y : CompactMPS.{u}) :
    @quotientInterleavingDist (ℝ ⥤ ℝ ⥤ Diss.{u}) _ kdfLPCat kdfAcyclic
      (kdfCurried Kernel.uniform X.toWDiss) (kdfCurried Kernel.uniform Y.toWDiss) ≤
        2 * ghpDist X Y :=
  (kdf_uniformKernel_lipschitz X.toWDiss Y.toWDiss).trans
    (quotientInterleavingDist_wDiss_le_ghp wDissLPCat (diagonalLPCat_changeOfEnrichment wDissLQPCat) X Y)
end ScoccolaPhd
