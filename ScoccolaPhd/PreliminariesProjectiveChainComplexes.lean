import Mathlib

/-!
# Projective generators for connective chain complexes

Background cited in Chapter 2, Example 2.5.9: the generating maps and smallness
arguments for the projective model structure on connective complexes of modules.

The index of `disk R n` is its lower degree. Thus its two nonzero modules are
in degrees `n` and `n + 1`, and its differential between them is the identity.
The sphere `sphere R n` has a single copy of `R` in degree `n`.

The generating trivial cofibrations are the zero maps into these disks.
Their right lifting class consists of maps surjective in every positive degree:
a map from the disk represents an arbitrary element in its top degree.
The universal property of the rank-one free module converts the lifting problem
into the existence of a preimage of that element.

The generating cofibrations also include the boundary inclusions into disks.
They must include the separate generator from zero into the degree-zero sphere,
since the boundary inclusions alone do not test degree-zero homology.
Their right lifting class consists of the positive-degree surjective
quasi-isomorphisms. The proof uses cycles and boundaries explicitly:
lifting a boundary square prescribes both a top element and its differential.
The converse first lifts a homology class and then corrects its representative
by a boundary to produce an actual lift of the original cycle.

Both families are countable. The domains of the trivial cofibrations are zero,
so their representable functors preserve connected colimits. The other domains
are spheres. Their finite presentability is proved directly: an element lifts
to some stage of a filtered colimit, and its single cycle equation holds at a
later stage. Equality of maps also holds at a later stage. These facts provide
the hypotheses of the small object argument with the first infinite cardinal.

For the remaining recognition condition, `cover Y` is an explicit contractible
complex mapping onto `Y` in positive degrees. Its module in degree zero is
`Y.X 1`, and its module in degree `n + 1` is `Y.X (n + 2) × Y.X (n + 1)`.
The differential sends `(a,b)` to `(b,0)`, with the evident modification at zero.
The contraction sends `(a,b)` to `(0,a)`. The augmentation sends `(a,b)` to
`d a + b`. Factoring through the direct sum with this cover makes any map
lifting against the fibrations a retract of a homotopy equivalence.
-/

universe v

namespace ScoccolaPhd

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

/-- Morphisms of chain complexes that are epimorphisms in positive degrees. -/
def positiveDegreeSurjections (R : Type v) [CommRing R] :
    MorphismProperty (ChainComplex (ModuleCat.{v} R) ℕ) :=
  fun _ _ f => ∀ n : ℕ, n ≥ 1 → Epi (f.f n)

lemma terminal_in_positiveDegreeSurjections (R : Type v) [CommRing R]
    (X T : ChainComplex (ModuleCat.{v} R) ℕ) (t : X ⟶ T) (hT : IsTerminal T) :
    positiveDegreeSurjections R t := by
  intro n _
  have hTn : IsZero (T.X n) := Functor.map_isZero (HomologicalComplex.eval _ _ n) hT.isZero
  exact hTn.epi (t.f n)

/-! The sphere and disk complexes used for the projective generators of Example 2.5.9.
The disk indexed by n is supported in degrees n and n+1. -/

namespace ProjectiveGenerators

open ZeroObject

/-- The rank-one sphere used in the generators for Example 2.5.9. -/
noncomputable abbrev sphere (R : Type v) [CommRing R] (n : ℕ) :
    ChainComplex (ModuleCat.{v} R) ℕ :=
  (HomologicalComplex.single (ModuleCat.{v} R) (ComplexShape.down ℕ) n).obj
    (ModuleCat.of R R)

/-- The supporting component of the rank-one sphere. -/
noncomputable def sphereIso (R : Type v) [CommRing R] (n : ℕ) :
    (sphere R n).X n ≅ ModuleCat.of R R :=
  HomologicalComplex.singleObjXSelf _ n _

lemma differential_apply_differential {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) (i j k : ℕ) (x : Y.X i) :
    Y.d j k (Y.d i j x) = 0 := by
  have h := congrArg (fun f : Y.X i ⟶ Y.X k => f x) (Y.d_comp_d i j k)
  exact h

/-- A cycle determines a chain map from its rank-one sphere. -/
noncomputable def sphereTo {R : Type v} [CommRing R] (n : ℕ)
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (φ : ModuleCat.of R R ⟶ K.X n)
    (hφ : φ ≫ K.d n (n - 1) = 0) : sphere R n ⟶ K :=
  HomologicalComplex.mkHomFromSingle φ (by
    intro k hk
    have hk' : n - 1 = k := by simp only [ComplexShape.down_Rel] at hk; omega
    subst k
    exact hφ)

@[simp]
lemma sphereTo_top {R : Type v} [CommRing R] (n : ℕ)
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (φ : ModuleCat.of R R ⟶ K.X n)
    (hφ : φ ≫ K.d n (n - 1) = 0) :
    (sphereIso R n).inv ≫ (sphereTo n K φ hφ).f n = φ := by
  simp [sphereIso, sphereTo, ← Category.assoc]

/-- The component of a sphere map is a cycle. -/
lemma sphereMap_cycle {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f : sphere R n ⟶ K) :
    ((sphereIso R n).inv ≫ f.f n) ≫ K.d n (n - 1) = 0 := by
  rw [Category.assoc, f.comm]
  simp [sphere]

/-- Maps out of a sphere are determined by their supporting component. -/
lemma sphere_hom_ext {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f g : sphere R n ⟶ K)
    (h : f.f n = g.f n) : f = g :=
  HomologicalComplex.from_single_hom_ext h

/-- Reconstruction of a sphere map from its cycle. -/
lemma sphereTo_eta {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f : sphere R n ⟶ K) :
    sphereTo n K ((sphereIso R n).inv ≫ f.f n) (sphereMap_cycle n f) = f := by
  apply sphere_hom_ext n
  apply (cancel_epi (sphereIso R n).inv).mp
  exact sphereTo_top n K _ _

/-- Linear maps out of the rank-one free module are determined by the image of `1`. -/
lemma rankOne_hom_ext {R : Type v} [CommRing R] {M : ModuleCat.{v} R}
    (f g : ModuleCat.of R R ⟶ M) (h : f (1 : R) = g (1 : R)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact h

/-- The linear map corresponding to an element of a module. -/
noncomputable def elementMap {R : Type v} [CommRing R] {M : ModuleCat.{v} R}
    (x : M) : ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

@[simp]
lemma elementMap_one {R : Type v} [CommRing R] {M : ModuleCat.{v} R} (x : M) :
    elementMap x (1 : R) = x := by simp [elementMap]

@[simp]
lemma elementMap_eta {R : Type v} [CommRing R] {M : ModuleCat.{v} R}
    (f : ModuleCat.of R R ⟶ M) : elementMap (f (1 : R)) = f := by
  apply rankOne_hom_ext
  simp [elementMap]

/-- The cycle represented by a sphere map. -/
noncomputable def sphereValue {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f : sphere R n ⟶ K) : K.X n :=
  ((sphereIso R n).inv ≫ f.f n) (1 : R)

/-- A cycle, regarded as a sphere map. -/
noncomputable def sphereElement {R : Type v} [CommRing R] (n : ℕ)
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (x : K.X n)
    (hx : K.d n (n - 1) x = 0) : sphere R n ⟶ K :=
  sphereTo n K (elementMap x) (by
    apply rankOne_hom_ext
    simpa [ModuleCat.comp_apply, elementMap] using hx)

@[simp]
lemma sphereElement_value {R : Type v} [CommRing R] (n : ℕ)
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (x : K.X n)
    (hx : K.d n (n - 1) x = 0) : sphereValue n (sphereElement n K x hx) = x := by
  unfold sphereValue sphereElement
  rw [sphereTo_top]
  exact elementMap_one x

lemma sphereValue_cycle {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f : sphere R n ⟶ K) :
    K.d n (n - 1) (sphereValue n f) = 0 := by
  have h := congrArg (fun φ : ModuleCat.of R R ⟶ K.X (n - 1) => φ (1 : R))
    (sphereMap_cycle n f)
  change K.d n (n - 1) (sphereValue n f) = 0 at h
  exact h

/-- A sphere map is determined by its represented cycle. -/
lemma sphere_hom_ext_value {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f g : sphere R n ⟶ K)
    (h : sphereValue n f = sphereValue n g) : f = g := by
  apply sphere_hom_ext n
  apply (cancel_epi (sphereIso R n).inv).mp
  exact rankOne_hom_ext _ _ h

@[simp]
lemma sphereValue_comp {R : Type v} [CommRing R] (n : ℕ)
    {K L : ChainComplex (ModuleCat.{v} R) ℕ} (f : sphere R n ⟶ K) (g : K ⟶ L) :
    sphereValue n (f ≫ g) = g.f n (sphereValue n f) := by
  simp [sphereValue, HomologicalComplex.comp_f, ← Category.assoc, ModuleCat.comp_apply]

@[simp]
lemma sphereValue_zero {R : Type v} [CommRing R] (n : ℕ)
    (K : ChainComplex (ModuleCat.{v} R) ℕ) :
    sphereValue n (0 : sphere R n ⟶ K) = 0 := by
  simp [sphereValue]

/-- Degreewise underlying sets, used to express finite presentability of the generators. -/
def complexElements (R : Type v) [CommRing R] (n : ℕ) :
    ChainComplex (ModuleCat.{v} R) ℕ ⥤ Type v :=
  HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.down ℕ) n ⋙ forget _

instance complexElements_preservesFilteredColimits (R : Type v) [CommRing R] (n : ℕ) :
    PreservesFilteredColimits (complexElements R n) := by
  unfold complexElements
  have : PreservesFilteredColimitsOfSize.{v, v}
      (HomologicalComplex.eval (ModuleCat.{v} R) (ComplexShape.down ℕ) n) :=
    ⟨fun J _ _ => by infer_instance⟩
  exact comp_preservesFilteredColimits _ _

set_option backward.isDefEq.respectTransparency false in
/-- A rank-one sphere is finitely presentable. A cycle lifts to one stage of a
filtered colimit; its one differential equation holds at a later stage. -/
instance sphere_finitelyPresentable (R : Type v) [CommRing R] (n : ℕ) :
    IsFinitelyPresentable.{v} (sphere R n) := by
  have : Fact Cardinal.aleph0.{v}.IsRegular := Cardinal.fact_isRegular_aleph0
  apply IsCardinalPresentable.mk
  intro J _ _ F c hc
  have : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  let hn := isColimitOfPreserves (complexElements R n) hc
  let hl := isColimitOfPreserves (complexElements R (n - 1)) hc
  constructor
  · intro g
    obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hn (sphereValue n g)
    change (F.obj j).X n at x
    change (c.ι.app j).f n x = sphereValue n g at hx
    let y := (F.obj j).d n (n - 1) x
    have hy : (c.ι.app j).f (n - 1) y = (c.ι.app j).f (n - 1) 0 := by
      have h := congrArg (fun φ : (F.obj j).X n ⟶ c.pt.X (n - 1) => φ x)
        ((c.ι.app j).comm n (n - 1))
      change c.pt.d n (n - 1) ((c.ι.app j).f n x) = (c.ι.app j).f (n - 1) y at h
      rw [hx, sphereValue_cycle] at h
      simpa only [map_zero] using h.symm
    obtain ⟨k, a, ha⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hl y (0 : (F.obj j).X (n - 1))).mp hy
    change (F.map a).f (n - 1) y = (F.map a).f (n - 1) 0 at ha
    let x' := (F.map a).f n x
    have hx' : (F.obj k).d n (n - 1) x' = 0 := by
      have h := congrArg (fun φ : (F.obj j).X n ⟶ (F.obj k).X (n - 1) => φ x)
        ((F.map a).comm n (n - 1))
      change (F.obj k).d n (n - 1) x' = (F.map a).f (n - 1) y at h
      rw [h, ha, map_zero]
    refine ⟨k, sphereElement n (F.obj k) x' hx', ?_⟩
    apply sphere_hom_ext_value n
    rw [sphereValue_comp, sphereElement_value]
    have h := congrArg (fun f : F.obj j ⟶ c.pt => f.f n x) (c.w a)
    exact h.trans hx
  · intro j f₁ f₂ h
    have he : (c.ι.app j).f n (sphereValue n f₁) =
        (c.ι.app j).f n (sphereValue n f₂) := by
      simpa only [sphereValue_comp] using congrArg (sphereValue n) h
    obtain ⟨k, a, ha⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hn (sphereValue n f₁) (sphereValue n f₂)).mp he
    change (F.map a).f n (sphereValue n f₁) = (F.map a).f n (sphereValue n f₂) at ha
    refine ⟨k, a, ?_⟩
    apply sphere_hom_ext_value n
    simpa only [sphereValue_comp] using ha

/-- Degreewise objects of the disk used in Example 2.5.9. -/
noncomputable abbrev diskX (R : Type v) [CommRing R] (n i : ℕ) : ModuleCat.{v} R :=
  if i = n ∨ i = n + 1 then ModuleCat.of R R else 0

/-- The sole nonzero differential of the disk is the identity of `R`. -/
noncomputable def diskD (R : Type v) [CommRing R] (n i : ℕ) :
    diskX R n (i + 1) ⟶ diskX R n i :=
  if h : i = n then
    eqToHom (show diskX R n (i + 1) = diskX R n i by simp [diskX, h])
  else 0

lemma diskD_sq (R : Type v) [CommRing R] (n i : ℕ) :
    diskD R n (i + 1) ≫ diskD R n i = 0 := by
  by_cases h : i = n
  · have h' : i + 1 ≠ n := by omega
    simp [diskD, h']
  · simp [diskD, h]

/-- The rank-one disk with top degree `n + 1`, used in Example 2.5.9. -/
noncomputable abbrev disk (R : Type v) [CommRing R] (n : ℕ) :
    ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (diskX R n) (diskD R n) (diskD_sq R n)

/-- The upper component of a disk is the free rank-one module. -/
noncomputable def diskTopIso (R : Type v) [CommRing R] (n : ℕ) :
    (disk R n).X (n + 1) ≅ ModuleCat.of R R :=
  eqToIso (by simp [disk, diskX])

instance disk_d_isIso (R : Type v) [CommRing R] (n : ℕ) :
    IsIso ((disk R n).d (n + 1) n) := by
  simp only [disk, ChainComplex.of_d]
  dsimp only [diskD]
  rw [dif_pos rfl]
  infer_instance

/-- Outside its two supporting degrees, a disk is zero. -/
lemma disk_isZero (R : Type v) [CommRing R] (n i : ℕ)
    (h : i ≠ n) (h' : i ≠ n + 1) : IsZero ((disk R n).X i) := by
  change IsZero (diskX R n i)
  simp only [diskX, if_neg (not_or_intro h h')]
  exact isZero_zero _

/-- Maps out of a disk are determined by their top-degree component. -/
lemma disk_hom_ext {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f g : disk R n ⟶ K)
    (h : f.f (n + 1) = g.f (n + 1)) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = n + 1
  · subst i; exact h
  · by_cases hi' : i = n
    · subst i
      apply (cancel_epi ((disk R n).d (n + 1) n)).mp
      rw [← f.comm, ← g.comm, h]
    · exact (disk_isZero R n i hi' hi).eq_of_src _ _

/-- Components of the map out of a disk specified by its top-degree component. -/
noncomputable def diskToF {R : Type v} [CommRing R] (n : ℕ)
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (φ : ModuleCat.of R R ⟶ K.X (n + 1))
    (i : ℕ) : (disk R n).X i ⟶ K.X i :=
  if h : i = n + 1 then
    eqToHom (show (disk R n).X i = ModuleCat.of R R by simp [disk, diskX, h]) ≫
      φ ≫ eqToHom (congrArg K.X h.symm)
  else if h' : i = n then
    eqToHom (show (disk R n).X i = ModuleCat.of R R by simp [disk, diskX, h']) ≫
      φ ≫ K.d (n + 1) n ≫ eqToHom (congrArg K.X h'.symm)
  else 0

lemma diskToF_comm {R : Type v} [CommRing R] (n : ℕ)
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (φ : ModuleCat.of R R ⟶ K.X (n + 1))
    (i : ℕ) :
    diskToF n K φ (i + 1) ≫ K.d (i + 1) i =
      (disk R n).d (i + 1) i ≫ diskToF n K φ i := by
  by_cases h : i = n
  · subst i
    dsimp [diskToF, disk, diskD, diskX]
    simp
    dsimp only [diskD]
    rw [dif_pos rfl]
    simp
  · by_cases h' : i + 1 = n
    · have hn : i + 1 ≠ n + 1 := by omega
      simp [diskToF, disk, diskD, h, h', hn, Category.assoc]
    · have hn : i + 1 ≠ n + 1 := by omega
      simp [diskToF, disk, diskD, h, h', hn]

/-- A map out of a disk is freely specified by a map out of `R` in its top degree. -/
noncomputable def diskTo {R : Type v} [CommRing R] (n : ℕ)
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (φ : ModuleCat.of R R ⟶ K.X (n + 1)) :
    disk R n ⟶ K :=
  ChainComplex.ofHom (diskToF n K φ) (diskToF_comm n K φ)

@[simp]
lemma diskTo_top {R : Type v} [CommRing R] (n : ℕ)
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (φ : ModuleCat.of R R ⟶ K.X (n + 1)) :
    (diskTopIso R n).inv ≫ (diskTo n K φ).f (n + 1) = φ := by
  simp [diskTopIso, diskTo, diskToF]

/-- Reconstruction of a disk map from its top-degree component. -/
lemma diskTo_eta {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f : disk R n ⟶ K) :
    diskTo n K ((diskTopIso R n).inv ≫ f.f (n + 1)) = f := by
  apply disk_hom_ext n
  apply (cancel_epi (diskTopIso R n).inv).mp
  exact diskTo_top n K _

@[reassoc]
lemma diskTo_comp {R : Type v} [CommRing R] (n : ℕ)
    {K L : ChainComplex (ModuleCat.{v} R) ℕ}
    (φ : ModuleCat.of R R ⟶ K.X (n + 1)) (f : K ⟶ L) :
    diskTo n K φ ≫ f = diskTo n L (φ ≫ f.f (n + 1)) := by
  apply disk_hom_ext n
  apply (cancel_epi (diskTopIso R n).inv).mp
  simp [HomologicalComplex.comp_f, ← Category.assoc]

/-- The lower component includes the sphere as the boundary of its disk. -/
noncomputable def sphereIntoDisk (R : Type v) [CommRing R] (n : ℕ) :
    sphere R n ⟶ disk R n :=
  HomologicalComplex.mkHomFromSingle
    (eqToHom (show ModuleCat.of R R = (disk R n).X n by simp [diskX]))
    (by
      intro k hk
      have hk' : k ≠ n := by simp only [ComplexShape.down_Rel] at hk; omega
      change _ ≫ ChainComplex.of.d (diskX R n) (diskD R n) n k = 0
      simp only [ChainComplex.of.d]
      split_ifs with h
      · simp [diskD, hk']
      · simp)

/-- The element represented by the top component of a disk map. -/
noncomputable def diskValue {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f : disk R n ⟶ K) : K.X (n + 1) :=
  ((diskTopIso R n).inv ≫ f.f (n + 1)) (1 : R)

@[simp]
lemma diskValue_to {R : Type v} [CommRing R] (n : ℕ)
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (x : K.X (n + 1)) :
    diskValue n (diskTo n K (elementMap x)) = x := by
  unfold diskValue
  rw [diskTo_top]
  exact elementMap_one x

@[simp]
lemma diskValue_comp {R : Type v} [CommRing R] (n : ℕ)
    {K L : ChainComplex (ModuleCat.{v} R) ℕ} (f : disk R n ⟶ K) (g : K ⟶ L) :
    diskValue n (f ≫ g) = g.f (n + 1) (diskValue n f) := by
  simp [diskValue, HomologicalComplex.comp_f, ← Category.assoc]

lemma disk_hom_ext_value {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f g : disk R n ⟶ K)
    (h : diskValue n f = diskValue n g) : f = g := by
  apply disk_hom_ext n
  apply (cancel_epi (diskTopIso R n).inv).mp
  exact rankOne_hom_ext _ _ h

lemma sphereIntoDisk_boundary (R : Type v) [CommRing R] (n : ℕ) :
    (sphereIso R n).inv ≫ (sphereIntoDisk R n).f n =
      (diskTopIso R n).inv ≫ (disk R n).d (n + 1) n := by
  simp [sphereIso, sphereIntoDisk, diskTopIso, diskD, ← Category.assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Restricting a disk map to its boundary gives the differential of its top element. -/
@[simp]
lemma sphereIntoDisk_value {R : Type v} [CommRing R] (n : ℕ)
    {K : ChainComplex (ModuleCat.{v} R) ℕ} (f : disk R n ⟶ K) :
    sphereValue n (sphereIntoDisk R n ≫ f) = K.d (n + 1) n (diskValue n f) := by
  unfold sphereValue diskValue
  simp only [HomologicalComplex.comp_f, ← Category.assoc]
  rw [sphereIntoDisk_boundary, Category.assoc, ← f.comm]
  rfl

/-- The generating cofibrations include the degree-zero generator as well as
the inclusions of sphere boundaries into positive-degree disks. -/
noncomputable def generatingCofibration (R : Type v) [CommRing R] :
    (n : ℕ) → Arrow (ChainComplex (ModuleCat.{v} R) ℕ)
  | 0 => Arrow.mk (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ sphere R 0)
  | n + 1 => Arrow.mk (sphereIntoDisk R n)

/-- The generating cofibrations for the connective projective structure. -/
def generatingCofibrations (R : Type v) [CommRing R] :
    MorphismProperty (ChainComplex (ModuleCat.{v} R) ℕ) :=
  MorphismProperty.ofHoms (fun n : ℕ => (generatingCofibration R n).hom)

instance generatingCofibrations_isSmall (R : Type v) [CommRing R] :
    (generatingCofibrations R).IsSmall.{v} := by
  unfold generatingCofibrations
  exact MorphismProperty.isSmall_ofHoms _

/-- Sphere-boundary lifting supplies a preimage with a prescribed differential. -/
lemma cofibration_rlp_boundaryLift {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y)
    (hp : (generatingCofibrations R).rlp p) (n : ℕ)
    (x : X.X n) (y : Y.X (n + 1)) (hx : X.d n (n - 1) x = 0)
    (hxy : p.f n x = Y.d (n + 1) n y) :
    ∃ z : X.X (n + 1), X.d (n + 1) n z = x ∧ p.f (n + 1) z = y := by
  have hi := hp (generatingCofibration R (n + 1)).hom ⟨n + 1⟩
  change HasLiftingProperty (sphereIntoDisk R n) p at hi
  letI := hi
  let u := sphereElement n X x hx
  let v := diskTo n Y (elementMap y)
  have hw : u ≫ p = sphereIntoDisk R n ≫ v := by
    apply sphere_hom_ext_value n
    dsimp only [u, v]
    rw [sphereValue_comp, sphereElement_value, sphereIntoDisk_value, diskValue_to]
    exact hxy
  let sq : CommSq u (sphereIntoDisk R n) p v := ⟨hw⟩
  refine ⟨diskValue n sq.lift, ?_, ?_⟩
  · have h := congrArg (sphereValue n) sq.fac_left
    simpa only [sphereIntoDisk_value, u, sphereElement_value] using h
  · have h := congrArg (diskValue n) sq.fac_right
    simpa only [diskValue_comp, v, diskValue_to] using h

/-- The degree-zero generator supplies surjectivity in degree zero. -/
lemma cofibration_rlp_zero_surjective {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y)
    (hp : (generatingCofibrations R).rlp p) : Function.Surjective (p.f 0) := by
  have hi := hp (generatingCofibration R 0).hom ⟨0⟩
  change HasLiftingProperty (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ sphere R 0) p at hi
  letI := hi
  intro y
  have hy : Y.d 0 (0 - 1) y = 0 := by simp
  let v := sphereElement 0 Y y hy
  let sq : CommSq (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ X)
      (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ sphere R 0) p v := ⟨by simp⟩
  refine ⟨sphereValue 0 sq.lift, ?_⟩
  have h := congrArg (sphereValue 0) sq.fac_right
  simpa only [sphereValue_comp, v, sphereElement_value] using h

/-- Lifting against the cofibration generators is surjective on cycles in every degree. -/
lemma cofibration_rlp_cycleLift {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y)
    (hp : (generatingCofibrations R).rlp p) (n : ℕ) (y : Y.X n)
    (hy : Y.d n (n - 1) y = 0) :
    ∃ x : X.X n, X.d n (n - 1) x = 0 ∧ p.f n x = y := by
  cases n with
  | zero =>
    obtain ⟨x, hx⟩ := cofibration_rlp_zero_surjective p hp y
    exact ⟨x, by simp, hx⟩
  | succ n =>
    have hn : n + 1 - 1 = n := by omega
    change Y.d (n + 1) (n + 1 - 1) y = 0 at hy
    change ∃ x : X.X (n + 1), X.d (n + 1) (n + 1 - 1) x = 0 ∧ p.f (n + 1) x = y
    rw [hn] at hy ⊢
    have h := cofibration_rlp_boundaryLift p hp n 0 y (by simp)
      (by simpa only [map_zero] using hy.symm)
    exact h

/-- In particular, lifting against the cofibration generators is degreewise surjective. -/
lemma cofibration_rlp_epi {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y)
    (hp : (generatingCofibrations R).rlp p) (n : ℕ) : Epi (p.f n) := by
  rw [ModuleCat.epi_iff_surjective]
  cases n with
  | zero => exact cofibration_rlp_zero_surjective p hp
  | succ n =>
    intro y
    obtain ⟨x, hx, hpx⟩ := cofibration_rlp_cycleLift p hp n (Y.d (n + 1) n y)
      (differential_apply_differential Y _ _ _ y)
    obtain ⟨z, _, hz⟩ := cofibration_rlp_boundaryLift p hp n x y hx hpx
    exact ⟨z, hz⟩

lemma next_nat_eq_sub_one (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  cases n <;> simp

/-- A concrete cycle as an element of the abstract cycles object. -/
noncomputable def cycleMk {R : Type v} [CommRing R]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : K.X n)
    (hx : K.d n (n - 1) x = 0) : K.cycles n :=
  K.cyclesMk x (n - 1) (next_nat_eq_sub_one n) hx

@[simp]
lemma iCycles_cycleMk {R : Type v} [CommRing R]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : K.X n)
    (hx : K.d n (n - 1) x = 0) : K.iCycles n (cycleMk K n x hx) = x := by
  exact K.i_cyclesMk x (n - 1) (next_nat_eq_sub_one n) hx

/-- The homology class represented by a concrete cycle. -/
noncomputable def cycleClass {R : Type v} [CommRing R]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : K.X n)
    (hx : K.d n (n - 1) x = 0) : K.homology n :=
  K.homologyπ n (cycleMk K n x hx)

lemma cycleClass_boundary_iff {R : Type v} [CommRing R]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : K.X n)
    (hx : K.d n (n - 1) x = 0) :
    cycleClass K n x hx = 0 ↔ ∃ y : K.X (n + 1), K.d (n + 1) n y = x := by
  have hi : Function.Injective (K.homologyι n) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have h : K.homologyι n (cycleClass K n x hx) = K.pOpcycles n x := by
    have h := congrArg (fun f : K.cycles n ⟶ K.opcycles n => f (cycleMk K n x hx))
      (K.homology_π_ι n)
    simpa only [ModuleCat.comp_apply, cycleClass, iCycles_cycleMk] using h
  rw [← hi.eq_iff]
  simp only [h, map_zero]
  change (K.sc n).pOpcycles x = 0 ↔ _
  erw [(K.sc n).moduleCat_pOpcycles_eq_zero_iff]
  change (∃ y : K.X ((ComplexShape.down ℕ).prev n),
    K.d ((ComplexShape.down ℕ).prev n) n y = x) ↔ _
  rw [ChainComplex.prev]

lemma cycleClass_exists {R : Type v} [CommRing R]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (a : K.homology n) :
    ∃ (x : K.X n) (hx : K.d n (n - 1) x = 0), cycleClass K n x hx = a := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance a
  let x := K.iCycles n z
  have hx : K.d n (n - 1) x = 0 := by
    have h := congrArg (fun f : K.cycles n ⟶ K.X (n - 1) => f z)
      (K.iCycles_d n (n - 1))
    exact h
  refine ⟨x, hx, ?_⟩
  have he : cycleMk K n x hx = z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    exact iCycles_cycleMk K n x hx
  simpa only [cycleClass, he] using hz

lemma map_cycle {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y) (n : ℕ)
    (x : X.X n) (hx : X.d n (n - 1) x = 0) :
    Y.d n (n - 1) (p.f n x) = 0 := by
  have h := congrArg (fun f : X.X n ⟶ Y.X (n - 1) => f x) (p.comm n (n - 1))
  change Y.d n (n - 1) (p.f n x) = p.f (n - 1) (X.d n (n - 1) x) at h
  rw [h, hx, map_zero]

lemma cycleMk_naturality {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y) (n : ℕ)
    (x : X.X n) (hx : X.d n (n - 1) x = 0) :
    HomologicalComplex.cyclesMap p n (cycleMk X n x hx) =
      cycleMk Y n (p.f n x) (map_cycle p n x hx) := by
  apply (ModuleCat.mono_iff_injective (Y.iCycles n)).mp inferInstance
  have h := congrArg (fun f : X.cycles n ⟶ Y.X n => f (cycleMk X n x hx))
    (HomologicalComplex.cyclesMap_i p n)
  simpa only [ModuleCat.comp_apply, iCycles_cycleMk] using h

lemma cycleClass_naturality {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y) (n : ℕ)
    (x : X.X n) (hx : X.d n (n - 1) x = 0) :
    HomologicalComplex.homologyMap p n (cycleClass X n x hx) =
      cycleClass Y n (p.f n x) (map_cycle p n x hx) := by
  have h := congrArg (fun f : X.cycles n ⟶ Y.homology n => f (cycleMk X n x hx))
    (HomologicalComplex.homologyπ_naturality p n)
  simpa only [ModuleCat.comp_apply, cycleClass, cycleMk_naturality] using h

/-- The boundary-lifting property detects injectivity and surjectivity on homology. -/
lemma cofibration_rlp_quasiIso {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y)
    (hp : (generatingCofibrations R).rlp p) : HomologicalComplex.quasiIso _ _ p := by
  rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have he : Epi (HomologicalComplex.homologyMap p n) := by
    rw [ModuleCat.epi_iff_surjective]
    intro a
    obtain ⟨y, hy, ha⟩ := cycleClass_exists Y n a
    obtain ⟨x, hx, hpx⟩ := cofibration_rlp_cycleLift p hp n y hy
    refine ⟨cycleClass X n x hx, ?_⟩
    rw [cycleClass_naturality]
    subst y
    exact ha
  have hm : Mono (HomologicalComplex.homologyMap p n) := by
    rw [ModuleCat.mono_iff_injective]
    apply (injective_iff_map_eq_zero (HomologicalComplex.homologyMap p n).hom).mpr
    intro a ha
    obtain ⟨x, hx, hxa⟩ := cycleClass_exists X n a
    rw [← hxa, cycleClass_naturality] at ha
    obtain ⟨y, hy⟩ := (cycleClass_boundary_iff Y n _ _).mp ha
    obtain ⟨z, hz, _⟩ := cofibration_rlp_boundaryLift p hp n x y hx hy.symm
    rw [← hxa]
    exact (cycleClass_boundary_iff X n x hx).mpr ⟨z, hz⟩
  exact isIso_of_mono_of_epi _

@[simp]
lemma homologyι_cycleClass {R : Type v} [CommRing R]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : K.X n)
    (hx : K.d n (n - 1) x = 0) :
    K.homologyι n (cycleClass K n x hx) = K.pOpcycles n x := by
  have h := congrArg (fun f : K.cycles n ⟶ K.opcycles n => f (cycleMk K n x hx))
    (K.homology_π_ι n)
  simpa only [ModuleCat.comp_apply, cycleClass, iCycles_cycleMk] using h

lemma cycleClass_sub {R : Type v} [CommRing R]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x y : K.X n)
    (hx : K.d n (n - 1) x = 0) (hy : K.d n (n - 1) y = 0)
    (hxy : K.d n (n - 1) (x - y) = 0) :
    cycleClass K n (x - y) hxy = cycleClass K n x hx - cycleClass K n y hy := by
  apply (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  simp only [map_sub, homologyι_cycleClass]

/-- A positive-degree surjective quasi-isomorphism lifts cycles strictly, rather
than merely lifting their homology classes. -/
lemma surjective_quasiIso_cycleLift {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y) [QuasiIso p]
    (hp : positiveDegreeSurjections R p) (n : ℕ) (y : Y.X n)
    (hy : Y.d n (n - 1) y = 0) :
    ∃ x : X.X n, X.d n (n - 1) x = 0 ∧ p.f n x = y := by
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap p n)).mp
    inferInstance (cycleClass Y n y hy)
  obtain ⟨x, hx, hxa⟩ := cycleClass_exists X n a
  have hpc := map_cycle p n x hx
  have hdiff : Y.d n (n - 1) (p.f n x - y) = 0 := by
    rw [map_sub, hpc, hy, sub_self]
  have hclass : cycleClass Y n (p.f n x - y) hdiff = 0 := by
    rw [cycleClass_sub Y n _ _ hpc hy hdiff, ← cycleClass_naturality p n x hx, hxa, ha, sub_self]
  obtain ⟨z, hz⟩ := (cycleClass_boundary_iff Y n _ _).mp hclass
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective (p.f (n + 1))).mp
    (hp (n + 1) (by omega)) z
  refine ⟨x - X.d (n + 1) n w, ?_, ?_⟩
  · rw [map_sub, hx, differential_apply_differential, sub_self]
  · have h := congrArg (fun f : X.X (n + 1) ⟶ Y.X n => f w) (p.comm (n + 1) n)
    change Y.d (n + 1) n (p.f (n + 1) w) = p.f n (X.d (n + 1) n w) at h
    rw [map_sub, ← h, hw, hz]
    abel

/-- A positive-degree surjective quasi-isomorphism lifts a prescribed boundary. -/
lemma surjective_quasiIso_boundaryLift {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y) [QuasiIso p]
    (hp : positiveDegreeSurjections R p) (n : ℕ)
    (x : X.X n) (y : Y.X (n + 1)) (hx : X.d n (n - 1) x = 0)
    (hxy : p.f n x = Y.d (n + 1) n y) :
    ∃ z : X.X (n + 1), X.d (n + 1) n z = x ∧ p.f (n + 1) z = y := by
  have hclass : cycleClass X n x hx = 0 := by
    apply (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap p n)).mp inferInstance
    rw [map_zero, cycleClass_naturality]
    exact (cycleClass_boundary_iff Y n _ _).mpr ⟨y, hxy.symm⟩
  obtain ⟨z, hz⟩ := (cycleClass_boundary_iff X n _ _).mp hclass
  have hdiff : Y.d (n + 1) (n + 1 - 1) (p.f (n + 1) z - y) = 0 := by
    have hn : n + 1 - 1 = n := by omega
    rw [hn, map_sub]
    have h := congrArg (fun f : X.X (n + 1) ⟶ Y.X n => f z) (p.comm (n + 1) n)
    change Y.d (n + 1) n (p.f (n + 1) z) = p.f n (X.d (n + 1) n z) at h
    rw [h, hz, hxy, sub_self]
  obtain ⟨w, hw, hpw⟩ := surjective_quasiIso_cycleLift p hp (n + 1) _ hdiff
  have hn : n + 1 - 1 = n := by omega
  rw [hn] at hw
  refine ⟨z - w, ?_, ?_⟩
  · rw [map_sub, hz, hw, sub_zero]
  · rw [map_sub, hpw]
    abel

/-- The elementary cycle and boundary lifts solve every generating square. -/
lemma surjective_quasiIso_rlp {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y) [QuasiIso p]
    (hp : positiveDegreeSurjections R p) : (generatingCofibrations R).rlp p := by
  intro A B i hi
  cases hi with
  | mk n =>
    cases n with
    | zero =>
      change HasLiftingProperty (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ sphere R 0) p
      refine ⟨fun {u v} sq => ?_⟩
      obtain ⟨x, hx, hpx⟩ := surjective_quasiIso_cycleLift p hp 0
        (sphereValue 0 v) (sphereValue_cycle 0 v)
      refine ⟨⟨sphereElement 0 X x hx, ?_, ?_⟩⟩
      · exact (isZero_zero _).eq_of_src _ _
      · apply sphere_hom_ext_value 0
        rw [sphereValue_comp, sphereElement_value]
        exact hpx
    | succ n =>
      change HasLiftingProperty (sphereIntoDisk R n) p
      refine ⟨fun {u v} sq => ?_⟩
      have hxy : p.f n (sphereValue n u) = Y.d (n + 1) n (diskValue n v) := by
        have h := congrArg (sphereValue n) sq.w
        rw [sphereValue_comp, sphereIntoDisk_value] at h
        exact h
      obtain ⟨z, hz, hpz⟩ := surjective_quasiIso_boundaryLift p hp n
        (sphereValue n u) (diskValue n v) (sphereValue_cycle n u) hxy
      refine ⟨⟨diskTo n X (elementMap z), ?_, ?_⟩⟩
      · apply sphere_hom_ext_value n
        rw [sphereIntoDisk_value, diskValue_to]
        exact hz
      · apply disk_hom_ext_value n
        rw [diskValue_comp, diskValue_to]
        exact hpz

/-- The right lifting class of the cofibration generators consists precisely of
positive-degree surjective quasi-isomorphisms. -/
lemma generatingCofibrations_rlp (R : Type v) [CommRing R] :
    (generatingCofibrations R).rlp =
      positiveDegreeSurjections R ⊓ HomologicalComplex.quasiIso _ _ := by
  ext X Y p
  constructor
  · intro hp
    exact ⟨fun n _ => cofibration_rlp_epi p hp n, cofibration_rlp_quasiIso p hp⟩
  · rintro ⟨hp, hw⟩
    letI : QuasiIso p := hw
    exact surjective_quasiIso_rlp p hp

/-- The disk generator tests precisely surjectivity in its top degree. -/
lemma disk_lifting_iff_epi {R : Type v} [CommRing R] (n : ℕ)
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (p : X ⟶ Y) :
    HasLiftingProperty (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ disk R n) p ↔
      Epi (p.f (n + 1)) := by
  constructor
  · intro hp
    letI := hp
    rw [ModuleCat.epi_iff_surjective]
    intro y
    let φ : ModuleCat.of R R ⟶ Y.X (n + 1) :=
      ModuleCat.ofHom (LinearMap.toSpanSingleton R (Y.X (n + 1)) y)
    let v := diskTo n Y φ
    let sq : CommSq (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ X)
        (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ disk R n) p v :=
      ⟨by simp⟩
    have hfac := congrArg
      (fun f : disk R n ⟶ Y => (diskTopIso R n).inv ≫ f.f (n + 1)) sq.fac_right
    have hfac' : ((diskTopIso R n).inv ≫ sq.lift.f (n + 1)) ≫ p.f (n + 1) = φ := by
      simpa only [HomologicalComplex.comp_f, ← Category.assoc, v, diskTo_top] using hfac
    refine ⟨((diskTopIso R n).inv ≫ sq.lift.f (n + 1)) (1 : R), ?_⟩
    have h := congrArg (fun f : ModuleCat.of R R ⟶ Y.X (n + 1) => f (1 : R)) hfac'
    simpa [φ, ModuleCat.comp_apply] using h
  · intro hp
    letI := hp
    refine ⟨fun {u v} sq => ?_⟩
    let φ := Projective.factorThru ((diskTopIso R n).inv ≫ v.f (n + 1)) (p.f (n + 1))
    refine ⟨⟨diskTo n X φ, ?_, ?_⟩⟩
    · exact (isZero_zero _).eq_of_src _ _
    · rw [diskTo_comp]
      dsimp only [φ]
      rw [Projective.factorThru_comp, diskTo_eta]

/-- The generating trivial cofibrations for the connective projective structure. -/
def generatingTrivialCofibrations (R : Type v) [CommRing R] :
    MorphismProperty (ChainComplex (ModuleCat.{v} R) ℕ) :=
  MorphismProperty.ofHoms
    (fun n : ℕ => (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ disk R n))

/-- Lifting against the disk generators characterizes the fibrations in Example 2.5.9. -/
lemma generatingTrivialCofibrations_rlp (R : Type v) [CommRing R] :
    (generatingTrivialCofibrations R).rlp = positiveDegreeSurjections R := by
  ext X Y p
  constructor
  · intro hp n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact (disk_lifting_iff_epi m p).mp (hp _ ⟨m⟩)
  · intro hp A B i hi
    cases hi with
    | mk n => exact (disk_lifting_iff_epi n p).mpr (hp (n + 1) (by omega))

instance generatingTrivialCofibrations_isSmall (R : Type v) [CommRing R] :
    (generatingTrivialCofibrations R).IsSmall.{v} := by
  unfold generatingTrivialCofibrations
  exact MorphismProperty.isSmall_ofHoms _

set_option backward.isDefEq.respectTransparency false in
/-- The maps out of a zero object preserve connected colimits. This supplies the
smallness condition for the disk generators, all of whose sources are zero. -/
lemma zero_coyoneda_preservesColimit {J : Type v} [SmallCategory J] [IsConnected J]
    (R : Type v) [CommRing R] (K : J ⥤ ChainComplex (ModuleCat.{v} R) ℕ) :
    PreservesColimit K
      (coyoneda.obj (Opposite.op (0 : ChainComplex (ModuleCat.{v} R) ℕ))) := by
  classical
  let j₀ : J := Classical.ofNonempty
  refine ⟨fun {c} hc => ⟨?_⟩⟩
  refine
    { desc := fun s => ↾fun _ =>
        s.ι.app j₀ (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ K.obj j₀)
      fac := ?_
      uniq := ?_ }
  · intro s j
    ext a
    change (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ K.obj j at a
    have ha : a = 0 := (isZero_zero _).eq_of_src _ _
    subst a
    change s.ι.app j₀ (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ K.obj j₀) =
      s.ι.app j (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ K.obj j)
    apply constant_of_preserves_morphisms
      (fun k : J => s.ι.app k (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ K.obj k))
      ?_ j₀ j
    intro k l f
    have h := congrArg (fun m : _ ⟶ s.pt =>
      m (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ K.obj k)) (s.ι.naturality f)
    simpa using h.symm
  · intro s m h
    ext a
    change (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ c.pt at a
    have ha : a = 0 := (isZero_zero _).eq_of_src _ _
    subst a
    have h₀ := congrArg (fun m : _ ⟶ s.pt =>
      m (0 : (0 : ChainComplex (ModuleCat.{v} R) ℕ) ⟶ K.obj j₀)) (h j₀)
    simpa using h₀

/-- The disk generators permit the small object argument, with the first infinite
cardinal, because their zero domains preserve the relevant connected colimits. -/
instance generatingTrivialCofibrations_hasSmallObjectArgument (R : Type v) [CommRing R] :
    (generatingTrivialCofibrations R).HasSmallObjectArgument.{v} := by
  let κ := Cardinal.aleph0.{v}
  have : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  have : OrderBot κ.ord.ToType := Cardinal.orderBotAleph0OrdToType
  refine ⟨κ, inferInstance, inferInstance, { preservesColimit := ?_ }⟩
  intro A B X Y i hi f hf
  cases hi with
  | mk n => exact zero_coyoneda_preservesColimit R hf.F

/-- Both the zero source and the rank-one sphere sources are finitely presentable,
so the cofibration generators permit the small object argument. -/
instance generatingCofibrations_hasSmallObjectArgument (R : Type v) [CommRing R] :
    (generatingCofibrations R).HasSmallObjectArgument.{v} := by
  let κ := Cardinal.aleph0.{v}
  have : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  have : OrderBot κ.ord.ToType := Cardinal.orderBotAleph0OrdToType
  refine ⟨κ, inferInstance, inferInstance, { preservesColimit := ?_ }⟩
  intro A B X Y i hi f hf
  cases hi with
  | mk n =>
    cases n with
    | zero => exact zero_coyoneda_preservesColimit R hf.F
    | succ n =>
      change PreservesColimit hf.F (coyoneda.obj (Opposite.op (sphere R n)))
      have : PreservesFilteredColimitsOfSize.{v, v}
          (coyoneda.obj (Opposite.op (sphere R n))) :=
        Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.mp inferInstance
      infer_instance

/-- Degreewise modules of a contractible cover, with no extra summand in degree zero. -/
noncomputable abbrev coverX {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) : ℕ → ModuleCat.{v} R
  | 0 => Y.X 1
  | n + 1 => ModuleCat.of R (Y.X (n + 2) × Y.X (n + 1))

/-- The differential of the contractible cover sends `(a,b)` to `(b,0)`. -/
noncomputable def coverD {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) : (n : ℕ) → coverX Y (n + 1) ⟶ coverX Y n
  | 0 => ModuleCat.ofHom (LinearMap.snd R _ _)
  | n + 1 => ModuleCat.ofHom ((LinearMap.snd R _ _).prod 0)

lemma coverD_sq {R : Type v} [CommRing R] (Y : ChainComplex (ModuleCat.{v} R) ℕ)
    (n : ℕ) : coverD Y (n + 1) ≫ coverD Y n = 0 := by
  cases n <;> ext x <;> rfl

/-- A contractible complex mapping surjectively onto `Y` in every positive degree. -/
noncomputable abbrev cover {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (coverX Y) (coverD Y) (coverD_sq Y)

/-- The augmentation of the cover sends `(a,b)` to `d a + b`. -/
noncomputable def coverMapF {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) : (n : ℕ) → (cover Y).X n ⟶ Y.X n
  | 0 => Y.d 1 0
  | n + 1 => ModuleCat.ofHom
      ((Y.d (n + 2) (n + 1)).hom.comp (LinearMap.fst R _ _) + LinearMap.snd R _ _)

lemma coverMapF_comm {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    coverMapF Y (n + 1) ≫ Y.d (n + 1) n =
      (cover Y).d (n + 1) n ≫ coverMapF Y n := by
  cases n <;> ext x <;>
    simp [coverMapF, coverD, ChainComplex.of.d, ModuleCat.comp_apply,
      differential_apply_differential]

/-- The augmentation is a positive-degree surjection. -/
noncomputable def coverMap {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) : cover Y ⟶ Y :=
  ChainComplex.ofHom (coverMapF Y) (coverMapF_comm Y)

lemma coverMap_surjective {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) : positiveDegreeSurjections R (coverMap Y) := by
  intro n hn
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [ModuleCat.epi_iff_surjective]
  intro y
  refine ⟨(0, y), ?_⟩
  simp [coverMap, coverMapF]

/-- The degree-raising contraction of the cover. -/
noncomputable def coverS {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) : (n : ℕ) → (cover Y).X n ⟶ (cover Y).X (n + 1)
  | 0 => ModuleCat.ofHom ((0 : Y.X 1 →ₗ[R] Y.X 2).prod LinearMap.id)
  | n + 1 => ModuleCat.ofHom
      ((0 : (Y.X (n + 2) × Y.X (n + 1)) →ₗ[R] Y.X (n + 3)).prod (LinearMap.fst R _ _))

/-- All components of the cover's contraction, including the zero off-diagonal ones. -/
noncomputable def coverHom {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) (i j : ℕ) : (cover Y).X i ⟶ (cover Y).X j :=
  if h : j = i + 1 then coverS Y i ≫ eqToHom (congrArg (coverX Y) h.symm) else 0

/-- The augmentation source is contractible. -/
noncomputable def coverContraction {R : Type v} [CommRing R]
    (Y : ChainComplex (ModuleCat.{v} R) ℕ) : Homotopy (𝟙 (cover Y)) 0 where
  hom := coverHom Y
  zero i j hij := by
    have h : j ≠ i + 1 := by simpa only [ComplexShape.down_Rel, ne_eq, eq_comm] using hij
    simp [coverHom, h]
  comm i := by
    change (𝟙 _) = dNext i (coverHom Y) + prevD i (coverHom Y) + 0
    rw [dNext_nat]
    cases i with
    | zero =>
      simp [dNext_nat, prevD, toPrev, HomologicalComplex.dTo,
        coverHom, coverS, coverD, ChainComplex.of.d]
      ext x
      rfl
    | succ i =>
      cases i <;>
        simp [prevD, toPrev, HomologicalComplex.dTo,
          coverHom, coverS, coverD, ChainComplex.of.d] <;> ext x <;> simp [ModuleCat.comp_apply]

/-- Adding the contractible cover does not change homotopy type. -/
noncomputable def coverInlEquiv {R : Type v} [CommRing R]
    (X Y : ChainComplex (ModuleCat.{v} R) ℕ) : HomotopyEquiv X (X ⊞ cover Y) where
  hom := biprod.inl
  inv := biprod.fst
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := by
    have hp : Homotopy
        ((biprod.snd : X ⊞ cover Y ⟶ cover Y) ≫
          (biprod.inr : cover Y ⟶ X ⊞ cover Y)) 0 := by
      simpa using ((coverContraction Y).compLeft
        (biprod.snd : X ⊞ cover Y ⟶ cover Y)).compRight
        (biprod.inr : cover Y ⟶ X ⊞ cover Y)
    have h := (Homotopy.refl
      ((biprod.fst : X ⊞ cover Y ⟶ X) ≫ (biprod.inl : X ⟶ X ⊞ cover Y))).add hp
    simpa only [biprod.total, add_zero] using h.symm

/-- Factorization through the cover has a positive-degree surjective right map. -/
lemma coverFactor_surjective {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (f : X ⟶ Y) :
    positiveDegreeSurjections R (biprod.desc f (coverMap Y)) := by
  intro n hn
  haveI := coverMap_surjective Y n hn
  have h : (biprod.inr : cover Y ⟶ X ⊞ cover Y).f n ≫
      (biprod.desc f (coverMap Y)).f n = (coverMap Y).f n := by
    simpa only [HomologicalComplex.comp_f] using congrArg
      (fun g : cover Y ⟶ Y => g.f n) (biprod.inr_desc f (coverMap Y))
  exact epi_of_epi_fac h

/-- A map lifting against all positive-degree surjections is a retract of a
homotopy equivalence, hence a quasi-isomorphism. -/
lemma disk_leftClass_quasiIso {R : Type v} [CommRing R]
    {X Y : ChainComplex (ModuleCat.{v} R) ℕ} (f : X ⟶ Y)
    (hf : (generatingTrivialCofibrations R).rlp.llp f) :
    HomologicalComplex.quasiIso _ _ f := by
  let p := biprod.desc f (coverMap Y)
  have hp : (generatingTrivialCofibrations R).rlp p := by
    rw [generatingTrivialCofibrations_rlp]
    exact coverFactor_surjective f
  haveI := hf p hp
  let sq : CommSq (biprod.inl : X ⟶ X ⊞ cover Y) f p (𝟙 Y) := ⟨by simp [p]⟩
  let hret : RetractArrow f (biprod.inl : X ⟶ X ⊞ cover Y) :=
    { i := Arrow.homMk (𝟙 X) sq.lift (by simpa using sq.fac_left.symm)
      r := Arrow.homMk (𝟙 X) p (by simp [p])
      retract := by ext <;> simp [sq.fac_right] }
  have hi : HomologicalComplex.quasiIso _ _ (biprod.inl : X ⟶ X ⊞ cover Y) := by
    have h := (coverInlEquiv X Y).quasiIso_hom
    exact h
  exact (inferInstance : (HomologicalComplex.quasiIso _ _).IsStableUnderRetracts).of_retract hret hi

end ProjectiveGenerators

end ScoccolaPhd
