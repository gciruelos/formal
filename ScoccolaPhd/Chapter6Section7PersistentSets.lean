import Mathlib
import ScoccolaPhd.Chapter6Section5ClusteringDiagrams

/-!
# §§6.7–6.9: persistent sets, finite filtered simplicial complexes and diagrams

This module follows Sections 6.7–6.9 of Scoccola’s thesis.
-/

universe u v

namespace ScoccolaPhd

/-! ## Chapter 6.7: The interleaving distance on persistent sets

`Set^ℝ` carries the locally persistent structure of persistent objects.  The full subcategory
of right continuous, q-tame persistent sets is `RTSet`; its locally persistent structure is
stated to exist.  Ultra metric spaces and their single-linkage persistent sets (Section 6.7.2)
are defined concretely.

Omitted: Proposition 6.7.4 (weighted sequential limits "of morphisms that are part of an
interleaving"), Definition 6.7.8 (dendrograms) and the embedding of dendrograms.

The total-boundedness and q-tameness assertion of Theorem 6.7.11 is proved by finite
ball covers. The categorical correspondence and remaining structure results are open. -/

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

/-- The finite-stage criterion in the proof of Theorem 6.7.11: surjective structure maps
identify q-tameness with finiteness at every positive parameter. -/
theorem qtame_iff_finite_positive (F : ℝ≥0 ⥤ Type u) (hF : IsFlabby F) :
    IsQTameSet F ↔ ∀ r : ℝ≥0, 0 < r → Finite (F.obj r) := by
  constructor
  · intro h r hr
    have hf := h 0 r hr
    rw [Set.range_eq_univ.mpr (hF 0 r (show 0 ≤ r from bot_le))] at hf
    exact Set.finite_univ_iff.mp hf
  · intro h r s hrs
    letI := h s ((show 0 ≤ r from bot_le).trans_lt hrs)
    exact Set.toFinite _

/-- Surjectivity of single-linkage structure maps, used in Theorem 6.7.11. -/
theorem UltraMet.singleLinkage_flabby (X : UltraMet.{u}) : IsFlabby X.singleLinkage := by
  intro r s h q
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨Quotient.mk _ x, rfl⟩

/-- The finite-ball-cover argument of Theorem 6.7.11, independent of the categorical
correspondence of Theorem 6.7.10. -/
theorem UltraMet.totallyBounded_iff_finite_singleLinkage (X : UltraMet.{u}) :
    IsTotallyBoundedEP X.carrier ↔
      ∀ r : ℝ≥0, 0 < r → Finite (Quotient (X.slSetoid r)) := by
  classical
  constructor
  · intro h r hr
    obtain ⟨s, hs⟩ := h r (ENNReal.coe_pos.mpr hr)
    have hsurj : Function.Surjective
        (fun p : {x // x ∈ s} => Quotient.mk (X.slSetoid r) p.1) := by
      intro q
      induction q using Quotient.inductionOn with
      | _ x =>
        obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
        refine ⟨⟨p, hp⟩, Quotient.sound ?_⟩
        exact (show edist p x < (r : ℝ≥0∞) by
          simpa only [Metric.mem_eball, edist_comm] using hxp).le
    exact Finite.of_surjective _ hsurj
  · intro h ε hε
    obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    have hr' : 0 < r := ENNReal.coe_pos.mp hr
    letI := h r hr'
    let s : Finset X.carrier := (Set.finite_range
      (Quotient.out : Quotient (X.slSetoid r) → X.carrier)).toFinset
    refine ⟨s, ?_⟩
    intro x _
    refine Set.mem_iUnion₂.mpr ⟨(Quotient.mk (X.slSetoid r) x).out, ?_, ?_⟩
    · change (Quotient.mk (X.slSetoid r) x).out ∈ (Set.finite_range
          (Quotient.out : Quotient (X.slSetoid r) → X.carrier)).toFinset
      simp only [Set.Finite.mem_toFinset]
      exact ⟨Quotient.mk _ x, rfl⟩
    · have hd : edist (Quotient.mk (X.slSetoid r) x).out x ≤ (r : ℝ≥0∞) :=
        @Quotient.exact X.carrier (X.slSetoid r) _ _
          (Quotient.out_eq (Quotient.mk (X.slSetoid r) x))
      exact lt_of_le_of_lt (by simpa only [edist_comm] using hd) hrε

/-- The first assertion of Theorem 6.7.11 for the canonical single-linkage functor. -/
theorem UltraMet.totallyBounded_iff_qtame_singleLinkage (X : UltraMet.{u}) :
    IsTotallyBoundedEP X.carrier ↔ IsQTameSet X.singleLinkage :=
  X.totallyBounded_iff_finite_singleLinkage.trans
    (qtame_iff_finite_positive X.singleLinkage X.singleLinkage_flabby).symm

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

/-- **Theorem 6.7.11 (total boundedness).** The single-linkage persistent set is q-tame
exactly when its ultrametric space is totally bounded. This is the source’s finite-cover proof. -/
theorem singleLinkage_totallyBounded (SL : UltraMet.{u} ⥤ (ℝ≥0 ⥤ Type u))
    (hSL : ∀ X r, (SL.obj X).obj r = Quotient (X.slSetoid r))
    (hSLmap : ∀ (X : UltraMet.{u}) (r s : ℝ≥0) (h : r ≤ s) (x : X.carrier),
      (SL.obj X).map (homOfLE h) (cast (hSL X r).symm (Quotient.mk (X.slSetoid r) x)) =
        cast (hSL X s).symm (Quotient.mk (X.slSetoid s) x))
    (X : UltraMet.{u}) :
    IsTotallyBoundedEP X.carrier ↔ IsQTameSet (SL.obj X) := by
  have hflabby : IsFlabby (SL.obj X) := by
    intro r s h q
    obtain ⟨x, hx⟩ := Quotient.mk_surjective (cast (hSL X s) q)
    refine ⟨cast (hSL X r).symm (Quotient.mk (X.slSetoid r) x), ?_⟩
    rw [hSLmap]
    rw [hx]
    exact (Equiv.cast (hSL X s)).symm_apply_apply q
  have hfinite : (∀ r : ℝ≥0, 0 < r → Finite ((SL.obj X).obj r)) ↔
      ∀ r : ℝ≥0, 0 < r → Finite (Quotient (X.slSetoid r)) := by
    constructor <;> intro h r hr
    · exact (Equiv.cast (hSL X r)).finite_iff.mp (h r hr)
    · exact (Equiv.cast (hSL X r)).finite_iff.mpr (h r hr)
  exact X.totallyBounded_iff_finite_singleLinkage.trans
    (hfinite.symm.trans (qtame_iff_finite_positive (SL.obj X) hflabby).symm)

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
  refine ⟨singleLinkage_totallyBounded SL hSL hSLmap X, ?_⟩
  sorry

end PersistentSets

/-! ## Chapter 6.8–6.9: Mémoli's `d_F`; persistence diagrams

6.8: finite filtered simplicial complexes `ffsCpx` form a locally persistent category (given
here concretely).  Remark 6.8.9 (comparison with the homotopy interleaving distance through
geometric realization) is omitted.

6.9: persistence diagrams and the locally persistent categories `PD^p_q`.  The extended-real
distance `|x - x'|` on `[-∞, ∞]` is taken to be `0` if `x = x'`, `∞` if exactly one is infinite
(or they are opposite infinities) and the usual absolute value otherwise.

The locally persistent structure of `ffsCpx`, its powers, copowers, binary products,
pullbacks and terminal midpoints, stability of acyclic morphisms under weighted pullback,
the acyclic-cover formula and its equality with Mémoli's distance are proved. The finite
canonical-model argument also proves reflection of quotient interleavings and geodesicity. -/

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
/-- The explicit powers of Lemma 6.8.1, also used to check Lemma 6.8.4. -/
private noncomputable def ffsPowered : @PoweredByRepresentables FFSCpx _ ffsCpxLPCat := by
  letI := ffsCpxLPCat
  exact
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
open scoped Classical in
/-- The explicit copowers of Lemma 6.8.1. -/
private noncomputable def ffsCopowered : @CopoweredByRepresentables FFSCpx _ ffsCpxLPCat := by
  letI := ffsCpxLPCat
  exact
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

open scoped Classical in
/-- Lemma 6.8.1: `ffsCpx` is copowered and powered by representables (powers `F_{Y^ε} = F_Y + ε`,
copowers `F_{ε·X} = F_X - ε`).

**Note.** The hypothesis `hL` pins the locally persistent structure to
the canonical `ffsCpxLPCat` of `exists_ffsCpx_lpcat` (an arbitrary structure with the same
hom-sets could have a different composition). -/
theorem ffsCpx_powered :
    Nonempty (@PoweredByRepresentables FFSCpx _ L) ∧ Nonempty (@CopoweredByRepresentables FFSCpx _ L) := by
  subst hL
  exact ⟨⟨ffsPowered⟩, ⟨ffsCopowered⟩⟩

open scoped Classical in
/-- The product filtration used in Lemma 6.8.2. -/
private noncomputable def ffsProduct (X Y : FFSCpx) : FFSCpx :=
  { carrier := X.carrier × Y.carrier
    F := fun σ => min (X.F (σ.image Prod.fst)) (Y.F (σ.image Prod.snd))
    mono := fun _ _ h => min_le_min (X.mono _ _ (Finset.image_subset_image h))
      (Y.mono _ _ (Finset.image_subset_image h)) }

open scoped Classical in
/-- The fibre-product filtration used in Lemma 6.8.2. -/
private noncomputable def ffsPullback {X Y Z : FFSCpx} (f : X ⟶ Z) (g : Y ⟶ Z) : FFSCpx :=
  { carrier := {p : X.carrier × Y.carrier // f.1 p.1 = g.1 p.2}
    F := fun σ => min (X.F (σ.image fun p => p.1.1)) (Y.F (σ.image fun p => p.1.2))
    mono := fun _ _ h => min_le_min (X.mono _ _ (Finset.image_subset_image h))
      (Y.mono _ _ (Finset.image_subset_image h)) }

omit hL in
set_option backward.isDefEq.respectTransparency false in
/-- Binary products used in Lemma 6.8.2. -/
private theorem ffs_hasBinaryProducts : HasBinaryProducts FFSCpx := by
  classical
  have : ∀ {X Y : FFSCpx}, HasLimit (pair X Y) := by
    intro X Y
    let P := ffsProduct X Y
    let pX : P ⟶ X := ⟨Prod.fst, fun σ => by simp [P, ffsProduct]⟩
    let pY : P ⟶ Y := ⟨Prod.snd, fun σ => by simp [P, ffsProduct]⟩
    let lift : ∀ s : BinaryFan X Y, s.pt ⟶ P := fun s =>
      ⟨fun x => (s.fst.1 x, s.snd.1 x), fun σ => by
        have hx := s.fst.2 σ
        have hy := s.snd.2 σ
        dsimp only [P, ffsProduct]
        simp only [Finset.image_image, Function.comp_def, NNReal.coe_zero, add_zero]
        exact le_min (by simpa using hx) (by simpa using hy)⟩
    refine ⟨⟨BinaryFan.mk pX pY, BinaryFan.isLimitMk lift (fun _ => rfl) (fun _ => rfl) ?_⟩⟩
    intro s m hmX hmY
    apply Subtype.ext
    funext x
    exact Prod.ext (congrFun (congrArg Subtype.val hmX) x)
      (congrFun (congrArg Subtype.val hmY) x)
  exact hasBinaryProducts_of_hasLimit_pair FFSCpx

omit hL in
set_option backward.isDefEq.respectTransparency false in
/-- The concrete pullback of Lemma 6.8.2, with the acyclic projection needed in Lemma 6.8.4. -/
private theorem ffs_pullback_cone {X Y Z : FFSCpx} (f : X ⟶ Z) (g : Y ⟶ Z) :
    ∃ (P : FFSCpx) (pX : P ⟶ X) (pY : P ⟶ Y), IsPullback pX pY f g ∧
      (acyclicFFSCpx g → acyclicFFSCpx pX) := by
  classical
  let P := ffsPullback f g
  let pX : P ⟶ X := ⟨fun p => p.1.1, fun σ => by
    exact (min_le_left _ _).trans (le_of_eq (add_zero _).symm)⟩
  let pY : P ⟶ Y := ⟨fun p => p.1.2, fun σ => by
    exact (min_le_right _ _).trans (le_of_eq (add_zero _).symm)⟩
  let c : PullbackCone f g := PullbackCone.mk pX pY (by
    apply Subtype.ext
    funext p
    exact p.2)
  have hc : Limits.IsLimit c := PullbackCone.isLimitAux' c fun s => by
    let lift : s.pt ⟶ P := ⟨fun x => ⟨(s.fst.1 x, s.snd.1 x),
      congrFun (congrArg Subtype.val s.condition) x⟩, fun σ => by
        have hx := s.fst.2 σ
        have hy := s.snd.2 σ
        dsimp only [P, ffsPullback]
        simp only [Finset.image_image, Function.comp_def, NNReal.coe_zero, add_zero]
        exact le_min (by simpa using hx) (by simpa using hy)⟩
    refine ⟨lift, rfl, rfl, ?_⟩
    intro m hmX hmY
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact Prod.ext (congrFun (congrArg Subtype.val hmX) x)
      (congrFun (congrArg Subtype.val hmY) x)
  refine ⟨P, pX, pY, IsPullback.of_isLimit hc, ?_⟩
  intro hg
  constructor
  · intro x
    obtain ⟨y, hy⟩ := hg.1 (f.1 x)
    exact ⟨⟨(x, y), hy.symm⟩, rfl⟩
  · intro σ
    change min (X.F (σ.image fun p => p.1.1)) (Y.F (σ.image fun p => p.1.2)) = _
    apply min_eq_left
    have h := f.2 (σ.image fun p : P.carrier => p.1.1)
    rw [hg.2 (σ.image fun p : P.carrier => p.1.2)]
    have hi : (σ.image fun p : P.carrier => p.1.1).image f.1 =
        (σ.image fun p : P.carrier => p.1.2).image g.1 := by
      simp only [Finset.image_image, Function.comp_def]
      congr 1
      funext p
      exact p.2
    simpa only [hi, NNReal.coe_zero, add_zero] using h

omit hL in
/-- Pullbacks used in Lemma 6.8.2. -/
private theorem ffs_hasPullbacks : HasPullbacks FFSCpx := by
  have : ∀ {X Y Z : FFSCpx} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g) := by
    intro X Y Z f g
    obtain ⟨P, pX, pY, h, _⟩ := ffs_pullback_cone f g
    exact h.hasPullback
  exact hasPullbacks_of_hasLimit_cospan FFSCpx

/-- **Lemma 6.8.2 and Corollary 6.8.3.** The underlying category has binary products and pullbacks;
hence `ffsCpx` admits weighted pullbacks and terminal midpoints.

**Gap (error, Lemma 6.8.2).** The thesis uses `max` for the product and pullback filtrations.
With its morphism convention `F_X σ ≤ F_Y (f σ)`, the projections instead require `min`.
For example, for singleton complexes with constant filtrations `0` and `1`, the proposed
`max` product has no projection to the first complex. We use `min` and verify the universal
properties directly. -/
theorem ffsCpx_limits :
    HasBinaryProducts FFSCpx ∧ HasPullbacks FFSCpx ∧ @HasTerminalMidpoints FFSCpx _ L := by
  classical
  letI := L
  letI := ffs_hasBinaryProducts
  letI := ffs_hasPullbacks
  letI := (ffsCpx_powered L hL).1.some
  letI := (ffsCpx_powered L hL).2.some
  have hp : ∀ ε, PreservesLimits (PoweredByRepresentables.pow (C := FFSCpx) ε) := by
    intro ε
    have := (copowPowAdjunction (C := FFSCpx) ε).isRightAdjoint
    infer_instance
  exact ⟨inferInstance, inferInstance, hasTerminalMidpoints_of_powered
    (fun ε => by letI := hp ε; infer_instance) (fun ε => by letI := hp ε; infer_instance)⟩

omit hL in
set_option backward.isDefEq.respectTransparency false in
/-- Isomorphisms preserve the filtration exactly, used to transfer the concrete pullback
calculation of Lemma 6.8.4 to arbitrary categorical pullbacks. -/
private theorem ffs_iso_acyclic {X Y : FFSCpx} (f : X ⟶ Y) [IsIso f] :
    acyclicFFSCpx f := by
  classical
  have hleft : ∀ x, (inv f).1 (f.1 x) = x :=
    fun x => congrFun (congrArg Subtype.val (IsIso.hom_inv_id f)) x
  have hright : ∀ y, f.1 ((inv f).1 y) = y :=
    fun y => congrFun (congrArg Subtype.val (IsIso.inv_hom_id f)) y
  refine ⟨Function.RightInverse.surjective hright, fun σ => le_antisymm ?_ ?_⟩
  · simpa using f.2 σ
  · have h := (inv f).2 (σ.image f.1)
    have hi : (σ.image f.1).image (inv f).1 = σ := by
      simp only [Finset.image_image, Function.comp_def, hleft, Finset.image_id']
    simpa only [hi, NNReal.coe_zero, add_zero] using h

set_option backward.isDefEq.respectTransparency false in
/-- **Lemma 6.8.4.** Acyclic morphisms of `ffsCpx` are stable under weighted pullback. -/
theorem isStableUnderWeightedPullbacks_acyclicFFSCpx :
    @IsStableUnderWeightedPullbacks FFSCpx _ L acyclicFFSCpx := by
  subst hL
  classical
  letI := ffsCpxLPCat
  letI := ffsPowered
  letI := ffsCopowered
  letI := ffs_hasPullbacks
  letI : acyclicFFSCpx.IsMultiplicative :=
    { id_mem := fun X => ⟨Function.surjective_id, fun σ => by
        change X.F σ = X.F (σ.image id)
        simp⟩
      comp_mem := fun {X Y Z} f g hf hg => ⟨hg.1.comp hf.1, fun σ => by
        change X.F σ = Z.F (σ.image (g.1 ∘ f.1))
        rw [hf.2 σ, hg.2 (σ.image f.1), Finset.image_image]⟩ }
  letI : acyclicFFSCpx.RespectsIso :=
    MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ f hf => by
      letI : IsIso f := hf
      exact ffs_iso_acyclic f)
  letI : acyclicFFSCpx.IsStableUnderBaseChange := by
    apply MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPullback
    intro X Y Z f g _ hg
    obtain ⟨P, pX, pY, h, hpX⟩ := ffs_pullback_cone f g
    exact ⟨P, pX, pY, h, hpX hg⟩
  apply isStableUnderWeightedPullbacks_of_powered
  · intro ε
    have := (copowPowAdjunction (C := FFSCpx) ε).isRightAdjoint
    infer_instance
  · intro ε X Y f hf
    exact ⟨hf.1, fun σ => congrArg (fun r : ℝ => r + ε) (hf.2 σ)⟩

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

omit hL in
open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- The pointwise description of interleavings used in Proposition 6.8.8: the underlying
maps are inverse bijections, and the two morphism inequalities give the absolute bound. -/
private theorem ffs_interleaved_iff (X Y : FFSCpx) (δ : ℝ≥0) :
    @IsInterleaved FFSCpx _ ffsCpxLPCat X Y δ ↔
      ∃ e : X.carrier ≃ Y.carrier, ∀ σ : Finset X.carrier,
        |X.F σ - Y.F (σ.image e)| ≤ (δ : ℝ) := by
  classical
  letI := ffsCpxLPCat
  constructor
  · rintro ⟨⟨f, g, hfg, hgf⟩⟩
    have hleft : ∀ x, g.1 (f.1 x) = x := fun x => congrFun (congrArg Subtype.val hfg) x
    have hright : ∀ y, f.1 (g.1 y) = y := fun y => congrFun (congrArg Subtype.val hgf) y
    refine ⟨⟨f.1, g.1, hleft, hright⟩, fun σ => ?_⟩
    have hf := f.2 σ
    have hg := g.2 (σ.image f.1)
    have hi : (σ.image f.1).image g.1 = σ := by
      simp only [Finset.image_image, Function.comp_def, hleft, Finset.image_id']
    rw [hi] at hg
    change |X.F σ - Y.F (σ.image f.1)| ≤ (δ : ℝ)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rintro ⟨e, he⟩
    let f : hom X Y δ := ⟨e, fun σ => by
      have h := (abs_le.mp (he σ)).2
      linarith⟩
    let g : hom Y X δ := ⟨e.symm, fun τ => by
      have h := (abs_le.mp (he (τ.image e.symm))).1
      have hi : (τ.image e.symm).image e = τ := by
        simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply, Finset.image_id']
      rw [hi] at h
      linarith⟩
    refine ⟨⟨f, g, ?_, ?_⟩⟩
    · apply Subtype.ext
      funext x
      exact e.symm_apply_apply x
    · apply Subtype.ext
      funext y
      exact e.apply_symm_apply y

/-- The finite discrete model in Lemma 6.8.6 is a sublevel-set persistence functor. -/
private def finiteCostFunctor {A : Type*} (cost : A → ℝ≥0) : ℝ≥0 ⥤ Type _ where
  obj r := {a : A // cost a ≤ r}
  map {r s} h := TypeCat.ofHom fun a => ⟨a.1, a.2.trans (leOfHom h)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

omit hL in
set_option backward.isDefEq.respectTransparency false in
/-- The closed inequalities in the finite model of Lemma 6.8.6 give right continuity. -/
private theorem finiteCost_rightContinuous {A : Type*} (cost : A → ℝ≥0) :
    IsRightContinuous (finiteCostFunctor cost) := by
  intro r
  rw [isIso_iff_bijective]
  constructor
  · intro a b hab
    apply Subtype.ext
    let s : {s : ℝ≥0 // r < s} := ⟨r + 1, lt_add_of_pos_right _ zero_lt_one⟩
    have h := congrArg (Limits.limit.π (upperSet r ⋙ finiteCostFunctor cost) s) hab
    simp only [← ConcreteCategory.comp_apply, Limits.limit.lift_π] at h
    exact congrArg (fun q : (finiteCostFunctor cost).obj s.1 => q.1) h
  · intro ℓ
    let w : ∀ s : {s : ℝ≥0 // r < s}, (finiteCostFunctor cost).obj s.1 :=
      fun s => Limits.limit.π (upperSet r ⋙ finiteCostFunctor cost) s ℓ
    have hw : ∀ (s t : {s : ℝ≥0 // r < s}) (h : s.1 ≤ t.1),
        (finiteCostFunctor cost).map (homOfLE h) (w s) = w t := by
      intro s t h
      exact Limits.limit.w_apply (upperSet r ⋙ finiteCostFunctor cost) (homOfLE h : s ⟶ t) ℓ
    let s₀ : {s : ℝ≥0 // r < s} := ⟨r + 1, lt_add_of_pos_right _ zero_lt_one⟩
    let a := (w s₀).1
    have ha : ∀ s, (w s).1 = a := by
      intro s
      let t : {s : ℝ≥0 // r < s} := ⟨max s.1 s₀.1, s.2.trans_le (le_max_left _ _)⟩
      exact (congrArg Subtype.val (hw s t (le_max_left _ _))).trans
        (congrArg Subtype.val (hw s₀ t (le_max_right _ _))).symm
    have hcost : cost a ≤ r := le_of_forall_gt_imp_ge_of_dense fun s hs => by
      have h := (w ⟨s, hs⟩).2
      rwa [ha] at h
    refine ⟨⟨a, hcost⟩, ?_⟩
    apply Types.limit_ext
    intro s
    simp only [← types_comp_apply, Limits.limit.lift_π]
    exact Subtype.ext (ha s).symm

omit hL in
/-- Finite discrete sublevels supply the q-tame, closed topologies of Lemma 6.8.6. -/
private theorem finiteCost_topologized {A : Type*} [Finite A] (cost : A → ℝ≥0) :
    Nonempty (TopologizedPersistentSet (finiteCostFunctor cost)) := by
  letI : ∀ r, TopologicalSpace ((finiteCostFunctor cost).obj r) := fun _ => ⊥
  letI : ∀ r, DiscreteTopology ((finiteCostFunctor cost).obj r) := fun _ => ⟨rfl⟩
  letI : ∀ r, Finite ((finiteCostFunctor cost).obj r) := fun r => by
    change Finite {a : A // cost a ≤ r}
    infer_instance
  refine ⟨{ top := fun r => inferInstance
            continuous := fun _ => continuous_of_discreteTopology
            isClosedMap := fun _ _ _ => isClosed_discrete _
            qtame := fun _ => (Set.toFinite _).isCompact }⟩

open scoped Classical in
/-- The finite subsets of `X × Y` with surjective projections, used for `QIᵇ` in Lemma 6.8.6. -/
private def ffsCorrespondences (X Y : FFSCpx) :=
  {R : Finset (X.carrier × Y.carrier) //
    (∀ x, ∃ y, (x, y) ∈ R) ∧ ∀ y, ∃ x, (x, y) ∈ R}

open scoped Classical in
/-- The maximum filtration discrepancy on a canonical model in Lemma 6.8.6. -/
private noncomputable def ffsCorrespondenceCost (X Y : FFSCpx)
    (R : ffsCorrespondences X Y) : ℝ≥0 :=
  Finset.univ.sup fun σ : Finset {p // p ∈ R.1} =>
    Real.nnabs (X.F (σ.image fun p => p.1.1) - Y.F (σ.image fun p => p.1.2))

omit hL in
open scoped Classical in
/-- The finite maximum is bounded exactly when all the source's pointwise inequalities hold. -/
private theorem ffsCorrespondenceCost_le (X Y : FFSCpx) (R : ffsCorrespondences X Y) (δ : ℝ≥0) :
    ffsCorrespondenceCost X Y R ≤ δ ↔ ∀ σ : Finset {p // p ∈ R.1},
      |X.F (σ.image fun p => p.1.1) - Y.F (σ.image fun p => p.1.2)| ≤ (δ : ℝ) := by
  unfold ffsCorrespondenceCost
  simp only [Finset.sup_le_iff, Finset.mem_univ, forall_const]
  simp only [← NNReal.coe_le_coe, Real.coe_nnabs]

omit hL in
set_option backward.isDefEq.respectTransparency false in
/-- A canonical finite model gives an acyclic cover and interleaving (Lemma 6.8.6). -/
private theorem ffsCorrespondence_cover (X Y : FFSCpx) (R : ffsCorrespondences X Y)
    (δ : ℝ≥0) (hR : ffsCorrespondenceCost X Y R ≤ δ) :
    ∃ (X' Y' : FFSCpx) (a : X' ⟶ X) (b : Y' ⟶ Y),
      acyclicFFSCpx a ∧ acyclicFFSCpx b ∧
      @IsInterleaved FFSCpx _ ffsCpxLPCat X' Y' δ := by
  classical
  let X' : FFSCpx :=
    { carrier := {p // p ∈ R.1}
      F := fun σ => X.F (σ.image fun p => p.1.1)
      mono := fun _ _ h => X.mono _ _ (Finset.image_subset_image h) }
  let Y' : FFSCpx :=
    { carrier := {p // p ∈ R.1}
      F := fun σ => Y.F (σ.image fun p => p.1.2)
      mono := fun _ _ h => Y.mono _ _ (Finset.image_subset_image h) }
  let a : X' ⟶ X := ⟨fun p => p.1.1, fun σ => by simp [X']⟩
  let b : Y' ⟶ Y := ⟨fun p => p.1.2, fun σ => by simp [Y']⟩
  refine ⟨X', Y', a, b, ⟨?_, fun _ => rfl⟩, ⟨?_, fun _ => rfl⟩, ?_⟩
  · intro x
    obtain ⟨y, hy⟩ := R.2.1 x
    exact ⟨⟨(x, y), hy⟩, rfl⟩
  · intro y
    obtain ⟨x, hx⟩ := R.2.2 y
    exact ⟨⟨(x, y), hx⟩, rfl⟩
  · apply (ffs_interleaved_iff X' Y' δ).2
    refine ⟨Equiv.refl _, fun σ => ?_⟩
    simpa [X', Y'] using (ffsCorrespondenceCost_le X Y R δ).1 hR σ

omit hL in
set_option backward.isDefEq.respectTransparency false in
/-- The source's map `(a, b ∘ e)` replaces any acyclic cover by a subset of `X × Y`,
without increasing its interleaving parameter (Lemma 6.8.6). -/
private theorem ffsCorrespondence_of_cover {X Y X' Y' : FFSCpx} (a : X' ⟶ X) (b : Y' ⟶ Y)
    (ha : acyclicFFSCpx a) (hb : acyclicFFSCpx b) {δ : ℝ≥0}
    (hi : @IsInterleaved FFSCpx _ ffsCpxLPCat X' Y' δ) :
    ∃ R : ffsCorrespondences X Y, ffsCorrespondenceCost X Y R ≤ δ := by
  classical
  obtain ⟨e, he⟩ := (ffs_interleaved_iff X' Y' δ).1 hi
  let v : X'.carrier → X.carrier × Y.carrier := fun x => (a.1 x, b.1 (e x))
  let R := Finset.univ.image v
  have hR : (∀ x, ∃ y, (x, y) ∈ R) ∧ ∀ y, ∃ x, (x, y) ∈ R := by
    constructor
    · intro x
      obtain ⟨x', rfl⟩ := ha.1 x
      exact ⟨b.1 (e x'), Finset.mem_image.mpr ⟨x', Finset.mem_univ _, rfl⟩⟩
    · intro y
      obtain ⟨y', rfl⟩ := hb.1 y
      exact ⟨a.1 (e.symm y'), Finset.mem_image.mpr
        ⟨e.symm y', Finset.mem_univ _, by simp [v]⟩⟩
  let Rc : ffsCorrespondences X Y := ⟨R, hR⟩
  refine ⟨Rc, (ffsCorrespondenceCost_le X Y Rc δ).2 ?_⟩
  intro σ
  let v' : X'.carrier → {p // p ∈ R} := fun x =>
    ⟨v x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
  have hv : Function.Surjective v' := by
    rintro ⟨p, hp⟩
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hp
    exact ⟨x, Subtype.ext hx⟩
  have hsub : σ ⊆ Finset.univ.image v' := by
    intro p _
    obtain ⟨x, rfl⟩ := hv p
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  obtain ⟨τ, hτ⟩ := Finset.subset_univ_image_iff.mp hsub
  have h := he τ
  rw [ha.2 τ, hb.2 (τ.image e)] at h
  have hX : σ.image (fun p => p.1.1) = τ.image a.1 := by
    rw [← hτ, Finset.image_image]
    rfl
  have hY : σ.image (fun p => p.1.2) = (τ.image e).image b.1 := by
    rw [← hτ, Finset.image_image, Finset.image_image]
    rfl
  rw [hX, hY]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **Lemma 6.8.6.** `(d_I)/≃` reflects quotient interleavings.
The proof applies the source's finite-model compactness argument directly to `QIᵇ`.

**Gap (typo, Lemma 6.8.6).** The displayed `QI` definition writes `epMetc` instead of `ffsCpx`,
and says that `f, g` interleave the endpoints rather than the intermediate objects `Z, Z'`. -/
theorem ffsCpx_reflects : @ReflectsQuotientInterleavings FFSCpx _ L acyclicFFSCpx := by
  subst hL
  classical
  letI := ffsCpxLPCat
  intro X Y δ hd
  letI : Finite (ffsCorrespondences X Y) :=
    Finite.of_injective (fun R : ffsCorrespondences X Y => R.1) Subtype.val_injective
  let cost := ffsCorrespondenceCost X Y
  obtain ⟨T⟩ := finiteCost_topologized cost
  have hne : ∀ r, δ < r → Nonempty ((finiteCostFunctor cost).obj r) := by
    intro r hr
    have hlt : quotientInterleavingDist acyclicFFSCpx X Y < (r : ℝ≥0∞) := by
      rw [hd]
      exact_mod_cast hr
    rw [ffsCpx_quotientInterleavingDist_spec ffsCpxLPCat rfl X Y] at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨δ', ⟨X', Y', a, b, ha, hb, hi⟩, hδ'⟩ := hlt
    have hi' := IsInterleaved.mono (by exact_mod_cast hδ'.le : δ' ≤ r) hi
    obtain ⟨R, hR⟩ := ffsCorrespondence_of_cover a b ha hb hi'
    exact ⟨⟨R, hR⟩⟩
  obtain ⟨R⟩ := nonempty_of_topologized_rc (finiteCost_rightContinuous cost) T δ hne
  obtain ⟨X', Y', a, b, ha, hb, hi⟩ := ffsCorrespondence_cover X Y R.1 δ R.2
  exact ⟨X', Y', Relation.EqvGen.rel _ _ ⟨a, ha⟩, Relation.EqvGen.rel _ _ ⟨b, hb⟩, hi⟩

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

set_option backward.isDefEq.respectTransparency false in
/-- **Proposition 6.8.8.** `(d_I)/≃ = d_F`. -/
theorem ffsCpx_quotientInterleavingDist_eq (X Y : FFSCpx) :
    @quotientInterleavingDist FFSCpx _ L acyclicFFSCpx X Y = ffsCpxDist X Y := by
  classical
  rw [ffsCpx_quotientInterleavingDist_spec L hL X Y]
  subst hL
  letI := ffsCpxLPCat
  unfold ffsCpxDist
  apply le_antisymm
  · refine le_iInf fun Z => le_iInf fun fin => le_iInf fun f => le_iInf fun g =>
      le_iInf fun hf => le_iInf fun hg => ?_
    letI := fin
    let D : ℝ≥0∞ := ⨆ σ : Finset Z, ENNReal.ofReal |X.F (σ.image f) - Y.F (σ.image g)|
    by_cases hD : D = ⊤
    · change _ ≤ D
      rw [hD]
      exact le_top
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0, D = δ := ⟨_, (ENNReal.coe_toNNReal hD).symm⟩
    change _ ≤ D
    rw [hδ]
    let X' : FFSCpx :=
      { carrier := Z
        F := fun σ => X.F (σ.image f)
        mono := fun _ _ h => X.mono _ _ (Finset.image_subset_image h) }
    let Y' : FFSCpx :=
      { carrier := Z
        F := fun σ => Y.F (σ.image g)
        mono := fun _ _ h => Y.mono _ _ (Finset.image_subset_image h) }
    let a : X' ⟶ X := ⟨f, fun σ => by simp [X']⟩
    let b : Y' ⟶ Y := ⟨g, fun σ => by simp [Y']⟩
    refine iInf₂_le_of_le δ ⟨X', Y', a, b, ⟨hf, fun _ => rfl⟩,
      ⟨hg, fun _ => rfl⟩, ?_⟩ le_rfl
    apply (ffs_interleaved_iff X' Y' δ).2
    refine ⟨Equiv.refl _, fun σ => ?_⟩
    have h : ENNReal.ofReal |X.F (σ.image f) - Y.F (σ.image g)| ≤ (δ : ℝ≥0∞) :=
      (le_iSup (fun σ : Finset Z => ENNReal.ofReal |X.F (σ.image f) - Y.F (σ.image g)|) σ).trans hδ.le
    simpa [X', Y'] using ENNReal.ofReal_le_coe.mp h
  · refine le_iInf₂ fun δ ⟨X', Y', a, b, ha, hb, hi⟩ => ?_
    obtain ⟨e, he⟩ := (ffs_interleaved_iff X' Y' δ).1 hi
    refine iInf_le_of_le X'.carrier (iInf_le_of_le (inferInstance : Fintype X'.carrier)
      (iInf_le_of_le a.1 (iInf_le_of_le (b.1 ∘ e)
        (iInf_le_of_le ha.1 (iInf_le_of_le (hb.1.comp e.surjective) ?_)))))
    refine iSup_le fun σ => ENNReal.ofReal_le_coe.mpr ?_
    have h := he σ
    rw [ha.2 σ, hb.2 (σ.image e)] at h
    simpa only [Finset.image_image] using h


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
