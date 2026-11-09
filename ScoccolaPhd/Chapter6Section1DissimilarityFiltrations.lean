import Mathlib
import ScoccolaPhd.Chapter5Section2Flows

/-!
# §§6.1–6.4: homotopy interleavings, dissimilarity spaces, filtrations

Contents:
* Chapter 6.1: The homotopy interleaving distance of a locally persistent model category
* Chapter 6.2: The Gromov–Hausdorff distance on dissimilarity spaces
* Chapter 6.3–6.4: Stability of Vietoris–Rips; persistent dissimilarity spaces
-/

universe u v w

namespace ScoccolaPhd

/-! ## Chapter 6.1: The homotopy interleaving distance of a locally persistent model category

Examples 6.1.8 (`Ch(R)^ℝ`, `sSet^ℝ`, `Top^ℝ`) and the comparisons induced by the Quillen
equivalence `|−| ⊣ S` and the chain complex functor are not yet formalized. -/

section HomotopyInterleaving

open CategoryTheory CategoryTheory.Limits MorphismProperty
open scoped NNReal ENNReal

open LPCat

variable {C : Type u} [Category.{v} C] [LPCat C]

/-- The homotopy interleaving distance (Section 6.1, [BL17]): the infimum of the `δ` such that
`x` and `y` are `δ`-interleaved after replacing them by weakly equivalent objects. -/
noncomputable def homotopyInterleavingDist (W : MorphismProperty C) (x y : C) : ℝ≥0∞ :=
  ⨅ (δ : ℝ≥0) (_ : ∃ x' y' : C, WeaklyEquivalent W x' x ∧ WeaklyEquivalent W y' y ∧
    IsInterleaved x' y' δ), (δ : ℝ≥0∞)

/-- The class `tFib = Fib ∩ W` of trivial fibrations. -/
def trivialFibrations (M : ModelStructure C) : MorphismProperty C := M.Fib ⊓ M.W

/-- Powers by representables preserve the trivial fibrations. -/
def PowersPreserveTrivialFibrations (M : ModelStructure C) [PoweredByRepresentables C] : Prop :=
  ∀ ε {a b : C} (f : a ⟶ b), trivialFibrations M f →
    trivialFibrations M ((PoweredByRepresentables.pow ε).map f)

/-- An object is fibrant if the map to the terminal object is a fibration. -/
def IsFibrant (M : ModelStructure C) (X : C) : Prop :=
  ∀ (T : C) (t : X ⟶ T), IsTerminal T → M.Fib t

/-- A locally persistent fibrant replacement functor: `F` with a natural weak equivalence
`id ⟹ F` whose values are fibrant. -/
structure LPFibrantReplacement (M : ModelStructure C) where
  F : LPFunctor C C
  η : 𝟭 C ⟶ F.toFunctor
  weq : ∀ X, M.W (η.app X)
  fibrant : ∀ X, IsFibrant M (F.toFunctor.obj X)

set_option backward.isDefEq.respectTransparency false in
/-- Copowers are left adjoint to powers, used for the limit hypotheses in Lemma 6.1.1
and Proposition 6.1.3. -/
noncomputable def copowPowAdjunction [PoweredByRepresentables C] [CopoweredByRepresentables C]
    (ε : ℝ≥0) : CopoweredByRepresentables.copow ε ⊣ PoweredByRepresentables.pow (C := C) ε := by
  let e := fun x y : C => (homZero (x := (CopoweredByRepresentables.copow ε).obj x) (y := y)).trans
    ((CopoweredByRepresentables.copowIso x y ε 0).trans
      ((PoweredByRepresentables.powIso x y ε 0).symm.trans homZero.symm))
  refine Adjunction.mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro x' x y f g
    apply homZero.injective
    apply (CopoweredByRepresentables.copowIso x' y ε 0).injective
    dsimp [e]
    rw [homZero_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [PoweredByRepresentables.powIso_S, PoweredByRepresentables.powIso_x,
      homZero_comp, Equiv.apply_symm_apply, CopoweredByRepresentables.copowIso_x,
      Equiv.apply_symm_apply, S_trans]
  · intro x y y' f g
    apply homZero.injective
    apply (PoweredByRepresentables.powIso x y' ε 0).injective
    dsimp [e]
    rw [Equiv.apply_symm_apply, homZero_comp, Equiv.apply_symm_apply]
    rw [CopoweredByRepresentables.copowIso_S, CopoweredByRepresentables.copowIso_y,
      homZero_comp, Equiv.apply_symm_apply, PoweredByRepresentables.powIso_y,
      Equiv.apply_symm_apply, S_trans]

/-- Right lifting classes are closed under sequential limits, used in Proposition 6.1.3. -/
theorem rlp_closedUnderSequentialLimits (W : MorphismProperty C) :
    IsClosedUnderSequentialLimits W.rlp := by
  intro X c hc hX n A B i hi
  let gc : GaloisConnection (fun k : ℕ => k - n.unop) (fun k : ℕ => k + n.unop) := by
    intro a b
    dsimp
    omega
  let T : ℕ ⥤ ℕ := gc.monotone_u.functor
  have : T.Final := Functor.final_of_adjunction gc.adjunction
  let ct := c.whisker T.op
  have hct : CategoryTheory.Limits.IsLimit ct := (Functor.Initial.isLimitWhiskerEquiv T.op c).symm hc
  have hco := isColimitCoconeRightOpOfCone (T.op ⋙ X) hct
  have hs := HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
    (hc := hco) (p := i.op) (fun j hj => by
      change HasLiftingProperty
        ((X.map (T.map (homOfLE (Order.le_succ j))).op).op) i.op
      exact (hX _ i hi).op)
  have h := hs.unop
  change HasLiftingProperty i (c.π.app (Opposite.op (0 + n.unop))) at h
  have hn : (Opposite.op (0 + n.unop) : ℕᵒᵖ) = n := by simp
  rw [hn] at h
  exact h

/-- **Lemma 6.1.1.** If `M` is copowered and powered by representables and powers preserve trivial
fibrations, then trivial fibrations are stable under weighted pullbacks. -/
theorem isStableUnderWeightedPullbacks_trivialFibrations (M : ModelCategory C)
    [PoweredByRepresentables C] [CopoweredByRepresentables C]
    (hpow : PowersPreserveTrivialFibrations M.str) :
    IsStableUnderWeightedPullbacks (trivialFibrations M.str) := by
  have : HasLimits C := M.hasLimits
  have h_eq : trivialFibrations M.str = M.str.wfs₁.L.rlp := by
    dsimp [trivialFibrations]
    rw [← M.str.wfs₁_R, M.str.wfs₁.R_eq]
  have : (trivialFibrations M.str).IsStableUnderBaseChange := by
    rw [h_eq]
    infer_instance
  apply isStableUnderWeightedPullbacks_of_powered
  · intro ε
    have := (copowPowAdjunction (C := C) ε).isRightAdjoint
    infer_instance
  · exact hpow

/-- Proposition 6.1.2. -/
theorem quotientInterleavingDist_tFib (M : ModelCategory C)
    [PoweredByRepresentables C] [CopoweredByRepresentables C]
    (hpow : PowersPreserveTrivialFibrations M.str) (x y : C) :
    quotientInterleavingDist (trivialFibrations M.str) x y =
      ⨅ (δ : ℝ≥0) (_ : ∃ x' y' : C, WeaklyEquivalent (trivialFibrations M.str) x' x ∧
        WeaklyEquivalent (trivialFibrations M.str) y' y ∧ IsInterleaved x' y' δ), (δ : ℝ≥0∞) := by
  have hW : IsStableUnderWeightedPullbacks (trivialFibrations M.str) :=
    isStableUnderWeightedPullbacks_trivialFibrations M hpow
  have h_eq : trivialFibrations M.str = M.str.wfs₁.L.rlp := by
    dsimp [trivialFibrations]
    rw [← M.str.wfs₁_R, M.str.wfs₁.R_eq]
  haveI : (trivialFibrations M.str).IsMultiplicative := by
    rw [h_eq]
    infer_instance
  exact quotientInterleavingDist_eq_inf_quotientInterleaved hW x y

/-- **Proposition 6.1.3.** The quotient distance by trivial fibrations is intrinsic
and complete under the power-preservation hypothesis. -/
theorem quotientInterleavingDist_tFib_intrinsic_complete (M : ModelCategory C)
    [PoweredByRepresentables C] [CopoweredByRepresentables C]
    (hpow : PowersPreserveTrivialFibrations M.str) :
    IsIntrinsicDist (quotientInterleavingDist (trivialFibrations M.str)) ∧
      IsCompleteDist (quotientInterleavingDist (trivialFibrations M.str)) := by
  have : HasLimits C := M.hasLimits
  have hpb : ∀ ε, PreservesLimitsOfShape WalkingCospan
      (PoweredByRepresentables.pow (C := C) ε) := fun ε => by
    have := (copowPowAdjunction (C := C) ε).isRightAdjoint
    infer_instance
  have hprod : ∀ ε, PreservesLimitsOfShape (Discrete WalkingPair)
      (PoweredByRepresentables.pow (C := C) ε) := fun ε => by
    have := (copowPowAdjunction (C := C) ε).isRightAdjoint
    infer_instance
  have hseq : ∀ ε, PreservesLimitsOfShape ℕᵒᵖ
      (PoweredByRepresentables.pow (C := C) ε) := fun ε => by
    have := (copowPowAdjunction (C := C) ε).isRightAdjoint
    infer_instance
  have h_eq : trivialFibrations M.str = M.str.wfs₁.L.rlp := by
    dsimp [trivialFibrations]
    rw [← M.str.wfs₁_R, M.str.wfs₁.R_eq]
  have : (trivialFibrations M.str).IsMultiplicative := by
    rw [h_eq]
    infer_instance
  have hlim : IsClosedUnderSequentialLimits (trivialFibrations M.str) := by
    rw [h_eq]
    exact rlp_closedUnderSequentialLimits _
  constructor
  · exact quotientInterleavingDistOf_intrinsic
      (admitsCoherentFactorizations_of_midpoints (hasTerminalMidpoints_of_powered hprod hpb))
      (WeaklyEquivalent (trivialFibrations M.str))
      (weaklyEquivalent_equivalence (trivialFibrations M.str))
  · exact quotientInterleavingDist_complete _ (hasWeightedSeqLimits_of_powered hseq) hlim
      (isStableUnderWeightedPullbacks_trivialFibrations M hpow)

/-- Lemma 6.1.4: any two fibrant weakly equivalent objects of a model category are connected
by a zig-zag of trivial fibrations. -/
theorem weaklyEquivalent_tFib_of_fibrant (M : ModelCategory C) {x y : C}
    (hx : IsFibrant M.str x) (hy : IsFibrant M.str y) (h : WeaklyEquivalent M.str.W x y) :
    WeaklyEquivalent (trivialFibrations M.str) x y := by
  sorry

omit [LPCat C] in
theorem id_mem_W (M : ModelCategory C) (X : C) : M.str.W (𝟙 X) := by
  let a : Arrow C := Arrow.mk (𝟙 X)
  have hπ : M.str.W (M.str.wfs₁.π.app a) := by
    have := M.str.wfs₁.π_mem a
    rw [M.str.wfs₁_R] at this
    exact this.2
  have hcomp : M.str.wfs₁.π.app a ≫ 𝟙 X = M.str.wfs₁.π.app a := Category.comp_id _
  exact M.str.twoOutOfThree.of_precomp (M.str.wfs₁.π.app a) (𝟙 X) hπ (by rw [hcomp]; exact hπ)

omit [LPCat C] in
theorem instIsMultiplicativeW (M : ModelCategory C) : M.str.W.IsMultiplicative where
  id_mem := id_mem_W M
  comp_mem := fun f g hf hg => M.str.twoOutOfThree.comp_mem f g hf hg

omit [LPCat C] in
theorem instIsMultiplicativeTFib (M : ModelCategory C) : (trivialFibrations M.str).IsMultiplicative := by
  have h_eq : trivialFibrations M.str = M.str.wfs₁.L.rlp := by
    dsimp [trivialFibrations]
    rw [← M.str.wfs₁_R, M.str.wfs₁.R_eq]
  rw [h_eq]
  infer_instance

/-- Lemma 6.1.5: a locally persistent fibrant replacement exhibits `(M, (d_I)/W)` as a pseudo
retract of `(M, (d_I)/tFib)`. (`C` is turned into an ep metric space by the respective
distance, through `PseudoEMetricSpace.ofEdist`-style structures; here the statement is that
`F` and `id` are distance non-increasing for the two distances and `F x ~ x`.) -/
theorem fibrantReplacement_retract (M : ModelCategory C) (R : LPFibrantReplacement M.str) :
    (∀ x y, quotientInterleavingDist (trivialFibrations M.str)
        (R.F.toFunctor.obj x) (R.F.toFunctor.obj y) ≤ quotientInterleavingDist M.str.W x y) ∧
      (∀ x y, quotientInterleavingDist M.str.W x y ≤
        quotientInterleavingDist (trivialFibrations M.str) x y) ∧
      ∀ x, quotientInterleavingDist M.str.W (R.F.toFunctor.obj x) x = 0 := by
  have : M.str.W.IsMultiplicative := instIsMultiplicativeW M
  have : (trivialFibrations M.str).IsMultiplicative := instIsMultiplicativeTFib M
  have hEqW : Equivalence (WeaklyEquivalent M.str.W) := weaklyEquivalent_equivalence M.str.W
  have hEqT : Equivalence (WeaklyEquivalent (trivialFibrations M.str)) :=
    weaklyEquivalent_equivalence (trivialFibrations M.str)
  have htFib_le_W : ∀ a b, WeaklyEquivalent (trivialFibrations M.str) a b → WeaklyEquivalent M.str.W a b := by
    intro a b hab
    induction hab with
    | rel x y h =>
      obtain ⟨f, hf⟩ := h
      exact Relation.EqvGen.rel x y ⟨f, hf.2⟩
    | refl x => exact hEqW.refl x
    | symm x y _ ih => exact hEqW.symm ih
    | trans x y z _ _ ih1 ih2 => exact hEqW.trans ih1 ih2
  have hF_weq : ∀ x y, WeaklyEquivalent M.str.W x y →
      WeaklyEquivalent (trivialFibrations M.str) (R.F.toFunctor.obj x) (R.F.toFunctor.obj y) := by
    intro x y hxy
    have hx : WeaklyEquivalent M.str.W (R.F.toFunctor.obj x) x :=
      hEqW.symm (Relation.EqvGen.rel x (R.F.toFunctor.obj x) ⟨R.η.app x, R.weq x⟩)
    have hy : WeaklyEquivalent M.str.W y (R.F.toFunctor.obj y) :=
      Relation.EqvGen.rel y (R.F.toFunctor.obj y) ⟨R.η.app y, R.weq y⟩
    have hxy_F : WeaklyEquivalent M.str.W (R.F.toFunctor.obj x) (R.F.toFunctor.obj y) :=
      hEqW.trans (hEqW.trans hx hxy) hy
    exact weaklyEquivalent_tFib_of_fibrant M (R.fibrant x) (R.fibrant y) hxy_F
  refine ⟨fun x y => ?_, fun x y => ?_, fun x => ?_⟩
  · exact LPFunctor.quotientInterleavingDist_le R.F M.str.W (trivialFibrations M.str) hF_weq x y
  · exact quotientDist_map_le _ _ interleavingDist_isEPMetric interleavingDist_isEPMetric
      id (fun a b => le_rfl) _ _ hEqT hEqW htFib_le_W x y
  · have hx : WeaklyEquivalent M.str.W (R.F.toFunctor.obj x) x :=
      hEqW.symm (Relation.EqvGen.rel x (R.F.toFunctor.obj x) ⟨R.η.app x, R.weq x⟩)
    have hinv := quotientDist_isInvariant interleavingDist (WeaklyEquivalent M.str.W) hEqW
      (R.F.toFunctor.obj x) x x x hx (hEqW.refl x)
    rw [quotientInterleavingDist, quotientInterleavingDistOf, hinv]
    exact (quotientInterleavingDist_isEPMetric M.str.W).refl x

/-- Theorem 6.1.6: for a locally persistent model category `M` which is powered and copowered
by representables, with powers preserving trivial fibrations and admitting a locally
persistent fibrant replacement, `(d_I^M)/W` is intrinsic and complete and equals the homotopy
interleaving distance. -/
theorem homotopyInterleavingDist_intrinsic_complete (M : ModelCategory C)
    [PoweredByRepresentables C] [CopoweredByRepresentables C]
    (hpow : PowersPreserveTrivialFibrations M.str) (R : LPFibrantReplacement M.str) :
    IsIntrinsicDist (quotientInterleavingDist M.str.W) ∧
      IsCompleteDist (quotientInterleavingDist M.str.W) ∧
      quotientInterleavingDist M.str.W = homotopyInterleavingDist M.str.W := by
  sorry

/-- Theorem 6.1.7: for `M` cofibrantly generated, the quotient interleaving distance of
`M^ℝ` (projective model structure `N`, with the locally persistent structure of persistent
objects) is intrinsic, complete, and equals the homotopy interleaving distance. -/
theorem homotopyInterleavingDist_persistent {C : Type u} [Category.{v} C]
    (M : ModelCategory C) (hM : IsCofibrantlyGenerated M.str)
    (N : ModelStructure (ℝ ⥤ C)) (hN : IsProjectiveModelStructure M.str N) :
    @IsIntrinsicDist (ℝ ⥤ C)
        (@quotientInterleavingDist (ℝ ⥤ C) _ (persistentLPCat C) N.W) ∧
      @IsCompleteDist (ℝ ⥤ C)
        (@quotientInterleavingDist (ℝ ⥤ C) _ (persistentLPCat C) N.W) ∧
      @quotientInterleavingDist (ℝ ⥤ C) _ (persistentLPCat C) N.W =
        @homotopyInterleavingDist (ℝ ⥤ C) _ (persistentLPCat C) N.W := by
  sorry

end HomotopyInterleaving

/-! ## Chapter 6.2: The Gromov–Hausdorff distance on dissimilarity spaces

The category `Diss` of dissimilarity spaces (a set with a function `X × X → [0, ∞]`) is made
into a locally persistent category (Definition 6.2.4); `Diss` is *constructed* here (category and
locally persistent structure, with proofs). Interleavings, powers, copowers and completeness
of the underlying category are also proved. Weak equivalences preserve the ep metric
axioms and compactness. The remaining statements are open.

Omitted: Proposition 6.2.15 (weighted sequential limits "of morphisms that are part of an
interleaving"), Lemma 6.2.19 and Example 6.2.14. -/

section Dissimilarity

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal Topology

open LPCat

/-- Definition 6.2.1: a dissimilarity space. -/
structure Diss where
  carrier : Type u
  d : carrier → carrier → ℝ≥0∞

namespace Diss

/-- Morphisms of dissimilarity spaces: maps with `d_X x x' ≥ d_Y (f x) (f x')`. -/
instance : Category.{u} Diss.{u} where
  Hom X Y := {f : X.carrier → Y.carrier // ∀ x x', Y.d (f x) (f x') ≤ X.d x x'}
  id X := ⟨id, fun _ _ => le_rfl⟩
  comp f g := ⟨g.1 ∘ f.1, fun x x' => (g.2 _ _).trans (f.2 x x')⟩

/-- Definition 6.2.4: `Hom_Diss(X, Y)_ε = Hom(ε · X, Y)`, i.e. maps with
`d_Y (f x) (f x') ≤ d_X x x' + ε`; composition and identities are those of functions. -/
instance : LPCat Diss.{u} where
  hom X Y ε := {f : X.carrier → Y.carrier // ∀ x x', Y.d (f x) (f x') ≤ X.d x x' + ε}
  homZero :=
    { toFun := fun f => ⟨f.1, fun x x' => by simpa using f.2 x x'⟩
      invFun := fun f => ⟨f.1, fun x x' => by simpa using f.2 x x'⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  comp {X Y Z ε δ} g f := ⟨g.1 ∘ f.1, fun x x' =>
    (g.2 _ _).trans (by
      calc Y.d (f.1 x) (f.1 x') + δ ≤ (X.d x x' + ε) + δ := by gcongr; exact f.2 x x'
        _ = X.d x x' + ((ε + δ : ℝ≥0) : ℝ≥0∞) := by push_cast; rw [add_assoc])⟩
  S {X Y ε δ} h f := ⟨f.1, fun x x' => (f.2 x x').trans (by
    gcongr)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  S_refl _ := rfl
  S_trans _ _ _ := rfl
  comp_S _ _ _ _ := rfl
  homZero_comp _ _ := rfl

end Diss

/-- `ε · X`'s dual: the power `X^ε` has the same points and distance `max (0, d - ε)`. -/
def Diss.power (ε : ℝ≥0) (X : Diss.{u}) : Diss.{u} := ⟨X.carrier, fun x x' => X.d x x' - ε⟩

/-- The copower `ε · X` has the same points and distance `d + ε`. -/
def Diss.copower (ε : ℝ≥0) (X : Diss.{u}) : Diss.{u} := ⟨X.carrier, fun x x' => X.d x x' + ε⟩

/-- Lemma 6.2.5: a `δ`-interleaving of dissimilarity spaces is a bijection
`e : X ≃ Y` with `|d_X x x' - d_Y (e x) (e x')| ≤ δ`. -/
theorem Diss.isInterleaved_iff (X Y : Diss.{u}) (δ : ℝ≥0) :
    IsInterleaved X Y δ ↔ ∃ e : X.carrier ≃ Y.carrier, ∀ x x',
      (X.d x x' - Y.d (e x) (e x')) ⊔ (Y.d (e x) (e x') - X.d x x') ≤ δ := by
  constructor
  · rintro ⟨⟨f, g, hfg, hgf⟩⟩
    have hleft : ∀ x, g.1 (f.1 x) = x := fun x => congrFun (congrArg Subtype.val hfg) x
    have hright : ∀ y, f.1 (g.1 y) = y := fun y => congrFun (congrArg Subtype.val hgf) y
    refine ⟨⟨f.1, g.1, hleft, hright⟩, fun x x' => sup_le ?_ (tsub_le_iff_right.mpr (by simpa [add_comm] using f.2 x x'))⟩
    change X.d x x' - Y.d (f.1 x) (f.1 x') ≤ (δ : ℝ≥0∞)
    apply tsub_le_iff_right.mpr
    simpa only [hleft, add_comm] using g.2 (f.1 x) (f.1 x')
  · rintro ⟨e, he⟩
    let f : hom X Y δ := ⟨e, fun x x' => by
      have h := tsub_le_iff_right.mp (le_sup_right.trans (he x x'))
      simpa [add_comm] using h⟩
    let g : hom Y X δ := ⟨e.symm, fun y y' => by
      have h := tsub_le_iff_right.mp ((le_sup_left).trans (he (e.symm y) (e.symm y')))
      simpa [add_comm] using h⟩
    refine ⟨⟨f, g, ?_, ?_⟩⟩
    · apply Subtype.ext
      funext x
      exact e.symm_apply_apply x
    · apply Subtype.ext
      funext y
      exact e.apply_symm_apply y

def Diss.copowFunctor (ε : ℝ≥0) : Diss.{u} ⥤ Diss.{u} where
  obj X := Diss.copower ε X
  map f := ⟨f.1, fun x x' => add_le_add (f.2 x x') le_rfl⟩

def Diss.powFunctor (ε : ℝ≥0) : Diss.{u} ⥤ Diss.{u} where
  obj X := Diss.power ε X
  map f := ⟨f.1, fun x x' => tsub_le_tsub_right (f.2 x x') _⟩

def Diss.adj (ε : ℝ≥0) : Diss.copowFunctor ε ⊣ Diss.powFunctor ε :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _ _ => {
      toFun := fun f => ⟨f.1, fun x x' => tsub_le_iff_right.mpr (f.2 x x')⟩
      invFun := fun g => ⟨g.1, fun x x' => tsub_le_iff_right.mp (g.2 x x')⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
    }
    homEquiv_naturality_left_symm := fun _ _ => Subtype.ext rfl
    homEquiv_naturality_right := fun _ _ => Subtype.ext rfl
  }

noncomputable instance (ε : ℝ≥0) : (Diss.powFunctor ε).IsRightAdjoint := ⟨_, ⟨Diss.adj ε⟩⟩

@[instance_reducible]
def Diss.powered : PoweredByRepresentables Diss.{u} :=
  { pow := Diss.powFunctor
    powIso := fun X Y ε r =>
      { toFun := fun f => ⟨f.1, fun x x' => by
          have h := tsub_le_iff_right.mp (f.2 x x')
          simpa [Diss.power, ENNReal.coe_add, add_comm, add_left_comm, add_assoc] using h⟩
        invFun := fun f => ⟨f.1, fun x x' => by
          apply tsub_le_iff_right.mpr
          simpa [ENNReal.coe_add, add_comm, add_left_comm, add_assoc] using f.2 x x'⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    powIso_S := fun _ _ => rfl
    powIso_x := fun _ _ => rfl
    powIso_y := fun _ _ => rfl }

instance : PoweredByRepresentables Diss.{u} := Diss.powered

noncomputable instance (ε : ℝ≥0) : (PoweredByRepresentables.pow (C := Diss.{u}) ε).IsRightAdjoint :=
  inferInstanceAs ((Diss.powFunctor ε).IsRightAdjoint)

/-- Lemma 6.2.6: `Diss` is powered by representables, with powers `X^ε`. -/
theorem Diss.exists_powered :
    ∃ P : PoweredByRepresentables Diss.{u}, ∀ ε X, (P.pow ε).obj X = Diss.power ε X :=
  ⟨Diss.powered, fun _ _ => rfl⟩

/-- Lemma 6.2.6: `Diss` is copowered by representables, with copowers `ε · X`. -/
theorem Diss.exists_copowered :
    ∃ P : CopoweredByRepresentables Diss.{u}, ∀ ε X, (P.copow ε).obj X = Diss.copower ε X := by
  let P : CopoweredByRepresentables Diss.{u} :=
    { copow := fun ε =>
        { obj := Diss.copower ε
          map := fun f => ⟨f.1, fun x x' => add_le_add (f.2 x x') le_rfl⟩ }
      copowIso := fun X Y ε r =>
        { toFun := fun f => ⟨f.1, fun x x' => by
            simpa [Diss.copower, ENNReal.coe_add, add_assoc] using f.2 x x'⟩
          invFun := fun f => ⟨f.1, fun x x' => by
            simpa [Diss.copower, ENNReal.coe_add, add_assoc] using f.2 x x'⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      copowIso_S := fun _ _ => rfl
      copowIso_x := fun _ _ => rfl
      copowIso_y := fun _ _ => rfl }
  exact ⟨P, fun _ _ => rfl⟩

/-- The limit of a diagram of dissimilarity spaces: compatible families with the supremum
distance. -/
noncomputable def Diss.limitPt {J : Type v} [Category.{w} J] (F : J ⥤ Diss.{max u v}) : Diss.{max u v} :=
  ⟨{x : ∀ j, (F.obj j).carrier // ∀ ⦃i j⦄ (f : i ⟶ j), (F.map f).1 (x i) = x j},
    fun x y => ⨆ j, (F.obj j).d (x.1 j) (y.1 j)⟩

/-- The limit cone of `Diss.limitPt`. -/
noncomputable def Diss.limitCone {J : Type v} [Category.{w} J] (F : J ⥤ Diss.{max u v}) : Cone F where
  pt := Diss.limitPt F
  π :=
    { app := fun j => ⟨fun x => x.1 j, fun x y => le_iSup (fun j => (F.obj j).d (x.1 j) (y.1 j)) j⟩
      naturality := by
        intro i j f
        apply Subtype.ext
        funext x
        exact (x.2 f).symm }

/-- `Diss.limitCone` is a limit cone. -/
noncomputable def Diss.limitConeIsLimit {J : Type v} [Category.{w} J] (F : J ⥤ Diss.{max u v}) :
    Limits.IsLimit (Diss.limitCone F) where
  lift s := ⟨fun x => ⟨fun j => (s.π.app j).1 x, fun i j f =>
      (congrFun (congrArg Subtype.val (s.π.naturality f)) x).symm⟩,
    fun x y => iSup_le fun j => (s.π.app j).2 x y⟩
  fac := fun s j => rfl
  uniq := by
    intro s m hm
    apply Subtype.ext
    funext x
    apply Subtype.ext
    funext j
    exact congrFun (congrArg Subtype.val (hm j)) x

/-- Lemma 6.2.7: the underlying category of `Diss` is complete. -/
instance Diss.hasLimits : HasLimits Diss.{u} :=
  ⟨fun J _ => ⟨fun F => ⟨⟨Diss.limitCone F, Diss.limitConeIsLimit F⟩⟩⟩⟩

/-- Lemma 6.2.8: `Diss` admits weighted sequential limits. -/
theorem Diss.hasWeightedSeqLimits : HasWeightedSeqLimits Diss.{u} :=
  hasWeightedSeqLimits_of_powered (fun _ => inferInstance)

/-- Lemma 6.2.8: `Diss` admits terminal midpoints. -/
theorem Diss.hasTerminalMidpoints : HasTerminalMidpoints Diss.{u} :=
  hasTerminalMidpoints_of_powered (fun _ => inferInstance) (fun _ => inferInstance)

/-- Definition 6.2.9: a morphism of dissimilarity spaces is acyclic if it is surjective and
distance preserving. -/
def acyclicDiss : MorphismProperty Diss.{u} :=
  fun X Y f => Function.Surjective f.1 ∧ ∀ x x', Y.d (f.1 x) (f.1 x') = X.d x x'

instance : acyclicDiss.{u}.IsMultiplicative where
  id_mem _ := ⟨Function.surjective_id, fun _ _ => rfl⟩
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1, fun x x' => (hg.2 _ _).trans (hf.2 x x')⟩

theorem eq_of_isPullback_proj_eq {X Y Y' S : Diss.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (hsq : IsPullback f' g' g f)
    (a b : Y'.carrier) (hX : g'.1 a = g'.1 b) (hY : f'.1 a = f'.1 b) : a = b := by
  let Pone : Diss.{u} := ⟨PUnit, fun _ _ => Y'.d a a ⊔ Y'.d b b⟩
  let ma : Pone ⟶ Y' := ⟨fun _ => a, fun _ _ => le_sup_left⟩
  let mb : Pone ⟶ Y' := ⟨fun _ => b, fun _ _ => le_sup_right⟩
  have h1 : ma ≫ f' = mb ≫ f' := by
    apply Subtype.ext
    funext ⟨⟩
    exact hY
  have h2 : ma ≫ g' = mb ≫ g' := by
    apply Subtype.ext
    funext ⟨⟩
    exact hX
  have heq : ma = mb := hsq.hom_ext h1 h2
  exact congrFun (congrArg Subtype.val heq) PUnit.unit

theorem surjective_of_isPullback {X Y Y' S : Diss.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (hsq : IsPullback f' g' g f) (hg : Function.Surjective g.1) :
    Function.Surjective g'.1 := by
  intro x
  obtain ⟨y, hy⟩ := hg (f.1 x)
  let Pone : Diss.{u} := ⟨PUnit, fun _ _ => X.d x x ⊔ Y.d y y⟩
  let ptX : Pone ⟶ X := ⟨fun _ => x, fun _ _ => le_sup_left⟩
  let ptY : Pone ⟶ Y := ⟨fun _ => y, fun _ _ => le_sup_right⟩
  have heq : ptY ≫ g = ptX ≫ f := by
    apply Subtype.ext
    funext ⟨⟩
    exact hy
  let c : PullbackCone g f := PullbackCone.mk ptY ptX heq
  let u : Pone ⟶ Y' := hsq.isLimit.lift c
  have hu : u ≫ g' = ptX := hsq.isLimit.fac c WalkingCospan.right
  use u.1 PUnit.unit
  have := congrFun (congrArg Subtype.val hu) PUnit.unit
  exact this

theorem dist_preserving_of_isPullback {X Y Y' S : Diss.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (hsq : IsPullback f' g' g f) (hg : acyclicDiss g)
    (a b : Y'.carrier) : X.d (g'.1 a) (g'.1 b) = Y'.d a b := by
  have hle : X.d (g'.1 a) (g'.1 b) ≤ Y'.d a b := g'.2 a b
  refine le_antisymm hle ?_
  let x₁ := g'.1 a
  let x₂ := g'.1 b
  let y₁ := f'.1 a
  let y₂ := f'.1 b
  have hcomm : ∀ z : Y'.carrier, f.1 (g'.1 z) = g.1 (f'.1 z) := fun z => by
    have := congrFun (congrArg Subtype.val hsq.w.symm) z
    exact this
  have hy : Y.d y₁ y₂ ≤ X.d x₁ x₂ := by
    have hd := hg.2 y₁ y₂
    have heq1 := hcomm a
    have heq2 := hcomm b
    rw [← hd, ← heq1, ← heq2]
    exact f.2 x₁ x₂
  have hy' : Y.d y₂ y₁ ≤ X.d x₂ x₁ := by
    have hd := hg.2 y₂ y₁
    have heq1 := hcomm a
    have heq2 := hcomm b
    rw [← hd, ← heq1, ← heq2]
    exact f.2 x₂ x₁
  let dP : Bool → Bool → ℝ≥0∞ := fun i j =>
    match i, j with
    | false, false => X.d x₁ x₁ ⊔ Y.d y₁ y₁
    | true, true => X.d x₂ x₂ ⊔ Y.d y₂ y₂
    | false, true => X.d x₁ x₂
    | true, false => X.d x₂ x₁
  let Ptwo : Diss.{u} := ⟨ULift Bool, fun i j => dP i.down j.down⟩
  let mX : Ptwo ⟶ X := ⟨fun i => match i.down with | false => x₁ | true => x₂, fun i j => by
    rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
    · exact le_sup_left
    · rfl
    · rfl
    · exact le_sup_left⟩
  let mY : Ptwo ⟶ Y := ⟨fun i => match i.down with | false => y₁ | true => y₂, fun i j => by
    rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
    · exact le_sup_right
    · exact hy
    · exact hy'
    · exact le_sup_right⟩
  have heq : mY ≫ g = mX ≫ f := by
    apply Subtype.ext
    funext ⟨i⟩
    cases i
    · exact (hcomm a).symm
    · exact (hcomm b).symm
  let c : PullbackCone g f := PullbackCone.mk mY mX heq
  let u : Ptwo ⟶ Y' := hsq.isLimit.lift c
  have huX : u ≫ g' = mX := hsq.isLimit.fac c WalkingCospan.right
  have huY : u ≫ f' = mY := hsq.isLimit.fac c WalkingCospan.left
  have hu_a : u.1 ⟨false⟩ = a := by
    apply eq_of_isPullback_proj_eq hsq
    · exact congrFun (congrArg Subtype.val huX) ⟨false⟩
    · exact congrFun (congrArg Subtype.val huY) ⟨false⟩
  have hu_b : u.1 ⟨true⟩ = b := by
    apply eq_of_isPullback_proj_eq hsq
    · exact congrFun (congrArg Subtype.val huX) ⟨true⟩
    · exact congrFun (congrArg Subtype.val huY) ⟨true⟩
  have hu_le := u.2 ⟨false⟩ ⟨true⟩
  rw [hu_a, hu_b] at hu_le
  exact hu_le

instance : acyclicDiss.{u}.IsStableUnderBaseChange where
  of_isPullback hsq hg :=
    ⟨surjective_of_isPullback hsq hg.1, dist_preserving_of_isPullback hsq hg⟩

theorem hpow_acyclicDiss :
    ∀ ε {a b : Diss.{u}} (f : a ⟶ b), acyclicDiss f →
      acyclicDiss ((PoweredByRepresentables.pow ε).map f) := by
  intro ε a b f ⟨hsurj, hdist⟩
  refine ⟨hsurj, fun x x' => ?_⟩
  exact congrArg (· - (ε : ℝ≥0∞)) (hdist x x')

/-- Proposition 6.2.10. -/
theorem isStableUnderWeightedPullbacks_acyclicDiss :
    IsStableUnderWeightedPullbacks acyclicDiss.{u} :=
  isStableUnderWeightedPullbacks_of_powered (C := Diss.{u}) (fun _ => inferInstance) hpow_acyclicDiss

theorem Diss.exists_compatible_of_surj (X : ℕᵒᵖ ⥤ Diss.{u})
    (hs : ∀ k, Function.Surjective (X.map (homOfLE (Nat.le_succ k)).op).1) (n : ℕ)
    (y : (X.obj ⟨n⟩).carrier) :
    ∃ z : ∀ j : ℕᵒᵖ, (X.obj j).carrier,
      (∀ ⦃i j : ℕᵒᵖ⦄ (f : i ⟶ j), (X.map f).1 (z i) = z j) ∧ z ⟨n⟩ = y := by
  classical
  let zf : ∀ j, n ≤ j → (X.obj ⟨j⟩).carrier := fun j hj =>
    Nat.leRec (motive := fun j _ => (X.obj ⟨j⟩).carrier) y
      (fun j _ ih => (hs j ih).choose) hj
  have zf_succ : ∀ j (hj : n ≤ j), (X.map (homOfLE (Nat.le_succ j)).op).1 (zf (j+1) (hj.trans (Nat.le_succ j))) = zf j hj := by
    intro j hj
    have : zf (j+1) (hj.trans (Nat.le_succ j)) = (hs j (zf j hj)).choose := by
      simp only [zf]; rw [Nat.leRec_succ]
    rw [this]; exact (hs j (zf j hj)).choose_spec
  have zf_n : zf n le_rfl = y := by simp [zf]
  -- compatibility along n ≤ j ≤ i
  have zf_map : ∀ j (hj : n ≤ j) (d : ℕ) (f : (⟨j + d⟩ : ℕᵒᵖ) ⟶ ⟨j⟩),
      (X.map f).1 (zf (j+d) (hj.trans (Nat.le_add_right _ _))) = zf j hj := by
    intro j hj d
    induction d with
    | zero => intro f; have : f = 𝟙 _ := Subsingleton.elim _ _
              subst this; rw [X.map_id]; rfl
    | succ d ih =>
      intro f
      have hf : f = (homOfLE (Nat.le_succ (j+d))).op ≫ (homOfLE (Nat.le_add_right j d)).op := Subsingleton.elim _ _
      rw [hf, X.map_comp]
      change (X.map (homOfLE (Nat.le_add_right j d)).op).1 ((X.map (homOfLE (Nat.le_succ (j+d))).op).1 _) = _
      rw [zf_succ (j+d) (hj.trans (Nat.le_add_right _ _))]
      exact ih _
  refine ⟨fun j => if h : n ≤ j.unop then zf j.unop h else (X.map (homOfLE (le_of_not_ge h)).op).1 y, ?_, ?_⟩
  · rintro ⟨i⟩ ⟨j⟩ f
    have hji : j ≤ i := f.unop.le
    dsimp only
    by_cases hj : n ≤ j
    · have hi : n ≤ i := hj.trans hji
      rw [dif_pos hi, dif_pos hj]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
      exact zf_map j hj d f
    · rw [dif_neg hj]
      by_cases hi : n ≤ i
      · rw [dif_pos hi]
        have hnj : j ≤ n := le_of_not_ge hj
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show n ≤ i from hi)
        have hf : f = (homOfLE (Nat.le_add_right n d)).op ≫ (homOfLE hnj).op := Subsingleton.elim _ _
        rw [hf, X.map_comp]
        change (X.map (homOfLE hnj).op).1 ((X.map (homOfLE (Nat.le_add_right n d)).op).1 _) = _
        rw [zf_map n le_rfl d (homOfLE (Nat.le_add_right n d)).op, zf_n]
      · rw [dif_neg hi]
        have hin : i ≤ n := le_of_not_ge hi
        have hf : (homOfLE (le_of_not_ge hi)).op ≫ f = (homOfLE (le_of_not_ge hj)).op := Subsingleton.elim _ _
        have := congrArg (fun g => g.1 y) (congrArg X.map hf)
        rw [X.map_comp] at this
        exact this
  · dsimp only; rw [dif_pos le_rfl]; exact zf_n

/-- Acyclic morphisms of `Diss` are closed under sequential limits (used in Theorem 6.2.11). -/
theorem Diss.isClosedUnderSequentialLimits_acyclicDiss :
    IsClosedUnderSequentialLimits acyclicDiss.{u} := by
  intro X c hc hX n
  have hP := Diss.limitConeIsLimit X
  let i := hc.conePointUniqueUpToIso hP
  have hcomp : c.π.app n = i.hom ≫ (Diss.limitCone X).π.app n := by simp [i]
  -- distances of compatible families are constant
  have hconst : ∀ (p q : (Diss.limitPt X).carrier) (j : ℕᵒᵖ),
      (X.obj j).d (p.1 j) (q.1 j) = (X.obj n).d (p.1 n) (q.1 n) := by
    intro p q j
    rcases le_total n.unop j.unop with h | h
    · have f : j ⟶ n := (homOfLE h).op
      rw [← p.2 f, ← q.2 f]
      exact ((hX f).2 _ _).symm
    · have f : n ⟶ j := (homOfLE h).op
      rw [← p.2 f, ← q.2 f]
      exact (hX f).2 _ _
  have hdist : ∀ p q : (Diss.limitPt X).carrier,
      (Diss.limitPt X).d p q = (X.obj n).d (p.1 n) (q.1 n) := by
    intro p q
    refine le_antisymm (iSup_le fun j => (hconst p q j).le) ?_
    exact le_iSup (fun j => (X.obj j).d (p.1 j) (q.1 j)) n
  have hsurjP : Function.Surjective ((Diss.limitCone X).π.app n).1 := by
    intro y
    have hs : ∀ k, Function.Surjective (X.map (homOfLE (Nat.le_succ k)).op).1 :=
      fun k => (hX _).1
    obtain ⟨z, hz, hzn⟩ := Diss.exists_compatible_of_surj X hs n.unop y
    exact ⟨⟨z, fun _ _ f => hz f⟩, hzn⟩
  have hsurji : Function.Surjective i.hom.1 := fun p =>
    ⟨i.inv.1 p, congrFun (congrArg Subtype.val i.inv_hom_id) p⟩
  have hiinv : ∀ x, i.inv.1 (i.hom.1 x) = x := fun x =>
    congrFun (congrArg Subtype.val i.hom_inv_id) x
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact hsurjP.comp hsurji
  · intro x x'
    rw [hcomp]
    change (X.obj n).d (((Diss.limitCone X).π.app n).1 (i.hom.1 x))
      (((Diss.limitCone X).π.app n).1 (i.hom.1 x')) = _
    have h1 := i.hom.2 x x'
    have h2 := i.inv.2 (i.hom.1 x) (i.hom.1 x')
    rw [hiinv, hiinv] at h2
    have := le_antisymm h2 h1
    exact ((hdist (i.hom.1 x) (i.hom.1 x')).symm).trans this.symm

/-- Theorem 6.2.11: the quotient interleaving distance of `Diss` is intrinsic and complete,
and is computed by interleavings of acyclic covers. -/
theorem Diss.quotientInterleavingDist_spec :
    IsIntrinsicDist (quotientInterleavingDist acyclicDiss.{u}) ∧
      IsCompleteDist (quotientInterleavingDist acyclicDiss.{u}) ∧
      ∀ X Y : Diss.{u}, quotientInterleavingDist acyclicDiss X Y =
        ⨅ (δ : ℝ≥0) (_ : ∃ (X' Y' : Diss.{u}) (a : X' ⟶ X) (b : Y' ⟶ Y),
          acyclicDiss a ∧ acyclicDiss b ∧ IsInterleaved X' Y' δ), (δ : ℝ≥0∞) := by
  refine ⟨?_, ?_, fun X Y => ?_⟩
  · exact quotientInterleavingDistOf_intrinsic
      (admitsCoherentFactorizations_of_midpoints Diss.hasTerminalMidpoints) _
      (weaklyEquivalent_equivalence _)
  · exact quotientInterleavingDist_complete _ Diss.hasWeightedSeqLimits
      Diss.isClosedUnderSequentialLimits_acyclicDiss isStableUnderWeightedPullbacks_acyclicDiss
  · exact quotientInterleavingDist_eq_inf_acyclicCover isStableUnderWeightedPullbacks_acyclicDiss X Y

/-! ### The Gromov–Hausdorff distance on dissimilarity spaces -/

/-- Definition 2.2.25 for dissimilarity spaces: a correspondence is a relation with full
projections. -/
def Diss.IsCorrespondence {X Y : Diss.{u}} (R : Set (X.carrier × Y.carrier)) : Prop :=
  (∀ x, ∃ y, (x, y) ∈ R) ∧ ∀ y, ∃ x, (x, y) ∈ R

/-- The distortion `sup |d_X (x, x') - d_Y (y, y')|` of a relation. -/
noncomputable def Diss.distortion {X Y : Diss.{u}} (R : Set (X.carrier × Y.carrier)) : ℝ≥0∞ :=
  ⨆ (p ∈ R) (q ∈ R), (X.d p.1 q.1 - Y.d p.2 q.2) ⊔ (Y.d p.2 q.2 - X.d p.1 q.1)

/-- Definition 6.2.3: `d_GH (X, Y) = ½ inf { dist R }`. -/
noncomputable def Diss.gromovHausdorff (X Y : Diss.{u}) : ℝ≥0∞ :=
  2⁻¹ * ⨅ (R : Set (X.carrier × Y.carrier)) (_ : Diss.IsCorrespondence R), Diss.distortion R

/-- Theorem 6.2.12: `d_I^{Diss}/≃ = 2 d_GH`. -/
theorem Diss.quotientInterleavingDist_eq_two_mul_gromovHausdorff (X Y : Diss.{u}) :
    quotientInterleavingDist acyclicDiss X Y = 2 * Diss.gromovHausdorff X Y := by
  rw [quotientInterleavingDist_eq_inf_acyclicCover isStableUnderWeightedPullbacks_acyclicDiss]
  unfold Diss.gromovHausdorff
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  apply le_antisymm
  · refine le_iInf₂ fun R hR => ?_
    by_cases hD : Diss.distortion R = ⊤
    · rw [hD]; exact le_top
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0, Diss.distortion R = δ := ⟨_, (ENNReal.coe_toNNReal hD).symm⟩
    rw [hδ]
    let X' : Diss.{u} := ⟨R, fun p q => X.d p.1.1 q.1.1⟩
    let Y' : Diss.{u} := ⟨R, fun p q => Y.d p.1.2 q.1.2⟩
    let a : X' ⟶ X := ⟨fun p => p.1.1, fun _ _ => le_rfl⟩
    let b : Y' ⟶ Y := ⟨fun p => p.1.2, fun _ _ => le_rfl⟩
    refine iInf₂_le_of_le δ ⟨X', Y', a, b, ⟨?_, fun _ _ => rfl⟩, ⟨?_, fun _ _ => rfl⟩, ?_⟩ le_rfl
    · intro x; obtain ⟨y, hy⟩ := hR.1 x; exact ⟨⟨(x, y), hy⟩, rfl⟩
    · intro y; obtain ⟨x, hx⟩ := hR.2 y; exact ⟨⟨(x, y), hx⟩, rfl⟩
    · rw [Diss.isInterleaved_iff]
      refine ⟨Equiv.refl _, fun p q => ?_⟩
      have := le_iSup₂ (f := fun (p : X.carrier × Y.carrier) (_ : p ∈ R) =>
        ⨆ (q : X.carrier × Y.carrier) (_ : q ∈ R),
          (X.d p.1 q.1 - Y.d p.2 q.2) ⊔ (Y.d p.2 q.2 - X.d p.1 q.1)) p.1 p.2
      have h2 := (le_iSup₂ (f := fun (q : X.carrier × Y.carrier) (_ : q ∈ R) =>
          (X.d p.1.1 q.1 - Y.d p.1.2 q.2) ⊔ (Y.d p.1.2 q.2 - X.d p.1.1 q.1)) q.1 q.2).trans this
      exact h2.trans (by rw [Diss.distortion] at hδ; exact hδ.le)
  · refine le_iInf₂ fun δ ⟨X', Y', a, b, ha, hb, hI⟩ => ?_
    obtain ⟨e, he⟩ := (Diss.isInterleaved_iff _ _ _).1 hI
    let R : Set (X.carrier × Y.carrier) := {p | ∃ x', a.1 x' = p.1 ∧ b.1 (e x') = p.2}
    have hRc : Diss.IsCorrespondence R := by
      refine ⟨fun x => ?_, fun y => ?_⟩
      · obtain ⟨x', hx'⟩ := ha.1 x; exact ⟨b.1 (e x'), x', hx', rfl⟩
      · obtain ⟨y', hy'⟩ := hb.1 y
        exact ⟨a.1 (e.symm y'), e.symm y', rfl, by simpa using hy'⟩
    refine iInf₂_le_of_le R hRc ?_
    refine iSup₂_le fun p hp => iSup₂_le fun q hq => ?_
    rcases p with ⟨p1, p2⟩
    rcases q with ⟨q1, q2⟩
    obtain ⟨x, rfl, rfl⟩ := hp
    obtain ⟨z, rfl, rfl⟩ := hq
    simp only
    rw [ha.2, hb.2]
    exact he x z

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

/-- Proposition 6.2.18: `epMet` admits coherent factorizations of interleavings. -/
theorem epMet_admitsCoherentFactorizations : AdmitsCoherentFactorizations EPMet.{u} := by
  intro x y ε hε f g hpair
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
            pair := fun r r' h => ⟨Subtype.ext rfl, Subtype.ext rfl⟩ }, ?_, ?_⟩
  · refine ⟨⟨⟨id, fun p p' => ?_⟩, ⟨id, fun p p' => ?_⟩, Subtype.ext rfl, Subtype.ext rfl⟩⟩
    · exact (hd0 p p').le.trans le_self_add
    · exact (hd0 p p').symm.le.trans le_self_add
  · refine ⟨⟨⟨f.1, fun p p' => ?_⟩, ⟨g.1, fun q q' => ?_⟩, Subtype.ext (funext hgf),
      Subtype.ext (funext hfg)⟩⟩
    · exact (hdε p p').symm.le.trans le_self_add
    · refine ((hdε (g.1 q) (g.1 q')).trans ?_).le.trans le_self_add
      change edist (f.1 (g.1 q)) (f.1 (g.1 q')) = edist q q'
      rw [hfg, hfg]


/-- Proposition 6.2.18 (compact case): if the interleaved spaces are compact, the factorization
can be chosen with all objects compact.

**Gap (proof gap, Proposition 6.2.18).** The thesis argues that a sequence in `M_γ` "has a subsequence
that converges in `P`, which in turn has a subsequence that converges in `Q`, and thus converges in
`M_γ`". This uses continuity of the bijection `f`, which an `ε`-interleaving does not provide
(`f` may distort distances by `ε`). For instance, take `P = Q = [0,1]` and `f` swapping `1/2` and
`3/4` (an `ε`-interleaving for `ε = 1/4`): for `0 < γ < ε` the sequence `1/2 + 1/n` has no
convergent subsequence in `M_γ`, so `M_γ` is not compact. Taking the closure of the graph of
`f` in `P × Q` repairs compactness, but then the maps of the factorization are no longer
bijections, which `IsInterleavingPair` requires; a correct proof needs a different argument.

**Gap (missing hypothesis, Proposition 6.2.18).** The Lean statement is also corrected: the
thesis tacitly needs `0 < ε`, and the endpoints of the factorization are only `0`-interleaved with
`P` and `Q` (they have a different underlying set, so they cannot be *equal* to them). -/
theorem epMet_coherentFactorizations_compact {P Q : EPMet.{u}} {ε : ℝ≥0} (hε : 0 < ε)
    (f : hom P Q ε) (g : hom Q P ε) (hfg : IsInterleavingPair f g) [CompactSpace P.carrier]
    [CompactSpace Q.carrier] :
    ∃ F : CoherentFactorization EPMet.{u} ε,
      IsInterleaved P (F.z (lo ε)) 0 ∧ IsInterleaved (F.z (hi ε)) Q 0 ∧
      ∀ r, CompactSpace (F.z r).carrier := by
  sorry

/-- Theorem 6.2.20: the quotient interleaving distance of `epMet` is `2 d_GH`, intrinsic and
complete. -/
theorem epMet_quotientInterleavingDist :
    (∀ P Q : EPMet.{u}, quotientInterleavingDist acyclicEPMet P Q = 2 * gromovHausdorff P Q) ∧
      IsIntrinsicDist (quotientInterleavingDist acyclicEPMet.{u}) ∧
      IsCompleteDist (quotientInterleavingDist acyclicEPMet.{u}) := by
  sorry

/-- Theorem 6.2.20 (compact case): on compact ep metric spaces, `d_GH` is geodesic and complete,
and two compact metric spaces at distance zero are isometric. -/
theorem epMetc_gromovHausdorff :
    IsGeodesicDist (fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} =>
      gromovHausdorff P.1 Q.1) ∧
    IsCompleteDist (fun P Q : {P : EPMet.{u} // CompactSpace P.carrier} =>
      gromovHausdorff P.1 Q.1) ∧
    ∀ (P Q : EPMet.{u}) [CompactSpace P.carrier] [CompactSpace Q.carrier]
      [T0Space P.carrier] [T0Space Q.carrier], gromovHausdorff P Q = 0 →
        Nonempty (P.carrier ≃ᵢ Q.carrier) := by
  sorry

/-- Proposition 6.2.21 (universal property of `d_GH`): a function `f` out of ep metric spaces
into an ep metric space `Z` is uniformly continuous for `d_GH` if it is uniformly continuous
for the sup distance between ep metrics on a fixed set, and constant on acyclic covers. -/
theorem gromovHausdorff_universal {Z : Type v} [PseudoEMetricSpace Z] (f : EPMet.{u} → Z)
    (hmetric : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ (X : Type u) (d₁ d₂ : X → X → ℝ≥0∞)
      (h₁ : IsEPMetric d₁) (h₂ : IsEPMetric d₂),
      (∀ x y, (d₁ x y - d₂ x y) ⊔ (d₂ x y - d₁ x y) ≤ δ) →
        edist (f (epMetOfDist d₁ h₁)) (f (epMetOfDist d₂ h₂)) ≤ ε)
    (hacyclic : ∀ (P Q : EPMet.{u}) (a : P ⟶ Q), acyclicEPMet.{u} a → edist (f P) (f Q) = 0) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ P Q : EPMet.{u},
      gromovHausdorff P Q < δ → edist (f P) (f Q) ≤ ε := by
  sorry

/-- Definition 6.2.22: a pseudo isometry is a map `f : P → Q` that is an isometry onto the
associated metric spaces: distance preserving and with dense... here, distance preserving and
surjective up to distance zero. -/
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
zig-zag of pseudo isometries iff connected by a zig-zag of acyclic morphisms. -/
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

end Dissimilarity

/-! ## Chapter 6.3–6.4: Stability of Vietoris–Rips; persistent dissimilarity spaces

Simplicial complexes `SCpx` and the Vietoris–Rips filtration are defined concretely.  Mathlib
has neither the geometric realization of abstract simplicial complexes nor weak homotopy
equivalences of spaces, so statements involving `Top` are made relative to a functor
`real : SCpx ⥤ TopCat` and a class `Wtop` of weak equivalences (the weak equivalences of the model
structure on `Top` of Example 2.5.11), together with Lemma 6.3.3 as a hypothesis
(`RealizationInvertsFullSurjections`).

Omitted: 6.4.4 (dynamic metric spaces / `λ`-slack interleaving), Remark 6.4.5, and the Čech-type
variations mentioned after Theorem 6.3.5.  The change of enrichment of 5.1 records hom-sets
only, so the locally persistent functors involved are stated to *exist* as `LPFunctor`s over
the given structures.

Statements only (the definitions are given); all proofs are `sorry`. -/

section Filtrations

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

open LPCat
open scoped Classical

/-! ### 6.3 Simplicial complexes and the Vietoris–Rips filtration -/

/-- Simplicial complexes: a set with a down-closed family of finite non-empty subsets. -/
structure SCpx where
  carrier : Type u
  S : Set (Finset carrier)
  nonempty : ∀ σ ∈ S, σ.Nonempty
  down : ∀ σ ∈ S, ∀ τ : Finset carrier, τ ⊆ σ → τ.Nonempty → τ ∈ S

/-- Morphisms of simplicial complexes: maps sending simplices to simplices. -/
instance : Category.{u} SCpx.{u} where
  Hom X Y := {f : X.carrier → Y.carrier // ∀ σ ∈ X.S, σ.image f ∈ Y.S}
  id X := ⟨id, fun σ hσ => by simpa using hσ⟩
  comp f g := ⟨g.1 ∘ f.1, fun σ hσ => by
    classical
    have := g.2 _ (f.2 σ hσ)
    rwa [Finset.image_image] at this⟩

/-- Definition 6.3.1: the Vietoris–Rips complex of a dissimilarity space at scale `r`.

**Note.** Writing the condition as `X.d x y ≤ ENNReal.ofReal r` alone is
wrong for `r < 0`: `ENNReal.ofReal r = 0` there, so distance-zero subsets would be simplices at
negative scales, whereas in the thesis (`d(x, x) = 0 ≤ r` fails) the complex is empty for `r < 0`.
With the clamped version an `ε`-morphism need not map simplices at scale `r < 0` to simplices at
scale `r + ε > 0`, and Lemma 6.3.2 is false. We add the condition `0 ≤ r`. -/
def vrComplex (X : Diss.{u}) (r : ℝ) : SCpx.{u} where
  carrier := X.carrier
  S := {σ | σ.Nonempty ∧ 0 ≤ r ∧ ∀ x ∈ σ, ∀ y ∈ σ, X.d x y ≤ ENNReal.ofReal r}
  nonempty σ hσ := hσ.1
  down σ hσ τ hτ hne := ⟨hne, hσ.2.1, fun x hx y hy => hσ.2.2 x (hτ hx) y (hτ hy)⟩

/-- Definition 6.3.1: the Vietoris–Rips filtration `VR(X) : ℝ ⥤ SCpx` (structure maps are the
inclusions). -/
def vrFiltration (X : Diss.{u}) : ℝ ⥤ SCpx.{u} where
  obj r := vrComplex X r
  map {r s} h := ⟨fun x => x, fun σ hσ => by
    have e : σ.image (fun x : X.carrier => x) = σ := Finset.image_id
    have hσ' : σ.Nonempty ∧ 0 ≤ r ∧ ∀ x ∈ σ, ∀ y ∈ σ, X.d x y ≤ ENNReal.ofReal r := hσ
    show σ.image (fun x : X.carrier => x) ∈ {σ : Finset X.carrier | σ.Nonempty ∧ 0 ≤ s ∧
      ∀ x ∈ σ, ∀ y ∈ σ, X.d x y ≤ ENNReal.ofReal s}
    rw [e]
    exact ⟨hσ'.1, hσ'.2.1.trans (leOfHom h), fun x hx y hy => (hσ'.2.2 x hx y hy).trans
      (ENNReal.ofReal_le_ofReal (leOfHom h))⟩⟩
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The component at scale `r` of the Vietoris–Rips functor on a morphism `f : X → Y`. -/
def vrMap {X Y : Diss.{u}} (f : X ⟶ Y) (r : ℝ) : vrComplex X r ⟶ vrComplex Y r :=
  ⟨f.1, fun σ hσ => by
    classical
    refine ⟨hσ.1.image _, hσ.2.1, ?_⟩
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    exact (f.2 a b).trans (hσ.2.2 a ha b hb)⟩

/-- The functor `Diss ⥤ sCpx^ℝ`, `X ↦ VR(X)`. -/
def vrFunctor : Diss.{u} ⥤ (ℝ ⥤ SCpx.{u}) where
  obj X := vrFiltration X
  map {X Y} f :=
    { app := fun r => vrMap f r
      naturality := fun r s h => by apply Subtype.ext; rfl }
  map_id := by intros; apply NatTrans.ext; funext r; apply Subtype.ext; rfl
  map_comp := by intros; apply NatTrans.ext; funext r; apply Subtype.ext; rfl

/-- An `ε`-morphism of dissimilarity spaces induces an `ε`-morphism `VR X ⟶ VR Y` of persistent
simplicial complexes (`VR X r ⟶ VR Y (ε + r)`). -/
def vrApproxMap {X Y : Diss.{u}} {ε : ℝ≥0}
    (f : LPCat.hom X Y ε) : vrFiltration X ⟶ shift (ε : ℝ) (vrFiltration Y) :=
  PersistentObjects.mk' (ε : ℝ) (fun q => ⟨f.1, fun σ hσ => by
    classical
    refine ⟨hσ.1.image _, add_nonneg (NNReal.coe_nonneg ε) hσ.2.1, ?_⟩
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    have h1 : X.d (a : X.carrier) (b : X.carrier) ≤ ENNReal.ofReal q := hσ.2.2 a ha b hb
    refine (f.2 (a : X.carrier) (b : X.carrier)).trans ?_
    rw [ENNReal.ofReal_add (NNReal.coe_nonneg ε) hσ.2.1, ENNReal.ofReal_coe_nnreal, add_comm]
    exact add_le_add_right h1 _⟩) (by
    intro q q' h; apply Subtype.ext; rfl)

/-- Lemma 6.3.2: `VR : Diss → sCpx^ℝ` is a locally persistent functor (for the locally
persistent category of persistent objects of `sCpx`, Example 3.1.3). -/
theorem exists_vr_lpFunctor :
    letI : LPCat (ℝ ⥤ SCpx.{u}) := persistentLPCat SCpx.{u}
    ∃ Φ : LPFunctor Diss.{u} (ℝ ⥤ SCpx.{u}), ∀ X, Φ.toFunctor.obj X = vrFiltration X := by
  letI : LPCat (ℝ ⥤ SCpx.{u}) := persistentLPCat SCpx.{u}
  refine ⟨{ toFunctor := vrFunctor
            map := fun {X Y ε} f => vrApproxMap f
            map_zero := ?_
            map_comp := ?_
            map_S := ?_ }, fun X => rfl⟩
  · intro X Y f
    apply NatTrans.ext; funext q; apply Subtype.ext; rfl
  · intro X Y Z ε δ f g
    apply NatTrans.ext; funext q; apply Subtype.ext; rfl
  · intro X Y ε δ h f
    apply NatTrans.ext; funext q; apply Subtype.ext; rfl

/-- Lemma 6.3.3 (hypothesis on the geometric realization `real`): a simplicial map which is
surjective on vertices and such that `σ` is a simplex iff `f σ` is, realizes to a weak
equivalence. -/
def RealizationInvertsFullSurjections (real : SCpx.{u} ⥤ TopCat.{u})
    (Wtop : MorphismProperty TopCat.{u}) : Prop :=
  ∀ {X Y : SCpx.{u}} (f : X ⟶ Y), Function.Surjective f.1 →
    (∀ σ : Finset X.carrier, σ.Nonempty → (σ ∈ X.S ↔ σ.image f.1 ∈ Y.S)) → Wtop (real.map f)

/-- Proposition 6.3.4: the Vietoris–Rips functor followed by the realization maps acyclic
morphisms of dissimilarity spaces to weak equivalences, at every scale. -/
theorem vr_maps_acyclic (real : SCpx.{u} ⥤ TopCat.{u}) (Wtop : MorphismProperty TopCat.{u})
    (h : RealizationInvertsFullSurjections real Wtop) {X Y : Diss.{u}} (f : X ⟶ Y)
    (hf : acyclicDiss f) (r : ℝ) : Wtop (real.map (vrMap f r)) := by
  refine h (vrMap f r) hf.1 ?_
  intro σ hne
  have hne_im : (σ.image f.1).Nonempty := hne.image f.1
  change (σ.Nonempty ∧ 0 ≤ r ∧ ∀ x ∈ σ, ∀ y ∈ σ, X.d x y ≤ ENNReal.ofReal r) ↔
    ((σ.image f.1).Nonempty ∧ 0 ≤ r ∧
      ∀ u ∈ σ.image f.1, ∀ v ∈ σ.image f.1, Y.d u v ≤ ENNReal.ofReal r)
  simp only [hne, hne_im, true_and]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hσ u hu v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    have hd : Y.d (f.1 x) (f.1 y) = X.d x y := hf.2 (x : X.carrier) (y : X.carrier)
    rw [hd]
    exact hσ x hx y hy
  · intro h_im x hx y hy
    have hd : X.d x y = Y.d (f.1 x) (f.1 y) := (hf.2 (x : X.carrier) (y : X.carrier)).symm
    rw [hd]
    exact h_im (f.1 x) (Finset.mem_image_of_mem _ hx) (f.1 y) (Finset.mem_image_of_mem _ hy)

/-- The functor `Diss ⥤ Top^ℝ`, `X ↦ |VR(X)|`. -/
def vrTop (real : SCpx.{u} ⥤ TopCat.{u}) : Diss.{u} ⥤ (ℝ ⥤ TopCat.{u}) where
  obj X := vrFiltration X ⋙ real
  map {X Y} f :=
    { app := fun r => real.map (vrMap f r)
      naturality := fun r s h => by
        change real.map _ ≫ real.map _ = real.map _ ≫ real.map _
        erw [← real.map_comp, ← real.map_comp]; rfl }
  map_id := by
    intro X
    apply NatTrans.ext
    funext r
    change real.map (vrMap (𝟙 X) r) = 𝟙 _
    rw [← real.map_id]; rfl
  map_comp := by
    intro X Y Z f g
    apply NatTrans.ext
    funext r
    change real.map (vrMap (f ≫ g) r) = real.map (vrMap f r) ≫ real.map (vrMap g r)
    rw [← real.map_comp]; rfl

/-- Theorem 6.3.5 (cf. [BL17]): `real ∘ VR : Diss → Top^ℝ` is 2-Lipschitz with respect to the
Gromov–Hausdorff distance and the homotopy interleaving distance. -/
theorem vr_lipschitz (real : SCpx.{u} ⥤ TopCat.{u}) (Wtop : MorphismProperty TopCat.{u})
    (h : RealizationInvertsFullSurjections real Wtop) :
    letI : LPCat (ℝ ⥤ TopCat.{u}) := persistentLPCat TopCat.{u}
    ∃ Φ : LPFunctor Diss.{u} (ℝ ⥤ TopCat.{u}),
      Φ.toFunctor = vrTop real ∧
      ∀ X Y : Diss.{u}, homotopyInterleavingDist (levelwiseProp Wtop) (Φ.toFunctor.obj X)
          (Φ.toFunctor.obj Y) ≤ 2 * Diss.gromovHausdorff X Y := by
  letI : LPCat (ℝ ⥤ TopCat.{u}) := persistentLPCat TopCat.{u}
  let Φ : LPFunctor Diss.{u} (ℝ ⥤ TopCat.{u}) :=
    { toFunctor := vrTop real
      map := fun {X Y ε} f => Functor.whiskerRight (vrApproxMap f) real
      map_zero := ?_
      map_comp := ?_
      map_S := ?_ }
  · refine ⟨Φ, rfl, fun X Y => ?_⟩
    rw [← Diss.quotientInterleavingDist_eq_two_mul_gromovHausdorff,
      quotientInterleavingDist_eq_inf_acyclicCover isStableUnderWeightedPullbacks_acyclicDiss]
    refine le_iInf₂ fun δ hδ => ?_
    obtain ⟨X', Y', a, b, ha, hb, hI⟩ := hδ
    refine iInf₂_le_of_le δ ⟨Φ.toFunctor.obj X', Φ.toFunctor.obj Y', ?_, ?_, ?_⟩ le_rfl
    · exact Relation.EqvGen.rel _ _ ⟨Φ.toFunctor.map a, fun r => vr_maps_acyclic real Wtop h a ha r⟩
    · exact Relation.EqvGen.rel _ _ ⟨Φ.toFunctor.map b, fun r => vr_maps_acyclic real Wtop h b hb r⟩
    · exact Φ.isInterleaved_map hI
  · intro X Y f
    apply NatTrans.ext; funext q
    erw [PersistentObjects.toZero_app (hr := by simp)]
    change real.map _ = real.map (vrMap f q) ≫ real.map _
    refine Eq.trans (congrArg real.map ?_) (real.map_comp (vrMap f q) _)
    exact Subtype.ext rfl
  · intro X Y Z ε δ f g
    apply NatTrans.ext; funext q
    erw [PersistentObjects.compR_app]
    unfold PersistentObjects.mapEq
    have e : ∀ {A B C D : SCpx.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D),
        real.map (a ≫ b ≫ c) = real.map a ≫ real.map b ≫ real.map c := by intros; simp
    refine Eq.trans (congrArg real.map ?_) (e _ _ _)
    exact Subtype.ext rfl
  · intro X Y ε δ hh f
    apply NatTrans.ext; funext q
    erw [PersistentObjects.shiftR_app]
    refine Eq.trans (congrArg real.map ?_) (real.map_comp _ _)
    exact Subtype.ext rfl

/-! ### 6.4 Persistent dissimilarity spaces -/

/-- Definition 6.4.1: the locally bi-persistent category `Diss^ℝ` of persistent dissimilarity
spaces is the instance of Definition 5.1.7 for `C = Diss` (`exists_lqpcat_persistent`): its
`(ε, δ)`-morphisms are natural transformations `X → Y^{(ε, δ)}`. -/
theorem exists_persistentDiss_lqpcat :
    ∃ L : LQPCat (ℝ≥0 × ℝ≥0) (ℝ ⥤ Diss.{u}), ∀ (X Y : ℝ ⥤ Diss.{u}) (ε δ : ℝ≥0),
      L.hom X Y (ε, δ) = PersistentHom X Y ε δ :=
  exists_lqpcat_persistent

/-- Definition 6.4.2: the acyclic morphisms of `Diss^ℝ` are the levelwise acyclic ones. -/
abbrev acyclicPersistentDiss : MorphismProperty (ℝ ⥤ Diss.{u}) := levelwiseProp acyclicDiss

/-- Definition 6.4.3 / Proposition 6.4.4: the Gromov–Hausdorff-interleaving distance (the
quotient interleaving distance of `Diss^ℝ_v`, for any locally persistent structure `L` obtained
by change of enrichment along `v`) is intrinsic and complete, and is an infimum over interleavings
of acyclic covers. -/
theorem ghInterleaving_spec (LR : LQPCat (ℝ≥0 × ℝ≥0) (ℝ ⥤ Diss.{u})) (v : ℝ≥0 × ℝ≥0)
    (L : LPCat (ℝ ⥤ Diss.{u})) (hL : IsChangeOfEnrichment (pairFamily v) LR L) :
    @IsIntrinsicDist (ℝ ⥤ Diss.{u}) (@quotientInterleavingDist _ _ L acyclicPersistentDiss) ∧
    @IsCompleteDist (ℝ ⥤ Diss.{u}) (@quotientInterleavingDist _ _ L acyclicPersistentDiss) ∧
    ∀ X Y : ℝ ⥤ Diss.{u}, @quotientInterleavingDist _ _ L acyclicPersistentDiss X Y =
      ⨅ (δ : ℝ≥0) (_ : ∃ (X' Y' : ℝ ⥤ Diss.{u}) (a : X' ⟶ X) (b : Y' ⟶ Y),
        acyclicPersistentDiss a ∧ acyclicPersistentDiss b ∧ @IsInterleaved _ _ L X' Y' δ),
        (δ : ℝ≥0∞) := by
  sorry

/-! #### 6.4.2 Filtered metric spaces -/

/-- A finite filtered metric space [CM10c]: a finite metric space with a filtering function. -/
structure FFMet where
  carrier : Type
  [fin : Fintype carrier]
  [metric : MetricSpace carrier]
  f : carrier → ℝ

attribute [instance] FFMet.fin FFMet.metric

/-- The filtered distortion `max (dist R, ‖f_X ∘ π_X - f_Y ∘ π_Y‖_∞)` of a relation. -/
noncomputable def FFMet.filteredDistortion {X Y : FFMet} (R : Set (X.carrier × Y.carrier)) :
    ℝ≥0∞ :=
  max (⨆ (p ∈ R) (q ∈ R), (edist p.1 q.1 - edist p.2 q.2) ⊔ (edist p.2 q.2 - edist p.1 q.1))
    (⨆ p ∈ R, ENNReal.ofReal |X.f p.1 - Y.f p.2|)

/-- [CM10c, Definition 2]: `D(X, Y) = inf_R dist_f R` over correspondences. -/
noncomputable def FFMet.dist (X Y : FFMet) : ℝ≥0∞ :=
  ⨅ (R : Set (X.carrier × Y.carrier)) (_ : (∀ x, ∃ y, (x, y) ∈ R) ∧ ∀ y, ∃ x, (x, y) ∈ R),
    FFMet.filteredDistortion R

/-- The sublevel-set filtration `r ↦ f_X⁻¹((-∞, r)) ∈ Diss` of a filtered metric space. -/
def FFMet.sublevel (X : FFMet) : ℝ ⥤ Diss.{0} where
  obj r := ⟨{x : X.carrier // X.f x < r}, fun a b => edist a.1 b.1⟩
  map {r s} h := ⟨fun a => ⟨a.1, lt_of_lt_of_le a.2 (leOfHom h)⟩, fun a b => le_rfl⟩
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Theorem 6.4.6: for `v = (1, 1)`, the Gromov–Hausdorff-interleaving distance of the
sublevel filtrations is `D(X, Y)`. -/
theorem ghInterleaving_eq_filteredDist (LR : LQPCat (ℝ≥0 × ℝ≥0) (ℝ ⥤ Diss.{0}))
    (L : LPCat (ℝ ⥤ Diss.{0})) (hL : IsChangeOfEnrichment (pairFamily (1, 1)) LR L)
    (X Y : FFMet) :
    @quotientInterleavingDist _ _ L acyclicPersistentDiss X.sublevel Y.sublevel =
      FFMet.dist X Y := by
  sorry

/-! #### 6.4.3 Stability of the parametrized Vietoris–Rips filtration -/

/-- Theorem 6.4.7: applying `|VR|` levelwise, `Diss^ℝ_v → (Top^ℝ)^ℝ_v`, is 1-Lipschitz for the
Gromov–Hausdorff-interleaving distance and the quotient interleaving distance of bi-persistent
topological spaces (levelwise weak equivalences). -/
theorem vrStar_lipschitz (real : SCpx.{u} ⥤ TopCat.{u}) (Wtop : MorphismProperty TopCat.{u})
    (h : RealizationInvertsFullSurjections real Wtop)
    [LPCat (ℝ ⥤ Diss.{u})] [LPCat (ℝ ⥤ TopCat.{u})] [LPCat (ℝ ⥤ (ℝ ⥤ TopCat.{u}))] :
    ∃ Φ : LPFunctor (ℝ ⥤ Diss.{u}) (ℝ ⥤ (ℝ ⥤ TopCat.{u})),
      Φ.toFunctor = (Functor.whiskeringRight ℝ Diss.{u} (ℝ ⥤ TopCat.{u})).obj (vrTop real) ∧
      ∀ X Y : ℝ ⥤ Diss.{u},
        quotientInterleavingDist (levelwiseProp (levelwiseProp Wtop)) (Φ.toFunctor.obj X)
          (Φ.toFunctor.obj Y) ≤ quotientInterleavingDist acyclicPersistentDiss X Y := by
  sorry

end Filtrations

end ScoccolaPhd
