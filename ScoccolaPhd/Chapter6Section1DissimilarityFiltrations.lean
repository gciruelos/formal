import Mathlib
import ScoccolaPhd.Chapter5Section2Flows

/-!
# §§6.1–6.4: homotopy interleavings, dissimilarity spaces, filtrations

Contents:
* Chapter 6.1: The homotopy interleaving distance of a locally persistent model category
* Chapter 6.2.1: The Gromov–Hausdorff distance on dissimilarity spaces
* The metric-space part (§6.2.2) is in `Chapter6Section2MetricSpaces.lean`
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
  haveI : HasLimits C := M.hasLimits
  have hFib_eq : M.str.Fib = M.str.wfs₂.L.rlp := by
    rw [← M.str.wfs₂_R, M.str.wfs₂.R_eq]
  have hFib_stable : M.str.Fib.IsStableUnderBaseChange := by
    rw [hFib_eq]; infer_instance
  have hFib_mult : M.str.Fib.IsMultiplicative := by
    rw [hFib_eq]; infer_instance
  have hFib_iso : M.str.Fib.RespectsIso := by
    rw [hFib_eq]; infer_instance
  have id_W : ∀ z : C, M.str.W (𝟙 z) := fun z => by
    let a : CategoryTheory.Arrow C := CategoryTheory.Arrow.mk (𝟙 z)
    have hπ : M.str.W (M.str.wfs₁.π.app a) := by
      have := M.str.wfs₁.π_mem a
      rw [M.str.wfs₁_R] at this
      exact this.2
    have hcomp : M.str.wfs₁.π.app a ≫ 𝟙 z = M.str.wfs₁.π.app a := Category.comp_id _
    exact M.str.twoOutOfThree.of_precomp (M.str.wfs₁.π.app a) (𝟙 z) hπ (by rw [hcomp]; exact hπ)
  have trivFib_of_weq : ∀ {a b : C} (ha : IsFibrant M.str a) (hb : IsFibrant M.str b)
      (f : a ⟶ b), M.str.W f → WeaklyEquivalent (trivialFibrations M.str) a b := by
    intro a b ha hb f hf
    let arr : CategoryTheory.Arrow C := CategoryTheory.Arrow.mk (prod.lift (𝟙 a) f)
    let e := M.str.wfs₂.mid.obj arr
    let j : a ⟶ e := M.str.wfs₂.ι.app arr
    let q : e ⟶ a ⨯ b := M.str.wfs₂.π.app arr
    have hj_mem : (M.str.Cof ⊓ M.str.W) j := by
      rw [← M.str.wfs₂_L]; exact M.str.wfs₂.ι_mem arr
    have hq_fib : M.str.Fib q := by
      rw [← M.str.wfs₂_R]; exact M.str.wfs₂.π_mem arr
    have hpb_fst : IsPullback (prod.fst : a ⨯ b ⟶ a) (prod.snd : a ⨯ b ⟶ b)
        (terminal.from a) (terminal.from b) :=
      { w := terminal.hom_ext _ _
        isLimit' := ⟨PullbackCone.IsLimit.mk _ (fun s => prod.lift s.fst s.snd)
          (fun _ => prod.lift_fst _ _) (fun _ => prod.lift_snd _ _)
          (fun _ _ h1 h2 => prod.hom_ext (by simpa using h1) (by simpa using h2))⟩ }
    have hfst_fib : M.str.Fib (prod.fst : a ⨯ b ⟶ a) :=
      hFib_stable.of_isPullback hpb_fst.flip (hb _ (terminal.from b) terminalIsTerminal)
    have hsnd_fib : M.str.Fib (prod.snd : a ⨯ b ⟶ b) :=
      hFib_stable.of_isPullback hpb_fst (ha _ (terminal.from a) terminalIsTerminal)
    have hp1_fib : M.str.Fib (q ≫ prod.fst) := hFib_mult.comp_mem q prod.fst hq_fib hfst_fib
    have hp2_fib : M.str.Fib (q ≫ prod.snd) := hFib_mult.comp_mem q prod.snd hq_fib hsnd_fib
    have hfac1 : j ≫ q ≫ prod.fst = 𝟙 a := by
      rw [← Category.assoc, M.str.wfs₂.fac arr]
      exact prod.lift_fst (𝟙 a) f
    have hfac2 : j ≫ q ≫ prod.snd = f := by
      rw [← Category.assoc, M.str.wfs₂.fac arr]
      exact prod.lift_snd (𝟙 a) f
    have hp1_W : M.str.W (q ≫ prod.fst) :=
      M.str.twoOutOfThree.of_precomp j (q ≫ prod.fst) hj_mem.2 (by rw [hfac1]; exact id_W a)
    have hp2_W : M.str.W (q ≫ prod.snd) :=
      M.str.twoOutOfThree.of_precomp j (q ≫ prod.snd) hj_mem.2 (by rw [hfac2]; exact hf)
    have h1 : WeaklyEquivalent (trivialFibrations M.str) a e :=
      Relation.EqvGen.symm _ _ (Relation.EqvGen.rel e a ⟨q ≫ prod.fst, hp1_fib, hp1_W⟩)
    have h2 : WeaklyEquivalent (trivialFibrations M.str) e b :=
      Relation.EqvGen.rel e b ⟨q ≫ prod.snd, hp2_fib, hp2_W⟩
    exact Relation.EqvGen.trans a e b h1 h2
  let R : C → C := fun z => M.str.wfs₂.mid.obj (CategoryTheory.Arrow.mk (terminal.from z))
  let r : ∀ z : C, z ⟶ R z := fun z => M.str.wfs₂.ι.app (CategoryTheory.Arrow.mk (terminal.from z))
  have hr_mem : ∀ z : C, (M.str.Cof ⊓ M.str.W) (r z) := fun z => by
    rw [← M.str.wfs₂_L]; exact M.str.wfs₂.ι_mem (CategoryTheory.Arrow.mk (terminal.from z))
  have hR_fib : ∀ z : C, IsFibrant M.str (R z) := fun z T t ht => by
    let p := M.str.wfs₂.π.app (CategoryTheory.Arrow.mk (terminal.from z))
    have hp : M.str.Fib p := by
      rw [← M.str.wfs₂_R]; exact M.str.wfs₂.π_mem (CategoryTheory.Arrow.mk (terminal.from z))
    let iso : ⊤_ C ≅ T := terminalIsTerminal.uniqueUpToIso ht
    have ht_eq : t = p ≫ iso.hom := ht.hom_ext _ _
    rw [ht_eq]
    exact MorphismProperty.RespectsIso.postcomp M.str.Fib iso.hom p hp
  have hR_weq : ∀ {a b : C} (f : a ⟶ b), M.str.W f →
      WeaklyEquivalent (trivialFibrations M.str) (R a) (R b) := by
    intro a b f hf
    let pb := M.str.wfs₂.π.app (CategoryTheory.Arrow.mk (terminal.from b))
    have hpb_fib : M.str.Fib pb := by
      rw [← M.str.wfs₂_R]; exact M.str.wfs₂.π_mem (CategoryTheory.Arrow.mk (terminal.from b))
    have hsq : CommSq (f ≫ r b) (r a) pb (terminal.from (R a)) :=
      ⟨terminal.hom_ext _ _⟩
    have hllp : HasLiftingProperty (r a) pb := by
      have hrL : M.str.wfs₂.L (r a) := M.str.wfs₂.ι_mem (CategoryTheory.Arrow.mk (terminal.from a))
      rw [M.str.wfs₂.L_eq, M.str.wfs₂_R] at hrL
      exact hrL pb hpb_fib
    let Rf : R a ⟶ R b := hsq.lift
    have hRf_W : M.str.W Rf := by
      have hcomp : M.str.W (r a ≫ Rf) := by
        rw [hsq.fac_left]
        exact M.str.twoOutOfThree.comp_mem f (r b) hf (hr_mem b).2
      exact M.str.twoOutOfThree.of_precomp (r a) Rf (hr_mem a).2 hcomp
    exact trivFib_of_weq (hR_fib a) (hR_fib b) Rf hRf_W
  have hxy : WeaklyEquivalent (trivialFibrations M.str) (R x) (R y) := by
    clear hx hy
    induction h with
    | rel a b hab =>
      obtain ⟨f, hf⟩ := hab
      exact hR_weq f hf
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have hxR := trivFib_of_weq hx (hR_fib x) (r x) (hr_mem x).2
  have hyR := trivFib_of_weq hy (hR_fib y) (r y) (hr_mem y).2
  exact Relation.EqvGen.trans x (R x) y hxR
    (Relation.EqvGen.trans (R x) (R y) y hxy (Relation.EqvGen.symm _ _ hyR))

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
retract of `(M, (d_I)/tFib)`.

`C` is turned into an ep metric space by the respective
distance, through `PseudoEMetricSpace.ofEdist`-style structures; here the statement is that
`F` and `id` are distance non-increasing for the two distances and `F x ~ x`. -/
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
  have : M.str.W.IsMultiplicative := instIsMultiplicativeW M
  have : (trivialFibrations M.str).IsMultiplicative := instIsMultiplicativeTFib M
  obtain ⟨hIntT, hCompT⟩ := quotientInterleavingDist_tFib_intrinsic_complete M hpow
  obtain ⟨hFR1, hFR2, hFR3⟩ := fibrantReplacement_retract M R
  let dW := quotientInterleavingDist M.str.W
  let dT := quotientInterleavingDist (trivialFibrations M.str)
  have hdW : IsEPMetric dW := quotientInterleavingDist_isEPMetric M.str.W
  have hdT : IsEPMetric dT := quotientInterleavingDist_isEPMetric (trivialFibrations M.str)
  have hpr : IsPseudoRetract (WithDist dW hdW) (WithDist dT hdT) :=
    ⟨R.F.toFunctor.obj, id, hFR1, hFR2, fun x => by
      change dW x (R.F.toFunctor.obj x) = 0
      exact (hdW.symm x (R.F.toFunctor.obj x)).trans (hFR3 x)⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hpr.isIntrinsicEP hIntT
  · exact hpr.isCompleteEP hCompT
  · ext x y
    apply le_antisymm
    · refine le_iInf₂ fun δ hδ => ?_
      obtain ⟨x', y', hx', hy', hI⟩ := hδ
      have hEqW := weaklyEquivalent_equivalence M.str.W
      have hinv := quotientDist_isInvariant interleavingDist (WeaklyEquivalent M.str.W)
        hEqW x x' y y' (hEqW.symm hx') (hEqW.symm hy')
      rw [quotientInterleavingDist, quotientInterleavingDistOf, hinv]
      exact (quotientDist_le interleavingDist (WeaklyEquivalent M.str.W) x' y').trans
        (iInf₂_le δ hI)
    · have h1 : homotopyInterleavingDist M.str.W x y ≤ dT (R.F.toFunctor.obj x) (R.F.toFunctor.obj y) := by
        dsimp [dT]
        rw [quotientInterleavingDist_tFib M hpow]
        refine le_iInf₂ fun δ hδ => ?_
        obtain ⟨x', y', hx', hy', hI⟩ := hδ
        have hEqW := weaklyEquivalent_equivalence M.str.W
        have htFib_le_W : ∀ a b, WeaklyEquivalent (trivialFibrations M.str) a b →
            WeaklyEquivalent M.str.W a b := fun a b hab => by
          induction hab with
          | rel u v huv => obtain ⟨f, hf⟩ := huv; exact Relation.EqvGen.rel u v ⟨f, hf.2⟩
          | refl u => exact hEqW.refl u
          | symm u v _ ih => exact hEqW.symm ih
          | trans u v w _ _ ih1 ih2 => exact hEqW.trans ih1 ih2
        have hxR : WeaklyEquivalent M.str.W (R.F.toFunctor.obj x) x :=
          hEqW.symm (Relation.EqvGen.rel x (R.F.toFunctor.obj x) ⟨R.η.app x, R.weq x⟩)
        have hyR : WeaklyEquivalent M.str.W (R.F.toFunctor.obj y) y :=
          hEqW.symm (Relation.EqvGen.rel y (R.F.toFunctor.obj y) ⟨R.η.app y, R.weq y⟩)
        exact iInf₂_le_of_le δ ⟨x', y', hEqW.trans (htFib_le_W _ _ hx') hxR,
          hEqW.trans (htFib_le_W _ _ hy') hyR, hI⟩ le_rfl
      exact h1.trans (hFR1 x y)

/-- Theorem 6.1.7: for `M` cofibrantly generated, the quotient interleaving distance of
`M^ℝ` (projective model structure `N`, with the locally persistent structure of persistent
objects) is intrinsic, complete, and equals the homotopy interleaving distance. -/
theorem homotopyInterleavingDist_persistent {C : Type u} [Category.{v} C]
    (M : ModelCategory C) (_hM : IsCofibrantlyGenerated M.str)
    (N : ModelStructure (ℝ ⥤ C)) (hN : IsProjectiveModelStructure M.str N) :
    @IsIntrinsicDist (ℝ ⥤ C)
        (@quotientInterleavingDist (ℝ ⥤ C) _ (persistentLPCat C) N.W) ∧
      @IsCompleteDist (ℝ ⥤ C)
        (@quotientInterleavingDist (ℝ ⥤ C) _ (persistentLPCat C) N.W) ∧
      @quotientInterleavingDist (ℝ ⥤ C) _ (persistentLPCat C) N.W =
        @homotopyInterleavingDist (ℝ ⥤ C) _ (persistentLPCat C) N.W := by
  letI : HasLimits C := M.hasLimits
  letI : HasColimits C := M.hasColimits
  letI : LPCat (ℝ ⥤ C) := persistentLPCat C
  letI : PoweredByRepresentables (ℝ ⥤ C) := persistentPowered C
  letI : CopoweredByRepresentables (ℝ ⥤ C) := persistentCopowered C
  let M' : ModelCategory (ℝ ⥤ C) := ⟨inferInstance, inferInstance, N⟩
  have hpow : PowersPreserveTrivialFibrations N := by
    intro ε X Y f hf
    have hf' : (projectiveFibrations M.str.Fib) f ∧ (projectiveWeakEquivalences M.str.W) f := by
      rwa [← hN.Fib_eq, ← hN.W_eq]
    refine ⟨?_, ?_⟩
    · rw [hN.Fib_eq]; intro r; exact hf'.1 _
    · rw [hN.W_eq]; intro r; exact hf'.2 _
  let termArrow : C ⥤ CategoryTheory.Arrow C :=
    { obj := fun X => CategoryTheory.Arrow.mk (terminal.from X)
      map := fun {X Y} f => CategoryTheory.Arrow.homMk f (𝟙 (⊤_ C)) (terminal.hom_ext _ _) }
  let R₀ : C ⥤ C := termArrow ⋙ M.str.wfs₂.mid
  let η₀ : 𝟭 C ⟶ R₀ :=
    { app := fun X => M.str.wfs₂.ι.app (termArrow.obj X)
      naturality := fun {X Y} f => M.str.wfs₂.ι.naturality (termArrow.map f) }
  let RFun : LPFunctor (ℝ ⥤ C) (ℝ ⥤ C) :=
    { toFunctor := (Functor.whiskeringRight ℝ C C).obj R₀
      map := fun {X Y ε} α =>
        { app := fun r => R₀.map (α.app r)
          naturality := fun {r s} h => by
            change R₀.map (X.map h) ≫ R₀.map (α.app s) =
              R₀.map (α.app r) ≫ R₀.map ((shift (↑ε) Y).map h)
            rw [← R₀.map_comp, ← R₀.map_comp]
            exact congrArg R₀.map (α.naturality h) }
      map_zero := fun {X Y} f => by
        apply NatTrans.ext; funext r
        erw [PersistentObjects.toZero_app (hr := by simp)]
        change R₀.map (f.app r ≫ Y.map (homOfLE (by simp))) =
          R₀.map (f.app r) ≫ R₀.map (Y.map (homOfLE (by simp)))
        exact R₀.map_comp _ _
      map_comp := fun {X Y Z ε δ} g f => by
        apply NatTrans.ext; funext r
        change R₀.map (g.app r ≫ f.app (↑ε + r) ≫ Z.map (homOfLE (by simp [addLeft]; linarith))) =
          R₀.map (g.app r) ≫ R₀.map (f.app (↑ε + r)) ≫
            R₀.map (Z.map (homOfLE (by simp [addLeft]; linarith)))
        rw [R₀.map_comp]
        congr 1
        exact R₀.map_comp _ _
      map_S := fun {X Y ε δ} h f => by
        apply NatTrans.ext; funext r
        erw [PersistentObjects.shiftR_app]
        change R₀.map (f.app r ≫ Y.map _) = R₀.map (f.app r) ≫ R₀.map (Y.map _)
        exact R₀.map_comp _ _ }
  let R : LPFibrantReplacement N :=
    { F := RFun
      η :=
        { app := fun X => Functor.whiskerLeft X η₀
          naturality := fun {X Y} α => by
            ext r
            exact η₀.naturality (α.app r) }
      weq := fun X => by
        rw [hN.W_eq]
        intro r
        have hmem : (M.str.Cof ⊓ M.str.W) (η₀.app (X.obj r)) := by
          rw [← M.str.wfs₂_L]
          exact M.str.wfs₂.ι_mem (termArrow.obj (X.obj r))
        simpa using hmem.2
      fibrant := fun X T t ht => by
        rw [hN.Fib_eq]
        intro r
        have hp : M.str.Fib (M.str.wfs₂.π.app (termArrow.obj (X.obj r))) := by
          rw [← M.str.wfs₂_R]
          exact M.str.wfs₂.π_mem (termArrow.obj (X.obj r))
        have hT_r : IsTerminal (T.obj r) :=
          let lim := isLimitOfPreserves ((evaluation ℝ C).obj r) ht
          IsTerminal.ofUniqueHom
            (fun Y => lim.lift ⟨Y, fun j => j.as.elim, fun {j} => j.as.elim⟩)
            (fun Y m => lim.uniq ⟨Y, fun j => j.as.elim, fun {j} => j.as.elim⟩ m
              (fun j => j.as.elim))
        let iso : ⊤_ C ≅ T.obj r := terminalIsTerminal.uniqueUpToIso hT_r
        have ht_eq : t.app r = M.str.wfs₂.π.app (termArrow.obj (X.obj r)) ≫ iso.hom :=
          hT_r.hom_ext _ _
        rw [ht_eq]
        have hFib_eq : M.str.Fib = M.str.wfs₂.L.rlp := by
          rw [← M.str.wfs₂_R, M.str.wfs₂.R_eq]
        haveI : M.str.Fib.RespectsIso := by rw [hFib_eq]; infer_instance
        exact MorphismProperty.RespectsIso.postcomp M.str.Fib iso.hom _ hp }
  exact homotopyInterleavingDist_intrinsic_complete M' hpow R

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

Definitions and proofs for the persistent dissimilarity constructions. -/

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

Adds `0 ≤ r` alongside `X.d x y ≤ ENNReal.ofReal r`: writing
`X.d x y ≤ ENNReal.ofReal r` alone is wrong for `r < 0` because `ENNReal.ofReal r = 0`, so
distance-zero subsets would be simplices at negative scales, whereas in the thesis
(`d(x, y) ≤ r` with `d ≥ 0`) the complex is empty for `r < 0` (making Lemma 6.3.2 hold). Also
defines `VR` directly on `Diss` (the source states Definition 6.3.1 for metric spaces and
immediately extends it to `Diss`). -/
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
morphisms of dissimilarity spaces to weak equivalences, at every scale.

Parameterizes over an abstract realization functor `real : SCpx ⥤ TopCat`, a
morphism property `Wtop`, and the conclusion of Lemma 6.3.3 (`RealizationInvertsFullSurjections`),
and states the result levelwise in `Wtop` rather than as acyclic morphisms of `Top^ℝ`. -/
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
Gromov–Hausdorff distance and the homotopy interleaving distance.

Parameterizes over `real : SCpx ⥤ TopCat`, `Wtop` (satisfying `Wtop.IsMultiplicative`
and `RespectsIso`), a `HomotopyInterleavingData` / model structure witness, and Lemma 6.3.3 as
`RealizationInvertsFullSurjections real Wtop` instead of specializing to standard geometric
realization and singular weak homotopy equivalences. -/
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
of acyclic covers.

Specializes the locally `(ℝ≥0 × ℝ≥0)`-persistent structure from an arbitrary `LR` to
`persistentLQPCat Diss.{u}` so `persistent_quotient_dist` applies. -/
theorem ghInterleaving_spec (v : ℝ≥0 × ℝ≥0)
    (L : LPCat (ℝ ⥤ Diss.{u})) (hL : IsChangeOfEnrichment (pairFamily v) (persistentLQPCat Diss.{u}) L) :
    @IsIntrinsicDist (ℝ ⥤ Diss.{u}) (@quotientInterleavingDist _ _ L acyclicPersistentDiss) ∧
    @IsCompleteDist (ℝ ⥤ Diss.{u}) (@quotientInterleavingDist _ _ L acyclicPersistentDiss) ∧
    ∀ X Y : ℝ ⥤ Diss.{u}, @quotientInterleavingDist _ _ L acyclicPersistentDiss X Y =
      ⨅ (δ : ℝ≥0) (_ : ∃ (X' Y' : ℝ ⥤ Diss.{u}) (a : X' ⟶ X) (b : Y' ⟶ Y),
        acyclicPersistentDiss a ∧ acyclicPersistentDiss b ∧ @IsInterleaved _ _ L X' Y' δ),
        (δ : ℝ≥0∞) :=
  persistent_quotient_dist (C := Diss.{u}) acyclicDiss Diss.powered
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    hpow_acyclicDiss Diss.isClosedUnderSequentialLimits_acyclicDiss v L hL

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

/-- Fixed labels with dissimilarities and real birth values, used to repair Theorem 6.4.6. -/
structure FilteredDiss where
  carrier : Type u
  d : carrier → carrier → ℝ≥0∞
  birth : carrier → ℝ

/-- An approximate map increases distances and birth values by at most its grade. -/
abbrev FilteredDissHom (X Y : FilteredDiss.{u}) (ε : ℝ≥0) :=
  {f : X.carrier → Y.carrier //
    (∀ x y, Y.d (f x) (f y) ≤ X.d x y + ε) ∧
    ∀ x, Y.birth (f x) ≤ X.birth x + ε}

/-- Composition adds both errors in the corrected category for Theorem 6.4.6. -/
def fdComp {X Y Z : FilteredDiss.{u}} {ε δ : ℝ≥0}
    (g : FilteredDissHom Y Z δ) (f : FilteredDissHom X Y ε) : FilteredDissHom X Z (ε + δ) :=
  ⟨g.1 ∘ f.1, fun x y => (g.2.1 _ _).trans (by
    calc Y.d (f.1 x) (f.1 y) + δ ≤ (X.d x y + ε) + δ := add_le_add (f.2.1 _ _) le_rfl
         _ = _ := by simp [ENNReal.coe_add, add_assoc]),
    fun x => (g.2.2 _).trans (by
      have h := f.2.2 x
      push_cast
      linarith)⟩

instance : Category.{u} FilteredDiss.{u} where
  Hom X Y := FilteredDissHom X Y 0
  id X := ⟨id, by constructor <;> intros <;> simp⟩
  comp f g := ⟨g.1 ∘ f.1, by
    constructor
    · intro x y
      simpa using (g.2.1 (f.1 x) (f.1 y)).trans (by simpa using f.2.1 x y)
    · intro x
      have hf := f.2.2 x
      have hg := g.2.2 (f.1 x)
      simp only [NNReal.coe_zero, add_zero] at hf hg ⊢
      exact hg.trans hf⟩

instance : LPCat FilteredDiss.{u} where
  hom := FilteredDissHom
  homZero := Equiv.refl _
  comp := fdComp
  S h f := ⟨f.1, (fun x y => (f.2.1 x y).trans (add_le_add le_rfl (ENNReal.coe_le_coe.mpr h))),
    fun x => (f.2.2 x).trans (by exact add_le_add le_rfl (by exact_mod_cast h))⟩
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl
  S_refl := fun _ => rfl
  S_trans := fun _ _ _ => rfl
  comp_S := fun _ _ _ _ => rfl
  homZero_comp := fun _ _ => rfl

/-- Acyclic maps preserve distances and births exactly and are surjective. -/
def acyclicFilteredDiss : MorphismProperty FilteredDiss.{u} := fun X Y f =>
  Function.Surjective f.1 ∧ (∀ x y, Y.d (f.1 x) (f.1 y) = X.d x y) ∧
  ∀ x, Y.birth (f.1 x) = X.birth x

instance : acyclicFilteredDiss.{u}.IsMultiplicative where
  id_mem _ := ⟨Function.surjective_id, fun _ _ => rfl, fun _ => rfl⟩
  comp_mem f g hf hg := ⟨hg.1.comp hf.1, fun x y => (hg.2.1 _ _).trans (hf.2.1 _ _),
    fun x => (hg.2.2 _).trans (hf.2.2 _)⟩

/-- Commutativity is equality of underlying functions in the corrected category. -/
lemma fdCommutes {X Y Z : FilteredDiss.{u}} {ε δ γ : ℝ≥0}
    (f : hom X Y ε) (g : hom Y Z δ) (h : hom X Z γ) :
    Commutes f g h ↔ ∀ x, g.1 (f.1 x) = h.1 x := by
  constructor
  · intro hh x
    exact (congrFun (congrArg Subtype.val hh) x).symm
  · intro hh
    exact Subtype.ext (funext (fun x => (hh x).symm))

/-- A commuting square is an equality of functions, used for Theorem 6.4.6. -/
lemma fdSquare {X Y Z V : FilteredDiss.{u}} {ε δ ε' δ' : ℝ≥0}
    (f : hom X Y ε) (g : hom Y V δ) (f' : hom X Z ε') (g' : hom Z V δ') :
    SqCommutes f g f' g' ↔ ∀ x, g.1 (f.1 x) = g'.1 (f'.1 x) := by
  constructor
  · intro hh x
    exact congrFun (congrArg Subtype.val hh) x
  · intro hh
    exact Subtype.ext (funext hh)

/-- Weighted pullback for the category used in the repair of Theorem 6.4.6. -/
noncomputable def fdPullback {A B C : FilteredDiss.{u}} {ε : ℝ≥0}
    (h : hom A C ε) (k : B ⟶ C) : WeightedPullback h k := by
  let P : FilteredDiss.{u} :=
    { carrier := {p : A.carrier × B.carrier // h.1 p.1 = k.1 p.2}
      d p q := max (A.d p.1.1 q.1.1) (B.d p.1.2 q.1.2 - ε)
      birth p := max (A.birth p.1.1) (B.birth p.1.2 - ε) }
  let j : P ⟶ A := ⟨fun p => p.1.1, by constructor <;> intros <;> simp [P]⟩
  let f : hom P B ε := ⟨fun p => p.1.2, by
    constructor
    · intro p q
      exact tsub_le_iff_right.mp (le_max_right _ _)
    · intro p
      have hh : B.birth p.1.2 - ε ≤ P.birth p := le_max_right _ _
      linarith⟩
  refine ⟨P, j, f, (fdSquare _ _ _ _).mpr (fun p => p.2.symm), ?_⟩
  intro V γ j' f' hs
  have hs' := (fdSquare _ _ _ _).mp hs
  let l : hom V P γ := ⟨fun x => ⟨(j'.1 x, f'.1 x), (hs' x).symm⟩, by
    constructor
    · intro x y
      refine max_le (j'.2.1 _ _) (tsub_le_iff_right.mpr ?_)
      have hh := f'.2.1 x y
      simpa [ENNReal.coe_add, add_assoc, add_comm, add_left_comm] using hh
    · intro x
      refine max_le (j'.2.2 x) ?_
      have hh := f'.2.2 x
      push_cast at hh
      linarith⟩
  refine ⟨l, ⟨(fdCommutes _ _ _).mpr (fun _ => rfl),
    (fdCommutes _ _ _).mpr (fun _ => rfl)⟩, ?_⟩
  intro m hm
  apply Subtype.ext
  funext x
  apply Subtype.ext
  exact Prod.ext ((fdCommutes _ _ _).mp hm.1 x) ((fdCommutes _ _ _).mp hm.2 x)

/-- The canonical weighted pullback preserves acyclic maps for Theorem 6.4.6. -/
lemma fdPullback_acyclic {A B C : FilteredDiss.{u}} {ε : ℝ≥0}
    (h : hom A C ε) (k : B ⟶ C) (hk : acyclicFilteredDiss k) :
    acyclicFilteredDiss (fdPullback h k).j := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨b, hb⟩ := hk.1 (h.1 a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  · intro p q
    change A.d p.1.1 q.1.1 = max _ _
    apply (max_eq_left _).symm
    apply tsub_le_iff_right.mpr
    rw [← hk.2.1 p.1.2 q.1.2, ← p.2, ← q.2]
    exact h.2.1 _ _
  · intro p
    change A.birth p.1.1 = max _ _
    apply (max_eq_left _).symm
    have hh := h.2.2 p.1.1
    rw [← hk.2.2 p.1.2, ← p.2]
    linarith

/-- Acyclic maps are stable under all weighted pullbacks, enabling the cover formula. -/
lemma fdAcyclic_stable : IsStableUnderWeightedPullbacks acyclicFilteredDiss.{u} := by
  intro A B C ε h k hk
  let P := fdPullback h k
  have hp : acyclicFilteredDiss P.j := fdPullback_acyclic h k hk
  refine ⟨⟨P⟩, fun Q => ?_⟩
  let u : hom Q.p P.p 0 := ⟨fun x => ⟨(Q.j.1 x, Q.f.1 x),
    ((fdSquare _ _ _ _).mp Q.comm x).symm⟩, by
    constructor
    · intro x y
      refine max_le (by simpa using Q.j.2.1 x y) (tsub_le_iff_right.mpr ?_)
      simpa [add_comm] using Q.f.2.1 x y
    · intro x
      refine max_le (by simpa using Q.j.2.2 x) ?_
      have hh := Q.f.2.2 x
      simp only [ENNReal.coe_zero, add_zero]
      linarith⟩
  obtain ⟨v, hv, hv_unique⟩ := Q.univ P.p 0 (homZero P.j)
    (S (le_of_eq (add_zero ε).symm) P.f) ((fdSquare _ _ _ _).mpr (fun p => p.2.symm))
  have hvj := (fdCommutes _ _ _).mp hv.1
  have hvf := (fdCommutes _ _ _).mp hv.2
  obtain ⟨w, hw, huniq⟩ := Q.univ Q.p 0 (homZero Q.j)
    (S (le_of_eq (add_zero ε).symm) Q.f) ((fdSquare _ _ _ _).mpr
      ((fdSquare Q.f (homZero k) (homZero Q.j) h).mp Q.comm))
  let vu : hom Q.p Q.p 0 := S (le_of_eq (add_zero 0)) (comp v u)
  have hcomp : vu = w := huniq vu ⟨
    (fdCommutes _ _ _).mpr (fun x => hvj (u.1 x)),
    (fdCommutes _ _ _).mpr (fun x => hvf (u.1 x))⟩
  have hid : idHom Q.p = w := huniq (idHom Q.p) ⟨
    (fdCommutes _ _ _).mpr (fun _ => rfl), (fdCommutes _ _ _).mpr (fun _ => rfl)⟩
  have hvu : ∀ x, v.1 (u.1 x) = x := fun x =>
    congrFun (congrArg Subtype.val (hcomp.trans hid.symm)) x
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨p, hpa⟩ := hp.1 a
    exact ⟨v.1 p, (hvj p).trans hpa⟩
  · intro x y
    refine le_antisymm (by simpa using Q.j.2.1 x y) ?_
    have hh := v.2.1 (u.1 x) (u.1 y)
    rw [hvu x, hvu y, ← hp.2.1 (u.1 x) (u.1 y)] at hh
    change Q.p.d x y ≤ A.d (Q.j.1 x) (Q.j.1 y) + (0 : ℝ≥0) at hh
    simpa using hh
  · intro x
    refine le_antisymm (by simpa using Q.j.2.2 x) ?_
    have hh := v.2.2 (u.1 x)
    rw [hvu x, ← hp.2.2 (u.1 x)] at hh
    change Q.p.birth x ≤ A.birth (Q.j.1 x) + (0 : ℝ≥0) at hh
    simpa using hh

/-- Interleavings are bijections controlling spatial distortion and birth differences. -/
lemma FilteredDiss.interleaved_iff (X Y : FilteredDiss.{u}) (δ : ℝ≥0) :
    IsInterleaved X Y δ ↔ ∃ e : X.carrier ≃ Y.carrier,
      (∀ x x', (X.d x x' - Y.d (e x) (e x')) ⊔ (Y.d (e x) (e x') - X.d x x') ≤ δ) ∧
      ∀ x, ENNReal.ofReal |X.birth x - Y.birth (e x)| ≤ δ := by
  constructor
  · rintro ⟨⟨f, g, hfg, hgf⟩⟩
    have hl : ∀ x, g.1 (f.1 x) = x := fun x => congrFun (congrArg Subtype.val hfg) x
    have hr : ∀ y, f.1 (g.1 y) = y := fun y => congrFun (congrArg Subtype.val hgf) y
    refine ⟨⟨f.1, g.1, hl, hr⟩, ?_, ?_⟩
    · intro x x'
      refine sup_le ?_ ?_
      · change X.d x x' - Y.d (f.1 x) (f.1 x') ≤ (δ : ℝ≥0∞)
        apply tsub_le_iff_right.mpr
        simpa only [hl, add_comm] using g.2.1 (f.1 x) (f.1 x')
      · change Y.d (f.1 x) (f.1 x') - X.d x x' ≤ (δ : ℝ≥0∞)
        apply tsub_le_iff_right.mpr
        simpa only [add_comm] using f.2.1 x x'
    · intro x
      have hf := f.2.2 x
      have hg := g.2.2 (f.1 x)
      rw [hl] at hg
      have hh : |X.birth x - Y.birth (f.1 x)| ≤ (δ : ℝ) :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      exact (ENNReal.ofReal_le_ofReal hh).trans_eq ENNReal.ofReal_coe_nnreal
  · rintro ⟨e, hd, hb⟩
    have hbr : ∀ x, |X.birth x - Y.birth (e x)| ≤ (δ : ℝ) := by
      intro x
      have hh := ENNReal.toReal_mono ENNReal.coe_ne_top (hb x)
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.coe_toReal] using hh
    let f : hom X Y δ := ⟨e, fun x x' => by
      have hh := tsub_le_iff_right.mp (le_sup_right.trans (hd x x'))
      simpa [add_comm] using hh,
      fun x => by have hh := (abs_le.mp (hbr x)).1; linarith⟩
    let g : hom Y X δ := ⟨e.symm, fun y y' => by
      have hh := tsub_le_iff_right.mp (le_sup_left.trans (hd (e.symm y) (e.symm y')))
      simpa [add_comm] using hh,
      fun y => by have hh := (abs_le.mp (hbr (e.symm y))).2; simpa using (by linarith :
        X.birth (e.symm y) ≤ Y.birth (e (e.symm y)) + (δ : ℝ))⟩
    refine ⟨⟨f, g, ?_, ?_⟩⟩
    · exact Subtype.ext (funext e.symm_apply_apply)
    · exact Subtype.ext (funext e.apply_symm_apply)

/-- Embed finite filtered metric spaces using their original labels and birth values. -/
def FFMet.toFilteredDiss (X : FFMet) : FilteredDiss.{0} :=
  ⟨X.carrier, fun x y => edist x y, X.f⟩

/-- **Theorem 6.4.6 (corrected category).** The quotient interleaving distance on
filtered dissimilarity spaces equals the filtered correspondence distortion distance.

**Gap (error).** The printed equality for arbitrary dissimilarity-valued diagrams is
false: a levelwise acyclic cover can introduce late distance-zero copies of an early
point. For a two-point space at distance 1 with births 0 and 10, and a singleton born
at 0, the correspondence distance is 10 but the original quotient distance is at most 1.
Lean replaces the ambient diagram category by `FilteredDiss`, with fixed labels
and birth values, and requires acyclic maps to preserve births as well as distances
exactly (approximate maps allow the same error in births and distances); completeness of
the new category is not asserted. See
[`6-4-6-filtered-distance-counterexample.md`](6-4-6-filtered-distance-counterexample.md). -/
theorem ghInterleaving_eq_filteredDist (X Y : FFMet) :
    quotientInterleavingDist acyclicFilteredDiss X.toFilteredDiss Y.toFilteredDiss = FFMet.dist X Y := by
  rw [quotientInterleavingDist_eq_inf_acyclicCover fdAcyclic_stable]
  unfold FFMet.dist
  apply le_antisymm
  · refine le_iInf₂ fun R hR => ?_
    by_cases hD : FFMet.filteredDistortion R = ⊤
    · rw [hD]; exact le_top
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ≥0, FFMet.filteredDistortion R = δ :=
      ⟨_, (ENNReal.coe_toNNReal hD).symm⟩
    rw [hδ]
    let X' : FilteredDiss.{0} := ⟨R, fun p q => edist p.1.1 q.1.1, fun p => X.f p.1.1⟩
    let Y' : FilteredDiss.{0} := ⟨R, fun p q => edist p.1.2 q.1.2, fun p => Y.f p.1.2⟩
    let a : X' ⟶ X.toFilteredDiss := ⟨fun p => p.1.1, by constructor <;> intros <;> simp [X', FFMet.toFilteredDiss]⟩
    let b : Y' ⟶ Y.toFilteredDiss := ⟨fun p => p.1.2, by constructor <;> intros <;> simp [Y', FFMet.toFilteredDiss]⟩
    refine iInf₂_le_of_le δ ⟨X', Y', a, b, ⟨?_, fun _ _ => rfl, fun _ => rfl⟩,
      ⟨?_, fun _ _ => rfl, fun _ => rfl⟩, ?_⟩ le_rfl
    · intro x; obtain ⟨y, hy⟩ := hR.1 x; exact ⟨⟨(x,y), hy⟩, rfl⟩
    · intro y; obtain ⟨x, hx⟩ := hR.2 y; exact ⟨⟨(x,y), hx⟩, rfl⟩
    · apply (FilteredDiss.interleaved_iff X' Y' δ).mpr
      refine ⟨Equiv.refl _, ?_, ?_⟩
      · intro p q
        have h1 := le_iSup₂ (f := fun (p : X.carrier × Y.carrier) (_ : p ∈ R) =>
          ⨆ (q : X.carrier × Y.carrier) (_ : q ∈ R),
            (edist p.1 q.1 - edist p.2 q.2) ⊔ (edist p.2 q.2 - edist p.1 q.1)) p.1 p.2
        have h2 := (le_iSup₂ (f := fun (q : X.carrier × Y.carrier) (_ : q ∈ R) =>
          (edist p.1.1 q.1 - edist p.1.2 q.2) ⊔ (edist p.1.2 q.2 - edist p.1.1 q.1)) q.1 q.2).trans h1
        rw [FFMet.filteredDistortion] at hδ
        exact h2.trans ((le_max_left _ _).trans hδ.le)
      · intro p
        have hh := le_iSup₂ (f := fun (p : X.carrier × Y.carrier) (_ : p ∈ R) =>
          ENNReal.ofReal |X.f p.1 - Y.f p.2|) p.1 p.2
        rw [FFMet.filteredDistortion] at hδ
        exact hh.trans ((le_max_right _ _).trans hδ.le)
  · refine le_iInf₂ fun δ ⟨X', Y', a, b, ha, hb, hI⟩ => ?_
    obtain ⟨e, hd, hbirth⟩ := (FilteredDiss.interleaved_iff X' Y' δ).mp hI
    let R : Set (X.carrier × Y.carrier) := {p | ∃ x', a.1 x' = p.1 ∧ b.1 (e x') = p.2}
    have hRc : (∀ x, ∃ y, (x,y) ∈ R) ∧ ∀ y, ∃ x, (x,y) ∈ R := by
      constructor
      · intro x
        obtain ⟨x', hx'⟩ := ha.1 x
        exact ⟨b.1 (e x'), x', hx', rfl⟩
      · intro y
        obtain ⟨y', hy'⟩ := hb.1 y
        exact ⟨a.1 (e.symm y'), e.symm y', rfl, by simpa using hy'⟩
    refine iInf₂_le_of_le R hRc ?_
    unfold FFMet.filteredDistortion
    apply max_le
    · refine iSup₂_le fun p hp => iSup₂_le fun q hq => ?_
      rcases p with ⟨p1,p2⟩
      rcases q with ⟨q1,q2⟩
      obtain ⟨x, rfl, rfl⟩ := hp
      obtain ⟨z, rfl, rfl⟩ := hq
      change (X.toFilteredDiss.d (a.1 x) (a.1 z) - Y.toFilteredDiss.d (b.1 (e x)) (b.1 (e z))) ⊔
        (Y.toFilteredDiss.d (b.1 (e x)) (b.1 (e z)) - X.toFilteredDiss.d (a.1 x) (a.1 z)) ≤ δ
      rw [ha.2.1, hb.2.1]
      exact hd x z
    · refine iSup₂_le fun p hp => ?_
      rcases p with ⟨p1,p2⟩
      obtain ⟨x, rfl, rfl⟩ := hp
      change ENNReal.ofReal |X.toFilteredDiss.birth (a.1 x) - Y.toFilteredDiss.birth (b.1 (e x))| ≤ δ
      rw [ha.2.2, hb.2.2]
      exact hbirth x

/-! #### 6.4.3 Stability of the parametrized Vietoris–Rips filtration -/

/-- Theorem 6.4.7: applying `|VR|` levelwise, `Diss^ℝ_v → (Top^ℝ)^ℝ_v`, is 1-Lipschitz for the
Gromov–Hausdorff-interleaving distance and the quotient interleaving distance of bi-persistent
topological spaces (levelwise weak equivalences).

Adds `v : ℝ≥0 × ℝ≥0` and hypotheses `hL₁`, `hL₂` witnessing that the `LPCat`
structures on `ℝ ⥤ Diss` and `ℝ ⥤ (ℝ ⥤ TopCat)` arise by change of enrichment along `pairFamily v`
from `persistentLQPCat` (using `persistentLPCat TopCat` on `ℝ ⥤ TopCat`), instead of unrelated
arbitrary `LPCat` instances; also parameterizes over `real : SCpx ⥤ TopCat`, `Wtop`, and
`hreal : RealizationInvertsFullSurjections real Wtop` as in Theorem 6.3.5. -/
theorem vrStar_lipschitz (real : SCpx.{u} ⥤ TopCat.{u}) (Wtop : MorphismProperty TopCat.{u})
    (h : RealizationInvertsFullSurjections real Wtop) (v : ℝ≥0 × ℝ≥0)
    [L₁ : LPCat (ℝ ⥤ Diss.{u})]
    [L₂ : LPCat (ℝ ⥤ (ℝ ⥤ TopCat.{u}))]
    (hL₁ : IsChangeOfEnrichment (pairFamily v) (persistentLQPCat Diss.{u}) L₁)
    (hL₂ : IsChangeOfEnrichment (pairFamily v)
      (@persistentLQPCat (ℝ ⥤ TopCat.{u}) _ (persistentLPCat TopCat.{u})) L₂) :
    ∃ Φ : LPFunctor (ℝ ⥤ Diss.{u}) (ℝ ⥤ (ℝ ⥤ TopCat.{u})),
      Φ.toFunctor = (Functor.whiskeringRight ℝ Diss.{u} (ℝ ⥤ TopCat.{u})).obj (vrTop real) ∧
      ∀ X Y : ℝ ⥤ Diss.{u},
        quotientInterleavingDist (levelwiseProp (levelwiseProp Wtop)) (Φ.toFunctor.obj X)
          (Φ.toFunctor.obj Y) ≤ quotientInterleavingDist acyclicPersistentDiss X Y := by
  letI : LPCat (ℝ ⥤ TopCat.{u}) := persistentLPCat TopCat.{u}
  obtain ⟨F, hF_eq, _⟩ := vr_lipschitz real Wtop h
  let LQ₁ := persistentLQPCat Diss.{u}
  let LQ₂ := persistentLQPCat (ℝ ⥤ TopCat.{u})
  obtain ⟨e₁, hz₁, hc₁, hs₁⟩ := hL₁
  obtain ⟨e₂, hz₂, hc₂, hs₂⟩ := hL₂
  let mapPH : ∀ {X Y : ℝ ⥤ Diss.{u}} {a b : ℝ≥0},
      PersistentHom X Y a b → PersistentHom (X ⋙ F.toFunctor) (Y ⋙ F.toFunctor) a b :=
    fun {X Y a b} α =>
      ⟨fun r => F.map (α.1 r), fun r s hrs => by
        have hnat := congrArg F.map (α.2 r s hrs)
        rw [F.map_S, F.map_S, F.map_comp, F.map_comp, F.map_zero, F.map_zero] at hnat
        exact hnat⟩
  have cast_symm_eq : ∀ {α β : Type _} (he : α = β) {x : β} {y : α},
      cast he.symm x = y ↔ x = cast he y := by
    intro α β he x y; subst he; rfl
  have mapPH_S : ∀ {X Y : ℝ ⥤ Diss.{u}} {a₁ a₂ b₁ b₂ : ℝ≥0} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂)
      (α : PersistentHom X Y a₁ b₁),
      mapPH (LQ₁.S (ε := (a₁, b₁)) (δ := (a₂, b₂)) ⟨ha, hb⟩ α) =
        LQ₂.S (ε := (a₁, b₁)) (δ := (a₂, b₂)) ⟨ha, hb⟩ (mapPH α) := by
    intro X Y a₁ a₂ b₁ b₂ ha hb α
    apply Subtype.ext; funext r
    dsimp only [LQ₁, LQ₂, persistentLQPCat, pSH, pS, mapPH]
    erw [F.map_S, F.map_comp, F.map_zero]
    rfl
  let Φ : LPFunctor (ℝ ⥤ Diss.{u}) (ℝ ⥤ (ℝ ⥤ TopCat.{u})) :=
    { toFunctor := (Functor.whiskeringRight ℝ Diss.{u} (ℝ ⥤ TopCat.{u})).obj F.toFunctor
      map := fun {X Y ε} f => cast (e₂ _ _ ε).symm (mapPH (cast (e₁ X Y ε) f))
      map_zero := fun {X Y} f => by
        refine (cast_symm_eq (e₂ _ _ 0)).mpr ?_
        rw [hz₂]
        erw [congrArg mapPH (hz₁ X Y f),
          mapPH_S (le_of_eq (pairFamily v).map_zero.symm).1
            (le_of_eq (pairFamily v).map_zero.symm).2]
        congr 1
        apply Subtype.ext; funext r
        dsimp only [LQ₁, LQ₂, persistentLQPCat, pZeroH, pZero, mapPH]
        erw [F.map_zero, F.toFunctor.map_comp]
        rfl
      map_comp := fun {X Y Z ε δ} g f => by
        refine (cast_symm_eq (e₂ _ _ (ε + δ))).mpr ?_
        rw [hc₂]
        erw [congrArg mapPH (hc₁ X Y Z ε δ f g),
          mapPH_S ((pairFamily v).superadd ε δ).1 ((pairFamily v).superadd ε δ).2]
        congr 1
        apply Subtype.ext; funext r
        have hcc : ∀ {α β : Type _} (he : α = β) (x : β), cast he (cast he.symm x) = x := by
          intro α β he x; subst he; rfl
        dsimp only [mapPH]
        erw [hcc (e₂ _ _ δ), hcc (e₂ _ _ ε), F.map_S, F.map_comp, F.map_comp, F.map_zero]
        rfl
      map_S := fun {X Y ε δ} h f => by
        refine (cast_symm_eq (e₂ _ _ δ)).mpr ?_
        rw [hs₂]
        erw [congrArg mapPH (hs₁ X Y ε δ h f),
          mapPH_S ((pairFamily v).mono h).1 ((pairFamily v).mono h).2]
        congr 1
        apply Subtype.ext; funext r
        have hcc : ∀ {α β : Type _} (he : α = β) (x : β), cast he (cast he.symm x) = x := by
          intro α β he x; subst he; rfl
        dsimp only [mapPH]
        erw [hcc (e₂ _ _ ε)]
        rfl }
  refine ⟨Φ, by simp [Φ, hF_eq], fun X Y => ?_⟩
  refine quotientDist_map_le _ _ interleavingDist_isEPMetric interleavingDist_isEPMetric
    Φ.toFunctor.obj (fun a b => Φ.interleavingDist_le a b) _ _
    (weaklyEquivalent_equivalence _) (weaklyEquivalent_equivalence _) (fun a b hab => ?_) X Y
  induction hab with
  | rel a b hrel =>
    obtain ⟨α, hα⟩ := hrel
    refine Relation.EqvGen.rel _ _ ⟨Φ.toFunctor.map α, fun r q => ?_⟩
    have hvr := vr_maps_acyclic real Wtop h (α.app r) (hα r) q
    change Wtop ((F.toFunctor.map (α.app r)).app q)
    rw [hF_eq]
    exact hvr
  | refl a => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end Filtrations

end ScoccolaPhd
