import ScoccolaPhd.Chapter6Section7PersistentSets

/-!
# §6.7: completeness and geodesics for persistent sets

The metric argument in Theorem 6.7.5, using the limit construction of Proposition 6.7.4
and the compactness argument following it.
-/

universe u v w
namespace ScoccolaPhd
open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal Topology
open LPCat
set_option backward.isDefEq.respectTransparency false
attribute [local instance] rtSetLPCatStd

/-- The compactness argument used in Theorem 6.7.5. Compact closures suffice for the
inverse-limit argument: restrict each stage to the closure of the next structure-map image.
This also avoids needing a separate closed-map hypothesis on the original spaces. -/
theorem nonempty_of_relativelyCompact_rc (F : ℝ≥0 ⥤ Type w) (hF : IsRightContinuous F)
    (T : ∀ r, TopologicalSpace (F.obj r))
    (hT : ∀ r, @T2Space _ (T r))
    (hcont : ∀ {r s} (h : r ≤ s), @Continuous _ _ (T r) (T s) (F.map (homOfLE h)))
    (hcomp : ∀ {r s} (h : r < s), @IsCompact _ (T s) (closure[T s] (Set.range (F.map (homOfLE h.le)))))
    (δ : ℝ≥0) (hne : ∀ r, δ < r → Nonempty (F.obj r)) : Nonempty (F.obj δ) := by
  classical
  letI : ∀ r, TopologicalSpace (F.obj r) := T
  letI : ∀ r, T2Space (F.obj r) := hT
  let s : ℕ → ℝ≥0 := fun n => δ + ((n : ℝ≥0) + 1)⁻¹
  have hs : ∀ n, δ < s n := fun n => lt_add_of_pos_right _ (by positivity)
  have hstrict : StrictAnti s := by
    intro n m h
    apply add_lt_add_right
    exact inv_strictAnti₀ (by positivity) (by exact_mod_cast Nat.succ_lt_succ h)
  have hlim : ∀ r, δ < r → ∃ n, s n ≤ r := by
    intro r hr
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (r - δ : ℝ≥0) by
      exact_mod_cast tsub_pos_of_lt hr)
    refine ⟨n, ?_⟩
    have hh : ((n : ℝ≥0) + 1)⁻¹ ≤ r - δ := by
      rw [← NNReal.coe_le_coe]; push_cast
      rw [← one_div]; exact hn.le
    exact (show s n ≤ δ + (r - δ) by dsimp [s]; gcongr).trans_eq (add_tsub_cancel_of_le hr.le)
  let K n : Set (F.obj (s n)) := closure (Set.range (F.map (homOfLE (hstrict (Nat.lt_succ_self n)).le)))
  have hK n : IsCompact (K n) := hcomp (hstrict (Nat.lt_succ_self n))
  letI : ∀ n, CompactSpace (K n) := fun n => isCompact_iff_compactSpace.mp (hK n)
  have hneK n : Nonempty (K n) := by
    obtain ⟨x⟩ := hne (s (n + 1)) (hs _)
    exact ⟨⟨F.map (homOfLE (hstrict (Nat.lt_succ_self n)).le) x, subset_closure ⟨x, rfl⟩⟩⟩
  let f n : K (n + 1) → K n := fun p => ⟨F.map (homOfLE (hstrict (Nat.lt_succ_self n)).le) p.1, by
    apply closure_mono (s := (F.map (homOfLE (hstrict (Nat.lt_succ_self n)).le)) ''
      Set.range (F.map (homOfLE (hstrict (Nat.lt_succ_self (n + 1))).le))) ?_
      (image_closure_subset_closure_image (hcont _) ⟨p.1, p.2, rfl⟩)
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩⟩
  have hf n : Continuous (f n) :=
    ((hcont _).comp continuous_subtype_val).subtype_mk _
  obtain ⟨x, hx⟩ := exists_compatible_tower f (fun n => (hf n).isClosedMap) hneK
  have hz : ∀ n m (h : n ≤ m),
      F.map (homOfLE (hstrict.antitone h)) (x m).1 = (x n).1 := by
    intro n m h
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m h ih =>
        have hstep := congrArg Subtype.val (hx m)
        change F.map (homOfLE _) (x (m + 1)).1 = (x m).1 at hstep
        rw [← ih, ← hstep, ← types_comp_apply, ← F.map_comp]
        rfl
  exact nonempty_of_rightContinuous_seq F hF δ s hs hstrict.antitone hlim
    (fun n => (x n).1) hz

/-- Pointwise discrete coordinates for natural transformations, used in the compactness
argument of Theorem 6.7.5. -/
abbrev natPointSpace (F G : ℝ ⥤ Type u) :=
  ∀ p : Σ r, F.obj r, WithDiscreteTopology (G.obj p.1)

/-- Evaluation in pointwise discrete coordinates, used in Theorem 6.7.5. -/
def natPointVal (F G : ℝ ⥤ Type u) (f : F ⟶ G) : natPointSpace F G :=
  fun p => WithTopology.toTopology ⊥ (f.app p.1 p.2)

/-- The pointwise topology, used for the compactness argument of Theorem 6.7.5. -/
def natPointTop (F G : ℝ ⥤ Type u) : TopologicalSpace (F ⟶ G) :=
  TopologicalSpace.induced (natPointVal F G) inferInstance
attribute [local instance] natPointTop

/-- Pointwise coordinates identify a natural transformation, used in Theorem 6.7.5. -/
theorem natPointVal_injective (F G : ℝ ⥤ Type u) : Function.Injective (natPointVal F G) := by
  intro f g h
  apply NatTrans.ext; funext r
  apply ConcreteCategory.hom_ext; intro x
  exact congrArg WithTopology.ofTopology (congrFun h ⟨r, x⟩)

/-- Naturality is closed in the product of discrete coordinate spaces. This is the
compatibility condition in the compactness argument of Theorem 6.7.5. -/
theorem natPointVal_closed (F G : ℝ ⥤ Type u) :
    Topology.IsClosedEmbedding (natPointVal F G) := by
  refine ⟨⟨⟨rfl⟩, natPointVal_injective F G⟩, ?_⟩
  have he : Set.range (natPointVal F G) =
      ⋂ (r : ℝ) (s : ℝ) (h : r ≤ s) (x : F.obj r),
        {p : natPointSpace F G | p ⟨s, F.map (homOfLE h) x⟩ =
          (WithTopology.toTopology ⊥ (G.map (homOfLE h) (p ⟨r, x⟩).ofTopology) : WithDiscreteTopology (G.obj s))} := by
    ext p
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨f, rfl⟩ r s h x
      apply WithTopology.ext
      exact ConcreteCategory.congr_hom (f.naturality (homOfLE h)) x
    · intro hp
      refine ⟨{ app := fun r => TypeCat.ofHom fun x => (p ⟨r, x⟩).ofTopology
                naturality := ?_ }, ?_⟩
      · intro r s h
        apply ConcreteCategory.hom_ext; intro x
        exact congrArg WithTopology.ofTopology (hp r s (leOfHom h) x)
      · rfl
  rw [he]
  refine isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun h =>
    isClosed_iInter fun x => ?_
  have hc : Continuous (fun p : natPointSpace F G =>
      (WithTopology.toTopology ⊥ (G.map (homOfLE h) (p ⟨r, x⟩).ofTopology) :
        WithDiscreteTopology (G.obj s))) :=
    (continuous_of_discreteTopology : Continuous (fun y : WithDiscreteTopology (G.obj r) =>
      (WithTopology.toTopology ⊥ (G.map (homOfLE h) y.ofTopology) : WithDiscreteTopology (G.obj s)))).comp
      (continuous_apply (⟨r, x⟩ : Σ r, F.obj r))
  exact isClosed_eq (continuous_apply _) hc

/-- The pointwise topology is Hausdorff, used in Theorem 6.7.5. -/
instance natPointT2 (F G : ℝ ⥤ Type u) : T2Space (F ⟶ G) :=
  (natPointVal_closed F G).isEmbedding.t2Space

/-- Evaluation at a fixed point is continuous, used in Theorem 6.7.5. -/
theorem natPoint_eval (F G : ℝ ⥤ Type u) (r : ℝ) (x : F.obj r) :
    Continuous (fun f : F ⟶ G => (WithTopology.toTopology ⊥ (f.app r x) : WithDiscreteTopology (G.obj r))) :=
  (continuous_apply (⟨r, x⟩ : Σ r, F.obj r)).comp
    (show Continuous (natPointVal F G) from continuous_induced_dom)

/-- A variable evaluation at a discrete input is continuous, used for the interleaving
identities in Theorem 6.7.5. -/
theorem natPoint_eval_variable (F G : ℝ ⥤ Type u) (r : ℝ) :
    Continuous (fun p : (F ⟶ G) × WithDiscreteTopology (F.obj r) =>
      (WithTopology.toTopology ⊥ (p.1.app r p.2.ofTopology) : WithDiscreteTopology (G.obj r))) := by
  apply continuous_prod_of_discrete_right.mpr
  intro x
  exact natPoint_eval F G r x.ofTopology

/-- Structure maps on hom spaces are continuous in pointwise coordinates, used in
Theorem 6.7.5. -/
theorem natPoint_shift_continuous (F G : ℝ ⥤ Type u) {a b : ℝ} (h : a ≤ b) :
    Continuous (fun f : F ⟶ shift a G => f ≫ shiftHom h G) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro p
  exact (continuous_of_discreteTopology : Continuous
    (fun y : WithDiscreteTopology ((shift a G).obj p.1) =>
      (WithTopology.toTopology ⊥ ((shiftHom h G).app p.1 y.ofTopology) :
        WithDiscreteTopology ((shift b G).obj p.1)))).comp
          (natPoint_eval F (shift a G) p.1 p.2)

/-- After a positive shift, each coordinate belongs to a finite structure-map image.
Tychonoff's theorem supplies the compactness used in Theorem 6.7.5. -/
theorem natPoint_shift_relativelyCompact (F G : ℝ ⥤ Type u) (hG : IsQTameSet G)
    {a b : ℝ} (h : a < b) :
    IsCompact (closure (Set.range (fun f : F ⟶ shift a G => f ≫ shiftHom h.le G))) := by
  classical
  let R (p : Σ r, F.obj r) : Set (WithDiscreteTopology ((shift b G).obj p.1)) :=
    WithTopology.toTopology ⊥ '' Set.range
      (G.map (homOfLE (show a + p.1 ≤ b + p.1 by linarith)))
  have hR (p) : (R p).Finite :=
    (hG (a + p.1) (b + p.1) (by linarith)).image (WithTopology.toTopology ⊥)
  let K : Set (natPointSpace F (shift b G)) := {p | ∀ i, p i ∈ R i}
  have hK : IsCompact K := isCompact_pi_infinite (fun p => (hR p).isCompact)
  have he := natPointVal_closed F (shift b G)
  have hc : IsCompact ((natPointVal F (shift b G)) ⁻¹' K) := he.isCompact_preimage hK
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro _ ⟨f, rfl⟩ p
    exact ⟨_, ⟨f.app p.1 p.2, rfl⟩, rfl⟩
  · exact hK.isClosed.preimage he.continuous

/-- The inclusion of nonnegative real parameters, used for hom right continuity. -/
def nonnegativeInclusion : ℝ≥0 ⥤ ℝ where
  obj r := r
  map h := homOfLE (NNReal.coe_le_coe.mpr (leOfHom h))

/-- Restricting a right continuous persistent set on the reals to nonnegative parameters
preserves right continuity. Used for the hom spaces in Theorem 6.7.5. -/
theorem rightContinuous_nonnegative (F : ℝ ⥤ Type u) (hF : IsRightContinuous F) :
    IsRightContinuous (nonnegativeInclusion ⋙ F) := by
  apply rightCont_intro
  · intro r x y h
    apply rightCont_inj hF (r : ℝ)
    intro s hs
    exact h ⟨s, by linarith [r.coe_nonneg]⟩ (by exact_mod_cast hs)
  · intro r x hx
    let z (s : ℝ) (hs : (r : ℝ) < s) : F.obj s :=
      x ⟨s, by linarith [r.coe_nonneg]⟩ (by exact_mod_cast hs)
    have hz : ∀ s s' (hs : (r : ℝ) < s) (hs' : (r : ℝ) < s') (h : s ≤ s'),
        persGm F h (z s hs) = z s' hs' := by
      intro s s' hs hs' h
      exact hx ⟨s, by linarith [r.coe_nonneg]⟩ ⟨s', by linarith [r.coe_nonneg]⟩
        (by exact_mod_cast hs) (by exact_mod_cast hs') (NNReal.coe_le_coe.mp h)
    obtain ⟨y, hy⟩ := rightCont_surj hF (r : ℝ) z hz
    exact ⟨y, fun s hs => hy s (by exact_mod_cast hs)⟩

/-- The right continuity of hom spaces used in Theorem 6.7.5 is Proposition 2.6.10. -/
theorem rtHom_rightContinuous (A B : RTSet.{u}) : IsRightContinuous (homFunctor A B) := by
  have hrc := internalHom_isRightContinuous (P := ℝ) (fun a b => le_total a b)
    (fun r q s h => ⟨(r + (s - q)) / 2, by linarith, by linarith⟩)
    A.X B.X B.rightContinuous
  convert rightContinuous_nonnegative (internalHom A.X B.X) hrc using 1
  apply CategoryTheory.Functor.hext (fun _ => rfl)
  intro r s h
  apply heq_of_eq
  apply ConcreteCategory.hom_ext
  intro f
  apply NatTrans.ext; funext t
  rfl

/-- The topology on approximate maps induced by their natural transformations. -/
def rtHomTop (A B : RTSet.{u}) (ε : ℝ≥0) : TopologicalSpace (hom A B ε) :=
  natPointTop A.X (shift (ε : ℝ) B.X)
attribute [local instance] rtHomTop
instance rtHomT2 (A B : RTSet.{u}) (ε : ℝ≥0) : T2Space (hom A B ε) :=
  natPointT2 A.X (shift (ε : ℝ) B.X)

/-- Composition is continuous in the pointwise discrete topology, used in Theorem 6.7.5. -/
theorem rtHom_comp_continuous (A B C : RTSet.{u}) (ε δ : ℝ≥0) :
    Continuous (fun p : hom B C δ × hom A B ε => comp p.1 p.2) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro p
  have he := (natPoint_eval_variable B.X (shift (δ : ℝ) C.X) ((ε : ℝ) + p.1)).comp
    (continuous_fst.prodMk ((natPoint_eval A.X (shift (ε : ℝ) B.X) p.1 p.2).comp continuous_snd))
  let e : WithDiscreteTopology (C.X.obj ((δ : ℝ) + ((ε : ℝ) + p.1))) →
      WithDiscreteTopology ((shift ((ε + δ : ℝ≥0) : ℝ) C.X).obj p.1) := fun z =>
    WithTopology.toTopology ⊥ (C.X.map (homOfLE (le_of_eq (by dsimp [shift, addLeft]; push_cast; ring))) z.ofTopology)
  exact (continuous_of_discreteTopology : Continuous e).comp he

/-- The interleaving equations are closed, as in the compactness proof of Theorem 6.7.5. -/
theorem rtInterleavings_closed (A B : RTSet.{u}) (ε : ℝ≥0) :
    IsClosed {p : hom A B ε × hom B A ε | IsInterleavingPair p.1 p.2} := by
  exact (isClosed_eq ((rtHom_comp_continuous A B A ε ε).comp continuous_swap) continuous_const).inter
    (isClosed_eq (rtHom_comp_continuous B A B ε ε) continuous_const)

/-- The topology on interleavings induced by their two natural transformations. -/
def rtInterleavingTop (A B : RTSet.{u}) (ε : ℝ≥0) :
    TopologicalSpace ((interleavingFunctor A B).obj ε) :=
  TopologicalSpace.induced (fun p : (interleavingFunctor A B).obj ε => p.1) inferInstance
attribute [local instance] rtInterleavingTop

/-- Interleavings form a closed subspace of the pair of hom spaces. -/
theorem rtInterleavingVal_closed (A B : RTSet.{u}) (ε : ℝ≥0) :
    Topology.IsClosedEmbedding (fun p : (interleavingFunctor A B).obj ε => p.1) :=
  ⟨⟨⟨rfl⟩, Subtype.val_injective⟩, by
    have he : (Set.range (fun p : (interleavingFunctor A B).obj ε => p.1)) =
        {p : hom A B ε × hom B A ε | IsInterleavingPair p.1 p.2} := by
      ext p; exact ⟨fun ⟨q, hq⟩ => hq ▸ q.2, fun hp => ⟨⟨p, hp⟩, rfl⟩⟩
    rw [he]; exact rtInterleavings_closed A B ε⟩

/-- The interleaving spaces are Hausdorff. -/
instance rtInterleavingT2 (A B : RTSet.{u}) (ε : ℝ≥0) :
    T2Space ((interleavingFunctor A B).obj ε) :=
  (rtInterleavingVal_closed A B ε).isEmbedding.t2Space

/-- Shifts on interleavings are continuous. -/
theorem rtInterleaving_continuous (A B : RTSet.{u}) {ε δ : ℝ≥0} (h : ε ≤ δ) :
    Continuous ((interleavingFunctor A B).map (homOfLE h)) := by
  apply continuous_induced_rng.mpr
  exact ((natPoint_shift_continuous A.X B.X (NNReal.coe_le_coe.mpr h)).prodMap
    (natPoint_shift_continuous B.X A.X (NNReal.coe_le_coe.mpr h))).comp continuous_induced_dom

/-- Positive shifts have relatively compact image in the interleaving spaces. This is
Tychonoff compactness applied to the finite coordinate images in the proof of Theorem 6.7.5. -/
theorem rtInterleaving_relativelyCompact (A B : RTSet.{u}) {ε δ : ℝ≥0} (h : ε < δ) :
    IsCompact (closure (Set.range ((interleavingFunctor A B).map (homOfLE h.le)))) := by
  have hK := (natPoint_shift_relativelyCompact A.X B.X B.qtame (NNReal.coe_lt_coe.mpr h)).prod
    (natPoint_shift_relativelyCompact B.X A.X A.qtame (NNReal.coe_lt_coe.mpr h))
  have he := rtInterleavingVal_closed A B δ
  have hc := he.isCompact_preimage hK
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro _ ⟨p, rfl⟩
    exact ⟨subset_closure ⟨p.1.1, rfl⟩, subset_closure ⟨p.1.2, rfl⟩⟩
  · exact hK.isClosed.preimage he.continuous

/-- The reflection step of Theorem 6.7.5: compactness of smoothed hom spaces and right
continuity realize an interleaving at the exact distance. -/
theorem rtSet_reflectsInterleavings : ReflectsInterleavings RTSet.{u} := by
  intro A B δ hd
  have hrc := interleavingFunctor_rightContinuous rtHom_rightContinuous A B
  obtain ⟨p⟩ := nonempty_of_relativelyCompact_rc (interleavingFunctor A B) hrc
    (rtInterleavingTop A B) (fun ε => rtInterleavingT2 A B ε)
    (fun h => rtInterleaving_continuous A B h)
    (fun h => rtInterleaving_relativelyCompact A B h) δ (by
      intro r hr
      obtain ⟨⟨f, g, hp⟩⟩ := isInterleaved_of_dist_lt (x := A) (y := B)
        (by rw [hd]; exact_mod_cast hr)
      exact ⟨⟨(f, g), hp⟩⟩)
  exact ⟨⟨p.1.1, p.1.2, p.2⟩⟩

/-- Right continuous persistent sets, the ambient category used for the limit construction
in Proposition 6.7.4. -/
structure RCSet where
  X : ℝ ⥤ Type u
  rightContinuous : IsRightContinuous X

instance : Category.{u} RCSet.{u} where
  Hom A B := A.X ⟶ B.X
  id A := 𝟙 A.X
  comp f g := f ≫ g

/-- The locally persistent structure inherited from persistent sets, used in Proposition 6.7.4. -/
noncomputable instance rcSetLPCat : LPCat RCSet.{u} :=
  let P := persistentLPCat (Type u)
  { hom := fun A B ε => P.hom A.X B.X ε
    homZero := P.homZero
    comp := P.comp
    S := P.S
    id_comp := P.id_comp
    comp_id := P.comp_id
    assoc := P.assoc
    S_refl := P.S_refl
    S_trans := P.S_trans
    comp_S := P.comp_S
    homZero_comp := P.homZero_comp }

/-- Translations in the ambient category of Proposition 6.7.4. -/
def RCSet.shiftFunctor (a : ℝ) : RCSet.{u} ⥤ RCSet.{u} where
  obj A := ⟨shift a A.X, rightContinuous_shift A.X A.rightContinuous a⟩
  map f := shiftMap a f

/-- Powers of right continuous persistent sets, used in Proposition 6.7.4. -/
noncomputable instance rcSetPowered : PoweredByRepresentables RCSet.{u} where
  pow ε := RCSet.shiftFunctor ε
  powIso A B := (persistentPowered (Type u)).powIso A.X B.X
  powIso_S := (persistentPowered (Type u)).powIso_S
  powIso_x := (persistentPowered (Type u)).powIso_x
  powIso_y := (persistentPowered (Type u)).powIso_y

/-- Copowers of right continuous persistent sets, used in Proposition 6.7.4. -/
noncomputable instance rcSetCopowered : CopoweredByRepresentables RCSet.{u} where
  copow ε := RCSet.shiftFunctor (-(ε : ℝ))
  copowIso A B := (persistentCopowered (Type u)).copowIso A.X B.X
  copowIso_S := (persistentCopowered (Type u)).copowIso_S
  copowIso_x := (persistentCopowered (Type u)).copowIso_x
  copowIso_y := (persistentCopowered (Type u)).copowIso_y

/-- Inclusion in persistent sets, used in Proposition 6.7.4. -/
def rcSetForget : RCSet.{u} ⥤ (ℝ ⥤ Type u) where
  obj A := A.X
  map f := f

/-- The limit object in the ambient right continuous category of Proposition 6.7.4. -/
def RCSet.limitObj {J : Type} [Category J] (F : J ⥤ RCSet.{u}) : RCSet :=
  ⟨persistentSetLimit (F ⋙ rcSetForget),
    persistentSetLimit_rightContinuous _ (fun j => (F.obj j).rightContinuous)⟩

/-- The limit cone in Proposition 6.7.4. -/
def RCSet.limitCone {J : Type} [Category J] (F : J ⥤ RCSet.{u}) : Cone F where
  pt := RCSet.limitObj F
  π := {
    app := fun j => {
      app := fun _ => TypeCat.ofHom fun p => p.1 j
      naturality := by intros; rfl }
    naturality := by
      intro i j f
      apply NatTrans.ext; funext r
      apply ConcreteCategory.hom_ext; intro p
      exact (p.2 i j f).symm }

/-- Universality of the limits in Proposition 6.7.4. -/
def RCSet.limitConeIsLimit {J : Type} [Category J] (F : J ⥤ RCSet.{u}) :
    Limits.IsLimit (RCSet.limitCone F) where
  lift c := {
    app := fun r => TypeCat.ofHom fun x => ⟨fun j => (c.π.app j).app r x,
      fun i j f => ConcreteCategory.congr_hom (NatTrans.congr_app (c.w f) r) x⟩
    naturality := by
      intro r s h
      apply ConcreteCategory.hom_ext; intro x
      apply Subtype.ext
      funext j
      exact ConcreteCategory.congr_hom ((c.π.app j).naturality h) x }
  fac _ _ := rfl
  uniq c m hm := by
    apply NatTrans.ext; funext r
    apply ConcreteCategory.hom_ext; intro x
    apply Subtype.ext
    funext j
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (hm j) r) x

/-- Small limits exist in the category of Proposition 6.7.4. -/
instance rcSetHasLimitsOfShape (J : Type) [Category J] : HasLimitsOfShape J RCSet.{u} where
  has_limit F := ⟨⟨⟨RCSet.limitCone F, RCSet.limitConeIsLimit F⟩⟩⟩

/-- A structure map of a persistent set interleaved with a q-tame set factors through
one of the latter's finite-image structure maps. This is the last argument in
Proposition 6.7.4. -/
theorem qtame_structureMap_of_interleaved (X Y : RCSet.{u}) (hY : IsQTameSet Y.X)
    {ε : ℝ≥0} (hI : IsInterleaved X Y ε) (r s : ℝ) (hrs : (ε : ℝ) + ε < s - r) :
    (Set.range (X.X.map (homOfLE (show r ≤ s by linarith [ε.coe_nonneg])))).Finite := by
  obtain ⟨⟨f, g, hp, _⟩⟩ := hI
  have hab : (ε : ℝ) + r < s - ε := by linarith
  have heq : (ε : ℝ) + (s - ε) = s := by ring
  let a := (ε : ℝ) + r
  let b := s - (ε : ℝ)
  let t := ((ε + ε : ℝ≥0) : ℝ) + r
  have hrt : r ≤ t := by dsimp [t]; push_cast; linarith [ε.coe_nonneg]
  have hts : t ≤ s := by dsimp [t]; push_cast; linarith
  have hp' := NatTrans.congr_app hp r
  change (PersistentObjects.compR (((ε + ε : ℝ≥0)) : ℝ) (by push_cast; rfl) g f).app r =
    (PersistentObjects.shiftR (show (0 : ℝ) ≤ ((ε + ε : ℝ≥0) : ℝ) by positivity)
      (PersistentObjects.toZero 0 rfl (𝟙 X.X))).app r at hp'
  rw [PersistentObjects.compR_app, PersistentObjects.shiftR_app, PersistentObjects.toZero_app] at hp'
  simp only [NatTrans.id_app, Category.id_comp] at hp'
  have hp'' : f.app r ≫ g.app a ≫ PersistentObjects.mapEq X.X (by dsimp [a, t, shift, addLeft]; push_cast; ring) =
      X.X.map (homOfLE hrt) := by
    dsimp only [a, t, shift, Functor.comp_obj, addLeft] at hp' ⊢
    simp only [PersistentObjects.mapEq, ← X.X.map_comp] at hp' ⊢
    convert hp' using 1 <;> congr 1
  have hn := g.naturality (homOfLE hab.le)
  have hfac : X.X.map (homOfLE (show r ≤ s by linarith [ε.coe_nonneg])) =
      f.app r ≫ Y.X.map (homOfLE hab.le) ≫ g.app b ≫
        X.X.map (homOfLE heq.le) := by
    calc
      _ = X.X.map (homOfLE hrt) ≫ X.X.map (homOfLE hts) := by rw [← X.X.map_comp]; rfl
      _ = (f.app r ≫ g.app a ≫ PersistentObjects.mapEq X.X _) ≫ X.X.map (homOfLE hts) := by rw [hp'']
      _ = _ := by
        dsimp only [shift, Functor.comp_map, addLeft] at hn
        simp only [Category.assoc]
        rw [reassoc_of% hn]
        simp only [PersistentObjects.mapEq, ← X.X.map_comp]
        rfl
  have hfin := (hY a b hab).image (fun y => (g.app b ≫ X.X.map (homOfLE heq.le)) y)
  apply hfin.subset
  rintro _ ⟨x, rfl⟩
  rw [hfac]
  exact ⟨Y.X.map (homOfLE hab.le) (f.app r x), ⟨f.app r x, rfl⟩, rfl⟩

/-- An interleaving limit of q-tame persistent sets is q-tame, as in Proposition 6.7.4. -/
theorem qtame_of_interleaving_limit (x : ℕ → RTSet.{u}) (L : RCSet.{u})
    (hlim : Filter.Tendsto (fun n => interleavingDist (RCSet.mk (x n).X (x n).rightContinuous) L)
      Filter.atTop (𝓝 0)) : IsQTameSet L.X := by
  intro r s hrs
  let ε : ℝ≥0 := ⟨(s - r) / 3, by positivity⟩
  have he : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by
    exact_mod_cast (show (0 : ℝ≥0) < ε by change (0 : ℝ) < (s - r) / 3; linarith)
  have hev := (ENNReal.tendsto_nhds_zero.mp hlim) (ε / 2) (ENNReal.half_pos he.ne')
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
  have hd : interleavingDist (RCSet.mk (x n).X (x n).rightContinuous) L < (ε : ℝ≥0∞) :=
    (hn n le_rfl).trans_lt (by exact_mod_cast (show ε / 2 < ε by exact half_lt_self (by exact_mod_cast he)))
  have hi := (isInterleaved_of_dist_lt hd).symm
  exact qtame_structureMap_of_interleaved L _ (x n).qtame hi r s (by change (s - r) / 3 + (s - r) / 3 < s - r; linarith)

/-- Inclusion into right continuous persistent sets preserves the interleaving distance. -/
theorem rtSet_rc_dist (A B : RTSet.{u}) :
    interleavingDist (RCSet.mk A.X A.rightContinuous) (RCSet.mk B.X B.rightContinuous) =
      interleavingDist A B := by
  have hI (ε : ℝ≥0) :
      IsInterleaved (RCSet.mk A.X A.rightContinuous) (RCSet.mk B.X B.rightContinuous) ε ↔
        IsInterleaved A B ε := by
    constructor <;> rintro ⟨⟨f, g, hp⟩⟩ <;> exact ⟨⟨f, g, hp⟩⟩
  unfold interleavingDist
  simp_rw [hI]

/-- Completeness in Theorem 6.7.5: compute the limit in right continuous persistent sets,
then use Proposition 6.7.4 to recover q-tameness. -/
theorem rtSet_complete : IsCompleteDist (interleavingDist (C := RTSet.{u})) := by
  have hcomplete : IsCompleteDist (interleavingDist (C := RCSet.{u})) := by
    apply interleavingDist_complete_of_powered
    intro ε
    have := (copowPowAdjunction (C := RCSet.{u}) ε).isRightAdjoint
    infer_instance
  intro x hx
  let y n : RCSet.{u} := ⟨(x n).X, (x n).rightContinuous⟩
  have hy : ∀ ε : ℝ≥0∞, 0 < ε → ∃ n, ∀ i j, n ≤ i → n ≤ j → interleavingDist (y i) (y j) < ε := by
    simpa only [y, rtSet_rc_dist] using hx
  obtain ⟨L, hL⟩ := hcomplete y hy
  let l : RTSet.{u} := ⟨L.X, L.rightContinuous, qtame_of_interleaving_limit x L hL⟩
  refine ⟨l, ?_⟩
  have heq (n) : interleavingDist (x n) l = interleavingDist (y n) L := by
    rw [← rtSet_rc_dist]
  simpa only [heq] using hL

/-- **Theorem 6.7.5.** the interleaving distance on right continuous, q-tame persistent sets is
complete and geodesic, and persistent sets at distance zero are isomorphic.

**Gap (proof gap, Theorem 6.7.5).** The source asserts without proof that the shifted
image `im(Nat(X, Y^ε) → Nat(X, Y^δ))` is isomorphic to the sequential limit of the images
`im(Nat(X, Y^ε) → Nat(X|_n, Y^δ|_n))`, and omits checking closedness/product-closedness of
structure maps for Theorem 4.5.14. Lean uses pointwise discrete coordinates and compact
closures of shifted hom-space images for the compactness argument, avoiding these assertions.

Fixes the canonical locally persistent structure `rtSetLPCatStd` as in
Proposition 6.7.3. -/
theorem rtSet_geodesic_complete (L : LPCat RTSet.{u})
    (hL : L = rtSetLPCatStd) :
    @IsGeodesicDist RTSet.{u} (@interleavingDist RTSet.{u} _ L) ∧
    @IsCompleteDist RTSet.{u} (@interleavingDist RTSet.{u} _ L) ∧
    ∀ A B : RTSet.{u}, @interleavingDist RTSet.{u} _ L A B = 0 → Nonempty (A ≅ B) := by
  subst L
  refine ⟨interleavingDist_geodesic (admitsCoherentFactorizations_of_midpoints (rtSet_structure _ rfl).2.2.2.2) rtSet_reflectsInterleavings,
    rtSet_complete, ?_⟩
  intro A B h
  have hi := rtSet_reflectsInterleavings A B 0 (by simpa using h)
  exact isInterleaved_zero_iff.mp hi


end ScoccolaPhd
