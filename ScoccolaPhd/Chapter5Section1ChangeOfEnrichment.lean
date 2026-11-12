import Mathlib
import ScoccolaPhd.Chapter4Section3CompletenessObservable

/-!
# Chapter 5.1: Change of enrichment

Definition 5.1.1 unfolded: a locally `Q`-persistent category is a category enriched in `Set^Q`
(Day convolution) for a monoidal poset `Q`; as in `Chapter3Basic.lean` it is presented as a
category with extra structure (`LQPCat`).  A change of enrichment along a lax monoidal functor
`ℝ≥0 → Q` (a *superlinear family*, Section 5.1.1) is recorded by the relation
`IsChangeOfEnrichment`: the resulting locally persistent structure has
`Hom(x, y)_ε = Hom_Q(x, y)_{φ ε}`.  The sublinear projections of Section 5.1.3 are treated
likewise.

The objectwise functor construction and Lawvere sublinear projection are proved. Omitted: Lemma 5.1.14 (the right adjoint formula
is recorded as the definition of `ProjectionHom`), the compatibility of composition with the
change of enrichment (only the hom-sets are recorded), and Remark 5.1.10.
-/

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

universe u v w u' v'

namespace ScoccolaPhd

open LPCat

/-! ### 5.1 Locally `Q`-persistent categories -/

/-- Definition 5.1.1 (unfolded): a locally `Q`-persistent structure on `C`, for `Q` a monoidal
poset (not necessarily commutative). -/
class LQPCat (Q : Type w) [AddMonoid Q] [PartialOrder Q] [AddLeftMono Q] [AddRightMono Q]
    (C : Type u) [Category.{v} C] where
  hom : C → C → Q → Type v
  homZero : ∀ {x y : C}, (x ⟶ y) ≃ hom x y 0
  comp : ∀ {x y z : C} {ε δ : Q}, hom y z δ → hom x y ε → hom x z (ε + δ)
  S : ∀ {x y : C} {ε δ : Q}, ε ≤ δ → hom x y ε → hom x y δ
  id_comp : ∀ {x y : C} {ε : Q} (f : hom x y ε),
    S (le_of_eq (add_zero ε)) (comp (homZero (𝟙 y)) f) = f
  comp_id : ∀ {x y : C} {ε : Q} (f : hom x y ε),
    S (le_of_eq (zero_add ε)) (comp f (homZero (𝟙 x))) = f
  assoc : ∀ {x y z w : C} {ε δ γ : Q} (f : hom x y ε) (g : hom y z δ) (h : hom z w γ),
    S (le_of_eq (add_assoc ε δ γ)) (comp h (comp g f)) = comp (comp h g) f
  S_refl : ∀ {x y : C} {ε : Q} (f : hom x y ε), S le_rfl f = f
  S_trans : ∀ {x y : C} {ε δ γ : Q} (h₁ : ε ≤ δ) (h₂ : δ ≤ γ) (f : hom x y ε),
    S h₂ (S h₁ f) = S (h₁.trans h₂) f
  comp_S : ∀ {x y z : C} {ε ε' δ δ' : Q} (hε : ε ≤ ε') (hδ : δ ≤ δ')
    (f : hom x y ε) (g : hom y z δ),
    comp (S hδ g) (S hε f) = S (add_le_add hε hδ) (comp g f)
  homZero_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z),
    homZero (f ≫ g) = S (le_of_eq (add_zero 0)) (comp (homZero g) (homZero f))

section Examples

/-- The poset `ℝⁿ` (with the pointwise order; a synonym to avoid the product category). -/
def RN (n : ℕ) : Type := Fin n → ℝ

instance (n : ℕ) : AddCommGroup (RN n) := inferInstanceAs (AddCommGroup (Fin n → ℝ))
instance (n : ℕ) : PartialOrder (RN n) := inferInstanceAs (PartialOrder (Fin n → ℝ))
instance (n : ℕ) : AddLeftMono (RN n) := inferInstanceAs (AddLeftMono (Fin n → ℝ))

/-- The translation `w ↦ w + v` of `ℝⁿ`, for `v ∈ ℝⁿ₊`. -/
def vecShift {n : ℕ} (v : Fin n → ℝ≥0) : RN n ⥤ RN n where
  obj w := w + (show RN n from fun i => (v i : ℝ))
  map {w w'} f := homOfLE (add_le_add_left (leOfHom f) _)

section RNFunctor
variable (n : ℕ) {D : Type u} [Category.{v} D]

theorem vecShift_le {a b : Fin n → ℝ≥0} (h : a ≤ b) (w : RN n) :
    (vecShift a).obj w ≤ (vecShift b).obj w := by
  intro i
  exact add_le_add_right (by exact_mod_cast h i) _

/-- The comparison `Y (w + v) ⟶ Y (w + v')` for `v ≤ v'`. -/
def vecSh (Y : RN n ⥤ D) {a b : Fin n → ℝ≥0} (h : a ≤ b) : vecShift a ⋙ Y ⟶ vecShift b ⋙ Y where
  app w := Y.map (homOfLE (vecShift_le n h w))
  naturality := by
    intros; simp only [Functor.comp_map, ← Functor.map_comp]
    exact congrArg Y.map (Subsingleton.elim _ _)

theorem vecSh_refl (Y : RN n ⥤ D) (a : Fin n → ℝ≥0) : vecSh n Y (le_refl a) = 𝟙 _ := by
  ext w; simp only [vecSh, NatTrans.id_app]
  exact (congrArg Y.map (Subsingleton.elim _ (𝟙 _))).trans (Y.map_id _)

theorem vecSh_trans (Y : RN n ⥤ D) {a b c : Fin n → ℝ≥0} (h1 : a ≤ b) (h2 : b ≤ c) :
    vecSh n Y h1 ≫ vecSh n Y h2 = vecSh n Y (h1.trans h2) := by
  ext w; simp only [vecSh, NatTrans.comp_app, ← Functor.map_comp]
  exact congrArg Y.map (Subsingleton.elim _ _)

theorem vs_zero (w : RN n) : (vecShift (0 : Fin n → ℝ≥0)).obj w = w := by
  funext i
  change w i + ((0 : ℝ≥0) : ℝ) = w i
  simp

theorem vs_add (w : RN n) (ε δ : Fin n → ℝ≥0) :
    (vecShift δ).obj ((vecShift ε).obj w) = (vecShift (ε + δ)).obj w := by
  funext i
  change w i + (ε i : ℝ) + (δ i : ℝ) = w i + ((ε i : ℝ) + (δ i : ℝ))
  ring

theorem vecLoop (Y : RN n ⥤ D) {a : RN n} (g : a ⟶ a) : Y.map g = 𝟙 _ := by
  rw [Subsingleton.elim g (𝟙 a)]; exact Y.map_id a

theorem vecPar (Y : RN n ⥤ D) {a b : RN n} (g g' : a ⟶ b) : Y.map g = Y.map g' := by
  rw [Subsingleton.elim g g']

/-- `Y ⟶ Y^0`. -/
def vecIn (Y : RN n ⥤ D) : Y ⟶ vecShift (0 : Fin n → ℝ≥0) ⋙ Y where
  app w := Y.map (homOfLE (vs_zero n w).ge)
  naturality := by
    intros; simp only [Functor.comp_map, ← Functor.map_comp]
    exact congrArg Y.map (Subsingleton.elim _ _)

/-- `Y^0 ⟶ Y`. -/
def vecOut (Y : RN n ⥤ D) : vecShift (0 : Fin n → ℝ≥0) ⋙ Y ⟶ Y where
  app w := Y.map (homOfLE (vs_zero n w).le)
  naturality := by
    intros; simp only [Functor.comp_map, ← Functor.map_comp]
    exact congrArg Y.map (Subsingleton.elim _ _)

theorem vecIn_out (Y : RN n ⥤ D) : vecIn n Y ≫ vecOut n Y = 𝟙 Y := by
  ext w; simp only [vecIn, vecOut, NatTrans.comp_app, ← Functor.map_comp, NatTrans.id_app]
  exact (congrArg Y.map (Subsingleton.elim _ (𝟙 _))).trans (Y.map_id _)

theorem vecOut_in (Y : RN n ⥤ D) : vecOut n Y ≫ vecIn n Y = 𝟙 (vecShift (0 : Fin n → ℝ≥0) ⋙ Y) := by
  ext w; simp only [vecIn, vecOut, NatTrans.comp_app, ← Functor.map_comp, NatTrans.id_app]
  exact (congrArg Y.map (Subsingleton.elim _ (𝟙 _))).trans (Y.map_id _)

/-- `(Y^δ)^ε ⟶ Y^(ε+δ)`. -/
def vecAssoc (Z : RN n ⥤ D) (ε δ : Fin n → ℝ≥0) :
    vecShift ε ⋙ (vecShift δ ⋙ Z) ⟶ vecShift (ε + δ) ⋙ Z where
  app w := Z.map (homOfLE (vs_add n w ε δ).le)
  naturality := by
    intros; simp only [Functor.comp_map, ← Functor.map_comp]
    exact congrArg Z.map (Subsingleton.elim _ _)

/-- `Y^(ε+δ) ⟶ (Y^δ)^ε`. -/
def vecAssocInv (Z : RN n ⥤ D) (ε δ : Fin n → ℝ≥0) :
    vecShift (ε + δ) ⋙ Z ⟶ vecShift ε ⋙ (vecShift δ ⋙ Z) where
  app w := Z.map (homOfLE (vs_add n w ε δ).ge)
  naturality := by
    intros; simp only [Functor.comp_map, ← Functor.map_comp]
    exact congrArg Z.map (Subsingleton.elim _ _)

end RNFunctor

/-- Example 5.1.2: for a category `D`, the functor category `D^{ℝⁿ}` is a locally
`ℝⁿ₊`-persistent category with `Hom(X, Y)_v = Nat(X, Y^v)`. -/
theorem exists_lqpcat_functor (n : ℕ) (D : Type u) [Category.{v} D] :
    ∃ L : LQPCat (Fin n → ℝ≥0) (RN n ⥤ D),
      ∀ (X Y : RN n ⥤ D) (v : Fin n → ℝ≥0), L.hom X Y v = (X ⟶ vecShift v ⋙ Y) := by
  refine ⟨{ hom := fun X Y v => X ⟶ vecShift v ⋙ Y
            homZero := ⟨fun f => f ≫ vecIn n _, fun g => g ≫ vecOut n _, ?_, ?_⟩
            comp := fun {x y z ε δ} g f => f ≫ Functor.whiskerLeft (vecShift ε) g ≫ vecAssoc n z ε δ
            S := fun {x y ε δ} h f => f ≫ vecSh n y h
            id_comp := ?_
            comp_id := ?_
            assoc := ?_
            S_refl := ?_
            S_trans := ?_
            comp_S := ?_
            homZero_comp := ?_ }, fun _ _ _ => rfl⟩
  · intro f
    show (f ≫ vecIn n _) ≫ vecOut n _ = f
    rw [Category.assoc, vecIn_out, Category.comp_id]
  · intro g
    show (g ≫ vecOut n _) ≫ vecIn n _ = g
    rw [Category.assoc, vecOut_in, Category.comp_id]
  · intro x y ε f
    ext w
    simp only [Equiv.coe_fn_mk, Category.id_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
      vecIn, vecAssoc, vecSh, Category.assoc, ← Functor.map_comp]
    rw [vecLoop]
    exact Category.comp_id _
  · intro x y ε f
    ext w
    simp only [Equiv.coe_fn_mk, Category.id_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
      vecIn, vecAssoc, vecSh, Category.assoc, ← Functor.map_comp]
    rw [← Category.assoc, f.naturality]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    rw [vecLoop]
    exact Category.comp_id _
  · intro x y z w ε δ γ f g h
    ext v
    simp only [Equiv.coe_fn_mk, Category.id_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
      vecIn, vecAssoc, vecSh, Category.assoc, ← Functor.map_comp]
    congr 2
    rw [← Category.assoc, h.naturality, Category.assoc, Functor.comp_map, ← w.map_comp]
    exact congrArg (fun t => h.app _ ≫ w.map t) (Subsingleton.elim _ _)
  · intro x y ε f
    rw [vecSh_refl, Category.comp_id]
  · intro x y ε δ γ h₁ h₂ f
    rw [Category.assoc, vecSh_trans]
  · intro x y z ε ε' δ δ' hε hδ f g
    ext v
    simp only [Equiv.coe_fn_mk, Category.id_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
      vecIn, vecAssoc, vecSh, Category.assoc, ← Functor.map_comp]
    congr 1
    rw [← Category.assoc, g.naturality, Category.assoc, Functor.comp_map, ← z.map_comp]
    exact congrArg (fun t => g.app _ ≫ z.map t) (Subsingleton.elim _ _)
  · intro x y z f g
    ext v
    simp only [Equiv.coe_fn_mk, Category.id_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
      vecIn, vecAssoc, vecSh, Category.assoc, ← Functor.map_comp]
    congr 1
    rw [← Category.assoc (y.map _), g.naturality, Category.assoc, ← z.map_comp]
    exact congrArg (fun t => g.app _ ≫ z.map t) (Subsingleton.elim _ _)

end Examples

/-! ### 5.1.1 Superlinear families -/

section Superlinear

variable {Q : Type w} [AddMonoid Q] [PartialOrder Q] [AddLeftMono Q] [AddRightMono Q]

/-- A superlinear family (a lax monoidal functor `ℝ≥0 → Q`), normalised so that `φ 0 = 0`
(the case of all the examples with a shared underlying category). -/
structure SuperlinearFamily (Q : Type w) [AddMonoid Q] [PartialOrder Q] [AddLeftMono Q]
    [AddRightMono Q] where
  toFun : ℝ≥0 → Q
  mono : Monotone toFun
  map_zero : toFun 0 = 0
  superadd : ∀ a b, toFun a + toFun b ≤ toFun (a + b)

/-- The locally persistent structure `L` on `C` is obtained from the locally `Q`-persistent
structure `LQ` by change of enrichment along `φ`: `Hom_L(x, y)_ε = Hom_Q(x, y)_{φ ε}`. -/
def IsChangeOfEnrichment {C : Type u} [Category.{v} C] (φ : SuperlinearFamily Q)
    (LQ : LQPCat Q C) (L : LPCat C) : Prop :=
  ∃ e : ∀ (x y : C) (ε : ℝ≥0), L.hom x y ε = LQ.hom x y (φ.toFun ε),
    (∀ (x y : C) (f : x ⟶ y), cast (e x y 0) (L.homZero f) =
      LQ.S (le_of_eq φ.map_zero.symm) (LQ.homZero f)) ∧
    (∀ (x y z : C) (ε δ : ℝ≥0) (g : L.hom y z δ) (f : L.hom x y ε),
      cast (e x z (ε + δ)) (L.comp g f) =
        LQ.S (φ.superadd ε δ) (LQ.comp (cast (e y z δ) g) (cast (e x y ε) f))) ∧
    (∀ (x y : C) (ε δ : ℝ≥0) (h : ε ≤ δ) (f : L.hom x y ε),
      cast (e x y δ) (L.S h f) = LQ.S (φ.mono h) (cast (e x y ε) f))

/-- Definition 2.4.2 / Section 5.1.1: the change of enrichment along a superlinear family
exists. -/
theorem exists_changeOfEnrichment {C : Type u} [Category.{v} C] (φ : SuperlinearFamily Q)
    (LQ : LQPCat Q C) : ∃ L : LPCat C, IsChangeOfEnrichment φ LQ L := by
  let Z : ∀ {x y : C}, (x ⟶ y) ≃ LQ.hom x y (φ.toFun 0) := fun {x y} =>
    { toFun := fun f => LQ.S (le_of_eq φ.map_zero.symm) (LQ.homZero f)
      invFun := fun f => LQ.homZero.symm (LQ.S (le_of_eq φ.map_zero) f)
      left_inv := by intro f; simp [LQ.S_trans, LQ.S_refl]
      right_inv := by intro f; simp [LQ.S_trans, LQ.S_refl] }
  refine ⟨{
    hom := fun x y ε => LQ.hom x y (φ.toFun ε)
    homZero := Z
    comp := fun {x y z ε δ} g f => LQ.S (φ.superadd ε δ) (LQ.comp g f)
    S := fun h f => LQ.S (φ.mono h) f
    id_comp := ?_
    comp_id := ?_
    assoc := ?_
    S_refl := fun f => LQ.S_refl f
    S_trans := fun h₁ h₂ f => LQ.S_trans _ _ f
    comp_S := ?_
    homZero_comp := ?_ }, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ _ _ => rfl⟩
  · intro x y ε f
    change LQ.S _ (LQ.S _ (LQ.comp (LQ.S _ (LQ.homZero (𝟙 y))) f)) = f
    rw [← LQ.S_refl f, LQ.comp_S, LQ.S_trans, LQ.S_trans]
    convert LQ.id_comp f using 1; exact LQ.S_refl f
  · intro x y ε f
    change LQ.S _ (LQ.S _ (LQ.comp f (LQ.S _ (LQ.homZero (𝟙 x))))) = f
    rw [← LQ.S_refl f, LQ.comp_S, LQ.S_trans, LQ.S_trans]
    convert LQ.comp_id f using 1; exact LQ.S_refl f
  · intro x y z w ε δ γ f g h
    have hl : ∀ {a b c : C} {i j j' : Q} (hj : j ≤ j')
        (g : LQ.hom b c j) (f : LQ.hom a b i),
        LQ.comp (LQ.S hj g) f = LQ.S (add_le_add le_rfl hj) (LQ.comp g f) := by
      intro a b c i j j' hj g f
      simpa [LQ.S_refl] using LQ.comp_S (le_refl i) hj f g
    have hr : ∀ {a b c : C} {i i' j : Q} (hi : i ≤ i')
        (g : LQ.hom b c j) (f : LQ.hom a b i),
        LQ.comp g (LQ.S hi f) = LQ.S (add_le_add hi le_rfl) (LQ.comp g f) := by
      intro a b c i i' j hi g f
      simpa [LQ.S_refl] using LQ.comp_S hi (le_refl j) f g
    simp only [hl, hr, LQ.S_trans]
    have hh := congrArg (LQ.S (show φ.toFun ε + (φ.toFun δ + φ.toFun γ) ≤
        φ.toFun (ε + (δ + γ)) from
          (add_le_add le_rfl (φ.superadd δ γ)).trans (φ.superadd ε (δ + γ))))
      (LQ.assoc f g h)
    simpa only [LQ.S_trans] using hh
  · intro x y z ε ε' δ δ' hε hδ f g
    simp only [LQ.comp_S, LQ.S_trans]
  · intro x y z f g
    change LQ.S _ (LQ.homZero (f ≫ g)) = _
    rw [LQ.homZero_comp]
    change LQ.S _ (LQ.S _ (LQ.comp (LQ.homZero g) (LQ.homZero f))) =
      LQ.S _ (LQ.S _ (LQ.comp (LQ.S _ (LQ.homZero g)) (LQ.S _ (LQ.homZero f))))
    simp only [LQ.comp_S, LQ.S_trans]


/-- The ray `ε ↦ ε • v` in `ℝⁿ₊` (Example 5.1.3). -/
def rayFamily {n : ℕ} (v : Fin n → ℝ≥0) : SuperlinearFamily (Fin n → ℝ≥0) where
  toFun ε := ε • v
  mono a b h := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_le_mul_of_nonneg_right h zero_le
  map_zero := by simp
  superadd a b := by simp [add_smul]

lemma exists_pos_le_smul {n : ℕ} (v w : Fin n → ℝ≥0) (hw : ∀ i, 0 < w i) :
    ∃ c : ℝ≥0, 0 < c ∧ v ≤ c • w := by
  let c : ℝ≥0 := 1 + ∑ i : Fin n, (v i / w i)
  have hc : 0 < c := zero_lt_one.trans_le (le_add_of_nonneg_right zero_le)
  refine ⟨c, hc, fun i => ?_⟩
  have hle : v i / w i ≤ ∑ j : Fin n, (v j / w j) :=
    Finset.single_le_sum (f := fun j => v j / w j) (fun _ _ => zero_le) (Finset.mem_univ i)
  have hle_c : v i / w i ≤ c := hle.trans le_add_self
  simpa only [Pi.smul_apply, smul_eq_mul] using (div_le_iff₀ (hw i)).mp hle_c

lemma smul_le_mul_smul {n : ℕ} (v w : Fin n → ℝ≥0) (c : ℝ≥0) (h : v ≤ c • w) (ε : ℝ≥0) :
    ε • v ≤ (ε * c) • w := by
  intro i
  simp only [Pi.smul_apply, smul_eq_mul]
  have := mul_le_mul_of_nonneg_left (h i) (show 0 ≤ ε from zero_le)
  rwa [mul_assoc]

/-- Interleavings transfer along a comparison `φ δ ≤ ψ (c δ)` of superlinear families. -/
lemma isInterleaved_of_le {Q : Type w} [AddMonoid Q] [PartialOrder Q] [AddLeftMono Q]
    [AddRightMono Q] {C : Type u} [Category.{v} C] (LQ : LQPCat Q C)
    (φ ψ : SuperlinearFamily Q) (Lv Lw : LPCat C)
    (hLv : IsChangeOfEnrichment φ LQ Lv) (hLw : IsChangeOfEnrichment ψ LQ Lw) (c : ℝ≥0)
    (hle : ∀ δ : ℝ≥0, φ.toFun δ ≤ ψ.toFun (c * δ)) {x y : C} {δ : ℝ≥0}
    (h : @IsInterleaved C _ Lv x y δ) : @IsInterleaved C _ Lw x y (c * δ) := by
  obtain ⟨ev, zv, cv, sv⟩ := hLv
  obtain ⟨ew, zw, cw, sw⟩ := hLw
  obtain ⟨⟨f, g, h1, h2⟩⟩ := h
  let F : LQ.hom x y (ψ.toFun (c * δ)) := LQ.S (hle δ) (cast (ev x y δ) f)
  let G : LQ.hom y x (ψ.toFun (c * δ)) := LQ.S (hle δ) (cast (ev y x δ) g)
  refine ⟨⟨cast (ew x y _).symm F, cast (ew y x _).symm G, ?_, ?_⟩⟩
  · apply (cast_inj (ew x x (c * δ + c * δ))).1
    have key := congrArg (cast (ev x x (δ + δ))) h1
    unfold LPCat.idHom at key
    rw [cv, sv, zv] at key
    show cast (ew x x (c * δ + c * δ)) (Lw.comp (cast (ew y x _).symm G) (cast (ew x y _).symm F)) =
      cast (ew x x (c * δ + c * δ)) (Lw.S zero_le (Lw.homZero (𝟙 x)))
    rw [cw, sw, zw]
    simp only [cast_cast, cast_eq]
    rw [LQ.comp_S]
    have hq : φ.toFun (δ + δ) ≤ ψ.toFun (c * δ + c * δ) :=
      (hle (δ + δ)).trans (ψ.mono (le_of_eq (by rw [mul_add])))
    calc _ = LQ.S hq (LQ.S (φ.superadd δ δ)
          (LQ.comp (cast (ev y x δ) g) (cast (ev x y δ) f))) := by simp only [LQ.S_trans]
      _ = LQ.S hq (LQ.S (φ.mono zero_le) (LQ.S (le_of_eq φ.map_zero.symm) (LQ.homZero (𝟙 x)))) := by
          rw [key]
      _ = _ := by simp only [LQ.S_trans]
  · apply (cast_inj (ew y y (c * δ + c * δ))).1
    have key := congrArg (cast (ev y y (δ + δ))) h2
    unfold LPCat.idHom at key
    rw [cv, sv, zv] at key
    show cast (ew y y (c * δ + c * δ)) (Lw.comp (cast (ew x y _).symm F) (cast (ew y x _).symm G)) =
      cast (ew y y (c * δ + c * δ)) (Lw.S zero_le (Lw.homZero (𝟙 y)))
    rw [cw, sw, zw]
    simp only [cast_cast, cast_eq]
    rw [LQ.comp_S]
    have hq : φ.toFun (δ + δ) ≤ ψ.toFun (c * δ + c * δ) :=
      (hle (δ + δ)).trans (ψ.mono (le_of_eq (by rw [mul_add])))
    calc _ = LQ.S hq (LQ.S (φ.superadd δ δ)
          (LQ.comp (cast (ev x y δ) f) (cast (ev y x δ) g))) := by simp only [LQ.S_trans]
      _ = LQ.S hq (LQ.S (φ.mono zero_le) (LQ.S (le_of_eq φ.map_zero.symm) (LQ.homZero (𝟙 y)))) := by
          rw [key]
      _ = _ := by simp only [LQ.S_trans]

lemma interleavingDist_le_mul_of_isInterleaved {C : Type u} [Category.{v} C]
    (Lv Lw : LPCat C) (c : ℝ≥0) (hc : 0 < c) (x y : C)
    (h : ∀ (δ : ℝ≥0), @IsInterleaved C _ Lv x y δ → @IsInterleaved C _ Lw x y (c * δ)) :
    @interleavingDist C _ Lw x y ≤ c * @interleavingDist C _ Lv x y := by
  unfold interleavingDist
  by_cases hne : ∃ δ : ℝ≥0, @IsInterleaved C _ Lv x y δ
  · obtain ⟨δ₀, hδ₀⟩ := hne
    have : Nonempty {δ : ℝ≥0 // @IsInterleaved C _ Lv x y δ} := ⟨⟨δ₀, hδ₀⟩⟩
    have h_top : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hdist_eq : (c : ℝ≥0∞) * (⨅ (δ : ℝ≥0) (_ : @IsInterleaved C _ Lv x y δ), (δ : ℝ≥0∞)) =
        ⨅ (d : {δ : ℝ≥0 // @IsInterleaved C _ Lv x y δ}), ((c * d.1 : ℝ≥0) : ℝ≥0∞) := by
      rw [iInf_subtype']
      rw [ENNReal.mul_iInf (by intro h; exact (h_top h).elim)]
      simp only [ENNReal.coe_mul]
    change @interleavingDist C _ Lw x y ≤ (c : ℝ≥0∞) * (⨅ (δ : ℝ≥0) (_ : @IsInterleaved C _ Lv x y δ), (δ : ℝ≥0∞))
    rw [hdist_eq]
    exact le_iInf fun ⟨d, hd⟩ => iInf₂_le (c * d) (h d hd)
  · have hne' : ∀ δ : ℝ≥0, ¬ @IsInterleaved C _ Lv x y δ := by
      intro δ hδ; exact hne ⟨δ, hδ⟩
    have : (⨅ (δ : ℝ≥0) (_ : @IsInterleaved C _ Lv x y δ), (δ : ℝ≥0∞)) = ⊤ := by
      refine top_unique (le_iInf fun δ => le_iInf fun hδ => (hne' δ hδ).elim)
    change @interleavingDist C _ Lw x y ≤ (c : ℝ≥0∞) * (⨅ (δ : ℝ≥0) (_ : @IsInterleaved C _ Lv x y δ), (δ : ℝ≥0∞))
    rw [this, ENNReal.mul_top (by exact_mod_cast hc.ne')]
    exact le_top

/-- Proposition 5.1.4: for strictly positive `v, w`, the interleaving distances obtained by
change of enrichment along `v` and `w` are bi-Lipschitz equivalent.

**Gap (proof gap, Proposition 5.1.4).** In the thesis proof (page 98), the inequality `ε₂ w ≤ v` is claimed
to give a `(c * δ)`-interleaving for `w` from a `δ`-interleaving for `v`. But `ε₂ w ≤ v` bounds `w`
by `v`, so shifting an `ε v`-morphism up to a `w`-morphism requires `v ≤ c w` (the other
inequality `ε₁ v ≤ w`, yielding factor `1 / ε₁`). -/
theorem interleavingDist_biLipschitz {n : ℕ} {C : Type u} [Category.{v} C]
    (LQ : LQPCat (Fin n → ℝ≥0) C) (v w : Fin n → ℝ≥0) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (Lv Lw : LPCat C) (hLv : IsChangeOfEnrichment (rayFamily v) LQ Lv)
    (hLw : IsChangeOfEnrichment (rayFamily w) LQ Lw) :
    ∃ c₁ c₂ : ℝ≥0, 0 < c₁ ∧ 0 < c₂ ∧ ∀ x y : C,
      @interleavingDist C _ Lv x y ≤ c₁ * @interleavingDist C _ Lw x y ∧
      @interleavingDist C _ Lw x y ≤ c₂ * @interleavingDist C _ Lv x y := by
  obtain ⟨c₁, hc₁, h₁⟩ := exists_pos_le_smul w v hv
  obtain ⟨c₂, hc₂, h₂⟩ := exists_pos_le_smul v w hw
  refine ⟨c₁, c₂, hc₁, hc₂, fun x y => ⟨?_, ?_⟩⟩
  · exact interleavingDist_le_mul_of_isInterleaved Lw Lv c₁ hc₁ x y (fun δ hδ =>
      isInterleaved_of_le LQ (rayFamily w) (rayFamily v) Lw Lv hLw hLv c₁
        (fun δ => by simpa [rayFamily, mul_comm] using smul_le_mul_smul w v c₁ h₁ δ) hδ)
  · exact interleavingDist_le_mul_of_isInterleaved Lv Lw c₂ hc₂ x y (fun δ hδ =>
      isInterleaved_of_le LQ (rayFamily v) (rayFamily w) Lv Lw hLv hLw c₂
        (fun δ => by simpa [rayFamily, mul_comm] using smul_le_mul_smul v w c₂ h₂ δ) hδ)

end Superlinear

section Lemma515

variable {Q : Type w} [AddCommMonoid Q] [PartialOrder Q] [AddLeftMono Q] [AddRightMono Q]
  {C : Type u} [Category.{v} C]

/-- `LQ` is powered by representables, in the `Q`-graded sense: `Hom(x, y^q)_r ≅ Hom(x, y)_{q+r}`,
naturally (the three laws mirror those of `PoweredByRepresentables`; they need `Q` commutative). -/
structure QPoweredByRepresentables (LQ : LQPCat Q C) where
  pow : Q → C ⥤ C
  powIso : ∀ (x y : C) (q r : Q), LQ.hom x ((pow q).obj y) r ≃ LQ.hom x y (q + r)
  powIso_S : ∀ {x y : C} {q r r' : Q} (h : r ≤ r') (u : LQ.hom x ((pow q).obj y) r),
    powIso x y q r' (LQ.S h u) = LQ.S (add_le_add le_rfl h) (powIso x y q r u)
  powIso_x : ∀ {x x' y : C} {q r δ : Q} (v : LQ.hom x' x δ) (u : LQ.hom x ((pow q).obj y) r),
    powIso x' y q (δ + r) (LQ.comp u v) =
      LQ.S (le_of_eq (add_left_comm δ q r)) (LQ.comp (powIso x y q r u) v)
  powIso_y : ∀ {x y y' : C} {q r : Q} (f : y ⟶ y') (u : LQ.hom x ((pow q).obj y) r),
    powIso x y' q r (LQ.S (le_of_eq (by simp)) (LQ.comp (LQ.homZero ((pow q).map f)) u)) =
      LQ.S (le_of_eq (by simp)) (LQ.comp (LQ.homZero f) (powIso x y q r u))



/-- The `Q`-graded copower equivalence, compatible with grade shifts. -/
structure QCopoweredByRepresentables (LQ : LQPCat Q C) where
  copow : Q → C ⥤ C
  copowIso : ∀ (x y : C) (q r : Q), LQ.hom ((copow q).obj x) y r ≃ LQ.hom x y (q + r)
  copowIso_S : ∀ {x y : C} {q r r' : Q} (h : r ≤ r') (u : LQ.hom ((copow q).obj x) y r),
    copowIso x y q r' (LQ.S h u) = LQ.S (add_le_add le_rfl h) (copowIso x y q r u)
  copowIso_x : ∀ {x x' y : C} {q r : Q} (f : x' ⟶ x) (u : LQ.hom ((copow q).obj x) y r),
    copowIso x' y q r (LQ.S (le_of_eq (by simp)) (LQ.comp u (LQ.homZero ((copow q).map f)))) =
      LQ.S (le_of_eq (by simp)) (LQ.comp (copowIso x y q r u) (LQ.homZero f))
  copowIso_y : ∀ {x y y' : C} {q r δ : Q} (v : LQ.hom y y' δ) (u : LQ.hom ((copow q).obj x) y r),
    copowIso x y' q (r + δ) (LQ.comp v u) =
      LQ.S (le_of_eq (add_assoc q r δ)) (LQ.comp v (copowIso x y q r u))


theorem lqS_l (LQ : LQPCat Q C) {x y z : C} {ε δ δ' : Q} (h : δ ≤ δ') (g : LQ.hom y z δ)
    (f : LQ.hom x y ε) : LQ.comp (LQ.S h g) f = LQ.S (add_le_add le_rfl h) (LQ.comp g f) := by
  have := LQ.comp_S (le_refl ε) h f g
  rwa [LQ.S_refl] at this

theorem lqS_r (LQ : LQPCat Q C) {x y z : C} {ε ε' δ : Q} (h : ε ≤ ε') (g : LQ.hom y z δ)
    (f : LQ.hom x y ε) : LQ.comp g (LQ.S h f) = LQ.S (add_le_add h le_rfl) (LQ.comp g f) := by
  have := LQ.comp_S h (le_refl δ) f g
  rwa [LQ.S_refl] at this

/-- Helper for Lemma 5.1.5 (powered case): existence of a `PoweredByRepresentables` structure
obtained by change of enrichment with explicit `pow`. -/
theorem exists_powered_of_changeOfEnrichment (φ : SuperlinearFamily Q)
    (hφ : ∀ a b, φ.toFun (a + b) = φ.toFun a + φ.toFun b) (LQ : LQPCat Q C)
    (P : QPoweredByRepresentables LQ) (L : LPCat C) (h : IsChangeOfEnrichment φ LQ L) :
    ∃ P' : @PoweredByRepresentables C _ L, ∀ ε, P'.pow ε = P.pow (φ.toFun ε) := by
  letI := L
  obtain ⟨e, hz, hc, hs⟩ := h
  let eqv : ∀ (x y : C) (ε : ℝ≥0), L.hom x y ε ≃ LQ.hom x y (φ.toFun ε) :=
    fun x y ε => Equiv.cast (e x y ε)
  have F_S : ∀ {x y : C} {ε δ : ℝ≥0} (h : ε ≤ δ) (f : L.hom x y ε),
      eqv x y δ (L.S h f) = LQ.S (φ.mono h) (eqv x y ε f) := fun h f => hs _ _ _ _ h f
  have F_comp : ∀ {x y z : C} {ε δ : ℝ≥0} (g : L.hom y z δ) (f : L.hom x y ε),
      eqv x z (ε + δ) (L.comp g f) =
        LQ.S (φ.superadd ε δ) (LQ.comp (eqv y z δ g) (eqv x y ε f)) :=
    fun g f => hc _ _ _ _ _ g f
  have F_zero : ∀ {x y : C} (f : x ⟶ y),
      eqv x y 0 (L.homZero f) = LQ.S (le_of_eq φ.map_zero.symm) (LQ.homZero f) :=
    fun f => hz _ _ f
  let toL : ∀ (x y : C) (ε r : ℝ≥0), LQ.hom x y (φ.toFun ε + φ.toFun r) → L.hom x y (ε + r) :=
    fun x y ε r u => (eqv x y (ε + r)).symm (LQ.S (le_of_eq (hφ ε r).symm) u)
  let ofL : ∀ (x y : C) (ε r : ℝ≥0), L.hom x y (ε + r) → LQ.hom x y (φ.toFun ε + φ.toFun r) :=
    fun x y ε r w => LQ.S (le_of_eq (hφ ε r)) (eqv x y (ε + r) w)
  have toL_ofL : ∀ x y ε r (w : L.hom x y (ε + r)), toL x y ε r (ofL x y ε r w) = w := by
    intro x y ε r w
    simp only [toL, ofL, LQ.S_trans, LQ.S_refl, Equiv.symm_apply_apply]
  have ofL_toL : ∀ x y ε r (u : LQ.hom x y (φ.toFun ε + φ.toFun r)), ofL x y ε r (toL x y ε r u) = u := by
    intro x y ε r u
    simp only [toL, ofL, LQ.S_trans, LQ.S_refl, Equiv.apply_symm_apply]
  refine ⟨{ pow := fun ε => P.pow (φ.toFun ε)
            powIso := fun x y ε r =>
              { toFun := fun u => toL x y ε r (P.powIso x y (φ.toFun ε) (φ.toFun r) (eqv _ _ r u))
                invFun := fun w => (eqv _ _ r).symm ((P.powIso x y (φ.toFun ε) (φ.toFun r)).symm (ofL x y ε r w))
                left_inv := fun u => by simp [ofL_toL]
                right_inv := fun w => by simp [toL_ofL] }
            powIso_S := ?_
            powIso_x := ?_
            powIso_y := ?_ }, fun _ => rfl⟩
  · intro x y ε r r' h u
    apply (eqv _ _ _).injective
    simp only [toL, Equiv.coe_fn_mk, Equiv.apply_symm_apply, F_S, P.powIso_S, LQ.S_trans]
  · intro x x' y ε r δ v u
    apply (eqv _ _ _).injective
    simp only [toL, Equiv.coe_fn_mk, Equiv.apply_symm_apply, F_S, F_comp, P.powIso_S, P.powIso_x,
      lqS_l, LQ.S_trans]
  · intro x y y' ε r f u
    apply (eqv _ _ _).injective
    simp only [toL, Equiv.coe_fn_mk, Equiv.apply_symm_apply, F_S, F_comp, F_zero,
      lqS_l, LQ.S_trans]
    rw [P.powIso_y f]
    simp only [lqS_l, lqS_r, LQ.S_trans]

/-- Lemma 5.1.5 (powered case). Here `QPoweredByRepresentables` carries the naturality laws of
`PoweredByRepresentables`, and `Q` is commutative (as in all applications). -/
theorem poweredByRepresentables_of_changeOfEnrichment (φ : SuperlinearFamily Q)
    (hφ : ∀ a b, φ.toFun (a + b) = φ.toFun a + φ.toFun b) (LQ : LQPCat Q C)
    (P : QPoweredByRepresentables LQ) (L : LPCat C) (h : IsChangeOfEnrichment φ LQ L) :
    Nonempty (@PoweredByRepresentables C _ L) :=
  ⟨(exists_powered_of_changeOfEnrichment φ hφ LQ P L h).choose⟩

/-- Lemma 5.1.5, copowered case. -/
theorem copoweredByRepresentables_of_changeOfEnrichment (φ : SuperlinearFamily Q)
    (hφ : ∀ a b, φ.toFun (a + b) = φ.toFun a + φ.toFun b) (LQ : LQPCat Q C)
    (P : QCopoweredByRepresentables LQ) (L : LPCat C) (h : IsChangeOfEnrichment φ LQ L) :
    Nonempty (@CopoweredByRepresentables C _ L) := by
  obtain ⟨e, hz, hc, hs⟩ := h
  let eqv : ∀ (x y : C) (ε : ℝ≥0), L.hom x y ε ≃ LQ.hom x y (φ.toFun ε) :=
    fun x y ε => Equiv.cast (e x y ε)
  have F_S : ∀ {x y : C} {ε δ : ℝ≥0} (h : ε ≤ δ) (f : L.hom x y ε),
      eqv x y δ (L.S h f) = LQ.S (φ.mono h) (eqv x y ε f) := fun h f => hs _ _ _ _ h f
  have F_comp : ∀ {x y z : C} {ε δ : ℝ≥0} (g : L.hom y z δ) (f : L.hom x y ε),
      eqv x z (ε + δ) (L.comp g f) =
        LQ.S (φ.superadd ε δ) (LQ.comp (eqv y z δ g) (eqv x y ε f)) :=
    fun g f => hc _ _ _ _ _ g f
  have F_zero : ∀ {x y : C} (f : x ⟶ y),
      eqv x y 0 (L.homZero f) = LQ.S (le_of_eq φ.map_zero.symm) (LQ.homZero f) :=
    fun f => hz _ _ f
  let toL : ∀ (x y : C) (ε r : ℝ≥0), LQ.hom x y (φ.toFun ε + φ.toFun r) → L.hom x y (ε + r) :=
    fun x y ε r u => (eqv x y (ε + r)).symm (LQ.S (le_of_eq (hφ ε r).symm) u)
  let ofL : ∀ (x y : C) (ε r : ℝ≥0), L.hom x y (ε + r) → LQ.hom x y (φ.toFun ε + φ.toFun r) :=
    fun x y ε r w => LQ.S (le_of_eq (hφ ε r)) (eqv x y (ε + r) w)
  have toL_ofL : ∀ x y ε r (w : L.hom x y (ε + r)), toL x y ε r (ofL x y ε r w) = w := by
    intro x y ε r w
    simp only [toL, ofL, LQ.S_trans, LQ.S_refl, Equiv.symm_apply_apply]
  have ofL_toL : ∀ x y ε r (u : LQ.hom x y (φ.toFun ε + φ.toFun r)), ofL x y ε r (toL x y ε r u) = u := by
    intro x y ε r u
    simp only [toL, ofL, LQ.S_trans, LQ.S_refl, Equiv.apply_symm_apply]
  refine ⟨{ copow := fun ε => P.copow (φ.toFun ε)
            copowIso := fun x y ε r =>
              { toFun := fun u => toL x y ε r (P.copowIso x y (φ.toFun ε) (φ.toFun r) (eqv _ _ r u))
                invFun := fun w => (eqv _ _ r).symm ((P.copowIso x y (φ.toFun ε) (φ.toFun r)).symm (ofL x y ε r w))
                left_inv := fun u => by simp [ofL_toL]
                right_inv := fun w => by simp [toL_ofL] }
            copowIso_S := ?_
            copowIso_x := ?_
            copowIso_y := ?_ }⟩
  · intro x y ε r r' h u
    apply (eqv _ _ _).injective
    simp only [toL, Equiv.coe_fn_mk, Equiv.apply_symm_apply, F_S, P.copowIso_S, LQ.S_trans]

  · intro x x' y ε r f u
    apply (eqv _ _ _).injective
    simp only [toL, Equiv.coe_fn_mk, Equiv.apply_symm_apply, F_S, F_comp, F_zero,
      lqS_r, LQ.S_trans]
    rw [P.copowIso_x f]
    simp only [lqS_l, lqS_r, LQ.S_trans]
  · intro x y y' ε r δ v u
    apply (eqv _ _ _).injective
    simp only [toL, Equiv.coe_fn_mk, Equiv.apply_symm_apply, F_S, F_comp, P.copowIso_S,
      P.copowIso_y, lqS_r, LQ.S_trans]

end Lemma515

/-! ### BSS13: translations of a poset -/

section Translations

/-- A translation of a preorder `P`: a monotone map `Γ` with `x ≤ Γ x`. -/
@[ext]
structure Translation (P : Type u) [Preorder P] where
  toFun : P → P
  mono : Monotone toFun
  le_apply : ∀ x, x ≤ toFun x

variable {P : Type u} [PartialOrder P]

instance : Zero (Translation P) := ⟨⟨id, monotone_id, fun _ => le_rfl⟩⟩

/-- Monoidal product of translations: `Γ + Δ` is "first `Γ`, then `Δ`" (so that
`Hom(X,Y)_Γ × Hom(Y,Z)_Δ → Hom(X,Z)_{Γ+Δ}`). -/
instance : Add (Translation P) :=
  ⟨fun Γ Δ => ⟨Δ.toFun ∘ Γ.toFun, Δ.mono.comp Γ.mono, fun x => (Γ.le_apply x).trans
    (Δ.le_apply _)⟩⟩

instance : AddMonoid (Translation P) where
  add_assoc _ _ _ := rfl
  zero_add _ := rfl
  add_zero _ := rfl
  nsmul := nsmulRec

instance : PartialOrder (Translation P) where
  le Γ Δ := ∀ x, Γ.toFun x ≤ Δ.toFun x
  le_refl _ _ := le_rfl
  le_trans _ _ _ h h' x := (h x).trans (h' x)
  le_antisymm Γ Δ h h' := Translation.ext (funext fun x => le_antisymm (h x) (h' x))

instance : AddLeftMono (Translation P) := ⟨fun Θ {_ _} h x => h (Θ.toFun x)⟩

instance : AddRightMono (Translation P) := ⟨fun Θ {_ _} h x => Θ.mono (h x)⟩

end Translations

section BSS

variable {P : Type u} [PartialOrder P] {C : Type u} [Category.{v} C]

/-- Section 5.1.1: the `Set^{Trans P}`-enrichment of `C^P`, `Hom(X, Y)_Γ = Nat(X, Y ∘ Γ)`. -/
theorem exists_lqpcat_translation :
    ∃ L : LQPCat (Translation P) (P ⥤ C), ∀ (X Y : P ⥤ C) (Γ : Translation P),
      L.hom X Y Γ = (X ⟶ (Monotone.functor Γ.mono) ⋙ Y) := by
  let Z : ∀ {X Y : P ⥤ C}, (X ⟶ Y) ≃ (X ⟶ (Monotone.functor (0 : Translation P).mono) ⋙ Y) :=
    fun {X Y} =>
      { toFun := fun f => { app := f.app, naturality := f.naturality }
        invFun := fun f => { app := f.app, naturality := f.naturality }
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  refine ⟨{
    hom := fun X Y Γ => X ⟶ (Monotone.functor Γ.mono) ⋙ Y
    homZero := Z
    comp := fun {X Y W Γ Δ} g f => f ≫ Functor.whiskerLeft (Monotone.functor Γ.mono) g
    S := fun {X Y Γ Δ} h f => f ≫ Functor.whiskerRight
      { app := fun x => homOfLE (h x) } Y
    id_comp := ?_
    comp_id := ?_
    assoc := ?_
    S_refl := ?_
    S_trans := ?_
    comp_S := ?_
    homZero_comp := ?_ }, fun _ _ _ => rfl⟩
  · intro X Y Γ f
    ext x
    change (f.app x ≫ 𝟙 _) ≫ Y.map (𝟙 _) = f.app x
    simp
  · intro X Y Γ f
    ext x
    change (𝟙 _ ≫ f.app x) ≫ Y.map (𝟙 _) = f.app x
    simp
  · intro X Y W V Γ Δ Θ f g h
    ext x
    change ((f.app x ≫ g.app (Γ.toFun x)) ≫ h.app (Δ.toFun (Γ.toFun x))) ≫
      V.map (𝟙 _) = f.app x ≫ (g.app (Γ.toFun x) ≫ h.app (Δ.toFun (Γ.toFun x)))
    simp [Category.assoc]
  · intro X Y Γ f
    ext x
    change f.app x ≫ Y.map (𝟙 _) = f.app x
    simp
  · intro X Y Γ Δ Θ h₁ h₂ f
    ext x
    dsimp
    rw [Category.assoc, ← Y.map_comp]
    rfl
  · intro X Y W Γ Γ' Δ Δ' hΓ hΔ f g
    ext x
    dsimp
    simp only [Category.assoc, NatTrans.naturality_assoc, Functor.comp_map, ← Functor.map_comp]
    rfl
  · intro X Y W f g
    ext x
    change f.app x ≫ g.app x = (f.app x ≫ g.app x) ≫ W.map (𝟙 _)
    simp


/-- Remark 5.1.6 / [BSS13, Section 2.5]: a superlinear family `ℝ≥0 → Trans P` induces a
locally persistent structure on `C^P`. -/
theorem exists_changeOfEnrichment_translation (φ : SuperlinearFamily (Translation P))
    (L : LQPCat (Translation P) (P ⥤ C)) : ∃ L' : LPCat (P ⥤ C), IsChangeOfEnrichment φ L L' :=
  exists_changeOfEnrichment φ L

end BSS

/-! ### 5.1.2 Persistent objects of a locally persistent category -/

section PersistentObjects

variable {C : Type u} [Category.{v} C] [LPCat C]

/-- Definition 5.1.7: `Hom_{C^ℝ}(X, Y)_{(ε, δ)} = Nat(X, Y^ε)_δ`: families of
`δ`-morphisms `α r : X r → Y (r + ε)` which commute with the structure maps of `X` and `Y`
(as `δ`-morphisms). -/
def PersistentHom (X Y : ℝ ⥤ C) (ε δ : ℝ≥0) : Type v :=
  {α : ∀ r : ℝ, hom (X.obj r) (Y.obj (r + ε)) δ //
    ∀ (r s : ℝ) (h : r ≤ s),
      S (le_of_eq (add_zero δ))
          (comp (homZero (Y.map (homOfLE (add_le_add_left h (ε : ℝ))))) (α r)) =
        S (le_of_eq (zero_add δ)) (comp (α s) (homZero (X.map (homOfLE h))))}

/-! ### Composition, shifts and units in `C^ℝ` (proof of Definition 5.1.7) -/

/-- The structure map `Y s ⟶ Y t` as a `0`-morphism. -/
def persPc (Y : ℝ ⥤ C) {a b : ℝ} (h : a ≤ b) : hom (Y.obj a) (Y.obj b) 0 :=
  homZero (Y.map (homOfLE h))

/-- Postcompose with a structure map. -/
def persTr (Y : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) {x : C} {δ : ℝ≥0} (f : hom x (Y.obj s) δ) :
    hom x (Y.obj t) δ := S (le_of_eq (add_zero δ)) (comp (persPc Y h) f)

/-- Precompose with a structure map. -/
def persPre (X : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) {y : C} {δ : ℝ≥0} (f : hom (X.obj t) y δ) :
    hom (X.obj s) y δ := S (le_of_eq (zero_add δ)) (comp f (persPc X h))

theorem persPc_refl (Y : ℝ ⥤ C) (s : ℝ) : persPc Y (le_refl s) = idHom (Y.obj s) := by
  simp [persPc, idHom]

theorem persPc_comp (Y : ℝ ⥤ C) {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    comp (persPc Y h2) (persPc Y h1) = S (le_of_eq (add_zero 0).symm) (persPc Y (h1.trans h2)) := by
  have := homZero_comp (Y.map (homOfLE h1)) (Y.map (homOfLE h2))
  rw [← Y.map_comp] at this
  unfold persPc
  have e : homOfLE h1 ≫ homOfLE h2 = homOfLE (h1.trans h2) := rfl
  rw [e] at this
  exact (eq_S_symm (add_zero (0 : ℝ≥0)) this.symm)

theorem persTr_refl (Y : ℝ ⥤ C) {s : ℝ} {x : C} {δ : ℝ≥0} (f : hom x (Y.obj s) δ) :
    persTr Y (le_refl s) f = f := by
  unfold persTr
  rw [persPc_refl, id_comp', S_trans, S_refl]

theorem persTr_S (Y : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) {x : C} {δ δ' : ℝ≥0} (k : δ ≤ δ')
    (f : hom x (Y.obj s) δ) : persTr Y h (S k f) = S k (persTr Y h f) := by
  unfold persTr
  rw [comp_S_r, S_trans, S_trans]

theorem persTr_trans (Y : ℝ ⥤ C) {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) {x : C} {δ : ℝ≥0}
    (f : hom x (Y.obj a) δ) : persTr Y h2 (persTr Y h1 f) = persTr Y (h1.trans h2) f := by
  unfold persTr
  rw [comp_S_r, assoc' f (persPc Y h1) (persPc Y h2), persPc_comp, comp_S_l]
  simp only [S_trans]

theorem persPc_comp' (X : ℝ ⥤ C) {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    comp (persPc X h2) (persPc X h1) = S (le_of_eq (add_zero 0).symm) (persPc X (h1.trans h2)) := persPc_comp X h1 h2

theorem persPre_refl (X : ℝ ⥤ C) {s : ℝ} {y : C} {δ : ℝ≥0} (f : hom (X.obj s) y δ) :
    persPre X (le_refl s) f = f := by
  unfold persPre
  rw [persPc_refl, comp_id', S_trans, S_refl]

theorem persPre_S (X : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) {y : C} {δ δ' : ℝ≥0} (k : δ ≤ δ')
    (f : hom (X.obj t) y δ) : persPre X h (S k f) = S k (persPre X h f) := by
  unfold persPre
  rw [comp_S_l, S_trans, S_trans]

theorem persPre_trans (X : ℝ ⥤ C) {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) {y : C} {δ : ℝ≥0}
    (f : hom (X.obj c) y δ) : persPre X h1 (persPre X h2 f) = persPre X (h1.trans h2) f := by
  unfold persPre
  rw [comp_S_l, ← LPCat.assoc (persPc X h1) (persPc X h2) f, persPc_comp', comp_S_r]
  simp only [S_trans]

theorem persTr_comp (Z : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) {x y : C} {ε δ : ℝ≥0}
    (g : hom y (Z.obj s) δ) (f : hom x y ε) : persTr Z h (comp g f) = comp (persTr Z h g) f := by
  unfold persTr
  rw [comp_S_l, assoc' f g (persPc Z h)]
  simp only [S_trans]

theorem persPre_comp (X : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) {y z : C} {ε δ : ℝ≥0}
    (g : hom y z δ) (f : hom (X.obj t) y ε) : persPre X h (comp g f) = comp g (persPre X h f) := by
  unfold persPre
  rw [comp_S_r, assoc' (persPc X h) f g]
  simp only [S_trans]

theorem persSlide (Y : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) {x z : C} {ε δ : ℝ≥0}
    (g : hom (Y.obj t) z ε) (f : hom x (Y.obj s) δ) :
    comp (persPre Y h g) f = comp g (persTr Y h f) := by
  unfold persPre persTr
  rw [comp_S_l, comp_S_r, assoc' f (persPc Y h) g]
  simp only [S_trans]

theorem persPre_tr (X Y : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) {s' t' : ℝ} (h' : s' ≤ t')
    {δ : ℝ≥0} (f : hom (X.obj t) (Y.obj s') δ) :
    persPre X h (persTr Y h' f) = persTr Y h' (persPre X h f) := by
  unfold persPre persTr
  rw [comp_S_l, comp_S_r, assoc' (persPc X h) f (persPc Y h'), ← LPCat.assoc (persPc X h) f (persPc Y h')]
  simp only [S_trans]

theorem persHomZero_tr (Y : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) {x : C} (f : x ⟶ Y.obj s) :
    homZero (f ≫ Y.map (homOfLE h)) = persTr Y h (homZero f) :=
  homZero_comp f (Y.map (homOfLE h))

theorem persHomZero_pre (X : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) {y : C} (f : X.obj t ⟶ y) :
    homZero (X.map (homOfLE h) ≫ f) = persPre X h (homZero f) :=
  homZero_comp (X.map (homOfLE h)) f


/-- Composition in `C^ℝ`: `g ∘ f` at `r` is `Y(r+a) → Z((r+a)+c)` composed with `f r`, then
re-indexed to `Z (r + (a + c))`. -/
def pComp {X Y Z : ℝ ⥤ C} {a b c d : ℝ≥0} (g : PersistentHom Y Z c d)
    (f : PersistentHom X Y a b) : ∀ r : ℝ, hom (X.obj r) (Z.obj (r + ((a + c : ℝ≥0) : ℝ))) (b + d) :=
  fun r => S (le_of_eq (add_zero _))
    (comp (persPc Z (le_of_eq (by push_cast; ring))) (comp (g.1 (r + a)) (f.1 r)))

/-- Shift in `C^ℝ`. -/
def pS {X Y : ℝ ⥤ C} {a b a' b' : ℝ≥0} (ha : a ≤ a') (hb : b ≤ b')
    (f : PersistentHom X Y a b) : ∀ r : ℝ, hom (X.obj r) (Y.obj (r + (a' : ℝ))) b' :=
  fun r => S (by simpa using hb)
    (comp (persPc Y (add_le_add le_rfl (by exact_mod_cast ha) : r + (a : ℝ) ≤ r + (a' : ℝ))) (f.1 r))

/-- A natural transformation as a `0`-`0`-morphism. -/
def pZero {X Y : ℝ ⥤ C} (f : X ⟶ Y) : ∀ r : ℝ, hom (X.obj r) (Y.obj (r + ((0 : ℝ≥0) : ℝ))) 0 :=
  fun r => homZero (f.app r ≫ Y.map (homOfLE (by simp)))

/-- Naturality of a persistent morphism, in `persTr`/`persPre` form. -/
theorem persNat {X Y : ℝ ⥤ C} {ε δ : ℝ≥0} (α : PersistentHom X Y ε δ) (r s : ℝ) (h : r ≤ s) :
    persTr Y (add_le_add_left h (ε : ℝ)) (α.1 r) = persPre X h (α.1 s) := α.2 r s h

theorem pComp_eq {X Y Z : ℝ ⥤ C} {a b c d : ℝ≥0} (g : PersistentHom Y Z c d)
    (f : PersistentHom X Y a b) (r : ℝ) :
    pComp g f r = persTr Z (le_of_eq (by push_cast; ring)) (comp (g.1 (r + a)) (f.1 r)) := rfl

theorem pS_eq {X Y : ℝ ⥤ C} {a b a' b' : ℝ≥0} (ha : a ≤ a') (hb : b ≤ b')
    (f : PersistentHom X Y a b) (r : ℝ) :
    pS ha hb f r = S hb (persTr Y (add_le_add le_rfl (by exact_mod_cast ha) : r + (a : ℝ) ≤ r + (a' : ℝ))
      (f.1 r)) := by
  unfold pS persTr
  rw [S_trans]

theorem pZero_eq_tr {Y Z : ℝ ⥤ C} (f : Y ⟶ Z) (t : ℝ) :
    pZero f t = persTr Z (by simp) (homZero (f.app t)) := persHomZero_tr Z _ (f.app t)

theorem persHomZero_id_app (Y : ℝ ⥤ C) (t : ℝ) : homZero ((𝟙 Y : Y ⟶ Y).app t) = idHom (Y.obj t) := rfl

/-! ### GROUP A: the data are well defined -/

theorem pComp_prop {X Y Z : ℝ ⥤ C} {a b c d : ℝ≥0} (g : PersistentHom Y Z c d)
    (f : PersistentHom X Y a b) :
    ∀ (r s : ℝ) (h : r ≤ s),
      S (le_of_eq (add_zero (b + d)))
          (comp (homZero (Z.map (homOfLE (add_le_add_left h ((a + c : ℝ≥0) : ℝ)))))
            (pComp g f r)) =
        S (le_of_eq (zero_add (b + d))) (comp (pComp g f s) (homZero (X.map (homOfLE h)))) := by
  intro r s h
  change persTr Z _ (pComp g f r) = persPre X h (pComp g f s)
  have hr := persNat f r s h
  have hg := persNat g (r + a) (s + a) (add_le_add_left h _)
  rw [pComp_eq, pComp_eq, persTr_trans, persPre_tr, persPre_comp, ← hr, ← persSlide, ← hg, ← persTr_comp, persTr_trans]

theorem pS_prop {X Y : ℝ ⥤ C} {a b a' b' : ℝ≥0} (ha : a ≤ a') (hb : b ≤ b')
    (f : PersistentHom X Y a b) :
    ∀ (r s : ℝ) (h : r ≤ s),
      S (le_of_eq (add_zero b'))
          (comp (homZero (Y.map (homOfLE (add_le_add_left h (a' : ℝ))))) (pS ha hb f r)) =
        S (le_of_eq (zero_add b')) (comp (pS ha hb f s) (homZero (X.map (homOfLE h)))) := by
  intro r s h
  change persTr Y _ (pS ha hb f r) = persPre X h (pS ha hb f s)
  rw [pS_eq, pS_eq, persTr_S, persPre_S, persTr_trans, persPre_tr, ← persNat f r s h, persTr_trans]

theorem pZero_prop {X Y : ℝ ⥤ C} (f : X ⟶ Y) :
    ∀ (r s : ℝ) (h : r ≤ s),
      S (le_of_eq (add_zero 0))
          (comp (homZero (Y.map (homOfLE (add_le_add_left h (((0 : ℝ≥0)) : ℝ))))) (pZero f r)) =
        S (le_of_eq (zero_add 0)) (comp (pZero f s) (homZero (X.map (homOfLE h)))) := by
  intro r s h
  change persTr Y _ (pZero f r) = persPre X h (pZero f s)
  unfold pZero
  rw [← persHomZero_tr, ← persHomZero_pre]
  congr 1
  rw [← Category.assoc (X.map (homOfLE h)), f.naturality, Category.assoc, Category.assoc,
    ← Y.map_comp, ← Y.map_comp]
  rfl

/-- Packaged composition. -/
def pCompH {X Y Z : ℝ ⥤ C} {a b c d : ℝ≥0} (g : PersistentHom Y Z c d)
    (f : PersistentHom X Y a b) : PersistentHom X Z (a + c) (b + d) :=
  ⟨pComp g f, pComp_prop g f⟩

/-- Packaged shift. -/
def pSH {X Y : ℝ ⥤ C} {a b a' b' : ℝ≥0} (ha : a ≤ a') (hb : b ≤ b')
    (f : PersistentHom X Y a b) : PersistentHom X Y a' b' :=
  ⟨pS ha hb f, pS_prop ha hb f⟩

/-- Packaged `0`-morphism. -/
def pZeroH {X Y : ℝ ⥤ C} (f : X ⟶ Y) : PersistentHom X Y 0 0 := ⟨pZero f, pZero_prop f⟩

/-- Inverse of `pZero`: the naturality of the underlying components. -/
theorem pUnzero_nat {X Y : ℝ ⥤ C} (α : PersistentHom X Y 0 0) {r s : ℝ} (h : r ⟶ s) :
    X.map h ≫ (homZero.symm (α.1 s) ≫ Y.map (homOfLE (by simp))) =
      (homZero.symm (α.1 r) ≫ Y.map (homOfLE (by simp))) ≫ Y.map h := by
  apply homZero.injective
  have hn := persNat α r s (leOfHom h)
  obtain ⟨⟨hle⟩⟩ := h
  change homZero (X.map (homOfLE hle) ≫ _) = homZero ((_ ≫ _) ≫ Y.map (homOfLE hle))
  change persTr Y _ (α.1 r) = persPre X (leOfHom (homOfLE hle)) (α.1 s) at hn
  rw [← Category.assoc, persHomZero_tr, persHomZero_pre, Equiv.apply_symm_apply, Category.assoc,
    ← Y.map_comp]
  erw [persHomZero_tr, Equiv.apply_symm_apply]
  rw [← hn, persTr_trans]

omit [LPCat C] in
theorem persMapLoop (Y : ℝ ⥤ C) {a : ℝ} (f : a ⟶ a) : Y.map f = 𝟙 _ := by
  rw [Subsingleton.elim f (𝟙 a)]; exact Y.map_id a

def pUnzero {X Y : ℝ ⥤ C} (α : PersistentHom X Y 0 0) : X ⟶ Y where
  app r := homZero.symm (α.1 r) ≫ Y.map (homOfLE (by simp))
  naturality := fun _ _ h => pUnzero_nat α h

theorem pUnzero_zero {X Y : ℝ ⥤ C} (f : X ⟶ Y) : pUnzero (pZeroH f) = f := by
  ext r
  change homZero.symm (homZero (f.app r ≫ Y.map _)) ≫ Y.map _ = f.app r
  rw [Equiv.symm_apply_apply, Category.assoc, ← Y.map_comp]
  rw [persMapLoop, Category.comp_id]

theorem pZero_unzero {X Y : ℝ ⥤ C} (α : PersistentHom X Y 0 0) : pZeroH (pUnzero α) = α := by
  apply Subtype.ext
  funext r
  change homZero ((homZero.symm (α.1 r) ≫ Y.map _) ≫ Y.map _) = α.1 r
  rw [Category.assoc, ← Y.map_comp]
  rw [persMapLoop, Category.comp_id]
  exact Equiv.apply_symm_apply _ _

/-! ### GROUP B: unit laws and compatibility of `homZero` -/

theorem p_id_comp {X Y : ℝ ⥤ C} {a b : ℝ≥0} (f : PersistentHom X Y a b) :
    pSH (le_of_eq (add_zero a)) (le_of_eq (add_zero b)) (pCompH (pZeroH (𝟙 Y)) f) = f := by
  apply Subtype.ext
  funext r
  change pS (le_of_eq (add_zero a)) (le_of_eq (add_zero b)) (pCompH (pZeroH (𝟙 Y)) f) r = f.1 r
  rw [pS_eq]
  change S _ (persTr Y _ (pComp (pZeroH (𝟙 Y)) f r)) = f.1 r
  rw [pComp_eq]
  change S _ (persTr Y _ (persTr Y _ (comp (pZero (𝟙 Y) (r + a)) (f.1 r)))) = f.1 r
  rw [pZero_eq_tr, persHomZero_id_app, ← persTr_comp, id_comp']
  simp only [persTr_S, S_trans, persTr_trans, persTr_refl, S_refl]

theorem p_comp_id {X Y : ℝ ⥤ C} {a b : ℝ≥0} (f : PersistentHom X Y a b) :
    pSH (le_of_eq (zero_add a)) (le_of_eq (zero_add b)) (pCompH f (pZeroH (𝟙 X))) = f := by
  apply Subtype.ext
  funext r
  change pS (le_of_eq (zero_add a)) (le_of_eq (zero_add b)) (pCompH f (pZeroH (𝟙 X))) r = f.1 r
  rw [pS_eq]
  change S _ (persTr Y _ (pComp f (pZeroH (𝟙 X)) r)) = f.1 r
  rw [pComp_eq]
  change S _ (persTr Y _ (persTr Y _ (comp (f.1 (r + ((0 : ℝ≥0) : ℝ))) (pZero (𝟙 X) r)))) = f.1 r
  have hn := persNat f r (r + ((0 : ℝ≥0) : ℝ)) (by simp)
  rw [pZero_eq_tr, persHomZero_id_app, ← persSlide, comp_id', ← hn]
  simp only [persTr_S, S_trans, persTr_trans, persTr_refl, S_refl]

theorem p_homZero_comp {X Y Z : ℝ ⥤ C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pZeroH (f ≫ g) = pSH (le_of_eq (add_zero 0)) (le_of_eq (add_zero 0))
      (pCompH (pZeroH g) (pZeroH f)) := by
  apply Subtype.ext
  funext r
  change pZero (f ≫ g) r = pS (le_of_eq (add_zero 0)) (le_of_eq (add_zero 0))
    (pCompH (pZeroH g) (pZeroH f)) r
  rw [pS_eq]
  change _ = S _ (persTr Z _ (pComp (pZeroH g) (pZeroH f) r))
  rw [pComp_eq]
  change _ = S _ (persTr Z _ (persTr Z _ (comp (pZero g (r + ((0 : ℝ≥0) : ℝ))) (pZero f r))))
  have hc : comp (homZero (g.app r)) (homZero (f.app r)) =
      S (le_of_eq (add_zero 0).symm) (homZero (f.app r ≫ g.app r)) :=
    eq_S_symm (add_zero (0 : ℝ≥0)) (homZero_comp (f.app r) (g.app r)).symm
  have hn : persPre Y (by simp : r ≤ r + ((0 : ℝ≥0) : ℝ)) (homZero (g.app (r + ((0 : ℝ≥0) : ℝ)))) =
      persTr Z (by simp : r ≤ r + ((0 : ℝ≥0) : ℝ)) (homZero (g.app r)) := by
    rw [← persHomZero_pre, ← persHomZero_tr]
    congr 1
    exact g.naturality _
  rw [pZero_eq_tr, pZero_eq_tr g, pZero_eq_tr f, ← persTr_comp, ← persSlide, hn, ← persTr_comp, hc]
  rw [show (f ≫ g).app r = f.app r ≫ g.app r from rfl]
  simp only [persTr_S, S_trans, persTr_trans, persTr_refl, S_refl]

/-! ### GROUP C: associativity and shifts -/

theorem p_assoc {X Y Z W : ℝ ⥤ C} {a b c d e e' : ℝ≥0} (f : PersistentHom X Y a b)
    (g : PersistentHom Y Z c d) (h : PersistentHom Z W e e') :
    pSH (le_of_eq (add_assoc a c e)) (le_of_eq (add_assoc b d e')) (pCompH h (pCompH g f)) =
      pCompH (pCompH h g) f := by
  apply Subtype.ext
  funext r
  change pS (le_of_eq (add_assoc a c e)) (le_of_eq (add_assoc b d e')) (pCompH h (pCompH g f)) r =
    pComp (pCompH h g) f r
  rw [pS_eq]
  change S _ (persTr W _ (pComp h (pCompH g f) r)) = _
  rw [pComp_eq h (pCompH g f), pComp_eq (pCompH h g) f]
  change S _ (persTr W _ (persTr W _ (comp (h.1 (r + ((a + c : ℝ≥0) : ℝ))) (pComp g f r)))) =
    persTr W _ (comp (pComp h g (r + a)) (f.1 r))
  rw [pComp_eq g f, pComp_eq h g, ← persTr_comp]
  have hn := persNat h ((r + a) + c) (r + ((a + c : ℝ≥0) : ℝ)) (le_of_eq (by push_cast; ring))
  rw [← persSlide, ← hn, ← persTr_comp, assoc' (f.1 r) (g.1 (r + a)) (h.1 ((r + a) + c))]
  simp only [persTr_S, S_trans, persTr_trans, S_refl]

theorem p_S_refl {X Y : ℝ ⥤ C} {a b : ℝ≥0} (f : PersistentHom X Y a b) :
    pSH le_rfl le_rfl f = f := by
  apply Subtype.ext
  funext r
  change pS le_rfl le_rfl f r = f.1 r
  rw [pS_eq]
  simp only [persTr_refl, S_refl]

theorem p_S_trans {X Y : ℝ ⥤ C} {a b a' b' a'' b'' : ℝ≥0} (h1a : a ≤ a') (h1b : b ≤ b')
    (h2a : a' ≤ a'') (h2b : b' ≤ b'') (f : PersistentHom X Y a b) :
    pSH h2a h2b (pSH h1a h1b f) = pSH (h1a.trans h2a) (h1b.trans h2b) f := by
  apply Subtype.ext
  funext r
  change pS h2a h2b (pSH h1a h1b f) r = pS (h1a.trans h2a) (h1b.trans h2b) f r
  rw [pS_eq, pS_eq]
  change S _ (persTr Y _ (pS h1a h1b f r)) = _
  rw [pS_eq]
  simp only [persTr_S, S_trans, persTr_trans]

theorem p_comp_S {X Y Z : ℝ ⥤ C} {a b a' b' c d c' d' : ℝ≥0} (ha : a ≤ a') (hb : b ≤ b')
    (hc : c ≤ c') (hd : d ≤ d') (f : PersistentHom X Y a b) (g : PersistentHom Y Z c d) :
    pCompH (pSH hc hd g) (pSH ha hb f) =
      pSH (add_le_add ha hc) (add_le_add hb hd) (pCompH g f) := by
  apply Subtype.ext
  funext r
  change pComp (pSH hc hd g) (pSH ha hb f) r = pS (add_le_add ha hc) (add_le_add hb hd) (pCompH g f) r
  rw [pComp_eq, pS_eq]
  change _ = S _ (persTr Z _ (pComp g f r))
  rw [pComp_eq]
  change persTr Z _ (comp (pS hc hd g (r + a')) (pS ha hb f r)) = _
  rw [pS_eq, pS_eq, comp_S_l, comp_S_r]
  have hn := persNat g (r + a) (r + a') (add_le_add le_rfl (by exact_mod_cast ha))
  rw [← persTr_comp, ← persSlide, ← hn, ← persTr_comp]
  simp only [persTr_S, S_trans, persTr_trans]


/-- Definition 5.1.7: `C^ℝ` is a locally `ℝ≥0 × ℝ≥0`-persistent category, whose underlying
category is the category of functors `ℝ ⥤ C₀`. -/
def persistentLQPCat (C : Type u) [Category.{v} C] [LPCat C] : LQPCat (ℝ≥0 × ℝ≥0) (ℝ ⥤ C) where
  hom := fun X Y q => PersistentHom X Y q.1 q.2
  homZero := ⟨pZeroH, pUnzero, pUnzero_zero, pZero_unzero⟩
  comp := fun {_ _ _ ε δ} g f => pCompH g f
  S := fun {_ _ ε δ} h f => pSH h.1 h.2 f
  id_comp := fun f => p_id_comp f
  comp_id := fun f => p_comp_id f
  assoc := fun f g h => p_assoc f g h
  S_refl := fun f => p_S_refl f
  S_trans := fun h₁ h₂ f => p_S_trans h₁.1 h₁.2 h₂.1 h₂.2 f
  comp_S := fun hε hδ f g => p_comp_S hε.1 hε.2 hδ.1 hδ.2 f g
  homZero_comp := fun f g => p_homZero_comp f g

theorem exists_lqpcat_persistent :
    ∃ L : LQPCat (ℝ≥0 × ℝ≥0) (ℝ ⥤ C), ∀ (X Y : ℝ ⥤ C) (ε δ : ℝ≥0),
      L.hom X Y (ε, δ) = PersistentHom X Y ε δ :=
  ⟨persistentLQPCat C, fun _ _ _ _ => rfl⟩

/-- The class `W^→` of natural transformations of `ℝ ⥤ C` all of whose components lie in `W`
(Definition 5.1.7). -/
def levelwiseProp (W : MorphismProperty C) : MorphismProperty (ℝ ⥤ C) :=
  fun _ _ α => ∀ r, W (α.app r)

/-- The superlinear family `ε ↦ (v₁ ε, v₂ ε)` for `v = (v₁, v₂) ∈ ℝ≥0 × ℝ≥0`. -/
def pairFamily (v : ℝ≥0 × ℝ≥0) : SuperlinearFamily (ℝ≥0 × ℝ≥0) where
  toFun ε := (ε * v.1, ε * v.2)
  mono a b h := ⟨mul_le_mul_of_nonneg_right h zero_le, mul_le_mul_of_nonneg_right h zero_le⟩
  map_zero := by simp
  superadd a b := by simp [add_mul]

section PersPow
variable (hC : PoweredByRepresentables C)

/-- The power `Y^{(ε,δ)}(s) = (Y (s + ε))^δ` of a persistent object. -/
def persPowObj (q : ℝ≥0 × ℝ≥0) (Y : ℝ ⥤ C) : ℝ ⥤ C where
  obj s := (hC.pow q.2).obj (Y.obj (s + q.1))
  map {s s'} h := (hC.pow q.2).map (Y.map (homOfLE (add_le_add_left (leOfHom h) (q.1 : ℝ))))
  map_id := by intro s; simp
  map_comp := by intros; simp [← Functor.map_comp]

/-- The power functor. -/
def persPow (q : ℝ≥0 × ℝ≥0) : (ℝ ⥤ C) ⥤ (ℝ ⥤ C) where
  obj Y := persPowObj hC q Y
  map {Y Y'} α :=
    { app := fun s => (hC.pow q.2).map (α.app (s + q.1))
      naturality := by
        intro s s' h
        simp only [persPowObj, ← Functor.map_comp]
        rw [α.naturality] }
  map_id := by intros; ext; simp [persPowObj]
  map_comp := by intros; ext; simp [persPowObj]

theorem powIso_tr (x : C) {Y : ℝ ⥤ C} {s t : ℝ} (h : s ≤ t) (δ b : ℝ≥0)
    (u : hom x ((hC.pow δ).obj (Y.obj s)) b) :
    hC.powIso x (Y.obj t) δ b
      (S (le_of_eq (add_zero b)) (comp (homZero ((hC.pow δ).map (Y.map (homOfLE h)))) u)) =
    persTr Y h (hC.powIso x (Y.obj s) δ b u) := by
  rw [hC.powIso_y (Y.map (homOfLE h)) u]
  rfl

theorem powIso_pre (X : ℝ ⥤ C) {s t : ℝ} (h : s ≤ t) (y : C) (δ b : ℝ≥0)
    (u : hom (X.obj t) ((hC.pow δ).obj y) b) :
    hC.powIso (X.obj s) y δ b (persPre X h u) = persPre X h (hC.powIso (X.obj t) y δ b u) := by
  unfold persPre
  rw [hC.powIso_S, hC.powIso_x]
  simp only [S_trans]

/-- Pointwise forward map of the powering equivalence (without naturality). -/
def pwFwdFun (q : ℝ≥0 × ℝ≥0) (x y : ℝ ⥤ C) (a b : ℝ≥0)
    (α : ∀ s : ℝ, hom (x.obj s) ((persPowObj hC q y).obj (s + a)) b) :
    ∀ s : ℝ, hom (x.obj s) (y.obj (s + ((q.1 + a : ℝ≥0) : ℝ))) (q.2 + b) :=
  fun s => persTr y (le_of_eq (by push_cast; ring))
    (hC.powIso (x.obj s) (y.obj (s + a + q.1)) q.2 b (α s))

/-- Pointwise inverse. -/
def pwBwdFun (q : ℝ≥0 × ℝ≥0) (x y : ℝ ⥤ C) (a b : ℝ≥0)
    (β : ∀ s : ℝ, hom (x.obj s) (y.obj (s + ((q.1 + a : ℝ≥0) : ℝ))) (q.2 + b)) :
    ∀ s : ℝ, hom (x.obj s) ((persPowObj hC q y).obj (s + a)) b :=
  fun s => (hC.powIso (x.obj s) (y.obj (s + a + q.1)) q.2 b).symm
    (persTr y (le_of_eq (by push_cast; ring)) (β s))

theorem pwFwd_nat (q : ℝ≥0 × ℝ≥0) (x y : ℝ ⥤ C) (a b : ℝ≥0)
    (α : PersistentHom x (persPowObj hC q y) a b) (r s : ℝ) (h : r ≤ s) :
    persTr y (add_le_add_left h ((q.1 + a : ℝ≥0) : ℝ)) (pwFwdFun hC q x y a b α.1 r) =
      persPre x h (pwFwdFun hC q x y a b α.1 s) := by
  have hα := persNat α r s h
  have H := congrArg (hC.powIso (x.obj r) (y.obj (s + a + q.1)) q.2 b) hα
  change hC.powIso (x.obj r) (y.obj (s + a + q.1)) q.2 b
    (S (le_of_eq (add_zero b)) (comp (homZero ((hC.pow q.2).map (y.map (homOfLE _)))) (α.1 r))) = _ at H
  erw [powIso_tr hC, powIso_pre hC] at H
  unfold pwFwdFun
  rw [persTr_trans, persPre_tr, ← H, persTr_trans]

theorem pwBwd_nat (q : ℝ≥0 × ℝ≥0) (x y : ℝ ⥤ C) (a b : ℝ≥0)
    (β : PersistentHom x y (q.1 + a) (q.2 + b)) (r s : ℝ) (h : r ≤ s) :
    persTr (persPowObj hC q y) (add_le_add_left h (a : ℝ)) (pwBwdFun hC q x y a b β.1 r) =
      persPre x h (pwBwdFun hC q x y a b β.1 s) := by
  apply (hC.powIso (x.obj r) (y.obj (s + a + q.1)) q.2 b).injective
  have hβ := persNat β r s h
  change hC.powIso (x.obj r) (y.obj (s + a + q.1)) q.2 b
    (S (le_of_eq (add_zero b)) (comp (homZero ((hC.pow q.2).map (y.map (homOfLE _))))
      (pwBwdFun hC q x y a b β.1 r))) = _
  erw [powIso_tr hC, powIso_pre hC]
  unfold pwBwdFun
  simp only [Equiv.apply_symm_apply]
  rw [persTr_trans, persPre_tr, ← hβ, persTr_trans]

/-- The powering equivalence on persistent homs. -/
def pwEquiv (q : ℝ≥0 × ℝ≥0) (x y : ℝ ⥤ C) (a b : ℝ≥0) :
    PersistentHom x (persPowObj hC q y) a b ≃ PersistentHom x y (q.1 + a) (q.2 + b) where
  toFun α := ⟨pwFwdFun hC q x y a b α.1, fun r s h => pwFwd_nat hC q x y a b α r s h⟩
  invFun β := ⟨pwBwdFun hC q x y a b β.1, fun r s h => pwBwd_nat hC q x y a b β r s h⟩
  left_inv α := by
    apply Subtype.ext; funext s
    simp only [pwBwdFun, pwFwdFun, persTr_trans, persTr_refl]
    exact Equiv.symm_apply_apply _ _
  right_inv β := by
    apply Subtype.ext; funext s
    simp only [pwBwdFun, pwFwdFun, persTr_trans, persTr_refl, Equiv.apply_symm_apply]

theorem pwEquiv_apply (q : ℝ≥0 × ℝ≥0) (x y : ℝ ⥤ C) (a b : ℝ≥0)
    (α : PersistentHom x (persPowObj hC q y) a b) (s : ℝ) :
    (pwEquiv hC q x y a b α).1 s = pwFwdFun hC q x y a b α.1 s := rfl

theorem pw_S (q : ℝ≥0 × ℝ≥0) (x y : ℝ ⥤ C) {r r' : ℝ≥0 × ℝ≥0} (h : r ≤ r')
    (u : PersistentHom x (persPowObj hC q y) r.1 r.2) :
    pwEquiv hC q x y r'.1 r'.2 (pSH h.1 h.2 u) =
      pSH (add_le_add le_rfl h).1 (add_le_add le_rfl h).2 (pwEquiv hC q x y r.1 r.2 u) := by
  apply Subtype.ext; funext s
  change pwFwdFun hC q x y r'.1 r'.2 (pS h.1 h.2 u) s =
    pS (add_le_add le_rfl h).1 (add_le_add le_rfl h).2 (pwEquiv hC q x y r.1 r.2 u) s
  unfold pwFwdFun
  rw [pS_eq, pS_eq, pwEquiv_apply]
  unfold pwFwdFun
  erw [hC.powIso_S]
  change persTr y _ (S _ (hC.powIso (x.obj s) (y.obj (s + r'.1 + q.1)) q.2 r.2 (S (le_of_eq (add_zero r.2))
      (comp (homZero ((hC.pow q.2).map (y.map (homOfLE _)))) (u.1 s))))) = _
  erw [powIso_tr hC]
  simp only [persTr_S, S_trans, persTr_trans]

theorem pw_x (q : ℝ≥0 × ℝ≥0) {x x' : ℝ ⥤ C} (y : ℝ ⥤ C) {r δ : ℝ≥0 × ℝ≥0}
    (v : PersistentHom x' x δ.1 δ.2) (u : PersistentHom x (persPowObj hC q y) r.1 r.2) :
    pwEquiv hC q x' y (δ + r).1 (δ + r).2 (pCompH u v) =
      pSH (le_of_eq (add_left_comm δ q r)).1 (le_of_eq (add_left_comm δ q r)).2
        (pCompH (pwEquiv hC q x y r.1 r.2 u) v) := by
  apply Subtype.ext; funext s
  change pwFwdFun hC q x' y (δ + r).1 (δ + r).2 (pComp u v) s =
    pS (le_of_eq (add_left_comm δ q r)).1 (le_of_eq (add_left_comm δ q r)).2
      (pCompH (pwEquiv hC q x y r.1 r.2 u) v) s
  unfold pwFwdFun
  rw [pComp_eq, pS_eq]
  change _ = S _ (persTr y _ (pComp (pwEquiv hC q x y r.1 r.2 u) v s))
  rw [pComp_eq]
  erw [powIso_tr hC]
  erw [hC.powIso_x]
  rw [pwEquiv_apply]
  unfold pwFwdFun
  rw [← persTr_comp]
  simp only [persTr_S, S_trans, persTr_trans]

theorem pw_y (q : ℝ≥0 × ℝ≥0) {x y y' : ℝ ⥤ C} {r : ℝ≥0 × ℝ≥0} (f : y ⟶ y')
    (u : PersistentHom x (persPowObj hC q y) r.1 r.2) :
    pwEquiv hC q x y' r.1 r.2
      (pSH (le_of_eq (add_zero r)).1 (le_of_eq (add_zero r)).2
        (pCompH (pZeroH ((persPow hC q).map f)) u)) =
      pSH (le_of_eq (add_zero (q + r))).1 (le_of_eq (add_zero (q + r))).2
        (pCompH (pZeroH f) (pwEquiv hC q x y r.1 r.2 u)) := by
  apply Subtype.ext; funext s
  change pwFwdFun hC q x y' r.1 r.2 (pS (le_of_eq (add_zero r)).1 (le_of_eq (add_zero r)).2
      (pCompH (pZeroH ((persPow hC q).map f)) u)) s =
    pS (le_of_eq (add_zero (q + r))).1 (le_of_eq (add_zero (q + r))).2
        (pCompH (pZeroH f) (pwEquiv hC q x y r.1 r.2 u)) s
  unfold pwFwdFun
  rw [pS_eq, pS_eq]
  change _ = S _ (persTr y' _ (pComp (pZeroH f) (pwEquiv hC q x y r.1 r.2 u) s))
  rw [pComp_eq]
  change _ = S _ (persTr y' _ (persTr y' _ (comp (pZero f (s + ↑(q.1 + r.1))) (pwFwdFun hC q x y r.1 r.2 u.1 s))))
  change persTr y' _ (hC.powIso (x.obj s) (y'.obj (s + r.1 + q.1)) q.2 r.2
      (S _ (persTr (persPowObj hC q y') _ (pComp (pZeroH ((persPow hC q).map f)) u s)))) = _
  erw [pComp_eq]
  erw [pZero_eq_tr]
  rw [show ∀ t, (pZeroH ((persPow hC q).map f)).1 t = pZero ((persPow hC q).map f) t from fun _ => rfl]
  erw [pZero_eq_tr]
  rw [← persTr_comp, ← persTr_comp]
  erw [persTr_trans, persTr_trans]
  erw [← persTr_S]
  erw [powIso_tr hC]
  erw [hC.powIso_y (f.app (s + ↑r.1 + ↑q.1)) (u.1 s)]
  unfold pwFwdFun
  rw [← persSlide, ← persHomZero_pre, f.naturality, persHomZero_tr, ← persTr_comp]
  simp only [persTr_S, S_trans, persTr_trans]

/-- `C^ℝ` is `ℝ≥0 × ℝ≥0`-powered by representables when `C` is. -/
def persistentQPowered : QPoweredByRepresentables (persistentLQPCat C) where
  pow := persPow hC
  powIso x y q r := pwEquiv hC q x y r.1 r.2
  powIso_S := fun {x y q r r'} h u => pw_S hC q x y h u
  powIso_x := fun {x x' y q r δ} v u => pw_x hC q y v u
  powIso_y := fun {x y y' q r} f u => pw_y hC q f u

theorem pairFamily_additive (v : ℝ≥0 × ℝ≥0) (a b : ℝ≥0) :
    (pairFamily v).toFun (a + b) = (pairFamily v).toFun a + (pairFamily v).toFun b := by
  simp [pairFamily, add_mul]

end PersPow

/-- Lemma 5.1.8: if `C` is powered by representables, so is `C^ℝ_v` (for any locally
persistent structure `L` on `ℝ ⥤ C` obtained from the canonical `ℝ≥0 × ℝ≥0`-persistent structure
`persistentLQPCat C` by change of enrichment along `v`).

The Lean statement fixes `LR` to be the structure of Definition 5.1.7 (instead of an arbitrary
structure with the same hom-sets, which does not determine the composition). -/
theorem persistent_powered (v : ℝ≥0 × ℝ≥0)
    (L : LPCat (ℝ ⥤ C)) (hL : IsChangeOfEnrichment (pairFamily v) (persistentLQPCat C) L)
    (hC : PoweredByRepresentables C) : Nonempty (@PoweredByRepresentables (ℝ ⥤ C) _ L) :=
  poweredByRepresentables_of_changeOfEnrichment (pairFamily v) (pairFamily_additive v)
    (persistentLQPCat C) (persistentQPowered hC) L hL

/-- The copower of a persistent object, obtained by translating backwards and applying
pointwise copower. -/
def persCopow (hC : CopoweredByRepresentables C) (q : ℝ≥0 × ℝ≥0) :
    (ℝ ⥤ C) ⥤ (ℝ ⥤ C) where
  obj X :=
    { obj s := (hC.copow q.2).obj (X.obj (s - q.1))
      map {s t} f := (hC.copow q.2).map (X.map (homOfLE (sub_le_sub_right (leOfHom f) _)))
      map_id := by intro s; simp
      map_comp := by intros; simp [← Functor.map_comp] }
  map {X Y} f :=
    { app s := (hC.copow q.2).map (f.app (s - q.1))
      naturality := by
        intro s t g
        simp only [← Functor.map_comp]
        rw [f.naturality] }
  map_id := by intros; ext; simp
  map_comp := by intros; ext; simp

/-- The pointwise forward map for the copower equivalence. -/
def persCopowFwd (hC : CopoweredByRepresentables C) (q : ℝ≥0 × ℝ≥0)
    (X Y : ℝ ⥤ C) (a b : ℝ≥0)
    (α : ∀ s : ℝ, hom ((persCopow hC q).obj X |>.obj s) (Y.obj (s + a)) b) :
    ∀ s : ℝ, hom (X.obj s) (Y.obj (s + ((q.1 + a : ℝ≥0) : ℝ))) (q.2 + b) :=
  fun s => persPre X (le_of_eq (by ring))
    (persTr Y (le_of_eq (by push_cast; ring))
      (hC.copowIso _ _ q.2 b (α (s + q.1))))

/-- The pointwise inverse candidate for the copower equivalence. -/
def persCopowBwd (hC : CopoweredByRepresentables C) (q : ℝ≥0 × ℝ≥0)
    (X Y : ℝ ⥤ C) (a b : ℝ≥0)
    (β : ∀ s : ℝ, hom (X.obj s) (Y.obj (s + ((q.1 + a : ℝ≥0) : ℝ))) (q.2 + b)) :
    ∀ s : ℝ, hom ((persCopow hC q).obj X |>.obj s) (Y.obj (s + a)) b :=
  fun s => (hC.copowIso _ _ q.2 b).symm
    (persTr Y (le_of_eq (by push_cast; ring)) (β (s - q.1)))

theorem copowIso_tr (hC : CopoweredByRepresentables C) (x : C) {Y : ℝ ⥤ C}
    {s t : ℝ} (h : s ≤ t) (δ b : ℝ≥0)
    (u : hom ((hC.copow δ).obj x) (Y.obj s) b) :
    hC.copowIso x (Y.obj t) δ b (persTr Y h u) =
      persTr Y h (hC.copowIso x (Y.obj s) δ b u) := by
  unfold persTr
  rw [hC.copowIso_S, hC.copowIso_y]
  simp only [S_trans]

theorem copowIso_pre (hC : CopoweredByRepresentables C) (X : ℝ ⥤ C)
    {s t : ℝ} (h : s ≤ t) (y : C) (δ b : ℝ≥0)
    (u : hom ((hC.copow δ).obj (X.obj t)) y b) :
    hC.copowIso (X.obj s) y δ b
      (S (le_of_eq (zero_add b)) (comp u (homZero ((hC.copow δ).map (X.map (homOfLE h)))))) =
      persPre X h (hC.copowIso (X.obj t) y δ b u) := by
  rw [hC.copowIso_x]
  rfl

section PersCopow
variable (hC : CopoweredByRepresentables C)

theorem cwFwd_nat (q : ℝ≥0 × ℝ≥0) (X Y : ℝ ⥤ C) (a b : ℝ≥0)
    (α : PersistentHom ((persCopow hC q).obj X) Y a b) (r s : ℝ) (h : r ≤ s) :
    persTr Y (add_le_add_left h ((q.1 + a : ℝ≥0) : ℝ)) (persCopowFwd hC q X Y a b α.1 r) =
      persPre X h (persCopowFwd hC q X Y a b α.1 s) := by
  have hα := persNat α (r + q.1) (s + q.1) (add_le_add_left h _)
  have H := congrArg (hC.copowIso (X.obj (r + q.1 - q.1)) (Y.obj (s + q.1 + a)) q.2 b) hα
  erw [copowIso_tr hC] at H
  unfold persPre at H
  erw [copowIso_pre hC] at H
  have h1 : r + (q.1 : ℝ) + (a : ℝ) ≤ s + (q.1 : ℝ) + (a : ℝ) := by linarith
  have h2 : s + (q.1 : ℝ) + (a : ℝ) ≤ s + (((q.1 + a : ℝ≥0)) : ℝ) := le_of_eq (by push_cast; ring)
  have h3 : r + (q.1 : ℝ) + (a : ℝ) ≤ s + (((q.1 + a : ℝ≥0)) : ℝ) := h1.trans h2
  unfold persCopowFwd
  rw [← persPre_tr, persTr_trans, persPre_trans]
  rw [show persTr Y (le_trans (le_of_eq (by push_cast; ring)) (add_le_add_left h ((q.1 + a : ℝ≥0) : ℝ)))
      (hC.copowIso (X.obj (r + (q.1 : ℝ) - q.1)) (Y.obj (r + (q.1 : ℝ) + a)) q.2 b (α.1 (r + q.1))) =
      persTr Y h2 (persTr Y h1 (hC.copowIso (X.obj (r + (q.1 : ℝ) - q.1)) (Y.obj (r + (q.1 : ℝ) + a)) q.2 b
        (α.1 (r + q.1)))) from (persTr_trans Y h1 h2 _).symm, H]
  rw [← persPre_tr]
  simp only [persPre_trans]

theorem cwBwd_nat (q : ℝ≥0 × ℝ≥0) (X Y : ℝ ⥤ C) (a b : ℝ≥0)
    (β : PersistentHom X Y (q.1 + a) (q.2 + b)) (r s : ℝ) (h : r ≤ s) :
    persTr Y (add_le_add_left h (a : ℝ)) (persCopowBwd hC q X Y a b β.1 r) =
      persPre ((persCopow hC q).obj X) h (persCopowBwd hC q X Y a b β.1 s) := by
  apply (hC.copowIso (X.obj (r - q.1)) (Y.obj (s + a)) q.2 b).injective
  have hβ := persNat β (r - q.1) (s - q.1) (sub_le_sub_right h _)
  erw [copowIso_tr hC]
  unfold persPre
  erw [copowIso_pre hC]
  unfold persCopowBwd
  simp only [Equiv.apply_symm_apply]
  rw [persPre_tr, ← hβ]
  simp only [persTr_trans]

/-- The copowering equivalence on persistent homs. -/
def cwEquiv (q : ℝ≥0 × ℝ≥0) (X Y : ℝ ⥤ C) (a b : ℝ≥0) :
    PersistentHom ((persCopow hC q).obj X) Y a b ≃ PersistentHom X Y (q.1 + a) (q.2 + b) where
  toFun α := ⟨persCopowFwd hC q X Y a b α.1, fun r s h => cwFwd_nat hC q X Y a b α r s h⟩
  invFun β := ⟨persCopowBwd hC q X Y a b β.1, fun r s h => cwBwd_nat hC q X Y a b β r s h⟩
  left_inv α := by
    apply Subtype.ext; funext s
    have hα := persNat α (s - q.1 + q.1) s (le_of_eq (by ring))
    have H := congrArg (hC.copowIso (X.obj (s - q.1 + q.1 - q.1)) (Y.obj (s + a)) q.2 b) hα
    erw [copowIso_tr hC] at H
    unfold persPre at H
    erw [copowIso_pre hC] at H
    change (persCopowBwd hC q X Y a b (persCopowFwd hC q X Y a b α.1)) s = α.1 s
    unfold persCopowBwd persCopowFwd
    rw [← persPre_tr, persTr_trans, H, persPre_trans, persPre_refl]
    exact Equiv.symm_apply_apply _ _
  right_inv β := by
    apply Subtype.ext; funext s
    have hβ := persNat β (s + q.1 - q.1) s (le_of_eq (by ring))
    change (persCopowFwd hC q X Y a b (persCopowBwd hC q X Y a b β.1)) s = β.1 s
    unfold persCopowBwd persCopowFwd
    simp only [Equiv.apply_symm_apply]
    rw [persTr_trans, hβ, persPre_trans, persPre_refl]

theorem cwEquiv_apply (q : ℝ≥0 × ℝ≥0) (X Y : ℝ ⥤ C) (a b : ℝ≥0)
    (α : PersistentHom ((persCopow hC q).obj X) Y a b) (s : ℝ) :
    (cwEquiv hC q X Y a b α).1 s = persCopowFwd hC q X Y a b α.1 s := rfl

theorem cw_S (q : ℝ≥0 × ℝ≥0) (X Y : ℝ ⥤ C) {r r' : ℝ≥0 × ℝ≥0} (h : r ≤ r')
    (u : PersistentHom ((persCopow hC q).obj X) Y r.1 r.2) :
    cwEquiv hC q X Y r'.1 r'.2 (pSH h.1 h.2 u) =
      pSH (add_le_add le_rfl h).1 (add_le_add le_rfl h).2 (cwEquiv hC q X Y r.1 r.2 u) := by
  apply Subtype.ext; funext s
  change persCopowFwd hC q X Y r'.1 r'.2 (pS h.1 h.2 u) s =
    pS (add_le_add le_rfl h).1 (add_le_add le_rfl h).2 (cwEquiv hC q X Y r.1 r.2 u) s
  unfold persCopowFwd
  rw [pS_eq, pS_eq, cwEquiv_apply]
  unfold persCopowFwd
  erw [hC.copowIso_S]
  erw [copowIso_tr hC]
  simp only [persTr_S, persPre_S, S_trans, persTr_trans, ← persPre_tr]

theorem cI_transport (q : ℝ≥0 × ℝ≥0) (X Y : ℝ ⥤ C) (a b : ℝ≥0)
    (α : PersistentHom ((persCopow hC q).obj X) Y a b) (t t' : ℝ) (h : t ≤ t') :
    persTr Y (add_le_add_left h (a : ℝ))
        (hC.copowIso (X.obj (t - q.1)) (Y.obj (t + a)) q.2 b (α.1 t)) =
      persPre X (sub_le_sub_right h _)
        (hC.copowIso (X.obj (t' - q.1)) (Y.obj (t' + a)) q.2 b (α.1 t')) := by
  have hα := persNat α t t' h
  have H := congrArg (hC.copowIso (X.obj (t - q.1)) (Y.obj (t' + a)) q.2 b) hα
  erw [copowIso_tr hC] at H
  unfold persPre at H
  erw [copowIso_pre hC] at H
  exact H

theorem f_slide {X X' : ℝ ⥤ C} (f : X' ⟶ X) {s a : ℝ} (h : s ≤ a) {y : C} {δ : ℝ≥0}
    (P : hom (X.obj a) y δ) :
    persPre X' h (comp P (homZero (f.app a))) = comp (persPre X h P) (homZero (f.app s)) := by
  rw [persPre_comp, ← persHomZero_pre, show X'.map (homOfLE h) ≫ f.app a = f.app s ≫ X.map (homOfLE h)
    from f.naturality _, persHomZero_tr, persSlide]

theorem cw_x (q : ℝ≥0 × ℝ≥0) {X X' : ℝ ⥤ C} (Y : ℝ ⥤ C) {r : ℝ≥0 × ℝ≥0} (f : X' ⟶ X)
    (u : PersistentHom ((persCopow hC q).obj X) Y r.1 r.2) :
    cwEquiv hC q X' Y r.1 r.2
      (pSH (le_of_eq (zero_add r)).1 (le_of_eq (zero_add r)).2
        (pCompH u (pZeroH ((persCopow hC q).map f)))) =
      pSH (le_of_eq (zero_add (q + r))).1 (le_of_eq (zero_add (q + r))).2
        (pCompH (cwEquiv hC q X Y r.1 r.2 u) (pZeroH f)) := by
  apply Subtype.ext; funext s
  change persCopowFwd hC q X' Y r.1 r.2 (pS (le_of_eq (zero_add r)).1 (le_of_eq (zero_add r)).2
      (pCompH u (pZeroH ((persCopow hC q).map f)))) s =
    pS (le_of_eq (zero_add (q + r))).1 (le_of_eq (zero_add (q + r))).2
        (pCompH (cwEquiv hC q X Y r.1 r.2 u) (pZeroH f)) s
  unfold persCopowFwd
  rw [pS_eq, pS_eq]
  change _ = S _ (persTr Y _ (pComp (cwEquiv hC q X Y r.1 r.2 u) (pZeroH f) s))
  rw [pComp_eq]
  change _ = S _ (persTr Y _ (persTr Y _ (comp (persCopowFwd hC q X Y r.1 r.2 u.1 (s + ((0 : ℝ≥0) : ℝ)))
    (pZero f s))))
  change persPre X' _ (persTr Y _ (hC.copowIso _ _ q.2 r.2 (S _ (persTr Y _
    (persTr Y _ (comp (u.1 (s + q.1 + ((0 : ℝ≥0) : ℝ))) (pZero ((persCopow hC q).map f) (s + q.1))))))))= _
  rw [pZero_eq_tr, pZero_eq_tr]
  rw [← persSlide]
  erw [← persSlide]
  simp only [← persTr_S]
  erw [copowIso_tr hC, copowIso_tr hC]
  erw [hC.copowIso_x]
  erw [copowIso_pre hC]
  simp only [persTr_S, persTr_comp]
  rw [persPre_S, f_slide]
  congr 2
  unfold persCopowFwd
  have hT := cI_transport hC q X Y r.1 r.2 u (s + q.1 + ((0 : ℝ≥0) : ℝ)) (s + ((0 : ℝ≥0) : ℝ) + q.1)
    (le_of_eq (by ring))
  simp only [← persPre_tr, persTr_trans, persPre_trans]
  have e1 : ∀ {M : ℝ} (T : (s + q.1 + ((0 : ℝ≥0) : ℝ)) + r.1 ≤ M) (T2 : (s + ((0 : ℝ≥0) : ℝ) + q.1) + r.1 ≤ M),
      persTr Y T (hC.copowIso (X.obj (s + ↑q.1 + ↑(0 : ℝ≥0) - ↑q.1)) (Y.obj (s + ↑q.1 + ↑(0 : ℝ≥0) + ↑r.1)) q.2 r.2
        (u.1 (s + q.1 + ((0 : ℝ≥0) : ℝ)))) =
      persTr Y T2 (persTr Y (le_of_eq (by ring) : (s + q.1 + ((0 : ℝ≥0) : ℝ)) + r.1 ≤ (s + ((0 : ℝ≥0) : ℝ) + q.1) + r.1) (hC.copowIso (X.obj (s + ↑q.1 + ↑(0 : ℝ≥0) - ↑q.1)) (Y.obj (s + ↑q.1 + ↑(0 : ℝ≥0) + ↑r.1)) q.2 r.2
        (u.1 (s + q.1 + ((0 : ℝ≥0) : ℝ))))) := by
    intro M T T2
    rw [persTr_trans]
  rw [e1 _ (le_of_eq (by push_cast; ring)), hT]
  simp only [← persPre_tr, persTr_trans, persPre_trans]

theorem cw_y (q : ℝ≥0 × ℝ≥0) (X : ℝ ⥤ C) {Y Y' : ℝ ⥤ C} {r δ : ℝ≥0 × ℝ≥0}
    (v : PersistentHom Y Y' δ.1 δ.2) (u : PersistentHom ((persCopow hC q).obj X) Y r.1 r.2) :
    cwEquiv hC q X Y' (r + δ).1 (r + δ).2 (pCompH v u) =
      pSH (le_of_eq (add_assoc q r δ)).1 (le_of_eq (add_assoc q r δ)).2
        (pCompH v (cwEquiv hC q X Y r.1 r.2 u)) := by
  apply Subtype.ext; funext s
  change persCopowFwd hC q X Y' (r + δ).1 (r + δ).2 (pComp v u) s =
    pS (le_of_eq (add_assoc q r δ)).1 (le_of_eq (add_assoc q r δ)).2
      (pCompH v (cwEquiv hC q X Y r.1 r.2 u)) s
  unfold persCopowFwd
  rw [pS_eq]
  change _ = S _ (persTr Y' _ (pComp v (cwEquiv hC q X Y r.1 r.2 u) s))
  rw [pComp_eq]
  change persPre X _ (persTr Y' _ (hC.copowIso _ _ q.2 (r + δ).2
    (persTr Y' _ (comp (v.1 (s + q.1 + r.1)) (u.1 (s + q.1)))))) = _
  erw [copowIso_tr hC, hC.copowIso_y]
  erw [pComp_eq]
  change _ = S _ (persTr Y' _ (persTr Y' _ (comp (v.1 (s + ((q.1 + r.1 : ℝ≥0) : ℝ)))
    (persCopowFwd hC q X Y r.1 r.2 u.1 s))))
  unfold persCopowFwd
  have hv := persNat v (s + q.1 + r.1) (s + ((q.1 + r.1 : ℝ≥0) : ℝ)) (le_of_eq (by push_cast; ring))
  rw [← persPre_comp]
  erw [← persSlide]
  rw [← hv, ← persTr_comp]
  simp only [persTr_S, persPre_S, ← persPre_tr, persTr_trans]

/-- `C^ℝ` is `ℝ≥0 × ℝ≥0`-copowered by representables when `C` is. -/
def persistentQCopowered : QCopoweredByRepresentables (persistentLQPCat C) where
  copow := persCopow hC
  copowIso x y q r := cwEquiv hC q x y r.1 r.2
  copowIso_S := fun {x y q r r'} h u => cw_S hC q x y h u
  copowIso_x := fun {x x' y q r} f u => cw_x hC q y f u
  copowIso_y := fun {x y y' q r δ} v u => cw_y hC q x v u

end PersCopow

/-- Lemma 5.1.8 (copowered case). -/
theorem persistent_copowered (v : ℝ≥0 × ℝ≥0)
    (L : LPCat (ℝ ⥤ C)) (hL : IsChangeOfEnrichment (pairFamily v) (persistentLQPCat C) L)
    (hC : CopoweredByRepresentables C) :
    Nonempty (@CopoweredByRepresentables (ℝ ⥤ C) _ L) :=
  copoweredByRepresentables_of_changeOfEnrichment (pairFamily v) (pairFamily_additive v)
    (persistentLQPCat C) (persistentQCopowered hC) L hL

/-- Helper for Proposition 5.1.9: `persPow` preserves limits of any shape `J` preserved by
pointwise powering. -/
theorem persPow_preservesLimitsOfShape (P : PoweredByRepresentables C) (q : ℝ≥0 × ℝ≥0)
    (J : Type*) [Category J] [HasLimitsOfShape J C]
    (hJ : PreservesLimitsOfShape J (P.pow q.2)) :
    PreservesLimitsOfShape J (persPow P q) := by
  let shift : ℝ ⥤ ℝ :=
    { obj := fun s => s + q.1
      map := fun {s t} f => homOfLE (add_le_add_left (leOfHom f) _) }
  let F : (ℝ ⥤ C) ⥤ (ℝ ⥤ C) :=
    (Functor.whiskeringLeft ℝ ℝ C).obj shift ⋙ (Functor.whiskeringRight ℝ C C).obj (P.pow q.2)
  have hF : PreservesLimitsOfShape J F := inferInstance
  let e : F ≅ persPow P q :=
    NatIso.ofComponents (fun Y => NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro s t f; simp [F, shift, persPow, persPowObj])) (by
      intro Y Z α; ext s; simp [F, shift, persPow, persPowObj])
  exact preservesLimitsOfShape_of_natIso e

/-- Proposition 5.1.9: if `C₀` has pullbacks, products and sequential limits, `C` is powered
by representables with powers preserving pullbacks, binary products, sequential limits and
morphisms of `W`, and `W` is closed under sequential limits, then the quotient interleaving
distance on `(C^ℝ_v, W^→)` is intrinsic and complete, and is computed by interleavings of
weakly equivalent replacements.

**Gap (missing hypothesis).** Proposition 5.1.9 assumes `(C, W)` is a relative locally persistent
category without stating that `W` is stable under base change (pullbacks); its proof invokes
Theorem 4.1.4 and Theorem 4.3.3 via Lemma 4.1.5, which require `W` to be stable under pullbacks.
We add `[W.IsStableUnderBaseChange]`. -/
theorem persistent_quotient_dist (W : MorphismProperty C) [W.IsMultiplicative]
    [W.IsStableUnderBaseChange]
    [HasPullbacks C] [HasBinaryProducts C] [HasLimitsOfShape ℕᵒᵖ C]
    (P : PoweredByRepresentables C)
    (hpb : ∀ ε, PreservesLimitsOfShape WalkingCospan (P.pow ε))
    (hprod : ∀ ε, PreservesLimitsOfShape (Discrete WalkingPair) (P.pow ε))
    (hseq : ∀ ε, PreservesLimitsOfShape ℕᵒᵖ (P.pow ε))
    (hW : ∀ ε {a b : C} (f : a ⟶ b), W f → W ((P.pow ε).map f))
    (hWlim : IsClosedUnderSequentialLimits W)
    (v : ℝ≥0 × ℝ≥0)
    (L : LPCat (ℝ ⥤ C)) (hL : IsChangeOfEnrichment (pairFamily v) (persistentLQPCat C) L) :
    @IsIntrinsicDist (ℝ ⥤ C) (@quotientInterleavingDist (ℝ ⥤ C) _ L (levelwiseProp W)) ∧
    @IsCompleteDist (ℝ ⥤ C) (@quotientInterleavingDist (ℝ ⥤ C) _ L (levelwiseProp W)) ∧
    ∀ X Y : ℝ ⥤ C, @quotientInterleavingDist (ℝ ⥤ C) _ L (levelwiseProp W) X Y =
      ⨅ (δ : ℝ≥0) (_ : ∃ X' Y' : ℝ ⥤ C, ∃ (a : X' ⟶ X) (b : Y' ⟶ Y),
          levelwiseProp W a ∧ levelwiseProp W b ∧ @IsInterleaved (ℝ ⥤ C) _ L X' Y' δ), (δ : ℝ≥0∞) := by
  letI := L
  obtain ⟨P', hpow_eq⟩ := exists_powered_of_changeOfEnrichment (pairFamily v) (pairFamily_additive v)
      (persistentLQPCat C) (persistentQPowered P) L hL
  letI := P'
  have hpb' : ∀ ε, PreservesLimitsOfShape WalkingCospan (P'.pow ε) := fun ε => by
    rw [hpow_eq ε]
    exact persPow_preservesLimitsOfShape P ((pairFamily v).toFun ε) WalkingCospan (hpb _)
  have hprod' : ∀ ε, PreservesLimitsOfShape (Discrete WalkingPair) (P'.pow ε) := fun ε => by
    rw [hpow_eq ε]
    exact persPow_preservesLimitsOfShape P ((pairFamily v).toFun ε) (Discrete WalkingPair) (hprod _)
  have hseq' : ∀ ε, PreservesLimitsOfShape ℕᵒᵖ (P'.pow ε) := fun ε => by
    rw [hpow_eq ε]
    exact persPow_preservesLimitsOfShape P ((pairFamily v).toFun ε) ℕᵒᵖ (hseq _)
  haveI : (levelwiseProp W).IsMultiplicative :=
    { id_mem := fun X r => W.id_mem (X.obj r)
      comp_mem := fun f g hf hg r => W.comp_mem _ _ (hf r) (hg r) }
  haveI : (levelwiseProp W).RespectsIso :=
    { precomp := fun e _ _ hf r =>
        MorphismProperty.RespectsIso.precomp W (((evaluation ℝ C).obj r).map e) _ (hf r)
      postcomp := fun e _ _ hf r =>
        MorphismProperty.RespectsIso.postcomp W (((evaluation ℝ C).obj r).map e) _ (hf r) }
  haveI : (levelwiseProp W).IsStableUnderBaseChange := by
    apply MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPullback
    intro X Y S f g _ hg
    refine ⟨pullback f g, pullback.fst f g, pullback.snd f g, IsPullback.of_hasPullback f g, ?_⟩
    intro r
    have hpb_r : IsPullback ((pullback.fst f g).app r) ((pullback.snd f g).app r)
        (f.app r) (g.app r) :=
      (IsPullback.of_hasPullback f g).map ((evaluation ℝ C).obj r)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb_r.flip (hg r)
  have hW' : ∀ ε {a b : ℝ ⥤ C} (f : a ⟶ b),
      levelwiseProp W f → levelwiseProp W ((P'.pow ε).map f) := fun ε a b f hf r => by
    rw [hpow_eq ε]
    exact hW _ (f.app (r + ((pairFamily v).toFun ε).1)) (hf _)
  have hWlim' : IsClosedUnderSequentialLimits (levelwiseProp W) := by
    intro X c hc hX n r
    exact hWlim (X ⋙ (evaluation ℝ C).obj r) (((evaluation ℝ C).obj r).mapCone c)
      (isLimitOfPreserves ((evaluation ℝ C).obj r) hc) (fun f => hX f r) n
  refine ⟨?_, ?_, ?_⟩
  · exact quotientInterleavingDistOf_intrinsic
      (admitsCoherentFactorizations_of_midpoints (hasTerminalMidpoints_of_powered hprod' hpb'))
      (WeaklyEquivalent (levelwiseProp W))
      (weaklyEquivalent_equivalence (levelwiseProp W))
  · exact quotientInterleavingDist_complete_of_powered hpb' hseq' (levelwiseProp W) hW' hWlim'
  · exact quotientInterleavingDist_eq_inf_acyclicCover_of_powered hpb' (levelwiseProp W) hW'

/-- Proposition 5.1.11: a locally persistent functor which preserves acyclic morphisms
induces, objectwise, a functor `C^ℝ → D^ℝ` preserving acyclic morphisms (and compatible with
the locally bi-persistent structures). -/
theorem exists_levelwise_functor {D : Type u'} [Category.{v'} D] [LPCat D]
    (F : LPFunctor C D) (W : MorphismProperty C) (V : MorphismProperty D)
    (hF : ∀ {a b : C} (f : a ⟶ b), W f → V (F.toFunctor.map f))
    (LC : LQPCat (ℝ≥0 × ℝ≥0) (ℝ ⥤ C)) (LD : LQPCat (ℝ≥0 × ℝ≥0) (ℝ ⥤ D)) :
    ∃ G : ((ℝ ⥤ C) ⥤ (ℝ ⥤ D)), G = (Functor.whiskeringRight ℝ C D).obj F.toFunctor ∧
      ∀ {X Y : ℝ ⥤ C} (α : X ⟶ Y), levelwiseProp W α → levelwiseProp V (G.map α) := by
  refine ⟨(Functor.whiskeringRight ℝ C D).obj F.toFunctor, rfl, ?_⟩
  intro X Y α hα r
  exact hF (α.app r) (hα r)

end PersistentObjects

/-! ### 5.1.3 Sublinear projections -/

section Sublinear

variable {P : Type u} [PartialOrder P]

/-- A monotone sublinear projection (Section 5.1.3): a monotone, subadditive `F` on
translations with `F 0 = 0`; i.e. a lax monoidal functor `Trans(P)ᵒᵖ → [0, ∞]ᵒᵖ`. -/
structure SublinearProjection (P : Type u) [PartialOrder P] where
  toFun : Translation P → ℝ≥0∞
  mono : Monotone toFun
  map_zero : toFun 0 = 0
  subadd : ∀ Γ Δ, toFun (Γ + Δ) ≤ toFun Γ + toFun Δ

/-- Lemma 5.1.14: the right adjoint `R` evaluated on `A : Set^Q`:
`R(A)(ε) = ⨿_{q, F q ≤ ε} A q`. -/
def ProjectionHom (F : SublinearProjection P) (A : Translation P → Type v) (ε : ℝ≥0) :
    Type (max u v) :=
  Σ q : {q : Translation P // F.toFun q ≤ ε}, A q.1

variable {C : Type u} [Category.{v} C]

/-- Proposition 5.1.15 (cf. [BSS13, Section 2.3]) and Remark 5.1.16: a sublinear projection
`F` induces a locally persistent structure on `C^P` whose `ε`-morphisms `X → Y` are the
natural transformations `X → Y ∘ Γ` with `F Γ ≤ ε`.

**Gap (missing hypothesis, Proposition 5.1.15).** In `LPCat`, `homZero` requires a bijection
`(X ⟶ Y) ≃ hom X Y 0`. Here `hom X Y 0` is `ProjectionHom F ... 0 = Σ q : {q // F q ≤ 0}, X ⟶ Y ∘ q`.
Unless `F q ≤ 0 ↔ q = 0`, this sigma type contains extra components for each translation with
measure 0, so it is not in bijection with `X ⟶ Y`. The thesis assumes a metric where `d(x, Γ x) = 0`
forces `Γ = id`, but `SublinearProjection` does not require definiteness. We add the hypothesis
`hF : F q ≤ 0 → q = 0`. -/
theorem exists_lpcat_sublinear (F : SublinearProjection P) (hF : ∀ q, F.toFun q ≤ 0 → q = 0) :
    ∃ L : LPCat (P ⥤ C), ∀ (X Y : P ⥤ C) (ε : ℝ≥0),
      L.hom X Y ε = ProjectionHom F (fun Γ => X ⟶ (Monotone.functor Γ.mono) ⋙ Y) ε := by
  obtain ⟨LQ, hLQ⟩ := exists_lqpcat_translation (P := P) (C := C)
  have hz : F.toFun 0 ≤ ((0 : ℝ≥0) : ℝ≥0∞) := by simp [F.map_zero]
  refine ⟨{
    hom := fun X Y ε => Σ q : {q : Translation P // F.toFun q ≤ ε}, LQ.hom X Y q.1
    homZero := {
      toFun := fun f => ⟨⟨0, hz⟩, LQ.homZero f⟩
      invFun := fun s => LQ.homZero.symm ((hF s.1.1 (by simpa using s.1.2)) ▸ s.2)
      left_inv := fun f => by simp
      right_inv := by
        rintro ⟨⟨q, hq⟩, a⟩
        obtain rfl := hF q (by simpa using hq)
        simp }
    comp := fun {X Y Z ε δ} g f => ⟨⟨f.1.1 + g.1.1, (F.subadd _ _).trans (by
      push_cast; exact add_le_add f.1.2 g.1.2)⟩, LQ.comp g.2 f.2⟩
    S := fun {X Y ε δ} h f => ⟨⟨f.1.1, f.1.2.trans (by exact_mod_cast h)⟩, f.2⟩
    id_comp := ?_
    comp_id := ?_
    assoc := ?_
    S_refl := ?_
    S_trans := ?_
    comp_S := ?_
    homZero_comp := ?_ }, fun _ _ _ => by simp only [ProjectionHom, hLQ]⟩
  · rintro X Y ε ⟨⟨q, hq⟩, a⟩
    exact Sigma.ext rfl (heq_of_eq ((LQ.S_refl _).symm.trans (LQ.id_comp a)))
  · rintro X Y ε ⟨⟨q, hq⟩, a⟩
    exact Sigma.ext rfl (heq_of_eq ((LQ.S_refl _).symm.trans (LQ.comp_id a)))
  · rintro X Y Z W ε δ γ ⟨⟨q, hq⟩, a⟩ ⟨⟨q', hq'⟩, b⟩ ⟨⟨q'', hq''⟩, c⟩
    exact Sigma.ext rfl (heq_of_eq ((LQ.S_refl _).symm.trans (LQ.assoc a b c)))
  · rintro X Y ε ⟨⟨q, hq⟩, a⟩
    rfl
  · rintro X Y ε δ γ h₁ h₂ ⟨⟨q, hq⟩, a⟩
    rfl
  · rintro X Y Z ε ε' δ δ' hε hδ ⟨⟨q, hq⟩, a⟩ ⟨⟨q', hq'⟩, b⟩
    rfl
  · intro X Y Z f g
    exact Sigma.ext rfl (heq_of_eq ((LQ.homZero_comp f g).trans (LQ.S_refl _)))

/-- A Lawvere metric on a poset, monotone in the sense of Example 5.1.17. -/
structure MonotoneLawvereMetric (P : Type u) [PartialOrder P] where
  d : P → P → ℝ≥0∞
  d_self : ∀ x, d x x = 0
  triangle : ∀ x y z, d x z ≤ d x y + d y z
  mono : ∀ x y z, x ≤ y → y ≤ z → d x y ≤ d x z

/-- Example 5.1.17: `Γ ↦ sup_x d (x, Γ x)` is a monotone sublinear projection. -/
theorem exists_sublinearProjection_lawvere (m : MonotoneLawvereMetric P) :
    ∃ F : SublinearProjection P, ∀ Γ, F.toFun Γ = ⨆ x, m.d x (Γ.toFun x) := by
  refine ⟨{
    toFun := fun Γ => ⨆ x, m.d x (Γ.toFun x)
    mono := ?_
    map_zero := ?_
    subadd := ?_ }, fun _ => rfl⟩
  · intro Γ Δ h
    exact iSup_mono fun x => m.mono x (Γ.toFun x) (Δ.toFun x) (Γ.le_apply x) (h x)
  · change (⨆ x, m.d x x) = 0
    simp [m.d_self]
  · intro Γ Δ
    refine iSup_le fun x => (m.triangle x (Γ.toFun x) (Δ.toFun (Γ.toFun x))).trans ?_
    exact add_le_add (le_iSup (fun y => m.d y (Γ.toFun y)) x)
      (le_iSup (fun y => m.d y (Δ.toFun y)) (Γ.toFun x))

end Sublinear

end ScoccolaPhd
