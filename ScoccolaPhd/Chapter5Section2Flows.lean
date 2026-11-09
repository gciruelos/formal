import Mathlib
import ScoccolaPhd.Chapter5Section1ChangeOfEnrichment

/-!
# Chapter 5.2: Categories with a flow

A `Q`-flow on `C` (Definition 5.2.22; a *flow* is the case `Q = ℝ≥0`) is a lax monoidal
functor `Q → End(C)`, given here by its unfolding (5.2.3)–(5.2.4): a functor `T : Q ⥤ (C ⥤ C)`,
a unit `u : id ⟶ T 0` and multiplications `μ ε δ : T ε ∘ T δ ⟶ T (ε + δ)`.

The enriched Kleisli construction (Section 5.2.1) is given by data: the underlying category of
`C^T` is the Kleisli category of the monad `T 0` (Lemma 5.2.10), the hom-sets are
`Hom(x, T ε y)`, composition is `f ≫ T ε g ≫ μ`. The monad and enriched composition
laws are proved.

The weak-interleaving characterization and equality of distances are proved. The remaining
flow and power constructions and metric consequences are stated below.
-/

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal Topology

universe u v w

namespace ScoccolaPhd

open LPCat

section QFlow

variable (Q : Type w) [AddMonoid Q] [PartialOrder Q] [AddLeftMono Q] [AddRightMono Q]
  (C : Type u) [Category.{v} C]

/-- Definition 5.2.22 (unfolded, cf. (5.2.3)–(5.2.4)): a `Q`-flow on `C`. -/
structure QFlow where
  T : Q ⥤ (C ⥤ C)
  u : 𝟭 C ⟶ T.obj 0
  μ : ∀ ε δ : Q, T.obj δ ⋙ T.obj ε ⟶ T.obj (ε + δ)
  unit_left : ∀ (ε : Q) (x : C), (u.app ((T.obj ε).obj x)) ≫ (μ 0 ε).app x ≫
    (T.map (eqToHom (zero_add ε))).app x = 𝟙 _
  unit_right : ∀ (ε : Q) (x : C), (T.obj ε).map (u.app x) ≫ (μ ε 0).app x ≫
    (T.map (eqToHom (add_zero ε))).app x = 𝟙 _
  assoc : ∀ (ε δ γ : Q) (x : C), (T.obj ε).map ((μ δ γ).app x) ≫ (μ ε (δ + γ)).app x ≫
    (T.map (eqToHom (add_assoc ε δ γ).symm)).app x =
      (μ ε δ).app ((T.obj γ).obj x) ≫ (μ (ε + δ) γ).app x
  μ_naturality : ∀ {ε ε' δ δ' : Q} (hε : ε ≤ ε') (hδ : δ ≤ δ') (x : C),
    (T.obj ε).map ((T.map (homOfLE hδ)).app x) ≫ (T.map (homOfLE hε)).app ((T.obj δ').obj x) ≫
      (μ ε' δ').app x = (μ ε δ).app x ≫ (T.map (homOfLE (add_le_add hε hδ))).app x

variable {Q C}

namespace QFlow

/-- Lemma 5.2.7: the flow structure induces a monad structure on `T 0`. -/
def monad (F : QFlow Q C) : Monad C where
  toFunctor := F.T.obj 0
  η := F.u
  μ := F.μ 0 0 ≫ F.T.map (eqToHom (add_zero 0))
  assoc := by
    intro x
    dsimp
    simp only [Functor.map_comp, Category.assoc]
    have hL := F.μ_naturality (le_refl (0 : Q)) (le_of_eq (add_zero (0 : Q))) x
    have hR := F.μ_naturality (le_of_eq (add_zero (0 : Q))) (le_refl (0 : Q)) x
    rw [show homOfLE (le_refl (0 : Q)) = 𝟙 (0 : Q) from rfl, F.T.map_id] at hL hR
    dsimp at hL hR
    rw [(F.T.obj (0 + 0)).map_id, Category.id_comp] at hR
    simp only [Category.id_comp] at hL
    rw [show eqToHom (add_zero (0 : Q)) = homOfLE (le_of_eq (add_zero (0 : Q)))
      from Subsingleton.elim _ _]
    rw [reassoc_of% hL, reassoc_of% hR]
    have ha := congrArg (fun k => k ≫
      (F.T.map (homOfLE (show (0 : Q) + 0 + 0 ≤ 0 from by simp))).app x)
      (F.assoc 0 0 0 x)
    simp only [Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp] at ha ⊢
    convert ha using 1
  left_unit := by
    intro x
    simpa using F.unit_left 0 x
  right_unit := by
    intro x
    simpa using F.unit_right 0 x

/-- Section 5.2.1: the locally `Q`-persistent category `C^T` with `Hom(x, y)_ε = Hom(x, T ε y)`,
on the Kleisli category of `T 0` (Lemma 5.2.10).  Composition of `f : x → T ε y` and
`g : y → T δ z` is `x → T ε y → T ε (T δ z) → T (ε + δ) z`. -/
def lqpCat (F : QFlow Q C) : LQPCat Q (Kleisli F.monad) where
  hom x y ε := x.of ⟶ (F.T.obj ε).obj y.of
  homZero := ⟨fun f => f.of, fun f => ⟨f⟩, fun _ => rfl, fun _ => rfl⟩
  comp {x y z ε δ} g f := f ≫ (F.T.obj ε).map g ≫ (F.μ ε δ).app z.of
  S {x y ε δ} h f := f ≫ (F.T.map (homOfLE h)).app y.of
  id_comp := by
    intro x y ε f
    change (f ≫ (F.T.obj ε).map (F.u.app y.of) ≫ (F.μ ε 0).app y.of) ≫
      (F.T.map (homOfLE _)).app y.of = f
    have h := congrArg (fun k => f ≫ k) (F.unit_right ε y.of)
    rw [show eqToHom (add_zero ε) = homOfLE (le_of_eq (add_zero ε)) from Subsingleton.elim _ _] at h
    dsimp at h ⊢
    simpa only [Category.assoc, Category.comp_id] using h
  comp_id := by
    intro x y ε f
    change (F.u.app x.of ≫ (F.T.obj 0).map f ≫ (F.μ 0 ε).app y.of) ≫
      (F.T.map (homOfLE _)).app y.of = f
    rw [← Category.assoc (F.u.app x.of), ← F.u.naturality f]
    have h := congrArg (fun k => f ≫ k) (F.unit_left ε y.of)
    rw [show eqToHom (zero_add ε) = homOfLE (le_of_eq (zero_add ε)) from Subsingleton.elim _ _] at h
    dsimp at h ⊢
    simpa only [Category.assoc, Category.comp_id] using h
  assoc := by
    intro x y z w ε δ γ f g h
    simp only [Functor.map_comp, Category.assoc]
    rw [← (F.μ ε δ).naturality_assoc h]
    have hi : (F.T.map (eqToHom (add_assoc ε δ γ).symm)).app w.of ≫
        (F.T.map (eqToHom (add_assoc ε δ γ))).app w.of = 𝟙 _ := by
      rw [← NatTrans.comp_app, ← Functor.map_comp]
      simp
    have ha := congrArg (fun k => k ≫ (F.T.map (eqToHom (add_assoc ε δ γ))).app w.of)
      (F.assoc ε δ γ w.of)
    simp only [Category.assoc, hi, Category.comp_id] at ha
    rw [show eqToHom (add_assoc ε δ γ) = homOfLE (le_of_eq (add_assoc ε δ γ))
      from Subsingleton.elim _ _] at ha
    rw [← ha]
    rfl
  S_refl := by
    intros
    simp
  S_trans := by
    intros
    simp [← NatTrans.comp_app, ← Functor.map_comp]
  comp_S := by
    intro x y z ε ε' δ δ' hε hδ f g
    simp only [Functor.map_comp, Category.assoc]
    rw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
    rw [F.μ_naturality hε hδ]
  homZero_comp := by
    intros
    change _ ≫ _ ≫ ((F.μ 0 0).app _ ≫ _) = _
    simp only [Category.assoc]
    rfl

end QFlow

end QFlow

section Transport
variable {P : Type u} {Q : Type u}

theorem pathLength_equiv (d : P → P → ℝ≥0∞) (d' : Q → Q → ℝ≥0∞) (e : P ≃ Q)
    (hd : ∀ p q, d' (e p) (e q) = d p q) (a b : ℝ) (f : ℝ → P) :
    pathLength d' a b (fun t => e (f t)) = pathLength d a b f := by
  simp only [pathLength, hd]

theorem isPathOn_equiv (d : P → P → ℝ≥0∞) (d' : Q → Q → ℝ≥0∞) (e : P ≃ Q)
    (hd : ∀ p q, d' (e p) (e q) = d p q) (a b : ℝ) (f : ℝ → P) :
    IsPathOn d' a b (fun t => e (f t)) ↔ IsPathOn d a b f := by
  simp only [IsPathOn, hd]

theorem isIntrinsicDist_of_equiv (d : P → P → ℝ≥0∞) (d' : Q → Q → ℝ≥0∞) (e : P ≃ Q)
    (hd : ∀ p q, d' (e p) (e q) = d p q) (h : IsIntrinsicDist d') : IsIntrinsicDist d := by
  intro p p'
  apply le_antisymm
  · refine le_iInf fun a => le_iInf fun b => le_iInf fun f => le_iInf fun hab => le_iInf fun hf =>
      le_iInf fun h1 => le_iInf fun h2 => ?_
    rw [← hd, h (e p) (e p')]
    refine (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le (fun t => e (f t))
      (iInf_le_of_le hab (iInf_le_of_le ((isPathOn_equiv d d' e hd a b f).2 hf)
        (iInf_le_of_le (by simp [h1]) (iInf_le_of_le (by simp [h2]) ?_))))))) 
    rw [pathLength_equiv d d' e hd]
  · rw [← hd, h (e p) (e p')]
    refine le_iInf fun a => le_iInf fun b => le_iInf fun g => le_iInf fun hab => le_iInf fun hg =>
      le_iInf fun h1 => le_iInf fun h2 => ?_
    have hg' : IsPathOn d a b (fun t => e.symm (g t)) := by
      rw [← isPathOn_equiv d d' e hd]; simpa using hg
    refine iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le (fun t => e.symm (g t))
      (iInf_le_of_le hab (iInf_le_of_le hg' (iInf_le_of_le (by simp [h1]) (iInf_le_of_le
        (by simp [h2]) ?_))))))
    have := pathLength_equiv d d' e hd a b (fun t => e.symm (g t))
    simpa using this.ge

theorem isCompleteDist_of_equiv (d : P → P → ℝ≥0∞) (d' : Q → Q → ℝ≥0∞) (e : P ≃ Q)
    (hd : ∀ p q, d' (e p) (e q) = d p q) (h : IsCompleteDist d') : IsCompleteDist d := by
  intro x hx
  obtain ⟨l, hl⟩ := h (fun i => e (x i)) (by simpa only [hd] using hx)
  refine ⟨e.symm l, ?_⟩
  simpa [← hd] using hl

end Transport

/-! ### Flows and their interleavings -/

/-- A flow ([SMS18]): a lax monoidal functor `ℝ≥0 → End(C)`; a flow is an `ℝ≥0`-flow. -/
abbrev Flow (C : Type u) [Category.{v} C] := QFlow ℝ≥0 C

namespace Flow

variable {C : Type u} [Category.{v} C] (F : Flow C)

/-- Proposition 5.2.2: the locally persistent category `C^T` of a category with a flow, on the
Kleisli category of `T 0`: `Hom(x, y)_δ = Hom_C(x, T δ y)`. -/
def lpCat : LPCat (Kleisli F.monad) where
  hom x y ε := x.of ⟶ (F.T.obj ε).obj y.of
  homZero := ⟨fun f => f.of, fun f => ⟨f⟩, fun _ => rfl, fun _ => rfl⟩
  comp {x y z ε δ} g f := f ≫ (F.T.obj ε).map g ≫ (F.μ ε δ).app z.of
  S {x y ε δ} h f := f ≫ (F.T.map (homOfLE h)).app y.of
  id_comp := by
    intro x y ε f
    change (f ≫ (F.T.obj ε).map (F.u.app y.of) ≫ (F.μ ε 0).app y.of) ≫
      (F.T.map (homOfLE _)).app y.of = f
    have h := congrArg (fun k => f ≫ k) (F.unit_right ε y.of)
    rw [show eqToHom (add_zero ε) = homOfLE (le_of_eq (add_zero ε)) from Subsingleton.elim _ _] at h
    dsimp at h ⊢
    simpa only [Category.assoc, Category.comp_id] using h
  comp_id := by
    intro x y ε f
    change (F.u.app x.of ≫ (F.T.obj 0).map f ≫ (F.μ 0 ε).app y.of) ≫
      (F.T.map (homOfLE _)).app y.of = f
    rw [← Category.assoc (F.u.app x.of), ← F.u.naturality f]
    have h := congrArg (fun k => f ≫ k) (F.unit_left ε y.of)
    rw [show eqToHom (zero_add ε) = homOfLE (le_of_eq (zero_add ε)) from Subsingleton.elim _ _] at h
    dsimp at h ⊢
    simpa only [Category.assoc, Category.comp_id] using h
  assoc := by
    intro x y z w ε δ γ f g h
    simp only [Functor.map_comp, Category.assoc]
    rw [← (F.μ ε δ).naturality_assoc h]
    have hi : (F.T.map (eqToHom (add_assoc ε δ γ).symm)).app w.of ≫
        (F.T.map (eqToHom (add_assoc ε δ γ))).app w.of = 𝟙 _ := by
      rw [← NatTrans.comp_app, ← Functor.map_comp]
      simp
    have ha := congrArg (fun k => k ≫ (F.T.map (eqToHom (add_assoc ε δ γ))).app w.of)
      (F.assoc ε δ γ w.of)
    simp only [Category.assoc, hi, Category.comp_id] at ha
    rw [show eqToHom (add_assoc ε δ γ) = homOfLE (le_of_eq (add_assoc ε δ γ))
      from Subsingleton.elim _ _] at ha
    rw [← ha]
    rfl
  S_refl := by
    intros
    simp
  S_trans := by
    intros
    simp [← NatTrans.comp_app, ← Functor.map_comp]
  comp_S := by
    intro x y z ε ε' δ δ' hε hδ f g
    simp only [Functor.map_comp, Category.assoc]
    rw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
    rw [F.μ_naturality hε hδ]
  homZero_comp := by
    intros
    change _ ≫ _ ≫ ((F.μ 0 0).app _ ≫ _) = _
    simp only [Category.assoc]
    rfl

/-- The canonical map `η_δ : x ⟶ T δ x`, `u` followed by `T (0 ≤ δ)`. -/
def eta (δ : ℝ≥0) (x : C) : x ⟶ (F.T.obj δ).obj x :=
  F.u.app x ≫ (F.T.map (homOfLE zero_le)).app x

/-- Definition 5.2.5: `f, g` form a weak `δ`-interleaving. -/
def IsWeakInterleaving {x y : C} {δ : ℝ≥0} (f : x ⟶ (F.T.obj δ).obj y)
    (g : y ⟶ (F.T.obj δ).obj x) : Prop :=
  f ≫ (F.T.obj δ).map g ≫ (F.μ δ δ).app x =
      F.u.app x ≫ (F.T.map (homOfLE zero_le)).app x ∧
    g ≫ (F.T.obj δ).map f ≫ (F.μ δ δ).app y =
      F.u.app y ≫ (F.T.map (homOfLE zero_le)).app y

/-- Definition 5.2.5: `f, g` form a strong `δ`-interleaving. -/
def IsStrongInterleaving {x y : C} {δ : ℝ≥0} (f : x ⟶ (F.T.obj δ).obj y)
    (g : y ⟶ (F.T.obj δ).obj x) : Prop :=
  f ≫ (F.T.obj δ).map g = F.eta δ x ≫ (F.T.obj δ).map (F.eta δ x) ∧
    g ≫ (F.T.obj δ).map f = F.eta δ y ≫ (F.T.obj δ).map (F.eta δ y)

/-- `x` and `y` are weakly `δ`-interleaved. -/
def IsWeaklyInterleaved (x y : C) (δ : ℝ≥0) : Prop :=
  ∃ (f : x ⟶ (F.T.obj δ).obj y) (g : y ⟶ (F.T.obj δ).obj x), F.IsWeakInterleaving f g

/-- `x` and `y` are strongly `δ`-interleaved. -/
def IsStronglyInterleaved (x y : C) (δ : ℝ≥0) : Prop :=
  ∃ (f : x ⟶ (F.T.obj δ).obj y) (g : y ⟶ (F.T.obj δ).obj x), F.IsStrongInterleaving f g

/-- The interleaving distance of a category with a flow ([SMS18]), using weak interleavings. -/
noncomputable def interleavingDist (x y : C) : ℝ≥0∞ :=
  ⨅ (δ : ℝ≥0) (_ : F.IsWeaklyInterleaved x y δ), (δ : ℝ≥0∞)

/-- Definition 5.2.9. -/
def IsIdempotent : Prop := ∀ x, IsIso ((F.monad.μ).app x)

/-- Definition 5.2.9: semi-strong flow: `u` is a natural isomorphism. -/
def IsSemiStrong : Prop := IsIso F.u

/-- Definition 5.2.9: strong flow: `u` and all `μ ε δ` are natural isomorphisms. -/
def IsStrong : Prop := IsIso F.u ∧ ∀ ε δ, IsIso (F.μ ε δ)

/-- Proposition 5.2.6: weak `δ`-interleavings in `(C, T)` are interleavings in `C^T`. -/
theorem isWeaklyInterleaved_iff (x y : C) (δ : ℝ≥0) :
    F.IsWeaklyInterleaved x y δ ↔
      @IsInterleaved _ _ F.lpCat (Kleisli.mk F.monad x) (Kleisli.mk F.monad y) δ := by
  letI := F.lpCat
  constructor
  · rintro ⟨f, g, h⟩
    exact ⟨⟨f, g, h⟩⟩
  · rintro ⟨⟨f, g, h⟩⟩
    exact ⟨f, g, h⟩

/-- The interleaving distance of `(C, T)` is that of `C^T` (Proposition 5.2.6). -/
theorem interleavingDist_eq (x y : C) :
    F.interleavingDist x y =
      @LPCat.interleavingDist _ _ F.lpCat (Kleisli.mk F.monad x) (Kleisli.mk F.monad y) := by
  unfold interleavingDist LPCat.interleavingDist
  simp_rw [F.isWeaklyInterleaved_iff]

/-- A strict distance bound yields a weak interleaving at that bound. -/
theorem isWeaklyInterleaved_of_dist_lt {x y : C} {ε : ℝ≥0}
    (h : F.interleavingDist x y < (ε : ℝ≥0∞)) : F.IsWeaklyInterleaved x y ε := by
  letI := F.lpCat
  apply (F.isWeaklyInterleaved_iff x y ε).2
  apply isInterleaved_of_dist_lt
  simpa only [← F.interleavingDist_eq] using h

/-! ### Weak power structures -/

end Flow

/-- Definition 5.2.12: a weak power structure on a locally persistent category `C`: objects
`ε ⋔ y` and functions `wp : Hom(x, ε ⋔ y)_δ → Hom(x, y)_{ε + δ}`, natural in everything, with
`wp_{ε, 0}` bijective.  (Naturality in `ε` is omitted, as for `PoweredByRepresentables`.) -/
class WeakPowerStructure (C : Type u) [Category.{v} C] [LPCat C] where
  pow : ℝ≥0 → C ⥤ C
  wp : ∀ (x y : C) (ε δ : ℝ≥0), hom x ((pow ε).obj y) δ → hom x y (ε + δ)
  wp_zero : ∀ (x y : C) (ε : ℝ≥0), Function.Bijective (wp x y ε 0)
  wp_S : ∀ {x y : C} {ε δ δ' : ℝ≥0} (h : δ ≤ δ') (u : hom x ((pow ε).obj y) δ),
    wp x y ε δ' (S h u) = S (add_le_add le_rfl h) (wp x y ε δ u)
  wp_x : ∀ {x x' y : C} {ε δ : ℝ≥0} (v : x' ⟶ x) (u : hom x ((pow ε).obj y) δ),
    wp x' y ε δ (S (le_of_eq (zero_add δ)) (comp u (homZero v))) =
      S (le_of_eq (by simp)) (comp (wp x y ε δ u) (homZero v))
  wp_y : ∀ {x y y' : C} {ε δ : ℝ≥0} (f : y ⟶ y') (u : hom x ((pow ε).obj y) δ),
    wp x y' ε δ (S (le_of_eq (by simp)) (comp (homZero ((pow ε).map f)) u)) =
      S (le_of_eq (by simp)) (comp (homZero f) (wp x y ε δ u))

namespace Flow

variable {C : Type u} [Category.{v} C] (F : Flow C)

/-- Lemma 5.2.15: a flow induces a weak power structure on `C^T`, with weak power
`ε ⋔ x = T ε x`.

**Gap (missing hypothesis, Lemma 5.2.15).** The thesis states that any flow induces
a weak power structure on `C^T`. However, `WeakPowerStructure` requires `wp_{ε, 0}` to be
a bijection, which means `x ⟶ T 0 (T ε y)` is naturally isomorphic to `x ⟶ T ε y` via `μ ε 0`.
This requires `μ ε 0 : T ε ∘ T 0 ⟶ T ε` to be an isomorphism, which fails for arbitrary
lax monoidal flows unless the flow is semi-strong (as Scoccola notes in Diagram 5.2.8,
where the equivalence is with semi-strong flows `FlCATs.strong`). -/
theorem exists_weakPower :
    ∃ W : @WeakPowerStructure (Kleisli F.monad) _ F.lpCat,
      ∀ (ε : ℝ≥0) (x : Kleisli F.monad), (W.pow ε).obj x = Kleisli.mk _ ((F.T.obj ε).obj x.of) := by
  sorry

/-- `u` is invertible for a strong flow. -/
noncomputable def uinv (h : F.IsStrong) (y : C) : (F.T.obj 0).obj y ⟶ y :=
  haveI : IsIso F.u := h.1
  inv (F.u.app y)

theorem u_uinv (h : F.IsStrong) (y : C) : F.u.app y ≫ F.uinv h y = 𝟙 _ := by
  haveI : IsIso F.u := h.1
  unfold uinv; simp

theorem uinv_u (h : F.IsStrong) (y : C) : F.uinv h y ≫ F.u.app y = 𝟙 _ := by
  haveI : IsIso F.u := h.1
  unfold uinv; simp

theorem uinv_nat (h : F.IsStrong) {y z : C} (g : y ⟶ z) :
    (F.T.obj 0).map g ≫ F.uinv h z = F.uinv h y ≫ g := by
  have := F.u.naturality g
  calc (F.T.obj 0).map g ≫ F.uinv h z = F.uinv h y ≫ F.u.app y ≫ (F.T.obj 0).map g ≫ F.uinv h z := by
        rw [← Category.assoc, uinv_u, Category.id_comp]
    _ = F.uinv h y ≫ g := by
        rw [← Category.assoc (F.u.app y), ← this]; simp [u_uinv]

theorem mu0_eq (h : F.IsStrong) (z : C) : F.monad.μ.app z = F.uinv h ((F.T.obj 0).obj z) := by
  have h1 : F.u.app ((F.T.obj 0).obj z) ≫ F.monad.μ.app z = 𝟙 _ := F.monad.left_unit z
  haveI : IsIso F.u := h.1
  refine (cancel_epi (F.u.app ((F.T.obj 0).obj z))).1 ?_
  exact h1.trans (u_uinv F h _).symm

theorem kPow_comp_aux (h : F.IsStrong) (ε : ℝ≥0) {a b c : C}
    (f : a ⟶ (F.T.obj 0).obj b) (g : b ⟶ (F.T.obj 0).obj c) :
    (F.T.obj ε).map ((f ≫ (F.T.obj 0).map g ≫ F.monad.μ.app c) ≫ F.uinv h c) ≫
        F.u.app ((F.T.obj ε).obj c) =
      ((F.T.obj ε).map (f ≫ F.uinv h b) ≫ F.u.app ((F.T.obj ε).obj b)) ≫
        (F.T.obj 0).map ((F.T.obj ε).map (g ≫ F.uinv h c) ≫ F.u.app ((F.T.obj ε).obj c)) ≫
          F.monad.μ.app ((F.T.obj ε).obj c) := by
  have hm := F.mu0_eq h c
  rw [hm]
  have nat := F.u.naturality ((F.T.obj ε).map (g ≫ F.uinv h c) ≫ F.u.app ((F.T.obj ε).obj c))
  have lu : F.u.app ((F.T.obj 0).obj ((F.T.obj ε).obj c)) ≫
      F.monad.μ.app ((F.T.obj ε).obj c) = 𝟙 _ := F.monad.left_unit ((F.T.obj ε).obj c)
  have e1 : (F.T.obj 0).map g ≫ F.uinv h ((F.T.obj 0).obj c) = F.uinv h b ≫ g := F.uinv_nat h g
  have nat' : F.u.app ((F.T.obj ε).obj b) ≫ (F.T.obj 0).map ((F.T.obj ε).map (g ≫ F.uinv h c) ≫
      F.u.app ((F.T.obj ε).obj c)) = ((F.T.obj ε).map (g ≫ F.uinv h c) ≫
      F.u.app ((F.T.obj ε).obj c)) ≫ F.u.app ((F.T.obj 0).obj ((F.T.obj ε).obj c)) := nat.symm
  have rhs : ((F.T.obj ε).map (f ≫ F.uinv h b) ≫ F.u.app ((F.T.obj ε).obj b)) ≫
      (F.T.obj 0).map ((F.T.obj ε).map (g ≫ F.uinv h c) ≫ F.u.app ((F.T.obj ε).obj c)) ≫
        F.monad.μ.app ((F.T.obj ε).obj c) =
      (F.T.obj ε).map (f ≫ F.uinv h b) ≫ (F.T.obj ε).map (g ≫ F.uinv h c) ≫
        F.u.app ((F.T.obj ε).obj c) := by
    rw [Category.assoc]
    erw [reassoc_of% nat']
    erw [lu]
    erw [Category.comp_id]
    rfl
  have lhs : (f ≫ (F.T.obj 0).map g ≫ F.uinv h ((F.T.obj 0).obj c)) ≫ F.uinv h c =
      (f ≫ F.uinv h b) ≫ (g ≫ F.uinv h c) := by
    rw [Category.assoc, e1]
    simp only [Category.assoc]
  rw [rhs]
  erw [lhs]
  rw [Functor.map_comp, Category.assoc]

/-- The power functor `y ↦ T ε y` on the Kleisli category of a strong flow. -/
noncomputable def kPow (h : F.IsStrong) (ε : ℝ≥0) : Kleisli F.monad ⥤ Kleisli F.monad where
  obj x := Kleisli.mk _ ((F.T.obj ε).obj x.of)
  map {x y} f := ⟨(F.T.obj ε).map (f.of ≫ F.uinv h y.of) ≫ F.u.app ((F.T.obj ε).obj y.of)⟩
  map_id := by
    intro x
    apply Kleisli.Hom.ext
    change (F.T.obj ε).map (F.u.app x.of ≫ F.uinv h x.of) ≫ F.u.app ((F.T.obj ε).obj x.of) =
      F.u.app ((F.T.obj ε).obj x.of)
    rw [u_uinv]
    exact (by rw [CategoryTheory.Functor.map_id, Category.id_comp])
  map_comp := by
    intro x y z f g
    apply Kleisli.Hom.ext
    exact F.kPow_comp_aux h ε f.of g.of

/-- `μ r ε` is invertible for a strong flow. -/
noncomputable def muInv (h : F.IsStrong) (r ε : ℝ≥0) (y : C) :
    (F.T.obj (r + ε)).obj y ⟶ (F.T.obj r).obj ((F.T.obj ε).obj y) :=
  haveI : IsIso (F.μ r ε) := h.2 r ε
  inv ((F.μ r ε).app y)

/-- The power isomorphism `Hom(x, T ε y)_r ≅ Hom(x, y)_{ε + r}` in `C^T`. -/
noncomputable def kPowIso (h : F.IsStrong) (x y : Kleisli F.monad) (ε r : ℝ≥0) :
    (x.of ⟶ (F.T.obj r).obj ((F.T.obj ε).obj y.of)) ≃ (x.of ⟶ (F.T.obj (ε + r)).obj y.of) where
  toFun u := u ≫ (F.μ r ε).app y.of ≫ (F.T.map (homOfLE (le_of_eq (add_comm r ε)))).app y.of
  invFun v := v ≫ (F.T.map (homOfLE (le_of_eq (add_comm r ε).symm))).app y.of ≫
    F.muInv h r ε y.of
  left_inv := by
    intro u
    haveI : IsIso (F.μ r ε) := h.2 r ε
    have c : (F.T.map (homOfLE (le_of_eq (add_comm r ε)))).app y.of ≫
        (F.T.map (homOfLE (le_of_eq (add_comm r ε).symm))).app y.of = 𝟙 _ := by
      rw [← NatTrans.comp_app, ← Functor.map_comp]; simp
    simp only [Category.assoc]
    rw [reassoc_of% c]
    simp [muInv]
  right_inv := by
    intro v
    haveI : IsIso (F.μ r ε) := h.2 r ε
    have c : (F.T.map (homOfLE (le_of_eq (add_comm r ε).symm))).app y.of ≫
        (F.T.map (homOfLE (le_of_eq (add_comm r ε)))).app y.of = 𝟙 _ := by
      rw [← NatTrans.comp_app, ← Functor.map_comp]; simp
    simp only [Category.assoc]
    simp only [muInv, IsIso.inv_hom_id_assoc]
    rw [c, Category.comp_id]

/-- LAW S: naturality of `kPowIso` in the shift. -/
theorem kPowIso_S (h : F.IsStrong) {x y : Kleisli F.monad} {ε r r' : ℝ≥0} (hh : r ≤ r')
    (u : x.of ⟶ (F.T.obj r).obj ((F.T.obj ε).obj y.of)) :
    F.kPowIso h x y ε r' (u ≫ (F.T.map (homOfLE hh)).app _) =
      F.kPowIso h x y ε r u ≫ (F.T.map (homOfLE (add_le_add le_rfl hh))).app y.of := by
  have nat : (F.T.map (homOfLE hh)).app ((F.T.obj ε).obj y.of) ≫ (F.μ r' ε).app y.of =
      (F.μ r ε).app y.of ≫ (F.T.map (homOfLE (add_le_add hh (le_refl ε)))).app y.of := by
    have := F.μ_naturality hh (le_refl ε) y.of
    have e : (F.T.map (homOfLE (le_refl ε))) = 𝟙 _ := F.T.map_id ε
    rw [e] at this
    simpa using this
  have c : (F.T.map (homOfLE (add_le_add hh (le_refl ε)))).app y.of ≫
      (F.T.map (homOfLE (le_of_eq (add_comm r' ε)))).app y.of =
      (F.T.map (homOfLE (le_of_eq (add_comm r ε)))).app y.of ≫
        (F.T.map (homOfLE (add_le_add le_rfl hh))).app y.of := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp]
    congr 2
  simp only [kPowIso, Equiv.coe_fn_mk, Category.assoc]
  rw [reassoc_of% nat, c]

/-- LAW X: naturality of `kPowIso` in the source (precomposition by an approximate morphism). -/
theorem kPowIso_x (h : F.IsStrong) {x x' y : Kleisli F.monad} {ε r δ : ℝ≥0}
    (v : x'.of ⟶ (F.T.obj δ).obj x.of) (u : x.of ⟶ (F.T.obj r).obj ((F.T.obj ε).obj y.of)) :
    F.kPowIso h x' y ε (δ + r) (v ≫ (F.T.obj δ).map u ≫ (F.μ δ r).app _) =
      (v ≫ (F.T.obj δ).map (F.kPowIso h x y ε r u) ≫ (F.μ δ (ε + r)).app y.of) ≫
        (F.T.map (homOfLE (le_of_eq (add_left_comm δ ε r)))).app y.of := by
  have ha := F.assoc δ r ε y.of
  have hn := F.μ_naturality (le_refl δ) (le_of_eq (add_comm r ε)) y.of
  rw [show eqToHom (add_assoc δ r ε).symm = homOfLE (le_of_eq (add_assoc δ r ε).symm)
    from Subsingleton.elim _ _] at ha
  have e : F.T.map (homOfLE (le_refl δ)) = 𝟙 _ := F.T.map_id δ
  rw [e] at hn
  simp only [NatTrans.id_app, Category.id_comp] at hn
  have cc : (F.T.map (homOfLE (add_le_add (le_refl δ) (le_of_eq (add_comm r ε))))).app y.of ≫
      (F.T.map (homOfLE (le_of_eq (add_left_comm δ ε r)))).app y.of =
      (F.T.map (homOfLE (le_of_eq (add_assoc δ r ε).symm))).app y.of ≫
        (F.T.map (homOfLE (le_of_eq (add_comm (δ + r) ε)))).app y.of := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp]
    congr 2
  simp only [kPowIso, Equiv.coe_fn_mk, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, cc, reassoc_of% ha]

theorem kPowIso_y_aux (h : F.IsStrong) {x y y' : C} {ε r : ℝ≥0}
    (f : y ⟶ (F.T.obj 0).obj y') (u : x ⟶ (F.T.obj r).obj ((F.T.obj ε).obj y)) :
    ((u ≫ (F.T.obj r).map ((F.T.obj ε).map (f ≫ F.uinv h y') ≫ F.u.app ((F.T.obj ε).obj y')) ≫
        (F.μ r 0).app ((F.T.obj ε).obj y')) ≫
        (F.T.map (homOfLE (le_of_eq (add_zero r)))).app ((F.T.obj ε).obj y')) ≫
      (F.μ r ε).app y' ≫ (F.T.map (homOfLE (le_of_eq (add_comm r ε)))).app y' =
    ((u ≫ (F.μ r ε).app y ≫ (F.T.map (homOfLE (le_of_eq (add_comm r ε)))).app y) ≫
        (F.T.obj (ε + r)).map f ≫ (F.μ (ε + r) 0).app y') ≫
      (F.T.map (homOfLE (le_of_eq (add_zero (ε + r))))).app y' := by
  have ur : ∀ (s : ℝ≥0) (z : C), (F.T.obj s).map (F.u.app z) ≫ (F.μ s 0).app z ≫
      (F.T.map (homOfLE (le_of_eq (add_zero s)))).app z = 𝟙 _ := by
    intro s z
    have := F.unit_right s z
    rwa [show eqToHom (add_zero s) = homOfLE (le_of_eq (add_zero s)) from Subsingleton.elim _ _]
      at this
  have tu : ∀ (s : ℝ≥0) (z : C), (F.T.obj s).map (F.uinv h z) =
      (F.μ s 0).app z ≫ (F.T.map (homOfLE (le_of_eq (add_zero s)))).app z := by
    intro s z
    have h1 := ur s z
    have h2 : (F.T.obj s).map (F.uinv h z) ≫ (F.T.obj s).map (F.u.app z) = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, uinv_u]; exact CategoryTheory.Functor.map_id _ _
    calc (F.T.obj s).map (F.uinv h z)
        = (F.T.obj s).map (F.uinv h z) ≫ ((F.T.obj s).map (F.u.app z) ≫ (F.μ s 0).app z ≫
            (F.T.map (homOfLE (le_of_eq (add_zero s)))).app z) := by
          erw [h1, Category.comp_id]
      _ = _ := by
          rw [← Category.assoc, h2]; erw [Category.id_comp]
  have nat := (F.μ r ε).naturality (f ≫ F.uinv h y')
  have cn := (F.T.map (homOfLE (le_of_eq (add_comm r ε)))).naturality (f ≫ F.uinv h y')
  rw [CategoryTheory.Functor.map_comp (F.T.obj r)]
  simp only [Category.assoc]
  erw [reassoc_of% (ur r ((F.T.obj ε).obj y'))]
  erw [reassoc_of% nat]
  rw [cn, CategoryTheory.Functor.map_comp (F.T.obj (ε + r)), tu (ε + r) y']

/-- LAW Y: naturality of `kPowIso` in the target (postcomposition by a `0`-morphism). -/
theorem kPowIso_y (h : F.IsStrong) {x y y' : Kleisli F.monad} {ε r : ℝ≥0} (f : y ⟶ y')
    (u : x.of ⟶ (F.T.obj r).obj ((F.T.obj ε).obj y.of)) :
    F.kPowIso h x y' ε r ((u ≫ (F.T.obj r).map (((F.kPow h ε).map f).of) ≫ (F.μ r 0).app _) ≫
        (F.T.map (homOfLE (le_of_eq (add_zero r)))).app _) =
      ((F.kPowIso h x y ε r u) ≫ (F.T.obj (ε + r)).map f.of ≫ (F.μ (ε + r) 0).app y'.of) ≫
        (F.T.map (homOfLE (le_of_eq (add_zero (ε + r))))).app y'.of := by
  simp only [kPowIso, Equiv.coe_fn_mk]
  exact F.kPowIso_y_aux h f.of u

/-- Proposition 5.2.16: if `T` is strong, `C^T` is powered by representables, with
`y^ε = T ε y`. -/
theorem uinv_comp_aux (h : F.IsStrong) {a b c : C} (f : a ⟶ (F.T.obj 0).obj b)
    (g : b ⟶ (F.T.obj 0).obj c) :
    (f ≫ (F.T.obj 0).map g ≫ F.monad.μ.app c) ≫ F.uinv h c = (f ≫ F.uinv h b) ≫ (g ≫ F.uinv h c) := by
  have hm := F.mu0_eq h c
  have e1 : (F.T.obj 0).map g ≫ F.uinv h ((F.T.obj 0).obj c) = F.uinv h b ≫ g := F.uinv_nat h g
  rw [hm, Category.assoc]
  erw [e1]
  erw [Category.assoc]
  erw [Category.assoc (F.uinv h b) g (F.uinv h c)]

/-- For a strong flow, the Kleisli category is equivalent to `C`: the functor back to `C`. -/
noncomputable def kToC (h : F.IsStrong) : Kleisli F.monad ⥤ C where
  obj x := x.of
  map {x y} f := f.of ≫ F.uinv h y.of
  map_id := by
    intro x
    exact F.u_uinv h x.of
  map_comp := by
    intro x y z f g
    exact F.uinv_comp_aux h f.of g.of

/-- The inclusion `C ⥤ Kleisli`. -/
noncomputable def kOfC : C ⥤ Kleisli F.monad where
  obj x := Kleisli.mk _ x
  map {x y} f := ⟨f ≫ F.u.app y⟩
  map_id := by
    intro x
    apply Kleisli.Hom.ext
    exact Category.id_comp _
  map_comp := by
    intro x y z f g
    apply Kleisli.Hom.ext
    change (f ≫ g) ≫ F.u.app z = (f ≫ F.u.app y) ≫ (F.T.obj 0).map (g ≫ F.u.app z) ≫
      F.monad.μ.app z
    have lu : F.u.app ((F.T.obj 0).obj z) ≫ F.monad.μ.app z = 𝟙 _ := F.monad.left_unit z
    have ru : (F.T.obj 0).map (F.u.app z) ≫ F.monad.μ.app z = 𝟙 _ := F.monad.right_unit z
    have nat : g ≫ F.u.app z = F.u.app y ≫ (F.T.obj 0).map g := F.u.naturality g
    have step : (F.T.obj 0).map (g ≫ F.u.app z) ≫ F.monad.μ.app z = (F.T.obj 0).map g := by
      erw [CategoryTheory.Functor.map_comp, Category.assoc]
      erw [ru, Category.comp_id]
    rw [Category.assoc]
    erw [step, Category.assoc, ← nat]
    rfl

/-- For a strong flow, `C^T` (the Kleisli category) is equivalent to `C`. -/
noncomputable def kEquiv (h : F.IsStrong) : Kleisli F.monad ≌ C where
  functor := F.kToC h
  inverse := F.kOfC
  unitIso := NatIso.ofComponents (fun x => Iso.refl x) (by
    intro x y f
    change f ≫ 𝟙 y = 𝟙 x ≫ (F.kToC h ⋙ F.kOfC).map f
    rw [Category.comp_id]
    erw [Category.id_comp]
    apply Kleisli.Hom.ext
    show f.of = (f.of ≫ F.uinv h y.of) ≫ F.u.app y.of
    erw [Category.assoc, uinv_u, Category.comp_id])
  counitIso := NatIso.ofComponents (fun x => Iso.refl x) (by
    intro x y f
    change (F.kOfC ⋙ F.kToC h).map f ≫ 𝟙 y = 𝟙 x ≫ f
    erw [Category.comp_id, Category.id_comp]
    show (f ≫ F.u.app y) ≫ F.uinv h y = f
    rw [Category.assoc, u_uinv]
    exact Category.comp_id _)
  functor_unitIso_comp := by
    intro X
    change (F.kToC h).map (𝟙 X) ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id]
    exact (F.kToC h).map_id X

theorem kPow_eq (h : F.IsStrong) (ε : ℝ≥0) :
    F.kPow h ε = F.kToC h ⋙ F.T.obj ε ⋙ F.kOfC := rfl

theorem kToC_isEquivalence (h : F.IsStrong) : (F.kToC h).IsEquivalence :=
  (F.kEquiv h).isEquivalence_functor

theorem kOfC_isEquivalence (h : F.IsStrong) : F.kOfC.IsEquivalence :=
  (F.kEquiv h).isEquivalence_inverse

theorem kHasLimitsOfShape (h : F.IsStrong) (J : Type) [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (Kleisli F.monad) := by
  haveI := F.kToC_isEquivalence h
  exact Adjunction.hasLimitsOfShape_of_equivalence (F.kToC h)

theorem kPow_preserves (h : F.IsStrong) (J : Type) [SmallCategory J] (ε : ℝ≥0)
    (hT : PreservesLimitsOfShape J (F.T.obj ε)) :
    PreservesLimitsOfShape J (F.kPow h ε) := by
  rw [kPow_eq]
  haveI := F.kToC_isEquivalence h
  haveI := F.kOfC_isEquivalence h
  infer_instance

/-- The powered-by-representables structure on `C^T` for a strong flow. -/
noncomputable def kPowered (h : F.IsStrong) : @PoweredByRepresentables (Kleisli F.monad) _ F.lpCat :=
  letI := F.lpCat
  { pow := F.kPow h
    powIso := fun x y ε r => F.kPowIso h x y ε r
    powIso_S := fun hh u => F.kPowIso_S h hh u
    powIso_x := fun v u => F.kPowIso_x h v u
    powIso_y := fun f u => F.kPowIso_y h f u }

theorem exists_powered_of_strong (h : F.IsStrong) :
    ∃ P : @PoweredByRepresentables (Kleisli F.monad) _ F.lpCat,
      ∀ (ε : ℝ≥0) (x : Kleisli F.monad), (P.pow ε).obj x = Kleisli.mk _ ((F.T.obj ε).obj x.of) :=
  ⟨F.kPowered h, fun ε x => rfl⟩

/-- Proposition 5.2.11: a flow induces a canonical flow on the Kleisli category of `T 0`, with
the same weak and strong interleavings (for `δ > 0`). -/
theorem exists_flow_kleisli :
    ∃ F' : Flow (Kleisli F.monad),
      (∀ (ε : ℝ≥0) (x : Kleisli F.monad), (F'.T.obj ε).obj x = Kleisli.mk _ ((F.T.obj ε).obj x.of)) ∧
      ∀ (x y : C) (δ : ℝ≥0), 0 < δ →
        (F.IsWeaklyInterleaved x y δ ↔
          F'.IsWeaklyInterleaved (Kleisli.mk F.monad x) (Kleisli.mk F.monad y) δ) ∧
        (F.IsStronglyInterleaved x y δ ↔
          F'.IsStronglyInterleaved (Kleisli.mk F.monad x) (Kleisli.mk F.monad y) δ) := by
  sorry

/-! ### Metric properties -/

/-- Proposition 5.2.18 (1): a strong flow on `C` with sequential limits preserved by every `T ε`
makes `C^T` admit weighted sequential limits. -/
theorem hasWeightedSeqLimits_of_strong (h : F.IsStrong) [HasLimitsOfShape ℕᵒᵖ C]
    (hT : ∀ ε, PreservesLimitsOfShape ℕᵒᵖ (F.T.obj ε)) :
    @HasWeightedSeqLimits (Kleisli F.monad) _ F.lpCat := by
  letI := F.lpCat
  letI := F.kPowered h
  haveI := F.kHasLimitsOfShape h ℕᵒᵖ
  exact hasWeightedSeqLimits_of_powered (fun ε => F.kPow_preserves h ℕᵒᵖ ε (hT ε))

/-- Proposition 5.2.18 (2): likewise for terminal midpoints, using binary products and
pullbacks. -/
theorem hasTerminalMidpoints_of_strong (h : F.IsStrong) [HasBinaryProducts C] [HasPullbacks C]
    (hT1 : ∀ ε, PreservesLimitsOfShape (Discrete WalkingPair) (F.T.obj ε))
    (hT2 : ∀ ε, PreservesLimitsOfShape WalkingCospan (F.T.obj ε)) :
    @HasTerminalMidpoints (Kleisli F.monad) _ F.lpCat := by
  letI := F.lpCat
  letI := F.kPowered h
  haveI : HasBinaryProducts (Kleisli F.monad) := F.kHasLimitsOfShape h (Discrete WalkingPair)
  haveI : HasPullbacks (Kleisli F.monad) := F.kHasLimitsOfShape h WalkingCospan
  have h1 : ∀ ε, PreservesLimitsOfShape (Discrete WalkingPair) (F.kPow h ε) :=
    fun ε => F.kPow_preserves h _ ε (hT1 ε)
  have h2 : ∀ ε, PreservesLimitsOfShape WalkingCospan (F.kPow h ε) :=
    fun ε => F.kPow_preserves h _ ε (hT2 ε)
  exact @hasTerminalMidpoints_of_powered (Kleisli F.monad) _ F.lpCat (F.kPowered h) _ _ h1 h2

/-- Theorem 5.2.19: if `T` is strong, `C` is complete and every `T ε` preserves limits, the
interleaving distance of `(C, T)` is intrinsic and complete. -/
theorem interleavingDist_intrinsic_complete (h : F.IsStrong) [HasLimits C]
    (hT : ∀ ε, PreservesLimits (F.T.obj ε)) :
    IsIntrinsicDist F.interleavingDist ∧ IsCompleteDist F.interleavingDist := by
  letI := F.lpCat
  letI := F.kPowered h
  haveI : ∀ ε, PreservesLimits (F.T.obj ε) := hT
  haveI : HasLimitsOfShape ℕᵒᵖ (Kleisli F.monad) := F.kHasLimitsOfShape h ℕᵒᵖ
  haveI : HasBinaryProducts (Kleisli F.monad) := F.kHasLimitsOfShape h (Discrete WalkingPair)
  haveI : HasPullbacks (Kleisli F.monad) := F.kHasLimitsOfShape h WalkingCospan
  let e : C ≃ Kleisli F.monad := ⟨fun x => Kleisli.mk _ x, fun x => x.of, fun _ => rfl, fun _ => rfl⟩
  have hd : ∀ x y : C, @LPCat.interleavingDist _ _ F.lpCat (e x) (e y) = F.interleavingDist x y :=
    fun x y => (F.interleavingDist_eq x y).symm
  have hprod : ∀ ε, PreservesLimitsOfShape (Discrete WalkingPair) (F.kPow h ε) :=
    fun ε => F.kPow_preserves h _ ε inferInstance
  have hpb : ∀ ε, PreservesLimitsOfShape WalkingCospan (F.kPow h ε) :=
    fun ε => F.kPow_preserves h _ ε inferInstance
  have hseq : ∀ ε, PreservesLimitsOfShape ℕᵒᵖ (F.kPow h ε) := fun ε => by
    have hs : PreservesLimitsOfSize.{0, 0} (F.T.obj ε) := preservesLimitsOfSize_shrink.{0, v, 0, v} (F.T.obj ε)
    exact F.kPow_preserves h _ ε hs.preservesLimitsOfShape
  exact ⟨isIntrinsicDist_of_equiv _ _ e hd
      (interleavingDist_intrinsic_of_powered (C := Kleisli F.monad) hprod hpb),
    isCompleteDist_of_equiv _ _ e hd
      (interleavingDist_complete_of_powered (C := Kleisli F.monad) hseq)⟩

/-- The bonding map in Cruz's inverse sequence of shifted objects. -/
noncomputable def seqLimitStep (a : ℕ → C) (ε : ℕ → ℝ≥0) (hε : Summable ε)
    (f : ∀ i, a (i + 1) ⟶ (F.T.obj (ε i)).obj (a i)) (i : ℕ) :
    (F.T.obj (tailSum ε (i + 1))).obj (a (i + 1)) ⟶
      (F.T.obj (tailSum ε i)).obj (a i) :=
  (F.T.obj (tailSum ε (i + 1))).map (f i) ≫
    (F.μ (tailSum ε (i + 1)) (ε i)).app (a i) ≫
    (F.T.map (homOfLE (le_of_eq (by rw [tailSum_succ hε i, add_comm])))).app (a i)

/-- Cruz's inverse sequence `⋯ ⟶ T (tailSum ε i) (a i) ⟶ ⋯`. -/
noncomputable def seqLimitDiagram (a : ℕ → C) (ε : ℕ → ℝ≥0) (hε : Summable ε)
    (f : ∀ i, a (i + 1) ⟶ (F.T.obj (ε i)).obj (a i)) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun i => (F.T.obj (tailSum ε i)).obj (a i))
    (F.seqLimitStep a ε hε f)

/-- Consecutive projections from the limit satisfy the bonding equation. -/
theorem seqLimit_projection_step [HasLimitsOfShape ℕᵒᵖ C]
    (a : ℕ → C) (ε : ℕ → ℝ≥0) (hε : Summable ε)
    (f : ∀ i, a (i + 1) ⟶ (F.T.obj (ε i)).obj (a i)) (i : ℕ) :
    limit.π (F.seqLimitDiagram a ε hε f) (Opposite.op (i + 1)) ≫
        F.seqLimitStep a ε hε f i =
      limit.π (F.seqLimitDiagram a ε hε f) (Opposite.op i) := by
  have h := limit.w (F.seqLimitDiagram a ε hε f) (homOfLE (Nat.le_succ i)).op
  rw [show (F.seqLimitDiagram a ε hε f).map (homOfLE (Nat.le_succ i)).op =
    F.seqLimitStep a ε hε f i from Functor.ofOpSequence_map_homOfLE_succ _ i] at h
  exact h

/-- The metric part of Cruz's completeness argument. It suffices to find an object
interleaved with each term of a sequence whose successive terms are geometrically close. -/
theorem complete_of_geometric_interleavings
    (hlim : ∀ (a : ℕ → C),
      (∀ k, F.IsWeaklyInterleaved (a (k + 1)) (a k) ((2⁻¹ : ℝ≥0) ^ k)) →
      ∃ L : C, ∀ k, F.IsWeaklyInterleaved L (a k)
        (tailSum (fun n : ℕ => (2⁻¹ : ℝ≥0) ^ n) k)) :
    IsCompleteDist F.interleavingDist := by
  letI := F.lpCat
  let e : C ≃ Kleisli F.monad := ⟨fun x => Kleisli.mk _ x, fun x => x.of,
    fun _ => rfl, fun _ => rfl⟩
  apply isCompleteDist_of_equiv _ _ e (fun x y => (F.interleavingDist_eq x y).symm)
  intro x hx
  have hE := LPCat.interleavingDist_isEPMetric (C := Kleisli F.monad)
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
  obtain ⟨L, hL⟩ := hlim (fun k => (x (N k)).of) (fun k =>
    (F.isWeaklyInterleaved_iff _ _ _).2 (hpair k))
  have hdist : ∀ i, LPCat.interleavingDist (x (N i)) (e L) ≤ (tailSum ε i : ℝ≥0∞) := fun i => by
    rw [hE.symm]
    exact iInf₂_le (tailSum ε i) ((F.isWeaklyInterleaved_iff _ _ _).1 (hL i))
  have htail : Filter.Tendsto (fun i => tailSum ε i) Filter.atTop (𝓝 0) := by
    have := NNReal.tendsto_sum_nat_add ε
    simpa [tailSum, add_comm] using this
  refine ⟨e L, ?_⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro r hr
  have hr2 : (0 : ℝ≥0∞) < r / 2 := ENNReal.half_pos hr.ne'
  obtain ⟨N0, hN0⟩ := hx _ hr2
  have hev : ∀ᶠ i in Filter.atTop, (tailSum ε i : ℝ≥0∞) < r / 2 := by
    have := ENNReal.tendsto_coe.2 htail
    exact this.eventually (gt_mem_nhds (by simpa using hr2))
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 hev
  refine Filter.eventually_atTop.2 ⟨N0, fun i hi => ?_⟩
  set kk := max k0 N0
  have hNk : N0 ≤ N kk := le_trans (le_max_right _ _) (Nat.le_add_right _ _)
  calc LPCat.interleavingDist (x i) (e L)
      ≤ LPCat.interleavingDist (x i) (x (N kk)) + LPCat.interleavingDist (x (N kk)) (e L) :=
        hE.triangle _ _ _
    _ ≤ r / 2 + r / 2 := add_le_add (hN0 _ _ hi hNk).le
        ((hdist kk).trans (hk0 kk (le_max_left _ _)).le)
    _ = r := ENNReal.add_halves r

/-- Theorem 5.2.20 ([Cru19, Theorem 4]): if `C` has sequential limits preserved by every `T ε`,
the interleaving distance of `(C, T)` is complete (no strength assumption). -/
theorem interleavingDist_complete [HasLimitsOfShape ℕᵒᵖ C]
    (hT : ∀ ε, PreservesLimitsOfShape ℕᵒᵖ (F.T.obj ε)) :
    IsCompleteDist F.interleavingDist := by
  apply F.complete_of_geometric_interleavings
  intro a ha
  let ε : ℕ → ℝ≥0 := fun k => (2⁻¹ : ℝ≥0) ^ k
  have hε : Summable ε := (NNReal.hasSum_geometric (by norm_num : (2⁻¹ : ℝ≥0) < 1)).summable
  choose f g hfg using ha
  let D := F.seqLimitDiagram a ε hε f
  refine ⟨limit D, ?_⟩
  intro k
  -- Construct the reverse map using the preserved limit, then prove the two equations.
  sorry

end Flow

section PowYoneda
variable {C : Type u} [Category.{v} C] [LPCat C] [W : WeakPowerStructure C]

open WeakPowerStructure in
/-- Transposition of a `0`-morphism into a weak power. -/
noncomputable def tr (ε : ℝ≥0) (x y : C) : (x ⟶ (pow ε).obj y) ≃ hom x y (ε + 0) :=
  homZero.trans (Equiv.ofBijective (wp x y ε 0) (wp_zero x y ε))

/-- evaluation `y^ε ⟶ y` of weight `ε + 0`. -/
noncomputable def powEval (ε : ℝ≥0) (y : C) : hom ((WeakPowerStructure.pow ε).obj y) y (ε + 0) :=
  tr ε _ y (𝟙 _)

open WeakPowerStructure in
theorem tr_comp_x {x x' y : C} (ε : ℝ≥0) (v : x' ⟶ x) (g : x ⟶ (pow ε).obj y) :
    tr ε x' y (v ≫ g) = S (le_of_eq (by simp [add_comm])) (comp (tr ε x y g) (homZero v)) := by
  have h1 := wp_x (x := x) (x' := x') (y := y) (ε := ε) (δ := 0) v (homZero g)
  unfold tr
  show wp x' y ε 0 (homZero (v ≫ g)) = _
  rw [homZero_comp]
  exact h1

open WeakPowerStructure in
theorem tr_comp_y {x y y' : C} (ε : ℝ≥0) (f : y ⟶ y') (g : x ⟶ (pow ε).obj y) :
    tr ε x y' (g ≫ (pow ε).map f) = S (le_of_eq (by simp)) (comp (homZero f) (tr ε x y g)) := by
  have h1 := wp_y (x := x) (ε := ε) (δ := 0) f (homZero g)
  unfold tr
  show wp x y' ε 0 (homZero (g ≫ (pow ε).map f)) = _
  rw [homZero_comp]
  exact h1

open WeakPowerStructure in
theorem tr_id (ε : ℝ≥0) (y : C) : tr ε ((pow ε).obj y) y (𝟙 _) = powEval ε y := rfl

open WeakPowerStructure in
/-- The structure map `y^ε ⟶ y^δ` for `ε ≤ δ`. -/
noncomputable def powMap {ε δ : ℝ≥0} (h : ε ≤ δ) (y : C) : (pow ε).obj y ⟶ (pow δ).obj y :=
  (tr δ ((pow ε).obj y) y).symm (S (add_le_add h le_rfl) (powEval ε y))

open WeakPowerStructure in
theorem tr_powMap {ε δ : ℝ≥0} (h : ε ≤ δ) (y : C) :
    tr δ ((pow ε).obj y) y (powMap h y) = S (add_le_add h le_rfl) (powEval ε y) :=
  (tr δ ((pow ε).obj y) y).apply_symm_apply _

open WeakPowerStructure in
theorem powMap_self (ε : ℝ≥0) (y : C) : powMap (le_refl ε) y = 𝟙 _ := by
  apply (tr ε ((pow ε).obj y) y).injective
  rw [tr_powMap, tr_id, S_refl]

open WeakPowerStructure in
theorem powMap_comp {ε δ γ : ℝ≥0} (h1 : ε ≤ δ) (h2 : δ ≤ γ) (y : C) :
    powMap h1 y ≫ powMap h2 y = powMap (h1.trans h2) y := by
  apply (tr γ ((pow ε).obj y) y).injective
  rw [tr_comp_x, tr_powMap, tr_powMap]
  have A := tr_comp_x δ (powMap h1 y) (𝟙 ((pow δ).obj y))
  rw [Category.comp_id, tr_powMap, tr_id] at A
  rw [comp_S_l, eq_S_symm (by simp) A.symm]
  simp only [S_trans]

open WeakPowerStructure in
/-- Naturality of the evaluation. -/
theorem powEval_nat {y y' : C} (ε : ℝ≥0) (f : y ⟶ y') :
    comp (powEval ε y') (homZero ((pow ε).map f)) =
      S (le_of_eq (by simp [add_comm])) (comp (homZero f) (powEval ε y)) := by
  have A := tr_comp_x ε ((pow ε).map f) (𝟙 ((pow ε).obj y'))
  have B := tr_comp_y ε f (𝟙 ((pow ε).obj y))
  rw [Category.id_comp, tr_id] at B
  rw [Category.comp_id, tr_id] at A
  rw [eq_S_symm (by simp) (A.symm.trans B)]
  simp only [S_trans]

open WeakPowerStructure in
theorem powMap_nat {ε δ : ℝ≥0} (h : ε ≤ δ) {y y' : C} (f : y ⟶ y') :
    (pow ε).map f ≫ powMap h y' = powMap h y ≫ (pow δ).map f := by
  apply (tr δ ((pow ε).obj y) y').injective
  rw [tr_comp_x, tr_comp_y, tr_powMap, tr_powMap, comp_S_l, comp_S_r, powEval_nat]
  simp only [S_trans]

open WeakPowerStructure in
theorem tr_comp_powMap {ε δ : ℝ≥0} (h : ε ≤ δ) {x y : C} (g : x ⟶ (pow ε).obj y) :
    tr δ x y (g ≫ powMap h y) = S (add_le_add h le_rfl) (tr ε x y g) := by
  have A := tr_comp_x ε g (𝟙 ((pow ε).obj y))
  rw [Category.comp_id, tr_id] at A
  rw [tr_comp_x, tr_powMap, comp_S_l, eq_S_symm (by simp) A.symm]
  simp only [S_trans]

open WeakPowerStructure in
/-- The functor `ε ↦ (y ↦ y^ε)`. -/
noncomputable def powFlowT : ℝ≥0 ⥤ (C ⥤ C) where
  obj ε := pow ε
  map {ε δ} h :=
    { app := fun y => powMap (leOfHom h) y
      naturality := fun y y' f => powMap_nat (leOfHom h) f }
  map_id := by intro ε; apply NatTrans.ext; funext y; exact powMap_self ε y
  map_comp := by
    intro ε δ γ h1 h2; apply NatTrans.ext; funext y
    exact (powMap_comp (leOfHom h1) (leOfHom h2) y).symm

open WeakPowerStructure in
/-- The unit `y ⟶ y^0`. -/
noncomputable def powU (y : C) : y ⟶ (pow 0).obj y :=
  (tr 0 y y).symm (S zero_le (idHom y))

open WeakPowerStructure in
theorem tr_powU (y : C) : tr 0 y y (powU y) = S zero_le (idHom y) :=
  (tr 0 y y).apply_symm_apply _

open WeakPowerStructure in
theorem powU_nat {y y' : C} (f : y ⟶ y') :
    f ≫ powU y' = powU y ≫ (pow 0).map f := by
  apply (tr 0 y y').injective
  rw [tr_comp_x, tr_comp_y, tr_powU, tr_powU, comp_S_l, comp_S_r, id_comp', comp_id']
  simp only [S_trans]

open WeakPowerStructure in
/-- The multiplication `(y^δ)^ε ⟶ y^(ε+δ)`. -/
noncomputable def powMu (ε δ : ℝ≥0) (y : C) :
    (pow ε).obj ((pow δ).obj y) ⟶ (pow (ε + δ)).obj y :=
  (tr (ε + δ) _ y).symm (S (le_of_eq (by simp [add_comm, add_left_comm]))
    (comp (powEval δ y) (powEval ε ((pow δ).obj y))))

open WeakPowerStructure in
theorem tr_powMu (ε δ : ℝ≥0) (y : C) :
    tr (ε + δ) _ y (powMu ε δ y) = S (le_of_eq (by simp [add_comm, add_left_comm]))
      (comp (powEval δ y) (powEval ε ((pow δ).obj y))) :=
  (tr _ _ y).apply_symm_apply _

open WeakPowerStructure in
theorem powMu_nat (ε δ : ℝ≥0) {y y' : C} (f : y ⟶ y') :
    (pow ε).map ((pow δ).map f) ≫ powMu ε δ y' = powMu ε δ y ≫ (pow (ε + δ)).map f := by
  apply (tr (ε + δ) _ y').injective
  rw [tr_comp_x, tr_comp_y, tr_powMu, tr_powMu, comp_S_l, comp_S_r]
  have e1 := powEval_nat ε ((pow δ).map f)
  have e2 := powEval_nat δ f
  rw [← LPCat.assoc, e1, comp_S_r, assoc', e2, assoc' (powEval ε ((pow δ).obj y)) (powEval δ y) (homZero f)]
  simp only [comp_S_l, S_trans]

open WeakPowerStructure in
theorem eval_powMap {ε δ : ℝ≥0} (h : ε ≤ δ) (y : C) :
    comp (powEval δ y) (homZero (powMap h y)) =
      S (le_of_eq (by simp [add_comm])) (S (add_le_add h le_rfl) (powEval ε y)) := by
  have A := tr_comp_x δ (powMap h y) (𝟙 ((pow δ).obj y))
  rw [Category.comp_id, tr_id, tr_powMap] at A
  exact eq_S_symm (by simp [add_comm]) A.symm

open WeakPowerStructure in
theorem eval_powU (y : C) :
    comp (powEval 0 y) (homZero (powU y)) =
      S (le_of_eq (by simp)) (S (zero_le : (0 : ℝ≥0) ≤ 0 + 0) (idHom y)) := by
  have A := tr_comp_x 0 (powU y) (𝟙 ((pow 0).obj y))
  rw [Category.comp_id, tr_id, tr_powU] at A
  exact eq_S_symm (by simp) A.symm

open WeakPowerStructure in
theorem powU_mu_powMap (ε : ℝ≥0) (x : C) :
    powU ((pow ε).obj x) ≫ powMu 0 ε x ≫ powMap (le_of_eq (zero_add ε)) x = 𝟙 _ := by
  apply (tr ε _ x).injective
  rw [tr_id, tr_comp_x, tr_comp_powMap, tr_powMu]
  simp only [comp_S_l]
  rw [← LPCat.assoc, eval_powU]
  simp only [comp_S_r, comp_id', S_trans, S_refl]

open WeakPowerStructure in
theorem powU_mu_powMap' (ε : ℝ≥0) (x : C) :
    (pow ε).map (powU x) ≫ powMu ε 0 x ≫ powMap (le_of_eq (add_zero ε)) x = 𝟙 _ := by
  apply (tr ε _ x).injective
  rw [tr_id, tr_comp_x, tr_comp_powMap, tr_powMu]
  simp only [comp_S_l]
  rw [← LPCat.assoc, powEval_nat]
  simp only [comp_S_r]
  rw [assoc', eval_powU]
  simp only [comp_S_l, comp_S_r, id_comp', S_trans, S_refl]

open WeakPowerStructure in
theorem eval_powMu (ε δ : ℝ≥0) (y : C) :
    comp (powEval (ε + δ) y) (homZero (powMu ε δ y)) =
      S (le_of_eq (by ring) : ((ε + 0) + (δ + 0) : ℝ≥0) ≤ 0 + ((ε + δ) + 0))
        (comp (powEval δ y) (powEval ε ((pow δ).obj y))) := by
  have A := tr_comp_x (ε + δ) (powMu ε δ y) (𝟙 ((pow (ε + δ)).obj y))
  rw [Category.comp_id, tr_id, tr_powMu] at A
  rw [eq_S_symm (by simp [add_comm]) A.symm]
  simp only [S_trans]

open WeakPowerStructure in
theorem powMu_assoc (ε δ γ : ℝ≥0) (x : C) :
    (pow ε).map (powMu δ γ x) ≫ powMu ε (δ + γ) x ≫ powMap (le_of_eq (add_assoc ε δ γ).symm) x =
      powMu ε δ ((pow γ).obj x) ≫ powMu (ε + δ) γ x := by
  apply (tr (ε + δ + γ) _ x).injective
  rw [tr_comp_x, tr_comp_powMap, tr_powMu, tr_comp_x, tr_powMu]
  simp only [comp_S_l]
  rw [← LPCat.assoc (homZero ((pow ε).map (powMu δ γ x))),
    ← LPCat.assoc (homZero (powMu ε δ ((pow γ).obj x))), powEval_nat, eval_powMu ε δ]
  simp only [comp_S_r]
  rw [assoc' (powEval ε _) (homZero (powMu δ γ x)) (powEval (δ + γ) x), eval_powMu δ γ]
  simp only [comp_S_l, S_trans]
  rw [← LPCat.assoc (powEval ε ((pow δ).obj ((pow γ).obj x))) (powEval δ ((pow γ).obj x))
    (powEval γ x)]
  simp only [S_trans]

open WeakPowerStructure in
theorem powMu_naturality {ε ε' δ δ' : ℝ≥0} (hε : ε ≤ ε') (hδ : δ ≤ δ') (x : C) :
    (pow ε).map (powMap hδ x) ≫ powMap hε ((pow δ').obj x) ≫ powMu ε' δ' x =
      powMu ε δ x ≫ powMap (add_le_add hε hδ) x := by
  apply (tr (ε' + δ') _ x).injective
  rw [tr_comp_x, tr_comp_x, tr_powMu, tr_comp_powMap, tr_powMu]
  simp only [comp_S_l]
  rw [← LPCat.assoc (homZero (powMap hε ((pow δ').obj x))) (powEval ε' ((pow δ').obj x))
    (powEval δ' x)]
  simp only [comp_S_l]
  rw [← LPCat.assoc (homZero ((pow ε).map (powMap hδ x)))
    (comp (powEval ε' ((pow δ').obj x)) (homZero (powMap hε ((pow δ').obj x)))) (powEval δ' x),
    eval_powMap hε]
  simp only [comp_S_l]
  rw [powEval_nat]
  simp only [comp_S_r]
  rw [assoc' (powEval ε ((pow δ).obj x)) (homZero (powMap hδ x)) (powEval δ' x), eval_powMap hδ]
  simp only [comp_S_l, comp_S_r, S_trans]

open WeakPowerStructure in
/-- The flow on the underlying category of a locally persistent category powered by
representables. -/
noncomputable def powFlow : Flow C where
  T := powFlowT
  u := { app := powU, naturality := fun _ _ f => powU_nat f }
  μ := fun ε δ => { app := powMu ε δ, naturality := fun _ _ f => powMu_nat ε δ f }
  unit_left := fun ε x => powU_mu_powMap ε x
  unit_right := fun ε x => powU_mu_powMap' ε x
  assoc := fun ε δ γ x => powMu_assoc ε δ γ x
  μ_naturality := fun hε hδ x => powMu_naturality hε hδ x

open WeakPowerStructure in
/-- The inverse of the unit. -/
noncomputable def powUInv (y : C) : (pow 0).obj y ⟶ y :=
  homZero.symm (S (le_of_eq (add_zero 0)) (powEval 0 y))

open WeakPowerStructure in
theorem homZero_powUInv (y : C) :
    homZero (powUInv y) = S (le_of_eq (add_zero 0)) (powEval 0 y) :=
  homZero.apply_symm_apply _

open WeakPowerStructure in
instance isIso_powU (y : C) : IsIso (powU y) := by
  refine ⟨⟨powUInv y, ?_, ?_⟩⟩
  · apply homZero.injective
    rw [homZero_comp, homZero_powUInv]
    simp only [comp_S_l]
    rw [eval_powU]
    simp only [S_trans]
    exact S_refl _
  · apply (tr 0 _ y).injective
    rw [tr_comp_x, tr_powU, tr_id]
    simp only [comp_S_l]
    rw [homZero_powUInv]
    simp only [comp_S_r, id_comp', S_trans]
    exact S_refl _


end PowYoneda

/-- A category powered by representables has a weak power structure. -/
@[reducible] noncomputable def PoweredByRepresentables.toWeak (C : Type u) [Category.{v} C]
    [LPCat C] [P : PoweredByRepresentables C] : WeakPowerStructure C where
  pow := PoweredByRepresentables.pow
  wp x y ε δ := PoweredByRepresentables.powIso x y ε δ
  wp_zero x y ε := (PoweredByRepresentables.powIso x y ε 0).bijective
  wp_S := fun h u => PoweredByRepresentables.powIso_S h u
  wp_x := fun {x x' y ε δ} v u => by
    have h1 := PoweredByRepresentables.powIso_x (x := x) (x' := x') (y := y) (ε := ε) (r := δ)
      (δ := 0) (homZero v) u
    rw [PoweredByRepresentables.powIso_S, h1]
    simp only [S_trans]
  wp_y := fun {x y y' ε δ} f u => PoweredByRepresentables.powIso_y f u

section PowStrong
variable {C : Type u} [Category.{v} C] [LPCat C] [P : PoweredByRepresentables C]

attribute [local instance] PoweredByRepresentables.toWeak

theorem powEval_eq (ε : ℝ≥0) (y : C) : powEval ε y =
    PoweredByRepresentables.powIso ((PoweredByRepresentables.pow ε).obj y) y ε 0 (homZero (𝟙 _)) := rfl

theorem powIso_eq {x y : C} (ε r : ℝ≥0)
    (w : hom x ((PoweredByRepresentables.pow ε).obj y) r) :
    PoweredByRepresentables.powIso x y ε r w =
      S (le_of_eq (by rw [add_zero, add_comm])) (comp (powEval ε y) w) := by
  rw [powEval_eq]
  have h1 := PoweredByRepresentables.powIso_x (x := (PoweredByRepresentables.pow ε).obj y)
    (x' := x) (y := y) (ε := ε) (r := 0) (δ := r) w (homZero (𝟙 _))
  have h2 : comp (homZero (𝟙 ((PoweredByRepresentables.pow ε).obj y))) w =
      S (le_of_eq (add_zero r).symm) w := id_comp' (C := C) w
  rw [h2, PoweredByRepresentables.powIso_S] at h1
  have h3 := congrArg (S (C := C) (le_of_eq (show ε + (r + 0) = ε + r by rw [add_zero]))) h1
  rw [S_trans, S_refl] at h3
  rw [S_trans] at h3
  exact h3

open WeakPowerStructure in
/-- Auxiliary: the `(ε+0)`-morphism `y^(ε+δ) ⟶ y^δ`. -/
noncomputable def powNuAux (ε δ : ℝ≥0) (y : C) : hom ((pow (ε + δ)).obj y) ((pow δ).obj y) (ε + 0) :=
  (PoweredByRepresentables.powIso ((pow (ε + δ)).obj y) y δ (ε + 0)).symm
    (S (le_of_eq (by ring) : ((ε + δ) + 0 : ℝ≥0) ≤ δ + (ε + 0)) (powEval (ε + δ) y))

open WeakPowerStructure in
theorem powIso_powNuAux (ε δ : ℝ≥0) (y : C) :
    PoweredByRepresentables.powIso ((pow (ε + δ)).obj y) y δ (ε + 0) (powNuAux ε δ y) =
      S (le_of_eq (by ring) : ((ε + δ) + 0 : ℝ≥0) ≤ δ + (ε + 0)) (powEval (ε + δ) y) :=
  (PoweredByRepresentables.powIso _ y δ (ε + 0)).apply_symm_apply _

open WeakPowerStructure in
/-- The inverse of the multiplication. -/
noncomputable def powNu (ε δ : ℝ≥0) (y : C) :
    (pow (ε + δ)).obj y ⟶ (pow ε).obj ((pow δ).obj y) :=
  (tr ε ((pow (ε + δ)).obj y) ((pow δ).obj y)).symm (powNuAux ε δ y)

open WeakPowerStructure in
theorem tr_powNu (ε δ : ℝ≥0) (y : C) :
    tr ε _ ((pow δ).obj y) (powNu ε δ y) = powNuAux ε δ y :=
  (tr ε _ _).apply_symm_apply _

open WeakPowerStructure in
theorem powNu_powMu (ε δ : ℝ≥0) (y : C) : powNu ε δ y ≫ powMu ε δ y = 𝟙 _ := by
  apply (tr (ε + δ) _ y).injective
  rw [tr_id, tr_comp_x, tr_powMu]
  simp only [comp_S_l]
  rw [← LPCat.assoc]
  have A := tr_comp_x ε (powNu ε δ y) (𝟙 ((pow ε).obj ((pow δ).obj y)))
  rw [Category.comp_id, tr_id, tr_powNu] at A
  rw [eq_S_symm (by simp [add_comm]) A.symm]
  simp only [comp_S_r]
  have B := powIso_eq (x := (pow (ε + δ)).obj y) (y := y) δ (ε + 0) (powNuAux ε δ y)
  rw [powIso_powNuAux] at B
  rw [eq_S_symm (by ring) B]
  simp only [S_trans]

open WeakPowerStructure in
theorem powMu_powNu (ε δ : ℝ≥0) (y : C) : powMu ε δ y ≫ powNu ε δ y = 𝟙 _ := by
  apply (tr ε _ ((pow δ).obj y)).injective
  rw [tr_id, tr_comp_x, tr_powNu]
  have key : PoweredByRepresentables.powIso ((pow ε).obj ((pow δ).obj y)) y δ (ε + 0)
      (S (le_of_eq (zero_add (ε + 0))) (comp (powNuAux ε δ y) (homZero (powMu ε δ y)))) =
      PoweredByRepresentables.powIso ((pow ε).obj ((pow δ).obj y)) y δ (ε + 0) (powEval ε ((pow δ).obj y)) := by
    rw [PoweredByRepresentables.powIso_S, PoweredByRepresentables.powIso_x, powIso_powNuAux,
      powIso_eq δ (ε + 0) (powEval ε ((pow δ).obj y))]
    simp only [comp_S_l, S_trans]
    rw [eval_powMu]
    simp only [S_trans]
  have := (PoweredByRepresentables.powIso ((pow ε).obj ((pow δ).obj y)) y δ (ε + 0)).injective key
  rw [← this]

open WeakPowerStructure in
instance isIso_powMu (ε δ : ℝ≥0) (y : C) : IsIso (powMu ε δ y) :=
  ⟨⟨powNu ε δ y, powMu_powNu ε δ y, powNu_powMu ε δ y⟩⟩

end PowStrong

/-- Proposition 5.2.17: a locally persistent category powered by representables gives a strong
flow on its underlying category, with `T ε = y ↦ y^ε`. -/
theorem exists_strongFlow_of_powered (C : Type u) [Category.{v} C] [LPCat C]
    [P : PoweredByRepresentables C] :
    ∃ F : Flow C, F.IsStrong ∧ ∀ ε, F.T.obj ε = PoweredByRepresentables.pow ε := by
  letI : WeakPowerStructure C := PoweredByRepresentables.toWeak C
  refine ⟨powFlow, ⟨?_, fun ε δ => ?_⟩, fun ε => rfl⟩
  · have : ∀ X : C, IsIso (powFlow.u.app X) := fun X => isIso_powU X
    exact NatIso.isIso_of_isIso_app _
  · have : ∀ X : C, IsIso ((powFlow.μ ε δ).app X) := fun X => isIso_powMu ε δ X
    exact NatIso.isIso_of_isIso_app _

/-- Lemma 5.2.13: a weak power structure gives a semi-strong flow on the underlying category
(with `T ε y = ε ⋔ y`). -/
theorem exists_semiStrongFlow_of_weakPower (C : Type u) [Category.{v} C] [LPCat C]
    [W : WeakPowerStructure C] :
    ∃ F : Flow C, F.IsSemiStrong ∧ ∀ ε, F.T.obj ε = WeakPowerStructure.pow ε := by
  refine ⟨powFlow, ?_, fun ε => rfl⟩
  have : ∀ X : C, IsIso (powFlow.u.app X) := fun X => isIso_powU X
  exact NatIso.isIso_of_isIso_app _

/-- Proposition 5.2.21: if `C` has a weak power structure, sequential limits in `C₀`, and the
weak powers preserve sequential limits, then `d_I` is complete. -/
theorem interleavingDist_complete_of_weakPower (C : Type u) [Category.{v} C] [LPCat C]
    [W : WeakPowerStructure C] [HasLimitsOfShape ℕᵒᵖ C]
    (h : ∀ ε, PreservesLimitsOfShape ℕᵒᵖ (WeakPowerStructure.pow (C := C) ε)) :
    IsCompleteDist (interleavingDist (C := C)) := by
  sorry

end ScoccolaPhd
