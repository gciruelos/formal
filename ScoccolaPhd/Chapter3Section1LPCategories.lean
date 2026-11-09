import Mathlib
import ScoccolaPhd.Chapter2Section4EnrichedPersistent

/-!
# §§3.1–3.3: locally persistent categories and their constructions

Contents:
* Chapter 3.1: Locally persistent categories
* Chapter 3.2: Category theory of locally persistent categories
* Chapter 3.3: Relative locally persistent categories
-/

universe u v u' v'

namespace ScoccolaPhd

/-! ## Chapter 3.1: Locally persistent categories

Definition 3.1.1 unfolded: a locally persistent category is a category enriched in `Set^{ℝ≥0}`.
We present it, as the thesis remarks, as *a category with extra structure*: the ambient
`Category C` is the underlying category `C₀`, and `LPCat C` adds the approximate morphisms
`hom x y ε` (with `hom x y 0 ≃ (x ⟶ y)`), composition, and shifts. Composition indices are
written exactly as in the thesis, `comp g f : hom x z (ε + δ)`, and the unit/associativity
laws are stated by re-indexing along `add_zero`, `zero_add`, `add_assoc`.

Most proofs are given; the remaining ones are `sorry`. -/

section Basic

open CategoryTheory
open scoped NNReal ENNReal

/-- Definition 3.1.1: a locally persistent category structure on a category `C` (whose
morphisms are the 0-morphisms). -/
class LPCat (C : Type u) [Category.{v} C] where
  /-- `ε`-approximate morphisms. -/
  hom : C → C → ℝ≥0 → Type v
  /-- 0-morphisms are the morphisms of the underlying category. -/
  homZero : ∀ {x y : C}, (x ⟶ y) ≃ hom x y 0
  /-- composition `hom y z δ × hom x y ε → hom x z (ε + δ)`. -/
  comp : ∀ {x y z : C} {ε δ : ℝ≥0}, hom y z δ → hom x y ε → hom x z (ε + δ)
  /-- the shift operation `S_{ε,δ}`. -/
  S : ∀ {x y : C} {ε δ : ℝ≥0}, ε ≤ δ → hom x y ε → hom x y δ
  id_comp : ∀ {x y : C} {ε : ℝ≥0} (f : hom x y ε),
    S (le_of_eq (add_zero ε)) (comp (homZero (𝟙 y)) f) = f
  comp_id : ∀ {x y : C} {ε : ℝ≥0} (f : hom x y ε),
    S (le_of_eq (zero_add ε)) (comp f (homZero (𝟙 x))) = f
  assoc : ∀ {x y z w : C} {ε δ γ : ℝ≥0} (f : hom x y ε) (g : hom y z δ) (h : hom z w γ),
    S (le_of_eq (add_assoc ε δ γ)) (comp h (comp g f)) = comp (comp h g) f
  S_refl : ∀ {x y : C} {ε : ℝ≥0} (f : hom x y ε), S le_rfl f = f
  S_trans : ∀ {x y : C} {ε δ γ : ℝ≥0} (h₁ : ε ≤ δ) (h₂ : δ ≤ γ) (f : hom x y ε),
    S h₂ (S h₁ f) = S (h₁.trans h₂) f
  comp_S : ∀ {x y z : C} {ε ε' δ δ' : ℝ≥0} (hε : ε ≤ ε') (hδ : δ ≤ δ')
    (f : hom x y ε) (g : hom y z δ),
    comp (S hδ g) (S hε f) = S (add_le_add hε hδ) (comp g f)
  /-- the underlying category is compatible with the approximate composition -/
  homZero_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z),
    homZero (f ≫ g) = S (le_of_eq (add_zero 0)) (comp (homZero g) (homZero f))

namespace LPCat

variable {C : Type u} [Category.{v} C] [LPCat C]

/-- The identity 0-morphism. -/
def idHom (x : C) : hom x x 0 := homZero (𝟙 x)

/-- Re-index an approximate morphism along an equality of indices. -/
def reindex {x y : C} {ε δ : ℝ≥0} (h : ε = δ) (f : hom x y ε) : hom x y δ :=
  S (le_of_eq h) f

/-- Definition 3.1.8: `f` and `g` form an `(ε, δ)`-interleaving. -/
def IsInterleavingPair {x y : C} {ε δ : ℝ≥0} (f : hom x y ε) (g : hom y x δ) : Prop :=
  comp g f = S (zero_le) (idHom x) ∧ comp f g = S (zero_le) (idHom y)

/-- Definition 3.1.8: an `(ε, δ)`-interleaving between `x` and `y`. -/
structure Interleaving (x y : C) (ε δ : ℝ≥0) where
  f : hom x y ε
  g : hom y x δ
  isPair : IsInterleavingPair f g

/-- Definition 3.1.8: `x` and `y` are `δ`-interleaved. -/
def IsInterleaved (x y : C) (δ : ℝ≥0) : Prop :=
  Nonempty (Interleaving x y δ δ)

/-- The hom-persistent set `Hom_C(x, y) : ℝ≥0 ⥤ Type`. -/
def homFunctor (x y : C) : ℝ≥0 ⥤ Type v where
  obj ε := hom x y ε
  map {ε δ} h := TypeCat.ofHom (S (leOfHom h))
  map_id := by intro ε; ext f; exact S_refl f
  map_comp := by intro a b c h₁ h₂; ext f; exact (S_trans _ _ f).symm

/-- Definition 3.1.11: the interleaving distance. -/
noncomputable def interleavingDist (x y : C) : ℝ≥0∞ :=
  ⨅ (δ : ℝ≥0) (_ : IsInterleaved x y δ), (δ : ℝ≥0∞)

/-- Notation 3.2.1: the triangle `h : x →γ z`, `f : x →ε y`, `g : y →δ z` commutes if
`S h = S (g ∘ f)` after shifting both to `max γ (ε + δ)`. -/
def Commutes {x y z : C} {ε δ γ : ℝ≥0} (f : hom x y ε) (g : hom y z δ) (h : hom x z γ) :
    Prop :=
  S (le_max_left γ (ε + δ)) h = S (le_max_right γ (ε + δ)) (comp g f)

/-- A commutative square `g₁ ∘ f₁ = g₂ ∘ f₂`, compared after shifting to the maximum index. -/
def SqCommutes {x y₁ y₂ z : C} {ε₁ δ₁ ε₂ δ₂ : ℝ≥0} (f₁ : hom x y₁ ε₁) (g₁ : hom y₁ z δ₁)
    (f₂ : hom x y₂ ε₂) (g₂ : hom y₂ z δ₂) : Prop :=
  S (le_max_left (ε₁ + δ₁) (ε₂ + δ₂)) (comp g₁ f₁) =
    S (le_max_right (ε₁ + δ₁) (ε₂ + δ₂)) (comp g₂ f₂)

/-! ### Calculus of shifts -/

theorem comp_S_l {x y z : C} {ε δ δ' : ℝ≥0} (h : δ ≤ δ') (g : hom y z δ) (f : hom x y ε) :
    comp (S h g) f = S (add_le_add le_rfl h) (comp g f) := by
  have := comp_S (le_refl ε) h f g
  rwa [S_refl] at this

theorem comp_S_r {x y z : C} {ε ε' δ : ℝ≥0} (h : ε ≤ ε') (g : hom y z δ) (f : hom x y ε) :
    comp g (S h f) = S (add_le_add h le_rfl) (comp g f) := by
  have := comp_S h (le_refl δ) f g
  rwa [S_refl] at this

theorem assoc' {x y z w : C} {ε δ γ : ℝ≥0} (f : hom x y ε) (g : hom y z δ) (h : hom z w γ) :
    comp h (comp g f) = S (le_of_eq (add_assoc ε δ γ).symm) (comp (comp h g) f) := by
  rw [← LPCat.assoc f g h, S_trans]
  exact (S_refl _).symm

theorem id_comp' {x y : C} {ε : ℝ≥0} (f : hom x y ε) :
    comp (idHom y) f = S (le_of_eq (add_zero ε).symm) f := by
  calc comp (idHom y) f = S le_rfl (comp (homZero (𝟙 y)) f) := (S_refl _).symm
    _ = S (le_of_eq (add_zero ε).symm)
          (S (le_of_eq (add_zero ε)) (comp (homZero (𝟙 y)) f)) := by rw [S_trans]
    _ = S (le_of_eq (add_zero ε).symm) f := by rw [LPCat.id_comp f]

theorem comp_id' {x y : C} {ε : ℝ≥0} (f : hom x y ε) :
    comp f (idHom x) = S (le_of_eq (zero_add ε).symm) f := by
  calc comp f (idHom x) = S le_rfl (comp f (homZero (𝟙 x))) := (S_refl _).symm
    _ = S (le_of_eq (zero_add ε).symm)
          (S (le_of_eq (zero_add ε)) (comp f (homZero (𝟙 x)))) := by rw [S_trans]
    _ = S (le_of_eq (zero_add ε).symm) f := by rw [LPCat.comp_id f]

theorem S_inj_of_eq {x y : C} {ε δ : ℝ≥0} (e : ε = δ) (h : ε ≤ δ) {f g : hom x y ε}
    (H : S h f = S h g) : f = g := by
  subst e
  rwa [S_refl, S_refl] at H

theorem S_max_eq_iff {x y : C} {a b : ℝ≥0} (e : a = b) (X : hom x y a) (Y : hom x y b) :
    S (le_max_left a b) X = S (le_max_right a b) Y ↔ S (le_of_eq e) X = Y := by
  subst e
  constructor
  · intro H
    have H' : S (le_of_eq (max_self a).symm) (S le_rfl X) =
        S (le_of_eq (max_self a).symm) (S le_rfl Y) := by
      simpa [S_trans] using H
    have := S_inj_of_eq (max_self a).symm (le_of_eq (max_self a).symm) H'
    simpa [S_refl] using this
  · intro H
    rw [S_refl] at H
    subst H
    rfl

theorem eq_S_symm {x y : C} {ε δ : ℝ≥0} (e : ε = δ) {X : hom x y ε} {Y : hom x y δ}
    (H : S (le_of_eq e) X = Y) : X = S (le_of_eq e.symm) Y := by
  subst e
  rw [S_refl] at H
  rw [S_refl]
  exact H

theorem Commutes_iff {x y z : C} {ε δ γ : ℝ≥0} (f : hom x y ε) (g : hom y z δ)
    (h : hom x z γ) (e : γ = ε + δ) :
    Commutes f g h ↔ S (le_of_eq e) h = comp g f :=
  S_max_eq_iff e h (comp g f)

theorem SqCommutes_iff {x y₁ y₂ z : C} {ε₁ δ₁ ε₂ δ₂ : ℝ≥0} (f₁ : hom x y₁ ε₁)
    (g₁ : hom y₁ z δ₁) (f₂ : hom x y₂ ε₂) (g₂ : hom y₂ z δ₂) (e : ε₁ + δ₁ = ε₂ + δ₂) :
    SqCommutes f₁ g₁ f₂ g₂ ↔ S (le_of_eq e) (comp g₁ f₁) = comp g₂ f₂ :=
  S_max_eq_iff e (comp g₁ f₁) (comp g₂ f₂)

/-- Remark after Definition 3.1.1: the underlying category together with the 0-morphisms
is `C` itself, with `homZero` compatible with composition; a 0-interleaving is an
isomorphism. -/
theorem isInterleaved_zero_iff {x y : C} : IsInterleaved x y 0 ↔ Nonempty (x ≅ y) := by
  constructor
  · rintro ⟨⟨f, g, h₁, h₂⟩⟩
    refine ⟨⟨homZero.symm f, homZero.symm g, ?_, ?_⟩⟩
    · apply homZero.injective
      rw [homZero_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, h₁, S_trans, S_refl]
      rfl
    · apply homZero.injective
      rw [homZero_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, h₂, S_trans, S_refl]
      rfl
  · rintro ⟨e⟩
    refine ⟨⟨homZero e.hom, homZero e.inv, ?_, ?_⟩⟩
    · have := homZero_comp e.hom e.inv
      rw [e.hom_inv_id] at this
      exact eq_S_symm (add_zero (0 : ℝ≥0)) this.symm
    · have := homZero_comp e.inv e.hom
      rw [e.inv_hom_id] at this
      exact eq_S_symm (add_zero (0 : ℝ≥0)) this.symm

theorem isInterleavingPair_comp {x y z : C} {ε δ : ℝ≥0} {f : hom x y ε} {g : hom y x ε}
    {h : hom y z δ} {i : hom z y δ} (hfg : IsInterleavingPair f g)
    (hhi : IsInterleavingPair h i) :
    IsInterleavingPair (comp h f) (S (le_of_eq (add_comm δ ε)) (comp g i)) := by
  obtain ⟨a1, a2⟩ := hfg
  obtain ⟨b1, b2⟩ := hhi
  constructor
  · rw [comp_S_l, ← LPCat.assoc (comp h f) i g, assoc' f h i, b1, comp_S_l, id_comp']
    simp only [comp_S_r, comp_S_l, a1, S_trans]
  · rw [comp_S_r, ← LPCat.assoc (comp g i) f h, assoc' i g f, a2, comp_S_l, id_comp']
    simp only [comp_S_r, comp_S_l, b2, S_trans]

/-- Lemma 3.1.10. -/
theorem IsInterleaved.trans {x y z : C} {ε δ : ℝ≥0} (h₁ : IsInterleaved x y ε)
    (h₂ : IsInterleaved y z δ) : IsInterleaved x z (ε + δ) := by
  obtain ⟨⟨f, g, hfg⟩⟩ := h₁
  obtain ⟨⟨h, i, hhi⟩⟩ := h₂
  exact ⟨⟨comp h f, S (le_of_eq (add_comm δ ε)) (comp g i), isInterleavingPair_comp hfg hhi⟩⟩

theorem IsInterleaved.refl (x : C) : IsInterleaved x x 0 :=
  ⟨⟨idHom x, idHom x, id_comp' _, id_comp' _⟩⟩

theorem IsInterleaved.symm {x y : C} {δ : ℝ≥0} (h : IsInterleaved x y δ) :
    IsInterleaved y x δ := by
  obtain ⟨⟨f, g, hp⟩⟩ := h
  exact ⟨⟨g, f, hp.2, hp.1⟩⟩

/-- Definition 3.1.11: the interleaving distance is an ep metric on `obj C`. -/
theorem interleavingDist_isEPMetric : IsEPMetric (interleavingDist (C := C)) :=
  isEPMetric_iInf (fun x y a => IsInterleaved x y a) IsInterleaved.refl
    (fun _ _ _ h => h.symm) (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂)

end LPCat

open LPCat

/-- Definition 3.1.6: a locally persistent functor. -/
structure LPFunctor (C : Type u) [Category.{v} C] [LPCat C] (D : Type u') [Category.{v'} D]
    [LPCat D] where
  toFunctor : C ⥤ D
  map : ∀ {x y : C} {ε : ℝ≥0}, hom x y ε → hom (toFunctor.obj x) (toFunctor.obj y) ε
  map_zero : ∀ {x y : C} (f : x ⟶ y), map (homZero f) = homZero (toFunctor.map f)
  map_comp : ∀ {x y z : C} {ε δ : ℝ≥0} (f : hom x y ε) (g : hom y z δ),
    map (comp g f) = comp (map g) (map f)
  map_S : ∀ {x y : C} {ε δ : ℝ≥0} (h : ε ≤ δ) (f : hom x y ε), map (S h f) = S h (map f)

/-- Locally persistent functors preserve `δ`-interleavings. -/
theorem LPFunctor.isInterleaved_map {C : Type u} [Category.{v} C] [LPCat C] {D : Type u'}
    [Category.{v'} D] [LPCat D] (F : LPFunctor C D) {x y : C} {δ : ℝ≥0}
    (h : IsInterleaved x y δ) : IsInterleaved (F.toFunctor.obj x) (F.toFunctor.obj y) δ := by
  have hid : ∀ c : C, F.map (idHom c) = idHom (F.toFunctor.obj c) := fun c => by
    rw [idHom, F.map_zero, CategoryTheory.Functor.map_id]; rfl
  obtain ⟨⟨f, g, h₁, h₂⟩⟩ := h
  refine ⟨⟨F.map f, F.map g, ?_, ?_⟩⟩
  · rw [← F.map_comp, h₁, F.map_S, hid]
  · rw [← F.map_comp, h₂, F.map_S, hid]

/-- Theorem 3.1.12: locally persistent functors are distance non-increasing. -/
theorem LPFunctor.interleavingDist_le {C : Type u} [Category.{v} C] [LPCat C] {D : Type u'}
    [Category.{v'} D] [LPCat D] (F : LPFunctor C D) (x y : C) :
    interleavingDist (F.toFunctor.obj x) (F.toFunctor.obj y) ≤ interleavingDist x y := by
  have hpair : ∀ {a b : C} {ε : ℝ≥0} {f : hom a b ε} {g : hom b a ε},
      IsInterleavingPair f g → IsInterleavingPair (F.map f) (F.map g) := by
    intro a b ε f g ⟨h₁, h₂⟩
    have hid : ∀ c : C, F.map (idHom c) = idHom (F.toFunctor.obj c) := fun c => by
      rw [idHom, F.map_zero, CategoryTheory.Functor.map_id]; rfl
    constructor
    · rw [← F.map_comp, h₁, F.map_S, hid]
    · rw [← F.map_comp, h₂, F.map_S, hid]
  refine le_iInf₂ fun δ hδ => iInf₂_le_of_le δ ?_ le_rfl
  obtain ⟨⟨f, g, hp⟩⟩ := hδ
  exact ⟨⟨F.map f, F.map g, hpair hp⟩⟩

/-- Remark after Definition 3.1.1: the opposite locally persistent category
`hom_{Cᵒᵖ}(x, y)_ε = hom_C(y, x)_ε`. -/
theorem exists_lpcat_op (C : Type u) [Category.{v} C] [LPCat C] :
    ∃ L : LPCat Cᵒᵖ, ∀ (x y : Cᵒᵖ) (ε : ℝ≥0), L.hom x y ε = hom y.unop x.unop ε := by
  let L : LPCat Cᵒᵖ :=
    { hom := fun x y ε => hom y.unop x.unop ε
      homZero :=
        { toFun := fun f => homZero f.unop
          invFun := fun f => (homZero.symm f).op
          left_inv := by intro f; simp
          right_inv := by intro f; simp }
      comp := fun {x y z ε δ} g f => S (le_of_eq (add_comm δ ε)) (comp f g)
      S := fun h f => S h f
      id_comp := by
        intro x y ε f
        change S _ (S _ (comp f (idHom y.unop))) = f
        rw [comp_id', S_trans, S_trans, S_refl]
      comp_id := by
        intro x y ε f
        change S _ (S _ (comp (idHom x.unop) f)) = f
        rw [id_comp', S_trans, S_trans, S_refl]
      assoc := by
        intro x y z w ε δ γ f g h
        simp only [comp_S_l, comp_S_r, S_trans]
        rw [← LPCat.assoc h g f]
        simp only [S_trans]
      S_refl := fun f => S_refl f
      S_trans := fun h₁ h₂ f => S_trans h₁ h₂ f
      comp_S := by
        intro x y z ε ε' δ δ' hε hδ f g
        rw [comp_S, S_trans, S_trans]
      homZero_comp := by
        intro x y z f g
        change homZero (g.unop ≫ f.unop) = _
        rw [homZero_comp, S_trans]
        rfl }
  exact ⟨L, fun _ _ _ => rfl⟩

/-- Example 3.1.4 (the structure): ep metric spaces form a locally persistent category whose
`ε`-morphisms are the maps with `d P p p' + ε ≥ d Q (f p) (f p')`. -/
def epMetLPCatStd : LPCat EPMet.{u} where
  hom := fun P Q ε => {f : P → Q // ∀ p p', edist (f p) (f p') ≤ edist p p' + ε}
  homZero :=
    { toFun := fun f => ⟨f.1, by simpa [IsDistNonIncreasing] using f.2⟩
      invFun := fun f => ⟨f.1, by simpa [IsDistNonIncreasing] using f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  comp := fun {P Q R ε δ} g f => ⟨g.1 ∘ f.1, fun p p' => by
    calc
      edist (g.1 (f.1 p)) (g.1 (f.1 p')) ≤ edist (f.1 p) (f.1 p') + δ := g.2 _ _
      _ ≤ (edist p p' + ε) + δ := add_le_add (f.2 _ _) le_rfl
      _ = edist p p' + (↑(ε + δ) : ℝ≥0∞) := by rw [ENNReal.coe_add, add_assoc]⟩
  S := fun h f => ⟨f.1, fun p p' => (f.2 p p').trans
    (add_le_add le_rfl (ENNReal.coe_le_coe.mpr h))⟩
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  assoc := fun _ _ _ => rfl
  S_refl := fun _ => rfl
  S_trans := fun _ _ _ => rfl
  comp_S := fun _ _ _ _ => rfl
  homZero_comp := fun _ _ => rfl

/-- Example 3.1.4: ep metric spaces form a locally persistent category whose `ε`-morphisms
are the maps with `d P p p' + ε ≥ d Q (f p) (f p')`. -/
theorem exists_lpcat_epMet :
    ∃ L : @LPCat EPMet.{u} _, ∀ (P Q : EPMet.{u}) (ε : ℝ≥0),
      L.hom P Q ε = {f : P → Q // ∀ p p', edist (f p) (f p') ≤ edist p p' + ε} :=
  ⟨epMetLPCatStd, fun _ _ _ => rfl⟩

end Basic

/-! ## Chapter 3.2: Category theory of locally persistent categories

Diagrams (3.2.1; see `LPCat.Commutes`), free locally persistent categories (3.2.2),
powers and copowers by representables (3.2.3), weighted pullbacks (3.2.4), weighted
sequential limits (3.2.5) and terminal midpoints (3.2.6).
Section 3.2.7 (these as weighted limits) is omitted: it needs the enriched functor category
from the abstract class `FunctorHoms`, which has no instance here.

Proved: 3.2.11 and the `ε = 0` symmetry of weighted pullbacks; the rest are `sorry`. -/

section Constructions

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

open LPCat

/-! ### 3.2.2 Diagrams as functors -/

/-- A locally persistent graph: a set of objects and a persistent set of arrows between
each pair. -/
structure LPGraph where
  obj : Type u
  arr : obj → obj → ℝ≥0 ⥤ Type u

/-- A morphism of locally persistent graphs. -/
structure LPGraphHom (G H : LPGraph.{u}) where
  obj : G.obj → H.obj
  arr : ∀ x y, G.arr x y ⟶ H.arr (obj x) (obj y)

/-- A bundled locally persistent category. -/
structure LPCatB where
  carrier : Type u
  [cat : Category.{u} carrier]
  [lp : LPCat carrier]

attribute [instance] LPCatB.cat LPCatB.lp

/-- The underlying graph `U C` of a locally persistent category (forget composition and
identities). -/
@[reducible] def LPCatB.toGraph (C : LPCatB.{u}) : LPGraph.{u} where
  obj := C.carrier
  arr x y := homFunctor x y

/-! #### The free locally persistent category (Prop 3.2.4) -/

section Free
variable (G : LPGraph.{u})

/-- Syntactic terms of the free locally persistent category on `G`. -/
inductive GExpr : G.obj → G.obj → ℝ≥0 → Type u
  | gen {x y : G.obj} {ε : ℝ≥0} (a : (G.arr x y).obj ε) : GExpr x y ε
  | id (x : G.obj) : GExpr x x 0
  | comp {x y z : G.obj} {ε δ : ℝ≥0} (g : GExpr y z δ) (f : GExpr x y ε) : GExpr x z (ε + δ)
  | shift {x y : G.obj} {ε δ : ℝ≥0} (h : ε ≤ δ) (f : GExpr x y ε) : GExpr x y δ

variable {G}

/-- Interpretation of terms in a locally persistent category along a graph morphism. -/
def GExpr.interp {C : LPCatB.{u}} (φ : LPGraphHom G C.toGraph) :
    ∀ {x y : G.obj} {ε : ℝ≥0}, GExpr G x y ε → hom (C := C.carrier) (φ.obj x) (φ.obj y) ε
  | _, _, _, .gen a => ((φ.arr _ _).app _) a
  | _, _, _, .id x => idHom (C := C.carrier) (φ.obj x)
  | _, _, _, .comp g f => LPCat.comp (GExpr.interp φ g) (GExpr.interp φ f)
  | _, _, _, .shift h f => LPCat.S h (GExpr.interp φ f)

/-- Two terms are equal if they are equal under every interpretation. -/
def GRel {x y : G.obj} {ε : ℝ≥0} (t t' : GExpr G x y ε) : Prop :=
  ∀ (C : LPCatB.{u}) (φ : LPGraphHom G C.toGraph), t.interp φ = t'.interp φ

instance GSetoid (x y : G.obj) (ε : ℝ≥0) : Setoid (GExpr G x y ε) where
  r := GRel
  iseqv := ⟨fun _ _ _ => rfl, fun h C φ => (h C φ).symm, fun h h' C φ => (h C φ).trans (h' C φ)⟩

/-- Approximate morphisms of the free locally persistent category. -/
def GHom (G : LPGraph.{u}) (x y : G.obj) (ε : ℝ≥0) : Type u := Quotient (GSetoid x y ε)


namespace GHom

variable {x y z : G.obj} {ε δ : ℝ≥0}

/-- The class of a term. -/
def mk (t : GExpr G x y ε) : GHom G x y ε := Quotient.mk (GSetoid x y ε) t

/-- Interpretation of classes. -/
def interp {C : LPCatB.{u}} (φ : LPGraphHom G C.toGraph) (f : GHom G x y ε) :
    hom (C := C.carrier) (φ.obj x) (φ.obj y) ε :=
  Quotient.lift (fun t => t.interp φ) (fun _ _ (h : GRel _ _) => h C φ) f

@[simp] theorem interp_mk {C : LPCatB.{u}} (φ : LPGraphHom G C.toGraph) (t : GExpr G x y ε) :
    interp φ (mk t) = t.interp φ := rfl

theorem ext {a b : GHom G x y ε}
    (h : ∀ (C : LPCatB.{u}) (φ : LPGraphHom G C.toGraph), interp φ a = interp φ b) : a = b := by
  induction a using Quotient.inductionOn with | _ s =>
  induction b using Quotient.inductionOn with | _ t =>
  exact Quotient.sound (fun C φ => h C φ)

/-- Composition. -/
def comp (g : GHom G y z δ) (f : GHom G x y ε) : GHom G x z (ε + δ) :=
  Quotient.map₂ (fun g f => GExpr.comp g f) (fun _ _ hg _ _ hf C φ => by
    show LPCat.comp _ _ = LPCat.comp _ _
    rw [(hg : GRel _ _) C φ, (hf : GRel _ _) C φ]) g f

/-- Shift. -/
def shift (h : ε ≤ δ) (f : GHom G x y ε) : GHom G x y δ :=
  Quotient.map (fun f => GExpr.shift h f) (fun _ _ hf C φ => by
    show LPCat.S _ _ = LPCat.S _ _
    rw [(hf : GRel _ _) C φ]) f

/-- The identity 0-morphism. -/
def id (x : G.obj) : GHom G x x 0 := mk (GExpr.id x)

@[simp] theorem interp_comp {C : LPCatB.{u}} (φ : LPGraphHom G C.toGraph) (g : GHom G y z δ)
    (f : GHom G x y ε) : interp φ (comp g f) = LPCat.comp (interp φ g) (interp φ f) := by
  induction g using Quotient.inductionOn with | _ s =>
  induction f using Quotient.inductionOn with | _ t =>
  rfl

@[simp] theorem interp_shift {C : LPCatB.{u}} (φ : LPGraphHom G C.toGraph) (h : ε ≤ δ)
    (f : GHom G x y ε) : interp φ (shift h f) = LPCat.S h (interp φ f) := by
  induction f using Quotient.inductionOn with | _ t =>
  rfl

@[simp] theorem interp_id {C : LPCatB.{u}} (φ : LPGraphHom G C.toGraph) (x : G.obj) :
    interp φ (id x) = idHom (C := C.carrier) (φ.obj x) := rfl

end GHom

/-- The underlying category of the free locally persistent category. -/
def freeCat (G : LPGraph.{u}) : Category.{u} G.obj where
  Hom x y := GHom G x y 0
  id x := GHom.id x
  comp f g := GHom.shift (le_of_eq (add_zero 0)) (GHom.comp g f)
  id_comp f := by
    refine GHom.ext fun C φ => ?_
    simp only [GHom.interp_shift, GHom.interp_comp, GHom.interp_id]
    rw [comp_id', S_trans]
    exact S_refl _
  comp_id f := by
    refine GHom.ext fun C φ => ?_
    simp only [GHom.interp_shift, GHom.interp_comp, GHom.interp_id]
    rw [id_comp', S_trans]
    exact S_refl _
  assoc f g h := by
    refine GHom.ext fun C φ => ?_
    simp only [GHom.interp_shift, GHom.interp_comp, GHom.interp_id]
    rw [comp_S_r, comp_S_l, assoc', S_trans, S_trans, S_trans]


/-- The locally persistent structure of the free category. -/
def freeLP (G : LPGraph.{u}) : @LPCat G.obj (freeCat G) :=
  @LPCat.mk G.obj (freeCat G) (GHom G) (fun {x y} => Equiv.refl _)
    (fun {x y z ε δ} g f => GHom.comp g f) (fun {x y ε δ} h f => GHom.shift h f)
    (fun {x y ε} f => by
      refine GHom.ext fun C φ => ?_
      simp only [GHom.interp_shift, GHom.interp_comp]
      show S _ (comp (idHom _) _) = _
      rw [id_comp', S_trans]
      exact S_refl _)
    (fun {x y ε} f => by
      refine GHom.ext fun C φ => ?_
      simp only [GHom.interp_shift, GHom.interp_comp]
      show S _ (comp _ (idHom _)) = _
      rw [comp_id', S_trans]
      exact S_refl _)
    (fun {x y z w ε δ γ} f g h => by
      refine GHom.ext fun C φ => ?_
      simp only [GHom.interp_shift, GHom.interp_comp]
      exact LPCat.assoc _ _ _)
    (fun {x y ε} f => by
      refine GHom.ext fun C φ => ?_
      simp only [GHom.interp_shift]
      exact S_refl _)
    (fun {x y ε δ γ} h₁ h₂ f => by
      refine GHom.ext fun C φ => ?_
      simp only [GHom.interp_shift]
      exact S_trans _ _ _)
    (fun {x y z ε ε' δ δ'} hε hδ f g => by
      refine GHom.ext fun C φ => ?_
      simp only [GHom.interp_shift, GHom.interp_comp]
      exact LPCat.comp_S _ _ _ _)
    (fun {x y z} f g => rfl)

/-- The free locally persistent category on `G`. -/
@[reducible] def freeLPCat (G : LPGraph.{u}) : LPCatB.{u} :=
  @LPCatB.mk G.obj (freeCat G) (freeLP G)


/-- The unit `G → U (F G)`. -/
def freeUnit (G : LPGraph.{u}) : LPGraphHom G (freeLPCat G).toGraph where
  obj := fun x => x
  arr := fun x y =>
    { app := fun ε => TypeCat.ofHom (fun a => GHom.mk (GExpr.gen a))
      naturality := fun ε ε' h => by
        apply ConcreteCategory.hom_ext
        intro a
        refine GHom.ext fun C φ => ?_
        have := ConcreteCategory.congr_hom ((φ.arr x y).naturality h) a
        exact this }


attribute [local instance] freeCat freeLP

/-- The extension of `φ` along the unit. -/
def freeLift (G : LPGraph.{u}) (C : LPCatB.{u}) (φ : LPGraphHom G C.toGraph) :
    LPFunctor (freeLPCat G).carrier C.carrier where
  toFunctor :=
    { obj := fun x => φ.obj x
      map := fun {x y} f => (LPCat.homZero (C := C.carrier)).symm (GHom.interp φ f)
      map_id := fun x => by
        apply (LPCat.homZero (C := C.carrier)).injective
        rw [Equiv.apply_symm_apply]
        rfl
      map_comp := fun {x y z} f g => by
        apply (LPCat.homZero (C := C.carrier)).injective
        rw [Equiv.apply_symm_apply, LPCat.homZero_comp, Equiv.apply_symm_apply,
          Equiv.apply_symm_apply]
        show GHom.interp φ (GHom.shift _ (GHom.comp g f)) = _
        rw [GHom.interp_shift]
        exact congrArg _ (GHom.interp_comp φ g f) }
  map := fun {x y ε} f => GHom.interp φ f
  map_zero := fun {x y} f => by
    show _ = LPCat.homZero ((LPCat.homZero (C := C.carrier)).symm _)
    rw [Equiv.apply_symm_apply]
    rfl
  map_comp := fun {x y z ε δ} f g => by
    exact GHom.interp_comp φ g f
  map_S := fun {x y ε δ} h f => by
    exact GHom.interp_shift φ h f


theorem LPFunctor.ext' {C : Type u} [Category.{u} C] [LPCat C] {D : Type u} [Category.{u} D]
    [LPCat D] (F F' : LPFunctor C D) (h1 : F.toFunctor = F'.toFunctor)
    (h2 : ∀ {x y : C} {ε : ℝ≥0} (f : hom x y ε), HEq (F.map f) (F'.map f)) : F = F' := by
  cases F with | mk T m mz mc ms =>
  cases F' with | mk T' m' mz' mc' ms' =>
  simp only at h1 h2
  subst h1
  have : @m = @m' := by
    funext x y ε f
    exact eq_of_heq (h2 f)
  cases this
  rfl


/-- Proposition 3.2.4: the forgetful functor `U : lpCat → lpGph` has a left adjoint `F`
(the free locally persistent category), with unit `u`: every graph morphism `G → U C`
extends uniquely to a locally persistent functor `F G → C`.

**Note.** Stating Proposition 3.2.4 as an existence statement that only prescribes the object map of the extension would
make it not unique (nor does it extend `φ`).  We also require the extension to agree with `φ` on
the arrows of `G` (a `HEq`, as the two sides live over propositionally equal objects). -/
theorem exists_free_lpcat (G : LPGraph.{u}) :
    ∃ (FG : LPCatB.{u}) (unit : LPGraphHom G FG.toGraph),
      ∀ (C : LPCatB.{u}) (φ : LPGraphHom G C.toGraph),
        ∃! Φ : LPFunctor FG.carrier C.carrier,
          (∀ x, Φ.toFunctor.obj (unit.obj x) = φ.obj x) ∧
          ∀ (x y : G.obj) (ε : ℝ≥0) (a : (G.arr x y).obj ε),
            HEq (Φ.map (((unit.arr x y).app ε) a)) (((φ.arr x y).app ε) a) := by
  refine ⟨freeLPCat G, freeUnit G, fun C φ => ⟨freeLift G C φ, ⟨fun x => rfl, fun x y ε a => HEq.rfl⟩, ?_⟩⟩
  rintro Ψ ⟨hobj, harr⟩
  obtain ⟨⟨obj, map, mid, mcomp⟩, mapΨ, mz, mc, ms⟩ := Ψ
  have hobj' : obj = φ.obj := funext fun x => hobj x
  subst hobj'
  have hmap : ∀ {x y : G.obj} {ε : ℝ≥0} (t : GExpr G x y ε),
      mapΨ (GHom.mk t) = GHom.interp φ (GHom.mk t) := by
    intro x y ε t
    induction t with
    | gen a => exact eq_of_heq (harr _ _ _ a)
    | id x =>
      exact (mz (𝟙 x)).trans (congrArg _ (mid x))
    | comp g f ihg ihf =>
      have h := mc (GHom.mk f) (GHom.mk g)
      rw [ihg, ihf] at h
      exact h
    | shift h f ih =>
      have h' := ms h (GHom.mk f)
      rw [ih] at h'
      exact h'
  have hmap' : ∀ {x y : G.obj} {ε : ℝ≥0} (f : GHom G x y ε), mapΨ f = GHom.interp φ f := by
    intro x y ε f
    induction f using Quotient.inductionOn with | _ t => exact hmap t
  have hm : ∀ {x y : G.obj} (f : x ⟶ y),
      map f = (LPCat.homZero (C := C.carrier)).symm (GHom.interp φ f) := by
    intro x y f
    have h1 := mz f
    rw [hmap' (LPCat.homZero f)] at h1
    exact ((Equiv.eq_symm_apply _).2 h1.symm)
  have hmapΨ : @mapΨ = @(freeLift G C φ).map := by
    funext x y ε f
    exact hmap' f
  have hmapF : @map = @(freeLift G C φ).toFunctor.map := by
    funext x y f
    exact hm f
  show LPFunctor.mk _ mapΨ mz mc ms = LPFunctor.mk _ _ _ _ _
  have hF : (⟨φ.obj, map, mid, mcomp⟩ : (freeLPCat G).carrier ⥤ C.carrier) =
      (freeLift G C φ).toFunctor := by
    refine CategoryTheory.Functor.ext (fun x => rfl) (fun x y f => ?_)
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact hm f
  refine LPFunctor.ext' _ _ hF ?_
  intro x y ε f
  exact heq_of_eq (hmap' f)


end Free

/-! ### 3.2.3 Powers and copowers by representables -/

/-- Definition 3.2.6: `C` is powered by representables: for `y : C`, `ε : ℝ≥0` there is
`y^ε`, functorially in `y`, with `Hom(x, y^ε)_r ≅ Hom(x, y)_{ε + r}`, naturally in `r`
(w.r.t. shifts) and in `x`, `y` (w.r.t. 0-morphisms). (Naturality in `x` is required for all approximate morphisms `v`, as for an enriched natural
isomorphism; naturality in `ε` is omitted.) -/
class PoweredByRepresentables (C : Type u) [Category.{v} C] [LPCat C] where
  pow : ℝ≥0 → C ⥤ C
  powIso : ∀ (x y : C) (ε r : ℝ≥0), hom x ((pow ε).obj y) r ≃ hom x y (ε + r)
  powIso_S : ∀ {x y : C} {ε r r' : ℝ≥0} (h : r ≤ r') (u : hom x ((pow ε).obj y) r),
    powIso x y ε r' (S h u) = S (add_le_add le_rfl h) (powIso x y ε r u)
  powIso_x : ∀ {x x' y : C} {ε r δ : ℝ≥0} (v : hom x' x δ) (u : hom x ((pow ε).obj y) r),
    powIso x' y ε (δ + r) (comp u v) =
      S (le_of_eq (add_left_comm δ ε r)) (comp (powIso x y ε r u) v)
  powIso_y : ∀ {x y y' : C} {ε r : ℝ≥0} (f : y ⟶ y') (u : hom x ((pow ε).obj y) r),
    powIso x y' ε r (S (le_of_eq (by simp)) (comp (homZero ((pow ε).map f)) u)) =
      S (le_of_eq (by simp)) (comp (homZero f) (powIso x y ε r u))

/-- Definition 3.2.6: `C` is copowered by representables: `Hom(ε · x, y)_r ≅ Hom(x, y)_{ε+r}`.
(Naturality as for `PoweredByRepresentables`.) -/
class CopoweredByRepresentables (C : Type u) [Category.{v} C] [LPCat C] where
  copow : ℝ≥0 → C ⥤ C
  copowIso : ∀ (x y : C) (ε r : ℝ≥0), hom ((copow ε).obj x) y r ≃ hom x y (ε + r)
  copowIso_S : ∀ {x y : C} {ε r r' : ℝ≥0} (h : r ≤ r') (u : hom ((copow ε).obj x) y r),
    copowIso x y ε r' (S h u) = S (add_le_add le_rfl h) (copowIso x y ε r u)
  copowIso_x : ∀ {x x' y : C} {ε r : ℝ≥0} (f : x' ⟶ x) (u : hom ((copow ε).obj x) y r),
    copowIso x' y ε r (S (le_of_eq (by simp)) (comp u (homZero ((copow ε).map f)))) =
      S (le_of_eq (by simp)) (comp (copowIso x y ε r u) (homZero f))
  copowIso_y : ∀ {x y y' : C} {ε r δ : ℝ≥0} (v : hom y y' δ) (u : hom ((copow ε).obj x) y r),
    copowIso x y' ε (r + δ) (comp v u) =
      S (le_of_eq (add_assoc ε r δ)) (comp v (copowIso x y ε r u))

/-! ### 3.2.4 Weighted pullbacks -/

variable {C : Type u} [Category.{v} C] [LPCat C]

/-- Definition 3.2.10: a weighted pullback of the 0-morphism `k : b ⟶ c` along the
`ε`-morphism `h : a →ε c`. -/
structure WeightedPullback {a b c : C} {ε : ℝ≥0} (h : hom a c ε) (k : b ⟶ c) where
  p : C
  j : p ⟶ a
  f : hom p b ε
  comm : SqCommutes f (homZero k) (homZero j) h
  /-- for every `j' : p' →γ a` and `f' : p' →(ε+γ) b` with `k ∘ f' = h ∘ j'` there is a
  unique `u : p' →γ p` with `j ∘ u = j'` and `f ∘ u = f'`. -/
  univ : ∀ (p' : C) (γ : ℝ≥0) (j' : hom p' a γ) (f' : hom p' b (ε + γ)),
    SqCommutes f' (homZero k) j' h →
      ∃! u : hom p' p γ, Commutes u (homZero j) j' ∧ Commutes u f f'

/-- Definition 4.1.2 (used here): a class `E` of 0-morphisms is stable under weighted
pullbacks if the pullback of a morphism in `E` along any approximate morphism exists and
(every such pullback) is again in `E`.

**Gap (imprecise).** The thesis says "the pullback … is again a morphism in `E`"; weighted
pullbacks are only determined up to isomorphism, so we require every one of them to be in
`E`. -/
@[reducible] def IsStableUnderWeightedPullbacks (E : MorphismProperty C) : Prop :=
  ∀ {a b c : C} {ε : ℝ≥0} (h : hom a c ε) (k : b ⟶ c), E k →
    Nonempty (WeightedPullback h k) ∧ ∀ P : WeightedPullback h k, E P.j

/-- A weighted pullback with `ε = 0` is symmetric: swapping the roles of the two
0-morphisms gives a weighted pullback of `homZero k` along `f`. -/
def WeightedPullback.swap0 {a b c : C} {f : a ⟶ c} {k : b ⟶ c}
    (P : WeightedPullback (homZero f) k) : WeightedPullback (homZero k) f where
  p := P.p
  j := homZero.symm P.f
  f := homZero P.j
  comm := by
    have := (SqCommutes_iff _ _ _ _ (rfl : (0 : ℝ≥0) + 0 = 0 + 0)).1 P.comm
    rw [SqCommutes_iff _ _ _ _ (rfl : (0 : ℝ≥0) + 0 = 0 + 0), Equiv.apply_symm_apply]
    rw [S_refl] at this ⊢
    exact this.symm
  univ := by
    intro p' γ j' f' hsq
    have hsq' : SqCommutes (S (le_of_eq (zero_add γ).symm) j' : hom p' _ (0 + γ))
        (homZero k) (S (le_of_eq (zero_add γ)) f' : hom p' _ γ) (homZero f) := by
      rw [SqCommutes_iff _ _ _ _ (by simp : (0 + γ) + 0 = γ + 0)]
      rw [SqCommutes_iff _ _ _ _ (by simp : (0 + γ) + 0 = γ + 0)] at hsq
      rw [comp_S_r, comp_S_r, ← hsq]
      simp only [S_trans]
    obtain ⟨u, ⟨hu1, hu2⟩, huu⟩ := P.univ p' γ _ _ hsq'
    refine ⟨u, ⟨?_, ?_⟩, ?_⟩
    · rw [Equiv.apply_symm_apply]
      rw [Commutes_iff _ _ _ (by simp : γ = γ + 0)]
      have := (Commutes_iff _ _ _ (by simp : 0 + γ = γ + 0)).1 hu2
      rw [S_trans] at this
      exact this
    · rw [Commutes_iff _ _ _ (by simp : 0 + γ = γ + 0)]
      have := (Commutes_iff _ _ _ (by simp : γ = γ + 0)).1 hu1
      rw [S_trans] at this
      exact this
    · rintro y ⟨hy1, hy2⟩
      apply huu
      rw [Equiv.apply_symm_apply] at hy1
      constructor
      · rw [Commutes_iff _ _ _ (by simp : γ = γ + 0)]
        have := (Commutes_iff _ _ _ (by simp : 0 + γ = γ + 0)).1 hy2
        rw [S_trans, this]
      · rw [Commutes_iff _ _ _ (by simp : 0 + γ = γ + 0)]
        have := (Commutes_iff _ _ _ (by simp : γ = γ + 0)).1 hy1
        rw [S_trans, this]

/-- Proposition 3.2.11: the weighted pullback of an interleaving is an interleaving. -/
theorem WeightedPullback.interleaving {a b c : C} {ε δ : ℝ≥0} {h : hom a c ε} {k : b ⟶ c}
    (P : WeightedPullback h k) (i : hom c a δ) (hi : IsInterleavingPair h i) :
    ∃! g : hom b P.p δ, IsInterleavingPair P.f g ∧
      Commutes g (homZero P.j) (comp i (homZero k)) := by
  obtain ⟨hi1, hi2⟩ := hi
  have hcomm := (SqCommutes_iff _ _ _ _ (by ring : ε + 0 = 0 + ε)).1 P.comm
  have hcomm' := eq_S_symm (by ring : ε + 0 = 0 + ε) hcomm
  -- the data for the universal property at `b`
  have hsq : SqCommutes (S zero_le (idHom b) : hom b b (ε + δ)) (homZero k)
      (S (le_of_eq (zero_add δ)) (comp i (homZero k))) h := by
    rw [SqCommutes_iff _ _ _ _ (by ring : ε + δ + 0 = δ + ε)]
    rw [comp_S_r, comp_id', comp_S_r, LPCat.assoc' (homZero k) i h, hi2, comp_S_l, id_comp']
    simp only [S_trans]
  obtain ⟨g, ⟨hg1, hg2⟩, hgu⟩ := P.univ b δ (S (le_of_eq (zero_add δ)) (comp i (homZero k)))
    (S zero_le (idHom b)) hsq
  have hg1' := (Commutes_iff _ _ _ (by simp : δ = δ + 0)).1 hg1
  have hg2' := (Commutes_iff _ _ _ (by ring : ε + δ = δ + ε)).1 hg2
  have hconj2 : comp P.f g = S zero_le (idHom b) := by
    rw [← hg2', S_trans]
  have hconj1 : comp g P.f = S zero_le (idHom P.p) := by
    have hsq2 : SqCommutes (S (le_self_add : ε ≤ ε + (ε + δ)) P.f : hom P.p b (ε + (ε + δ)))
        (homZero k) (S zero_le (homZero P.j) : hom P.p a (ε + δ)) h := by
      rw [SqCommutes_iff _ _ _ _ (by ring : ε + (ε + δ) + 0 = ε + δ + ε)]
      rw [comp_S_r, comp_S_r, ← hcomm]
      simp only [S_trans]
    obtain ⟨u, ⟨hu1, hu2⟩, huu⟩ := P.univ P.p (ε + δ) _ _ hsq2
    have e1 : comp g P.f = u := by
      apply huu
      constructor
      · rw [Commutes_iff _ _ _ (by ring : ε + δ = ε + δ + 0),
          LPCat.assoc' P.f g (homZero P.j), ← hg1', comp_S_l, comp_S_l,
          ← LPCat.assoc P.f (homZero k) i, hcomm', comp_S_r, LPCat.assoc' (homZero P.j) h i, hi1,
          comp_S_l, id_comp']
        simp only [S_trans]
      · rw [Commutes_iff _ _ _ (by ring : ε + (ε + δ) = ε + δ + ε),
          LPCat.assoc' P.f g P.f, hconj2, comp_S_l, id_comp']
        simp only [S_trans]
    have e2 : S zero_le (idHom P.p) = u := by
      apply huu
      constructor
      · rw [Commutes_iff _ _ _ (by ring : ε + δ = ε + δ + 0), comp_S_r, comp_id']
        simp only [S_trans]
      · rw [Commutes_iff _ _ _ (by ring : ε + (ε + δ) = ε + δ + ε), comp_S_r, comp_id']
        simp only [S_trans]
    rw [e1, e2]
  refine ⟨g, ⟨⟨hconj1, hconj2⟩, ?_⟩, ?_⟩
  · rw [Commutes_iff _ _ _ (by ring : 0 + δ = δ + 0), ← hg1', S_trans]
  · rintro g' ⟨hp, hc⟩
    apply hgu
    constructor
    · rw [Commutes_iff _ _ _ (by simp : δ = δ + 0)]
      have := (Commutes_iff _ _ _ (by ring : 0 + δ = δ + 0)).1 hc
      rw [S_trans, this]
    · rw [Commutes_iff _ _ _ (by ring : ε + δ = δ + ε), hp.2, S_trans]

-- Proposition 3.2.12 (`exists_weightedPullback`) is proved in `Chapter3PowerLimits.lean`.

/-! ### 3.2.5 Weighted sequential limits -/

/-- The data of a sequential diagram `⋯ → x₂ →ε₁ x₁ →ε₀ x₀` of approximate morphisms, with
`∑ εᵢ = ε`. -/
structure SeqDiagram (C : Type u) [Category.{v} C] [LPCat C] where
  ε : ℝ≥0
  εs : ℕ → ℝ≥0
  hsum : HasSum εs ε
  x : ℕ → C
  f : ∀ i, hom (x (i + 1)) (x i) (εs i)

/-- The tail `ε̃ᵢ = ε - ∑_{j<i} εⱼ = ∑_{j ≥ i} εⱼ`. -/
noncomputable def tailSum (εs : ℕ → ℝ≥0) (i : ℕ) : ℝ≥0 := ∑' j, εs (i + j)

theorem tailSum_succ {εs : ℕ → ℝ≥0} (hs : Summable εs) (i : ℕ) :
    tailSum εs i = εs i + tailSum εs (i + 1) := by
  have h : Summable (fun j => εs (i + 1 + j)) := by
    simpa [add_comm] using (NNReal.summable_nat_add_iff (i + 1)).2 hs
  have h' : Summable (fun j => εs (i + (j + 1))) := by
    simpa [Nat.add_assoc, Nat.add_comm 1] using h
  unfold tailSum
  rw [tsum_eq_zero_add' (f := fun j => εs (i + j)) h']
  simp only [Nat.add_zero]
  congr 1
  exact tsum_congr fun j => by congr 1; omega

/-- Definition 3.2.13: a weighted sequential limit. -/
structure WeightedSeqLimit (D : SeqDiagram C) where
  l : C
  g : ∀ i, hom l (D.x i) (tailSum D.εs i)
  comm : ∀ i, Commutes (g (i + 1)) (D.f i) (g i)
  univ : ∀ (l' : C) (γ : ℝ≥0) (g' : ∀ i, hom l' (D.x i) (tailSum D.εs i + γ)),
    (∀ i, Commutes (g' (i + 1)) (D.f i) (g' i)) →
      ∃! u : hom l' l γ, ∀ i, Commutes u (g i) (g' i)

/-- `C` admits weighted sequential limits. -/
def HasWeightedSeqLimits (C : Type u) [Category.{v} C] [LPCat C] : Prop :=
  ∀ D : SeqDiagram C, Nonempty (WeightedSeqLimit D)

-- Proposition 3.2.14 (`WeightedSeqLimit.interleaving`) is proved in `Chapter3SeqLimit.lean`.

-- Proposition 3.2.15 (`hasWeightedSeqLimits_of_powered`) is proved in `Chapter3PowerLimits.lean`.

/-! ### 3.2.6 Midpoints -/

/-- Definition 3.2.16: a terminal `(γ, δ)`-midpoint of the `ε`-interleaving `(f, g)`,
`γ + δ = ε`. -/
structure TerminalMidpoint {x y : C} {ε : ℝ≥0} (f : hom x y ε) (g : hom y x ε) (γ δ : ℝ≥0)
    (hγδ : γ + δ = ε) where
  z : C
  a : hom z x γ
  b : hom z y δ
  commf : Commutes a f b
  commg : Commutes b g a
  univ : ∀ (z' : C) (α : ℝ≥0) (a' : hom z' x (γ + α)) (b' : hom z' y (δ + α)),
    Commutes a' f b' → Commutes b' g a' →
      ∃! u : hom z' z α, Commutes u a a' ∧ Commutes u b b'

/-- `C` admits terminal midpoints of all interleavings. -/
def HasTerminalMidpoints (C : Type u) [Category.{v} C] [LPCat C] : Prop :=
  ∀ {x y : C} {ε : ℝ≥0} (f : hom x y ε) (g : hom y x ε), IsInterleavingPair f g →
    ∀ (γ δ : ℝ≥0) (h : γ + δ = ε), Nonempty (TerminalMidpoint f g γ δ h)

theorem S_max_le_right {x y : C} {a b : ℝ≥0} (hle : a ≤ b) (X : hom x y a) (Y : hom x y b) :
    S (le_max_left a b) X = S (le_max_right a b) Y ↔ S hle X = Y := by
  constructor
  · intro H
    have heq : max a b = b := max_eq_right hle
    have H2 := congr_arg (S (le_of_eq heq)) H
    rw [S_trans, S_trans] at H2
    rwa [S_refl] at H2
  · intro H
    rw [← H, S_trans]

theorem Commutes_of_le {x y z : C} {ε δ γ : ℝ≥0} (f : hom x y ε) (g : hom y z δ) (h : hom x z γ)
    (hle : γ ≤ ε + δ) :
    Commutes f g h ↔ S hle h = comp g f :=
  S_max_le_right hle h (comp g f)

/-- Proposition 3.2.17: the interleaving factors through a terminal midpoint. -/
theorem TerminalMidpoint.factor {x y : C} {ε : ℝ≥0} {f : hom x y ε} {g : hom y x ε}
    {γ δ : ℝ≥0} {h : γ + δ = ε} (M : TerminalMidpoint f g γ δ h) (hfg : IsInterleavingPair f g) :
    ∃! cd : hom x M.z γ × hom y M.z δ,
      IsInterleavingPair cd.1 M.a ∧ IsInterleavingPair M.b cd.2 ∧
        Commutes cd.1 M.b f ∧ Commutes cd.2 M.a g := by
  -- Construct c : hom x M.z γ
  let a' : hom x x (γ + γ) := S zero_le (idHom x)
  have hδε : ε ≤ δ + γ := by rw [← h, add_comm]
  let b' : hom x y (δ + γ) := S hδε f
  have hcomm_a'f : Commutes a' f b' := by
    rw [Commutes_of_le _ _ _ (by subst h; linarith : δ + γ ≤ (γ + γ) + ε)]
    dsimp [a', b']
    rw [comp_S_r, comp_id', S_trans, S_trans]
  have hcomm_b'g : Commutes b' g a' := by
    rw [Commutes_of_le _ _ _ (by subst h; linarith : γ + γ ≤ (δ + γ) + ε)]
    dsimp [a', b']
    rw [comp_S_r, hfg.1, S_trans, S_trans]
  obtain ⟨c, ⟨hc_a, hc_b⟩, hcu⟩ := M.univ x γ a' b' hcomm_a'f hcomm_b'g
  have hc_a' : comp M.a c = S zero_le (idHom x) := by
    have := (Commutes_iff c M.a a' (by ring : γ + γ = γ + γ)).1 hc_a
    rw [S_refl] at this
    exact this.symm
  have hc_b' : Commutes c M.b f := by
    rw [Commutes_iff c M.b f h.symm]
    have h1 := (Commutes_iff c M.b b' (add_comm δ γ)).1 hc_b
    rw [← h1, S_trans]

  -- Construct d : hom y M.z δ
  have hγε : ε ≤ γ + δ := by rw [← h]
  let a'y : hom y x (γ + δ) := S hγε g
  let b'y : hom y y (δ + δ) := S zero_le (idHom y)
  have hcomm_a'y_f : Commutes a'y f b'y := by
    rw [Commutes_of_le _ _ _ (by subst h; linarith : δ + δ ≤ (γ + δ) + ε)]
    dsimp [a'y, b'y]
    rw [comp_S_r, hfg.2, S_trans, S_trans]
  have hcomm_b'y_g : Commutes b'y g a'y := by
    rw [Commutes_of_le _ _ _ (by subst h; linarith : γ + δ ≤ (δ + δ) + ε)]
    dsimp [a'y, b'y]
    rw [comp_S_r, comp_id', S_trans, S_trans]
  obtain ⟨d, ⟨hd_a, hd_b⟩, hdu⟩ := M.univ y δ a'y b'y hcomm_a'y_f hcomm_b'y_g
  have hd_b' : comp M.b d = S zero_le (idHom y) := by
    have := (Commutes_iff d M.b b'y (by ring : δ + δ = δ + δ)).1 hd_b
    rw [S_refl] at this
    exact this.symm
  have hd_a' : Commutes d M.a g := by
    rw [Commutes_iff d M.a g (by rw [add_comm, h] : ε = δ + γ)]
    have h1 := (Commutes_iff d M.a a'y (add_comm γ δ)).1 hd_a
    rw [← h1, S_trans]

  -- Show comp c M.a = S zero_le (idHom M.z)
  have hca_comm : comp c M.a = S zero_le (idHom M.z) := by
    let a'' : hom M.z x (γ + (γ + γ)) := S (by linarith) M.a
    let b'' : hom M.z y (δ + (γ + γ)) := S (by linarith) M.b
    have hcomm_a''f : Commutes a'' f b'' := by
      rw [Commutes_of_le _ _ _ (by subst h; linarith : δ + (γ + γ) ≤ (γ + (γ + γ)) + ε)]
      have hmf := (Commutes_of_le M.a f M.b (by subst h; linarith : δ ≤ γ + ε)).1 M.commf
      dsimp [a'', b'']
      rw [comp_S_r, ← hmf, S_trans, S_trans]
    have hcomm_b''g : Commutes b'' g a'' := by
      rw [Commutes_of_le _ _ _ (by subst h; linarith : γ + (γ + γ) ≤ (δ + (γ + γ)) + ε)]
      have hmg := (Commutes_of_le M.b g M.a (by subst h; linarith : γ ≤ δ + ε)).1 M.commg
      dsimp [a'', b'']
      rw [comp_S_r, ← hmg, S_trans, S_trans]
    obtain ⟨u, ⟨hu_a, hu_b⟩, huu⟩ := M.univ M.z (γ + γ) a'' b'' hcomm_a''f hcomm_b''g
    have e1 : comp c M.a = u := by
      apply huu
      constructor
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [a'']
        rw [assoc' M.a c M.a, hc_a', comp_S_l, id_comp']
        simp only [S_trans]
      · rw [Commutes_of_le _ _ _ (by subst h; linarith)]
        dsimp [b'']
        rw [assoc' M.a c M.b]
        have hcb_eq := (Commutes_iff c M.b f h.symm).1 hc_b'
        rw [← hcb_eq, comp_S_l]
        have hmf := (Commutes_of_le M.a f M.b (by subst h; linarith : δ ≤ γ + ε)).1 M.commf
        rw [← hmf]
        simp only [S_trans]
    have e2 : S zero_le (idHom M.z) = u := by
      apply huu
      constructor
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [a'']
        rw [comp_S_r, comp_id', S_trans, S_trans]
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [b'']
        rw [comp_S_r, comp_id', S_trans, S_trans]
    rw [e1, e2]

  -- Show comp d M.b = S zero_le (idHom M.z)
  have hdb_comm : comp d M.b = S zero_le (idHom M.z) := by
    let a'' : hom M.z x (γ + (δ + δ)) := S (by linarith) M.a
    let b'' : hom M.z y (δ + (δ + δ)) := S (by linarith) M.b
    have hcomm_a''f : Commutes a'' f b'' := by
      rw [Commutes_of_le _ _ _ (by subst h; linarith : δ + (δ + δ) ≤ (γ + (δ + δ)) + ε)]
      have hmf := (Commutes_of_le M.a f M.b (by subst h; linarith : δ ≤ γ + ε)).1 M.commf
      dsimp [a'', b'']
      rw [comp_S_r, ← hmf, S_trans, S_trans]
    have hcomm_b''g : Commutes b'' g a'' := by
      rw [Commutes_of_le _ _ _ (by subst h; linarith : γ + (δ + δ) ≤ (δ + (δ + δ)) + ε)]
      have hmg := (Commutes_of_le M.b g M.a (by subst h; linarith : γ ≤ δ + ε)).1 M.commg
      dsimp [a'', b'']
      rw [comp_S_r, ← hmg, S_trans, S_trans]
    obtain ⟨u, ⟨hu_a, hu_b⟩, huu⟩ := M.univ M.z (δ + δ) a'' b'' hcomm_a''f hcomm_b''g
    have e1 : comp d M.b = u := by
      apply huu
      constructor
      · rw [Commutes_of_le _ _ _ (by subst h; linarith)]
        dsimp [a'']
        rw [assoc' M.b d M.a]
        have hda_eq := (Commutes_iff d M.a g (by rw [add_comm, h] : ε = δ + γ)).1 hd_a'
        rw [← hda_eq, comp_S_l]
        have hmg := (Commutes_of_le M.b g M.a (by subst h; linarith : γ ≤ δ + ε)).1 M.commg
        rw [← hmg]
        simp only [S_trans]
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [b'']
        rw [assoc' M.b d M.b, hd_b', comp_S_l, id_comp']
        simp only [S_trans]
    have e2 : S zero_le (idHom M.z) = u := by
      apply huu
      constructor
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [a'']
        rw [comp_S_r, comp_id', S_trans, S_trans]
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [b'']
        rw [comp_S_r, comp_id', S_trans, S_trans]
    rw [e1, e2]

  refine ⟨(c, d), ⟨⟨hc_a', hca_comm⟩, ⟨hdb_comm, hd_b'⟩, hc_b', hd_a'⟩, ?_⟩
  rintro ⟨c', d'⟩ ⟨hpair_c, hpair_d, hcomm_c, hcomm_d⟩
  dsimp at hpair_c hpair_d hcomm_c hcomm_d
  have hc'_eq : c' = c := by
    apply hcu
    constructor
    · rw [Commutes_iff _ _ _ (by ring)]
      rw [S_refl, hpair_c.1]
    · rw [Commutes_iff _ _ _ (add_comm δ γ)]
      have h1 := (Commutes_iff c' M.b f h.symm).1 hcomm_c
      dsimp [b']
      rw [S_trans, ← h1]
  have hd'_eq : d' = d := by
    apply hdu
    constructor
    · rw [Commutes_iff _ _ _ (add_comm γ δ)]
      have h1 := (Commutes_iff d' M.a g (by rw [add_comm, h] : ε = δ + γ)).1 hcomm_d
      dsimp [a'y]
      rw [S_trans, ← h1]
    · rw [Commutes_iff _ _ _ (by ring)]
      rw [S_refl, hpair_d.2]
  ext
  · exact hc'_eq
  · exact hd'_eq

/-- Proposition 3.2.18 (existence and uniqueness of the comparison interleaving between
midpoints; the compatibility of the composite with `f, g` is not recorded). -/
theorem TerminalMidpoint.compare {x y : C} {ε : ℝ≥0} {f : hom x y ε} {g : hom y x ε}
    {γ δ γ' δ' : ℝ≥0} {h : γ + δ = ε} {h' : γ' + δ' = ε} (hγ : γ ≤ γ') (hδ : δ' ≤ δ)
    (M : TerminalMidpoint f g γ δ h) (M' : TerminalMidpoint f g γ' δ' h') :
    ∃! jk : hom M.z M'.z (γ' - γ) × hom M'.z M.z (γ' - γ),
      IsInterleavingPair jk.1 jk.2 ∧ Commutes jk.2 M.a M'.a ∧ Commutes jk.1 M'.b M.b := by
  have hal_eq : (γ' - γ) + δ' = δ := by
    apply NNReal.eq
    have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
    have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
    simp only [NNReal.coe_add, NNReal.coe_sub hγ]
    linarith
  have hga_eq : γ + (γ' - γ) = γ' := by
    ext
    simp only [NNReal.coe_add, NNReal.coe_sub hγ]
    linarith
  have hd_eq : δ' + (γ' - γ) = δ := by rw [add_comm, hal_eq]

  -- Construct k : hom M'.z M.z (γ' - γ) using M.univ
  let a'k : hom M'.z x (γ + (γ' - γ)) := S (le_of_eq hga_eq.symm) M'.a
  have hδ_le : δ' ≤ δ + (γ' - γ) := by
    rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_add, NNReal.coe_sub hγ]
    have : (δ' : ℝ) ≤ δ := hδ
    linarith
  let b'k : hom M'.z y (δ + (γ' - γ)) := S hδ_le M'.b
  have hcomm_a'k_f : Commutes a'k f b'k := by
    rw [Commutes_of_le _ _ _ (by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_add, NNReal.coe_sub hγ]
      have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
      have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
      linarith)]
    have hmf := (Commutes_of_le M'.a f M'.b (by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_add]
      have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
      linarith)).1 M'.commf
    dsimp [a'k, b'k]
    rw [comp_S_r, ← hmf, S_trans, S_trans]
  have hcomm_b'k_g : Commutes b'k g a'k := by
    rw [Commutes_of_le _ _ _ (by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_add, NNReal.coe_sub hγ]
      have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
      have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
      linarith)]
    have hmg := (Commutes_of_le M'.b g M'.a (by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_add]
      have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
      linarith)).1 M'.commg
    dsimp [a'k, b'k]
    rw [comp_S_r, ← hmg, S_trans, S_trans]
  obtain ⟨k, ⟨hk_a, hk_b⟩, hku⟩ := M.univ M'.z (γ' - γ) a'k b'k hcomm_a'k_f hcomm_b'k_g
  have hk_a' : Commutes k M.a M'.a := by
    rw [Commutes_iff k M.a M'.a (by rw [add_comm, hga_eq])]
    have h1 := (Commutes_iff k M.a a'k (by ring : γ + (γ' - γ) = (γ' - γ) + γ)).1 hk_a
    dsimp [a'k] at h1
    rw [← h1, S_trans]

  -- Construct j : hom M.z M'.z (γ' - γ) using M'.univ
  let b''j : hom M.z y (δ' + (γ' - γ)) := S (le_of_eq hd_eq.symm) M.b
  have hγ_le : γ ≤ γ' + (γ' - γ) := by
    rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_add, NNReal.coe_sub hγ]
    linarith
  let a''j : hom M.z x (γ' + (γ' - γ)) := S hγ_le M.a
  have hcomm_a''j_f : Commutes a''j f b''j := by
    rw [Commutes_of_le _ _ _ (by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_add, NNReal.coe_sub hγ]
      have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
      have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
      linarith)]
    have hmf := (Commutes_of_le M.a f M.b (by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_add]
      have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
      linarith)).1 M.commf
    dsimp [a''j, b''j]
    rw [comp_S_r, ← hmf, S_trans, S_trans]
  have hcomm_b''j_g : Commutes b''j g a''j := by
    rw [Commutes_of_le _ _ _ (by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_add, NNReal.coe_sub hγ]
      have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
      have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
      linarith)]
    have hmg := (Commutes_of_le M.b g M.a (by
      rw [← NNReal.coe_le_coe]
      simp only [NNReal.coe_add]
      have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
      linarith)).1 M.commg
    dsimp [a''j, b''j]
    rw [comp_S_r, ← hmg, S_trans, S_trans]
  obtain ⟨j, ⟨hj_a, hj_b⟩, hju⟩ := M'.univ M.z (γ' - γ) a''j b''j hcomm_a''j_f hcomm_b''j_g
  have hj_b' : Commutes j M'.b M.b := by
    rw [Commutes_iff j M'.b M.b hal_eq.symm]
    have h1 := (Commutes_iff j M'.b b''j (by ring : δ' + (γ' - γ) = (γ' - γ) + δ')).1 hj_b
    dsimp [b''j] at h1
    rw [← h1, S_trans]

  -- Show comp k j = S zero_le (idHom M.z)
  have hkj_comm : comp k j = S zero_le (idHom M.z) := by
    let a'' : hom M.z x (γ + ((γ' - γ) + (γ' - γ))) := S (by linarith) M.a
    let b'' : hom M.z y (δ + ((γ' - γ) + (γ' - γ))) := S (by linarith) M.b
    have hcomm_a''f : Commutes a'' f b'' := by
      rw [Commutes_of_le _ _ _ (by
        rw [← NNReal.coe_le_coe]
        simp only [NNReal.coe_add, NNReal.coe_sub hγ]
        have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
        linarith)]
      have hmf := (Commutes_of_le M.a f M.b (by
        rw [← NNReal.coe_le_coe]
        simp only [NNReal.coe_add]
        have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
        linarith)).1 M.commf
      dsimp [a'', b'']
      rw [comp_S_r, ← hmf, S_trans, S_trans]
    have hcomm_b''g : Commutes b'' g a'' := by
      rw [Commutes_of_le _ _ _ (by
        rw [← NNReal.coe_le_coe]
        simp only [NNReal.coe_add, NNReal.coe_sub hγ]
        have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
        linarith)]
      have hmg := (Commutes_of_le M.b g M.a (by
        rw [← NNReal.coe_le_coe]
        simp only [NNReal.coe_add]
        have : (γ : ℝ) + δ = ε := congr_arg Subtype.val h
        linarith)).1 M.commg
      dsimp [a'', b'']
      rw [comp_S_r, ← hmg, S_trans, S_trans]
    obtain ⟨u, ⟨hu_a, hu_b⟩, huu⟩ := M.univ M.z ((γ' - γ) + (γ' - γ)) a'' b'' hcomm_a''f hcomm_b''g
    have e1 : comp k j = u := by
      apply huu
      constructor
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [a'']
        rw [assoc' j k M.a]
        have hka_eq := (Commutes_iff k M.a M'.a (by rw [add_comm, hga_eq])).1 hk_a'
        rw [← hka_eq, comp_S_l]
        have hja_eq := (Commutes_iff j M'.a a''j (by ring : γ' + (γ' - γ) = (γ' - γ) + γ')).1 hj_a
        dsimp [a''j] at hja_eq
        rw [← hja_eq]
        simp only [S_trans]
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [b'']
        rw [assoc' j k M.b]
        have hkb_eq := (Commutes_iff k M.b b'k (add_comm δ (γ' - γ))).1 hk_b
        dsimp [b'k] at hkb_eq
        rw [← hkb_eq, comp_S_l, comp_S_l]
        have hjb_eq := (Commutes_iff j M'.b M.b hal_eq.symm).1 hj_b'
        rw [← hjb_eq]
        simp only [S_trans]
    have e2 : S zero_le (idHom M.z) = u := by
      apply huu
      constructor
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [a'']
        rw [comp_S_r, comp_id', S_trans, S_trans]
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [b'']
        rw [comp_S_r, comp_id', S_trans, S_trans]
    rw [e1, e2]

  -- Show comp j k = S zero_le (idHom M'.z)
  have hjk_comm : comp j k = S zero_le (idHom M'.z) := by
    let a'' : hom M'.z x (γ' + ((γ' - γ) + (γ' - γ))) := S (by linarith) M'.a
    let b'' : hom M'.z y (δ' + ((γ' - γ) + (γ' - γ))) := S (by linarith) M'.b
    have hcomm_a''f : Commutes a'' f b'' := by
      rw [Commutes_of_le _ _ _ (by
        rw [← NNReal.coe_le_coe]
        simp only [NNReal.coe_add, NNReal.coe_sub hγ]
        have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
        linarith)]
      have hmf := (Commutes_of_le M'.a f M'.b (by
        rw [← NNReal.coe_le_coe]
        simp only [NNReal.coe_add]
        have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
        linarith)).1 M'.commf
      dsimp [a'', b'']
      rw [comp_S_r, ← hmf, S_trans, S_trans]
    have hcomm_b''g : Commutes b'' g a'' := by
      rw [Commutes_of_le _ _ _ (by
        rw [← NNReal.coe_le_coe]
        simp only [NNReal.coe_add, NNReal.coe_sub hγ]
        have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
        linarith)]
      have hmg := (Commutes_of_le M'.b g M'.a (by
        rw [← NNReal.coe_le_coe]
        simp only [NNReal.coe_add]
        have : (γ' : ℝ) + δ' = ε := congr_arg Subtype.val h'
        linarith)).1 M'.commg
      dsimp [a'', b'']
      rw [comp_S_r, ← hmg, S_trans, S_trans]
    obtain ⟨u, ⟨hu_a, hu_b⟩, huu⟩ := M'.univ M'.z ((γ' - γ) + (γ' - γ)) a'' b'' hcomm_a''f hcomm_b''g
    have e1 : comp j k = u := by
      apply huu
      constructor
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [a'']
        rw [assoc' k j M'.a]
        have hja_eq := (Commutes_iff j M'.a a''j (add_comm γ' (γ' - γ))).1 hj_a
        dsimp [a''j] at hja_eq
        rw [← hja_eq, comp_S_l, comp_S_l]
        have hka_eq := (Commutes_iff k M.a M'.a (by rw [add_comm, hga_eq])).1 hk_a'
        rw [← hka_eq]
        simp only [S_trans]
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [b'']
        rw [assoc' k j M'.b]
        have hjb_eq := (Commutes_iff j M'.b M.b hal_eq.symm).1 hj_b'
        rw [← hjb_eq, comp_S_l]
        have hkb_eq := (Commutes_iff k M.b b'k (add_comm δ (γ' - γ))).1 hk_b
        dsimp [b'k] at hkb_eq
        rw [← hkb_eq]
        simp only [S_trans]
    have e2 : S zero_le (idHom M'.z) = u := by
      apply huu
      constructor
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [a'']
        rw [comp_S_r, comp_id', S_trans, S_trans]
      · rw [Commutes_of_le _ _ _ (by linarith)]
        dsimp [b'']
        rw [comp_S_r, comp_id', S_trans, S_trans]
    rw [e1, e2]

  refine ⟨(j, k), ⟨⟨hkj_comm, hjk_comm⟩, hk_a', hj_b'⟩, ?_⟩
  rintro ⟨j', k'⟩ ⟨hpair_jk, hk'_a, hj'_b⟩
  dsimp at hpair_jk hk'_a hj'_b
  have hk'_eq : k' = k := by
    apply hku
    constructor
    · rw [Commutes_iff _ _ _ (by ring)]
      have h1 := (Commutes_iff k' M.a M'.a (by rw [add_comm, hga_eq])).1 hk'_a
      dsimp [a'k]
      rw [S_trans, ← h1]
    · rw [Commutes_iff k' M.b b'k (add_comm δ (γ' - γ))]
      have hjb := (Commutes_iff j' M'.b M.b hal_eq.symm).1 hj'_b
      have h_comp : M.b = S (le_of_eq hal_eq) (comp M'.b j') := by
        rw [← hjb, S_trans, S_refl]
      rw [h_comp, comp_S_l]
      have h_assoc := (LPCat.assoc k' j' M'.b).symm
      rw [h_assoc, hpair_jk.2, comp_S_r, comp_id']
      dsimp [b'k]
      simp only [S_trans]
  have hj'_eq : j' = j := by
    apply hju
    constructor
    · rw [Commutes_iff j' M'.a a''j (add_comm γ' (γ' - γ))]
      have hka := (Commutes_iff k' M.a M'.a (by rw [add_comm, hga_eq])).1 hk'_a
      have h_comp : M'.a = S (le_of_eq (by rw [add_comm, hga_eq])) (comp M.a k') := by
        rw [← hka, S_trans, S_refl]
      rw [h_comp, comp_S_l]
      have h_assoc := (LPCat.assoc j' k' M.a).symm
      rw [h_assoc, hpair_jk.1, comp_S_r, comp_id']
      dsimp [a''j]
      simp only [S_trans]
    · rw [Commutes_iff _ _ _ (by ring)]
      have h1 := (Commutes_iff j' M'.b M.b hal_eq.symm).1 hj'_b
      dsimp [b''j]
      rw [S_trans, ← h1]
  ext
  · exact hj'_eq
  · exact hk'_eq

-- Proposition 3.2.19 (`hasTerminalMidpoints_of_powered`) is proved in `Chapter3PowerLimits.lean`.

end Constructions

/-! ## Chapter 3.3: Relative locally persistent categories

A relative category is a category with a class `W` of acyclic morphisms closed under
composition and containing the identities (Mathlib: `MorphismProperty C` with
`W.IsMultiplicative`). A relative locally persistent category is an `LPCat C` together with
such a class `W` of 0-morphisms. Statements only. -/

section Relative

open CategoryTheory
open scoped NNReal ENNReal

open LPCat

variable {C : Type u} [Category.{v} C]

/-- Definitions 3.3.3–3.3.4: `x` and `y` are weakly equivalent if they are connected by a
zig-zag of acyclic morphisms. -/
def WeaklyEquivalent (W : MorphismProperty C) (x y : C) : Prop :=
  Relation.EqvGen (fun a b => ∃ f : a ⟶ b, W f) x y

/-- Weak equivalence is an equivalence relation. -/
theorem weaklyEquivalent_equivalence (W : MorphismProperty C) :
    Equivalence (WeaklyEquivalent W) :=
  Relation.EqvGen.is_equivalence _

variable [LPCat C]

/-- Definitions 3.3.1 and 3.3.6: the quotient interleaving distance `(d_I)/R` of an
equivalence relation `R` on the objects (via the quotient ep metric of Chapter 2). -/
noncomputable def quotientInterleavingDistOf (R : C → C → Prop) : C → C → ℝ≥0∞ :=
  quotientDist interleavingDist R

/-- Definition 3.3.6: the quotient interleaving distance of a relative locally persistent
category `(C, W)`. -/
noncomputable def quotientInterleavingDist (W : MorphismProperty C) : C → C → ℝ≥0∞ :=
  quotientInterleavingDistOf (WeaklyEquivalent W)

/-- The quotient interleaving distance is an ep metric. -/
theorem quotientInterleavingDist_isEPMetric (W : MorphismProperty C) [W.IsMultiplicative] :
    IsEPMetric (quotientInterleavingDist W) :=
  quotientDist_isEPMetric _ _

end Relative

end ScoccolaPhd
