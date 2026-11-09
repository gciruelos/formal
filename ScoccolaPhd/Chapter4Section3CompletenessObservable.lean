import Mathlib
import ScoccolaPhd.Chapter4Section1QuotientDistances

/-!
# §4.3 (completeness), §§4.6–4.7 and Theorems B–D

Contents:
* Toward Theorem 4.3.3: sequential limits in `C₀` from weighted ones
* Whisker
* Theorem 4.3.3: completeness of the quotient interleaving distance
* Chapter 4.6–4.7: Higher interpolation; the observable category
* Chapter 4.7: The observable category of a locally persistent category
* Chapter 4: Theorems B, C and D under the hypotheses of the introduction
-/

universe u v w

namespace ScoccolaPhd

/-! ## Toward Theorem 4.3.3: sequential limits in `C₀` from weighted ones

If `C` admits weighted sequential limits, then its underlying category has sequential limits
(take all `εᵢ = 0`). -/

section ClosedLimits

open CategoryTheory CategoryTheory.Limits
open scoped NNReal

open LPCat

variable {C : Type u} [Category.{v} C] [LPCat C]

/-- A diagram `F : ℕᵒᵖ ⥤ C` as a sequential diagram of `0`-morphisms. -/
@[reducible] noncomputable def seqOfFunctor (F : ℕᵒᵖ ⥤ C) : SeqDiagram C where
  ε := 0
  εs := fun _ => 0
  hsum := hasSum_zero
  x := fun n => F.obj (Opposite.op n)
  f := fun n => homZero (F.map (homOfLE (Nat.le_succ n)).op)

theorem tailSum_zero (n : ℕ) : tailSum (fun _ : ℕ => (0 : ℝ≥0)) n = 0 := by
  simp [tailSum]

section
variable {F : ℕᵒᵖ ⥤ C} (L : WeightedSeqLimit (seqOfFunctor F))

/-- The projections of the weighted limit as `0`-morphisms of `C`. -/
noncomputable def projC (n : ℕ) : L.l ⟶ F.obj (Opposite.op n) :=
  homZero.symm (reindex (tailSum_zero n) (L.g n))

theorem homZero_projC (n : ℕ) : homZero (projC L n) = reindex (tailSum_zero n) (L.g n) :=
  Equiv.apply_symm_apply _ _

theorem projC_comm (n : ℕ) :
    projC L (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = projC L n := by
  apply homZero.injective
  have e : tailSum (seqOfFunctor F).εs n = tailSum (seqOfFunctor F).εs (n + 1) +
      (seqOfFunctor F).εs n := by
    show tailSum (fun _ : ℕ => (0 : ℝ≥0)) n = tailSum (fun _ : ℕ => (0 : ℝ≥0)) (n + 1) + 0
    rw [tailSum_zero, tailSum_zero]; simp
  have h1 := (Commutes_iff _ _ _ e).1 (L.comm n)
  rw [homZero_comp, homZero_projC, homZero_projC]
  unfold reindex
  erw [comp_S_r, ← h1]
  erw [S_trans, S_trans]

end

end ClosedLimits

/-! ## Whisker -/

end ScoccolaPhd

open CategoryTheory CategoryTheory.Limits
open scoped NNReal


namespace ScoccolaPhd
open LPCat
variable {C : Type u} [Category.{v} C] [LPCat C]

/-- Postcompose an `ε`-morphism with a 0-morphism, keeping the index `ε`. -/
def postZ {x y z : C} {ε : ℝ≥0} (φ : y ⟶ z) (f : hom x y ε) : hom x z ε :=
  S (le_of_eq (add_zero ε)) (comp (homZero φ) f)

/-- Precompose an `ε`-morphism with a 0-morphism, keeping the index `ε`. -/
def preZ {x y z : C} {ε : ℝ≥0} (f : hom y z ε) (φ : x ⟶ y) : hom x z ε :=
  S (le_of_eq (zero_add ε)) (comp f (homZero φ))

theorem S_congr {x y : C} {a b : ℝ≥0} (h h' : a ≤ b) (f : hom x y a) : S h f = S h' f := rfl

theorem postZ_comp {x y z w : C} {ε δ : ℝ≥0} (φ : z ⟶ w) (g : hom y z δ) (f : hom x y ε) :
    postZ φ (comp g f) = comp (postZ φ g) f := by
  simp only [postZ, comp_S_l, ← LPCat.assoc, S_trans]

theorem comp_preZ {x y y' z : C} {ε δ : ℝ≥0} (g : hom y z δ) (φ : y' ⟶ y) (f : hom x y' ε) :
    comp (preZ g φ) f = comp g (postZ φ f) := by
  simp only [preZ, postZ, comp_S_l, comp_S_r, assoc', S_trans]

theorem comp_preZ' {x x' y z : C} {ε δ : ℝ≥0} (g : hom y z δ) (f : hom x y ε) (φ : x' ⟶ x) :
    comp g (preZ f φ) = preZ (comp g f) φ := by
  simp only [preZ, comp_S_r, assoc', S_trans]

theorem postZ_preZ {x x' y z : C} {ε : ℝ≥0} (φ : y ⟶ z) (f : hom x y ε) (ψ : x' ⟶ x) :
    postZ φ (preZ f ψ) = preZ (postZ φ f) ψ := by
  simp only [preZ, postZ, comp_S_l, comp_S_r, assoc', S_trans]

theorem preZ_preZ {x x' x'' y : C} {ε : ℝ≥0} (f : hom x y ε) (ψ₁ : x' ⟶ x) (ψ₂ : x'' ⟶ x') :
    preZ (preZ f ψ₁) ψ₂ = preZ f (ψ₂ ≫ ψ₁) := by
  simp only [preZ, homZero_comp, comp_S_l, comp_S_r, assoc', S_trans]

theorem postZ_postZ {x y z w : C} {ε : ℝ≥0} (φ₁ : y ⟶ z) (φ₂ : z ⟶ w) (f : hom x y ε) :
    postZ φ₂ (postZ φ₁ f) = postZ (φ₁ ≫ φ₂) f := by
  simp only [postZ, homZero_comp, comp_S_l, comp_S_r, assoc', S_trans]

theorem postZ_S {x y z : C} {ε δ : ℝ≥0} (h : ε ≤ δ) (φ : y ⟶ z) (f : hom x y ε) :
    postZ φ (S h f) = S h (postZ φ f) := by
  simp only [postZ, comp_S_r, S_trans]

theorem preZ_S {x y z : C} {ε δ : ℝ≥0} (h : ε ≤ δ) (f : hom y z ε) (φ : x ⟶ y) :
    preZ (S h f) φ = S h (preZ f φ) := by
  simp only [preZ, comp_S_l, S_trans]

theorem postZ_homZero {x y z : C} (φ : y ⟶ z) (ψ : x ⟶ y) :
    postZ φ (homZero ψ) = homZero (ψ ≫ φ) := by
  simp only [postZ, homZero_comp]

theorem preZ_homZero {x y z : C} (ψ : y ⟶ z) (φ : x ⟶ y) :
    preZ (homZero ψ) φ = homZero (φ ≫ ψ) := by
  simp only [preZ, homZero_comp]

theorem commutes_homZero_iff {x y z : C} {γ : ℝ≥0} (u : hom x y γ) (φ : y ⟶ z)
    (g : hom x z γ) : Commutes u (homZero φ) g ↔ postZ φ u = g := by
  rw [Commutes_iff _ _ _ (add_zero γ).symm]
  constructor
  · intro H; rw [postZ, ← H, S_trans, S_refl]
  · intro H; rw [← H, postZ, S_trans, S_refl]

theorem sqCommutes_homZero_iff {a b c p : C} {ε : ℝ≥0} (f : hom p b ε) (k : b ⟶ c)
    (j : p ⟶ a) (h : hom a c ε) : SqCommutes f (homZero k) (homZero j) h ↔ postZ k f = preZ h j := by
  rw [SqCommutes_iff _ _ _ _ (by simp : ε + 0 = 0 + ε)]
  constructor
  · intro H; rw [postZ, preZ, ← H, S_trans]
  · intro H
    have := congrArg (S (le_of_eq (zero_add ε).symm)) H
    simp only [postZ, preZ, S_trans, S_refl] at this
    exact this

theorem commutes_pullback_iff {a b c p : C} {δ : ℝ≥0} (g : hom b p δ) (j : p ⟶ a)
    (i : hom c a δ) (k : b ⟶ c) :
    Commutes g (homZero j) (comp i (homZero k)) ↔ postZ j g = preZ i k := by
  rw [Commutes_iff _ _ _ (by simp : 0 + δ = δ + 0)]
  constructor
  · intro H
    have := congrArg (S (le_of_eq (add_zero δ))) H
    simp only [postZ, preZ, S_trans] at this ⊢
    exact this.symm
  · intro H
    have := congrArg (S (le_of_eq (add_zero δ).symm)) H
    simp only [postZ, preZ, S_trans, S_refl] at this
    exact this.symm

end ScoccolaPhd

namespace ScoccolaPhd
open LPCat
variable {C : Type u} [Category.{v} C] [LPCat C]

theorem S_eq_S_iff_of_eq {x y : C} {a b : ℝ≥0} (e : a = b) (h h' : a ≤ b) (X Y : hom x y a) :
    S h X = S h' Y ↔ X = Y :=
  ⟨S_inj_of_eq e h, fun H => H ▸ rfl⟩

/-! ### Zero-weight sequential limits -/

section ZeroLimit
variable {F : ℕᵒᵖ ⥤ C} (L : WeightedSeqLimit (seqOfFunctor F))

/-- Universal property of the weighted limit of a diagram of 0-morphisms, at any index `γ`. -/
theorem zl_univ (l' : C) (γ : ℝ≥0) (g' : ∀ n, hom l' (F.obj (Opposite.op n)) γ)
    (hg : ∀ n, postZ (F.map (homOfLE (Nat.le_succ n)).op) (g' (n + 1)) = g' n) :
    ∃! w : hom l' L.l γ, ∀ n, postZ (projC L n) w = g' n := by
  have ht : ∀ n, tailSum (seqOfFunctor F).εs n = 0 := tailSum_zero
  have e : ∀ n, γ = tailSum (seqOfFunctor F).εs n + γ := fun n => by rw [ht]; simp
  let g'' : ∀ n, hom l' ((seqOfFunctor F).x n) (tailSum (seqOfFunctor F).εs n + γ) :=
    fun n => S (le_of_eq (e n)) (g' n)
  have hc : ∀ n, Commutes (g'' (n + 1)) ((seqOfFunctor F).f n) (g'' n) := by
    intro n
    rw [Commutes_iff _ _ _ (by rw [ht, ht]; simp)]
    show S _ (S _ (g' n)) = comp (homZero (F.map (homOfLE (Nat.le_succ n)).op))
      (S _ (g' (n + 1)))
    rw [← hg n, comp_S_r]
    simp only [postZ]
    erw [S_trans, S_trans]
  have hgL : ∀ n, L.g n = S (le_of_eq (ht n).symm) (homZero (projC L n)) := fun n => by
    rw [homZero_projC]; unfold reindex; erw [S_trans, S_refl]
  have key : ∀ (w : hom l' L.l γ) n,
      Commutes w (L.g n) (g'' n) ↔ postZ (projC L n) w = g' n := by
    intro w n
    have hc' : comp (homZero (projC L n)) w =
        S (le_of_eq (add_zero γ).symm) (postZ (projC L n) w) := by
      rw [postZ, S_trans, S_refl]
    rw [Commutes_iff _ _ _ (add_comm _ _), hgL, comp_S_l, hc']
    simp only [g'', S_trans]
    exact (S_eq_S_iff_of_eq (by rw [ht]; simp) _ _ _ _).trans eq_comm
  obtain ⟨w, hw, hwu⟩ := L.univ l' γ g'' hc
  exact ⟨w, fun n => (key w n).1 (hw n), fun w' hw' => hwu w' fun n => (key w' n).2 (hw' n)⟩

theorem zl_ext {l' : C} {γ : ℝ≥0} (w₁ w₂ : hom l' L.l γ)
    (h : ∀ n, postZ (projC L n) w₁ = postZ (projC L n) w₂) : w₁ = w₂ := by
  obtain ⟨w, _, hu⟩ := zl_univ L l' γ (fun n => postZ (projC L n) w₂) (fun n => by
    rw [postZ_postZ, projC_comm])
  exact (hu w₁ h).trans (hu w₂ fun _ => rfl).symm

/-- The weighted limit of a diagram of 0-morphisms as a cone in the underlying category. -/
noncomputable def zlCone : Cone F where
  pt := L.l
  π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj L.l) (G := F)
    (fun n => projC L n) (fun n => by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      exact (projC_comm L n).symm)

/-- ... and this cone is a limit cone. -/
noncomputable def zlIsLimit : CategoryTheory.Limits.IsLimit (zlCone L) where
  lift s := homZero.symm (Classical.choose (zl_univ L s.pt 0
    (fun n => homZero (s.π.app (Opposite.op n))) (fun n => by
      rw [postZ_homZero]; exact congrArg homZero (s.w (homOfLE (Nat.le_succ n)).op))))
  fac s j := by
    obtain ⟨n⟩ := j
    apply homZero.injective
    have := (Classical.choose_spec (zl_univ L s.pt 0
      (fun n => homZero (s.π.app (Opposite.op n))) (fun n => by
        rw [postZ_homZero]; exact congrArg homZero (s.w (homOfLE (Nat.le_succ n)).op)))).1 n
    rw [← this, ← postZ_homZero, Equiv.apply_symm_apply]
    rfl
  uniq s m hm := by
    apply homZero.injective
    rw [Equiv.apply_symm_apply]
    apply (Classical.choose_spec (zl_univ L s.pt 0
      (fun n => homZero (s.π.app (Opposite.op n))) (fun n => by
        rw [postZ_homZero]; exact congrArg homZero (s.w (homOfLE (Nat.le_succ n)).op)))).2
    intro n
    erw [postZ_homZero, ← hm (Opposite.op n)]
    rfl

end ZeroLimit

omit [LPCat C] in
theorem ofOpSequence_map_mem (W : MorphismProperty C) [W.IsMultiplicative] {X : ℕ → C}
    (θ : ∀ n, X (n + 1) ⟶ X n) (hθ : ∀ n, W (θ n)) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    W ((Functor.ofOpSequence θ).map f) := by
  obtain ⟨j⟩ := j
  obtain ⟨i⟩ := i
  have hle : j ≤ i := leOfHom f.unop
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hf : f = (homOfLE hle).op := Subsingleton.elim _ _
  subst hf
  induction d with
  | zero =>
    have : (homOfLE hle).op = 𝟙 (Opposite.op j) := Subsingleton.elim _ _
    convert MorphismProperty.id_mem W ((Functor.ofOpSequence θ).obj (Opposite.op j)) using 1
    rw [this]; exact (Functor.ofOpSequence θ).map_id _
  | succ d ih =>
    have : (homOfLE hle).op = (homOfLE (Nat.le_succ (j + d))).op ≫
        (homOfLE (Nat.le_add_right j d)).op := Subsingleton.elim _ _
    have hA : W ((Functor.ofOpSequence θ).map (homOfLE (Nat.le_succ (j + d))).op) := by
      exact (Functor.ofOpSequence_map_homOfLE_succ θ (j + d)) ▸ hθ (j + d)
    convert MorphismProperty.comp_mem W _ _ hA (ih _) using 1
    rw [this]; exact (Functor.ofOpSequence θ).map_comp _ _

end ScoccolaPhd

namespace ScoccolaPhd

/-! ## Theorem 4.3.3: completeness of the quotient interleaving distance

The proof follows the thesis. A Cauchy sequence `y` is first replaced by a fast one,
`Q(y (k+1), y k) < 2⁻ᵏ`. Theorem 4.1.4 then gives, for each `k`, acyclic
`a k → y k ← ⋯`, `b k → y (k+1)` and an `εₖ`-interleaving `a k ↔ b k`.

The thesis builds diagrams `F_n` and acyclic transformations `F_{n+1} ⇒ F_n`. We
organize the same objects as a grid `U m k` (`k` = position, `m` = number of times
position `k` has been pulled back), stored row by row:

* row `0` (`U 0 k`) and row `1` come from the given spans and interleavings
  (`baseSeq`, `baseAt`): `U 0 k` maps acyclicly to `y k`, `U 1 k → U 0 k` is acyclic, and
  `U 1 k ↔ U 0 (k+1)` is an `εₖ`-interleaving;
* row `m+2` is obtained from rows `m`, `m+1` by pulling back the interleaving
  `U (m+1) k ↔ U m (k+1)` along the acyclic `U (m+1) (k+1) → U m (k+1)` (Proposition
  3.2.11, `RowState.step`), giving an interleaving `U (m+2) k ↔ U (m+1) (k+1)` compatible
  with the vertical maps.

Every row is infinite, so there are no boundary cases. Column `k` is a sequence of acyclic
0-morphisms; its limit `L k` is acyclic over `U 0 k`, hence weakly equivalent to `y k`
(here we use that `W` is closed under sequential limits). The compatible interleavings
induce `εₖ`-interleavings `L k ↔ L (k+1)` (universal property of the weighted limit at
index `εₖ`), and Proposition 3.2.14 finishes as in Theorem 4.3.1. -/

section QuotientComplete

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal Topology

open LPCat

/-! ### A completeness criterion -/

theorem isCompleteDist_of_fast {P : Type w} {d : P → P → ℝ≥0∞} (hE : IsEPMetric d)
    (H : ∀ x : ℕ → P, (∀ k, d (x (k + 1)) (x k) < (((2⁻¹ : ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞)) →
      ∃ l, ∀ k, d (x k) l ≤ (tailSum (fun k => (2⁻¹ : ℝ≥0) ^ k) k : ℝ≥0∞)) :
    IsCompleteDist d := by
  intro x hx
  let ε : ℕ → ℝ≥0 := fun k => 2⁻¹ ^ k
  have hεpos : ∀ k, (0 : ℝ≥0∞) < (ε k : ℝ≥0∞) := fun k => by
    simp [ε]
  choose M hM using fun k => hx _ (hεpos k)
  let N : ℕ → ℕ := fun k => k + (Finset.range (k + 1)).sup M
  have hN : ∀ k, M k ≤ N k := fun k =>
    le_add_left (Finset.le_sup (f := M) (Finset.mem_range.2 (Nat.lt_succ_self k)))
  have hN' : ∀ k, M k ≤ N (k + 1) := fun k =>
    le_add_left (Finset.le_sup (f := M) (Finset.mem_range.2 (by omega)))
  obtain ⟨l, hdist⟩ := H (fun k => x (N k)) (fun k => hM k _ _ (hN' k) (hN k))
  have htail : Filter.Tendsto (fun i => tailSum ε i) Filter.atTop (𝓝 0) := by
    have := NNReal.tendsto_sum_nat_add ε
    simpa [tailSum, add_comm] using this
  refine ⟨l, ?_⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro r hr
  have hr2 : (0 : ℝ≥0∞) < r / 2 := ENNReal.half_pos hr.ne'
  obtain ⟨N0, hN0⟩ := hx _ hr2
  have hev : ∀ᶠ i in Filter.atTop, (tailSum ε i : ℝ≥0∞) < r / 2 := by
    have := (ENNReal.tendsto_coe.2 htail)
    exact this.eventually (gt_mem_nhds (by simpa using hr2))
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 hev
  refine Filter.eventually_atTop.2 ⟨N0, fun i hi => ?_⟩
  set kk := max k0 N0
  have hNk : N0 ≤ N kk := le_trans (le_max_right _ _) (Nat.le_add_right _ _)
  calc d (x i) l
      ≤ d (x i) (x (N kk)) + d (x (N kk)) l := hE.triangle _ _ _
    _ ≤ r / 2 + r / 2 := add_le_add (hN0 _ _ hi hNk).le
        ((hdist kk).trans (hk0 kk (le_max_left _ _)).le)
    _ = r := ENNReal.add_halves r

variable {C : Type u} [Category.{v} C] [LPCat C]

theorem IsQuotientInterleaved.mono {W : MorphismProperty C} {x y : C} {δ δ' : ℝ≥0}
    (hle : δ ≤ δ') (h : IsQuotientInterleaved W x y δ) : IsQuotientInterleaved W x y δ' := by
  obtain ⟨x', y', hx, hy, h⟩ := h
  exact ⟨x', y', hx, hy, IsInterleaved.mono hle h⟩

theorem isQuotientInterleaved_of_lt {W : MorphismProperty C} {x y : C} {ε : ℝ≥0}
    (h : qiDist W x y < ε) : IsQuotientInterleaved W x y ε := by
  unfold qiDist at h
  rw [iInf_lt_iff] at h
  obtain ⟨δ, hδ⟩ := h
  rw [iInf_lt_iff] at hδ
  obtain ⟨hi, hlt⟩ := hδ
  exact IsQuotientInterleaved.mono (by exact_mod_cast hlt.le) hi

/-! ### The grid -/

section Grid

variable (W : MorphismProperty C) [W.IsMultiplicative] (ε : ℕ → ℝ≥0)

/-- The data extracted from a fast Cauchy sequence (Theorem 4.1.4): acyclic `u k : a k → y k`,
`v k : b k → y (k+1)` and `εₖ`-interleavings `a k ↔ b k`. -/
structure CoverData where
  y : ℕ → C
  a : ℕ → C
  b : ℕ → C
  u : ∀ k, a k ⟶ y k
  v : ∀ k, b k ⟶ y (k + 1)
  hu : ∀ k, W (u k)
  hv : ∀ k, W (v k)
  I : ∀ k, Interleaving (a k) (b k) (ε k) (ε k)

/-- Two consecutive rows `A = U m ·` and `B = U (m+1) ·` of the grid, with the acyclic vertical
maps `B k → A k` and the interleavings `B k ↔ A (k+1)`. -/
structure RowState where
  A : ℕ → C
  B : ℕ → C
  θ : ∀ k, B k ⟶ A k
  hθ : ∀ k, W (θ k)
  K : ∀ k, Interleaving (B k) (A (k + 1)) (ε k) (ε k)

variable {W ε}

/-- The next row, with its compatibility with the previous two. -/
structure RowStep (R : RowState W ε) where
  B' : ℕ → C
  θ' : ∀ k, B' k ⟶ R.B k
  hθ' : ∀ k, W (θ' k)
  K' : ∀ k, Interleaving (B' k) (R.B (k + 1)) (ε k) (ε k)
  sqf : ∀ k, postZ (R.θ (k + 1)) (K' k).f = preZ (R.K k).f (θ' k)
  sqg : ∀ k, postZ (θ' k) (K' k).g = preZ (R.K k).g (R.θ (k + 1))

omit [W.IsMultiplicative] in
theorem rowStep_nonempty (hW : IsStableUnderWeightedPullbacks W) (R : RowState W ε) :
    Nonempty (RowStep R) := by
  have : ∀ k, ∃ (p : C) (j : p ⟶ R.B k) (f : hom p (R.B (k + 1)) (ε k))
      (g : hom (R.B (k + 1)) p (ε k)), W j ∧ IsInterleavingPair f g ∧
      postZ (R.θ (k + 1)) f = preZ (R.K k).f j ∧
      postZ j g = preZ (R.K k).g (R.θ (k + 1)) := by
    intro k
    obtain ⟨⟨P⟩, hP⟩ := hW (R.K k).f (R.θ (k + 1)) (R.hθ (k + 1))
    obtain ⟨g, ⟨hg, hgc⟩, _⟩ := P.interleaving (R.K k).g (R.K k).isPair
    exact ⟨P.p, P.j, P.f, g, hP P, hg, (sqCommutes_homZero_iff _ _ _ _).1 P.comm,
      (commutes_pullback_iff _ _ _ _).1 hgc⟩
  choose p j f g hj hp hsf hsg using this
  exact ⟨⟨p, j, hj, fun k => ⟨f k, g k, hp k⟩, hsf, hsg⟩⟩

/-- A chosen next row (Proposition 3.2.11 applied at every position). -/
noncomputable def RowState.step (hW : IsStableUnderWeightedPullbacks W) (R : RowState W ε) :
    RowStep R :=
  (rowStep_nonempty hW R).some

/-- Shift the pair of rows by one. -/
@[reducible] noncomputable def RowState.next (hW : IsStableUnderWeightedPullbacks W) (R : RowState W ε) :
    RowState W ε :=
  ⟨R.B, (R.step hW).B', (R.step hW).θ', (R.step hW).hθ', (R.step hW).K'⟩

/-- The first step: from `x` acyclic over `y k`, a span `x ← c → a k` and the pullback of the
interleaving `a k ↔ b k` to `c ↔ nx`, with `nx` acyclic over `y (k+1)`. -/
structure BaseStep (D : CoverData W ε) (k : ℕ) (x : C) (t : x ⟶ D.y k) where
  c : C
  θ : c ⟶ x
  hθ : W θ
  nx : C
  t' : nx ⟶ D.y (k + 1)
  ht' : W t'
  K : Interleaving c nx (ε k) (ε k)

theorem baseStep_nonempty (hW : IsStableUnderWeightedPullbacks W) (D : CoverData W ε) (k : ℕ)
    (x : C) (t : x ⟶ D.y k) (ht : W t) : Nonempty (BaseStep D k x t) := by
  obtain ⟨⟨P⟩, hP⟩ := hW (homZero t) (D.u k) (D.hu k)
  have he : W (homZero.symm P.f) := (hW (homZero (D.u k)) t ht).2 P.swap0
  obtain ⟨⟨Q⟩, hQ⟩ := hW (D.I k).g (homZero.symm P.f) he
  obtain ⟨g, ⟨hg, _⟩, _⟩ := Q.interleaving (D.I k).f ⟨(D.I k).isPair.2, (D.I k).isPair.1⟩
  exact ⟨⟨P.p, P.j, hP P, Q.p, Q.j ≫ D.v k, MorphismProperty.comp_mem _ _ _ (hQ Q) (D.hv k),
    ⟨g, Q.f, hg.2, hg.1⟩⟩⟩

/-- Row `0` of the grid: `U 0 k`, with an acyclic map to `y k`. -/
noncomputable def baseSeq (hW : IsStableUnderWeightedPullbacks W) (D : CoverData W ε) :
    ∀ k, Σ x : C, {t : x ⟶ D.y k // W t}
  | 0 => ⟨D.y 0, 𝟙 _, MorphismProperty.id_mem _ _⟩
  | k + 1 =>
    let B := (baseStep_nonempty hW D k _ (baseSeq hW D k).2.1 (baseSeq hW D k).2.2).some
    ⟨B.nx, B.t', B.ht'⟩

/-- The first step at position `k`. -/
noncomputable def baseAt (hW : IsStableUnderWeightedPullbacks W) (D : CoverData W ε) (k : ℕ) :
    BaseStep D k (baseSeq hW D k).1 (baseSeq hW D k).2.1 :=
  (baseStep_nonempty hW D k _ (baseSeq hW D k).2.1 (baseSeq hW D k).2.2).some

/-- Rows `0` and `1`. -/
noncomputable def row0 (hW : IsStableUnderWeightedPullbacks W) (D : CoverData W ε) :
    RowState W ε where
  A k := (baseSeq hW D k).1
  B k := (baseAt hW D k).c
  θ k := (baseAt hW D k).θ
  hθ k := (baseAt hW D k).hθ
  K k := (baseAt hW D k).K

/-- Rows `m` and `m + 1`. -/
@[reducible] noncomputable def rows (hW : IsStableUnderWeightedPullbacks W) (D : CoverData W ε) :
    ℕ → RowState W ε
  | 0 => row0 hW D
  | m + 1 => (rows hW D m).next hW

variable (hW : IsStableUnderWeightedPullbacks W) (D : CoverData W ε)

theorem rows_sqf (m k : ℕ) :
    postZ ((rows hW D m).θ (k + 1)) ((rows hW D (m + 1)).K k).f =
      preZ ((rows hW D m).K k).f ((rows hW D (m + 1)).θ k) :=
  ((rows hW D m).step hW).sqf k

theorem rows_sqg (m k : ℕ) :
    postZ ((rows hW D (m + 1)).θ k) ((rows hW D (m + 1)).K k).g =
      preZ ((rows hW D m).K k).g ((rows hW D m).θ (k + 1)) :=
  ((rows hW D m).step hW).sqg k

/-- Column `k` of the grid, as a diagram of 0-morphisms `ℕᵒᵖ ⥤ C`. -/
noncomputable def colFun (k : ℕ) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun m => (rows hW D m).A k) (fun m => (rows hW D m).θ k)

theorem colFun_map (k m : ℕ) :
    (colFun hW D k).map (homOfLE (Nat.le_succ m)).op = (rows hW D m).θ k :=
  Functor.ofOpSequence_map_homOfLE_succ _ m

variable (h : HasWeightedSeqLimits C)

/-- The limit `L k` of column `k`. -/
noncomputable def colLim (k : ℕ) : WeightedSeqLimit (seqOfFunctor (colFun hW D k)) :=
  (h _).some

/-- The projection `L k → U m k`. -/
noncomputable def proj (k m : ℕ) : (colLim hW D h k).l ⟶ (rows hW D m).A k :=
  projC (colLim hW D h k) m

theorem colLim_comm (k m : ℕ) :
    proj hW D h k (m + 1) ≫ (rows hW D m).θ k = proj hW D h k m :=
  (congrArg (fun φ => projC (colLim hW D h k) (m + 1) ≫ φ) (colFun_map hW D k m)).symm.trans
    (projC_comm _ m)

theorem col_univ (k : ℕ) (l' : C) (γ : ℝ≥0) (g' : ∀ m, hom l' ((rows hW D m).A k) γ)
    (hg : ∀ m, postZ ((rows hW D m).θ k) (g' (m + 1)) = g' m) :
    ∃! w : hom l' (colLim hW D h k).l γ, ∀ m, postZ (proj hW D h k m) w = g' m :=
  zl_univ (colLim hW D h k) l' γ g' fun m =>
    (congrArg (fun φ => postZ φ (g' (m + 1))) (colFun_map hW D k m)).trans (hg m)

theorem col_ext (k : ℕ) {l' : C} {γ : ℝ≥0} (w₁ w₂ : hom l' (colLim hW D h k).l γ)
    (H : ∀ m, postZ (proj hW D h k m) w₁ = postZ (proj hW D h k m) w₂) : w₁ = w₂ :=
  zl_ext (colLim hW D h k) w₁ w₂ H

theorem fUp_cone (k m : ℕ) :
    postZ ((rows hW D m).θ (k + 1))
      (preZ ((rows hW D (m + 1)).K k).f (proj hW D h k (m + 1 + 1))) =
    preZ ((rows hW D m).K k).f (proj hW D h k (m + 1)) := by
  rw [postZ_preZ, rows_sqf, preZ_preZ, colLim_comm]

/-- The `εₖ`-morphism `L k → L (k+1)`. -/
noncomputable def fUp (k : ℕ) : hom (colLim hW D h k).l (colLim hW D h (k + 1)).l (ε k) :=
  Classical.choose (col_univ hW D h (k + 1) _ (ε k)
    (fun m => preZ ((rows hW D m).K k).f (proj hW D h k (m + 1))) (fUp_cone hW D h k))

theorem fUp_spec (k m : ℕ) :
    postZ (proj hW D h (k + 1) m) (fUp hW D h k) =
      preZ ((rows hW D m).K k).f (proj hW D h k (m + 1)) :=
  (Classical.choose_spec (col_univ hW D h (k + 1) _ (ε k)
    (fun m => preZ ((rows hW D m).K k).f (proj hW D h k (m + 1)))
    (fUp_cone hW D h k))).1 m

theorem gDown_cone (k m : ℕ) :
    postZ ((rows hW D m).θ k)
      (postZ ((rows hW D (m + 1)).θ k)
        (preZ ((rows hW D (m + 1)).K k).g (proj hW D h (k + 1) (m + 1)))) =
    postZ ((rows hW D m).θ k)
      (preZ ((rows hW D m).K k).g (proj hW D h (k + 1) m)) := by
  rw [postZ_preZ, rows_sqg, preZ_preZ, colLim_comm]

/-- The `εₖ`-morphism `L (k+1) → L k`. -/
noncomputable def gDown (k : ℕ) : hom (colLim hW D h (k + 1)).l (colLim hW D h k).l (ε k) :=
  Classical.choose (col_univ hW D h k _ (ε k)
    (fun m => postZ ((rows hW D m).θ k)
      (preZ ((rows hW D m).K k).g (proj hW D h (k + 1) m))) (gDown_cone hW D h k))

theorem gDown_spec (k m : ℕ) :
    postZ (proj hW D h k m) (gDown hW D h k) =
      postZ ((rows hW D m).θ k)
        (preZ ((rows hW D m).K k).g (proj hW D h (k + 1) m)) :=
  (Classical.choose_spec (col_univ hW D h k _ (ε k)
    (fun m => postZ ((rows hW D m).θ k)
      (preZ ((rows hW D m).K k).g (proj hW D h (k + 1) m)))
    (gDown_cone hW D h k))).1 m

theorem gDown_fUp (k : ℕ) :
    comp (gDown hW D h k) (fUp hW D h k) = S zero_le (idHom (colLim hW D h k).l) := by
  apply col_ext hW D h k
  intro m
  rw [postZ_comp, gDown_spec, ← postZ_comp, comp_preZ, fUp_spec, comp_preZ',
    ((rows hW D m).K k).isPair.1, preZ_S, postZ_S, postZ_S]
  unfold idHom
  rw [preZ_homZero, postZ_homZero, postZ_homZero]
  simp only [Category.comp_id, Category.id_comp, colLim_comm]

theorem fUp_gDown (k : ℕ) :
    comp (fUp hW D h k) (gDown hW D h k) = S zero_le (idHom (colLim hW D h (k + 1)).l) := by
  apply col_ext hW D h (k + 1)
  intro m
  rw [postZ_comp, fUp_spec, comp_preZ, gDown_spec, ← comp_preZ, ← rows_sqf, ← postZ_comp,
    comp_preZ', ((rows hW D (m + 1)).K k).isPair.2, preZ_S, postZ_S, postZ_S]
  unfold idHom
  rw [preZ_homZero, postZ_homZero, postZ_homZero]
  simp only [Category.comp_id, Category.id_comp, colLim_comm]

theorem colLim_pair (k : ℕ) : IsInterleavingPair (gDown hW D h k) (fUp hW D h k) :=
  ⟨fUp_gDown hW D h k, gDown_fUp hW D h k⟩

theorem colLim_weq (hlim : IsClosedUnderSequentialLimits W) (k : ℕ) :
    WeaklyEquivalent W (colLim hW D h k).l (D.y k) := by
  have h1 : W (proj hW D h k 0) :=
    hlim (colFun hW D k) (zlCone (colLim hW D h k)) (zlIsLimit _)
      (ofOpSequence_map_mem W _ (fun m => (rows hW D m).hθ k)) (Opposite.op 0)
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨_, h1⟩)
    (Relation.EqvGen.rel _ _ ⟨_, (baseSeq hW D k).2.2⟩)

end Grid

/-- Theorem C (4.3.3): if `C` admits weighted sequential limits, and `W` is closed under
sequential limits and stable under weighted pullbacks, then `(d_I)/≃` is complete. -/
theorem quotientInterleavingDist_complete (W : MorphismProperty C) [W.IsMultiplicative]
    (h : HasWeightedSeqLimits C) (hlim : IsClosedUnderSequentialLimits W)
    (hW : IsStableUnderWeightedPullbacks W) :
    IsCompleteDist (quotientInterleavingDist W) := by
  have heq : quotientInterleavingDist W = qiDist W := funext fun x => funext fun y =>
    quotientInterleavingDist_eq_inf_quotientInterleaved hW x y
  rw [heq]
  apply isCompleteDist_of_fast (qiDist_isEPMetric hW)
  intro x hx
  let ε : ℕ → ℝ≥0 := fun k => 2⁻¹ ^ k
  have hsum : HasSum ε (1 - 2⁻¹)⁻¹ := NNReal.hasSum_geometric (by norm_num)
  have hq : ∀ k, IsQuotientInterleaved W (x k) (x (k + 1)) (ε k) := fun k =>
    (isQuotientInterleaved_of_lt (hx k)).symm
  choose a b u v hu hv hI using fun k => exists_acyclicCover hW (hq k)
  let D : CoverData W ε := ⟨x, a, b, u, v, hu, hv, fun k => (hI k).some⟩
  let SD : SeqDiagram C :=
    ⟨_, ε, hsum, fun k => (colLim hW D h k).l, fun k => gDown hW D h k⟩
  obtain ⟨L⟩ := h SD
  obtain ⟨kk, ⟨hk, _⟩, _⟩ := L.interleaving ε hsum.summable (fun i => fUp hW D h i)
    (fun i => colLim_pair hW D h i)
  refine ⟨L.l, fun i => iInf₂_le_of_le (tailSum ε i) ⟨_, _, colLim_weq hW D h hlim i,
    Relation.EqvGen.refl _, ⟨⟨kk i, L.g i, (hk i).2, (hk i).1⟩⟩⟩ le_rfl⟩

end QuotientComplete

/-! ## Chapter 4.6–4.7: Higher interpolation; the observable category

The construction `cat(P)` and its interleaving distance formula are proved; the observable
category (Section 4.7) is in `Chapter4Observable.lean`.

Omitted from 4.6: Example 4.6.1 and Examples 4.6.6–4.6.8 (they need the two-point metric
spaces `2_δ` and the subspaces `{1/2ⁿ}`), the adjunction `met ⊣ cat` (Prop. 4.6.2), the full
embedding of `epMET` in `lpCAT` (Prop. 4.6.4), Lemma 4.6.9 and the extension theorem 4.6.10
(they need the enriched Kan extension on the locally persistent side), the space-time
category `st` and Remark 4.6.12. Omitted from 4.7: Props. 4.7.2 and 4.7.4. -/

section Interpolation

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

open LPCat

/-! ### 4.6 Higher interpolation -/

/-- `cat(P)` (Section 4.6.1): the locally persistent category on the points of an ep metric
space `P` with `Hom(p, q)_r = {*}` if `d p q ≤ r` and `∅` otherwise. -/
theorem exists_cat_structure (P : Type u) [PseudoEMetricSpace P] :
    ∃ (_ : Category.{u} P) (L : LPCat P),
      ∀ (p q : P) (r : ℝ≥0), L.hom p q r = ULift.{u} (PLift (edist p q ≤ r)) := by
  let H := fun p q : P => ULift.{u} (PLift (edist p q ≤ (0 : ℝ≥0∞)))
  letI : Category.{u} P :=
    { Hom := H
      id := fun p => ⟨⟨by simp⟩⟩
      comp := fun {p q r} f g => ⟨⟨by
        calc edist p r ≤ edist p q + edist q r := edist_triangle _ _ _
          _ ≤ 0 + 0 := add_le_add f.down.down g.down.down
          _ = 0 := zero_add _⟩⟩ }
  let L : LPCat P :=
    { hom := fun p q r => ULift.{u} (PLift (edist p q ≤ r))
      homZero := Equiv.refl _
      comp := fun {p q r ε δ} g f => ⟨⟨by
        calc edist p r ≤ edist p q + edist q r := edist_triangle _ _ _
          _ ≤ (ε : ℝ≥0∞) + δ := add_le_add f.down.down g.down.down
          _ = ↑(ε + δ) := (ENNReal.coe_add _ _).symm⟩⟩
      S := fun h f => ⟨⟨f.down.down.trans (ENNReal.coe_le_coe.mpr h)⟩⟩
      id_comp := fun _ => Subsingleton.elim _ _
      comp_id := fun _ => Subsingleton.elim _ _
      assoc := fun _ _ _ => Subsingleton.elim _ _
      S_refl := fun _ => Subsingleton.elim _ _
      S_trans := fun _ _ _ => Subsingleton.elim _ _
      comp_S := fun _ _ _ _ => Subsingleton.elim _ _
      homZero_comp := fun _ _ => Subsingleton.elim _ _ }
  exact ⟨inferInstance, L, fun _ _ _ => rfl⟩

/-- The locally persistent category `cat(P)`, chosen via `exists_cat_structure`. -/
noncomputable def catOf (P : Type u) [PseudoEMetricSpace P] : LPCatB.{u} :=
  @LPCatB.mk P (Classical.choose (exists_cat_structure P))
    (Classical.choose (Classical.choose_spec (exists_cat_structure P)))

/-- Lemma 4.6.3: the counit `met (cat P) → P` is an isomorphism of ep metric spaces; in
particular `d_I(p, q) = d_P(p, q)` in `cat(P)`. -/
theorem interleavingDist_catOf (P : Type u) [PseudoEMetricSpace P] (p q : P) :
    interleavingDist (C := (catOf P).carrier) p q = edist p q := by
  have hh (x y : (catOf P).carrier) (r : ℝ≥0) :
      hom x y r = ULift.{u} (PLift (edist (α := P) x y ≤ r)) :=
    (Classical.choose_spec (Classical.choose_spec (exists_cat_structure P))) x y r
  have hs (x y : (catOf P).carrier) (r : ℝ≥0) : Subsingleton (hom x y r) := by
    rw [hh]
    infer_instance
  have hi (r : ℝ≥0) : IsInterleaved (C := (catOf P).carrier) p q r ↔ edist p q ≤ r := by
    constructor
    · rintro ⟨i⟩
      have f := i.f
      erw [hh p q r] at f
      exact f.down.down
    · intro h
      have f : hom (C := (catOf P).carrier) p q r := by erw [hh p q r]; exact ⟨⟨h⟩⟩
      have g : hom (C := (catOf P).carrier) q p r := by
        erw [hh q p r]; exact ⟨⟨by simpa [edist_comm] using h⟩⟩
      letI := hs p p (r + r)
      letI := hs q q (r + r)
      exact ⟨⟨f, g, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  apply le_antisymm
  · by_cases h : edist p q = ∞
    · simp [h]
    · have he := ENNReal.coe_toNNReal h
      exact (iInf₂_le_of_le (edist p q).toNNReal ((hi _).mpr he.ge) he.le)
  · exact le_iInf₂ fun r hr => (hi r).mp hr

/-- Definition 4.6.5: a distance non-increasing map `f : P → met(C)` is coherent if it is
the object map of a locally persistent functor `cat(P) → C`. -/
def IsCoherent {P : Type u} [PseudoEMetricSpace P] {C : Type u} [Category.{u} C] [LPCat C]
    (f : P → C) : Prop :=
  (∀ p q, interleavingDist (f p) (f q) ≤ edist p q) ∧
    ∃ F : LPFunctor (catOf P).carrier C, ∀ p, F.toFunctor.obj p = f p

/-! ### 4.7 The observable category: see `Chapter4Observable.lean`. -/

end Interpolation

/-! ## Chapter 4.7: The observable category of a locally persistent category

`C^#` has the objects of `C`, hom-persistent sets `Hom(x, y)^# = lim_{r > 0} Hom(x, y)^r`
(concretely: compatible families `(f_r)_{r > 0}`, `f_r ∈ Hom(x, y)_{r + ε}`), composition given
levelwise by `(g ∘ f)_r = g_{r/2} ∘ f_{r/2}`, and its own underlying category (whose
morphisms are `Hom(x, y)^#_0`).  We construct it and the identity-on-objects locally persistent
functor `η : C → C^#`, and prove that the interleaving distance is an observable invariant
(Proposition 4.7.3). -/

section Observable

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

open LPCat

noncomputable section Observable
variable {C : Type u} [instC : Category.{v} C] (L : LPCat C)

/-- Elements of `Hom(x, y)^#_ε = lim_{r > 0} Hom(x, y)_{r + ε}`, concretely as compatible
families. -/
@[ext]
structure Sharp (x y : C) (ε : ℝ≥0) where
  f : ∀ r : ℝ≥0, 0 < r → hom x y (r + ε)
  compat : ∀ (r r' : ℝ≥0) (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r'),
    S (add_le_add h le_rfl) (f r hr) = f r' hr'

namespace Sharp
variable {L} {x y z w : C} {ε δ γ ε' : ℝ≥0}

/-- Shift in `C^#`. -/
def shift (h : ε ≤ ε') (s : Sharp (L := L) x y ε) : Sharp (L := L) x y ε' where
  f r hr := S (add_le_add le_rfl h) (s.f r hr)
  compat r r' hr hr' hrr := by
    rw [S_trans, ← s.compat r r' hr hr' hrr, S_trans]

/-- Composition in `C^#`: `(g ∘ f)_r = g_{r/2} ∘ f_{r/2}`. -/
def comp (g : Sharp (L := L) y z δ) (f : Sharp (L := L) x y ε) : Sharp (L := L) x z (ε + δ) where
  f r hr := S (le_of_eq (by ring)) (LPCat.comp (g.f (r / 2) (half_pos hr)) (f.f (r / 2) (half_pos hr)))
  compat r r' hr hr' h := by
    have h2 : r / 2 ≤ r' / 2 := by gcongr
    rw [S_trans, ← g.compat _ _ (half_pos hr) (half_pos hr') h2,
      ← f.compat _ _ (half_pos hr) (half_pos hr') h2, comp_S, S_trans]

/-- The identity of `C^#`. -/
def id (x : C) : Sharp (L := L) x x 0 where
  f r hr := S (by simp) (idHom x)
  compat r r' hr hr' h := by rw [S_trans]


theorem shift_refl (s : Sharp (L := L) x y ε) : Sharp.shift le_rfl s = s := by
  ext r hr; exact S_refl _

theorem shift_trans (h₁ : ε ≤ δ) (h₂ : δ ≤ γ) (s : Sharp (L := L) x y ε) :
    Sharp.shift h₂ (Sharp.shift h₁ s) = Sharp.shift (h₁.trans h₂) s := by
  ext r hr; exact S_trans _ _ _

theorem comp_shift (hε : ε ≤ ε') (hδ : δ ≤ γ) (f : Sharp (L := L) x y ε)
    (g : Sharp (L := L) y z δ) :
    Sharp.comp (Sharp.shift hδ g) (Sharp.shift hε f) =
      Sharp.shift (add_le_add hε hδ) (Sharp.comp g f) := by
  ext r hr
  show S _ (LPCat.comp (S _ (g.f (r / 2) _)) (S _ (f.f (r / 2) _))) =
    S _ (S _ (LPCat.comp (g.f (r / 2) _) (f.f (r / 2) _)))
  rw [comp_S, S_trans, S_trans]

theorem id_comp (f : Sharp (L := L) x y ε) :
    Sharp.shift (le_of_eq (add_zero ε)) (Sharp.comp (Sharp.id y) f) = f := by
  ext r hr
  have hc := f.compat (r / 2) r (half_pos hr) hr (by linarith [half_pos hr] : r / 2 ≤ r)
  show S _ (S _ (LPCat.comp (S _ (idHom y)) (f.f (r / 2) _))) = f.f r hr
  rw [comp_S_l, S_trans, S_trans, ← hc]
  have h1 := congrArg (S (by simp : r / 2 + ε ≤ r + ε)) (LPCat.id_comp (f.f (r / 2) (half_pos hr)))
  rw [← h1, S_trans]
  rfl

theorem comp_id (f : Sharp (L := L) x y ε) :
    Sharp.shift (le_of_eq (zero_add ε)) (Sharp.comp f (Sharp.id x)) = f := by
  ext r hr
  have hc := f.compat (r / 2) r (half_pos hr) hr (by linarith [half_pos hr] : r / 2 ≤ r)
  show S _ (S _ (LPCat.comp (f.f (r / 2) _) (S _ (idHom x)))) = f.f r hr
  rw [comp_S_r, S_trans, S_trans, ← hc]
  have h1 := congrArg (S (by simp : r / 2 + ε ≤ r + ε)) (LPCat.comp_id (f.f (r / 2) (half_pos hr)))
  rw [← h1, S_trans]
  rfl

theorem assoc (f : Sharp (L := L) x y ε) (g : Sharp (L := L) y z δ) (h : Sharp (L := L) z w γ) :
    Sharp.shift (le_of_eq (add_assoc ε δ γ)) (Sharp.comp h (Sharp.comp g f)) =
      Sharp.comp (Sharp.comp h g) f := by
  ext r hr
  have hr2 := half_pos hr
  have hr4 := half_pos hr2
  have h24 : r / 2 / 2 ≤ r / 2 := by linarith
  have hh := h.compat _ _ hr4 hr2 h24
  have hf := f.compat _ _ hr4 hr2 h24
  show S _ (S _ (LPCat.comp (h.f (r / 2) _) (S _ (LPCat.comp (g.f (r / 2 / 2) _) (f.f (r / 2 / 2) _))))) =
    S _ (LPCat.comp (S _ (LPCat.comp (h.f (r / 2 / 2) _) (g.f (r / 2 / 2) _))) (f.f (r / 2) _))
  rw [← hh, ← hf, comp_S_r, comp_S_l, S_trans, S_trans, S_trans, comp_S_r, S_trans]
  rw [comp_S_l, ← LPCat.assoc (f.f (r / 2 / 2) hr4) (g.f (r / 2 / 2) hr4) (h.f (r / 2 / 2) hr4),
    S_trans, S_trans]

theorem comp_shift_r (hε : ε ≤ ε') (f : Sharp (L := L) x y ε) (g : Sharp (L := L) y z δ) :
    Sharp.comp g (Sharp.shift hε f) = Sharp.shift (add_le_add hε le_rfl) (Sharp.comp g f) := by
  have := comp_shift hε le_rfl f g
  rwa [shift_refl] at this

theorem comp_shift_l (hδ : δ ≤ γ) (f : Sharp (L := L) x y ε) (g : Sharp (L := L) y z δ) :
    Sharp.comp (Sharp.shift hδ g) f = Sharp.shift (add_le_add le_rfl hδ) (Sharp.comp g f) := by
  have := comp_shift (le_refl ε) hδ f g
  rwa [shift_refl] at this

end Sharp

/-- The underlying category of the observable locally persistent category `C^#`: its
morphisms are `Hom(x, y)^#_0`. -/
@[instance_reducible] def observableCat : Category.{v} C where
  Hom x y := Sharp L x y 0
  id x := Sharp.id x
  comp f g := Sharp.shift (le_of_eq (add_zero 0)) (Sharp.comp g f)
  id_comp f := by
    show Sharp.shift _ (Sharp.comp f (Sharp.id _)) = f
    exact Sharp.comp_id f
  comp_id f := by
    show Sharp.shift _ (Sharp.comp (Sharp.id _) f) = f
    exact Sharp.id_comp f
  assoc f g h := by
    show Sharp.shift _ (Sharp.comp h (Sharp.shift _ (Sharp.comp g f))) =
      Sharp.shift _ (Sharp.comp (Sharp.shift _ (Sharp.comp h g)) f)
    rw [Sharp.comp_shift_r, Sharp.comp_shift_l, Sharp.shift_trans, Sharp.shift_trans]
    have := Sharp.assoc f g h
    rw [← this, Sharp.shift_trans]


/-- The observable locally persistent structure on `C^#`. -/
@[instance_reducible] def observableLP : @LPCat C (observableCat L) :=
  @LPCat.mk C (observableCat L) (fun x y ε => Sharp L x y ε) (fun {x y} => Equiv.refl _)
    (fun {x y z ε δ} g f => Sharp.comp g f) (fun {x y ε δ} h f => Sharp.shift h f)
    (fun {x y ε} f => Sharp.id_comp f) (fun {x y ε} f => Sharp.comp_id f)
    (fun {x y z w ε δ γ} f g h => Sharp.assoc f g h) (fun {x y ε} f => Sharp.shift_refl f)
    (fun {x y ε δ γ} h₁ h₂ f => Sharp.shift_trans h₁ h₂ f)
    (fun {x y z ε ε' δ δ'} hε hδ f g => Sharp.comp_shift hε hδ f g)
    (fun {x y z} f g => rfl)


/-- The unit `η : Hom(x, y)_ε → Hom(x, y)^#_ε`. -/
def Sharp.unit {x y : C} {ε : ℝ≥0} (f : hom x y ε) : Sharp L x y ε where
  f r hr := S (by simp) f
  compat r r' hr hr' h := by rw [S_trans]

/-- The equivalence `Hom(x, y)^#_ε ≃ (Hom(x, y)^#)(ε)` with the limit of Chapter 2. -/
def Sharp.equivSharp (x y : C) (ε : ℝ≥0) :
    Sharp L x y ε ≃ (sharp (@homFunctor C instC L x y)).obj ε where
  toFun s := Types.Limit.mk (sharpDiagram (@homFunctor C instC L x y) ε) (fun r => s.f r.1 r.2)
    (fun r r' f => s.compat r.1 r'.1 r.2 r'.2 (leOfHom f))
  invFun u :=
    { f := fun r hr => Limits.limit.π (sharpDiagram (@homFunctor C instC L x y) ε) ⟨r, hr⟩ u
      compat := fun r r' hr hr' h => by
        exact Limits.limit.w_apply (sharpDiagram (@homFunctor C instC L x y) ε)
          (homOfLE h : (⟨r, hr⟩ : {r : ℝ≥0 // 0 < r}) ⟶ ⟨r', hr'⟩) u }
  left_inv s := by
    ext r hr
    exact Types.Limit.π_mk (sharpDiagram (@homFunctor C instC L x y) ε) (fun r => s.f r.1 r.2)
      (fun r r' f => s.compat r.1 r'.1 r.2 r'.2 (leOfHom f)) (⟨r, hr⟩ : {r : ℝ≥0 // 0 < r})
  right_inv u := by
    apply Types.limit_ext
    intro r
    exact Types.Limit.π_mk (sharpDiagram (@homFunctor C instC L x y) ε) _ _ r


/-- The underlying functor of `η : C → C^#`. -/
def observableUnitFunctor : @Functor C _ C (observableCat L) :=
  @CategoryTheory.Functor.mk C _ C (observableCat L)
    (fun x => x) (fun {x y} f => Sharp.unit (L := L) (LPCat.homZero f))
    (fun x => by
      apply Sharp.ext; funext r hr; rfl)
    (fun {x y z} f g => by
      apply Sharp.ext; funext r hr
      show S _ (LPCat.homZero (f ≫ g)) =
        S _ (S _ (LPCat.comp (S _ (LPCat.homZero g)) (S _ (LPCat.homZero f))))
      rw [LPCat.homZero_comp, comp_S, S_trans, S_trans, S_trans])

/-- The identity-on-objects locally persistent functor `η : C → C^#`. -/
def observableUnit : @LPFunctor C _ L C (observableCat L) (observableLP L) :=
  @LPFunctor.mk C _ L C (observableCat L) (observableLP L) (observableUnitFunctor L)
    (fun {x y ε} f => Sharp.unit (L := L) f)
    (fun {x y} f => rfl)
    (fun {x y z ε δ} f g => by
      apply Sharp.ext; funext r hr
      show S _ (LPCat.comp g f) = S _ (LPCat.comp (S _ g) (S _ f))
      rw [comp_S, S_trans])
    (fun {x y ε δ} h f => by
      apply Sharp.ext; funext r hr
      show S _ (S h f) = S _ (S _ f)
      rw [S_trans, S_trans])


/-- Definition 4.7.1 (corrected): the observable locally persistent category `C^#` exists: it has
its own underlying category (with 0-morphisms `Hom(x, y)^#_0`), hom-persistent sets
`Hom(x, y)^#`, and the identity-on-objects locally persistent functor `η : C → C^#`, acting by
the unit `η : Hom → Hom^#`. -/
theorem exists_observable (L : LPCat C) :
    ∃ (cat' : Category.{v} C) (L' : @LPCat C cat')
      (e : ∀ x y ε, @LPCat.hom C cat' L' x y ε ≃ (sharp (@homFunctor C instC L x y)).obj ε)
      (F : @LPFunctor C instC L C cat' L'),
      (∀ x, @CategoryTheory.Functor.obj C instC C cat' (@LPFunctor.toFunctor C instC L C cat' L' F)
        x = x) ∧
        ∀ (x y : C) (ε : ℝ≥0) (f : @LPCat.hom C instC L x y ε),
          HEq (e (@CategoryTheory.Functor.obj C instC C cat'
              (@LPFunctor.toFunctor C instC L C cat' L' F) x)
              (@CategoryTheory.Functor.obj C instC C cat'
                (@LPFunctor.toFunctor C instC L C cat' L' F) y) ε
              (@LPFunctor.map C instC L C cat' L' F x y ε f))
            ((sharpUnit (@homFunctor C instC L x y)).app ε f) := by
  refine ⟨observableCat L, observableLP L, Sharp.equivSharp L, observableUnit L, fun x => rfl, ?_⟩
  intro x y ε f
  refine heq_of_eq ?_
  apply Types.limit_ext
  intro r
  erw [Types.Limit.π_mk]
  simp only [sharpUnit, sharp]
  erw [← ConcreteCategory.comp_apply, Limits.limit.lift_π]
  rfl


theorem Sharp.pair_component {x y : C} {δ : ℝ≥0} (f : Sharp L x y δ) (g : Sharp L y x δ)
    (hp : @IsInterleavingPair C (observableCat L) (observableLP L) x y δ δ f g)
    (r : ℝ≥0) (hr : 0 < r) :
    IsInterleavingPair (f.f (r / 2) (half_pos hr)) (g.f (r / 2) (half_pos hr)) := by
  obtain ⟨h1, h2⟩ := hp
  have hr2 := half_pos hr
  have e : (r / 2 + δ) + (r / 2 + δ) = r + (δ + δ) := by
    apply NNReal.eq; push_cast; ring
  have c1 := congrArg (fun s : Sharp L x x (δ + δ) => s.f r hr) h1
  have c2 := congrArg (fun s : Sharp L y y (δ + δ) => s.f r hr) h2
  refine ⟨?_, ?_⟩
  · refine S_inj_of_eq e (le_of_eq e) ?_
    have c1' : S (le_of_eq (show (r / 2 + δ) + (r / 2 + δ) = r + (δ + δ) from e))
        (LPCat.comp (g.f (r / 2) hr2) (f.f (r / 2) hr2)) =
        S (add_le_add le_rfl zero_le) (S (by simp) (idHom x)) := c1
    rw [c1', S_trans, S_trans]
  · refine S_inj_of_eq e (le_of_eq e) ?_
    have c2' : S (le_of_eq (show (r / 2 + δ) + (r / 2 + δ) = r + (δ + δ) from e))
        (LPCat.comp (f.f (r / 2) hr2) (g.f (r / 2) hr2)) =
        S (add_le_add le_rfl zero_le) (S (by simp) (idHom y)) := c2
    rw [c2', S_trans, S_trans]


/-- Proposition 4.7.3: the interleaving distance is an observable invariant,
`d_I^{C^#} = d_I^C`. -/
theorem interleavingDist_observable (L : LPCat C) (x y : C) :
    @interleavingDist C (observableCat L) (observableLP L) x y = @interleavingDist C instC L x y := by
  apply le_antisymm
  · exact @LPFunctor.interleavingDist_le C instC L C (observableCat L) (observableLP L)
      (observableUnit L) x y
  · unfold interleavingDist
    refine le_iInf fun δ => le_iInf fun hδ => ?_
    obtain ⟨⟨f, g, hp⟩⟩ := hδ
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε2 : 0 < 2 * ε := by positivity
    have hpair := Sharp.pair_component L (f : Sharp L x y δ) (g : Sharp L y x δ) hp (2 * ε) hε2
    have hI : IsInterleaved x y (2 * ε / 2 + δ) :=
      ⟨⟨f.f (2 * ε / 2) (half_pos hε2), g.f (2 * ε / 2) (half_pos hε2), hpair⟩⟩
    have h1 := interleavingDist_le_of_isInterleaved hI
    have e : 2 * ε / 2 + δ = ε + δ := by apply NNReal.eq; push_cast; ring
    rw [e] at h1
    have h2 : interleavingDist x y ≤ (δ : ℝ≥0∞) + ε := by simpa [add_comm] using h1
    exact h2

end Observable

end Observable

/-! ## Chapter 4: Theorems B, C and D under the hypotheses of the introduction

Theorem B (4.1.4 using Lemma 4.1.5), Theorem C (4.3.3 using Proposition 3.2.15 and
Lemma 4.1.5), and Theorem D (4.4.2 using Proposition 3.2.19), with the hypotheses on
the underlying category `C₀` and the powers as in the thesis: `C` is powered by representables,
`C₀` has pullbacks (and sequential limits, and binary products), the powers preserve them, and
the acyclic morphisms are stable under base change, powers (and closed under sequential limits). -/

section Concrete

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

open LPCat

variable {C : Type u} [Category.{v} C] [LPCat C] [PoweredByRepresentables C]

/-- Theorem B (4.1.4 using Lemma 4.1.5). -/
theorem quotientInterleavingDist_eq_inf_acyclicCover_of_powered [HasPullbacks C]
    (hpres : ∀ ε, PreservesLimitsOfShape WalkingCospan (PoweredByRepresentables.pow (C := C) ε))
    (W : MorphismProperty C) [W.IsMultiplicative] [W.IsStableUnderBaseChange]
    (hpow : ∀ ε {a b : C} (f : a ⟶ b), W f → W ((PoweredByRepresentables.pow ε).map f))
    (x y : C) :
    quotientInterleavingDist W x y =
      ⨅ (δ : ℝ≥0) (_ : ∃ (x' y' : C) (u : x' ⟶ x) (v : y' ⟶ y),
        W u ∧ W v ∧ IsInterleaved x' y' δ), (δ : ℝ≥0∞) :=
  quotientInterleavingDist_eq_inf_acyclicCover
    (isStableUnderWeightedPullbacks_of_powered hpres hpow) x y

/-- Theorem C (4.3.3 using Proposition 3.2.15 and Lemma 4.1.5). -/
theorem quotientInterleavingDist_complete_of_powered [HasPullbacks C]
    [HasLimitsOfShape ℕᵒᵖ C]
    (hpres : ∀ ε, PreservesLimitsOfShape WalkingCospan (PoweredByRepresentables.pow (C := C) ε))
    (hseq : ∀ ε, PreservesLimitsOfShape ℕᵒᵖ (PoweredByRepresentables.pow (C := C) ε))
    (W : MorphismProperty C) [W.IsMultiplicative] [W.IsStableUnderBaseChange]
    (hpow : ∀ ε {a b : C} (f : a ⟶ b), W f → W ((PoweredByRepresentables.pow ε).map f))
    (hlim : IsClosedUnderSequentialLimits W) :
    IsCompleteDist (quotientInterleavingDist W) :=
  quotientInterleavingDist_complete W (hasWeightedSeqLimits_of_powered hseq) hlim
    (isStableUnderWeightedPullbacks_of_powered hpres hpow)

/-- The interleaving distance (trivial relation) is complete for a category powered by
representables with sequential limits preserved by the powers (Theorem 4.3.1 with Prop. 3.2.15). -/
theorem interleavingDist_complete_of_powered [HasLimitsOfShape ℕᵒᵖ C]
    (hseq : ∀ ε, PreservesLimitsOfShape ℕᵒᵖ (PoweredByRepresentables.pow (C := C) ε)) :
    IsCompleteDist (interleavingDist (C := C)) :=
  interleavingDist_complete (hasWeightedSeqLimits_of_powered hseq)

/-- Theorem D (4.4.2 with Prop. 3.2.19): the interleaving distance is intrinsic for a category
powered by representables with binary products and pullbacks preserved by the powers. -/
theorem interleavingDist_intrinsic_of_powered [HasBinaryProducts C] [HasPullbacks C]
    (hprod : ∀ ε, PreservesLimitsOfShape (Discrete WalkingPair) (PoweredByRepresentables.pow (C := C) ε))
    (hpb : ∀ ε, PreservesLimitsOfShape WalkingCospan (PoweredByRepresentables.pow (C := C) ε)) :
    IsIntrinsicDist (interleavingDist (C := C)) :=
  interleavingDist_intrinsic_of_midpoints (hasTerminalMidpoints_of_powered hprod hpb)

end Concrete

end ScoccolaPhd
