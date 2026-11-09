import Mathlib
import ScoccolaPhd.Chapter3Section1LPCategories

/-!
# §3.2 (continued): powers, sequential limits, persistent objects

Contents:
* Chapter 3.2: Limits from powers
* Composites of interleavings along a sequence (toward Proposition 3.2.14)
* The locally persistent category of persistent objects (Example 3.1.3)
* Weighted sequential limits in `D^ℝ`
-/

universe u v

namespace ScoccolaPhd

/-! ## Chapter 3.2: Limits from powers

Propositions 3.2.12, 3.2.15 and 3.2.19: weighted pullbacks, weighted sequential limits and
terminal midpoints in a locally persistent category powered by representables.

The key point is `exists_unique_hom_cone`: for fixed `p'` and `γ`, the functor
`y ↦ Hom(p', y)_γ ≅ Hom_{C₀}(p', y^γ)` preserves every limit that `(-)^γ` preserves. -/

section PowerLimits

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

open LPCat

variable {C : Type u} [Category.{v} C] [LPCat C] [PoweredByRepresentables C]

namespace PoweredByRepresentables

/-- The 0-morphism `x → y^γ` corresponding to a `γ`-morphism `x → y`. -/
def up {x y : C} {γ : ℝ≥0} (u : hom x y γ) : x ⟶ (pow γ).obj y :=
  homZero.symm ((powIso x y γ 0).symm (S (le_of_eq (add_zero γ).symm) u))

/-- Postcomposition of a `γ`-morphism with a 0-morphism, `Hom(x, -)_γ` as a functor on `C₀`. -/
def pmap {x y z : C} {γ : ℝ≥0} (f : y ⟶ z) (u : hom x y γ) : hom x z γ :=
  S (le_of_eq (add_zero γ)) (comp (homZero f) u)

theorem pmap_comp {x y z w : C} {γ : ℝ≥0} (f : y ⟶ z) (g : z ⟶ w) (u : hom x y γ) :
    pmap (f ≫ g) u = pmap g (pmap f u) := by
  unfold pmap
  rw [homZero_comp (C := C), comp_S_l, comp_S_r, assoc', S_trans, S_trans, S_trans]

theorem pmap_id {x y : C} {γ : ℝ≥0} (u : hom x y γ) : pmap (𝟙 y) u = u := by
  unfold pmap
  exact LPCat.id_comp u

/-- The `γ`-morphism `x → y` corresponding to a 0-morphism `x → y^γ`. -/
def down {x y : C} {γ : ℝ≥0} (g : x ⟶ (pow γ).obj y) : hom x y γ :=
  S (le_of_eq (add_zero γ)) (powIso x y γ 0 (homZero g))

theorem down_up {x y : C} {γ : ℝ≥0} (u : hom x y γ) : down (up u) = u := by
  unfold down up
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, S_trans]
  exact S_refl u

theorem up_down {x y : C} {γ : ℝ≥0} (g : x ⟶ (pow γ).obj y) : up (down g) = g := by
  unfold down up
  rw [S_trans, S_refl, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- `up`/`down` as an equivalence. -/
def powEquiv (γ : ℝ≥0) (x y : C) : (x ⟶ (pow γ).obj y) ≃ hom x y γ where
  toFun := down
  invFun := up
  left_inv := up_down
  right_inv := down_up

/-- Naturality of `down` in the target. -/
theorem down_comp_map {x y y' : C} {γ : ℝ≥0} (g : x ⟶ (pow γ).obj y) (f : y ⟶ y') :
    down (g ≫ (pow γ).map f) =
      S (le_of_eq (add_zero γ)) (comp (homZero f) (down g)) := by
  unfold down
  rw [homZero_comp (C := C), powIso_y f (homZero g)]
  rw [comp_S_r, S_trans]

theorem down_comp_map' {x y y' : C} {γ : ℝ≥0} (g : x ⟶ (pow γ).obj y) (f : y ⟶ y') :
    down (g ≫ (pow γ).map f) = pmap f (down g) := down_comp_map g f

theorem down_injective {x y : C} {γ : ℝ≥0} : Function.Injective (down (x := x) (y := y) (γ := γ)) :=
  (powEquiv γ x y).injective

/-- The functor `y ↦ Hom(p', y)_γ` preserves the limits preserved by `(-)^γ`: compatible
families of `γ`-morphisms into a diagram factor uniquely through a limit cone. -/
theorem exists_unique_hom_cone {J : Type*} [Category J] {D : J ⥤ C} (c : Cone D)
    (hc : Limits.IsLimit c) (γ : ℝ≥0) [PreservesLimit D (pow γ)] (p' : C)
    (a : ∀ j, hom p' (D.obj j) γ)
    (ha : ∀ {j j' : J} (e : j ⟶ j'), pmap (D.map e) (a j) = a j') :
    ∃! u : hom p' c.pt γ, ∀ j, pmap (c.π.app j) u = a j := by
  have hg : ∀ {j j' : J} (e : j ⟶ j'), up (a j) ≫ (pow γ).map (D.map e) = up (a j') := by
    intro j j' e
    apply down_injective
    rw [down_comp_map', down_up, down_up, ha]
  let s : Cone (D ⋙ pow γ) :=
    { pt := p'
      π :=
        { app := fun j => up (a j)
          naturality := by
            intro j j' e
            simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
              Category.id_comp, Functor.comp_map]
            exact (hg e).symm } }
  have hc' : Limits.IsLimit ((pow γ).mapCone c) := isLimitOfPreserves (pow γ) hc
  have hfac : ∀ j, hc'.lift s ≫ (pow γ).map (c.π.app j) = up (a j) := fun j => hc'.fac s j
  refine ⟨down (hc'.lift s), fun j => ?_, fun u' hu' => ?_⟩
  · rw [← down_comp_map', hfac, down_up]
  · have : up u' = hc'.lift s := by
      refine hc'.uniq s (up u') fun j => ?_
      apply down_injective
      show down (up u' ≫ (pow γ).map (c.π.app j)) = down (up (a j))
      rw [down_comp_map', down_up, down_up, hu']
    rw [← this, down_up]

/-- Naturality of `down` in the source, for 0-morphisms. -/
theorem down_comp_pre {x x' y : C} {γ : ℝ≥0} (v : x' ⟶ x) (g : x ⟶ (pow γ).obj y) :
    down (v ≫ g) = S (le_of_eq (zero_add γ)) (comp (down g) (homZero v)) := by
  unfold down
  rw [homZero_comp (C := C), comp_S_l]
  have := powIso_x (C := C) (homZero v) (homZero g)
  rw [powIso_S, this, S_trans, S_trans, S_trans]

theorem comp_homZero_down {x y y' : C} {γ : ℝ≥0} (g : x ⟶ (pow γ).obj y) (f : y ⟶ y') :
    comp (homZero f) (down g) = S (le_of_eq (add_zero γ).symm) (down (g ≫ (pow γ).map f)) := by
  rw [down_comp_map, S_trans]
  exact (S_refl _).symm

theorem comp_down_homZero {x x' y : C} {γ : ℝ≥0} (v : x' ⟶ x) (g : x ⟶ (pow γ).obj y) :
    comp (down g) (homZero v) = S (le_of_eq (zero_add γ).symm) (down (v ≫ g)) := by
  rw [down_comp_pre, S_trans]
  exact (S_refl _).symm

/-- `Commutes u (homZero v) j'` says `v ∘ u = j'`, i.e. `pmap v u = j'`. -/
theorem commutes_homZero_iff {x y z : C} {γ : ℝ≥0} (u : hom x y γ) (v : y ⟶ z) (j' : hom x z γ) :
    Commutes u (homZero v) j' ↔ pmap v u = j' := by
  rw [Commutes_iff _ _ _ (by simp : γ = γ + 0)]
  unfold pmap
  constructor
  · intro H
    rw [← H, S_trans]; exact S_refl _
  · intro H
    rw [← H, S_trans]; exact S_refl _

/-- Naturality of `powIso` in the source for approximate morphisms, in terms of `pmap`. -/
theorem powIso_pmap_hom {x x' y : C} {ε δ : ℝ≥0} (v : hom x' x δ) (g : x ⟶ (pow ε).obj y) :
    powIso x' y ε δ (pmap g v) = S (le_of_eq (add_comm δ ε)) (comp (down g) v) := by
  unfold pmap down
  simp only [powIso_S, powIso_x, comp_S_l, S_trans]

/-- A reformulation of `powIso_pmap_hom`: the triangle with `down g` commutes iff `g ∘ v`
corresponds to `f'` under `powIso`. -/
theorem commutes_down_iff {x x' y : C} {ε δ : ℝ≥0} (v : hom x' x δ) (g : x ⟶ (pow ε).obj y)
    (f' : hom x' y (ε + δ)) :
    Commutes v (down g) f' ↔ powIso x' y ε δ (pmap g v) = f' := by
  rw [Commutes_iff _ _ _ (add_comm ε δ), powIso_pmap_hom]
  constructor
  · intro H
    rw [← H, S_trans]; exact S_refl _
  · intro H
    rw [← H, S_trans]; exact S_refl _

theorem pmap_homZero {x y z : C} (m : x ⟶ y) (v : y ⟶ z) :
    pmap v (homZero m : hom x y 0) = homZero (m ≫ v) := by
  unfold pmap
  rw [homZero_comp (C := C)]

/-- Triangles with a 0-morphism and an approximate morphism: `g ∘ m = f'` iff `up g ∘ m` is
`up f'`. -/
theorem commutes_homZero_up_iff {x x' y : C} {ε : ℝ≥0} (m : x' ⟶ x) (g : hom x y ε)
    (s : x' ⟶ (pow ε).obj y) :
    Commutes (homZero m) g (S (le_of_eq (add_zero ε).symm) (down s)) ↔ m ≫ up g = s := by
  rw [Commutes_iff _ _ _ (by simp : ε + 0 = 0 + ε)]
  conv_lhs => rw [S_trans]
  have e1 := comp_down_homZero m (up g)
  rw [down_up] at e1
  rw [e1]
  constructor
  · intro H
    have := S_inj_of_eq (by simp : ε = ε) le_rfl (f := down (m ≫ up g)) (g := down s) ?_
    · have h2 := congrArg up this
      rwa [up_down, up_down] at h2
    · rw [S_refl, S_refl]
      have h3 := congrArg (S (le_of_eq (zero_add ε))) H
      rw [S_trans, S_trans] at h3
      simpa [S_refl] using h3.symm
  · intro H
    subst H
    rfl

/-- Naturality of `powIso` in the target, in terms of `pmap`. -/
theorem powIso_pmap_map {x y y' : C} {ε r : ℝ≥0} (f : y ⟶ y') (u : hom x ((pow ε).obj y) r) :
    powIso x y' ε r (pmap ((pow ε).map f) u) = pmap f (powIso x y ε r u) := by
  unfold pmap
  exact powIso_y f u

end PoweredByRepresentables

open PoweredByRepresentables

/-- Pullbacks: a pair of `γ`-morphisms into the legs of a pullback with equal images in the
base factors uniquely through the pullback, if `(-)^γ` preserves it. -/
theorem exists_unique_hom_pullback {a b c : C} (H : a ⟶ c) (K : b ⟶ c) (t : PullbackCone H K)
    (ht : Limits.IsLimit t) (γ : ℝ≥0) [PreservesLimit (cospan H K) (pow γ)] (p' : C)
    (j' : hom p' a γ) (f'' : hom p' b γ) (hsq : pmap H j' = pmap K f'') :
    ∃! u : hom p' t.pt γ, pmap t.fst u = j' ∧ pmap t.snd u = f'' := by
  let A : ∀ j : WalkingCospan, hom p' ((cospan H K).obj j) γ := fun
    | .left => j'
    | .right => f''
    | .one => pmap H j'
  have hA : ∀ {j j' : WalkingCospan} (e : j ⟶ j'), pmap ((cospan H K).map e) (A j) = A j' := by
    intro j j' e
    rcases e with _ | _
    · change pmap ((cospan H K).map (𝟙 _)) _ = _
      rw [CategoryTheory.Functor.map_id]
      exact pmap_id _
    · rename_i w
      cases w
      · exact rfl
      · exact hsq.symm
  obtain ⟨u, hu, huniq⟩ := PoweredByRepresentables.exists_unique_hom_cone t ht γ p' A hA
  refine ⟨u, ⟨hu WalkingCospan.left, hu WalkingCospan.right⟩, fun u' hu' => huniq u' fun j => ?_⟩
  rcases j with _ | w
  · show pmap (t.π.app WalkingCospan.one) u' = pmap H j'
    rw [PullbackCone.condition_one, pmap_comp]
    exact congrArg (pmap H) hu'.1
  · cases w
    · exact hu'.1
    · exact hu'.2

/-- Proposition 3.2.12: if `C` is powered by representables, has pullbacks in the underlying
category, and powers preserve them, then weighted pullbacks along approximate morphisms
exist. -/
theorem exists_weightedPullback [HasPullbacks C]
    (hpres : ∀ ε, PreservesLimitsOfShape WalkingCospan (pow (C := C) ε))
    {a b c : C} {ε : ℝ≥0} (h : hom a c ε) (k : b ⟶ c) : Nonempty (WeightedPullback h k) := by
  have hcond : pullback.fst (up h) ((pow ε).map k) ≫ up h =
      pullback.snd (up h) ((pow ε).map k) ≫ (pow ε).map k := pullback.condition
  refine ⟨{ p := pullback (up h) ((pow ε).map k)
            j := pullback.fst (up h) ((pow ε).map k)
            f := down (pullback.snd (up h) ((pow ε).map k))
            comm := ?_
            univ := ?_ }⟩
  · rw [SqCommutes_iff _ _ _ _ (by simp : ε + 0 = 0 + ε), comp_homZero_down]
    have e1 := comp_down_homZero (pullback.fst (up h) ((pow ε).map k)) (up h)
    rw [down_up] at e1
    rw [e1, ← hcond, S_trans]
  · intro p' γ j' f' hsq
    have ht := pullbackIsPullback (up h) ((pow ε).map k)
    have := hpres γ
    let f'' := (powIso p' b ε γ).symm f'
    have hsq' : pmap (up h) j' = pmap ((pow ε).map k) f'' := by
      apply (powIso p' c ε γ).injective
      have h1 := (SqCommutes_iff _ _ _ _ (by ring : ε + γ + 0 = γ + ε)).1 hsq
      rw [powIso_pmap_hom, powIso_pmap_map, down_up, Equiv.apply_symm_apply]
      unfold pmap
      rw [← h1, S_trans]
    obtain ⟨u, ⟨hu1, hu2⟩, huniq⟩ :=
      exists_unique_hom_pullback (up h) ((pow ε).map k) _ ht γ p' j' f'' hsq'
    refine ⟨u, ⟨(commutes_homZero_iff _ _ _).2 hu1, ?_⟩, ?_⟩
    · rw [commutes_down_iff]
      have := congrArg (powIso p' b ε γ) hu2
      simpa [f''] using this
    · rintro u' ⟨c1, c2⟩
      refine huniq u' ⟨(commutes_homZero_iff _ _ _).1 c1, ?_⟩
      apply (powIso p' b ε γ).injective
      rw [Equiv.apply_symm_apply]
      exact (commutes_down_iff _ _ _).1 c2

theorem pmap_S {x y z : C} {γ γ' : ℝ≥0} (f : y ⟶ z) (hle : γ ≤ γ') (u : hom x y γ) :
    pmap f (S hle u) = S hle (pmap f u) := by
  unfold pmap
  rw [comp_S_r, S_trans, S_trans]

theorem sqCommutes_iff_pmap {p' a b c : C} {ε γ : ℝ≥0} (f' : hom p' b (ε + γ)) (k : b ⟶ c)
    (j' : hom p' a γ) (h : hom a c ε) :
    SqCommutes f' (homZero k) j' h ↔
      pmap k f' = S (le_of_eq (add_comm γ ε)) (comp h j') := by
  rw [SqCommutes_iff _ _ _ _ (by ring : ε + γ + 0 = γ + ε)]
  unfold pmap
  constructor
  · intro H; rw [← H, S_trans]
  · intro H
    have e : S (le_of_eq (by ring : ε + γ + 0 = γ + ε)) (comp (homZero k) f') =
        S (le_of_eq (add_comm ε γ)) (S (le_of_eq (add_zero (ε + γ))) (comp (homZero k) f')) :=
      (S_trans _ _ _).symm
    rw [e, H, S_trans]
    exact S_refl _

/-- The square of a 0-morphism `j` and `s : x → b^ε` commutes with the cospan `(up h, K)` iff
the corresponding approximate square commutes. -/
theorem sq_iff_up {a b c x : C} {ε : ℝ≥0} (h : hom a c ε) (k : b ⟶ c) (j : x ⟶ a)
    (s : x ⟶ (pow ε).obj b) :
    SqCommutes (S (le_of_eq (add_zero ε).symm) (down s)) (homZero k) (homZero j) h ↔
      j ≫ up h = s ≫ (pow ε).map k := by
  rw [sqCommutes_iff_pmap, pmap_S, ← down_comp_map']
  have e1 := comp_down_homZero j (up h)
  rw [down_up] at e1
  rw [e1, S_trans]
  constructor
  · intro H
    apply down_injective
    have := S_inj_of_eq (by simp : ε = ε + 0) (le_of_eq (by simp)) H
    exact this.symm
  · intro H
    rw [H]

theorem sq_iff_up' {a b c x : C} {ε : ℝ≥0} (h : hom a c ε) (k : b ⟶ c) (j : x ⟶ a)
    (s : x ⟶ (pow ε).obj b) :
    SqCommutes (down s) (homZero k) (homZero j) h ↔ j ≫ up h = s ≫ (pow ε).map k := by
  rw [SqCommutes_iff _ _ _ _ (by simp : ε + 0 = 0 + ε), comp_homZero_down]
  have e1 := comp_down_homZero j (up h)
  rw [down_up] at e1
  rw [e1, S_trans]
  constructor
  · intro H
    apply down_injective
    have := S_inj_of_eq (by simp : ε = 0 + ε) (le_of_eq (by simp)) H
    exact this.symm
  · intro H
    rw [H]

/-- Every weighted pullback is a pullback in `C₀` of `up h` and `(-)^ε k`. -/
theorem WeightedPullback.isPullback {a b c : C} {ε : ℝ≥0} {h : hom a c ε} {k : b ⟶ c}
    (P : WeightedPullback h k) : IsPullback P.j (up P.f) (up h) ((pow ε).map k) := by
  have hcomm : P.j ≫ up h = up P.f ≫ (pow ε).map k := by
    refine (sq_iff_up' h k P.j (up P.f)).1 ?_
    rw [down_up]; exact P.comm
  have key : ∀ s : PullbackCone (up h) ((pow ε).map k),
      ∃! m : s.pt ⟶ P.p, m ≫ P.j = s.fst ∧ m ≫ up P.f = s.snd := by
    intro s
    have hsq : SqCommutes (S (le_of_eq (add_zero ε).symm) (down s.snd)) (homZero k)
        (homZero s.fst) h := (sq_iff_up h k s.fst s.snd).2 s.condition
    obtain ⟨u, ⟨hu1, hu2⟩, huniq⟩ := P.univ s.pt 0 (homZero s.fst) _ hsq
    obtain ⟨m, rfl⟩ : ∃ m, u = homZero m := ⟨homZero.symm u, by simp⟩
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    · have := (commutes_homZero_iff _ _ _).1 hu1
      rw [pmap_homZero] at this
      exact homZero.injective this
    · exact (commutes_homZero_up_iff m P.f s.snd).1 hu2
    · rintro m' ⟨h1, h2⟩
      have := huniq (homZero m') ⟨(commutes_homZero_iff _ _ _).2 (by rw [pmap_homZero, h1]),
        (commutes_homZero_up_iff m' P.f s.snd).2 h2⟩
      exact homZero.injective this
  refine IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.IsLimit.mk hcomm
    (fun s => (key s).choose) (fun s => (key s).choose_spec.1.1)
    (fun s => (key s).choose_spec.1.2) fun s m h1 h2 => ?_)
  exact (key s).unique ⟨h1, h2⟩ (key s).choose_spec.1 |>.symm.symm

/-- Sequential limits: a family of `γ`-morphisms into a sequence `⋯ → X₂ → X₁ → X₀`, compatible
with consecutive maps, factors uniquely through a limit cone. -/
theorem exists_unique_hom_seq {F : ℕᵒᵖ ⥤ C}
    (c : Cone F) (hc : Limits.IsLimit c) (γ : ℝ≥0)
    [PreservesLimit F (pow γ)] (p' : C) (a : ∀ n : ℕ, hom p' (F.obj (Opposite.op n)) γ)
    (ha : ∀ n : ℕ, pmap (F.map (homOfLE (Nat.le_succ n)).op) (a (n + 1)) = a n) :
    ∃! u : hom p' c.pt γ, ∀ n : ℕ, pmap (c.π.app (Opposite.op n)) u = a n := by
  have hgen : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), pmap (F.map f) (a i.unop) = a j.unop := by
    intro i j f
    obtain ⟨j⟩ := j
    obtain ⟨i⟩ := i
    have hle : j ≤ i := leOfHom f.unop
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hf : f = (homOfLE hle).op := Subsingleton.elim _ _
    subst hf
    induction d with
    | zero =>
      have : (homOfLE hle).op = 𝟙 (Opposite.op j) := Subsingleton.elim _ _
      rw [this]
      erw [CategoryTheory.Functor.map_id]
      exact pmap_id _
    | succ d ih =>
      have : (homOfLE hle).op = (homOfLE (Nat.le_succ (j + d))).op ≫
          (homOfLE (Nat.le_add_right j d)).op := Subsingleton.elim _ _
      rw [this]
      erw [CategoryTheory.Functor.map_comp, pmap_comp]
      erw [ha (j + d)]
      exact ih _
  obtain ⟨u, hu, huniq⟩ := exists_unique_hom_cone c hc γ p' (fun j => a j.unop) hgen
  exact ⟨u, fun n => hu (Opposite.op n), fun u' hu' => huniq u' fun j => hu' j.unop⟩

/-! ### Weighted sequential limits (Proposition 3.2.15) -/

section SeqLimits

variable (D : SeqDiagram C)

theorem SeqDiagram.summable : Summable D.εs := D.hsum.summable

theorem SeqDiagram.tail_eq (i : ℕ) : tailSum D.εs (i + 1) + D.εs i = tailSum D.εs i := by
  rw [tailSum_succ D.summable i, add_comm]

/-- The 0-morphism `x_{i+1}^{t_{i+1}} → x_i^{t_i}` induced by `f_i`. -/
noncomputable def SeqDiagram.phi (i : ℕ) :
    (pow (tailSum D.εs (i + 1))).obj (D.x (i + 1)) ⟶ (pow (tailSum D.εs i)).obj (D.x i) :=
  up (S (le_of_eq (D.tail_eq i)) (comp (D.f i) (down (𝟙 ((pow (tailSum D.εs (i + 1))).obj (D.x (i + 1)))))))

/-- The sequential diagram of powers. -/
noncomputable def SeqDiagram.powDiagram : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun i => (pow (tailSum D.εs i)).obj (D.x i)) D.phi

theorem SeqDiagram.down_phi (i : ℕ) :
    down (D.phi i) = S (le_of_eq (D.tail_eq i))
      (comp (D.f i) (down (𝟙 ((pow (tailSum D.εs (i + 1))).obj (D.x (i + 1)))))) := by
  unfold SeqDiagram.phi
  rw [down_up]

/-- The projection from the limit to `x_i^{t_i}`. -/
noncomputable def SeqDiagram.proj [HasLimitsOfShape ℕᵒᵖ C] (i : ℕ) :
    limit D.powDiagram ⟶ (pow (tailSum D.εs i)).obj (D.x i) :=
  limit.π D.powDiagram (Opposite.op i)

theorem SeqDiagram.proj_phi [HasLimitsOfShape ℕᵒᵖ C] (i : ℕ) :
    D.proj (i + 1) ≫ D.phi i = D.proj i := by
  have hF : D.powDiagram.map (homOfLE (Nat.le_succ i)).op = D.phi i :=
    Functor.ofOpSequence_map_homOfLE_succ _ i
  have := limit.w D.powDiagram (homOfLE (Nat.le_succ i)).op
  rw [hF] at this
  exact this

theorem SeqDiagram.comm_aux [HasLimitsOfShape ℕᵒᵖ C] (i : ℕ) :
    Commutes (down (D.proj (i + 1))) (D.f i) (down (D.proj i)) := by
  rw [Commutes_iff _ _ _ (D.tail_eq i).symm, ← D.proj_phi i, down_comp_pre, SeqDiagram.down_phi]
  have e1 := comp_down_homZero (D.proj (i + 1)) (𝟙 _)
  rw [Category.comp_id] at e1
  have e2 := eq_S_symm (add_assoc (0 : ℝ≥0) (tailSum D.εs (i + 1)) (D.εs i)).symm (assoc' (homZero (D.proj (i + 1)))
    (down (𝟙 ((pow (tailSum D.εs (i + 1))).obj (D.x (i + 1))))) (D.f i)).symm
  rw [comp_S_l, e2, e1, comp_S_r]
  simp only [comp_S_r, S_trans]
  exact S_refl _

theorem SeqDiagram.map_eq (i : ℕ) :
    D.powDiagram.map (homOfLE (Nat.le_succ i)).op = D.phi i :=
  Functor.ofOpSequence_map_homOfLE_succ _ i

/-- Key computation: the images of a family under `phi` correspond to the images under `f`. -/
theorem SeqDiagram.powIso_pmap_phi (i : ℕ) (l' : C) (γ : ℝ≥0)
    (a : hom l' ((pow (tailSum D.εs (i + 1))).obj (D.x (i + 1))) γ) :
    powIso l' (D.x i) (tailSum D.εs i) γ (pmap (D.phi i) a) =
      S (le_of_eq (by rw [← D.tail_eq i]; ring))
        (comp (D.f i) (powIso l' (D.x (i + 1)) (tailSum D.εs (i + 1)) γ a)) := by
  rw [powIso_pmap_hom, SeqDiagram.down_phi]
  have h2 := powIso_pmap_hom a (𝟙 ((pow (tailSum D.εs (i + 1))).obj (D.x (i + 1))))
  rw [pmap_id] at h2
  rw [h2, comp_S_l, comp_S_r, assoc' a (down (𝟙 ((pow (tailSum D.εs (i + 1))).obj (D.x (i + 1))))) (D.f i)]
  simp only [S_trans]

end SeqLimits

/-- Proposition 3.2.15: if `C` is powered by representables and has sequential limits that
powers preserve, then `C` has weighted sequential limits. -/
theorem hasWeightedSeqLimits_of_powered [HasLimitsOfShape ℕᵒᵖ C]
    (hpres : ∀ ε, PreservesLimitsOfShape ℕᵒᵖ (pow (C := C) ε)) : HasWeightedSeqLimits C := by
  intro D
  refine ⟨{ l := limit D.powDiagram, g := fun i => down (D.proj i), comm := D.comm_aux,
            univ := ?_ }⟩
  intro l' γ g' hg
  have := hpres γ
  let a : ∀ n : ℕ, hom l' (D.powDiagram.obj (Opposite.op n)) γ :=
    fun n => (powIso l' (D.x n) (tailSum D.εs n) γ).symm (g' n)
  have ha : ∀ n : ℕ, pmap (D.powDiagram.map (homOfLE (Nat.le_succ n)).op) (a (n + 1)) = a n := by
    intro n
    rw [D.map_eq n]
    apply (powIso l' (D.x n) (tailSum D.εs n) γ).injective
    erw [D.powIso_pmap_phi n l' γ (a (n + 1))]
    have hg' := (Commutes_iff _ _ _ (by rw [← D.tail_eq n]; ring :
      tailSum D.εs n + γ = tailSum D.εs (n + 1) + γ + D.εs n)).1 (hg n)
    show S _ (comp (D.f n) ((powIso l' (D.x (n + 1)) (tailSum D.εs (n + 1)) γ)
      ((powIso l' (D.x (n + 1)) (tailSum D.εs (n + 1)) γ).symm (g' (n + 1))))) =
      (powIso l' (D.x n) (tailSum D.εs n) γ) ((powIso l' (D.x n) (tailSum D.εs n) γ).symm (g' n))
    simp only [Equiv.apply_symm_apply]
    rw [← hg', S_trans]
    exact S_refl _
  obtain ⟨u, hu, huniq⟩ := exists_unique_hom_seq (limit.cone D.powDiagram)
    (limit.isLimit _) γ l' a ha
  have key : ∀ (v : hom l' (limit D.powDiagram) γ) (n : ℕ),
      Commutes v (down (D.proj n)) (g' n) ↔ pmap (D.proj n) v = a n := by
    intro v n
    rw [commutes_down_iff]
    constructor
    · intro H
      apply (powIso l' (D.x n) (tailSum D.εs n) γ).injective
      exact H.trans (Equiv.apply_symm_apply _ _).symm
    · intro H
      rw [H]
      exact Equiv.apply_symm_apply _ _
  refine ⟨u, fun n => (key u n).2 (hu n), fun u' hu' => huniq u' fun n => (key u' n).1 (hu' n)⟩

/-! ### Terminal midpoints (Proposition 3.2.19) -/

section Midpoints

theorem comp_down_one {z' u : C} {n α : ℝ≥0} (v : hom z' ((pow n).obj u) α) :
    comp (down (𝟙 ((pow n).obj u))) v = S (le_of_eq (add_comm n α)) (powIso z' u n α v) := by
  have h2 := powIso_pmap_hom v (𝟙 ((pow n).obj u))
  rw [pmap_id] at h2
  rw [h2, S_trans]
  exact (S_refl _).symm

theorem powIso_up {z' u w : C} {n m α : ℝ≥0} (θ : hom ((pow n).obj u) w m)
    (v : hom z' ((pow n).obj u) α) :
    powIso z' w m α (pmap (up θ) v) = S (le_of_eq (add_comm α m)) (comp θ v) := by
  rw [powIso_pmap_hom, down_up]

variable {x y : C} {ε : ℝ≥0} (f : hom x y ε) (g : hom y x ε) (γ δ : ℝ≥0)

/-- The map `x^γ → x^{δ+ε}`. -/
noncomputable def midSx (hle : γ ≤ δ + ε) : (pow γ).obj x ⟶ (pow (δ + ε)).obj x :=
  up (S hle (down (𝟙 ((pow γ).obj x))))

/-- The map `x^γ → y^{γ+ε}`. -/
noncomputable def midFy : (pow γ).obj x ⟶ (pow (γ + ε)).obj y :=
  up (comp f (down (𝟙 ((pow γ).obj x))))

/-- The map `y^δ → x^{δ+ε}`. -/
noncomputable def midGx : (pow δ).obj y ⟶ (pow (δ + ε)).obj x :=
  up (comp g (down (𝟙 ((pow δ).obj y))))

/-- The map `y^δ → y^{γ+ε}`. -/
noncomputable def midSy (hle : δ ≤ γ + ε) : (pow δ).obj y ⟶ (pow (γ + ε)).obj y :=
  up (S hle (down (𝟙 ((pow δ).obj y))))

theorem powIso_midSx (hle : γ ≤ δ + ε) {z' : C} {α : ℝ≥0} (v : hom z' ((pow γ).obj x) α) :
    powIso z' x (δ + ε) α (pmap (midSx γ δ hle) v) =
      S (add_le_add hle le_rfl : γ + α ≤ δ + ε + α)
        (powIso z' x γ α v) := by
  unfold midSx
  rw [powIso_up, comp_S_l, comp_down_one]
  simp only [S_trans]

theorem powIso_midSy (hle : δ ≤ γ + ε) {z' : C} {α : ℝ≥0} (v : hom z' ((pow δ).obj y) α) :
    powIso z' y (γ + ε) α (pmap (midSy γ δ hle) v) =
      S (add_le_add hle le_rfl : δ + α ≤ γ + ε + α)
        (powIso z' y δ α v) := by
  unfold midSy
  rw [powIso_up, comp_S_l, comp_down_one]
  simp only [S_trans]

theorem powIso_midFy {z' : C} {α : ℝ≥0} (v : hom z' ((pow γ).obj x) α) :
    powIso z' y (γ + ε) α (pmap (midFy f γ) v) =
      S (le_of_eq (by ring)) (comp f (powIso z' x γ α v)) := by
  unfold midFy
  rw [powIso_up, eq_S_symm (add_comm γ α) (comp_down_one v).symm, comp_S_r,
    assoc' v (down (𝟙 ((pow γ).obj x))) f]
  simp only [S_trans]

theorem powIso_midGx {z' : C} {α : ℝ≥0} (v : hom z' ((pow δ).obj y) α) :
    powIso z' x (δ + ε) α (pmap (midGx g δ) v) =
      S (le_of_eq (by ring)) (comp g (powIso z' y δ α v)) := by
  unfold midGx
  rw [powIso_up, eq_S_symm (add_comm δ α) (comp_down_one v).symm, comp_S_r,
    assoc' v (down (𝟙 ((pow δ).obj y))) g]
  simp only [S_trans]

end Midpoints

theorem S_eq_S_iff {x y : C} {s1 s2 t : ℝ≥0} (A : hom x y s1) (B : hom x y s2) (h1 : s1 ≤ t)
    (h2 : s2 ≤ t) (e : s2 = t) :
    S h1 A = S h2 B ↔ S (h1.trans (le_of_eq e.symm)) A = B := by
  subst e
  rw [S_refl]

theorem Commutes_iff_le {x y z : C} {ε δ γ : ℝ≥0} (f : hom x y ε) (g : hom y z δ)
    (h : hom x z γ) (hle : γ ≤ ε + δ) : Commutes f g h ↔ S hle h = comp g f := by
  unfold Commutes
  exact S_eq_S_iff h (comp g f) _ _ (max_eq_right hle).symm

/-- Binary products: `γ`-morphisms into a product are determined by their components. -/
theorem hom_prod_ext [HasBinaryProducts C] {A B z' : C} (α : ℝ≥0)
    [PreservesLimitsOfShape (Discrete WalkingPair) (pow (C := C) α)] {r r' : hom z' (A ⨯ B) α}
    (h1 : pmap prod.fst r = pmap prod.fst r') (h2 : pmap prod.snd r = pmap prod.snd r') :
    r = r' := by
  let a : ∀ j : Discrete WalkingPair, hom z' ((pair A B).obj j) α := fun
    | ⟨WalkingPair.left⟩ => pmap prod.fst r
    | ⟨WalkingPair.right⟩ => pmap prod.snd r
  have ha : ∀ {j j' : Discrete WalkingPair} (e : j ⟶ j'), pmap ((pair A B).map e) (a j) = a j' := by
    intro j j' e
    have hj : j = j' := Discrete.ext (Discrete.eq_of_hom e)
    subst hj
    have : e = 𝟙 j := Subsingleton.elim _ _
    subst this
    rw [CategoryTheory.Functor.map_id]
    exact pmap_id _
  have hc := prodIsProd A B
  obtain ⟨u, hu, huniq⟩ := exists_unique_hom_cone (BinaryFan.mk (prod.fst : A ⨯ B ⟶ A) prod.snd) hc α z' a ha
  have e1 : r = u := huniq r (by
    rintro ⟨_ | _⟩
    · exact rfl
    · exact rfl)
  have e2 : r' = u := huniq r' (by
    rintro ⟨_ | _⟩
    · exact h1.symm
    · exact h2.symm)
  rw [e1, e2]

section MidpointsMain

variable {x y : C} {ε : ℝ≥0} (f : hom x y ε) (g : hom y x ε) (γ δ : ℝ≥0)

theorem mid_E1 (hle1 : γ ≤ δ + ε) {z' : C} {α : ℝ≥0} (a' : hom z' x (γ + α))
    (b' : hom z' y (δ + α)) :
    pmap (midSx γ δ hle1) ((powIso z' x γ α).symm a') = pmap (midGx g δ) ((powIso z' y δ α).symm b') ↔
      Commutes b' g a' := by
  rw [← (powIso z' x (δ + ε) α).injective.eq_iff, powIso_midSx, powIso_midGx,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    S_eq_S_iff _ _ _ _ (by ring : δ + α + ε = δ + ε + α)]
  exact (Commutes_iff_le b' g a' (le_of_le_of_eq (add_le_add hle1 le_rfl)
    (by ring))).symm

theorem mid_E2 (hle2 : δ ≤ γ + ε) {z' : C} {α : ℝ≥0} (a' : hom z' x (γ + α))
    (b' : hom z' y (δ + α)) :
    pmap (midFy f γ) ((powIso z' x γ α).symm a') = pmap (midSy γ δ hle2) ((powIso z' y δ α).symm b') ↔
      Commutes a' f b' := by
  rw [← (powIso z' y (γ + ε) α).injective.eq_iff, powIso_midFy, powIso_midSy,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, eq_comm,
    S_eq_S_iff _ _ _ _ (by ring : γ + α + ε = γ + ε + α)]
  exact (Commutes_iff_le a' f b' (le_of_le_of_eq (add_le_add hle2 le_rfl)
    (by ring))).symm

variable [HasBinaryProducts C]

/-- The map `x^γ → x^{δ+ε} × y^{γ+ε}` of Proposition 3.2.19. -/
noncomputable def midH (hle1 : γ ≤ δ + ε) :
    (pow γ).obj x ⟶ (pow (δ + ε)).obj x ⨯ (pow (γ + ε)).obj y :=
  prod.lift (midSx γ δ hle1) (midFy f γ)

/-- The map `y^δ → x^{δ+ε} × y^{γ+ε}` of Proposition 3.2.19. -/
noncomputable def midK (hle2 : δ ≤ γ + ε) :
    (pow δ).obj y ⟶ (pow (δ + ε)).obj x ⨯ (pow (γ + ε)).obj y :=
  prod.lift (midGx g δ) (midSy γ δ hle2)

theorem mid_iff (hle1 : γ ≤ δ + ε) (hle2 : δ ≤ γ + ε) {z' : C} {α : ℝ≥0}
    [PreservesLimitsOfShape (Discrete WalkingPair) (pow (C := C) α)] (a' : hom z' x (γ + α))
    (b' : hom z' y (δ + α)) :
    pmap (midH f γ δ hle1) ((powIso z' x γ α).symm a') =
        pmap (midK g γ δ hle2) ((powIso z' y δ α).symm b') ↔
      Commutes a' f b' ∧ Commutes b' g a' := by
  constructor
  · intro H
    have h1 := congrArg (pmap prod.fst) H
    have h2 := congrArg (pmap prod.snd) H
    rw [← pmap_comp, ← pmap_comp] at h1 h2
    simp only [midH, midK, prod.lift_fst] at h1
    simp only [midH, midK, prod.lift_snd] at h2
    exact ⟨(mid_E2 f γ δ hle2 a' b').1 h2, (mid_E1 g γ δ hle1 a' b').1 h1⟩
  · rintro ⟨hf, hg⟩
    apply hom_prod_ext α
    · rw [← pmap_comp, ← pmap_comp]
      simp only [midH, midK, prod.lift_fst]
      exact (mid_E1 g γ δ hle1 a' b').2 hg
    · rw [← pmap_comp, ← pmap_comp]
      simp only [midH, midK, prod.lift_snd]
      exact (mid_E2 f γ δ hle2 a' b').2 hf

end MidpointsMain

theorem commutes_reindex {z x y : C} {ε n n' m m' : ℝ≥0} (e : n = n') (e' : m = m')
    (a' : hom z x n) (f : hom x y ε) (b' : hom z y m) :
    Commutes (S (le_of_eq e) a') f (S (le_of_eq e') b') ↔ Commutes a' f b' := by
  subst e e'
  rw [S_refl, S_refl]

/-- Proposition 3.2.19: if `C` is powered by representables, has binary products and
pullbacks, and powers preserve them, then `C` admits terminal midpoints. -/
theorem hasTerminalMidpoints_of_powered [HasBinaryProducts C] [HasPullbacks C]
    (hprod : ∀ ε, PreservesLimitsOfShape (Discrete WalkingPair) (pow (C := C) ε))
    (hpb : ∀ ε, PreservesLimitsOfShape WalkingCospan (pow (C := C) ε)) :
    HasTerminalMidpoints C := by
  intro x y ε f g _ γ δ hγδ
  have hle1 : γ ≤ δ + ε := calc
    γ ≤ γ + δ := le_self_add
    _ = ε := hγδ
    _ ≤ δ + ε := le_add_self
  have hle2 : δ ≤ γ + ε := calc
    δ ≤ γ + δ := le_add_self
    _ = ε := hγδ
    _ ≤ γ + ε := le_add_self
  have hcond : pullback.fst (midH f γ δ hle1) (midK g γ δ hle2) ≫ midH f γ δ hle1 =
      pullback.snd (midH f γ δ hle1) (midK g γ δ hle2) ≫ midK g γ δ hle2 := pullback.condition
  set H := midH f γ δ hle1
  set K := midK g γ δ hle2
  have hz := (mid_iff f g γ δ hle1 hle2 (z' := pullback H K) (α := 0)
    (powIso _ x γ 0 (homZero (pullback.fst H K))) (powIso _ y δ 0 (homZero (pullback.snd H K)))).1
    (by
      simp only [Equiv.symm_apply_apply]
      rw [pmap_homZero, pmap_homZero, hcond])
  have ha : down (pullback.fst H K) = S (le_of_eq (add_zero γ)) (powIso _ x γ 0 (homZero (pullback.fst H K))) := rfl
  have hb : down (pullback.snd H K) = S (le_of_eq (add_zero δ)) (powIso _ y δ 0 (homZero (pullback.snd H K))) := rfl
  refine ⟨{ z := pullback H K, a := down (pullback.fst H K), b := down (pullback.snd H K),
            commf := ?_, commg := ?_, univ := ?_ }⟩
  · rw [ha, hb]
    exact (commutes_reindex (add_zero γ) (add_zero δ) _ f _).2 hz.1
  · rw [ha, hb]
    exact (commutes_reindex (add_zero δ) (add_zero γ) _ g _).2 hz.2
  · intro z' α a' b' hf hg
    have := hprod α
    have := hpb α
    have hsq : pmap H ((powIso z' x γ α).symm a') = pmap K ((powIso z' y δ α).symm b') :=
      (mid_iff f g γ δ hle1 hle2 a' b').2 ⟨hf, hg⟩
    obtain ⟨u, ⟨hu1, hu2⟩, huniq⟩ := exists_unique_hom_pullback H K _
      (pullbackIsPullback H K) α z' _ _ hsq
    refine ⟨u, ⟨?_, ?_⟩, ?_⟩
    · rw [commutes_down_iff]
      have := congrArg (powIso z' x γ α) hu1
      simpa using this
    · rw [commutes_down_iff]
      have := congrArg (powIso z' y δ α) hu2
      simpa using this
    · rintro u' ⟨c1, c2⟩
      refine huniq u' ⟨?_, ?_⟩
      · apply (powIso z' x γ α).injective
        rw [Equiv.apply_symm_apply]
        exact (commutes_down_iff _ _ _).1 c1
      · apply (powIso z' y δ α).injective
        rw [Equiv.apply_symm_apply]
        exact (commutes_down_iff _ _ _).1 c2

end PowerLimits

/-! ## Composites of interleavings along a sequence (toward Proposition 3.2.14)

For a sequence of interleavings `f i : x (i+1) →εs i x i`, `h i : x i →δs i x (i+1)` we define
the `n`-fold composites `upChain : x i → x (i+n)` and `downChain : x (m+n) → x m`, and prove
that they cancel up to a shift. -/

section SeqLimit

open CategoryTheory
open scoped NNReal ENNReal

open LPCat

theorem tail_eq_sum_add {εs : ℕ → ℝ≥0} (hs : Summable εs) (i n : ℕ) :
    tailSum εs i = (∑ j ∈ Finset.range n, εs (i + j)) + tailSum εs (i + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, tailSum_succ hs (i + n), Finset.sum_range_succ]
    simp only [← add_assoc]

variable {C : Type u} [Category.{v} C] [LPCat C]

/-- The `n`-fold composite `x (m+n) → x m` of the maps `f`. -/
noncomputable def downChain {x : ℕ → C} {εs : ℕ → ℝ≥0}
    (f : ∀ i, hom (x (i + 1)) (x i) (εs i)) (m : ℕ) :
    ∀ n, hom (x (m + n)) (x m) (∑ j ∈ Finset.range n, εs (m + j))
  | 0 => S (le_of_eq (by simp)) (idHom (x m))
  | n + 1 => S (le_of_eq (by rw [Finset.sum_range_succ, add_comm]))
      (comp (downChain f m n) (f (m + n)))

/-- The `n`-fold composite `x i → x (i+n)` of the maps `h`. -/
noncomputable def upChain {x : ℕ → C} {δs : ℕ → ℝ≥0}
    (h : ∀ i, hom (x i) (x (i + 1)) (δs i)) (i : ℕ) :
    ∀ n, hom (x i) (x (i + n)) (∑ j ∈ Finset.range n, δs (i + j))
  | 0 => S (le_of_eq (by simp)) (idHom (x i))
  | n + 1 => S (le_of_eq (by rw [Finset.sum_range_succ]))
      (comp (h (i + n)) (upChain h i n))

section
variable {x : ℕ → C} {εs δs : ℕ → ℝ≥0} (f : ∀ i, hom (x (i + 1)) (x i) (εs i))
  (h : ∀ i, hom (x i) (x (i + 1)) (δs i)) (hp : ∀ i, IsInterleavingPair (f i) (h i))

include hp

theorem up_down (i n : ℕ) :
    comp (upChain h i n) (downChain f i n) = S zero_le (idHom (x (i + n))) := by
  induction n with
  | zero =>
    simp only [upChain, downChain, comp_S_l, comp_S_r, id_comp', S_trans]
    rfl
  | succ n ih =>
    simp only [upChain, downChain, comp_S_l, comp_S_r]
    rw [← LPCat.assoc (comp (downChain f i n) (f (i + n))) (upChain h i n) (h (i + n)),
      LPCat.assoc' (f (i + n)) (downChain f i n) (upChain h i n), ih]
    simp only [comp_S_l, comp_S_r, id_comp']
    erw [(hp (i + n)).1]
    simp only [comp_S_r, S_trans]
    rfl

theorem down_up (i n : ℕ) :
    comp (downChain f i n) (upChain h i n) = S zero_le (idHom (x i)) := by
  induction n with
  | zero =>
    simp only [upChain, downChain, comp_S_l, comp_S_r]
    erw [id_comp']
    simp only [S_trans]
  | succ n ih =>
    simp only [upChain, downChain, comp_S_l, comp_S_r]
    rw [← LPCat.assoc (comp (h (i + n)) (upChain h i n)) (f (i + n)) (downChain f i n),
      LPCat.assoc' (upChain h i n) (h (i + n)) (f (i + n))]
    simp only [comp_S_l, comp_S_r]
    erw [(hp (i + n)).2]
    simp only [comp_S_l, comp_S_r, id_comp']
    erw [ih]
    simp only [S_trans]
end

theorem down_comp_g {D : SeqDiagram C} (L : WeightedSeqLimit D) (m n : ℕ) :
    S (le_of_eq (by
        have := tail_eq_sum_add D.hsum.summable m n
        rw [this, add_comm])) (L.g m) =
      comp (downChain D.f m n) (L.g (m + n)) := by
  induction n with
  | zero =>
    simp only [downChain, comp_S_l]
    erw [id_comp']
    simp only [S_trans]
    rfl
  | succ n ih =>
    simp only [downChain, comp_S_l]
    erw [← LPCat.assoc (L.g (m + n + 1)) (D.f (m + n)) (downChain D.f m n)]
    have hc := (Commutes_iff _ _ _ (by rw [tailSum_succ D.hsum.summable (m + n), add_comm]
      : tailSum D.εs (m + n) = tailSum D.εs (m + n + 1) + D.εs (m + n))).1 (L.comm (m + n))
    rw [← hc]
    simp only [comp_S_r]
    rw [← ih]
    simp only [S_trans]

/-! ### Chains with an explicit endpoint equation

`downEq f m n i e : x i → x m` is `downChain f m n` transported along `e : m + n = i`.
All lemmas below quantify over such equations and `subst` them, which avoids casts between
`m + 1 + n` and `m + n + 1`. -/

section Eq
variable {x : ℕ → C} {εs δs : ℕ → ℝ≥0} (f : ∀ i, hom (x (i + 1)) (x i) (εs i))
  (h : ∀ i, hom (x i) (x (i + 1)) (δs i))

/-- `downChain f m n` with its source re-indexed along `m + n = i`. -/
noncomputable def downEq (m n i : ℕ) (e : m + n = i) :
    hom (x i) (x m) (∑ j ∈ Finset.range n, εs (m + j)) := e ▸ downChain f m n

/-- `upChain h i n` with its target re-indexed along `i + n = m`. -/
noncomputable def upEq (i n m : ℕ) (e : i + n = m) :
    hom (x i) (x m) (∑ j ∈ Finset.range n, δs (i + j)) := e ▸ upChain h i n

theorem downEq_rfl (m n : ℕ) : downEq f m n (m + n) rfl = downChain f m n := rfl
theorem upEq_rfl (i n : ℕ) : upEq h i n (i + n) rfl = upChain h i n := rfl

theorem down_peel (m n j : ℕ) (ej : m + n = j) (e : m + (n + 1) = j + 1) :
    downEq f m (n + 1) (j + 1) e = S (le_of_eq (by subst ej; rw [Finset.sum_range_succ, add_comm]))
      (comp (downEq f m n j ej) (f j)) := by
  subst ej
  rfl

theorem up_peel (i n j : ℕ) (ej : i + n = j) (e : i + (n + 1) = j + 1) :
    upEq h i (n + 1) (j + 1) e = S (le_of_eq (by subst ej; rw [Finset.sum_range_succ]))
      (comp (h j) (upEq h i n j ej)) := by
  subst ej
  rfl

/-- Left composition with `f m` extends a down-chain starting at `m + 1`. -/
theorem down_left (m n i : ℕ) (e1 : m + 1 + n = i) (e2 : m + (n + 1) = i) :
    comp (f m) (downEq f (m + 1) n i e1) =
      S (le_of_eq (by
        rw [Finset.sum_range_succ' (fun j => εs (m + j)) n]
        simp only [Nat.add_zero]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [show m + (j + 1) = m + 1 + j by omega]))
        (downEq f m (n + 1) i e2) := by
  induction n generalizing i with
  | zero =>
    subst e1
    have e : downEq f m (0 + 1) (m + 1 + 0) e2 = downChain f m 1 := rfl
    rw [e, downEq_rfl]
    simp only [downChain, comp_S_l, comp_S_r]
    erw [comp_id', id_comp']
    simp only [S_trans]
    rfl
  | succ n ih =>
    subst e1
    have ej : m + (n + 1) = m + 1 + n := by omega
    have hp1 := down_peel f (m + 1) n (m + 1 + n) rfl rfl
    have hp2 := down_peel f m (n + 1) (m + 1 + n) ej e2
    erw [hp1, hp2]
    simp only [comp_S_r, comp_S_l]
    erw [LPCat.assoc' (f (m + 1 + n)) (downEq f (m + 1) n (m + 1 + n) rfl) (f m),
      ih (m + 1 + n) rfl ej]
    simp only [comp_S_l, S_trans]
/-- Right composition with `h i` extends an up-chain starting at `i + 1`. -/
theorem up_left (i n m : ℕ) (e1 : i + 1 + n = m) (e2 : i + (n + 1) = m) :
    comp (upEq h (i + 1) n m e1) (h i) =
      S (le_of_eq (by
        rw [Finset.sum_range_succ' (fun j => δs (i + j)) n, add_comm]
        simp only [Nat.add_zero]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by rw [show i + (j + 1) = i + 1 + j by omega]))
        (upEq h i (n + 1) m e2) := by
  induction n generalizing m with
  | zero =>
    subst e1
    have e : upEq h i (0 + 1) (i + 1 + 0) e2 = upChain h i 1 := rfl
    rw [e, upEq_rfl]
    simp only [upChain, comp_S_l, comp_S_r]
    erw [comp_id', id_comp']
    simp only [S_trans]
    rfl
  | succ n ih =>
    subst e1
    have ej : i + (n + 1) = i + 1 + n := by omega
    have hp1 := up_peel h (i + 1) n (i + 1 + n) rfl rfl
    have hp2 := up_peel h i (n + 1) (i + 1 + n) ej e2
    erw [hp1, hp2]
    simp only [comp_S_r, comp_S_l]
    erw [← LPCat.assoc (h i) (upEq h (i + 1) n (i + 1 + n) rfl) (h (i + 1 + n)),
      ih (i + 1 + n) rfl ej]
    simp only [comp_S_r, S_trans]

theorem downEq_congr_n (m i : ℕ) {n n' : ℕ} (hn : n = n') (e : m + n = i) (e' : m + n' = i) :
    downEq f m n i e = S (le_of_eq (by subst hn; rfl)) (downEq f m n' i e') := by
  subst hn
  rw [S_refl]

theorem upEq_congr_n (i m : ℕ) {n n' : ℕ} (hn : n = n') (e : i + n = m) (e' : i + n' = m) :
    upEq h i n m e = S (le_of_eq (by subst hn; rfl)) (upEq h i n' m e') := by
  subst hn
  rw [S_refl]
end Eq

/-! ### The cone from `x i` -/

section Cone
variable {D : SeqDiagram C} {δs : ℕ → ℝ≥0} (hδ : Summable δs)
  (h : ∀ i, hom (D.x i) (D.x (i + 1)) (δs i))

/-- The cone from `x i` to `x m`: the down-chain if `m ≤ i`, the up-chain otherwise. -/
noncomputable def coneElt (i m : ℕ) : hom (D.x i) (D.x m) (tailSum D.εs m + tailSum δs i) :=
  if hm : m ≤ i then
    S (by
      calc (∑ j ∈ Finset.range (i - m), D.εs (m + j)) ≤ tailSum D.εs m := by
            rw [tail_eq_sum_add D.hsum.summable m (i - m)]; exact le_self_add
        _ ≤ tailSum D.εs m + tailSum δs i := le_self_add)
      (downEq D.f m (i - m) i (Nat.add_sub_cancel' hm))
  else
    S (by
      calc (∑ j ∈ Finset.range (m - i), δs (i + j)) ≤ tailSum δs i := by
            rw [tail_eq_sum_add hδ i (m - i)]; exact le_self_add
        _ ≤ tailSum D.εs m + tailSum δs i := le_add_self)
      (upEq h i (m - i) m (Nat.add_sub_cancel' (by omega)))

theorem cone_comm (hp : ∀ i, IsInterleavingPair (D.f i) (h i)) (i m : ℕ) :
    Commutes (coneElt hδ h i (m + 1)) (D.f m) (coneElt hδ h i m) := by
  rw [Commutes_iff _ _ _ (by rw [tailSum_succ D.hsum.summable m]; ring :
    tailSum D.εs m + tailSum δs i = tailSum D.εs (m + 1) + tailSum δs i + D.εs m)]
  rcases lt_trichotomy m i with hlt | heq | hgt
  · have hm1 : m + 1 ≤ i := hlt
    have hm : m ≤ i := by omega
    unfold coneElt
    rw [dif_pos hm1, dif_pos hm]
    have h1 := downEq_congr_n D.f m i (show i - m = i - (m + 1) + 1 by omega)
      (Nat.add_sub_cancel' hm) (by omega : m + (i - (m + 1) + 1) = i)
    have h2 := down_left D.f m (i - (m + 1)) i (by omega) (by omega)
    rw [h1]
    simp only [comp_S_r, S_trans]
    erw [h2]
    simp only [S_trans]
  · subst heq
    unfold coneElt
    rw [dif_neg (by omega : ¬ m + 1 ≤ m), dif_pos le_rfl]
    have h1 := downEq_congr_n D.f m m (show m - m = 0 by omega) (Nat.add_sub_cancel' le_rfl)
      (by omega : m + 0 = m)
    have h2 := upEq_congr_n h m (m + 1) (show m + 1 - m = 1 by omega)
      (Nat.add_sub_cancel' (by omega)) (by omega : m + 1 = m + 1)
    rw [h1, h2]
    have h3 : downEq D.f m 0 m (by omega : m + 0 = m) = downChain D.f m 0 := rfl
    have h4 : upEq h m 1 (m + 1) (by omega : m + 1 = m + 1) = upChain h m 1 := rfl
    rw [h3, h4]
    simp only [downChain, upChain, comp_S_r]
    erw [comp_id']
    simp only [comp_S_r, S_trans]
    erw [(hp m).2]
    simp only [S_trans]
  · have hm : ¬ m ≤ i := by omega
    have hm1 : ¬ m + 1 ≤ i := by omega
    unfold coneElt
    rw [dif_neg hm, dif_neg hm1]
    have h1 := upEq_congr_n h i (m + 1) (show m + 1 - i = m - i + 1 by omega)
      (Nat.add_sub_cancel' (by omega)) (by omega : i + (m - i + 1) = m + 1)
    have h2 := up_peel h i (m - i) m (by omega) (by omega : i + (m - i + 1) = m + 1)
    rw [h1, h2]
    simp only [comp_S_r, S_trans]
    erw [LPCat.assoc' (upEq h i (m - i) m (Nat.add_sub_cancel' (by omega))) (h m) (D.f m),
      (hp m).2]
    simp only [comp_S_l, id_comp', S_trans]
end Cone

section Compose
variable {D : SeqDiagram C} {δs : ℕ → ℝ≥0} (h : ∀ i, hom (D.x i) (D.x (i + 1)) (δs i))
  (L : WeightedSeqLimit D)

theorem up_down_eq (hp : ∀ i, IsInterleavingPair (D.f i) (h i)) (i n m : ℕ) (e : i + n = m) :
    comp (upEq h i n m e) (downEq D.f i n m e) = S zero_le (idHom (D.x m)) := by
  subst e
  exact up_down D.f h hp i n

theorem down_up_eq (hp : ∀ i, IsInterleavingPair (D.f i) (h i)) (i n m : ℕ) (e : i + n = m) :
    comp (downEq D.f i n m e) (upEq h i n m e) = S zero_le (idHom (D.x i)) := by
  subst e
  exact down_up D.f h hp i n

theorem down_comp_g_eq (m n i : ℕ) (e : m + n = i) :
    S (le_of_eq (by
        subst e
        rw [tail_eq_sum_add D.hsum.summable m n, add_comm])) (L.g m) =
      comp (downEq D.f m n i e) (L.g i) := by
  subst e
  exact down_comp_g L m n

theorem up_comp_g_eq (hp : ∀ i, IsInterleavingPair (D.f i) (h i)) (i n m : ℕ)
    (e : i + n = m) :
    comp (upEq h i n m e) (L.g i) =
      S (by
        calc tailSum D.εs m ≤ tailSum D.εs i := by
              subst e
              rw [tail_eq_sum_add D.hsum.summable i n]
              exact le_add_self
          _ ≤ tailSum D.εs i + ∑ j ∈ Finset.range n, δs (i + j) := le_self_add) (L.g m) := by
  have h1 := down_comp_g_eq L i n m e
  have h2 := eq_S_symm (by subst e; rw [tail_eq_sum_add D.hsum.summable i n, add_comm]) h1
  rw [h2]
  simp only [comp_S_r]
  erw [LPCat.assoc' (L.g m) (downEq D.f i n m e) (upEq h i n m e), up_down_eq h hp i n m e]
  simp only [comp_S_l, id_comp', S_trans]

end Compose

section Props
variable {D : SeqDiagram C} {δs : ℕ → ℝ≥0} (hδ : Summable δs)
  (h : ∀ i, hom (D.x i) (D.x (i + 1)) (δs i))

theorem coneElt_diag (i : ℕ) : coneElt hδ h i i = S zero_le (idHom (D.x i)) := by
  unfold coneElt
  rw [dif_pos le_rfl]
  have h1 := downEq_congr_n D.f i i (show i - i = 0 by omega) (Nat.add_sub_cancel' le_rfl)
    (by omega : i + 0 = i)
  rw [h1]
  have h3 : downEq D.f i 0 i (by omega : i + 0 = i) = downChain D.f i 0 := rfl
  rw [h3]
  simp only [downChain, S_trans]

/-- Composing the cone from `x i` with `g i` recovers `g m`. -/
theorem coneElt_comp_g (hp : ∀ i, IsInterleavingPair (D.f i) (h i)) (L : WeightedSeqLimit D)
    (i m : ℕ) :
    comp (coneElt hδ h i m) (L.g i) =
      S (le_self_add.trans le_add_self : tailSum D.εs m ≤
        tailSum D.εs i + (tailSum D.εs m + tailSum δs i)) (L.g m) := by
  by_cases hm : m ≤ i
  · unfold coneElt
    rw [dif_pos hm, comp_S_l]
    have := down_comp_g_eq L m (i - m) i (Nat.add_sub_cancel' hm)
    rw [← this]
    simp only [S_trans]
  · unfold coneElt
    rw [dif_neg hm, comp_S_l]
    rw [up_comp_g_eq h L hp i (m - i) m (Nat.add_sub_cancel' (by omega))]
    simp only [S_trans]

theorem coneElt_comp_h (hp : ∀ i, IsInterleavingPair (D.f i) (h i)) (i m : ℕ) :
    comp (coneElt hδ h (i + 1) m) (h i) =
      S (le_of_eq (by rw [tailSum_succ hδ i]; ring)) (coneElt hδ h i m) := by
  rcases Nat.lt_or_ge m (i + 1) with hlt | hge
  · -- m ≤ i
    have hm : m ≤ i := by omega
    have hm' : m ≤ i + 1 := by omega
    unfold coneElt
    rw [dif_pos hm, dif_pos hm', comp_S_l]
    have h1 := downEq_congr_n D.f m (i + 1) (show i + 1 - m = (i - m) + 1 by omega)
      (Nat.add_sub_cancel' hm') (by omega : m + (i - m + 1) = i + 1)
    have h2 := down_peel D.f m (i - m) i (Nat.add_sub_cancel' hm) (by omega)
    rw [h1, h2]
    simp only [comp_S_r, comp_S_l, S_trans]
    erw [← LPCat.assoc (h i) (D.f i) (downEq D.f m (i - m) i (Nat.add_sub_cancel' hm)),
      (hp i).2]
    simp only [comp_S_r, comp_id', S_trans]
  · rcases Nat.eq_or_lt_of_le hge with heq | hlt2
    · subst heq
      have hn : ¬ i + 1 ≤ i := by omega
      unfold coneElt
      rw [dif_neg hn]
      have hy : (i + 1 : ℕ) ≤ i + 1 := le_rfl
      rw [dif_pos hy, comp_S_l]
      have h1 := downEq_congr_n D.f (i + 1) (i + 1) (show i + 1 - (i + 1) = 0 by omega)
        (Nat.add_sub_cancel' hy) (by omega : i + 1 + 0 = i + 1)
      have h2 := upEq_congr_n h i (i + 1) (show i + 1 - i = 1 by omega)
        (Nat.add_sub_cancel' (by omega)) (by omega : i + 1 = i + 1)
      rw [h1, h2]
      have h3 : downEq D.f (i + 1) 0 (i + 1) (by omega : i + 1 + 0 = i + 1) =
          downChain D.f (i + 1) 0 := rfl
      have h4 : upEq h i 1 (i + 1) (by omega : i + 1 = i + 1) = upChain h i 1 := rfl
      rw [h3, h4]
      simp only [downChain, upChain, comp_S_l, comp_S_r]
      erw [id_comp', comp_id']
      simp only [S_trans]
      rfl
    · have hm : ¬ m ≤ i := by omega
      have hm' : ¬ m ≤ i + 1 := by omega
      unfold coneElt
      rw [dif_neg hm, dif_neg hm', comp_S_l]
      have h1 := upEq_congr_n h i m (show m - i = (m - (i + 1)) + 1 by omega)
        (Nat.add_sub_cancel' (by omega)) (by omega : i + (m - (i + 1) + 1) = m)
      have h2 := up_left h i (m - (i + 1)) m (by omega) (by omega)
      rw [h1]
      erw [h2]
      simp only [S_trans]
end Props

section Main
variable {D : SeqDiagram C} {δs : ℕ → ℝ≥0} (hδ : Summable δs)
  (h : ∀ i, hom (D.x i) (D.x (i + 1)) (δs i))
  (hp : ∀ i, IsInterleavingPair (D.f i) (h i)) (L : WeightedSeqLimit D)
  (k : ∀ i, hom (D.x i) L.l (tailSum δs i))
  (hk : ∀ i m, Commutes (k i) (L.g m) (coneElt hδ h i m))

include hk in
theorem comp_g_k (i : ℕ) : comp (L.g i) (k i) = S zero_le (idHom (D.x i)) := by
  have := (Commutes_iff _ _ _ (by ring : tailSum D.εs i + tailSum δs i =
    tailSum δs i + tailSum D.εs i)).1 (hk i i)
  rw [coneElt_diag] at this
  rw [← this, S_trans]

include hp hk in
theorem comp_k_g (i : ℕ) : comp (k i) (L.g i) = S zero_le (idHom L.l) := by
  -- the cone `S (g m)` from `L.l` with parameter `T i + U i`
  let g'' : ∀ m, hom L.l (D.x m) (tailSum D.εs m + (tailSum D.εs i + tailSum δs i)) :=
    fun m => S le_self_add (L.g m)
  have hcone : ∀ m, Commutes (g'' (m + 1)) (D.f m) (g'' m) := by
    intro m
    have hc := (Commutes_iff _ _ _ (by rw [tailSum_succ D.hsum.summable m]; ring :
      tailSum D.εs m = tailSum D.εs (m + 1) + D.εs m)).1 (L.comm m)
    rw [Commutes_iff _ _ _ (by rw [tailSum_succ D.hsum.summable m]; ring :
      tailSum D.εs m + (tailSum D.εs i + tailSum δs i) =
        tailSum D.εs (m + 1) + (tailSum D.εs i + tailSum δs i) + D.εs m)]
    simp only [g'', comp_S_r, S_trans]
    rw [← hc, S_trans]
  obtain ⟨u, _, hu⟩ := L.univ L.l (tailSum D.εs i + tailSum δs i) g'' hcone
  have h1 : S zero_le (idHom L.l) = u := by
    apply hu
    intro m
    rw [Commutes_iff _ _ _ (by ring : tailSum D.εs m + (tailSum D.εs i + tailSum δs i) =
      tailSum D.εs i + tailSum δs i + tailSum D.εs m)]
    simp only [g'', comp_S_r, comp_id', S_trans]
  have h2 : comp (k i) (L.g i) = u := by
    apply hu
    intro m
    rw [Commutes_iff _ _ _ (by ring : tailSum D.εs m + (tailSum D.εs i + tailSum δs i) =
      tailSum D.εs i + tailSum δs i + tailSum D.εs m)]
    have hkm := (Commutes_iff _ _ _ (by ring : tailSum D.εs m + tailSum δs i =
        tailSum δs i + tailSum D.εs m)).1 (hk i m)
    erw [LPCat.assoc' (L.g i) (k i) (L.g m), ← hkm]
    simp only [comp_S_l, coneElt_comp_g hδ h hp L i m, g'', S_trans]
  rw [h2, h1]

include hp hk in
theorem k_compat
    (hku : ∀ i y, (∀ m, Commutes y (L.g m) (coneElt hδ h i m)) → y = k i) (i : ℕ) :
    Commutes (h i) (k (i + 1)) (k i) := by
  have e : tailSum δs i = δs i + tailSum δs (i + 1) := tailSum_succ hδ i
  have hu2 : ∀ m, Commutes (S (le_of_eq e.symm) (comp (k (i + 1)) (h i)) : hom _ _ (tailSum δs i))
      (L.g m) (coneElt hδ h i m) := by
    intro m
    rw [Commutes_iff _ _ _ (by ring : tailSum D.εs m + tailSum δs i =
      tailSum δs i + tailSum D.εs m)]
    have hkm := (Commutes_iff _ _ _ (by ring : tailSum D.εs m + tailSum δs (i + 1) =
        tailSum δs (i + 1) + tailSum D.εs m)).1 (hk (i + 1) m)
    simp only [comp_S_r]
    erw [LPCat.assoc' (h i) (k (i + 1)) (L.g m), ← hkm]
    simp only [comp_S_l, coneElt_comp_h hδ h hp i m, S_trans]
  have := hku i _ hu2
  rw [Commutes_iff _ _ _ e, ← this]
  simp only [S_trans, S_refl]

end Main

section Unique
variable {D : SeqDiagram C} {δs : ℕ → ℝ≥0} (hδ : Summable δs)
  (h : ∀ i, hom (D.x i) (D.x (i + 1)) (δs i))
  (L : WeightedSeqLimit D) (k' : ∀ i, hom (D.x i) L.l (tailSum δs i))
  (hc' : ∀ i, Commutes (h i) (k' (i + 1)) (k' i))

include hc' in
theorem compat_iter (i n m : ℕ) (e : i + n = m) :
    S (le_of_eq (by
        subst e
        rw [tail_eq_sum_add hδ i n, add_comm])) (k' i) = comp (k' m) (upEq h i n m e) := by
  induction n generalizing m with
  | zero =>
    subst e
    have h0 : upEq h i 0 (i + 0) rfl = upChain h i 0 := rfl
    have : upEq h i 0 (i + 0) rfl = upChain h i 0 := h0
    rw [this]
    simp only [upChain, comp_S_r]
    erw [comp_id']
    simp only [S_trans]
    rfl
  | succ n ih =>
    subst e
    have hp1 := up_peel h i n (i + n) rfl rfl
    have hc := (Commutes_iff _ _ _ (tailSum_succ hδ (i + n))).1 (hc' (i + n))
    erw [hp1]
    simp only [comp_S_r]
    erw [LPCat.assoc' (upEq h i n (i + n) rfl) (h (i + n)) (k' (i + n + 1)), ← hc]
    simp only [comp_S_l]
    erw [← ih (i + n) rfl]
    simp only [S_trans]
include hc' in
theorem k'_cone (hp : ∀ i, IsInterleavingPair (D.f i) (h i))
    (hpair' : ∀ i, IsInterleavingPair (L.g i) (k' i)) (i m : ℕ) :
    Commutes (k' i) (L.g m) (coneElt hδ h i m) := by
  rw [Commutes_iff _ _ _ (by ring : tailSum D.εs m + tailSum δs i =
    tailSum δs i + tailSum D.εs m)]
  by_cases hm : m ≤ i
  · unfold coneElt
    rw [dif_pos hm]
    have h1 := down_comp_g_eq L m (i - m) i (Nat.add_sub_cancel' hm)
    have h2 := eq_S_symm (by
      rw [tail_eq_sum_add D.hsum.summable m (i - m), Nat.add_sub_cancel' hm, add_comm]) h1
    rw [h2]
    simp only [comp_S_l, S_trans]
    erw [← LPCat.assoc (k' i) (L.g i) (downEq D.f m (i - m) i (Nat.add_sub_cancel' hm)),
      (hpair' i).2]
    simp only [comp_S_r, comp_id', S_trans]
  · unfold coneElt
    rw [dif_neg hm]
    have h1 := compat_iter hδ h L k' hc' i (m - i) m (Nat.add_sub_cancel' (by omega))
    have h2 := eq_S_symm (by
      rw [tail_eq_sum_add hδ i (m - i), Nat.add_sub_cancel' (by omega), add_comm]) h1
    rw [h2]
    simp only [comp_S_r, S_trans]
    erw [LPCat.assoc' (upEq h i (m - i) m (Nat.add_sub_cancel' (by omega))) (k' m) (L.g m),
      (hpair' m).2]
    simp only [comp_S_l, id_comp', S_trans]
end Unique

/-- Proposition 3.2.14: a weighted sequential limit of a diagram whose maps are part of
interleavings is interleaved with each object of the diagram: `g i : l →ε̃ᵢ xᵢ` and
`k i : xᵢ →δ̃ᵢ l` form an interleaving, where `ε̃ᵢ, δ̃ᵢ` are the tails of the sums. -/
theorem WeightedSeqLimit.interleaving {D : SeqDiagram C} (L : WeightedSeqLimit D)
    (δs : ℕ → ℝ≥0) (hδs : Summable δs) (h : ∀ i, hom (D.x i) (D.x (i + 1)) (δs i))
    (hpair : ∀ i, IsInterleavingPair (D.f i) (h i)) :
    ∃! k : ∀ i, hom (D.x i) L.l (tailSum δs i),
      (∀ i, IsInterleavingPair (L.g i) (k i)) ∧ ∀ i, Commutes (h i) (k (i + 1)) (k i) := by
  have hu := fun i => L.univ (D.x i) (tailSum δs i) (coneElt hδs h i)
    (cone_comm hδs h hpair i)
  choose k hk hku using hu
  refine ⟨k, ⟨fun i => ⟨comp_k_g hδs h hpair L k hk i, comp_g_k hδs h L k hk i⟩,
    fun i => k_compat hδs h hpair L k hk hku i⟩, ?_⟩
  rintro k' ⟨hpair', hc'⟩
  funext i
  exact hku i (k' i) (k'_cone hδs h L k' hc' hpair hpair' i)

end SeqLimit

/-! ## The locally persistent category of persistent objects (Example 3.1.3)

For a category `D`, the functor category `ℝ ⥤ D` with `ε`-morphisms `X → Y` the natural
transformations `X → Y^ε`, composition by whiskering, and shifts given by the structure maps. -/

section PersistentObjects

open CategoryTheory
open scoped NNReal

variable (D : Type u) [Category.{v} D]

namespace PersistentObjects

variable {D}

/-- `Y.map` along an equality of real parameters. -/
def mapEq (Y : ℝ ⥤ D) {a b : ℝ} (e : a = b) : Y.obj a ⟶ Y.obj b := Y.map (homOfLE (le_of_eq e))

theorem mapEq_comp (Y : ℝ ⥤ D) {a b c : ℝ} (e : a = b) (e' : b = c) :
    mapEq Y e ≫ mapEq Y e' = mapEq Y (e.trans e') := by
  simp [mapEq, ← Y.map_comp]

theorem mapEq_rfl (Y : ℝ ⥤ D) (a : ℝ) : mapEq Y (rfl : a = a) = 𝟙 _ := by
  simp [mapEq]

variable {X Y Z : ℝ ⥤ D}

/-- Build an `ε`-approximate morphism from components. -/
def mk' (ε : ℝ) (c : ∀ q, X.obj q ⟶ Y.obj (ε + q))
    (nat : ∀ (q q' : ℝ) (h : q ≤ q'), X.map (homOfLE h) ≫ c q' =
      c q ≫ Y.map (homOfLE (add_le_add le_rfl h))) : X ⟶ shift ε Y where
  app := c
  naturality := fun q q' g => nat q q' (leOfHom g)

/-- A natural transformation `X ⟶ Y` as a `0`-approximate morphism (`r = 0`). -/
def toZero (r : ℝ) (hr : r = 0) (f : X ⟶ Y) : X ⟶ shift r Y :=
  mk' r (fun q => f.app q ≫ mapEq Y (show q = r + q by rw [hr]; simp)) (by
    subst hr
    intro q q' h
    have := f.naturality (homOfLE h)
    erw [← Category.assoc, this]
    simp only [Category.assoc, mapEq, ← Y.map_comp]
    rfl)

/-- A `0`-approximate morphism (`r = 0`) as a natural transformation. -/
def ofZero (r : ℝ) (hr : r = 0) (f : X ⟶ shift r Y) : X ⟶ Y where
  app q := f.app q ≫ mapEq Y (show r + q = q by rw [hr]; simp)
  naturality := by
    subst hr
    intro q q' g
    have := f.naturality g
    simp only [shift, Functor.comp_map] at this
    erw [← Category.assoc, this]
    unfold mapEq
    erw [Category.assoc, Category.assoc, ← Y.map_comp, ← Y.map_comp]
    rfl

/-- Composition of approximate morphisms, with real parameter `r = ε + δ`. -/
def compR {ε δ : ℝ} (r : ℝ) (hr : r = ε + δ) (g : Y ⟶ shift δ Z) (f : X ⟶ shift ε Y) :
    X ⟶ shift r Z :=
  mk' r (fun q => f.app q ≫ g.app (ε + q) ≫ mapEq Z (show δ + (ε + q) = r + q by
      rw [hr]; ring)) (by
    intro q q' h
    have h1 := f.naturality (homOfLE h)
    have h2 := g.naturality (homOfLE (add_le_add le_rfl h : ε + q ≤ ε + q'))
    erw [← Category.assoc, h1, Category.assoc, Category.assoc, ← Category.assoc (Y.map _), h2]
    unfold mapEq
    erw [Category.assoc (g.app (ε + q)), Category.assoc (g.app (ε + q)), ← Z.map_comp,
      ← Z.map_comp]
    rfl)

/-- Shift of approximate morphisms, with real parameters. -/
def shiftR {ε δ : ℝ} (hle : ε ≤ δ) (f : X ⟶ shift ε Y) : X ⟶ shift δ Y :=
  mk' δ (fun q => f.app q ≫ Y.map (homOfLE (add_le_add hle le_rfl))) (by
    intro q q' h
    have h1 := f.naturality (homOfLE h)
    erw [← Category.assoc, h1]
    erw [Category.assoc, Category.assoc, ← Y.map_comp, ← Y.map_comp]
    rfl)

theorem comp_Ymap_eq_id (Y : ℝ ⥤ D) {P : D} {a : ℝ} (f : P ⟶ Y.obj a) (e : a ⟶ a) :
    f ≫ Y.map e = f := by
  rw [Subsingleton.elim e (𝟙 a)]
  simp

theorem comp_two_Ymap (Y : ℝ ⥤ D) {P : D} {a b : ℝ} (f : P ⟶ Y.obj a) (e1 : a ⟶ b)
    (e2 : b ⟶ a) : (f ≫ Y.map e1) ≫ Y.map e2 = f := by
  rw [Category.assoc, ← Y.map_comp, Subsingleton.elim (e1 ≫ e2) (𝟙 a)]
  simp

theorem aux3 (Z : ℝ ⥤ D) {P : D} {a b c d : ℝ} (u : P ⟶ Z.obj a) (e1 : a ⟶ b)
    (e2 : b ⟶ d) (e3 : a ⟶ c) (e4 : c ⟶ d) :
    (u ≫ Z.map e1) ≫ Z.map e2 = (u ≫ Z.map e3) ≫ Z.map e4 := by
  rw [Category.assoc, Category.assoc, ← Z.map_comp, ← Z.map_comp,
    Subsingleton.elim (e1 ≫ e2) (e3 ≫ e4)]

theorem aux4 (Z : ℝ ⥤ D) {P A : D} {b c d e b' : ℝ} (f : P ⟶ A) (g : A ⟶ Z.obj b)
    (s : b ⟶ c) (m1 : c ⟶ d) (m2 : d ⟶ e) (m : b ⟶ b') (c' : b' ⟶ e) :
    f ≫ ((g ≫ Z.map s) ≫ (Z.map m1 ≫ Z.map m2)) = (f ≫ (g ≫ Z.map m)) ≫ Z.map c' := by
  simp only [Category.assoc, ← Z.map_comp]
  rw [Subsingleton.elim (s ≫ m1 ≫ m2) (m ≫ c')]

theorem aux5 (Z W : ℝ ⥤ D) {P A : D} {z1 z2 w1 w2 w3 w4 w5 : ℝ} (f : P ⟶ A) (g : A ⟶ Z.obj z1)
    (e : z1 ⟶ z2) (H : Z.obj z2 ⟶ W.obj w1) (H' : Z.obj z1 ⟶ W.obj w2) (n : w2 ⟶ w1)
    (hnat : Z.map e ≫ H = H' ≫ W.map n) (m1 : w1 ⟶ w3) (m2 : w3 ⟶ w5) (m3 : w2 ⟶ w4)
    (m4 : w4 ⟶ w5) :
    ((f ≫ (g ≫ Z.map e)) ≫ (H ≫ W.map m1)) ≫ W.map m2 =
      f ≫ ((g ≫ (H' ≫ W.map m3)) ≫ W.map m4) := by
  simp only [Category.assoc]
  rw [reassoc_of% hnat]
  simp only [← W.map_comp, ← Category.assoc]
  simp only [Category.assoc, ← W.map_comp]
  rw [Subsingleton.elim (n ≫ m1 ≫ m2) (m3 ≫ m4)]

theorem aux6 (Y Z : ℝ ⥤ D) {P : D} {y1 y2 z1 z2 z3 z4 z5 : ℝ} (f : P ⟶ Y.obj y1)
    (e : y1 ⟶ y2) (g : Y.obj y1 ⟶ Z.obj z1) (g' : Y.obj y2 ⟶ Z.obj z2) (n : z1 ⟶ z2)
    (hnat : Y.map e ≫ g' = g ≫ Z.map n) (m : z1 ⟶ z5) (m1 : z2 ⟶ z3) (m2 : z3 ⟶ z4)
    (m3 : z4 ⟶ z5) :
    (f ≫ g) ≫ Z.map m = ((f ≫ Y.map e) ≫ ((g' ≫ Z.map m1) ≫ Z.map m2)) ≫ Z.map m3 := by
  simp only [Category.assoc]
  rw [reassoc_of% hnat]
  simp only [← Z.map_comp, Category.assoc]
  rw [Subsingleton.elim (n ≫ m1 ≫ m2 ≫ m3) m]

theorem aux8 (Y : ℝ ⥤ D) {P A : D} {a1 a2 a3 a4 a5 a6 : ℝ} (p : P ⟶ A) (u : A ⟶ Y.obj a1)
    (m1 : a1 ⟶ a2) (m2 : a2 ⟶ a3) (m3 : a3 ⟶ a6) (m4 : a1 ⟶ a4) (m5 : a4 ⟶ a5)
    (m6 : a5 ⟶ a6) :
    ((p ≫ (u ≫ Y.map m1)) ≫ Y.map m2) ≫ Y.map m3 =
      (p ≫ ((u ≫ Y.map m4) ≫ Y.map m5)) ≫ Y.map m6 := by
  simp only [Category.assoc, ← Y.map_comp]
  rw [Subsingleton.elim (m1 ≫ m2 ≫ m3) (m4 ≫ m5 ≫ m6)]

theorem aux10 (Y Y' : ℝ ⥤ D) {P : D} {y1 y2 w1 w2 w3 w4 w5 w6 w3' w4' : ℝ} (u : P ⟶ Y.obj y1)
    (e : y1 ⟶ y2) (F : Y.obj y1 ⟶ Y'.obj w1) (f' : Y.obj y2 ⟶ Y'.obj w2) (n : w1 ⟶ w2)
    (hnat : Y.map e ≫ f' = F ≫ Y'.map n) (a1 : w1 ⟶ w3) (a2 : w3 ⟶ w4) (a3 : w4 ⟶ w5)
    (a4 : w5 ⟶ w6) (b1 : w2 ⟶ w3') (b2 : w3' ⟶ w4') (b3 : w4' ⟶ w6) :
    ((u ≫ ((F ≫ Y'.map a1) ≫ Y'.map a2)) ≫ Y'.map a3) ≫ Y'.map a4 =
      ((u ≫ Y.map e) ≫ ((f' ≫ Y'.map b1) ≫ Y'.map b2)) ≫ Y'.map b3 := by
  simp only [Category.assoc]
  rw [reassoc_of% hnat]
  simp only [← Y'.map_comp]
  rw [Subsingleton.elim (a1 ≫ a2 ≫ a3 ≫ a4) (n ≫ b1 ≫ b2 ≫ b3)]

theorem aux13 (Y : ℝ ⥤ D) {P A : D} {a1 a2 a3 a5 a6 : ℝ} (p : P ⟶ A) (u : A ⟶ Y.obj a1)
    (m1 : a1 ⟶ a2) (m2 : a2 ⟶ a6) (m3 : a1 ⟶ a3) (m4 : a3 ⟶ a5) (m5 : a5 ⟶ a6) :
    (p ≫ u ≫ Y.map m1) ≫ Y.map m2 = (p ≫ (u ≫ Y.map m3) ≫ Y.map m4) ≫ Y.map m5 := by
  simp only [Category.assoc, ← Y.map_comp]
  rw [Subsingleton.elim (m1 ≫ m2) (m3 ≫ m4 ≫ m5)]

theorem toZero_app (r : ℝ) (hr : r = 0) (f : X ⟶ Y) (q : ℝ) :
    (toZero r hr f).app q = f.app q ≫ mapEq Y (show q = r + q by rw [hr]; simp) := rfl

theorem ofZero_app (r : ℝ) (hr : r = 0) (f : X ⟶ shift r Y) (q : ℝ) :
    (ofZero r hr f).app q = f.app q ≫ mapEq Y (show r + q = q by rw [hr]; simp) := rfl

theorem compR_app {ε δ : ℝ} (r : ℝ) (hr : r = ε + δ) (g : Y ⟶ shift δ Z) (f : X ⟶ shift ε Y)
    (q : ℝ) : (compR r hr g f).app q =
      f.app q ≫ g.app (ε + q) ≫ mapEq Z (show δ + (ε + q) = r + q by rw [hr]; ring) := rfl

theorem shiftR_app {ε δ : ℝ} (hle : ε ≤ δ) (f : X ⟶ shift ε Y) (q : ℝ) :
    (shiftR hle f).app q = f.app q ≫ Y.map (homOfLE (add_le_add hle le_rfl)) := rfl

end PersistentObjects

open PersistentObjects in
/-- Example 3.1.3: the locally persistent category of persistent objects of `D`. -/
noncomputable def persistentLPCat : LPCat (ℝ ⥤ D) where
  hom X Y ε := X ⟶ shift (ε : ℝ) Y
  homZero {X Y} :=
    { toFun := fun f => toZero ((0 : ℝ≥0) : ℝ) (by simp) f
      invFun := fun f => ofZero ((0 : ℝ≥0) : ℝ) (by simp) f
      left_inv := by
        intro f; ext q
        erw [ofZero_app (hr := by simp), toZero_app (hr := by simp)]
        unfold mapEq
        exact comp_two_Ymap Y _ _ _
      right_inv := by
        intro f; ext q
        erw [toZero_app (hr := by simp), ofZero_app (hr := by simp)]
        unfold mapEq
        exact comp_two_Ymap Y _ _ _ }
  comp g f := compR (((_ + _ : ℝ≥0)) : ℝ) (by push_cast; rfl) g f
  S hle f := shiftR (NNReal.coe_le_coe.2 hle) f
  id_comp := by
    intro X Y ε f
    ext q
    erw [shiftR_app, compR_app, toZero_app (hr := by simp)]
    simp only [NatTrans.id_app, Category.id_comp, Category.assoc, mapEq, ← Y.map_comp]
    erw [Category.assoc, Category.assoc, ← Y.map_comp, ← Y.map_comp]
    exact comp_Ymap_eq_id Y _ _
  comp_id := by
    intro X Y ε f
    ext q
    erw [shiftR_app, compR_app, toZero_app (hr := by simp)]
    have hnat := f.naturality (homOfLE (le_of_eq (show q = ((0 : ℝ≥0) : ℝ) + q by simp)))
    simp only [NatTrans.id_app, Category.id_comp, mapEq]
    erw [Category.assoc, Category.assoc, ← Category.assoc (X.map _) (f.app _), hnat]
    erw [← Y.map_comp]
    exact comp_two_Ymap Y _ _ _
  assoc := by
    intro X Y Z W ε δ γ f g h
    ext q
    erw [shiftR_app, compR_app, compR_app, compR_app, compR_app]
    have hh := h.naturality (homOfLE (le_of_eq (show ((δ : ℝ≥0) : ℝ) + (((ε : ℝ≥0) : ℝ) + q) =
      ((ε + δ : ℝ≥0) : ℝ) + q by push_cast; ring)))
    unfold mapEq
    exact aux5 Z W _ _ _ _ _ _ hh _ _ _ _
  S_refl := by
    intro X Y ε f
    ext q
    erw [shiftR_app]
    exact comp_Ymap_eq_id Y _ _
  S_trans := by
    intro X Y ε δ γ h1 h2 f
    ext q
    erw [shiftR_app, shiftR_app, shiftR_app]
    erw [Category.assoc, ← Y.map_comp]
    rfl
  comp_S := by
    intro X Y Z ε ε' δ δ' hε hδ f g
    ext q
    erw [compR_app, shiftR_app, shiftR_app, shiftR_app, compR_app]
    have hg := g.naturality (homOfLE (show ((ε : ℝ≥0) : ℝ) + q ≤ ((ε' : ℝ≥0) : ℝ) + q from
      add_le_add (NNReal.coe_le_coe.2 hε) le_rfl))
    erw [Category.assoc, Category.assoc (g.app _), ← Category.assoc (Y.map _) (g.app _), hg]
    unfold mapEq
    exact aux4 Z _ _ _ _ _ _ _
  homZero_comp := by
    intro X Y Z f g
    ext q
    erw [toZero_app (hr := by simp), shiftR_app, compR_app, toZero_app (hr := by simp),
      toZero_app (hr := by simp)]
    have hg := g.naturality (homOfLE (le_of_eq (show q = ((0 : ℝ≥0) : ℝ) + q by simp)))
    unfold mapEq
    erw [NatTrans.comp_app]
    exact aux6 Y Z _ _ _ _ _ hg _ _ _ _

namespace PersistentObjects
variable {D} {X Y : ℝ ⥤ D}

/-- `Hom(X, (Y^ε)^r) ≅ Hom(X, Y^{s})` for `s = ε + r`: post-composition with the
structure isomorphism `Y(s + q) = Y(ε + (r + q))`. -/
def powTo (ε r s : ℝ) (hs : s = ε + r) (u : X ⟶ shift r (shift ε Y)) : X ⟶ shift s Y :=
  mk' s (fun q => u.app q ≫ mapEq Y (show ε + (r + q) = s + q by rw [hs]; ring)) (by
    intro q q' h
    have h1 := u.naturality (homOfLE h)
    erw [← Category.assoc, h1]
    unfold mapEq
    exact aux3 Y _ _ _ _ _)

/-- The inverse of `powTo`. -/
def powFrom (ε r s : ℝ) (hs : s = ε + r) (u : X ⟶ shift s Y) : X ⟶ shift r (shift ε Y) :=
  mk' r (fun q => u.app q ≫ mapEq Y (show s + q = ε + (r + q) by rw [hs]; ring)) (by
    intro q q' h
    have h1 := u.naturality (homOfLE h)
    erw [← Category.assoc, h1]
    unfold mapEq
    exact aux3 Y _ _ _ _ _)

theorem powTo_app (ε r s : ℝ) (hs : s = ε + r) (u : X ⟶ shift r (shift ε Y)) (q : ℝ) :
    (powTo ε r s hs u).app q = u.app q ≫ mapEq Y (show ε + (r + q) = s + q by rw [hs]; ring) :=
  rfl

end PersistentObjects

/-- Example 3.1.3: the locally persistent structure on `ℝ ⥤ D` has `ε`-morphisms
`X → Y^ε`. -/
theorem persistentLPCat_hom (X Y : ℝ ⥤ D) (ε : ℝ≥0) :
    @LPCat.hom _ _ (persistentLPCat D) X Y ε = (X ⟶ shift (ε : ℝ) Y) := rfl

attribute [local instance] persistentLPCat

open PersistentObjects in
/-- The powers by representables of `D^ℝ`: `Y^ε = shift ε Y`. -/
noncomputable def persistentPowered : @PoweredByRepresentables (ℝ ⥤ D) _ (persistentLPCat D) where
  pow ε := (Functor.whiskeringLeft ℝ ℝ D).obj (addLeft ((ε : ℝ≥0) : ℝ))
  powIso x y ε r :=
    { toFun := fun u => powTo ((ε : ℝ≥0) : ℝ) ((r : ℝ≥0) : ℝ) (((ε + r : ℝ≥0)) : ℝ)
        (by push_cast; rfl) u
      invFun := fun u => powFrom ((ε : ℝ≥0) : ℝ) ((r : ℝ≥0) : ℝ) (((ε + r : ℝ≥0)) : ℝ)
        (by push_cast; rfl) u
      left_inv := by
        intro u; apply NatTrans.ext; funext q
        change (u.app q ≫ mapEq y _) ≫ mapEq y _ = u.app q
        unfold mapEq
        exact comp_two_Ymap y _ _ _
      right_inv := by
        intro u; apply NatTrans.ext; funext q
        change (u.app q ≫ mapEq y _) ≫ mapEq y _ = u.app q
        unfold mapEq
        exact comp_two_Ymap y _ _ _ }
  powIso_S := by
    intro x y ε r r' h u
    apply NatTrans.ext; funext q
    exact aux3 y _ _ _ _ _
  powIso_x := by
    intro x x' y ε r δ v u
    apply NatTrans.ext; funext q
    erw [powTo_app (hs := by push_cast; rfl), compR_app, shiftR_app, compR_app,
      powTo_app (hs := by push_cast; rfl)]
    unfold mapEq
    exact aux13 y _ _ _ _ _ _ _
  powIso_y := by
    intro x y y' ε r f u
    apply NatTrans.ext; funext q
    erw [powTo_app (hs := by push_cast; rfl), shiftR_app, compR_app, toZero_app (hr := by simp),
      shiftR_app, compR_app, powTo_app (hs := by push_cast; rfl), toZero_app (hr := by simp)]
    have hf := f.naturality (homOfLE (le_of_eq (show ((ε : ℝ≥0) : ℝ) + (((r : ℝ≥0) : ℝ) + q) =
      ((ε + r : ℝ≥0) : ℝ) + q by push_cast; ring)))
    unfold mapEq
    exact aux10 y y' _ _ _ _ _ hf _ _ _ _ _ _ _

/-- Example 3.2.7 (powers): `D^ℝ` is powered by representables, with `Y^ε = shift ε Y`. -/
theorem persistent_poweredByRepresentables :
    Nonempty (@PoweredByRepresentables (ℝ ⥤ D) _ (persistentLPCat D)) :=
  ⟨persistentPowered D⟩

namespace PersistentObjects
variable {D}

theorem aux14 (y : ℝ ⥤ D) {P Q : D} (m : P ⟶ Q) {a b c d : ℝ} (u : Q ⟶ y.obj a) (e1 : a ⟶ b)
    (e2 : b ⟶ d) (e3 : a ⟶ c) (e4 : c ⟶ d) :
    m ≫ (u ≫ y.map e1) ≫ y.map e2 = (m ≫ u ≫ y.map e3) ≫ y.map e4 := by
  simp only [Category.assoc, ← y.map_comp]
  congr 3

theorem aux15 (x x' y : ℝ ⥤ D) (f : x' ⟶ x) {q a b1 b2 b3 w1 w2 w3 w4 w5 w6 w7 : ℝ}
    (U1 : x.obj b1 ⟶ y.obj w1) (U2 : x.obj b3 ⟶ y.obj w2) (eb : b1 ⟶ b3) (ew : w1 ⟶ w2)
    (hU : x.map eb ≫ U2 = U1 ≫ y.map ew)
    (m0 : q ⟶ a) (M : a ⟶ b1) (N1 : q ⟶ b2) (N2 : b2 ⟶ b3)
    (Y1 : w1 ⟶ w3) (Y2 : w3 ⟶ w4) (Y3 : w4 ⟶ w5) (Y4 : w2 ⟶ w6) (Y5 : w6 ⟶ w7) (Y6 : w7 ⟶ w5) :
    x'.map m0 ≫ (((f.app a ≫ x.map M) ≫ U1 ≫ y.map Y1) ≫ y.map Y2) ≫ y.map Y3 =
      ((f.app q ≫ x.map N1) ≫ (x.map N2 ≫ U2 ≫ y.map Y4) ≫ y.map Y5) ≫ y.map Y6 := by
  have hf := f.naturality m0
  simp only [Category.assoc]
  rw [reassoc_of% hf]
  simp only [← x.map_comp_assoc, ← y.map_comp]
  have e : N1 ≫ N2 = (m0 ≫ M) ≫ eb := Subsingleton.elim _ _
  rw [e]
  simp only [x.map_comp, Category.assoc]
  rw [reassoc_of% hU]
  simp only [← y.map_comp]
  rw [Subsingleton.elim (Y1 ≫ Y2 ≫ Y3) (ew ≫ Y4 ≫ Y5 ≫ Y6)]

theorem aux16 (x y y' : ℝ ⥤ D) {q a b c2 d1 d2 e1 e2 f1 : ℝ}
    (U : x.obj a ⟶ y.obj b) (V1 : y.obj b ⟶ y'.obj d1) (V2 : y.obj c2 ⟶ y'.obj d2)
    (ec : b ⟶ c2) (ed : d1 ⟶ d2) (hV : y.map ec ≫ V2 = V1 ≫ y'.map ed)
    (m0 : q ⟶ a) (m1 : q ⟶ a) (M' : b ⟶ c2) (Y1 : d1 ⟶ e1) (Y2 : e1 ⟶ f1)
    (Y3 : d2 ⟶ e2) (Y4 : e2 ⟶ f1) :
    x.map m0 ≫ (U ≫ V1 ≫ y'.map Y1) ≫ y'.map Y2 =
      ((x.map m1 ≫ U ≫ y.map M') ≫ V2 ≫ y'.map Y3) ≫ y'.map Y4 := by
  have e : M' = ec := Subsingleton.elim _ _
  rw [Subsingleton.elim m1 m0, e]
  simp only [Category.assoc, y.map_comp]
  rw [reassoc_of% hV]
  simp only [← y'.map_comp]
  rw [Subsingleton.elim (Y1 ≫ Y2) (ed ≫ Y3 ≫ Y4)]

/-- The map `Hom(ε·x, y)_r → Hom(x, y)_{ε+r}` (copowers of persistent objects). -/
def copowTo (ε r s : ℝ) (hs : s = ε + r) {x y : ℝ ⥤ D} (u : (addLeft (-ε) ⋙ x) ⟶ shift r y) :
    x ⟶ shift s y :=
  mk' s (fun q => mapEq x (show q = -ε + (ε + q) by ring) ≫ u.app (ε + q) ≫
      mapEq y (show r + (ε + q) = s + q by rw [hs]; ring)) (by
    intro q q' h
    subst hs
    have hu := u.naturality (homOfLE (add_le_add_right h ε))
    simp only [mapEq, Category.assoc]
    have h1 : x.map (homOfLE h) ≫ x.map (homOfLE (le_of_eq (show q' = -ε + (ε + q') by ring))) =
        x.map (homOfLE (le_of_eq (show q = -ε + (ε + q) by ring))) ≫
          x.map (homOfLE (add_le_add_right (add_le_add_right h ε) (-ε))) := by
      rw [← x.map_comp, ← x.map_comp]; rfl
    have h2 : y.map (homOfLE (add_le_add_right (add_le_add_right h ε) r) ) ≫
          y.map (homOfLE (le_of_eq (show r + (ε + q') = (ε + r) + q' by ring))) =
        y.map (homOfLE (le_of_eq (show r + (ε + q) = (ε + r) + q by ring))) ≫
          y.map (homOfLE (add_le_add le_rfl h)) := by
      rw [← y.map_comp, ← y.map_comp]; rfl
    have hu' : x.map (homOfLE (add_le_add_right (add_le_add_right h ε) (-ε))) ≫ u.app (ε + q') =
        u.app (ε + q) ≫ y.map (homOfLE (add_le_add_right (add_le_add_right h ε) r)) := hu
    erw [← Category.assoc (x.map (homOfLE h)) (x.map _), h1, Category.assoc, Category.assoc,
      ← Category.assoc (x.map (homOfLE (add_le_add_right (add_le_add_right h ε) (-ε)))), hu']
    erw [Category.assoc (u.app (ε + q)), h2]
    rfl)

def copowFrom (ε r s : ℝ) (hs : s = ε + r) {x y : ℝ ⥤ D} (v : x ⟶ shift s y) :
    (addLeft (-ε) ⋙ x) ⟶ shift r y :=
  mk' r (fun q => v.app (-ε + q) ≫ mapEq y (show s + (-ε + q) = r + q by rw [hs]; ring)) (by
    intro q q' h
    subst hs
    have h1 := v.naturality (homOfLE (add_le_add_right h (-ε)))
    erw [← Category.assoc, h1]
    unfold mapEq
    exact aux3 y _ _ _ _ _)

theorem copowTo_app (ε r s : ℝ) (hs : s = ε + r) {x y : ℝ ⥤ D}
    (u : (addLeft (-ε) ⋙ x) ⟶ shift r y) (q : ℝ) :
    (copowTo ε r s hs u).app q = mapEq x (show q = -ε + (ε + q) by ring) ≫ u.app (ε + q) ≫
      mapEq y (show r + (ε + q) = s + q by rw [hs]; ring) := rfl

theorem copow_left_inv (ε r s : ℝ) (hs : s = ε + r) {x y : ℝ ⥤ D}
    (u : (addLeft (-ε) ⋙ x) ⟶ shift r y) :
    copowFrom ε r s hs (copowTo ε r s hs u) = u := by
  subst hs
  apply NatTrans.ext; funext q
  have hn := u.naturality (homOfLE (le_of_eq (show q = ε + (-ε + q) by ring)))
  change ((mapEq x _ ≫ u.app (ε + (-ε + q)) ≫ mapEq y _) ≫ mapEq y _) = u.app q
  have hn' : mapEq x (show -ε + q = -ε + (ε + (-ε + q)) by ring) ≫ u.app (ε + (-ε + q)) =
      u.app q ≫ mapEq y (show r + q = r + (ε + (-ε + q)) by ring) := hn
  erw [Category.assoc (mapEq x _), Category.assoc (u.app (ε + (-ε + q))),
    ← Category.assoc (mapEq x _), hn', Category.assoc, mapEq_comp, mapEq_comp]
  exact comp_Ymap_eq_id y _ _

theorem copow_right_inv (ε r s : ℝ) (hs : s = ε + r) {x y : ℝ ⥤ D} (v : x ⟶ shift s y) :
    copowTo ε r s hs (copowFrom ε r s hs v) = v := by
  subst hs
  apply NatTrans.ext; funext q
  have hn := v.naturality (homOfLE (le_of_eq (show q = -ε + (ε + q) by ring)))
  change mapEq x _ ≫ ((v.app (-ε + (ε + q)) ≫ mapEq y _) ≫ mapEq y _) = v.app q
  have hn' : mapEq x (show q = -ε + (ε + q) by ring) ≫ v.app (-ε + (ε + q)) =
      v.app q ≫ mapEq y (show (ε + r) + q = (ε + r) + (-ε + (ε + q)) by ring) := hn
  erw [Category.assoc (v.app (-ε + (ε + q))), ← Category.assoc (mapEq x _), hn', Category.assoc,
    mapEq_comp, mapEq_comp]
  exact comp_Ymap_eq_id y _ _

end PersistentObjects

open PersistentObjects in
/-- The copowers by representables of `D^ℝ`: `(ε · X)(r) = X(r - ε)`. -/
noncomputable def persistentCopowered :
    @CopoweredByRepresentables (ℝ ⥤ D) _ (persistentLPCat D) where
  copow ε := (Functor.whiskeringLeft ℝ ℝ D).obj (addLeft (-((ε : ℝ≥0) : ℝ)))
  copowIso x y ε r :=
    { toFun := fun u => copowTo ((ε : ℝ≥0) : ℝ) ((r : ℝ≥0) : ℝ) (((ε + r : ℝ≥0)) : ℝ)
        (by push_cast; rfl) u
      invFun := fun v => copowFrom ((ε : ℝ≥0) : ℝ) ((r : ℝ≥0) : ℝ) (((ε + r : ℝ≥0)) : ℝ)
        (by push_cast; rfl) v
      left_inv := fun u => copow_left_inv _ _ _ _ u
      right_inv := fun v => copow_right_inv _ _ _ _ v }
  copowIso_S := by
    intro x y ε r r' h u
    apply NatTrans.ext; funext q
    erw [shiftR_app]
    show mapEq x _ ≫ (shiftR _ u).app (((ε : ℝ≥0) : ℝ) + q) ≫ mapEq y _ = _
    erw [shiftR_app]
    unfold mapEq
    exact aux14 y _ _ _ _ _ _
  copowIso_x := by
    intro x x' y ε r f u
    apply NatTrans.ext; funext q
    erw [copowTo_app (hs := by push_cast; rfl), shiftR_app, compR_app, toZero_app (hr := by simp)]
    erw [shiftR_app, compR_app, toZero_app (hr := by simp), copowTo_app (hs := by push_cast; rfl)]
    have hf := f.naturality (homOfLE (le_of_eq (show q = -((ε : ℝ≥0) : ℝ) + (((ε : ℝ≥0) : ℝ) + q) by ring)))
    have hu := u.naturality (homOfLE (le_of_eq (show (((0 : ℝ≥0)) : ℝ) + (((ε : ℝ≥0) : ℝ) + q) =
      ((ε : ℝ≥0) : ℝ) + ((((0 : ℝ≥0)) : ℝ) + q) by simp)))
    unfold mapEq
    exact aux15 x x' y f _ _ _ _ hu _ _ _ _ _ _ _ _ _ _
  copowIso_y := by
    intro x y y' ε r δ v u
    apply NatTrans.ext; funext q
    erw [copowTo_app (hs := by push_cast; rfl), compR_app]
    erw [shiftR_app, compR_app, copowTo_app (hs := by push_cast; rfl)]
    unfold mapEq
    have hv := v.naturality (homOfLE (le_of_eq (show ((r : ℝ≥0) : ℝ) + (((ε : ℝ≥0) : ℝ) + q) =
      (((ε + r : ℝ≥0)) : ℝ) + q by push_cast; ring)))
    exact aux16 x y y' _ _ _ _ _ hv _ _ _ _ _ _ _

/-- Example 3.2.7 (copowers): `D^ℝ` is copowered by representables, with
`(ε · X)(r) = X(r - ε)`. -/
theorem persistent_copoweredByRepresentables :
    Nonempty (@CopoweredByRepresentables (ℝ ⥤ D) _ (persistentLPCat D)) :=
  ⟨persistentCopowered D⟩

end PersistentObjects

/-! ## Weighted sequential limits in `D^ℝ`

For `D` with sequential limits, `persistentLPCat D` has weighted sequential limits: pointwise,
`l(q) = lim_i x_i(ε̃_i + q)`. (This is the concrete case of Proposition 3.2.15 needed for
Corollary 4.3.2.) -/

section PersistentLimits

open CategoryTheory CategoryTheory.Limits
open scoped NNReal

open LPCat PersistentObjects

attribute [local instance] persistentLPCat

variable {D : Type u} [Category.{v, u} D] [HasLimitsOfShape ℕᵒᵖ D]

namespace PersistentLimits

theorem auxD (Y : ℝ ⥤ D) {P Q : D} {a1 a2 c : ℝ} (A : P ⟶ Y.obj a1) (B : P ⟶ Q)
    (C : Q ⟶ Y.obj c) (m1 : a1 ⟶ a2) (m2 : c ⟶ a2) (back : a2 ⟶ c) (k : a1 ⟶ c)
    (hE : A ≫ Y.map m1 = B ≫ (C ≫ Y.map m2)) : B ≫ C = A ≫ Y.map k := by
  have h1 : B ≫ C = (B ≫ (C ≫ Y.map m2)) ≫ Y.map back := by
    rw [Category.assoc, Category.assoc, ← Y.map_comp, Subsingleton.elim (m2 ≫ back) (𝟙 c)]
    simp
  rw [h1, ← hE, Category.assoc, ← Y.map_comp, Subsingleton.elim (m1 ≫ back) k]

theorem auxA (X Y : ℝ ⥤ D) {P : D} {a1 a2 a3 a4 a5 b1 b2 : ℝ} (A : P ⟶ Y.obj a1)
    (B : P ⟶ X.obj b1) (F1 : X.obj b1 ⟶ Y.obj a2) (F2 : X.obj b2 ⟶ Y.obj a3)
    (e : b1 ⟶ b2) (n1 : a2 ⟶ a3) (m1 : a1 ⟶ a4) (m2 : a2 ⟶ a4) (back : a4 ⟶ a5)
    (hc : A ≫ Y.map m1 = B ≫ (F1 ≫ Y.map m2)) (hnat : X.map e ≫ F2 = F1 ≫ Y.map n1)
    (k : a1 ⟶ a5) (n2 : a3 ⟶ a5) :
    A ≫ Y.map k = (B ≫ X.map e) ≫ (F2 ≫ Y.map n2) := by
  have h1 : A ≫ Y.map k = (A ≫ Y.map m1) ≫ Y.map back := by
    rw [Category.assoc, ← Y.map_comp, Subsingleton.elim (m1 ≫ back) k]
  rw [h1, hc]
  simp only [Category.assoc]
  rw [reassoc_of% hnat]
  simp only [← Y.map_comp, Category.assoc]
  rw [Subsingleton.elim (m2 ≫ back) (n1 ≫ n2)]

theorem aux12 (Y : ℝ ⥤ D) {P A : D} {a1 a2 a3 : ℝ} (u : P ⟶ A) (F : A ⟶ Y.obj a1)
    (m1 : a1 ⟶ a2) (m2 : a2 ⟶ a3) (m3 : a1 ⟶ a3) :
    (u ≫ (F ≫ Y.map m1)) ≫ Y.map m2 = u ≫ (F ≫ Y.map m3) := by
  simp only [Category.assoc, ← Y.map_comp]
  rw [Subsingleton.elim (m1 ≫ m2) m3]

variable (Dg : SeqDiagram (ℝ ⥤ D))

/-- The diagram `i ↦ x_i(ε̃_i + q)` in `D`. -/
noncomputable def Ψ (q : ℝ) : ℕᵒᵖ ⥤ D :=
  Functor.ofOpSequence (X := fun i => (Dg.x i).obj (((tailSum Dg.εs i : ℝ≥0) : ℝ) + q))
    (fun i => (Dg.f i).app (((tailSum Dg.εs (i + 1) : ℝ≥0) : ℝ) + q) ≫
      mapEq (Dg.x i) (show ((Dg.εs i : ℝ≥0) : ℝ) + (((tailSum Dg.εs (i + 1) : ℝ≥0) : ℝ) + q) =
        ((tailSum Dg.εs i : ℝ≥0) : ℝ) + q by
          rw [tailSum_succ Dg.hsum.summable i]; push_cast; ring))

/-- The comparison `Ψ q ⟶ Ψ q'` for `q ≤ q'`. -/
noncomputable def Θ {q q' : ℝ} (h : q ≤ q') : Ψ Dg q ⟶ Ψ Dg q' :=
  NatTrans.ofOpSequence
    (fun n => (Dg.x n).map (homOfLE (add_le_add le_rfl h)))
    (by
      intro n
      have hn := (Dg.f n).naturality (homOfLE (add_le_add le_rfl h :
        ((tailSum Dg.εs (n + 1) : ℝ≥0) : ℝ) + q ≤ ((tailSum Dg.εs (n + 1) : ℝ≥0) : ℝ) + q'))
      simp only [Ψ, Functor.ofOpSequence_map_homOfLE_succ]
      unfold mapEq
      erw [← Category.assoc, hn]
      exact aux3 (Dg.x n) _ _ _ _ _)

theorem Θ_refl (q : ℝ) : Θ Dg (le_refl q) = 𝟙 (Ψ Dg q) := by
  ext ⟨n⟩
  change (Dg.x n).map (homOfLE _) = 𝟙 _
  exact (Dg.x n).map_id _

theorem Θ_trans {q q' q'' : ℝ} (h : q ≤ q') (h' : q' ≤ q'') :
    Θ Dg h ≫ Θ Dg h' = Θ Dg (h.trans h') := by
  ext ⟨n⟩
  change (Dg.x n).map (homOfLE _) ≫ (Dg.x n).map (homOfLE _) = (Dg.x n).map (homOfLE _)
  rw [← (Dg.x n).map_comp]
  rfl

/-- The limit functor `q ↦ lim_i x_i(ε̃_i + q)`. -/
noncomputable def Lfun : ℝ ⥤ D where
  obj q := limit (Ψ Dg q)
  map {q q'} h := limMap (Θ Dg (leOfHom h))
  map_id q := by
    show lim.map (Θ Dg _) = 𝟙 _
    rw [Θ_refl]
    exact lim.map_id _
  map_comp {q q' q''} h h' := by
    show lim.map (Θ Dg _) = lim.map (Θ Dg _) ≫ lim.map (Θ Dg _)
    rw [← lim.map_comp, Θ_trans]

/-- The projections `Lfun ⟶ shift ε̃ᵢ xᵢ`. -/
noncomputable def gL (i : ℕ) : @LPCat.hom _ _ (persistentLPCat D) (Lfun Dg) (Dg.x i)
    (tailSum Dg.εs i) :=
  mk' _ (fun q => limit.π (Ψ Dg q) (Opposite.op i)) (by
    intro q q' h
    exact limMap_π (Θ Dg h) (Opposite.op i))

theorem gL_comm (i : ℕ) : Commutes (gL Dg (i + 1)) (Dg.f i) (gL Dg i) := by
  rw [Commutes_iff _ _ _ (by rw [tailSum_succ Dg.hsum.summable i, add_comm] :
    tailSum Dg.εs i = tailSum Dg.εs (i + 1) + Dg.εs i)]
  apply NatTrans.ext; funext q
  erw [shiftR_app, compR_app]
  have hw := limit.w (Ψ Dg q) (homOfLE (Nat.le_succ i)).op
  simp only [Ψ, Functor.ofOpSequence_map_homOfLE_succ] at hw
  have h2 : (gL Dg i).app q = (gL Dg (i + 1)).app q ≫ ((Dg.f i).app _ ≫ mapEq (Dg.x i) _) :=
    hw.symm
  rw [h2]
  unfold mapEq
  exact aux12 (Dg.x i) _ _ _ _ _

section Univ
variable (l' : ℝ ⥤ D) (γ : ℝ≥0)
  (g' : ∀ i, @LPCat.hom _ _ (persistentLPCat D) l' (Dg.x i) (tailSum Dg.εs i + γ))

/-- The legs `l'(q) → x_i(ε̃_i + (γ + q))`. -/
noncomputable def leg (i : ℕ) (q : ℝ) : l'.obj q ⟶ (Dg.x i).obj (((tailSum Dg.εs i : ℝ≥0) : ℝ) +
    (((γ : ℝ≥0) : ℝ) + q)) :=
  (g' i).app q ≫ mapEq (Dg.x i) (show ((tailSum Dg.εs i + γ : ℝ≥0) : ℝ) + q =
    ((tailSum Dg.εs i : ℝ≥0) : ℝ) + (((γ : ℝ≥0) : ℝ) + q) by push_cast; ring)

variable (hc : ∀ i, Commutes (g' (i + 1)) (Dg.f i) (g' i))

include hc in
theorem leg_cone (n : ℕ) (q : ℝ) :
    leg Dg l' γ g' n q = leg Dg l' γ g' (n + 1) q ≫ (Ψ Dg (((γ : ℝ≥0) : ℝ) + q)).map
      (homOfLE (Nat.le_succ n)).op := by
  have h1 := (Commutes_iff _ _ _ (by rw [tailSum_succ Dg.hsum.summable n]; push_cast; ring :
    (tailSum Dg.εs n + γ : ℝ≥0) = tailSum Dg.εs (n + 1) + γ + Dg.εs n)).1 (hc n)
  have h2 := congrArg (fun t => NatTrans.app t q) h1
  beta_reduce at h2
  erw [shiftR_app, compR_app] at h2
  have hnat := (Dg.f n).naturality (homOfLE (le_of_eq (show
    ((tailSum Dg.εs (n + 1) + γ : ℝ≥0) : ℝ) + q = ((tailSum Dg.εs (n + 1) : ℝ≥0) : ℝ) +
      (((γ : ℝ≥0) : ℝ) + q) by push_cast; ring)))
  have hΨ : (Ψ Dg (((γ : ℝ≥0) : ℝ) + q)).map (homOfLE (Nat.le_succ n)).op =
      (Dg.f n).app (((tailSum Dg.εs (n + 1) : ℝ≥0) : ℝ) + (((γ : ℝ≥0) : ℝ) + q)) ≫
        mapEq (Dg.x n) (show ((Dg.εs n : ℝ≥0) : ℝ) + (((tailSum Dg.εs (n + 1) : ℝ≥0) : ℝ) +
          (((γ : ℝ≥0) : ℝ) + q)) = ((tailSum Dg.εs n : ℝ≥0) : ℝ) + (((γ : ℝ≥0) : ℝ) + q) by
            rw [tailSum_succ Dg.hsum.summable n]; push_cast; ring) := by
    simp [Ψ]
    rfl
  erw [hΨ]
  unfold leg mapEq
  exact auxA (Dg.x (n + 1)) (Dg.x n) _ _ _ _ _ _ _ _
    (homOfLE (le_of_eq (by rw [tailSum_succ Dg.hsum.summable n]; push_cast; ring))) h2 hnat _ _

/-- The cone on `Ψ (γ + q)` with vertex `l' q`. -/
noncomputable def coneAt (hc : ∀ i, Commutes (g' (i + 1)) (Dg.f i) (g' i)) (q : ℝ) : Cone (Ψ Dg (((γ : ℝ≥0) : ℝ) + q)) where
  pt := l'.obj q
  π := NatTrans.ofOpSequence (F := (Functor.const _).obj (l'.obj q))
    (G := Ψ Dg (((γ : ℝ≥0) : ℝ) + q)) (fun n => leg Dg l' γ g' n q) (by
      intro n
      simp only [Functor.const_obj_map]
      exact (Category.id_comp _).trans (leg_cone Dg l' γ g' hc n q))

/-- The mediating morphism `l' ⟶ shift γ L`. -/
noncomputable def uMap (hc : ∀ i, Commutes (g' (i + 1)) (Dg.f i) (g' i)) : @LPCat.hom _ _ (persistentLPCat D) l' (Lfun Dg) γ :=
  mk' _ (fun q => limit.lift (Ψ Dg (((γ : ℝ≥0) : ℝ) + q)) (coneAt Dg l' γ g' hc q)) (by
    intro q q' h
    apply limit.hom_ext
    intro j
    induction j using Opposite.rec with
    | op i =>
    have hl := (g' i).naturality (homOfLE h)
    have h1 : l'.map (homOfLE h) ≫ leg Dg l' γ g' i q' =
        leg Dg l' γ g' i q ≫ (Dg.x i).map (homOfLE (add_le_add le_rfl
          (add_le_add le_rfl h))) := by
      unfold leg mapEq
      erw [← Category.assoc, hl]
      exact aux3 (Dg.x i) _ _ _ _ _
    erw [Category.assoc, Category.assoc, limit.lift_π, limMap_π,
      ← Category.assoc (limit.lift _ _), limit.lift_π]
    exact h1)

theorem uMap_comm (hc : ∀ i, Commutes (g' (i + 1)) (Dg.f i) (g' i)) (i : ℕ) :
    Commutes (uMap Dg l' γ g' hc) (gL Dg i) (g' i) := by
  rw [Commutes_iff _ _ _ (add_comm (tailSum Dg.εs i) γ)]
  apply NatTrans.ext; funext q
  erw [shiftR_app, compR_app]
  erw [← Category.assoc (limit.lift _ _), limit.lift_π]
  show (g' i).app q ≫ _ = leg Dg l' γ g' i q ≫ _
  unfold leg mapEq
  erw [Category.assoc, ← (Dg.x i).map_comp]
  rfl

theorem uMap_unique (hc : ∀ i, Commutes (g' (i + 1)) (Dg.f i) (g' i))
    (u' : @LPCat.hom _ _ (persistentLPCat D) l' (Lfun Dg) γ)
    (hu' : ∀ i, Commutes u' (gL Dg i) (g' i)) : u' = uMap Dg l' γ g' hc := by
  apply NatTrans.ext; funext q
  apply limit.hom_ext
  intro j
  induction j using Opposite.rec with
  | op i =>
  have hu := (Commutes_iff _ _ _ (add_comm (tailSum Dg.εs i) γ)).1 (hu' i)
  have h2 := congrArg (fun t => NatTrans.app t q) hu
  beta_reduce at h2
  erw [shiftR_app, compR_app] at h2
  erw [limit.lift_π]
  show _ = leg Dg l' γ g' i q
  unfold leg mapEq
  exact auxD (Dg.x i) _ _ _ _ _ (homOfLE (le_of_eq (show ((γ + tailSum Dg.εs i : ℝ≥0) : ℝ) + q =
    ((tailSum Dg.εs i : ℝ≥0) : ℝ) + (((γ : ℝ≥0) : ℝ) + q) by push_cast; ring))) _ h2

end Univ

/-- The weighted sequential limit of a diagram in `D^ℝ`, computed pointwise. -/
noncomputable def weightedLimit : WeightedSeqLimit Dg where
  l := Lfun Dg
  g := gL Dg
  comm := gL_comm Dg
  univ l' γ g' hc := ⟨uMap Dg l' γ g' hc, uMap_comm Dg l' γ g' hc,
    fun u' hu' => uMap_unique Dg l' γ g' hc u' hu'⟩

end PersistentLimits

/-- `D^ℝ` has weighted sequential limits when `D` has sequential limits. -/
theorem persistent_hasWeightedSeqLimits :
    HasWeightedSeqLimits (ℝ ⥤ D) := fun Dg => ⟨PersistentLimits.weightedLimit Dg⟩

end PersistentLimits

end ScoccolaPhd
