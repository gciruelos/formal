import Mathlib

/-!
# Chapter 2, §2.1–2.4: rewriting systems, Gröbner bases and monomial algebras

Recollections from Chapter 2 of the thesis (Section 2, "Recollections", Subsections 2.1–2.4),
used in Chapters 3 and 6.

## Contents

* `FreeAlg`: the free algebra `k⟨X⟩`, realized as the monoid algebra of the free monoid `⟨X⟩`,
  so that monomials form its basis and `supp` is the support of the coefficient function.
* Definitions 1–6: rewriting systems, basic reductions and reductions, irreducible elements and
  normal forms, pseudo-reductions and termination, compatible rewriting orderings, the ordering
  `<_Σ`, convergence.
* The algebras `A_Σ = k⟨X | w - f(w)⟩` and `A_Σ⁰ = k⟨X | W⟩` (the monomial algebra of `Σ`).
* §2.2: the rewriting system `xyz ↦ x³ + y³ + z³`, terminating although it comes from no total
  order.

-/

noncomputable section

namespace TamaroffPhd

open MonoidAlgebra Classical

section FreeAlgebra

variable (k : Type) [Field k] (X : Type)

/-- The free associative algebra `k⟨X⟩` (§2.1), realized as the monoid algebra `k[⟨X⟩]` of the
free monoid `⟨X⟩`. Its elements are finite linear combinations of monomials. -/
abbrev FreeAlg := MonoidAlgebra k (FreeMonoid X)

variable {k X}

/-- The monomial `m ∈ ⟨X⟩` as an element of `k⟨X⟩`. -/
noncomputable abbrev mono (m : FreeMonoid X) : FreeAlg k X := MonoidAlgebra.single m 1

/-- `supp(g)`: the monomials appearing in `g` with nonzero coefficient (§2.1). -/
def supp (g : FreeAlg k X) : Finset (FreeMonoid X) := g.coeff.support

/-- The linear map on `k⟨X⟩` determined by its values on monomials. -/
noncomputable def linOnMonomials {M : Type} [AddCommGroup M] [Module k M]
    (v : FreeMonoid X → M) : FreeAlg k X →ₗ[k] M :=
  Finsupp.linearCombination k v ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

/-- `v` is a divisor of `u` in `⟨X⟩`: `u = a v b` (§2.6). -/
def IsDivisor (v u : FreeMonoid X) : Prop := ∃ a b : FreeMonoid X, u = a * v * b

/-- Expansion into monomials, used in the basis and termination proofs in Chapter 2. -/
theorem sum_coeff_mono (g : FreeAlg k X) : ∑ m ∈ supp g, g.coeff m • mono m = g := by
  simpa only [supp, mono, MonoidAlgebra.smul_single, smul_eq_mul, mul_one, Finsupp.sum] using
    MonoidAlgebra.sum_coeff_single g

end FreeAlgebra

section Rewriting

variable (k : Type) [Field k] (X : Type)

/-- **Definition 1 (Rewriting system).** A rewriting system on `k⟨X⟩` is a set `W ⊆ ⟨X⟩` of
monomials with a function `f` on `W` with values in `k⟨X⟩` (only the values on `W` matter).

**Change.** The thesis fixes `X` finite; the definitions here do not need it, and it is assumed
where the statements need it. -/
structure RewritingSystem where
  /-- The monomials that can be rewritten. -/
  W : Set (FreeMonoid X)
  /-- The rewriting rules `w ↦ f(w)`. -/
  f : FreeMonoid X → FreeAlg k X

variable {k X}

namespace RewritingSystem

variable (S : RewritingSystem k X)

/-- The relations `R = {w - f(w) : w ∈ W}`, as a relation on `k⟨X⟩` for `RingQuot`. -/
def rel : FreeAlg k X → FreeAlg k X → Prop := fun a b => ∃ w ∈ S.W, a = mono w ∧ b = S.f w

/-- The algebra `A_Σ = k⟨X | R⟩` presented by the rewriting system (§2.1). -/
abbrev Alg := RingQuot S.rel

/-- The quotient map `k⟨X⟩ → A_Σ`. -/
noncomputable def toAlg : FreeAlg k X →ₐ[k] S.Alg := RingQuot.mkAlgHom k S.rel

/-- The rewriting system `Σ⁰ = (X, W, 0)` (§2.1). -/
def zero : RewritingSystem k X := ⟨S.W, fun _ => 0⟩

/-- The monomial algebra `A_Σ⁰ = k⟨X | W⟩` associated to `Σ` (§2.1). -/
abbrev monomialAlg := S.zero.Alg

/-- **Definition 2 (Basic reduction).** The basic reduction associated to `(a, w, b)` with
`w ∈ W`: the linear endomorphism of `k⟨X⟩` sending `awb` to `a f(w) b` and fixing every other
monomial. -/
noncomputable def basicReduction (a w b : FreeMonoid X) : FreeAlg k X →ₗ[k] FreeAlg k X :=
  linOnMonomials fun m => if m = a * w * b then mono a * S.f w * mono b else mono m

/-- The basic reductions of `Σ`, as a set of endomorphisms. -/
def basicReductions : Set (FreeAlg k X →ₗ[k] FreeAlg k X) :=
  {ρ | ∃ a w b, w ∈ S.W ∧ ρ = S.basicReduction a w b}

/-- **Definition 2 (Reduction).** A finite sequence of basic reductions, composed in the given
order (the first one applied first). -/
noncomputable def reduction (ρs : List (FreeAlg k X →ₗ[k] FreeAlg k X)) :
    FreeAlg k X →ₗ[k] FreeAlg k X :=
  ρs.foldl (fun acc ρ => ρ ∘ₗ acc) LinearMap.id

/-- A list of basic reductions of `Σ`. -/
def IsReductionList (ρs : List (FreeAlg k X →ₗ[k] FreeAlg k X)) : Prop :=
  ∀ ρ ∈ ρs, ρ ∈ S.basicReductions

/-- **Definition 3 (Irreducible).** `g` is irreducible if every basic reduction fixes it. -/
def IsIrreducible (g : FreeAlg k X) : Prop := ∀ ρ ∈ S.basicReductions, ρ g = g

/-- **Definition 3 (Normal form).** An irreducible element with the same coset in `A_Σ`. -/
def IsNormalForm (g gbar : FreeAlg k X) : Prop := S.IsIrreducible gbar ∧ S.toAlg gbar = S.toAlg g

/-- **Definition 4 (Reduction finite).** `g` is reduction finite if for every pseudo-reduction
`(ρ₁, ρ₂, …)` (an infinite sequence of basic reductions) the sequence
`ρ₁ g, ρ₂ ρ₁ g, …` is eventually constant. -/
def IsReductionFinite (g : FreeAlg k X) : Prop :=
  ∀ ρ : ℕ → FreeAlg k X →ₗ[k] FreeAlg k X, (∀ n, ρ n ∈ S.basicReductions) →
    ∃ N, ∀ n ≥ N, reduction ((List.range (n + 1)).map ρ) g =
      reduction ((List.range (N + 1)).map ρ) g

/-- **Definition 4 (Terminating).** All elements of `k⟨X⟩` are reduction finite. -/
def IsTerminating : Prop := ∀ g, S.IsReductionFinite g

/-- **Definition 5 (Compatible rewriting ordering).** A partial order `le` on `⟨X⟩` that is
multiplicative, well-founded, and such that every monomial of `f(w)` is smaller than `w`. -/
structure IsCompatibleOrdering (le : FreeMonoid X → FreeMonoid X → Prop) : Prop where
  /-- `le` is a partial order. -/
  isPartialOrder : IsPartialOrder (FreeMonoid X) le
  /-- (1) multiplicativity. -/
  mul : ∀ m m' a b, le m m' ∧ m ≠ m' → le (a * m * b) (a * m' * b) ∧ a * m * b ≠ a * m' * b
  /-- (2) well-ordering: every nonempty set of monomials has a minimal element. -/
  wf : WellFounded fun m m' => le m m' ∧ m ≠ m'
  /-- (3) compatibility with `Σ`. -/
  compat : ∀ w ∈ S.W, ∀ w' ∈ supp (S.f w), le w' w ∧ w' ≠ w

/-- The one-step relation generating `<_Σ`: `a w' b` is below `a w b` when `w ∈ W` and
`w' ∈ supp(f(w))`. -/
def stepLT (m m' : FreeMonoid X) : Prop :=
  ∃ a b w w', w ∈ S.W ∧ w' ∈ supp (S.f w) ∧ m = a * w' * b ∧ m' = a * w * b

/-- The relation `<_Σ` (§2.1): the smallest transitive multiplicative relation compatible with
`Σ`. -/
def lt : FreeMonoid X → FreeMonoid X → Prop := Relation.TransGen S.stepLT

/-- **Definition 6 (Convergent).** `Σ` is terminating and every element has exactly one normal
form. -/
def IsConvergent : Prop := S.IsTerminating ∧ ∀ g, ∃! gbar, S.IsNormalForm g gbar

/-- Irreducible monomials: those not divisible by any element of `W` (§2.1). -/
def IrreducibleMonomials : Set (FreeMonoid X) := {m | ∀ w ∈ S.W, ¬ IsDivisor w m}

/-- Effect of a basic reduction on an arbitrary polynomial, used in the convergence
criterion and the terminating example of Chapter 2. -/
theorem basicReduction_sub : ∀ (a w b : FreeMonoid X) (g : FreeAlg k X),
      S.basicReduction a w b g - g =
        g.coeff (a * w * b) • (mono a * S.f w * mono b - mono (a * w * b)) := by
  intro a w b g
  induction g using MonoidAlgebra.induction_linear with
  | zero => simp
  | add g₁ g₂ h₁ h₂ =>
    simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul]
    rw [← h₁, ← h₂]
    abel
  | single m c =>
    have hs : (MonoidAlgebra.single m c : FreeAlg k X) = c • mono m := by
      simp [mono, MonoidAlgebra.smul_single]
    rw [hs, map_smul]
    simp only [basicReduction, linOnMonomials, LinearMap.comp_apply,
      MonoidAlgebra.coeffLinearEquiv_apply, mono, Finsupp.linearCombination_single]
    by_cases hm : m = a * w * b
    · subst hm
      simp [MonoidAlgebra.coeff_single_apply, smul_sub, MonoidAlgebra.smul_single]
    · have hne' : a * w * b ≠ m := Ne.symm hm
      simp [hm, hne', MonoidAlgebra.coeff_single_apply]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **§2.1.** Irreducible monomials form a basis of the monomial algebra `A_Σ⁰`: their images
are linearly independent and span. -/
theorem irreducibleMonomials_basis :
    LinearIndependent k (fun m : S.IrreducibleMonomials => S.zero.toAlg (mono (m : FreeMonoid X)))
      ∧ Submodule.span k (Set.range fun m : S.IrreducibleMonomials =>
          S.zero.toAlg (mono (m : FreeMonoid X))) = ⊤ := by
  let π : FreeAlg k X →ₗ[k] FreeAlg k X :=
    linOnMonomials fun m => if m ∈ S.IrreducibleMonomials then mono m else 0
  have hπ_mono_irr : ∀ m ∈ S.IrreducibleMonomials, π (mono m) = mono m := by
    intro m hm
    simp [π, linOnMonomials, mono, hm]
  have hπ_mono_nirr : ∀ m, m ∉ S.IrreducibleMonomials → π (mono m) = 0 := by
    intro m hm
    simp [π, linOnMonomials, mono, hm]
  have hπ_div : ∀ a w b : FreeMonoid X, w ∈ S.W → π (mono a * mono w * mono b) = 0 := by
    intro a w b hw
    rw [show mono a * mono w * mono b = (mono (a * w * b) : FreeAlg k X) by
      simp [mono, MonoidAlgebra.single_mul_single]]
    apply hπ_mono_nirr
    intro h
    exact h w hw ⟨a, b, rfl⟩
  have hπ_mul_w : ∀ x y : FreeAlg k X, ∀ w ∈ S.W, π (x * mono w * y) = 0 := by
    intro x y w hw
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x₁ x₂ hx₁ hx₂ => simp [add_mul, map_add, hx₁, hx₂]
    | single a c =>
      have ha : (MonoidAlgebra.single a c : FreeAlg k X) = c • mono a := by
        simp [mono, MonoidAlgebra.smul_single]
      rw [ha]
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ => simp only [mul_add, map_add, hy₁, hy₂, add_zero]
      | single b d =>
        have hb : (MonoidAlgebra.single b d : FreeAlg k X) = d • mono b := by
          simp [mono, MonoidAlgebra.smul_single]
        rw [hb, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, map_smul, map_smul,
          hπ_div a w b hw, smul_zero, smul_zero]
  have hπ_rel_ctx : ∀ a b, RingQuot.Rel S.zero.rel a b → ∀ x y, π (x * a * y) = π (x * b * y) := by
    intro a b hab
    induction hab with
    | of hr =>
      intro x y
      obtain ⟨w, hw, rfl, rfl⟩ := hr
      change π (x * mono w * y) = π (x * 0 * y)
      rw [hπ_mul_w x y w hw]
      simp
    | add_left _ ih =>
      intro x y
      simp only [mul_add, add_mul, map_add, ih x y]
    | @mul_left a b c _ ih =>
      intro x y
      simpa only [mul_assoc] using ih x (c * y)
    | @mul_right a b c _ ih =>
      intro x y
      simpa only [mul_assoc] using ih (x * a) y
  have hπ_rel : ∀ a b, Relation.EqvGen (RingQuot.Rel S.zero.rel) a b → π a = π b := by
    intro a b hab
    induction hab with
    | rel x y h => simpa only [one_mul, mul_one] using hπ_rel_ctx x y h 1 1
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  constructor
  · rw [linearIndependent_iff']
    intro s g hg m hm
    have h0 : S.zero.toAlg (∑ i ∈ s, g i • mono (i : FreeMonoid X)) = S.zero.toAlg 0 := by
      simpa only [map_sum, map_smul, map_zero] using hg
    have hEq : Relation.EqvGen (RingQuot.Rel S.zero.rel)
        (∑ i ∈ s, g i • mono (i : FreeMonoid X)) 0 := by
      have e' : RingQuot.mkRingHom S.zero.rel (∑ i ∈ s, g i • mono (i : FreeMonoid X)) =
          RingQuot.mkRingHom S.zero.rel 0 := by
        rw [← RingQuot.mkAlgHom_coe k S.zero.rel]
        exact h0
      simp only [RingQuot.mkRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] at e'
      exact Quot.eqvGen_exact (RingQuot.mk.inj e')
    have hπ0 := hπ_rel _ _ hEq
    rw [map_zero, map_sum] at hπ0
    have hsum : (∑ i ∈ s, g i • mono (i : FreeMonoid X)) = (0 : FreeAlg k X) := by
      simp only [map_smul] at hπ0
      convert hπ0 using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hπ_mono_irr (i : FreeMonoid X) i.2]
    have hcoeff := congrArg (fun x : FreeAlg k X => x.coeff (m : FreeMonoid X)) hsum
    simp only [MonoidAlgebra.coeff_sum, Finset.sum_apply', MonoidAlgebra.coeff_smul,
      smul_eq_mul, mono, MonoidAlgebra.coeff_single_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
    rw [Finset.sum_eq_single m] at hcoeff
    · simpa using hcoeff
    · intro b _ hbm
      simp [Subtype.coe_injective.ne hbm]
    · intro hms; exact False.elim (hms hm)
  · rw [eq_top_iff]
    intro x hx
    clear hx
    obtain ⟨y, rfl⟩ := RingQuot.mkAlgHom_surjective k S.zero.rel x
    change S.zero.toAlg y ∈ _
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ => rw [map_add]; exact add_mem hy₁ hy₂
    | single m c =>
      have hs : (MonoidAlgebra.single m c : FreeAlg k X) = c • mono m := by
        simp [mono, MonoidAlgebra.smul_single]
      rw [hs, map_smul]
      apply Submodule.smul_mem
      by_cases hm : m ∈ S.IrreducibleMonomials
      · exact Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
      · simp only [IrreducibleMonomials, Set.mem_setOf_eq, not_forall, not_not] at hm
        obtain ⟨w, hw, a, b, rfl⟩ := hm
        have hw0 : S.zero.toAlg (mono w) = 0 := by
          have := RingQuot.mkAlgHom_rel k (s := S.zero.rel)
            (show S.zero.rel (mono w) 0 from ⟨w, hw, rfl, rfl⟩)
          change (RingQuot.mkAlgHom k S.zero.rel) (mono w) = 0
          exact this.trans (map_zero _)
        have hm0 : S.zero.toAlg (mono (a * w * b)) = 0 := by
          rw [show (mono (a * w * b) : FreeAlg k X) = mono a * mono w * mono b by
            simp [mono, MonoidAlgebra.single_mul_single]]
          simp only [map_mul, hw0, zero_mul, mul_zero]
        rw [hm0]
        exact zero_mem _

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **§2.3.** A terminating `Σ` is convergent if and only if the images of the irreducible
monomials in `A_Σ` are linearly independent (equivalently, the map `A_Σ⁰ → A_Σ` sending each
irreducible monomial to its coset is a linear isomorphism).

**Gap (missing hypothesis).** Without `∀ w ∈ S.W, S.f w ≠ mono w`, a rule `w ↦ w` makes
`basicReduction a w b = id`, so `w` is irreducible even though `w ∉ IrreducibleMonomials`.
Counterexample: `X = {x, y}`, `W = {x², xy, yx}`, `f(x²) = x²`, `f(xy) = x²`, `f(yx) = x`. Here `Σ`
is terminating (`y`-count strictly decreases) and `IrreducibleMonomials = {1, x, y, y², …}` is
linearly independent in `A_Σ = k⟨x, y⟩/(xy - x², yx - x)`, yet `xyx` has two distinct normal
forms `x²` and `x³`. We add `hne : ∀ w ∈ S.W, S.f w ≠ mono w` (implied by `<_Σ` being
well-founded). -/
theorem isConvergent_iff_linearIndependent (hS : S.IsTerminating)
    (hne : ∀ w ∈ S.W, S.f w ≠ mono w) :
    S.IsConvergent ↔
      LinearIndependent k (fun m : S.IrreducibleMonomials => S.toAlg (mono (m : FreeMonoid X))) := by
  have hbasic_diff := S.basicReduction_sub
  have hmul_inj : ∀ (a b : FreeMonoid X) (x y : FreeAlg k X),
      mono a * x * mono b = mono a * y * mono b → x = y := by
    intro a b x y hxy
    ext u
    have hc := congrArg (fun z : FreeAlg k X => z.coeff (a * u * b)) hxy
    have hcoeff : ∀ z : FreeAlg k X, (mono a * z * mono b).coeff (a * u * b) = z.coeff u := by
      intro z
      induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add z₁ z₂ h₁ h₂ => simp [mul_add, add_mul, h₁, h₂]
      | single v d =>
        have hs : (MonoidAlgebra.single v d : FreeAlg k X) = d • mono v := by
          simp [mono, MonoidAlgebra.smul_single]
        rw [hs, mul_smul_comm, smul_mul_assoc,
          show (mono a * mono v * mono b : FreeAlg k X) = mono (a * v * b) by
            simp [mono, MonoidAlgebra.single_mul_single]]
        simp only [MonoidAlgebra.coeff_smul_apply, mono, MonoidAlgebra.coeff_single_apply, mul_right_cancel_iff, mul_left_cancel_iff]
    rwa [hcoeff x, hcoeff y] at hc
  have hIrr : ∀ g : FreeAlg k X, S.IsIrreducible g ↔ ↑(supp g) ⊆ S.IrreducibleMonomials := by
    intro g
    constructor
    · intro hg m hm w hw ⟨a, b, heq⟩
      subst m
      have hred := hg (S.basicReduction a w b) ⟨a, w, b, hw, rfl⟩
      have h0 := hbasic_diff a w b g
      rw [hred, sub_self] at h0
      have hc0 : g.coeff (a * w * b) ≠ 0 := by simpa [supp] using hm
      rcases smul_eq_zero.1 h0.symm with hc | hf
      · exact hc0 hc
      · apply hne w hw
        apply hmul_inj a b
        rw [show mono a * mono w * mono b = (mono (a * w * b) : FreeAlg k X) by
          simp [mono, MonoidAlgebra.single_mul_single]]
        exact sub_eq_zero.1 hf
    · intro hsub ρ hρ
      obtain ⟨a, w, b, hw, rfl⟩ := hρ
      have hna : a * w * b ∉ supp g := fun h => hsub h w hw ⟨a, b, rfl⟩
      have hc0 : g.coeff (a * w * b) = 0 := by simpa [supp] using hna
      have h0 := hbasic_diff a w b g
      rw [hc0, zero_smul] at h0
      exact sub_eq_zero.1 h0
  have htoAlg_basic : ∀ ρ ∈ S.basicReductions, ∀ g, S.toAlg (ρ g) = S.toAlg g := by
    rintro ρ ⟨a, w, b, hw, rfl⟩ g
    have hw_eq : S.toAlg (mono w) = S.toAlg (S.f w) := by
      have := RingQuot.mkAlgHom_rel k (s := S.rel)
        (show S.rel (mono w) (S.f w) from ⟨w, hw, rfl, rfl⟩)
      simpa [toAlg] using this
    have hdiff := congrArg S.toAlg (hbasic_diff a w b g)
    rw [map_sub, map_smul, map_sub,
      show (mono (a * w * b) : FreeAlg k X) = mono a * mono w * mono b by
        simp [mono, MonoidAlgebra.single_mul_single],
      map_mul S.toAlg, map_mul S.toAlg, map_mul S.toAlg, map_mul S.toAlg, hw_eq, sub_self, smul_zero] at hdiff
    exact sub_eq_zero.1 hdiff
  constructor
  · rintro ⟨-, huniq⟩
    rw [linearIndependent_iff']
    intro s c hc m hm
    let g : FreeAlg k X := ∑ i ∈ s, c i • mono (i : FreeMonoid X)
    have hgsupp : ↑(supp g) ⊆ S.IrreducibleMonomials := by
      intro x hx
      have hxs : x ∈ (s.image (fun i : S.IrreducibleMonomials => (i : FreeMonoid X))) := by
        by_contra hnx
        have hx0 : g.coeff x = 0 := by
          simp only [g, Finset.sum_apply, MonoidAlgebra.coeff_sum, Finset.sum_apply', MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
            smul_eq_mul, mono, MonoidAlgebra.coeff_single_apply]
          apply Finset.sum_eq_zero
          intro i hi
          have hne_i : (i : FreeMonoid X) ≠ x := fun h => hnx (Finset.mem_image.2 ⟨i, hi, h⟩)
          simp [hne_i]
        exact (by simpa [supp] using hx : g.coeff x ≠ 0) hx0
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hxs
      exact i.2
    have hgirr : S.IsIrreducible g := (hIrr g).2 hgsupp
    have hg0 : S.toAlg g = S.toAlg 0 := by
      simpa only [g, map_sum, map_smul, map_zero] using hc
    have h0irr : S.IsIrreducible 0 := fun ρ _ => map_zero ρ
    have hg_eq_0 : g = 0 := (huniq g).unique ⟨hgirr, rfl⟩ ⟨h0irr, hg0.symm⟩
    have hcoeff := congrArg (fun z : FreeAlg k X => z.coeff (m : FreeMonoid X)) hg_eq_0
    simp only [g, Finset.sum_apply, MonoidAlgebra.coeff_sum, Finset.sum_apply', MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      smul_eq_mul, mono, MonoidAlgebra.coeff_single_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
    rw [Finset.sum_eq_single m] at hcoeff
    · simpa using hcoeff
    · intro b _ hbm
      simp [Subtype.coe_injective.ne hbm]
    · intro hms; exact False.elim (hms hm)
  · intro hli
    refine ⟨hS, fun g => ?_⟩
    have hex : ∃ gbar, S.IsNormalForm g gbar := by
      by_contra hnex
      push Not at hnex
      have hstep : ∀ h, S.toAlg h = S.toAlg g → ∃ ρ ∈ S.basicReductions, ρ h ≠ h := by
        intro h hh
        have hnirr : ¬ S.IsIrreducible h := fun hi => hnex h ⟨hi, hh⟩
        simpa [IsIrreducible] using hnirr
      let seq : ℕ → Σ' (h : FreeAlg k X), S.toAlg h = S.toAlg g :=
        Nat.rec ⟨g, rfl⟩ fun _ ⟨h, hh⟩ =>
          let ρ := (hstep h hh).choose
          have hρ := (hstep h hh).choose_spec.1
          ⟨ρ h, (htoAlg_basic ρ hρ h).trans hh⟩
      let ρ : ℕ → FreeAlg k X →ₗ[k] FreeAlg k X := fun n =>
        (hstep (seq n).1 (seq n).2).choose
      have hρ_mem : ∀ n, ρ n ∈ S.basicReductions := fun n =>
        (hstep (seq n).1 (seq n).2).choose_spec.1
      have hρ_ne : ∀ n, ρ n (seq n).1 ≠ (seq n).1 := fun n =>
        (hstep (seq n).1 (seq n).2).choose_spec.2
      have hred_eq : ∀ n, reduction ((List.range n).map ρ) g = (seq n).1 := by
        intro n
        induction n with
        | zero => simp [reduction, seq]
        | succ n ih =>
          rw [List.range_succ, List.map_append, reduction, List.foldl_append]
          simp [reduction] at ih
          simp [ih, ρ, seq]
      obtain ⟨N, hN⟩ := hS g ρ hρ_mem
      have hN1 := hN (N + 1) (Nat.le_succ N)
      rw [hred_eq (N + 2), hred_eq (N + 1)] at hN1
      exact hρ_ne (N + 1) hN1
    obtain ⟨gbar, hgbar⟩ := hex
    refine ⟨gbar, hgbar, fun g' hg' => ?_⟩
    have hg1 : ↑(supp (g' - gbar)) ⊆ S.IrreducibleMonomials := by
      intro m hm
      have hm' : m ∈ supp g' ∨ m ∈ supp gbar := by
        by_contra h
        push Not at h
        have h1 : g'.coeff m = 0 := by simpa [supp] using h.1
        have h2 : gbar.coeff m = 0 := by simpa [supp] using h.2
        have : (g' - gbar).coeff m = 0 := by simp [h1, h2]
        exact (by simpa [supp] using hm : (g' - gbar).coeff m ≠ 0) this
      rcases hm' with h1 | h2
      · exact (hIrr g').1 hg'.1 h1
      · exact (hIrr gbar).1 hgbar.1 h2
    have hdiff0 : S.toAlg (g' - gbar) = 0 := by
      rw [map_sub, hg'.2, hgbar.2, sub_self]
    have hsum : ∑ m ∈ (supp (g' - gbar)).attach,
        (g' - gbar).coeff m.1 • S.toAlg (mono m.1) = 0 := by
      rw [Finset.sum_attach (supp (g' - gbar))
        (fun m => (g' - gbar).coeff m • S.toAlg (mono m))]
      simpa only [map_sum, map_smul] using
        (congrArg S.toAlg (sum_coeff_mono (g' - gbar))).trans hdiff0
    let s : Finset S.IrreducibleMonomials :=
      (supp (g' - gbar)).attach.image fun m => ⟨m.1, hg1 m.2⟩
    have hsum' : ∑ m ∈ s, (g' - gbar).coeff (m : FreeMonoid X) •
        S.toAlg (mono (m : FreeMonoid X)) = 0 := by
      dsimp only [s]
      rw [Finset.sum_image]
      · exact hsum
      · intro a _ b _ hab
        apply Subtype.ext
        exact congrArg (fun z : S.IrreducibleMonomials => (z : FreeMonoid X)) hab
    have hcoeff0 := (linearIndependent_iff'.1 hli) s (fun m => (g' - gbar).coeff m.1) hsum'
    apply sub_eq_zero.1
    ext m
    by_cases hm : m ∈ supp (g' - gbar)
    · have hms : (⟨m, hg1 hm⟩ : S.IrreducibleMonomials) ∈ s :=
        Finset.mem_image.2 ⟨⟨m, hm⟩, Finset.mem_attach _ _, rfl⟩
      simpa using hcoeff0 ⟨m, hg1 hm⟩ hms
    · simpa [supp] using hm

end RewritingSystem

/-- **§2.2.** A rewriting system is a Gröbner basis if some total order satisfies the three
conditions of Definition 5. -/
def RewritingSystem.IsGroebner (S : RewritingSystem k X) : Prop :=
  ∃ le : FreeMonoid X → FreeMonoid X → Prop, S.IsCompatibleOrdering le ∧ ∀ m m', le m m' ∨ le m' m

end Rewriting

section Example

/-- The three variables of the example of §2.2. -/
inductive XYZ | x | y | z
  deriving DecidableEq

variable (k : Type) [Field k]

/-- **§2.2 (example).** The rewriting system on `k⟨x, y, z⟩` with the single rule
`xyz ↦ x³ + y³ + z³`. -/
noncomputable def xyzSystem : RewritingSystem k XYZ where
  W := {FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z}
  f _ := mono (FreeMonoid.of .x ^ 3) + mono (FreeMonoid.of .y ^ 3) + mono (FreeMonoid.of .z ^ 3)

/-- Bounding the weight of the three replacement terms in the termination proof of §2.2. -/
private lemma sum_insert_weight_le {A : Type*} [DecidableEq A] (s : Finset A)
    (f : A → ℕ) (a : A) : ∑ x ∈ insert a s, f x ≤ f a + ∑ x ∈ s, f x := by
  by_cases ha : a ∈ s
  · rw [Finset.insert_eq_of_mem ha]
    omega
  · rw [Finset.sum_insert ha]

/-- A union can only remove duplicate weights, used in the termination proof of §2.2. -/
private lemma sum_union_weight_le {A : Type*} [DecidableEq A] (s t : Finset A)
    (f : A → ℕ) : ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have heq := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  omega

private def countXYZ : List XYZ → ℕ
  | [] => 0
  | .x :: .y :: .z :: rest => 1 + countXYZ (.y :: .z :: rest)
  | _ :: rest => countXYZ rest

private def countY (l : List XYZ) : ℕ := l.count .y

private def phiXYZ (m : FreeMonoid XYZ) : ℕ := 3 * countXYZ m.toList + countY m.toList

private lemma countXYZ_le_cons (a : XYZ) (l : List XYZ) : countXYZ (a :: l) ≤ 1 + countXYZ l := by
  cases a with
  | x =>
    cases l with
    | nil => simp [countXYZ]
    | cons b l' =>
      cases b with
      | x => simp [countXYZ]
      | y =>
        cases l' with
        | nil => simp [countXYZ]
        | cons c l'' =>
          cases c <;> simp [countXYZ] <;> omega
      | z => simp [countXYZ]
  | y => simp [countXYZ]
  | z => simp [countXYZ]

private lemma countXYZ_append_xyz (l₁ l₂ : List XYZ) :
    countXYZ (l₁ ++ [.x, .y, .z] ++ l₂) = countXYZ l₁ + 1 + countXYZ l₂ := by
  have hyz : countXYZ (.y :: .z :: l₂) = countXYZ l₂ := by simp [countXYZ]
  induction l₁ with
  | nil => simp [countXYZ, hyz]
  | cons a l₁ ih =>
    cases a with
    | x =>
      cases l₁ with
      | nil => simp [countXYZ, hyz]
      | cons b l₁' =>
        cases b with
        | x => simp [countXYZ] at ih ⊢ <;> omega
        | y =>
          cases l₁' with
          | nil => simp [countXYZ, hyz]
          | cons c l₁'' =>
            cases c <;> simp [countXYZ] at ih ⊢ <;> omega
        | z => simp [countXYZ] at ih ⊢ <;> omega
    | y => simp [countXYZ] at ih ⊢ <;> omega
    | z => simp [countXYZ] at ih ⊢ <;> omega

private lemma countXYZ_append_cube (c : XYZ) (l₁ l₂ : List XYZ) :
    countXYZ (l₁ ++ [c, c, c] ++ l₂) ≤
      countXYZ l₁ + (if c = .y then 0 else 1) + countXYZ l₂ := by
  have h1 := countXYZ_le_cons .x l₂
  suffices h : ∀ n (l₁ : List XYZ), l₁.length = n →
      countXYZ (l₁ ++ [c, c, c] ++ l₂) ≤
        countXYZ l₁ + (if c = .y then 0 else 1) + countXYZ l₂ from h l₁.length l₁ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro l₁ hn
    rcases l₁ with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · cases c <;> simp [countXYZ] <;> omega
    · cases a <;> cases c <;> simp [countXYZ] <;> omega
    · cases a <;> cases b <;> cases c <;> simp [countXYZ] <;> omega
    · have ih1 := ih (rest.length + 2) (by simp only [List.length_cons] at hn; omega) (b :: d :: rest) rfl
      have ih2 := ih (rest.length + 1) (by simp only [List.length_cons] at hn; omega) (d :: rest) rfl
      cases a with
      | x =>
        cases b with
        | x => simp [countXYZ] at ih1 ⊢; exact ih1
        | y =>
          cases d with
          | x => simp [countXYZ] at ih2 ⊢; exact ih2
          | y => simp [countXYZ] at ih2 ⊢; exact ih2
          | z =>
            simp only [List.cons_append, countXYZ] at ih1 ⊢
            omega
        | z => simp [countXYZ] at ih1 ⊢; exact ih1
      | y => simp [countXYZ] at ih1 ⊢; exact ih1
      | z => simp [countXYZ] at ih1 ⊢; exact ih1

private lemma phiXYZ_cube_lt (a b : FreeMonoid XYZ) (c : XYZ) :
    phiXYZ (a * FreeMonoid.of c ^ 3 * b) <
      phiXYZ (a * (FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z) * b) := by
  have htoList_xyz :
      (a * (FreeMonoid.of XYZ.x * FreeMonoid.of XYZ.y * FreeMonoid.of XYZ.z) * b).toList =
        a.toList ++ [.x, .y, .z] ++ b.toList := by
    simp [FreeMonoid.toList_mul, List.append_assoc]
  have htoList_cube :
      (a * FreeMonoid.of c ^ 3 * b).toList = a.toList ++ [c, c, c] ++ b.toList := by
    simp [FreeMonoid.toList_mul, pow_succ, List.append_assoc]
  have hA := countXYZ_append_cube c a.toList b.toList
  have hAxyz := countXYZ_append_xyz a.toList b.toList
  have hB : countY (a.toList ++ [c, c, c] ++ b.toList) =
      countY a.toList + (if c = .y then 3 else 0) + countY b.toList := by
    simp [countY, List.count_append]
    cases c <;> simp <;> omega
  have hBxyz : countY (a.toList ++ [.x, .y, .z] ++ b.toList) =
      countY a.toList + 1 + countY b.toList := by
    simp [countY, List.count_append]
    omega
  simp only [phiXYZ, htoList_cube, htoList_xyz, hAxyz, hB, hBxyz]
  cases c <;> simp at hA ⊢ <;> omega

private lemma pow4_lt_of_lt (p x y z : ℕ) (hx : x < p) (hy : y < p) (hz : z < p) :
    4 ^ x + (4 ^ y + 4 ^ z) < 4 ^ p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have h1 : 4 ^ x ≤ 4 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 4 ^ y ≤ 4 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 4 ^ z ≤ 4 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ^ (q + 1) = 4 * 4 ^ q := by ring
  have hp : 0 < 4 ^ q := by positivity
  omega

/-- The three replacement monomials have less combined weight than the removed monomial;
this extends the source’s Φ decrease to polynomials in the termination proof of §2.2. -/
private lemma xyz_cubes_weight_lt (a b : FreeMonoid XYZ) :
    (∑ m ∈ ({a * FreeMonoid.of .x ^ 3 * b, a * FreeMonoid.of .y ^ 3 * b,
      a * FreeMonoid.of .z ^ 3 * b} : Finset (FreeMonoid XYZ)), 4 ^ phiXYZ m) <
      4 ^ phiXYZ (a * (FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z) * b) := by
  have hsum : (∑ m ∈ ({a * FreeMonoid.of .x ^ 3 * b, a * FreeMonoid.of .y ^ 3 * b,
      a * FreeMonoid.of .z ^ 3 * b} : Finset (FreeMonoid XYZ)), 4 ^ phiXYZ m) ≤
      4 ^ phiXYZ (a * FreeMonoid.of .x ^ 3 * b) +
        (4 ^ phiXYZ (a * FreeMonoid.of .y ^ 3 * b) +
          4 ^ phiXYZ (a * FreeMonoid.of .z ^ 3 * b)) := by
    have h₁ := sum_insert_weight_le
      {a * FreeMonoid.of .y ^ 3 * b, a * FreeMonoid.of .z ^ 3 * b}
      (fun m => 4 ^ phiXYZ m) (a * FreeMonoid.of .x ^ 3 * b)
    have h₂ := sum_insert_weight_le
      {a * FreeMonoid.of .z ^ 3 * b}
      (fun m => 4 ^ phiXYZ m) (a * FreeMonoid.of .y ^ 3 * b)
    simpa only [Finset.sum_singleton] using
      h₁.trans (add_le_add le_rfl h₂)
  exact hsum.trans_lt (pow4_lt_of_lt _ _ _ _ (phiXYZ_cube_lt a b .x)
    (phiXYZ_cube_lt a b .y) (phiXYZ_cube_lt a b .z))

/-- Weight of a polynomial: sum of `4 ^ Φ` over its support. -/
private def xyzWeight {k : Type} [Field k] (h : FreeAlg k XYZ) : ℕ := ∑ m ∈ supp h, 4 ^ phiXYZ m

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **§2.2.** The rewriting system `xyz ↦ x³ + y³ + z³` is terminating: `Φ(m) = 3A(m) + B(m)`
strictly decreases, where `A(m)` counts the divisors `xyz` of `m` and `B(m)` the letters `y`. -/
theorem xyzSystem_isTerminating : (xyzSystem k).IsTerminating := by
  intro g ρ hρ
  have hstep : ∀ (r : FreeAlg k XYZ →ₗ[k] FreeAlg k XYZ), r ∈ (xyzSystem k).basicReductions →
      ∀ h, r h ≠ h → xyzWeight (r h) < xyzWeight h := by
    rintro r ⟨a, w, b, hw, rfl⟩ h hne
    simp only [xyzSystem, Set.mem_singleton_iff] at hw
    subst hw
    let m₀ : FreeMonoid XYZ := a * (FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z) * b
    have hm₀ : m₀ ∈ supp h := by
      by_contra hnm
      have hc0 : h.coeff m₀ = 0 := by simpa [supp] using hnm
      apply hne
      have hd := (xyzSystem k).basicReduction_sub a
        (FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z) b h
      change _ - h = h.coeff m₀ • _ at hd
      rw [hc0, zero_smul] at hd
      exact sub_eq_zero.mp hd
    let rhs : FreeAlg k XYZ :=
      mono a * (xyzSystem k).f (FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z) * mono b
    have hdiff : (xyzSystem k).basicReduction a
        (FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z) b h =
        h - h.coeff m₀ • mono m₀ + h.coeff m₀ • rhs := by
      have hd := (xyzSystem k).basicReduction_sub a
        (FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z) b h
      change _ - h = h.coeff m₀ • (rhs - mono m₀) at hd
      rw [sub_eq_iff_eq_add, smul_sub] at hd
      rw [hd]
      abel
    let S_cubes : Finset (FreeMonoid XYZ) :=
      {a * FreeMonoid.of .x ^ 3 * b, a * FreeMonoid.of .y ^ 3 * b, a * FreeMonoid.of .z ^ 3 * b}
    have hrhs_supp : supp rhs ⊆ S_cubes := by
      intro m hm
      have hne0 : rhs.coeff m ≠ 0 := by simpa [supp] using hm
      have hrhs_eq : rhs = mono (a * FreeMonoid.of .x ^ 3 * b) +
          mono (a * FreeMonoid.of .y ^ 3 * b) + mono (a * FreeMonoid.of .z ^ 3 * b) := by
        simp only [rhs, xyzSystem, add_mul, mul_add]
        simp only [mono, MonoidAlgebra.single_mul_single, mul_one]
      rw [hrhs_eq] at hne0
      by_contra hns
      simp only [S_cubes, Finset.mem_insert, Finset.mem_singleton, not_or] at hns
      apply hne0
      simp [mono, MonoidAlgebra.coeff_single_apply, Ne.symm hns.1, Ne.symm hns.2.1, Ne.symm hns.2.2]
    have hm_sub : supp ((xyzSystem k).basicReduction a
        (FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z) b h) ⊆
        (supp h).erase m₀ ∪ S_cubes := by
      intro m hm
      have hne0 : ((xyzSystem k).basicReduction a
          (FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z) b h).coeff m ≠ 0 := by
        simpa [supp] using hm
      rw [hdiff] at hne0
      by_cases hm_eq : m = m₀
      · subst hm_eq
        have hnm_rhs : m₀ ∉ supp rhs := by
          intro hmr
          have hcube := hrhs_supp hmr
          simp only [S_cubes, Finset.mem_insert, Finset.mem_singleton] at hcube
          rcases hcube with h1 | h2 | h3 <;>
            [have := phiXYZ_cube_lt a b .x;
             have := phiXYZ_cube_lt a b .y;
             have := phiXYZ_cube_lt a b .z] <;>
            [rw [← h1] at this; rw [← h2] at this; rw [← h3] at this] <;>
            exact Nat.lt_irrefl _ this
        have hc_rhs : rhs.coeff m₀ = 0 := by simpa [supp] using hnm_rhs
        exfalso; apply hne0
        simp [mono, MonoidAlgebra.coeff_single_apply, hc_rhs]
      · by_cases hm_h : m ∈ supp h
        · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hm_eq, hm_h⟩)
        · have hc_h : h.coeff m = 0 := by simpa [supp] using hm_h
          have hc_rhs : rhs.coeff m ≠ 0 := by
            intro hr0
            apply hne0
            simp [hc_h, hr0, mono, MonoidAlgebra.coeff_single_apply, Ne.symm hm_eq]
          exact Finset.mem_union_right _ (hrhs_supp (by simpa [supp] using hc_rhs))
    have hm_le : xyzWeight ((xyzSystem k).basicReduction a
        (FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z) b h) ≤
        ∑ m ∈ (supp h).erase m₀ ∪ S_cubes, 4 ^ phiXYZ m :=
      by unfold xyzWeight; exact Finset.sum_le_sum_of_subset (f := fun m => 4 ^ phiXYZ m) hm_sub
    have h2 := sum_union_weight_le ((supp h).erase m₀) S_cubes (fun m => 4 ^ phiXYZ m)
    have h3 : ∑ m ∈ S_cubes, 4 ^ phiXYZ m < 4 ^ phiXYZ m₀ := xyz_cubes_weight_lt a b
    have h4 : (∑ m ∈ (supp h).erase m₀, 4 ^ phiXYZ m) + 4 ^ phiXYZ m₀ = xyzWeight h := by
      unfold xyzWeight; exact Finset.sum_erase_add (supp h) (fun m => 4 ^ phiXYZ m) hm₀
    omega
  -- Now a decreasing sequence of naturals must stabilize:
  let seq : ℕ → FreeAlg k XYZ := fun n => RewritingSystem.reduction ((List.range n).map ρ) g
  have hseq_succ : ∀ n, seq (n + 1) = ρ n (seq n) := by
    intro n
    simp only [seq, List.range_succ, List.map_append, RewritingSystem.reduction, List.foldl_append]
    rfl
  have hmono : ∀ n, xyzWeight (seq (n + 1)) ≤ xyzWeight (seq n) := by
    intro n
    rw [hseq_succ]
    by_cases he : ρ n (seq n) = seq n
    · rw [he]
    · exact Nat.le_of_lt (hstep (ρ n) (hρ n) (seq n) he)
  have hmono_le : ∀ a b, a ≤ b → xyzWeight (seq b) ≤ xyzWeight (seq a) := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | step _ ih => exact le_trans (hmono _) ih
  have hex : ∃ m, ∃ N, xyzWeight (seq N) = m := ⟨_, 0, rfl⟩
  let m₀ := Nat.find hex
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  have hconst : ∀ n ≥ N, seq n = seq N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [hseq_succ]
      by_cases he : ρ k (seq k) = seq k
      · exact he.trans ih
      exfalso
      have hlt : xyzWeight (ρ k (seq k)) < xyzWeight (seq k) := hstep (ρ k) (hρ k) (seq k) he
      rw [← hseq_succ] at hlt
      have hle : xyzWeight (seq k) ≤ xyzWeight (seq N) := hmono_le N k hk
      have hlt' : xyzWeight (seq (k + 1)) < m₀ := lt_of_lt_of_le hlt (hle.trans (le_of_eq hN))
      exact Nat.find_min hex hlt' ⟨k + 1, rfl⟩
  refine ⟨N, fun n hn => ?_⟩
  exact hconst (n + 1) (by omega) |>.trans (hconst (N + 1) (by omega)).symm

/-- Each cube occurs with coefficient one in the rule of §2.2; used to exclude
compatible total multiplicative orders. -/
theorem xyzSystem_cube_mem_supp (a : XYZ) : FreeMonoid.of a ^ 3 ∈ supp ((xyzSystem k).f
    (FreeMonoid.of XYZ.x * FreeMonoid.of XYZ.y * FreeMonoid.of XYZ.z)) := by
  have hxy : (FreeMonoid.of XYZ.x ^ 3 : FreeMonoid XYZ) ≠ FreeMonoid.of XYZ.y ^ 3 := by
    intro h
    have := congrArg FreeMonoid.toList h
    simp [pow_succ] at this
  have hxz : (FreeMonoid.of XYZ.x ^ 3 : FreeMonoid XYZ) ≠ FreeMonoid.of XYZ.z ^ 3 := by
    intro h
    have := congrArg FreeMonoid.toList h
    simp [pow_succ] at this
  have hyz : (FreeMonoid.of XYZ.y ^ 3 : FreeMonoid XYZ) ≠ FreeMonoid.of XYZ.z ^ 3 := by
    intro h
    have := congrArg FreeMonoid.toList h
    simp [pow_succ] at this
  cases a <;> simp [supp, xyzSystem, mono, hxy, hxz, hyz, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]

/-- **§2.2.** No total order makes `xyz ↦ x³ + y³ + z³` a Gröbner basis: for a total
multiplicative order, `xyz < max(x³, y³, z³)`. -/
theorem xyzSystem_not_isGroebner : ¬ (xyzSystem k).IsGroebner := by
  rintro ⟨le, h, ht⟩
  haveI := h.isPartialOrder
  have hmul : ∀ u v a b, le u v → le (a * u * b) (a * v * b) := by
    intro u v a b huv
    by_cases he : u = v
    · subst v; exact Std.Refl.refl _
    · exact (h.mul u v a b ⟨huv, he⟩).1
  have hmax : ∃ m : FreeMonoid XYZ, le (FreeMonoid.of XYZ.x) m ∧
      le (FreeMonoid.of XYZ.y) m ∧ le (FreeMonoid.of XYZ.z) m ∧
      (m = FreeMonoid.of XYZ.x ∨ m = FreeMonoid.of XYZ.y ∨ m = FreeMonoid.of XYZ.z) := by
    rcases ht (FreeMonoid.of XYZ.x) (FreeMonoid.of XYZ.y) with hxy | hyx
    · rcases ht (FreeMonoid.of XYZ.y) (FreeMonoid.of XYZ.z) with hyz | hzy
      · exact ⟨_, IsTrans.trans _ _ _ hxy hyz, hyz, Std.Refl.refl _, Or.inr (Or.inr rfl)⟩
      · exact ⟨_, hxy, Std.Refl.refl _, hzy, Or.inr (Or.inl rfl)⟩
    · rcases ht (FreeMonoid.of XYZ.x) (FreeMonoid.of XYZ.z) with hxz | hzx
      · exact ⟨_, hxz, IsTrans.trans _ _ _ hyx hxz, Std.Refl.refl _, Or.inr (Or.inr rfl)⟩
      · exact ⟨_, Std.Refl.refl _, hyx, hzx, Or.inl rfl⟩
  obtain ⟨m, hx, hy, hz, hm⟩ := hmax
  have hbound : le (FreeMonoid.of XYZ.x * FreeMonoid.of XYZ.y * FreeMonoid.of XYZ.z) (m ^ 3) := by
    have h₁ := hmul _ _ 1 (FreeMonoid.of XYZ.y * FreeMonoid.of XYZ.z) hx
    have h₂ := hmul _ _ m (FreeMonoid.of XYZ.z) hy
    have h₃ := hmul _ _ (m * m) 1 hz
    simp only [one_mul, mul_one, ← mul_assoc] at h₁ h₃
    simpa only [pow_succ, pow_zero, one_mul] using
      IsTrans.trans _ _ _ h₁ (IsTrans.trans _ _ _ h₂ h₃)
  have hsupp : m ^ 3 ∈ supp ((xyzSystem k).f
      (FreeMonoid.of XYZ.x * FreeMonoid.of XYZ.y * FreeMonoid.of XYZ.z)) := by
    rcases hm with rfl | rfl | rfl <;> exact xyzSystem_cube_mem_supp k _
  have hc := h.compat _ (Set.mem_singleton _) _ hsupp
  exact hc.2 (Std.Antisymm.antisymm _ _ hc.1 hbound)

end Example

end TamaroffPhd

end
