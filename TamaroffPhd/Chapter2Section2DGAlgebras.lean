import TamaroffPhd.Chapter2Section2AnickChains

/-!
# Chapter 2, §2.9 and §2.11–2.12: quasi-free dg algebras, models and A∞-coalgebras

## Contents

* `GradedGens`: a set of generators with non-negative homological degrees, and the free algebra
  `T(V)` on them with its homological grading.
* `gradedDerivation`: the graded derivation of `T(V)` extending given values on generators.
* `QuasiFree`: a quasi-free algebra `(T(V), d)` (Definition 8), its cycles and boundaries,
  triangulated (Definition 8) and minimal ones.
* `QuasiFree.IsModel`: a model of an algebra concentrated in degree zero (Definition 9).
* `AInfCoalgebra`: an A∞-coalgebra on a graded vector space with a chosen basis (§2.9), with its
  ∞-cobar construction `Ω∞`.

-/

noncomputable section

namespace TamaroffPhd

open Classical

variable (k : Type) [Field k]

/-! ## Graded generators -/

/-- A set of generators with homological degrees: the basis of a non-negatively graded vector
space `V`, so that `T(V) = k⟨G⟩`. -/
structure GradedGens where
  /-- The generators. -/
  G : Type
  /-- Their homological degrees. -/
  deg : G → ℕ

namespace GradedGens

variable {k} (V : GradedGens)

/-- The homological degree of a monomial: the sum of the degrees of its letters. -/
def wdeg (w : FreeMonoid V.G) : ℕ := (w.toList.map V.deg).sum

/-- The elements of `T(V)` of homological degree `n`. -/
def hom (n : ℕ) : Submodule k (FreeAlg k V.G) :=
  Submodule.span k (mono '' {w | V.wdeg w = n})

/-- Multiplication adds homogeneous degrees, used for the adjoint derivation in
Chapter 4, §2.2. -/
theorem hom_mul {n m : ℕ} {x y : FreeAlg k V.G}
    (hx : x ∈ V.hom n) (hy : y ∈ V.hom m) : x * y ∈ V.hom (n + m) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨u * v, ?_, ?_⟩
      · simpa [wdeg, FreeMonoid.toList_mul, List.map_append, List.sum_append] using congrArg₂ (· + ·) hu hv
      · simp [mono, MonoidAlgebra.single_mul_single]
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- The decomposable elements: combinations of monomials of length at least two. -/
def decomposable : Submodule k (FreeAlg k V.G) :=
  Submodule.span k (mono '' {w : FreeMonoid V.G | 2 ≤ w.toList.length})

/-- The value on a monomial (as a list of generators) of the graded derivation with values `v`
on generators; `odd` records the parity of the degree of the derivation, which governs the
Koszul sign `(-1)^{|D| |x|}` of the Leibniz rule. -/
def derivWord (odd : Bool) (v : V.G → FreeAlg k V.G) : List V.G → FreeAlg k V.G
  | [] => 0
  | g :: w => v g * mono (FreeMonoid.ofList w) +
      (if odd then (-1 : k) ^ V.deg g else 1) • (mono (FreeMonoid.of g) * derivWord odd v w)

/-- The graded derivation of `T(V)` extending `v`: on a monomial `g₁ ⋯ gₙ` it is
`∑ᵢ ± g₁ ⋯ g_{i-1} v(gᵢ) g_{i+1} ⋯ gₙ`, with the Koszul sign of the Leibniz rule
`D(ab) = D(a) b + (-1)^{|D||a|} a D(b)`. -/
def gradedDerivation (odd : Bool) (v : V.G → FreeAlg k V.G) : FreeAlg k V.G →ₗ[k] FreeAlg k V.G :=
  linOnMonomials fun w => V.derivWord odd v w.toList

/-- The value of `gradedDerivation` on a generator is the prescribed value. -/
theorem gradedDerivation_of (odd : Bool) (v : V.G → FreeAlg k V.G) (g : V.G) :
    V.gradedDerivation odd v (mono (FreeMonoid.of g)) = v g := by
  simp [gradedDerivation, linOnMonomials, mono, derivWord, ← MonoidAlgebra.one_def]

end GradedGens

/-! ## Quasi-free algebras and models -/

/-- **Definition 8 (Quasi-free algebra).** A dg algebra `(T(V), d)` whose underlying graded
algebra is free: generators with degrees, and the values `d g` of the differential on
generators, of degree `|g| - 1` (and zero on generators of degree zero, the algebras being
concentrated in non-negative degrees). The differential is the induced degree `-1` derivation;
`d² = 0` is a separate condition (`QuasiFree.IsDG`).

**Change.** Mathlib has no differential graded algebras. We only need dg algebras
that are free as graded algebras (Chapters 3, 4 and 6 work with models), so a dg algebra is a
free algebra `k⟨G⟩` on graded generators together with a degree `-1` derivation. Homology is
expressed through cycles and boundaries in each degree instead of a quotient. -/
structure QuasiFree extends GradedGens where
  /-- The differential on generators. -/
  dGen : G → FreeAlg k G
  /-- `d g` has degree `|g| - 1`. -/
  dGen_mem : ∀ g, dGen g ∈ toGradedGens.hom (deg g - 1)
  /-- Generators of degree zero are cycles. -/
  dGen_zero : ∀ g, deg g = 0 → dGen g = 0

namespace QuasiFree

variable {k} (B : QuasiFree k)

/-- The differential `d` of `(T(V), d)`: the odd derivation extending `dGen`. -/
def d : FreeAlg k B.G →ₗ[k] FreeAlg k B.G := B.gradedDerivation true B.dGen

/-- `(T(V), d)` is a dg algebra: `d² = 0`. -/
def IsDG : Prop := B.d ∘ₗ B.d = 0

/-- Cycles of degree `n`. -/
def cycles (n : ℕ) : Submodule k (FreeAlg k B.G) := LinearMap.ker B.d ⊓ B.hom n

/-- Boundaries of degree `n`: the image of the degree `n + 1` part under `d`. -/
def boundaries (n : ℕ) : Submodule k (FreeAlg k B.G) := (B.hom (n + 1)).map B.d

/-- The homology vanishes in degree `n`. -/
def IsAcyclicIn (n : ℕ) : Prop := B.cycles n ≤ B.boundaries n

/-- **Definition 8 (Triangulated).** The generators admit a filtration `V = V(1) ⊕ V(2) ⊕ ⋯`
with `d V(j+1)` in the subalgebra generated by `V(1) ⊕ ⋯ ⊕ V(j)`: a level function on
generators. -/
def IsTriangulated : Prop :=
  ∃ level : B.G → ℕ, ∀ g, B.dGen g ∈
    Algebra.adjoin k ((fun g' => mono (FreeMonoid.of g')) '' {g' | level g' < level g})

/-- **Definition 9 (Minimal).** The differential is decomposable on generators. -/
def IsMinimal : Prop := ∀ g, B.dGen g ∈ B.decomposable

/-- **Definition 9 (Model).** A model of an algebra `A` concentrated in degree zero: a
triangulated quasi-free dg algebra `(T(V), d)` with a surjective quasi-isomorphism `φ` to `A`.
Since `A` has no differential, `φ` vanishes on positive degrees and on boundaries, the
homology of `T(V)` vanishes in positive degrees, and `φ` identifies `H₀` with `A`. -/
structure IsModel {A : Type} [Ring A] [Algebra k A] (φ : FreeAlg k B.G →ₐ[k] A) : Prop where
  isDG : B.IsDG
  triangulated : B.IsTriangulated
  map_pos : ∀ g, 0 < B.deg g → φ (mono (FreeMonoid.of g)) = 0
  surjective : Function.Surjective φ
  ker_zero : ∀ x ∈ B.hom 0, φ x = 0 ↔ x ∈ B.boundaries 0
  acyclic : ∀ n, 0 < n → B.IsAcyclicIn n

/-- A model is of *finite type* if there are finitely many generators in each degree (§6.2). -/
def IsFiniteType : Prop := ∀ n, Set.Finite {g | B.deg g = n}

end QuasiFree

/-! ## Graded derivations and the tangent complex (§6.3.2) -/

namespace GradedGens

variable {k} (V : GradedGens)

/-- A *graded derivation* of `T(V)` of degree `δ ∈ ℤ`: a linear map shifting degrees by `δ`
that satisfies the graded Leibniz rule on monomials. Every one is `gradedDerivation` of its
values on generators. -/
structure IsGradedDerivation (δ : ℤ) (D : FreeAlg k V.G →ₗ[k] FreeAlg k V.G) : Prop where
  deg : ∀ (n : ℕ) (x : FreeAlg k V.G), x ∈ V.hom n → 0 ≤ (n : ℤ) + δ →
    D x ∈ V.hom ((n : ℤ) + δ).toNat
  deg_neg : ∀ (n : ℕ) (x : FreeAlg k V.G), x ∈ V.hom n → (n : ℤ) + δ < 0 → D x = 0
  leibniz : ∀ a b : FreeMonoid V.G, D (mono a * mono b) =
    D (mono a) * mono b + (-1 : k) ^ (δ.natAbs * V.wdeg a) • (mono a * D (mono b))

/-- The graded commutator `[D₁, D₂] = D₁ D₂ - (-1)^{|D₁||D₂|} D₂ D₁` of two derivations of
degrees `δ₁`, `δ₂`; it makes `Der(T(V))` a graded Lie algebra (§6.3.2). -/
def bracket (δ₁ δ₂ : ℤ) (D₁ D₂ : FreeAlg k V.G →ₗ[k] FreeAlg k V.G) :
    FreeAlg k V.G →ₗ[k] FreeAlg k V.G :=
  D₁ ∘ₗ D₂ - (-1 : k) ^ (δ₁.natAbs * δ₂.natAbs) • (D₂ ∘ₗ D₁)

/-- A graded derivation satisfies the graded Leibniz rule on homogeneous left factors. -/
theorem IsGradedDerivation.leibniz_hom {V : GradedGens} {δ : ℤ}
    {D : FreeAlg k V.G →ₗ[k] FreeAlg k V.G}
    (hD : V.IsGradedDerivation δ D) {n : ℕ} {x : FreeAlg k V.G} (hx : x ∈ V.hom n)
    (y : FreeAlg k V.G) :
    D (x * y) = D x * y + (-1 : k) ^ (δ.natAbs * n) • (x * D y) := by
  have hy_mono : ∀ (a : FreeMonoid V.G) (y : FreeAlg k V.G),
      D (mono a * y) = D (mono a) * y + (-1 : k) ^ (δ.natAbs * V.wdeg a) • (mono a * D y) := by
    intro a y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      rw [mul_add, map_add, hy₁, hy₂, mul_add, map_add, mul_add, smul_add]
      abel
    | single b c =>
      have hs : (MonoidAlgebra.single b c : FreeAlg k V.G) = c • mono b := by
        simp [mono, MonoidAlgebra.smul_single]
      rw [hs, mul_smul_comm, map_smul, hD.leibniz a b, smul_add, mul_smul_comm,
        map_smul, mul_smul_comm, smul_comm ((-1 : k) ^ (δ.natAbs * V.wdeg a)) c]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← ha]
    exact hy_mono a y
  | zero => simp
  | add x z _ _ hx hz =>
    rw [add_mul, map_add, hx, hz, map_add, add_mul, add_mul, smul_add]
    abel
  | smul c x _ hx =>
    rw [smul_mul_assoc, map_smul, hx, map_smul, smul_mul_assoc, smul_mul_assoc, smul_add,
      smul_comm c]

private lemma neg_one_pow_eq_of_mod_two {α : Type*} [Ring α] {m n : ℕ}
    (h : (m : ℤ) % 2 = (n : ℤ) % 2) : (-1 : α) ^ m = (-1 : α) ^ n := by
  have h' : m % 2 = n % 2 := by omega
  rw [← Nat.div_add_mod m 2, ← Nat.div_add_mod n 2, pow_add, pow_add,
    pow_mul, pow_mul, neg_one_sq, one_pow, one_pow, one_mul, one_mul, h']

private lemma int_mod_two_natAbs (a : ℤ) : a % 2 = (a.natAbs : ℤ) % 2 := by
  cases a with
  | ofNat n => simp
  | negSucc n => rw [Int.natAbs_negSucc, Int.negSucc_eq]; omega

/-- **§6.3.2.** The graded commutator of graded derivations is a graded derivation. -/
theorem isGradedDerivation_bracket {δ₁ δ₂ : ℤ} {D₁ D₂ : FreeAlg k V.G →ₗ[k] FreeAlg k V.G}
    (h₁ : V.IsGradedDerivation δ₁ D₁) (h₂ : V.IsGradedDerivation δ₂ D₂) :
    V.IsGradedDerivation (δ₁ + δ₂) (V.bracket δ₁ δ₂ D₁ D₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n x hx hnonneg
    simp only [bracket, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    apply Submodule.sub_mem
    · by_cases h2 : (n : ℤ) + δ₂ < 0
      · rw [h₂.deg_neg n x hx h2, map_zero]; exact zero_mem _
      · push Not at h2
        have hx2 := h₂.deg n x hx h2
        have hx1 := h₁.deg ((n : ℤ) + δ₂).toNat (D₂ x) hx2 (by omega)
        rwa [show (((n : ℤ) + δ₂).toNat : ℤ) + δ₁ = (n : ℤ) + (δ₁ + δ₂) by omega] at hx1
    · apply Submodule.smul_mem
      by_cases h1 : (n : ℤ) + δ₁ < 0
      · rw [h₁.deg_neg n x hx h1, map_zero]; exact zero_mem _
      · push Not at h1
        have hx1 := h₁.deg n x hx h1
        have hx2 := h₂.deg ((n : ℤ) + δ₁).toNat (D₁ x) hx1 (by omega)
        rwa [show (((n : ℤ) + δ₁).toNat : ℤ) + δ₂ = (n : ℤ) + (δ₁ + δ₂) by omega] at hx2
  · intro n x hx hneg
    simp only [bracket, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    have h12 : D₁ (D₂ x) = 0 := by
      by_cases h2 : (n : ℤ) + δ₂ < 0
      · rw [h₂.deg_neg n x hx h2, map_zero]
      · push Not at h2
        exact h₁.deg_neg ((n : ℤ) + δ₂).toNat (D₂ x) (h₂.deg n x hx h2) (by omega)
    have h21 : D₂ (D₁ x) = 0 := by
      by_cases h1 : (n : ℤ) + δ₁ < 0
      · rw [h₁.deg_neg n x hx h1, map_zero]
      · push Not at h1
        exact h₂.deg_neg ((n : ℤ) + δ₁).toNat (D₁ x) (h₁.deg n x hx h1) (by omega)
    rw [h12, h21, smul_zero, sub_zero]
  · intro a b
    have ha : (mono a : FreeAlg k V.G) ∈ V.hom (k := k) (V.wdeg a) :=
      Submodule.subset_span ⟨a, rfl, rfl⟩
    have hD1D2 : D₁ (D₂ (mono a * mono b)) =
        D₁ (D₂ (mono a) * mono b) +
        (-1 : k) ^ (δ₂.natAbs * V.wdeg a) • (D₁ (mono a) * D₂ (mono b)) +
        (-1 : k) ^ (δ₂.natAbs * V.wdeg a + δ₁.natAbs * V.wdeg a) • (mono a * D₁ (D₂ (mono b))) := by
      rw [h₂.leibniz a b, map_add, map_smul, h₁.leibniz_hom ha (D₂ (mono b)),
        smul_add, smul_smul, ← pow_add, add_assoc]
    have hD2D1 : D₂ (D₁ (mono a * mono b)) =
        D₂ (D₁ (mono a) * mono b) +
        (-1 : k) ^ (δ₁.natAbs * V.wdeg a) • (D₂ (mono a) * D₁ (mono b)) +
        (-1 : k) ^ (δ₁.natAbs * V.wdeg a + δ₂.natAbs * V.wdeg a) • (mono a * D₂ (D₁ (mono b))) := by
      rw [h₁.leibniz a b, map_add, map_smul, h₂.leibniz_hom ha (D₁ (mono b)),
        smul_add, smul_smul, ← pow_add, add_assoc]
    have hcross1 : D₁ (D₂ (mono a) * mono b) -
        (-1 : k) ^ (δ₁.natAbs * δ₂.natAbs + δ₁.natAbs * V.wdeg a) • (D₂ (mono a) * D₁ (mono b)) =
        D₁ (D₂ (mono a)) * mono b := by
      by_cases h2 : (V.wdeg a : ℤ) + δ₂ < 0
      · rw [h₂.deg_neg _ _ ha h2, zero_mul, map_zero, zero_mul, smul_zero, sub_zero, zero_mul]
      · push Not at h2
        rw [h₁.leibniz_hom (h₂.deg _ _ ha h2) (mono b)]
        have hs : (-1 : k) ^ (δ₁.natAbs * ((V.wdeg a : ℤ) + δ₂).toNat) =
            (-1 : k) ^ (δ₁.natAbs * δ₂.natAbs + δ₁.natAbs * V.wdeg a) := by
          apply neg_one_pow_eq_of_mod_two
          have htoNat : (((V.wdeg a : ℤ) + δ₂).toNat : ℤ) = (V.wdeg a : ℤ) + δ₂ := by omega
          have hm2 : (δ₂.natAbs : ℤ) % 2 = δ₂ % 2 := (int_mod_two_natAbs δ₂).symm
          rw [Nat.cast_mul, htoNat, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
            Int.mul_emod, Int.add_emod ((δ₁.natAbs : ℤ) * _),
            Int.mul_emod (δ₁.natAbs : ℤ) (δ₂.natAbs : ℤ),
            Int.mul_emod (δ₁.natAbs : ℤ) (V.wdeg a : ℤ), hm2,
            Int.add_emod (V.wdeg a : ℤ) δ₂]
          rcases Int.emod_two_eq_zero_or_one δ₂ with h2' | h2' <;>
            rcases Int.emod_two_eq_zero_or_one (V.wdeg a : ℤ) with ha' | ha' <;>
            rcases Int.emod_two_eq_zero_or_one (δ₁.natAbs : ℤ) with h1' | h1' <;>
            simp [h2', ha'] <;> omega
        rw [hs, add_sub_cancel_right]
    have hcross2 : (-1 : k) ^ (δ₂.natAbs * V.wdeg a) • (D₁ (mono a) * D₂ (mono b)) -
        (-1 : k) ^ (δ₁.natAbs * δ₂.natAbs) • D₂ (D₁ (mono a) * mono b) =
        -((-1 : k) ^ (δ₁.natAbs * δ₂.natAbs) • (D₂ (D₁ (mono a)) * mono b)) := by
      by_cases h1 : (V.wdeg a : ℤ) + δ₁ < 0
      · rw [h₁.deg_neg _ _ ha h1, zero_mul, smul_zero, zero_mul, map_zero, smul_zero, sub_zero,
          zero_mul, smul_zero, neg_zero]
      · push Not at h1
        rw [h₂.leibniz_hom (h₁.deg _ _ ha h1) (mono b), smul_add, smul_smul, ← pow_add]
        have hs : (-1 : k) ^ (δ₁.natAbs * δ₂.natAbs + δ₂.natAbs * ((V.wdeg a : ℤ) + δ₁).toNat) =
            (-1 : k) ^ (δ₂.natAbs * V.wdeg a) := by
          apply neg_one_pow_eq_of_mod_two
          have htoNat : (((V.wdeg a : ℤ) + δ₁).toNat : ℤ) = (V.wdeg a : ℤ) + δ₁ := by omega
          have hm1 : (δ₁.natAbs : ℤ) % 2 = δ₁ % 2 := (int_mod_two_natAbs δ₁).symm
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, htoNat,
            Int.add_emod, Int.mul_emod (δ₁.natAbs : ℤ), Int.mul_emod (δ₂.natAbs : ℤ),
            hm1, Int.add_emod (V.wdeg a : ℤ) δ₁, Int.mul_emod (δ₂.natAbs : ℤ) (V.wdeg a : ℤ)]
          rcases Int.emod_two_eq_zero_or_one δ₁ with h1' | h1' <;>
            rcases Int.emod_two_eq_zero_or_one (V.wdeg a : ℤ) with ha' | ha' <;>
            rcases Int.emod_two_eq_zero_or_one (δ₂.natAbs : ℤ) with h2' | h2' <;>
            simp [h1', ha'] <;> omega
        rw [hs, sub_add_eq_sub_sub]
        abel
    have htail : (-1 : k) ^ (δ₂.natAbs * V.wdeg a + δ₁.natAbs * V.wdeg a) =
        (-1 : k) ^ ((δ₁ + δ₂).natAbs * V.wdeg a) := by
      apply neg_one_pow_eq_of_mod_two
      have hm1 : (δ₁.natAbs : ℤ) % 2 = δ₁ % 2 := (int_mod_two_natAbs δ₁).symm
      have hm2 : (δ₂.natAbs : ℤ) % 2 = δ₂ % 2 := (int_mod_two_natAbs δ₂).symm
      have hm12 : ((δ₁ + δ₂).natAbs : ℤ) % 2 = (δ₁ + δ₂) % 2 := (int_mod_two_natAbs (δ₁ + δ₂)).symm
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Int.add_emod, Int.mul_emod (δ₂.natAbs : ℤ), Int.mul_emod (δ₁.natAbs : ℤ),
        Int.mul_emod ((δ₁ + δ₂).natAbs : ℤ), hm1, hm2, hm12, Int.add_emod δ₁ δ₂]
      rcases Int.emod_two_eq_zero_or_one δ₁ with h1' | h1' <;>
        rcases Int.emod_two_eq_zero_or_one δ₂ with h2' | h2' <;>
        rcases Int.emod_two_eq_zero_or_one (V.wdeg a : ℤ) with ha' | ha' <;>
        simp [h1', h2', ha']
    have hcross2' : (-1 : k) ^ (δ₁.natAbs * δ₂.natAbs) • (D₂ (D₁ (mono a)) * mono b) =
        (-1 : k) ^ (δ₁.natAbs * δ₂.natAbs) • D₂ (D₁ (mono a) * mono b) -
          (-1 : k) ^ (δ₂.natAbs * V.wdeg a) • (D₁ (mono a) * D₂ (mono b)) := by
      rw [← neg_inj, neg_sub]
      exact hcross2.symm
    simp only [bracket, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      hD1D2, hD2D1, smul_add, smul_smul, ← pow_add]
    rw [htail, sub_mul, smul_mul_assoc, mul_sub, smul_sub, ← hcross1, hcross2']
    rw [show (-1 : k) ^ (δ₁.natAbs * δ₂.natAbs + (δ₁.natAbs * V.wdeg a + δ₂.natAbs * V.wdeg a)) •
        (mono a * D₂ (D₁ (mono b))) =
        (-1 : k) ^ ((δ₁ + δ₂).natAbs * V.wdeg a) •
          (mono a * ((-1 : k) ^ (δ₁.natAbs * δ₂.natAbs) • D₂ (D₁ (mono b)))) by
      rw [mul_smul_comm, smul_smul, ← htail, ← pow_add, add_comm (δ₂.natAbs * V.wdeg a),
        add_comm (δ₁.natAbs * δ₂.natAbs)]]
    abel

end GradedGens

/-! ## A∞-coalgebras (§2.9) -/

/-- The desuspension sign `(-1)^{∑ᵢ (n - i) |cᵢ|}` of `(s⁻¹)^{⊗n}(c₁ ⊗ ⋯ ⊗ cₙ)`. -/
def desuspSign {C : Type} (deg : C → ℕ) : List C → k
  | [] => 1
  | c :: w => (-1 : k) ^ (w.length * deg c) * desuspSign deg w

/-- The value of the ∞-cobar differential on a generator `s⁻¹ c`: `∑ₙ (s⁻¹)^{⊗n} Δₙ(s c)`. -/
def cobarDiffOf {C : Type} (deg : C → ℕ) (Δ : C → FreeAlg k C) (c : C) : FreeAlg k C :=
  linOnMonomials (fun w => desuspSign k deg w.toList • mono w) (Δ c)

/-- **§2.9 (A∞-coalgebra).** A positively graded vector space with a basis `C`, with locally
finite coproducts `Δₙ : V → V^{⊗n}` of degree `n - 2`. All the `Δₙ(c)` are recorded together as
one element of `k⟨C⟩` whose part of word length `n` is `Δₙ(c)`; the degree condition is stated
on the desuspension. The Stasheff identities are imposed through the ∞-cobar construction,
`AInfCoalgebra.IsAInf`.

**Change.** §2.9 defines A∞-coalgebras by the Stasheff identities `SI(n)` and
notes that they are equivalent to `b² = 0` for the ∞-cobar construction. We take the latter as
the definition. The ∞-cobar construction is the quasi-free algebra on the desuspended basis. -/
structure AInfCoalgebra where
  /-- The basis. -/
  C : Type
  /-- Homological degrees (positive). -/
  deg : C → ℕ
  deg_pos : ∀ c, 0 < deg c
  /-- `Δ(c) = ∑ₙ Δₙ(c)`. -/
  Δ : C → FreeAlg k C
  /-- `Δₙ` has degree `n - 2`: after desuspension, `b(s⁻¹ c)` has degree `|c| - 2`. -/
  cobar_mem : ∀ c, cobarDiffOf k deg Δ c ∈ (GradedGens.mk C fun c => deg c - 1).hom (deg c - 2)
  /-- Generators of degree one go to zero (there is nothing in negative degrees). -/
  cobar_zero : ∀ c, deg c = 1 → cobarDiffOf k deg Δ c = 0

namespace AInfCoalgebra

variable {k} (C : AInfCoalgebra k)

/-- **§2.9 (∞-cobar construction).** `Ω∞ V`: the free algebra on `s⁻¹ V` (generators of degree
`|c| - 1`) with the derivation `b` extending `cobarDiffOf`. -/
def cobar : QuasiFree k where
  G := C.C
  deg c := C.deg c - 1
  dGen := cobarDiffOf k C.deg C.Δ
  dGen_mem c := by rw [show C.deg c - 1 - 1 = C.deg c - 2 by omega]; exact C.cobar_mem c
  dGen_zero c h := C.cobar_zero c (by have := C.deg_pos c; omega)

/-- **§2.9.** The Stasheff identities `SI(n)`, in the form `b² = 0` on the ∞-cobar
construction. -/
def IsAInf : Prop := C.cobar.IsDG

/-- An A∞-coalgebra is *minimal* if `Δ₁ = 0`. -/
def IsMinimal : Prop := ∀ c, ∀ w ∈ (C.Δ c).coeff.support, 2 ≤ w.toList.length

end AInfCoalgebra

end TamaroffPhd

end
