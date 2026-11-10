import TamaroffPhd.Chapter3MinimalModels

/-!
# Chapter 6, §6.1–6.3: Term rewriting and homotopical algebra

Every multiplicative free resolution of a monomial algebra gives a Diamond Lemma: convergence of
a rewriting system `Σ = (X, W, f)` is equivalent to perturbing the differential of a model of the
monomial algebra `A_Σ⁰` (Theorem 2.1), to solving the Maurer–Cartan equation in low degrees
(Theorem 3.1), and to reducing the obstructions of the degree-two generators to zero
(Theorem 3.2). For the inclusion–exclusion model this is Bergman's Diamond Lemma
(Proposition 4.1); for the minimal model, the Triangle Lemma (Proposition 4.2).

## Contents

* Definition 19: the Shafarevich complex `Sha(S, k⟨X⟩)`.
* Definitions 20–21: word-homogeneous acyclic extensions of Shafarevich complexes
  (`ShaExtension`), the maps to `A_Σ⁰` and `A_Σ`, perturbations, `Σ`-filtered maps.
* Theorem 2.1, Definition 23 (Maurer–Cartan equation in the tangent complex), Theorem 3.1,
  Definition 24 (obstructions), Theorem 3.2.

Proposition 4.1 (Bergman's Diamond Lemma) and Proposition 4.2 (Triangle Lemma) are in
`Chapter6Section4DiamondLemma`.

-/

noncomputable section

namespace TamaroffPhd

open Classical MonomialData

variable (k : Type) [Field k] {X : Type}

/-- The inclusion `k⟨X⟩ → k⟨X ⊕ S⟩` of the degree-zero generators. -/
def inclLeft (Y : Type) : FreeAlg k X →ₐ[k] FreeAlg k (X ⊕ Y) :=
  MonoidAlgebra.mapDomainAlgHom k k (FreeMonoid.map Sum.inl)

theorem inclLeft_hom (S : Set (FreeAlg k X)) (a : FreeAlg k X) :
    inclLeft k S a ∈ (GradedGens.mk (X ⊕ S) (Sum.elim (fun _ => 0) (fun _ => 1))).hom 0 := by
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    change MonoidAlgebra.mapDomainAlgHom k k (FreeMonoid.map Sum.inl) (mono m) ∈ _
    rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
    apply Submodule.subset_span
    refine ⟨FreeMonoid.map Sum.inl m, ?_, rfl⟩
    dsimp [GradedGens.wdeg]
    simp [List.map_map]
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

/-- **Definition 19 (Shafarevich complex).** `Sha(S, k⟨X⟩) = (T(V), d)` with `V₀ = kX`,
`V₁ = kS` and `d(e_s) = s`. -/
def sha (S : Set (FreeAlg k X)) : QuasiFree k where
  G := X ⊕ S
  deg := Sum.elim (fun _ => 0) (fun _ => 1)
  dGen := Sum.elim (fun _ => 0) (fun s => inclLeft k S s.val)
  dGen_mem := by
    rintro (x | s)
    · simp
    · simpa using inclLeft_hom k S s.val
  dGen_zero := by
    rintro (x | s) h
    · rfl
    · cases h

/-- The algebra `k⟨X | S⟩` presented by a set of relations. -/
abbrev PresAlg (S : Set (FreeAlg k X)) := RingQuot fun x y : FreeAlg k X => x ∈ S ∧ y = 0

/-- The projection `T(X ⊕ S) → k⟨X | S⟩` sending letters `x` to `[x]` and `S` to 0. -/
def shaH0_proj (S : Set (FreeAlg k X)) : FreeAlg k (X ⊕ S) →ₐ[k] PresAlg k S :=
  MonoidAlgebra.lift k (PresAlg k S) (FreeMonoid (X ⊕ S))
    (FreeMonoid.lift (Sum.elim (fun x => RingQuot.mkAlgHom k _ (mono (FreeMonoid.of x))) (fun _ => 0)))

lemma inclLeft_mono (S : Set (FreeAlg k X)) (m : FreeMonoid X) :
    inclLeft k S (mono m) = (mono (FreeMonoid.map Sum.inl m) : FreeAlg k (X ⊕ S)) := by
  change MonoidAlgebra.mapDomainAlgHom k k (FreeMonoid.map Sum.inl) (mono m) = _
  rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]

@[simp] lemma shaH0_proj_mono_of_inl (S : Set (FreeAlg k X)) (x : X) :
    shaH0_proj k S (mono (FreeMonoid.of (Sum.inl x))) =
      RingQuot.mkAlgHom k (fun x y => x ∈ S ∧ y = 0) (mono (FreeMonoid.of x)) := by
  dsimp [shaH0_proj, mono]
  rw [MonoidAlgebra.lift_single, FreeMonoid.lift_eval_of]
  simp

theorem shaH0_proj_inclLeft (S : Set (FreeAlg k X)) (a : FreeAlg k X) :
    shaH0_proj k S (inclLeft k S a) = RingQuot.mkAlgHom k (fun x y => x ∈ S ∧ y = 0) a := by
  have hcomp : (shaH0_proj k S).comp (inclLeft k S) = RingQuot.mkAlgHom k (fun x y => x ∈ S ∧ y = 0) := by
    refine MonoidAlgebra.algHom_ext (fun m => ?_) (Subsingleton.elim _ _)
    induction m using FreeMonoid.inductionOn' with
    | one =>
      change ((shaH0_proj k S).comp (inclLeft k S)) 1 = RingQuot.mkAlgHom k _ 1
      simp only [map_one]
    | of_mul x m ih =>
      change ((shaH0_proj k S).comp (inclLeft k S)) (mono (FreeMonoid.of x * m)) =
        RingQuot.mkAlgHom k _ (mono (FreeMonoid.of x * m))
      have e : (mono (FreeMonoid.of x * m) : FreeAlg k X) = mono (FreeMonoid.of x) * mono m := by
        simp [mono, MonoidAlgebra.single_mul_single]
      rw [e, map_mul, map_mul]
      change ((shaH0_proj k S).comp (inclLeft k S)) (mono (FreeMonoid.of x)) *
        ((shaH0_proj k S).comp (inclLeft k S)) (mono m) = _
      rw [ih]
      congr 1
      change shaH0_proj k S (inclLeft k S (mono (FreeMonoid.of x))) = _
      rw [inclLeft_mono, FreeMonoid.map_of, shaH0_proj_mono_of_inl]
  exact congrFun (congrArg DFunLike.coe hcomp) a

lemma shaH0_proj_dGen (S : Set (FreeAlg k X)) (g : X ⊕ S) :
    shaH0_proj k S ((sha k S).dGen g) = 0 := by
  dsimp only [sha]
  rcases g with (x | s)
  · change shaH0_proj k S 0 = 0
    simp
  · change shaH0_proj k S (inclLeft k S s.val) = 0
    rw [shaH0_proj_inclLeft]
    have hrel : (fun x y : FreeAlg k X => x ∈ S ∧ y = 0) s.val 0 := ⟨s.2, rfl⟩
    have := RingQuot.mkAlgHom_rel (A := FreeAlg k X) (S := k) (s := fun x y => x ∈ S ∧ y = 0) hrel
    rw [this, map_zero]

lemma shaH0_proj_derivWord (S : Set (FreeAlg k X)) (l : List (sha k S).G) :
    shaH0_proj k S ((sha k S).derivWord true (sha k S).dGen l) = 0 := by
  induction l with
  | nil =>
    change shaH0_proj k S 0 = 0
    simp
  | cons g l ih =>
    have h_eq : (sha k S).derivWord true (sha k S).dGen (g :: l) =
      (sha k S).dGen g * mono (FreeMonoid.ofList l) +
      ((-1 : k) ^ (sha k S).deg g) • (mono (FreeMonoid.of g) * (sha k S).derivWord true (sha k S).dGen l) := rfl
    erw [h_eq, map_add, map_mul, map_smul, map_mul, ih, mul_zero, smul_zero, add_zero,
      shaH0_proj_dGen, zero_mul]

/-- **§6.1.1.** `H₀(Sha(S, k⟨X⟩)) ≅ k⟨X | S⟩`: the degree-zero cycles modulo boundaries are the
quotient by the ideal generated by `S`. -/
theorem sha_H0 (S : Set (FreeAlg k X)) (x : FreeAlg k X) :
    inclLeft k S x ∈ (sha k S).boundaries 0 ↔
      RingQuot.mkAlgHom k (fun x y : FreeAlg k X => x ∈ S ∧ y = 0) x = 0 := by
  sorry

variable (S : RewritingSystem k X)

/-- **Definitions 20–21.** A word-homogeneous extension of the Shafarevich complex
`Sha(W, k⟨X⟩)`: a quasi-free algebra whose degree-zero generators are the letters `X`, whose
degree-one generators `e_w` are indexed by `W` with `d(e_w) = w`, graded by the free monoid `⟨X⟩`
(`e_w` of grade `w`) with a grade-preserving differential. -/
structure ShaExtension extends QuasiFree k where
  /-- The degree-zero generators are the letters. -/
  gen0 : X → G
  /-- The degree-one generators `e_w`, `w ∈ W`. -/
  gen1 : S.W → G
  /-- The grade of a generator. -/
  gr : G → FreeMonoid X
  gen0_deg : ∀ x, deg (gen0 x) = 0
  gen1_deg : ∀ w, deg (gen1 w) = 1
  gen0_bij : Function.Injective gen0 ∧ ∀ g, deg g = 0 → ∃ x, gen0 x = g
  gen1_bij : Function.Injective gen1 ∧ ∀ g, deg g = 1 → ∃ w, gen1 w = g
  d_gen1 : ∀ w, dGen (gen1 w) = mono (FreeMonoid.map gen0 w.val)
  gr_gen0 : ∀ x, gr (gen0 x) = FreeMonoid.of x
  gr_gen1 : ∀ w, gr (gen1 w) = w.val
  /-- Word-homogeneity: `d` preserves the grade. -/
  homog : ∀ g, ∀ w ∈ supp (dGen g), FreeMonoid.prodAux (w.toList.map gr) = gr g

namespace ShaExtension

variable {k S} (B : ShaExtension k S)

/-- The grade of a monomial in the generators. -/
def grade (w : FreeMonoid B.G) : FreeMonoid X := FreeMonoid.prodAux (w.toList.map B.gr)

/-- The map `T(V) → A` sending each letter `x` to `ι x` and the other generators to zero. -/
def toAlg {A : Type} [Ring A] [Algebra k A] (ι : X → A) : FreeAlg k B.G →ₐ[k] A :=
  MonoidAlgebra.lift k A (FreeMonoid B.G)
    (FreeMonoid.lift fun g => if h : ∃ x, B.gen0 x = g then ι h.choose else 0)

/-- **Definition 20.** `B` is an acyclic extension of `Sha(W, k⟨X⟩)`: a model of the monomial
algebra `A_Σ⁰`, concentrated in non-negative degrees. -/
def IsAcyclic : Prop :=
  B.IsModel (B.toAlg fun x => S.zero.toAlg (mono (FreeMonoid.of x)))

/-- **§6.2.** A linear map is `Σ`-filtered if it sends monomials of grade `u` to combinations of
monomials of grades strictly smaller than `u` for `<_Σ`. -/
def IsFiltered (D : FreeAlg k B.G →ₗ[k] FreeAlg k B.G) : Prop :=
  ∀ w : FreeMonoid B.G, ∀ w' ∈ supp (D (mono w)), S.lt (B.grade w') (B.grade w)

/-- The values on generators of a perturbation `d'` are `Σ`-filtered. -/
def IsFilteredOn (v : B.G → FreeAlg k B.G) (P : B.G → Prop) : Prop :=
  ∀ g, P g → ∀ w' ∈ supp (v g), S.lt (B.grade w') (B.gr g)

/-- The perturbed quasi-free algebra `(T(V), d + d')`, with `d'` given on generators. -/
def perturb (v : B.G → FreeAlg k B.G) (hv : ∀ g, v g ∈ B.hom (B.deg g - 1))
    (hv0 : ∀ g, B.deg g = 0 → v g = 0) : QuasiFree k where
  G := B.G
  deg := B.deg
  dGen g := B.dGen g + v g
  dGen_mem g := Submodule.add_mem _ (B.dGen_mem g) (hv g)
  dGen_zero g h := by simp [B.dGen_zero g h, hv0 g h]

/-- The image of `f(w) ∈ k⟨X⟩` in `T(V₀) ⊆ T(V)`. -/
def inclX : FreeAlg k X →ₐ[k] FreeAlg k B.G :=
  MonoidAlgebra.mapDomainAlgHom k k (FreeMonoid.map B.gen0)

/-- **Theorem 2.1.** Let `B` be a word-homogeneous acyclic extension of finite type of
`Sha(W, k⟨X⟩)`, for a terminating rewriting system `Σ`. Then `Σ` is convergent iff there is a
`Σ`-filtered perturbation `d'` such that `(T(V), d + d')` is an acyclic extension of
`Sha(R, k⟨X⟩)`, `R = {w - f(w)}`: `d'` vanishes on `V₀`, `d'(e_w) = -f(w)`, and
`(T(V), d + d') → A_Σ` is a model. -/
theorem theorem_2_1 (hterm : S.IsTerminating) (hB : B.IsAcyclic) (hfin : B.IsFiniteType) :
    S.IsConvergent ↔
      ∃ (v : B.G → FreeAlg k B.G) (hv : ∀ g, v g ∈ B.hom (B.deg g - 1))
        (hv0 : ∀ g, B.deg g = 0 → v g = 0),
        (∀ w, v (B.gen1 w) = - B.inclX (S.f w)) ∧ B.IsFilteredOn v (fun _ => True) ∧
        (B.perturb v hv hv0).IsModel (B.toAlg fun x => S.toAlg (mono (FreeMonoid.of x))) := by
  sorry

/-- **Definition 23 (Maurer–Cartan equation), §6.3.2.** For a degree `-1` derivation `F` of
`T(V)` given on generators, the Maurer–Cartan equation `[d + F, d + F] = 0` of the tangent
complex `(Der(T(V)), [d, -])`, in its square-zero form `(d + F)² = 0`, evaluated on a
generator.

**Change.** Over a field of characteristic zero the Maurer–Cartan equation
`[d + F, d + F] = 0` in `Der(T(V))` is equivalent to `(d + F)² = 0`. The thesis remarks
(§6.3) that the square-zero form makes Theorem 3.1 valid over any field; we use it throughout,
and do not need a general notion of dg Lie algebra (Definition 22). -/
def MaurerCartanAt (F : B.G → FreeAlg k B.G) (g : B.G) : Prop :=
  let D := B.gradedDerivation true (fun g => B.dGen g + F g)
  D (D (mono (FreeMonoid.of g))) = 0

/-- **Theorem 3.1.** Under the hypotheses of Theorem 2.1, `Σ` is convergent iff there is a
degree `-1` derivation `F` with `F(e_w) = -f(w)`, `F` `Σ`-filtered on `V₂`, satisfying the
Maurer–Cartan equation on generators of degree at most two. -/
theorem theorem_3_1 (hterm : S.IsTerminating) (hB : B.IsAcyclic) (hfin : B.IsFiniteType) :
    S.IsConvergent ↔
      ∃ F : B.G → FreeAlg k B.G, (∀ g, F g ∈ B.hom (B.deg g - 1)) ∧
        (∀ g, B.deg g = 0 → F g = 0) ∧
        (∀ w, F (B.gen1 w) = - B.inclX (S.f w)) ∧ B.IsFilteredOn F (fun g => B.deg g = 2) ∧
        ∀ g, B.deg g ≤ 2 → B.MaurerCartanAt F g := by
  sorry

/-- The substitution `T(V) → k⟨X⟩` sending `x ↦ x`, `e_w ↦ f(w)` and the generators of degree at
least two to zero. On `T(V₀) ⊗ V₁ ⊗ T(V₀)` it is `a e_w b ↦ a f(w) b`. -/
def substF : FreeAlg k B.G →ₐ[k] FreeAlg k X :=
  MonoidAlgebra.lift k (FreeAlg k X) (FreeMonoid B.G)
    (FreeMonoid.lift fun g =>
      if h : ∃ x, B.gen0 x = g then mono (FreeMonoid.of h.choose)
      else if h' : ∃ w, B.gen1 w = g then S.f h'.choose else 0)

/-- **Definition 24 (Obstruction).** For `c ∈ V₂`, `d(c) = ∑ aᵢ e_{wᵢ} bᵢ`, and
`S_c = ∑ aᵢ f(wᵢ) bᵢ ∈ k⟨X⟩`. -/
def obstruction (c : B.G) : FreeAlg k X := B.substF (B.dGen c)

/-- **Theorem 3.2.** Under the hypotheses of Theorem 2.1, `Σ` is convergent iff for each
(word-homogeneous) generator `c ∈ V₂` the obstruction `S_c` is sent to zero by some
reduction. -/
theorem theorem_3_2 (hterm : S.IsTerminating) (hB : B.IsAcyclic) (hfin : B.IsFiniteType) :
    S.IsConvergent ↔
      ∀ c, B.deg c = 2 → ∃ ρs, S.IsReductionList ρs ∧
        RewritingSystem.reduction ρs (B.obstruction c) = 0 := by
  sorry

end ShaExtension

end TamaroffPhd

end
