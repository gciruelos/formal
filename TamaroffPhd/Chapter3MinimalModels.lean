import TamaroffPhd.Chapter2Section2DGAlgebras
import TamaroffPhd.PreliminariesAnickChains

/-!
# Chapter 3: Models for monomial algebras

The minimal model of a monomial algebra (Theorem 3.2.6), the A∞-coalgebra structure on Tor
(Theorem 3.2.1), the A∞-algebra structure on Ext (Theorems 3.2.7, 3.2.9 and 3.3.3), the
Chuang–King example (Theorem 3.3.4), vanishing patterns (Proposition 3.3.5, Corollary 3.3.6) and
models of algebras with a Gröbner basis (Theorem 3.4.1).

## Contents

* `torCoalgebra`: the A∞-coalgebra on the span of Anick chains with the coproducts of
  Theorem 2.1; Proposition 1.7 (adjoining a relation).
* `minimalModel`: the quasi-free algebra on Anick chains with the differential of Theorem 2.6.
* `extMu`: the higher products on `Ext_A` of Theorem 2.7, and their duality with `torCoalgebra`.
* Higher products on `Ext*_Λ(k, k) = k ⊕ kC∨` for monomial quiver algebras, formula (3.5):
  `yoneda`, multilinear extension, the Stasheff identities (3.4), A∞-isomorphisms.
* Theorem 3.4 (Chuang–King), Proposition 3.5, Corollary 3.6, Theorem 4.1.

Bardzell's resolution (§3.5), the Govorov–Gruenberg formulas (Theorem 3.1, used only in the
proof of Proposition 3.5) and the conjecture of §4.2 are not stated.
-/

noncomputable section

namespace TamaroffPhd

open Classical MonomialData

/-- `∑_{i<j} rᵢ (rⱼ + 1)` for a list of degrees. -/
def pairSum : List ℕ → ℕ
  | [] => 0
  | r :: rs => r * (rs.map (· + 1)).sum + pairSum rs

/-! ## One-vertex monomial algebras -/

section OneVertex

variable (k : Type) [Field k] {X : Type} (W : Set (List X))

/-- The monomial data `(X, W)` of the algebra `k⟨X⟩/(W)`. -/
abbrev monData : MonomialData X := MonomialData.ofRelations W

/-- The rewriting system `(X, W, 0)`, whose algebra is the monomial algebra `A = k⟨X | W⟩`. -/
def monSystem : RewritingSystem k X := ⟨FreeMonoid.ofList '' W, fun _ => 0⟩

/-- The monomial algebra `A = k⟨X⟩/(W)`. -/
abbrev MonAlg := (monSystem k W).Alg

/-- The sign `(-1)^{C(n+1, 2) + |γ₁|}` of a decomposition `(γ₁, …, γₙ)` in Theorem 2.6. -/
def modelSign (ds : List (monData W).Chain) : k :=
  (-1 : k) ^ ((ds.length + 1).choose 2 + ((ds.map Chain.deg).headD 0))

/-- The generators of the minimal model: the Anick chains, an `r`-chain in degree `r` (the
desuspension `s⁻¹ Tor_{r+1}`). -/
def modelGens : GradedGens := ⟨(monData W).Chain, fun γ => γ.deg⟩

/-- **Theorem 2.6 (differential).** `dγ = - ∑ (-1)^{C(n+1, 2) + |γ₁|} γ₁ ⋯ γₙ`, the sum over all
decompositions `(γ₁, …, γₙ)` of `γ`. -/
def modelDiff (γ : (monData W).Chain) : FreeAlg k (monData W).Chain :=
  - ∑ᶠ ds : (monData W).Decomposition γ, modelSign k W ds.val • mono (FreeMonoid.ofList ds.val)

/-- **Theorem 2.6.** The quasi-free algebra `Ω∞ Tor_A` on the Anick chains, with the
differential `modelDiff`. -/
def minimalModel : QuasiFree k where
  G := (monData W).Chain
  deg γ := γ.deg
  dGen := modelDiff k W
  dGen_mem γ := by
    refine Submodule.neg_mem _ (finsum_induction (p := (· ∈ _)) (Submodule.zero_mem _)
      (fun _ _ => Submodule.add_mem _) fun ds => Submodule.smul_mem _ _ ?_)
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    have h := ds.2.2.2
    simp only [Set.mem_setOf_eq, GradedGens.wdeg, FreeMonoid.toList_ofList]
    have e : (ds.val.map fun γ : (monData W).Chain => γ.deg).sum = (ds.val.map Chain.deg).sum := rfl
    omega
  dGen_zero γ hγ := by
    have : IsEmpty ((monData W).Decomposition γ) := ⟨fun ds => by have := ds.2.2.2; simp_all⟩
    simp [modelDiff, finsum_of_isEmpty]

/-- The augmentation `Ω∞ Tor_A → A`: a `0`-chain (a letter) goes to its class, chains of
positive degree to zero. -/
def modelAug : FreeAlg k (monData W).Chain →ₐ[k] MonAlg k W :=
  MonoidAlgebra.lift k (MonAlg k W) (FreeMonoid (monData W).Chain)
    (FreeMonoid.lift fun γ =>
      if γ.deg = 0 then (monSystem k W).toAlg (mono (FreeMonoid.ofList γ.word)) else 0)

/-- The differential of a chain lies in any submodule containing the monomial
`γ₁ ⋯ γₙ` of every decomposition. -/
theorem modelDiff_mem {γ : (monData W).Chain} {S : Submodule k (FreeAlg k (monData W).Chain)}
    (h : ∀ ds : (monData W).Decomposition γ, mono (FreeMonoid.ofList ds.val) ∈ S) :
    modelDiff k W γ ∈ S :=
  Submodule.neg_mem _ (finsum_induction (p := (· ∈ S)) (Submodule.zero_mem _)
    (fun _ _ => Submodule.add_mem _) fun ds => Submodule.smul_mem _ _ (h ds))

/-- **Theorem 2.6 (minimality).** The differential is decomposable: each decomposition has at
least two factors. -/
theorem minimalModel_isMinimal : (minimalModel k W).IsMinimal := fun γ =>
  modelDiff_mem k W (S := (minimalModel k W).decomposable) fun ds =>
    (show mono (FreeMonoid.ofList ds.val) ∈ Submodule.span k
        (mono '' {w : FreeMonoid (monData W).Chain | 2 ≤ w.toList.length}) from
      Submodule.subset_span ⟨_, (by show 2 ≤ (FreeMonoid.toList (FreeMonoid.ofList ds.val)).length; rw [FreeMonoid.toList_ofList]; exact ds.2.1), rfl⟩)

/-- **Theorem 2.6 (triangulated).** Ordering the generators by degree, `dγ` is a polynomial in
chains of smaller degree, since the degrees of the factors of a decomposition add up to
`deg γ - 1`. -/
theorem minimalModel_isTriangulated : (minimalModel k W).IsTriangulated := by
  refine ⟨fun γ => γ.deg, fun γ => modelDiff_mem k W
    (S := (Algebra.adjoin (R := k) (A := FreeAlg k (monData W).Chain) ((fun g' => mono (FreeMonoid.of g')) ''
      {g' : (monData W).Chain | g'.deg < γ.deg})).toSubmodule) fun ds => ?_⟩
  have key : ∀ l : List (monData W).Chain, (∀ g ∈ l, g.deg < γ.deg) →
      mono (FreeMonoid.ofList l) ∈ Algebra.adjoin (R := k) (A := FreeAlg k (monData W).Chain)
        ((fun g' => mono (FreeMonoid.of g')) '' {g' : (monData W).Chain | g'.deg < γ.deg}) := by
    intro l
    induction l with
    | nil => intro _; exact one_mem _
    | cons a l ih =>
        intro hl
        have : mono (FreeMonoid.ofList (a :: l)) =
            (mono (k := k) (FreeMonoid.of a)) * mono (FreeMonoid.ofList l) := by
          rw [FreeMonoid.ofList_cons, MonoidAlgebra.single_mul_single, mul_one]
        rw [this]
        exact mul_mem (Algebra.subset_adjoin ⟨a, hl a (by simp), rfl⟩)
          (ih fun g hg => hl g (by simp [hg]))
  refine key _ fun g hg => ?_
  have hsum := ds.2.2.2
  have : g.deg ≤ (ds.val.map Chain.deg).sum := List.le_sum_of_mem (List.mem_map_of_mem hg)
  omega

/-- The augmentation kills the generators of positive degree. -/
theorem modelAug_of_pos (g : (monData W).Chain) (hg : 0 < g.deg) :
    modelAug k W (mono (FreeMonoid.of g)) = 0 := by
  simp [modelAug, MonoidAlgebra.lift_single, Nat.pos_iff_ne_zero.1 hg]

/-- The augmentation is surjective: the letters are the `0`-chains. -/
theorem modelAug_surjective : Function.Surjective (modelAug k W) := by
  let ψ : FreeAlg k X →ₐ[k] FreeAlg k (monData W).Chain :=
    MonoidAlgebra.lift k (FreeAlg k (monData W).Chain) (FreeMonoid X)
      (FreeMonoid.lift fun x => mono (FreeMonoid.of (⟨(0, [x]), ⟨[x], show (monData W).IsChain 0 [x] [x] from ⟨x, rfl, rfl⟩⟩⟩ :
        (monData W).Chain)))
  have hcomp : (modelAug k W).comp ψ = (monSystem k W).toAlg := by
    refine MonoidAlgebra.algHom_ext (fun m => ?_) (Subsingleton.elim _ _)
    induction m using FreeMonoid.inductionOn' with
    | one => simp [← MonoidAlgebra.one_def]
    | of_mul x m ih =>
        have e : (MonoidAlgebra.single (FreeMonoid.of x * m) (1 : k)) =
            MonoidAlgebra.single (FreeMonoid.of x) 1 * MonoidAlgebra.single m 1 := by
          rw [MonoidAlgebra.single_mul_single, mul_one]
        rw [e, map_mul, map_mul, ih]
        congr 1
        simp [ψ, modelAug, MonoidAlgebra.lift_single]
        refine (if_pos rfl).trans ?_
        rfl
  intro a
  obtain ⟨b, rfl⟩ := RingQuot.mkAlgHom_surjective k _ a
  exact ⟨ψ b, congrArg (fun f => f b) (congrArg DFunLike.coe hcomp)⟩

/-- **Theorem 2.6.** For each monomial algebra `A = k⟨X⟩/(W)` (finitely many letters and
relations, relations minimal), `Ω∞ Tor_A → A` is a minimal model.

**Status.** Proved: minimality, triangulated, `φ` kills positive degrees, `φ` surjective. Open
(the three `sorry`s below, in order): `d² = 0` (sign bookkeeping over decompositions),
`ker φ ∩ T₀ = boundaries`, and acyclicity in positive degrees. The thesis obtains these by
homotopy transfer from the bar construction (Chapter 2), which is not formalized. -/
theorem minimalModel_isModel [Finite X] (hW : W.Finite) (hmin : (monData W).IsMinimal) :
    (minimalModel k W).IsModel (modelAug k W) ∧ (minimalModel k W).IsMinimal := by
  refine ⟨⟨?_, minimalModel_isTriangulated k W, fun g hg => modelAug_of_pos k W g hg,
    modelAug_surjective k W, ?_, ?_⟩, minimalModel_isMinimal k W⟩
  · sorry
  · sorry
  · sorry

/-- The minimal model is of finite type (§6.2). -/
theorem minimalModel_isFiniteType [Finite X] (hW : W.Finite) :
    (minimalModel k W).IsFiniteType := by
  sorry

/-! ### The A∞-coalgebra on Tor -/

/-- The sign `(-1)^N` of Theorem 2.1, `N = C(n+1, 2) + r₁ + ∑_{i<n} (n - i)(rᵢ + 1)`. -/
def torSign (ds : List (monData W).Chain) : k :=
  let rs := ds.map Chain.deg
  (-1 : k) ^ ((rs.length + 1).choose 2 + rs.headD 0 +
    ((List.range rs.length).map fun i => (rs.length - (i + 1)) * (rs.getD i 0 + 1)).sum)

/-- **Theorem 2.1 (coproducts).** `Δₙ(γ) = ∑ (-1)^N γ₁ ⊗ ⋯ ⊗ γₙ` over the decompositions of `γ`
into `n ≥ 2` chains; `Δ₁ = 0`. -/
def torDelta (γ : (monData W).Chain) : FreeAlg k (monData W).Chain :=
  ∑ᶠ ds : (monData W).Decomposition γ, torSign k W ds.val • mono (FreeMonoid.ofList ds.val)

/-- **Theorem 2.1.** The A∞-coalgebra `Tor_A` on the Anick chains, an `r`-chain in degree
`r + 1`, with the coproducts `torDelta`. -/
def torCoalgebra : AInfCoalgebra k where
  C := (monData W).Chain
  deg γ := γ.deg + 1
  deg_pos _ := Nat.succ_pos _
  Δ := torDelta k W
  cobar_mem := sorry
  cobar_zero := sorry

/-- **Theorem 2.1.** The coproducts of `torCoalgebra` satisfy the Stasheff identities and form a
canonical minimal A∞-coalgebra structure on `Tor_A`: its ∞-cobar construction is a model of
`A`.

**Change.** The thesis obtains the A∞-coalgebra on `Tor_A` by homotopy transfer
along the Jöllenbeck–Welker contraction of the bar construction, and Theorem 2.1 describes the
transferred coproducts. The bar construction and the transfer are not formalized here. We define
the coproducts by the formula of Theorem 2.1 and state that they form an A∞-coalgebra whose
∞-cobar construction is a model of `A` (a *canonical* structure, §1.1: such a structure is the
same as a quasi-free model). The technical results of §3.1–3.2 on the contraction
(Proposition 1.1, Lemma 1.2, Corollary 1.3, Lemma 1.4, Corollary 1.5, Theorem 1.6, Lemmas 2.2–2.4,
Proposition 2.5) concern the transfer and are left for a later pass. -/
theorem torCoalgebra_canonical [Finite X] (hW : W.Finite) (hmin : (monData W).IsMinimal) :
    (torCoalgebra k W).IsAInf ∧ (torCoalgebra k W).IsMinimal ∧
      ∃ φ : FreeAlg k (monData W).Chain →ₐ[k] MonAlg k W, (torCoalgebra k W).cobar.IsModel φ := by
  sorry

/-- **Theorem 2.6 (proof).** Desuspending the coproducts of Theorem 2.1 gives the differential of
Theorem 2.6: the cobar construction of `torCoalgebra` is `minimalModel`. -/
theorem cobar_torCoalgebra_dGen (γ : (monData W).Chain) :
    (torCoalgebra k W).cobar.dGen γ = (minimalModel k W).dGen γ := by
  sorry

/-- **Proposition 1.7.** Adjoining a non-redundant monomial relation: if `W ⊆ W'`, every
`n`-chain of `W` is an `n`-chain of `W'`, and the coproducts of a chain of `W` are the same for
`W` and for `W'`. -/
theorem chains_mono_of_subset {W W' : Set (List X)} (h : W ⊆ W')
    (hmin : (monData W).IsMinimal) (hmin' : (monData W').IsMinimal) (n : ℕ) :
    (monData W).Chains n ⊆ (monData W').Chains n := by
  sorry

/-! ### The A∞-algebra on Ext -/

/-- The sign `(-1)^M` of Theorem 2.7, `M = C(n+1, 2) - 1 + ∑_{i<j} rᵢ(rⱼ + 1) + r₁ + r` with
`r = r₁ + ⋯ + rₙ + 1`. -/
def extSign (ds : List (monData W).Chain) : k :=
  let rs := ds.map Chain.deg
  (-1 : k) ^ ((rs.length + 1).choose 2 - 1 + pairSum rs + rs.headD 0 + (rs.sum + 1))

/-- **Theorem 2.7.** The higher product `μₙ(γ₁∨ ⊗ ⋯ ⊗ γₙ∨)` on `Ext_A = Tor_A∨`, as the coefficient
of `γ∨`: `(-1)^M` if the concatenation `γ₁ ⋯ γₙ` is the chain `γ` of degree `r₁ + ⋯ + rₙ + 1`,
and `0` otherwise. -/
def extMu (ds : List (monData W).Chain) (γ : (monData W).Chain) : k :=
  if (ds.map Chain.word).flatten = γ.word ∧ (ds.map Chain.deg).sum + 1 = γ.deg then extSign k W ds
  else 0

/-- The Koszul sign `(-1)^{N}`, `N = ∑_{i ≥ 2} (|c₁| + ⋯ + |c_{i-1}|) |fᵢ|`, of the pairing
`Dⁿ : Ext^{⊗n} → (Tor^{⊗n})∨` on `fᵢ = cᵢ∨` (§3.2.2), with `|c| = r + 1`. -/
def pairingSign (ds : List (monData W).Chain) : k :=
  let rs := ds.map Chain.deg
  (-1 : k) ^ ((List.range rs.length).map fun i =>
    ((rs.take i).map (· + 1)).sum * (rs.getD i 0 + 1)).sum

/-- **Theorem 2.7.** The products `extMu` are the dual of the coproducts of `torCoalgebra`:
`μₙ(φ₁ ⊗ ⋯ ⊗ φₙ) = (-1)^{n ∑|φᵢ|} Dⁿ(φ₁ ⊗ ⋯ ⊗ φₙ) ∘ Δₙ`. Hence they form a canonical A∞-algebra
structure on `Ext_A`, dual to Theorem 2.1. -/
theorem extMu_eq_dual (ds : List (monData W).Chain) (hds : 2 ≤ ds.length)
    (γ : (monData W).Chain) :
    extMu k W ds γ = (-1 : k) ^ (ds.length * (ds.map fun c => c.deg + 1).sum) *
      pairingSign k W ds * (torDelta k W γ).coeff (FreeMonoid.ofList ds) := by
  sorry

end OneVertex

/-! ## The Yoneda algebra of a monomial quiver algebra (§3.3.2) -/

section Quiver

variable (k : Type) [Field k] (Q : Quiv) (R : Set (List Q.A))

/-- The basis of `Ext*_Λ(k, k) = 𝕜 ⊕ kC∨_{*-1}`: the vertex idempotents (degree `0`) and the
duals of Anick chains (an `r`-chain in degree `r + 1`). -/
abbrev EBasis := Q.V ⊕ (Q.data R).Chain

/-- The homological degree on `EBasis`. -/
def EBasis.deg {Q : Quiv} {R : Set (List Q.A)} : EBasis Q R → ℕ
  | .inl _ => 0
  | .inr γ => γ.deg + 1

/-- The Yoneda algebra `E = Ext*_Λ(k, k)`, as the span of `EBasis`. -/
abbrev E := EBasis Q R →₀ k

/-- The sign `(-1)^N` of (3.5), `N = ∑_{i<j} rᵢ(rⱼ + 1) + r₁ + ∑ᵢ rᵢ`. -/
def yonedaSign (ds : List (Q.data R).Chain) : k :=
  let rs := ds.map Chain.deg
  (-1 : k) ^ (pairSum rs + rs.headD 0 + rs.sum)

/-- The chain underlying the product `γ₁∨ ⋯ γₙ∨` in `kQ^op`: the path `γₙ ⋯ γ₁` of `Q`, when it is a
chain of degree `r₁ + ⋯ + rₙ + 1`. -/
def opConcat (ds : List (Q.data R).Chain) : Option (Q.data R).Chain :=
  let p := (ds.reverse.map Chain.word).flatten
  let r := (ds.map Chain.deg).sum + 1
  if h : p ∈ (Q.data R).Chains r then some ⟨(r, p), h⟩ else none

/-- **(3.5).** The higher products `mₙ` of `Ext*_Λ(k, k)` on basis elements, `n ≥ 2`:
`mₙ(γ₁, …, γₙ) = (-1)^N γ₁ ⋯ γₙ` when the product in `kQ^op` is a chain of degree
`r₁ + ⋯ + rₙ + 1`, and `0` otherwise. The vertex idempotents act as a strict unit: `m₂` with
an idempotent multiplies paths, `mₙ` vanishes on idempotents for `n ≥ 3`; `m₁ = 0`. -/
def yoneda : List (EBasis Q R) → E k Q R
  | [.inl v, .inl w] => if v = w then Finsupp.single (.inl v) 1 else 0
  | [.inl v, .inr γ] =>
      if hγ : γ.word ≠ [] then
        if Q.finish γ.word hγ = v then Finsupp.single (.inr γ) 1 else 0
      else 0
  | [.inr γ, .inl v] =>
      if hγ : γ.word ≠ [] then
        if Q.start γ.word hγ = v then Finsupp.single (.inr γ) 1 else 0
      else 0
  | bs =>
      if 2 ≤ bs.length then
        match bs.mapM (fun b => match b with | .inr γ => some γ | .inl _ => none) with
        | some ds =>
            match opConcat Q R ds with
            | some γ => Finsupp.single (.inr γ) (yonedaSign k Q R ds)
            | none => 0
        | none => 0
      else 0

/-- The multilinear extension of a function on lists of basis elements to lists of vectors. -/
def multilin {B V : Type} [AddCommGroup V] [Module k V] (f : List B → V) :
    List (B →₀ k) → V
  | [] => f []
  | x :: xs => x.sum fun b c => c • multilin (fun bs => f (b :: bs)) xs

/-- The degree of a basis tuple. -/
def tupleDeg {B : Type} (deg : B → ℕ) (bs : List B) : ℕ := (bs.map deg).sum

/-- **(3.4).** The left side of the Stasheff identity on a basis tuple `b₁, …, bₙ`:
`∑_{r+s+t=n} (-1)^{rs+t} m_{r+1+t}(id^r ⊗ m_s ⊗ id^t)`, where applying `m_s` (of degree `2 - s`)
after `b₁, …, b_r` contributes the Koszul sign `(-1)^{s (|b₁| + ⋯ + |b_r|)}`. -/
def stasheff {B : Type} (deg : B → ℕ) (m : List B → (B →₀ k)) (bs : List B) : B →₀ k :=
  ((List.range (bs.length + 1)).flatMap fun r => (List.range (bs.length + 1 - r)).map fun s => (r, s)).foldr
    (fun rs acc =>
      let r := rs.1
      let s := rs.2
      if 1 ≤ s then
        let t := bs.length - r - s
        acc + ((-1 : k) ^ (r * s + t + s * tupleDeg deg (bs.take r))) •
          multilin k m ((bs.take r).map (Finsupp.single · 1) ++ [m ((bs.drop r).take s)] ++
            (bs.drop (r + s)).map (Finsupp.single · 1))
      else acc) 0

/-- **(3.4).** `m` (on basis tuples, extended multilinearly) satisfies the Stasheff identities:
an A∞-algebra structure on the span of the basis. -/
def IsAInfAlgebra {B : Type} (deg : B → ℕ) (m : List B → (B →₀ k)) : Prop :=
  ∀ bs : List B, bs ≠ [] → stasheff k deg m bs = 0

/-- **Theorems 2.9 and 3.3.** The products (3.5) on `Ext*_Λ(k, k)` satisfy the Stasheff
identities: they form a minimal, strictly unital A∞-algebra structure, which models the
canonical A∞-structure on the Yoneda algebra.

**Change.** For one-vertex algebras, an A∞-algebra structure on
`Ext_A` is canonical here when the dual A∞-coalgebra is canonical (its cobar construction is a
model). For quiver algebras the cobar construction is relative to `kQ₀`, which is not
formalized, so Theorems 2.9 and 3.3 are stated as the Stasheff identities for (3.5); that (3.5)
models the canonical structure is used through Theorem 3.3 in Chapter 5. -/
theorem yoneda_isAInf (hR : (Q.data R).IsMinimal) :
    IsAInfAlgebra k EBasis.deg (yoneda k Q R) := by
  sorry

/-- The compositions of `n` (lists of positive integers with sum `n`). -/
def compositions : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range (n + 1)).flatMap fun i =>
      (compositions (n - i)).map fun c => (i + 1) :: c
  decreasing_by omega

/-- **§3.3.3.** An `∞`-morphism `f : (E, m) → (E, ν)` with `f₁ = id` between two minimal A∞-algebra
structures on the span of `B`: maps `fₙ` (`n ≥ 2`, of degree `1 - n`) on basis tuples with
`∑_{r+s+t=n} (-1)^{r+st} f_{r+1+t}(1^r ⊗ m_s ⊗ 1^t) = ∑_{i₁+⋯+i_q=n} (-1)^w ν_q(f_{i₁} ⊗ ⋯ ⊗ f_{i_q})`,
`w = ∑_j (q - j)(i_j - 1)`, with the Koszul signs of the evaluation. -/
def IsInfIso {B : Type} (deg : B → ℕ) (m ν : List B → (B →₀ k)) (f : List B → (B →₀ k)) :
    Prop :=
  (∀ b, f [b] = Finsupp.single b 1) ∧
  ∀ bs : List B, bs ≠ [] →
    ((List.range (bs.length + 1)).flatMap fun r => (List.range (bs.length + 1 - r)).map fun s => (r, s)).foldr
      (fun rs acc =>
        let r := rs.1
        let s := rs.2
        if 1 ≤ s then
          acc + ((-1 : k) ^ (r + s * (bs.length - r - s) + s * tupleDeg deg (bs.take r))) •
            multilin k f ((bs.take r).map (Finsupp.single · 1) ++ [m ((bs.drop r).take s)] ++
              (bs.drop (r + s)).map (Finsupp.single · 1))
        else acc) 0 =
    (compositions bs.length).foldr (fun is acc =>
      let pieces := (List.range is.length).map fun j =>
        ((bs.drop ((is.take j).sum)).take (is.getD j 0))
      let w := ((List.range is.length).map fun j => (is.length - (j + 1)) * (is.getD j 0 - 1)).sum
      let koszul := ((List.range is.length).map fun j =>
        (is.getD j 0 + 1) * tupleDeg deg ((bs.take ((is.take j).sum)))).sum
      acc + ((-1 : k) ^ (w + koszul)) • multilin k ν (pieces.map f)) 0

end Quiver

/-! ## The Chuang–King example (§3.3.3) -/

section ChuangKing

/-- The arrows `a, b, c, d, e` of the cyclic quiver `C₅`. -/
inductive C5Arrow | a | b | c | d | e
  deriving DecidableEq

instance : Fintype C5Arrow := ⟨{.a, .b, .c, .d, .e}, by intro x; cases x <;> simp⟩

/-- The cyclic quiver `C₅` with arrows `a, b, c, d, e` in cyclic order. -/
def C5 : Quiv where
  V := Fin 5
  A := C5Arrow
  src := fun | .a => 0 | .b => 1 | .c => 2 | .d => 3 | .e => 4
  tgt := fun | .a => 1 | .b => 2 | .c => 3 | .d => 4 | .e => 0

/-- The relations `abcd, bcde, deab` of the algebra `CK₅`. -/
def ck5Rels : Set (List C5.A) := {[.a, .b, .c, .d], [.b, .c, .d, .e], [.d, .e, .a, .b]}

variable (k : Type) [Field k]

/-- The element `ωₙ = d ⊗ e ⊗ (abcde)^{⊗(n-4)} ⊗ a ⊗ b` of `B^{⊗n}`, as a basis tuple, given the
chains `d, e, a, b` (`0`-chains) and `abcde` (a `2`-chain). -/
def omegaTuple (n : ℕ) (d e a b abcde : (C5.data ck5Rels).Chain) : List (EBasis C5 ck5Rels) :=
  [.inr d, .inr e] ++ List.replicate (n - 4) (.inr abcde) ++ [.inr a, .inr b]

/-- **Theorem 3.4 (Chuang–King).** The Yoneda algebra of `CK₅ = kC₅/(abcd, bcde, deab)` has
infinitely many non-vanishing higher products for any canonical A∞-structure: for every
A∞-structure `ν` on `Ext` that is `∞`-isomorphic to (3.5) (with `f₁ = id`), `νₙ(ωₙ) ≠ 0` for all
`n ≥ 4`. -/
theorem chuangKing (ν f : List (EBasis C5 ck5Rels) → E k C5 ck5Rels)
    (hν : IsAInfAlgebra k EBasis.deg ν) (hf : IsInfIso k EBasis.deg (yoneda k C5 ck5Rels) ν f)
    (d e a b abcde : (C5.data ck5Rels).Chain)
    (hd : d.word = [.d]) (he : e.word = [.e]) (ha : a.word = [.a]) (hb : b.word = [.b])
    (habcde : abcde.word = [.a, .b, .c, .d, .e]) (n : ℕ) (hn : 4 ≤ n) :
    ν (omegaTuple n d e a b abcde) ≠ 0 := by
  sorry

end ChuangKing

/-! ## Vanishing patterns (§3.3.4) -/

section Vanishing

variable (k : Type) [Field k] (Q : Quiv) (R : Set (List Q.A))

/-- **Proposition 3.5.** For chains `γ₁, …, γₙ` (`n ≥ 2`) of the Ext algebra (an `r`-chain has
degree `r + 1`), `mₙ(γ₁, …, γₙ) = 0` if at least three have even degree, if exactly two have
even degree unless they are `γ₁` and `γₙ`, or if exactly one has even degree unless it is `γ₁`
or `γₙ`. -/
theorem yoneda_vanishing (hR : (Q.data R).IsMinimal) (ds : List (Q.data R).Chain)
    (hn : 2 ≤ ds.length)
    (hne : yoneda k Q R (ds.map .inr) ≠ 0) :
    let even := (List.range ds.length).filter fun i => Even ((ds.map Chain.deg).getD i 0 + 1)
    even.length ≤ 2 ∧ (even.length = 2 → even = [0, ds.length - 1]) ∧
      (even.length = 1 → even = [0] ∨ even = [ds.length - 1]) := by
  sorry

/-- **Corollary 3.6.** When `γ₁ ⋯ γₙ` is a chain, the sign of (3.5) is
`(-1)^{n r₁ + r₁ rₙ + r₁ + rₙ}`. -/
theorem yonedaSign_simplify (hR : (Q.data R).IsMinimal) (ds : List (Q.data R).Chain)
    (hn : 2 ≤ ds.length) (hc : (opConcat Q R ds).isSome) :
    let rs := ds.map Chain.deg
    yonedaSign k Q R ds = (-1 : k) ^ (rs.length * rs.headD 0 + rs.headD 0 * rs.getLastD 0 +
      rs.headD 0 + rs.getLastD 0) := by
  sorry

end Vanishing

/-! ## Algebras with a Gröbner basis (§3.4.2) -/

section Groebner

variable (k : Type) [Field k] {X : Type}

/-- The underlying monomial of a monomial in the chain generators: the concatenation of the
chains. -/
def underlyingWord {W : Set (List X)} (w : FreeMonoid (monData W).Chain) : List X :=
  w.toList.flatMap Chain.word

/-- **Theorem 4.1.** Let `A` be presented by a rewriting system `S` that is a finite Gröbner basis
for a total monomial order `le`, with associated monomial algebra `A⁰ = k⟨X | W⟩`. There is a
(possibly non-minimal) model `(T(W'), d) → A` on the generators of the minimal model of `A⁰`
such that `d - d⁰` lowers the order of the underlying monomial of each chain. -/
theorem groebner_model [Finite X] (S : RewritingSystem k X) (W : Set (List X))
    (hW : W.Finite) (hSW : S.W = FreeMonoid.ofList '' W) (hmin : (monData W).IsMinimal)
    (le : FreeMonoid X → FreeMonoid X → Prop) (hle : S.IsCompatibleOrdering le)
    (htot : ∀ m m', le m m' ∨ le m' m) :
    ∃ (B : QuasiFree k) (e : B.G ≃ (monData W).Chain) (φ : FreeAlg k B.G →ₐ[k] S.Alg),
      B.IsModel φ ∧ (∀ g, B.deg g = (e g).deg) ∧
      ∀ g, ∀ w ∈ (B.dGen g - (MonoidAlgebra.mapDomainAlgHom k k
          (FreeMonoid.map e.symm)) ((minimalModel k W).dGen (e g))).coeff.support,
        le (FreeMonoid.ofList (underlyingWord (FreeMonoid.map e w))) (FreeMonoid.ofList (e g).word) ∧
          FreeMonoid.ofList (underlyingWord (FreeMonoid.map e w)) ≠ FreeMonoid.ofList (e g).word := by
  sorry

end Groebner

end TamaroffPhd

end
