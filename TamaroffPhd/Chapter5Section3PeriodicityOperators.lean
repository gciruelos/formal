import TamaroffPhd.Chapter5Section2FGConditions

/-!
# Chapter 5, §5.3: periodicity operators for Gorenstein algebras

Stable relation cycles, their rotations, the periodicity operators `χ_γ ∈ Ext*_Λ(k, k)`, and the
ring `R` they generate.

## Contents

* Definition 14: the period `ℓ` of `Λ`.
* Definition 15: stable relation cycles.
* Lemmas 3.1–3.4 (perfect walks of even length, perfect rewriting, recognition), Corollary 3.5.
* Associated sets of rotations, Lemma 3.6 (completeness), Lemma 3.7 (rigidity).
* Definition 16 and Proposition 3.8: periodicity operators are A∞-central.
* Definition 17 (branch equivalence), Lemmas 3.9–3.12, Definition 18 (`ordᵢ`).
* Lemma 3.13 (product lemma), Lemma 3.14, Proposition 3.15, Proposition 3.16.

Throughout `d` stands for the Gorenstein dimension `dim Λ` and `ℓ` for the period.

Example 3 (`k[t]/(tⁿ)`, Gulliksen's operator) and the example of §5.3.5 are not stated.
-/

noncomputable section

namespace TamaroffPhd

open Classical MonomialData Quiv

variable {Q : Quiv} (R : Set (List Q.A))

/-- **Definition 14 (Period).** The period `ℓ` of `Λ`: the least common multiple of the periods
of the perfect cycles.

**Change.** Definition 14 defines `ℓ` as the least common multiple of the periods of
the minimal projective resolutions of the indecomposable non-projective Gorenstein-projective
modules. By Theorem 1.1 these modules are the `pΛ` for perfect paths `p`, resolved by the
periodic complexes (5.7) of their perfect cycles, so `ℓ` is the least common multiple of the
periods of the perfect cycles, which is the definition used here. -/
def periodΛ : ℕ := sInf {ℓ | 0 < ℓ ∧ ∀ ps, IsPerfectCycle R ps → cyclePeriod ps ∣ ℓ}

/-- **Definition 15 (Stable relation cycle).** An `(s-1)`-chain `γ` is a stable relation cycle
if (i) `s` is even and `s ≥ dim Λ + 1`, (ii) `s` is a multiple of `ℓ`, (iii) `γ = p₀ ⋯ p_{s-1}`
for a perfect cycle `(p₀, …, p_{s-1})` with `t_γ = p_{s-1}`, (iv) `γ = q₀ ⋯ q_{s-1}` for a perfect
cycle `(q₀, …, q_{s-1})` with `h_γ = q₀`.

**Gap (error).** Condition (i) is printed as "`s` is even and at most `dim Λ + 1`". Every use
needs the opposite inequality: the Recognition Lemma 3.4 derives stability from
`n ≥ dim Λ + 1`, Corollary 3.5 picks `s ≥ dim Λ + 1`, and Proposition 4.2 applies Lemma 3.4 to
walks of length `p ≥ dim Λ + 1`. With "at most", Lemma 3.4 is false for large `n`, and only
finitely many stable relation cycles would exist, whereas Lemma 3.14 (ii) needs `γⁿ` to be one
for all `n`. We formalize `s ≥ dim Λ + 1`. -/
def IsStableRelCycle (d s : ℕ) (γ : List Q.A) : Prop :=
  1 ≤ s ∧ γ ∈ (Q.data R).Chains (s - 1) ∧ Even s ∧ d + 1 ≤ s ∧ periodΛ R ∣ s ∧
  (∃ ps, IsPerfectCycle R ps ∧ ps.length = s ∧ γ = ps.flatten ∧
    (Q.data R).tail (s - 1) γ = ps.getLastD []) ∧
  (∃ qs, IsPerfectCycle R qs ∧ qs.length = s ∧ γ = qs.flatten ∧
    (Q.data R).head (s - 1) γ = qs.headD [])

/-! ## Perfect walks of even length (§5.3.1) -/

/-- **Lemma 3.1.** For a perfect walk `(w₀, …, w_{n-1})` of even length `n`, `γ = w₀ ⋯ w_{n-1}` is
an `(n-1)`-chain and `w_{n-1}` is a right divisor of `t_γ`. -/
theorem lemma_3_1 (hR : (Q.data R).IsMinimal) {ws : List (List Q.A)} (hw : IsPerfectWalk R ws)
    (hev : Even ws.length) :
    ws.flatten ∈ (Q.data R).Chains (ws.length - 1) ∧
      ws.getLastD [] <:+ (Q.data R).tail (ws.length - 1) ws.flatten := by
  sorry

/-- **Lemma 3.2 (i).** For an `(n-1)`-chain `γ = w₀ ⋯ w_{n-1}` given by a perfect walk of even
length, the relations `r₀ = w₀w₁, r₂ = w₂w₃, …` do not depend on the walk. -/
theorem lemma_3_2_i (hR : (Q.data R).IsMinimal) {ws ws' : List (List Q.A)}
    (hw : IsPerfectWalk R ws) (hw' : IsPerfectWalk R ws') (hlen : ws.length = ws'.length)
    (hev : Even ws.length) (heq : ws.flatten = ws'.flatten) (i : ℕ) (hi : 2 * i + 1 < ws.length) :
    ws.getD (2 * i) [] ++ ws.getD (2 * i + 1) [] = ws'.getD (2 * i) [] ++ ws'.getD (2 * i + 1) [] := by
  sorry

/-- **Lemma 3.2 (ii).** Two perfect walks of the same even length with the same first relation,
or the same last relation, give the same chain. -/
theorem lemma_3_2_ii (hR : (Q.data R).IsMinimal) {ws ws' : List (List Q.A)}
    (hw : IsPerfectWalk R ws) (hw' : IsPerfectWalk R ws') (hlen : ws.length = ws'.length)
    (hev : Even ws.length) (h2 : 2 ≤ ws.length)
    (hrel : ws.getD 0 [] ++ ws.getD 1 [] = ws'.getD 0 [] ++ ws'.getD 1 [] ∨
      ws.getD (ws.length - 2) [] ++ ws.getLastD [] = ws'.getD (ws.length - 2) [] ++ ws'.getLastD []) :
    ws.flatten = ws'.flatten := by
  sorry

/-- **Lemma 3.3 (Perfect rewriting).** Let `γ = w₀ ⋯ w_{n-1}` for a perfect walk of even length
`n`. (i) If `t_γ` is perfect, `γ` is given by the perfect walk ending in `p_{n-1} = t_γ`.
(ii) If `h_γ` is perfect, by the perfect walk starting at `q₀ = h_γ`. -/
theorem lemma_3_3 (hR : (Q.data R).IsMinimal) {ws : List (List Q.A)} (hw : IsPerfectWalk R ws)
    (hev : Even ws.length) :
    (IsPerfect R ((Q.data R).tail (ws.length - 1) ws.flatten) →
      ∃ ps, IsPerfectWalk R ps ∧ ps.length = ws.length ∧ ps.flatten = ws.flatten ∧
        ps.getLastD [] = (Q.data R).tail (ws.length - 1) ws.flatten) ∧
    (IsPerfect R ((Q.data R).head (ws.length - 1) ws.flatten) →
      ∃ qs, IsPerfectWalk R qs ∧ qs.length = ws.length ∧ qs.flatten = ws.flatten ∧
        qs.headD [] = (Q.data R).head (ws.length - 1) ws.flatten) := by
  sorry

variable (k : Type) [Field k]

/-- **Lemma 3.4 (Recognition Lemma).** For a perfect walk `(w₀, …, w_{n-1})` over a Gorenstein
algebra of dimension `d`, with `n ≥ d + 1` even and divisible by `ℓ`, `w₀ ⋯ w_{n-1}` is a stable
relation cycle. -/
theorem lemma_3_4 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d : ℕ} (hd : gorDim R k = d)
    {ws : List (List Q.A)} (hw : IsPerfectWalk R ws) (hn : d + 1 ≤ ws.length)
    (hev : Even ws.length) (hℓ : periodΛ R ∣ ws.length) :
    IsStableRelCycle R d ws.length ws.flatten := by
  sorry

/-- **Corollary 3.5.** Every perfect path `p` is the first path `p₀` (and also the last path
`p_{s-1}`) of a stable relation cycle `p₀ ⋯ p_{s-1}`. -/
theorem cor_3_5 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d : ℕ} (hd : gorDim R k = d) {p : List Q.A} (hp : IsPerfect R p) :
    (∃ ws, IsPerfectWalk R ws ∧ ws.headD [] = p ∧ IsStableRelCycle R d ws.length ws.flatten) ∧
    (∃ ws, IsPerfectWalk R ws ∧ ws.getLastD [] = p ∧ IsStableRelCycle R d ws.length ws.flatten) := by
  sorry

/-! ## Rotating stable relation cycles (§5.3.2) -/

/-- **§5.3.2 (Associated set).** The rotations of a stable relation cycle `γ = a₀ ⋯ a_{n-1}`
(substrings `a_j ⋯ a_{j+n-1}` of the periodic string `⋯ a₀ ⋯ a_{n-1} a₀ ⋯`) that are again stable
relation cycles of the same Anick degree. -/
def assocSet (d s : ℕ) (γ : List Q.A) : Set (List Q.A) :=
  {γ' | ∃ j < γ.length, γ' = γ.rotate j ∧ IsStableRelCycle R d s γ'}

/-- **§5.3.2.** `γ ∼ γ'`: the stable relation cycles have the same associated set. -/
def RotEquiv (d s : ℕ) (γ γ' : List Q.A) : Prop := assocSet R d s γ = assocSet R d s γ'

/-- **Lemma 3.6 (Completeness).** For a stable relation cycle `γ = p₀ ⋯ p_{s-1} = q₀ ⋯ q_{s-1}`,
every rotation `p_k ⋯ p_{k+s-1}` (and `q_k ⋯ q_{k+s-1}`) of the perfect cycle is in the
associated set. -/
theorem lemma_3_6 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s : ℕ} (hd : gorDim R k = d) {γ : List Q.A}
    (hγ : IsStableRelCycle R d s γ) {ps : List (List Q.A)} (hps : IsPerfectCycle R ps)
    (hlen : ps.length = s) (hflat : γ = ps.flatten) (j : ℕ) :
    (ps.rotate j).flatten ∈ assocSet R d s γ := by
  sorry

/-- **Lemma 3.7 (Rigidity Lemma).** For a path `α` and `k ≥ 1`, `γᵢ α` is an `(s-1+k)`-chain for
at most one `γᵢ` in the associated set (and likewise `α γᵢ`). -/
theorem lemma_3_7 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s : ℕ} (hd : gorDim R k = d) {γ : List Q.A}
    (hγ : IsStableRelCycle R d s γ) (α : List Q.A) (j : ℕ) (hj : 1 ≤ j) :
    {γ' | γ' ∈ assocSet R d s γ ∧ γ' ++ α ∈ (Q.data R).Chains (s - 1 + j)}.Subsingleton ∧
    {γ' | γ' ∈ assocSet R d s γ ∧ α ++ γ' ∈ (Q.data R).Chains (s - 1 + j)}.Subsingleton := by
  sorry

/-! ## Periodicity operators (§5.3.3) -/

/-- **Definition 16 (Periodicity operator).** `χ_γ = ∑ᵢ γᵢ∨ ∈ Extˢ_Λ(k, k)`, the sum over the
associated set of the stable relation cycle `γ`. -/
def chiOp (d s : ℕ) (γ : List Q.A) : E k Q R :=
  ∑ᶠ c : {c : (Q.data R).Chain // c.deg = s - 1 ∧ c.word ∈ assocSet R d s γ},
    Finsupp.single (Sum.inr c.val) 1

/-- **Proposition 3.8.** For a Gorenstein monomial algebra, every periodicity operator `χ_γ` is
A∞-central, and so lies in the image of Hochschild cohomology. -/
theorem prop_3_8 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s : ℕ} (hd : gorDim R k = d) {γ : List Q.A}
    (hγ : IsStableRelCycle R d s γ) :
    IsAInfCentral k Q R s (chiOp R k d s γ) := by
  sorry

/-! ## The ring of periodicity operators (§5.3.4) -/

/-- The `n`-th power `γⁿ` of a path (concatenation). -/
def pathPow (γ : List Q.A) (n : ℕ) : List Q.A := (List.replicate n γ).flatten

/-- A stable relation cycle of some degree. -/
def IsStable (d : ℕ) (γ : List Q.A) : Prop := ∃ s, IsStableRelCycle R d s γ

/-- The Anick degree `s - 1` of a stable relation cycle, as `s`. -/
def stableS (d : ℕ) (γ : List Q.A) : ℕ := if h : IsStable R d γ then h.choose else 0

/-- **Definition 17 (Branch equivalence).** `γ₁ ≈ γ₂` if `γ₁^{n₁} ∼ γ₂^{n₂}` for some
`n₁, n₂ ≥ 1`. -/
def BranchEquiv (d : ℕ) (γ₁ γ₂ : List Q.A) : Prop :=
  ∃ n₁ n₂, 1 ≤ n₁ ∧ 1 ≤ n₂ ∧ IsStable R d (pathPow γ₁ n₁) ∧
    RotEquiv R d (stableS R d (pathPow γ₁ n₁)) (pathPow γ₁ n₁) (pathPow γ₂ n₂)

/-- **Lemma 3.9.** Stable relation cycles with the same tail, or the same head, are branch
equivalent. -/
theorem lemma_3_9 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s₁ s₂ : ℕ} (hd : gorDim R k = d) {γ₁ γ₂ : List Q.A}
    (h₁ : IsStableRelCycle R d s₁ γ₁) (h₂ : IsStableRelCycle R d s₂ γ₂)
    (h : (Q.data R).tail (s₁ - 1) γ₁ = (Q.data R).tail (s₂ - 1) γ₂ ∨
      (Q.data R).head (s₁ - 1) γ₁ = (Q.data R).head (s₂ - 1) γ₂) :
    BranchEquiv R d γ₁ γ₂ := by
  sorry

/-- **Lemma 3.10.** There are finitely many branch equivalence classes: finitely many stable
relation cycles represent all of them. -/
theorem lemma_3_10 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d : ℕ} (hd : gorDim R k = d) :
    ∃ F : Finset (List Q.A), (∀ γ ∈ F, IsStable R d γ) ∧
      ∀ γ, IsStable R d γ → ∃ γ₀ ∈ F, BranchEquiv R d γ γ₀ := by
  sorry

/-- The gcd `gcdᵢ` of the path lengths in the branch class of `γ₀` (5.33). -/
def classGcd (d : ℕ) (γ₀ : List Q.A) : ℕ :=
  sSup {g | ∀ γ, IsStable R d γ → BranchEquiv R d γ γ₀ → g ∣ γ.length}

/-- **Definition 18 (`ordᵢ`).** `ordᵢ(γ) = len(γ) / gcdᵢ` if `γ` is in the branch class of `γ₀`,
and `-∞` (here `none`) otherwise. -/
def ord (d : ℕ) (γ₀ γ : List Q.A) : Option ℕ :=
  if BranchEquiv R d γ γ₀ then some (γ.length / classGcd R d γ₀) else none

/-- **Lemma 3.11.** For `γ₁, γ₂` in the same branch class, `γ₁ ∼ γ₂` iff
`ordᵢ(γ₁) = ordᵢ(γ₂)`. -/
theorem lemma_3_11 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s₁ s₂ : ℕ} (hd : gorDim R k = d) {γ₀ γ₁ γ₂ : List Q.A}
    (h₁ : IsStableRelCycle R d s₁ γ₁) (h₂ : IsStableRelCycle R d s₂ γ₂)
    (hb₁ : BranchEquiv R d γ₁ γ₀) (hb₂ : BranchEquiv R d γ₂ γ₀) :
    RotEquiv R d s₁ γ₁ γ₂ ↔ ord R d γ₀ γ₁ = ord R d γ₀ γ₂ := by
  sorry

/-- **Lemma 3.12.** Branch-equivalent stable relation cycles have the same Anick degree iff
they are rotation-equivalent. -/
theorem lemma_3_12 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s₁ s₂ : ℕ} (hd : gorDim R k = d) {γ₁ γ₂ : List Q.A}
    (h₁ : IsStableRelCycle R d s₁ γ₁) (h₂ : IsStableRelCycle R d s₂ γ₂)
    (hb : BranchEquiv R d γ₁ γ₂) :
    s₁ = s₂ ↔ RotEquiv R d s₁ γ₁ γ₂ := by
  sorry

/-- **Lemma 3.13 (Product lemma).** If `γ₁`, `γ₂` and `γ₂γ₁` are stable relation cycles, then
(i) `γ₁ ≈ γ₂ ≈ γ₂γ₁`, and (ii) for `γ̃₂ ∼ γ₂`, `γ̃₁ ∼ γ₁` with `γ̃₂γ̃₁` stable,
`γ̃₂γ̃₁ ∼ γ₂γ₁`. -/
theorem lemma_3_13 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s₁ s₂ : ℕ} (hd : gorDim R k = d) {γ₁ γ₂ : List Q.A}
    (h₁ : IsStableRelCycle R d s₁ γ₁) (h₂ : IsStableRelCycle R d s₂ γ₂)
    (h₃ : IsStableRelCycle R d (s₁ + s₂) (γ₂ ++ γ₁)) :
    (BranchEquiv R d γ₁ γ₂ ∧ BranchEquiv R d γ₂ (γ₂ ++ γ₁)) ∧
    ∀ γ₁' γ₂', RotEquiv R d s₁ γ₁ γ₁' → RotEquiv R d s₂ γ₂ γ₂' →
      IsStableRelCycle R d (s₁ + s₂) (γ₂' ++ γ₁') →
      RotEquiv R d (s₁ + s₂) (γ₂' ++ γ₁') (γ₂ ++ γ₁) := by
  sorry

/-- **Lemma 3.14 (Product decompositions for associated sets).** If `γ₃ = γ₂γ₁` with all three
stable, then (i) `S₃ = S₂ · S₁`: each element of `S₃` is `γ̃₂γ̃₁` for unique `γ̃ᵢ ∈ Sᵢ`, and
each `γ̃₂ ∈ S₂` (resp. `γ̃₁ ∈ S₁`) has a unique compatible partner; (ii) the associated set of
`γⁿ` consists of the `γ̃ⁿ` with `γ̃ ∼ γ`. -/
theorem lemma_3_14 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s₁ s₂ : ℕ} (hd : gorDim R k = d) {γ₁ γ₂ : List Q.A}
    (h₁ : IsStableRelCycle R d s₁ γ₁) (h₂ : IsStableRelCycle R d s₂ γ₂)
    (h₃ : IsStableRelCycle R d (s₁ + s₂) (γ₂ ++ γ₁)) :
    (∀ γ₃' ∈ assocSet R d (s₁ + s₂) (γ₂ ++ γ₁), ∃! p : List Q.A × List Q.A,
      p.2 ∈ assocSet R d s₂ γ₂ ∧ p.1 ∈ assocSet R d s₁ γ₁ ∧ γ₃' = p.2 ++ p.1) ∧
    (∀ γ₂' ∈ assocSet R d s₂ γ₂, ∃! γ₁', γ₁' ∈ assocSet R d s₁ γ₁ ∧
      γ₂' ++ γ₁' ∈ assocSet R d (s₁ + s₂) (γ₂ ++ γ₁)) ∧
    (∀ γ₁' ∈ assocSet R d s₁ γ₁, ∃! γ₂', γ₂' ∈ assocSet R d s₂ γ₂ ∧
      γ₂' ++ γ₁' ∈ assocSet R d (s₁ + s₂) (γ₂ ++ γ₁)) := by
  sorry

/-- **Lemma 3.14 (ii).** The associated set of `γⁿ` is `{γ̃ⁿ | γ̃ ∼ γ}`. -/
theorem lemma_3_14_ii (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s : ℕ} (hd : gorDim R k = d) {γ : List Q.A}
    (hγ : IsStableRelCycle R d s γ) (n : ℕ) (hn : 1 ≤ n) :
    assocSet R d (n * s) (pathPow γ n) = (pathPow · n) '' assocSet R d s γ := by
  sorry

/-- **Proposition 3.15.** (i) If `χ_{γ₁} · χ_{γ₂} ≠ 0` then `γ₁ ≈ γ₂`. (ii) If `γ₁ ≈ γ₂`, then
`χ_{γ₁} · χ_{γ₂} = χ_{γ₃}` for some `γ₃ ≈ γ₁`, with `ordᵢ` additive. (iii) `χ_γⁿ = χ_{γⁿ}`. -/
theorem prop_3_15 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s₁ s₂ : ℕ} (hd : gorDim R k = d) {γ₁ γ₂ : List Q.A}
    (h₁ : IsStableRelCycle R d s₁ γ₁) (h₂ : IsStableRelCycle R d s₂ γ₂) :
    (mul2 k Q R (chiOp R k d s₁ γ₁) (chiOp R k d s₂ γ₂) ≠ 0 → BranchEquiv R d γ₁ γ₂) ∧
    (BranchEquiv R d γ₁ γ₂ → ∃ γ₃, IsStableRelCycle R d (s₁ + s₂) γ₃ ∧ BranchEquiv R d γ₃ γ₁ ∧
      mul2 k Q R (chiOp R k d s₁ γ₁) (chiOp R k d s₂ γ₂) = chiOp R k d (s₁ + s₂) γ₃ ∧
      γ₃.length = γ₁.length + γ₂.length) ∧
    ∀ n, 1 ≤ n → mulPow k Q R (chiOp R k d s₁ γ₁) n = chiOp R k d (n * s₁) (pathPow γ₁ n) := by
  sorry

/-- The ring `R = k⟨χ_γ | γ⟩ ⊆ Ext*_Λ(k, k)` generated by the periodicity operators. -/
def periodicityRing (d : ℕ) : Submodule k (E k Q R) :=
  genAlg k Q R {x | ∃ s γ, IsStableRelCycle R d s γ ∧ x = chiOp R k d s γ}

/-- The numerical semigroup `N_Γ` of a branch class (5.33): the values of `ordᵢ`. -/
def semigroupOf (d : ℕ) (γ₀ : List Q.A) : Set ℕ :=
  {n | ∃ γ, IsStable R d γ ∧ ord R d γ₀ γ = some n}

/-- **Proposition 3.16.** For a Gorenstein monomial algebra of infinite global dimension (there are
chains in every degree, by Theorem 3.3.2), with
branch classes represented by `γ₁, …, γ_b`, there is an injective multiplicative linear map
`φ : R → ∏ᵢ k[tᵢ]`, `χ_γ ↦ tᵢ^{ordᵢ(γ)}` (in the `i`-th factor, for `γ` in the `i`-th class),
whose image is the fibre product `k[t₁^{N_{Γ₁}}] ×_k ⋯ ×_k k[t_b^{N_{Γ_b}}]`. In particular `R`
is Noetherian, reduced, of Krull dimension one. -/
theorem prop_3_16 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d : ℕ} (hd : gorDim R k = d)
    (hgl : ∀ n, ∃ γ, γ ∈ (Q.data R).Chains n)
    (b : ℕ) (reps : Fin b → List Q.A) (hreps : ∀ i, IsStable R d (reps i))
    (hcover : ∀ γ, IsStable R d γ → ∃! i, BranchEquiv R d γ (reps i)) :
    ∃ φ : periodicityRing R k d →ₗ[k] (Fin b → Polynomial k),
      Function.Injective φ ∧
      (∀ x y : periodicityRing R k d, ∀ h : mul2 k Q R x y ∈ periodicityRing R k d,
        φ ⟨mul2 k Q R x y, h⟩ = φ x * φ y) ∧
      (∀ s γ, ∀ (h : IsStableRelCycle R d s γ) (i : Fin b), BranchEquiv R d γ (reps i) →
        ∀ hm, φ ⟨chiOp R k d s γ, hm⟩ = Pi.single i
          (Polynomial.monomial ((ord R d (reps i) γ).getD 0) 1)) ∧
      Set.range φ = {f | (∀ i, ∀ n ∈ (f i).support, n = 0 ∨ n ∈ semigroupOf R d (reps i)) ∧
        ∀ i j, (f i).coeff 0 = (f j).coeff 0} := by
  sorry

end TamaroffPhd

end
