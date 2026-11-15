import TamaroffPhd.PreliminariesChenShenZhou
import TamaroffPhd.PreliminariesGorensteinAlgebras

/-!
# Chapter 5, §5.1.2–5.1.4: Anick chains over Gorenstein monomial algebras

## Contents

* Theorem 1.6: `Λ` is Gorenstein of dimension at most `d + 1` iff the tails (or heads) of the
  `d`-chains have at most one minimal zero cofactor, which is perfect.
* Corollary 1.7: `Λ` is Gorenstein iff high chains have perfect tails (or heads).
* Proposition 1.8: local Gorenstein monomial algebras are `k[t]/(tⁿ)`.
* Corollary 1.12: high chains over a Gorenstein algebra are extended by perfect walks.

Proposition 1.2 (Gorenstein in terms of the syzygies `Ωⁿk`, via Bergh–Jorgensen–Oppermann
[17, Th. 4.1]) and Lemma 1.5 (projective summands of syzygies) are steps in the proof of
Theorem 1.6 about general syzygy modules. They are not stated, since syzygies are only
available here through the Anick resolution (Proposition 1.3). The example `Λ_d` of §5.1.3 is
not stated because its quiver is only given in a figure.
-/

noncomputable section

namespace TamaroffPhd

open Classical MonomialData CategoryTheory Quiv

variable {Q : Quiv} (R : Set (List Q.A)) (k : Type) [Field k]

/-- **Theorem 1.6.** For a finite-dimensional monomial algebra and `d ≥ 0`, the following are
equivalent: (i) `Λ` is Gorenstein of dimension at most `d + 1`; (ii) for every `d`-chain `γ`,
`R(t_γ)` is empty or `{p}` with `p` perfect; (iii) for every `d`-chain `γ`, `L(h_γ)` is empty or
`{q}` with `q` perfect.

Because `IsChain` in Lean drops the overlap condition of
Definition 25, `(i) → (ii)` fails at `d = 1`: take `Q` with vertices `x, y, z`, arrows
`a : x → y`, `b : y → y`, `c : y → z`, and `R = {[b, b]}`. Here `Λ` is finite-dimensional
(`dim Λ = 9`), `R` is minimal, and `IsGorensteinLE R k 2` holds (in fact `gorDim = 1`), yet
`[a, b, b] ∈ Chains 1` has `tail 1 [a, b, b] = [b, b]`, for which `rightCof R [b, b] = {[b], [c]}`
has size `2` (neither empty nor a singleton). -/
theorem theorem_1_6 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R)) (d : ℕ) :
    (IsGorensteinLE R k (d + 1) ↔
      ∀ γ ∈ (Q.data R).Chains d, rightCof R ((Q.data R).tail d γ) = ∅ ∨
        ∃ p, rightCof R ((Q.data R).tail d γ) = {p} ∧ IsPerfect R p) ∧
    (IsGorensteinLE R k (d + 1) ↔
      ∀ γ ∈ (Q.data R).Chains d, leftCof R ((Q.data R).head d γ) = ∅ ∨
        ∃ q, leftCof R ((Q.data R).head d γ) = {q} ∧ IsPerfect R q) := by
  sorry

/-- **Theorem 1.6 (last claim).** If `dim Λ < d + 1`, then the tail `t_γ` and the head `h_γ` of
every `d`-chain are perfect.

Fails at `d = 1` under Lean's `IsChain`: on the quiver
`x —a→ y —b→ y —c→ z` (`b` a loop at `y`) with `R = {[b, b]}`, `IsGorensteinLE R k 1` holds
(`gorDim = 1`), yet `[a, b, b] ∈ Chains 1` has `tail 1 [a, b, b] = [b, b]` (zero in `Λ`, hence
not perfect) and `head 1 [a, b, b] = []` (also not perfect). -/
theorem theorem_1_6_perfect (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (d : ℕ) (hd : IsGorensteinLE R k d) :
    ∀ γ ∈ (Q.data R).Chains d, IsPerfect R ((Q.data R).tail d γ) ∧
      IsPerfect R ((Q.data R).head d γ) := by
  sorry

/-- **Corollary 1.7.** `Λ` is Gorenstein iff there is `n₀` such that every `n`-chain with
`n ≥ n₀` has a perfect tail, iff the same holds for heads. -/
theorem cor_1_7 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R)) :
    (IsGorenstein R k ↔ ∃ n₀, ∀ n ≥ n₀, ∀ γ ∈ (Q.data R).Chains n,
      IsPerfect R ((Q.data R).tail n γ)) ∧
    (IsGorenstein R k ↔ ∃ n₀, ∀ n ≥ n₀, ∀ γ ∈ (Q.data R).Chains n,
      IsPerfect R ((Q.data R).head n γ)) := by
  sorry

/-- **Proposition 1.8.** A local finite-dimensional monomial algebra `k⟨S⟩/I` (one vertex,
`S` non-empty) is Gorenstein iff it is `k[t]/(tⁿ)` for some `n ≥ 2`: there is one arrow and the
single relation is a power of it.

"`Λ ≅ k[t]/(tⁿ)`" is stated combinatorially, as the presentation having one arrow and relation
`tⁿ`; for minimal monomial presentations the two are equivalent. -/
theorem prop_1_8 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hV : Fintype.card Q.V = 1) (hA : Nonempty Q.A) :
    IsGorenstein R k ↔ Fintype.card Q.A = 1 ∧ ∃ n ≥ 2, ∃ t : Q.A, R = {List.replicate n t} := by
  sorry

/-- **Corollary 1.12.** Let `Λ` be Gorenstein of dimension `d ≥ 1` and `γ` an `n`-chain with
`n ≥ d`. There are a `(d-1)`-chain `γ_{d-1}` and a perfect walk `(p_d, …, pₙ)` such that each
`γ_{d-1} p_d ⋯ pᵢ` is an `i`-chain with tail `pᵢ`, and `γ = γ_{d-1} p_d ⋯ pₙ`.

Fails at `d = n = 1` under Lean's `IsChain`: on
`x —a→ y —b→ y —c→ z` (`R = {[b, b]}`, `gorDim = 1`), `γ = [a, b, b] ∈ Chains 1` has no
decomposition `γ = γ₀ ++ [p₁]` with `γ₀ ∈ Chains 0` and `IsPerfect R p₁` (the only
`0`-chain prefix leaves `p₁ = [b, b]`, which is zero in `Λ` and not perfect). -/
theorem cor_1_12 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) (d : ℕ) (hd : 1 ≤ d) (hdim : gorDim R k = d)
    (n : ℕ) (hn : d ≤ n) (γ : List Q.A) (hγ : γ ∈ (Q.data R).Chains n) :
    ∃ γ₀ ∈ (Q.data R).Chains (d - 1), ∃ ws : List (List Q.A),
      IsPerfectWalk R ws ∧ ws.length = n - d + 1 ∧ γ = γ₀ ++ ws.flatten ∧
      ∀ i < ws.length, (Q.data R).IsChain (d + i) (γ₀ ++ (ws.take (i + 1)).flatten) (ws.getD i []) := by
  sorry

/-- **Corollary 1.12 (ii).** Dually, `γ = q₋ₙ ⋯ q₋_d γ_{d-1}` for a perfect walk read from the
left, each `q₋ᵢ ⋯ q₋_d γ_{d-1}` an `i`-chain with head `q₋ᵢ`.

**Gap (typo).** In the second bullet of Corollary 1.12 (ii), the thesis prints
`γ_n = q_{-n} q_{-n+1} ... q_d γ_{d-1}` with `q_d` instead of `q_{-d}`.

Lean avoids the indexed notation by using a list `ws`, omits the condition that
`q_{-i} ⋯ q_{-d} γ_{d-1}` is an `i`-chain with head `q_{-i}` for `d ≤ i ≤ n`, and fails at
`d = n = 1` under Lean's `IsChain` for the same example `x —a→ y —b→ y —c→ z` (`R = {[b, b]}`,
`γ = [a, b, b] ∈ Chains 1`). -/
theorem cor_1_12_left (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) (d : ℕ) (hd : 1 ≤ d) (hdim : gorDim R k = d)
    (n : ℕ) (hn : d ≤ n) (γ : List Q.A) (hγ : γ ∈ (Q.data R).Chains n) :
    ∃ γ₀ ∈ (Q.data R).Chains (d - 1), ∃ ws : List (List Q.A),
      IsPerfectWalk R ws ∧ ws.length = n - d + 1 ∧ γ = ws.flatten ++ γ₀ := by
  sorry

end TamaroffPhd

end
