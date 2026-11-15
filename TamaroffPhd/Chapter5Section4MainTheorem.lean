import TamaroffPhd.Chapter5Section3PeriodicityOperators

/-!
# Chapter 5, §5.4–5.5: the main theorem and further results

## Contents

* Lemma 4.1, Proposition 4.2 (periodicity of `Ext*_Λ(k, k)` under `χ`).
* Theorem 4.3: a monomial algebra satisfies FG (here FG′) iff it is Gorenstein.
* Theorem 5.1: decidable combinatorial criteria for FG.
* Hochschild cohomology `HH*(Λ, Λ) = Ext*_{Λᵉ}(Λ, Λ)` and Theorem 5.2: it is eventually
  periodic.

Corollary 5.3 (Tate–Hochschild cohomology is `HH*(Λ, Λ)[χ⁻¹]`) is not stated: Mathlib has no
singularity categories.
-/

noncomputable section

namespace TamaroffPhd

open Classical MonomialData CategoryTheory Quiv TensorProduct

variable {Q : Quiv} (R : Set (List Q.A)) (k : Type) [Field k]

/-- **Lemma 4.1.** Let `w` be a perfect path and `γ = w₀ ⋯ w_{s-1}` a stable relation cycle with
`w = w_{s-1}`, of minimal path length among such. Then `ordᵢ(γ)` is the minimum of `N_{Γᵢ}` for
its branch class. -/
theorem lemma_4_1 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d s : ℕ} (hd : gorDim R k = d) {w : List Q.A} (hw : IsPerfect R w)
    {ws : List (List Q.A)} (hws : IsPerfectWalk R ws) (hlast : ws.getLastD [] = w)
    (hγ : IsStableRelCycle R d s ws.flatten)
    (hmin : ∀ ws' s', IsPerfectWalk R ws' → ws'.getLastD [] = w →
      IsStableRelCycle R d s' ws'.flatten → ws.flatten.length ≤ ws'.flatten.length)
    (γ₀ : List Q.A) (hb : BranchEquiv R d ws.flatten γ₀) :
    ∀ n ∈ semigroupOf R d γ₀, ws.flatten.length / classGcd R d γ₀ ≤ n := by
  sorry

/-- **Proposition 4.2.** For a Gorenstein monomial algebra of dimension `d` and infinite global
dimension, there is a homogeneous `χ` of even degree `p > 0`, a multiple of `ℓ`, in the ring `R`
of periodicity operators, such that `χ · - : Extⁿ_Λ(k, k) → Ext^{n+p}_Λ(k, k)` is an isomorphism
for `n ≥ d + 1` and an epimorphism for `n = d`.

The thesis fixes the class `χ` of (5.35), built from the minimal periodicity operators of
the branch classes. Lean states Proposition 4.2 for some homogeneous `χ ∈ R` of degree `p` (a
multiple of `ℓ`), which is how Theorems 4.3 and 5.2 use it, and adds `hgl : ∀ n, ∃ γ, γ ∈ Chains n`
(`gldim Λ = ∞`; the finite-global-dimension case is trivial with `χ = 0` in the thesis).

False under Lean's `IsChain`: on the quiver
`x —a→ y —b→ y —c→ z` (`b` a loop at `y`) with `R = {[b, b]}` (`gorDim = 1`), `[b]` is the
unique perfect cycle, so every `χ ∈ periodicityRing R k 1 ∩ Ehom p` (`p ≥ 2` even) is a scalar
multiple of `eb (.inr [b]^p)`. Then `mul2 χ` sends `Ehom 1 = span {[a], [b], [c]}` into
`span {[b]^{p+1}}` (dimension `1`, since `[a] ++ [b]^p ∈ Chains (p - 1)`, not `Chains p`), whereas
`Ehom (1 + p)` (`Chains p`) contains both `[b]^{p+1}` and `[a, b^{p+1}]` (dimension `2`), so
`Set.SurjOn (mul2 χ) (Ehom 1) (Ehom (1 + p))` fails. -/
theorem prop_4_2 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d : ℕ} (hd : gorDim R k = d)
    (hgl : ∀ n, ∃ γ, γ ∈ (Q.data R).Chains n) :
    ∃ p χ, 0 < p ∧ Even p ∧ periodΛ R ∣ p ∧ χ ∈ periodicityRing R k d ∧ χ ∈ Ehom k Q R p ∧
      (∀ n ≥ d + 1, Set.BijOn (mul2 k Q R χ) (Ehom k Q R n) (Ehom k Q R (n + p))) ∧
      Set.SurjOn (mul2 k Q R χ) (Ehom k Q R d) (Ehom k Q R (d + p)) := by
  sorry

/-- **Theorem 4.3.** A finite-dimensional monomial algebra satisfies FG if and only if it is
Gorenstein. The implication FG ⇒ Gorenstein is Erdmann–Holloway–Snashall–Solberg–Taillefer
[59, Th. 1.5]; the converse is the main result of the chapter.

Under Lean's `IsChain`, `IsGorenstein R k → FG' k Q R`
fails on the `4`-cycle `0 —a→ 1 —b→ 2 —c→ 3 —d→ 0` with `R = {[a, b], [c, d]}`: here
`gldim Λ = 2 < ∞`, so `IsGorenstein R k` holds, yet `Chains n` is non-empty for all `n` (two
chains of length `2n` and two of length `2n + 1`), making `E k Q R` infinite-dimensional while
`mul2` vanishes on `Ehom (≥ 2) × Ehom (≥ 2)` and `ZInf ∩ Ehom 1 = 0`. Thus any finitely
generated subalgebra `ZInf` is finite-dimensional and cannot finitely generate the
infinite-dimensional space `E k Q R`, so `FG' k Q R` is false. -/
theorem theorem_4_3 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R)) :
    FG' k Q R ↔ IsGorenstein R k := by
  sorry

/-- **Theorem 5.1.** For a finite-dimensional monomial algebra the following are equivalent:
(1) FG; (2) Gorenstein; (3) every `n`-chain has a perfect tail, `n = rfindim Λ`; (4) every
`n`-chain has a perfect head, `n = lfindim Λ`; (5), (6) the same with `n = n_Λ`.

Takes explicit natural-number witnesses `{nr nl : ℕ}` for `rfindim R k = nr` and
`lfindim R k = nl` (which exist for non-empty finite-dimensional algebras by `findim_finite`).

Under Lean's `IsChain`, the theorem fails: on `x —a→ y —b→ y —c→ z`
with `R = {[b, b]}`, `IsGorenstein R k` holds with `rfindim = lfindim = gorDim = 1`, yet
`[a, b, b] ∈ Chains 1` has `tail 1 [a, b, b] = [b, b]` and `head 1 [a, b, b] = []`, neither of
which is perfect; and on the `4`-cycle with `R = {[a, b], [c, d]}`, (2) holds while (1) (`FG'`)
fails as in `theorem_4_3`. -/
theorem theorem_5_1 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    {nr nl : ℕ} (hnr : rfindim R k = nr) (hnl : lfindim R k = nl) :
    (FG' k Q R ↔ IsGorenstein R k) ∧
    (IsGorenstein R k ↔ ∀ γ ∈ (Q.data R).Chains nr, IsPerfect R ((Q.data R).tail nr γ)) ∧
    (IsGorenstein R k ↔ ∀ γ ∈ (Q.data R).Chains nl, IsPerfect R ((Q.data R).head nl γ)) ∧
    (IsGorenstein R k ↔ ∀ γ ∈ (Q.data R).Chains (nBound R k),
      IsPerfect R ((Q.data R).tail (nBound R k) γ)) ∧
    (IsGorenstein R k ↔ ∀ γ ∈ (Q.data R).Chains (nBound R k),
      IsPerfect R ((Q.data R).head (nBound R k) γ)) := by
  sorry

/-! ## Hochschild cohomology -/

/-- `Λ` as a module over the enveloping algebra `Λᵉ = Λᵒᵖ ⊗_k Λ`. -/
def diagonalModule : ModuleCat ((Q.PathAlg k R)ᵐᵒᵖ ⊗[k] Q.PathAlg k R) :=
  letI := TensorProduct.Algebra.module (R := k) (A := (Q.PathAlg k R)ᵐᵒᵖ)
    (B := Q.PathAlg k R) (M := Q.PathAlg k R)
  ModuleCat.of _ (Q.PathAlg k R)

/-- **§5.2.1.** Hochschild cohomology `HHⁿ(Λ, Λ) = Extⁿ_{Λᵉ}(Λ, Λ)`. -/
abbrev HH (n : ℕ) : Type := Abelian.Ext (diagonalModule R k) (diagonalModule R k) n

/-- **Theorem 5.2.** For a Gorenstein monomial algebra of dimension `d`, Hochschild cohomology
is eventually periodic: there is `χ ∈ HH^p(Λ, Λ)` of even degree `p > 0` such that cup product
with `χ` is an isomorphism `HHⁿ(Λ, Λ) → HH^{n+p}(Λ, Λ)` for all `n ≥ d + 1`.

On `HH*(Λ, Λ) = Ext*_{Λᵉ}(Λ, Λ)` the cup product agrees with the Yoneda product, so Theorem 5.2
is stated with `Ext.comp`. Lean also adds `hgl : ∀ n, ∃ γ, γ ∈ Chains n` (`gldim Λ = ∞`) and
`d : ℕ` (`gorDim R k = d`), whereas Theorem 5.2 in §5.5.2 does not explicitly assume infinite
global dimension (the finite case is trivial with `χ = 0` since `HHⁿ = 0` for `n ≥ dim Λ + 1`). -/
theorem theorem_5_2 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (hG : IsGorenstein R k) {d : ℕ} (hd : gorDim R k = d)
    (hgl : ∀ n, ∃ γ, γ ∈ (Q.data R).Chains n) :
    ∃ p, 0 < p ∧ Even p ∧ ∃ χ : HH R k p, ∀ n ≥ d + 1,
      Function.Bijective fun x : HH R k n => χ.comp x (show p + n = n + p by omega) := by
  sorry

end TamaroffPhd

end
