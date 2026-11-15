# Counterexample to Proposition 5.2.21 and Theorem 5.2.20

The **printed sequential-limit preservation hypotheses** in these two results are
insufficient. The counterexample below is checked in
[`FlowCompletenessCounterexample.lean`](FlowCompletenessCounterexample.lean).
It does **not** refute the proved strong-flow specializations now in the repository,
which also require preservation of all categorical limits.

## The category: positively labelled sets

An object is a set `X` with a function `ℓ_X : X → ℝ` such that `ℓ_X(x) > 0` for every
point. Empty sets are allowed. An ordinary morphism is a function preserving labels
exactly. An `ε`-morphism is a function `f : X → Y` such that

\[
|\ell_X(x)-\ell_Y(f(x))|\leq\varepsilon\qquad\text{for every }x\in X.
\]

Composition adds errors by the triangle inequality; increasing the permitted error
leaves the function unchanged. These operations define a locally persistent category.
In Lean, its objects are `Marked`, with explicit category and `LPCat` instances.

## Weak powers

Define

\[
T_\varepsilon X
 =\{(r,x): r>0,\ |r-\ell_X(x)|\leq\varepsilon\},
\qquad \ell_{T_\varepsilon X}(r,x)=r.
\]

An ordinary map `f : X → Y` induces `(r,x) ↦ (r,f(x))`. A label-preserving map
`X → T_ε Y` has the form `x ↦ (ℓ_X(x),f(x))`, and therefore corresponds bijectively
to an `ε`-morphism `X → Y`. More generally, forgetting the first coordinate sends
a `δ`-morphism into `T_ε Y` to an `(ε+δ)`-morphism into `Y`.

This is the weak power structure `weakPowers`, with power functor `thickening ε`.
The induced flow is `counterexampleFlow`; its interleaving distance agrees with the
locally persistent category's distance, by `powFlow_interleavingDist`.

## Sequential limits exist and are preserved

Consider an inverse sequence of ordinary maps

\[
\cdots\longrightarrow X_2\longrightarrow X_1\longrightarrow X_0.
\]

Its limit has the usual set of compatible threads `(x_n)`. All entries of a thread
have the same label, since the bonding maps preserve labels. Label the thread by
`ℓ_{X_0}(x_0)`. This is positive, and the projections and universal map preserve
labels. Thus the category has every sequential limit. The construction also handles
an empty set of compatible threads.

Now apply `T_ε` to the sequence. A compatible thread is a family `(r_n,x_n)` whose
first coordinates are all equal, because the thickened bonding maps keep the first
coordinate unchanged. The labels `ℓ_{X_n}(x_n)` are also all equal. Consequently,

\[
T_\varepsilon(\lim_n X_n)\cong\lim_n T_\varepsilon X_n.
\]

The isomorphism sends `(r,(x_n))` to `((r,x_n))`, in both directions preserving the
label `r`. Hence every weak power preserves sequential limits.

The Lean constructions are `threadCone`, `threadConeIsLimit`, and
`thickeningConeIsLimit`. The resulting `HasLimitsOfShape ℕᵒᵖ Marked` and
`PreservesLimitsOfShape ℕᵒᵖ (thickening ε)` instances are proved explicitly.

## A Cauchy sequence with no metric limit

Let `P_a` be a singleton labelled by `a > 0`. The unique functions between two
singletons give an `ε`-interleaving precisely when `|a-b| ≤ ε`. Thus

\[
d_I(P_a,P_b)=|a-b|.
\]

In particular, `P_{1/(n+1)}` is Cauchy.

Suppose it converged to a labelled set `L`. Eventually its distance from `L` would
be finite, so an interleaving would supply a function from a singleton to `L`.
Therefore `L` must be nonempty. Choose `x ∈ L`, and put `λ = ℓ_L(x) > 0`.

For any `ε`-interleaving between `P_a` and `L`, the reverse map `L → P_a` forces
`|a-λ| ≤ ε`. Taking the infimum over interleavings gives

\[
|a-\lambda|\leq d_I(P_a,L).
\]

Apply this to `a = 1/(n+1)`. Convergence in interleaving distance would imply
`1/(n+1) → λ`. But this real sequence tends to `0`, contradicting `λ > 0`.
There is no metric limit.

The relevant Lean results are `singletonSequence_cauchy`, `point_label_le_dist`,
`not_complete`, and `counterexampleFlow_not_complete`. The two bundled conclusions
are:

- `flow_counterexample`: the hypotheses printed in Theorem 5.2.20 hold, but flow
  completeness fails;
- `weak_power_counterexample`: the hypotheses printed in Proposition 5.2.21 hold,
  but completeness fails.

Their axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Neither proof uses the completeness statements being tested.

## Why Cruz's stronger hypothesis excludes this example

[Cruz, Theorem 4](https://arxiv.org/html/1901.04828#S3.SS2) asks the flow functors to
preserve categorical limits, rather than only the sequential limits stated in the
thesis. Our thickening fails to preserve a terminal object.

The terminal labelled set has one point at every positive label: its underlying
set is `(0,∞)`, and its label function is the identity. Every object has a unique
label-preserving map into it.

After applying `T_1`, there are at least two points with label `1`: the pairs
`(1,1)` and `(1,2)`. Thus there are two distinct ordinary maps from `P_1` into
`T_1` of the terminal object. That object is no longer terminal.

This failure is checked by `terminalMarkedIsTerminal`,
`thickening_terminal_not_terminal`, and `thickening_not_preserves_all_limits`.

## Correction and proof status

The formalized versions of **both** Theorem 5.2.20 and Proposition 5.2.21 now require:

- preservation of all categorical limits;
- a **strong flow**, meaning that the unit `Id → T₀` and all multiplication maps
  `T_ε T_δ → T_(ε+δ)` are natural isomorphisms. For Proposition 5.2.21 this is an
  explicit hypothesis on the flow induced by its chosen weak powers.

Their completeness conclusions are unchanged. These restricted versions are proved
without admissions. The proof reduces to
`Flow.interleavingDist_complete_of_strong`, which needs only sequential-limit
preservation. The all-limits assumption is retained in the numbered statements to
keep the earlier preservation correction explicit. The uniform Lean hypotheses include
parameter zero as well; Cruz phrases his preservation assumption for positive parameters.

The additional strength restriction goes beyond Cruz's preservation hypothesis.
The unrestricted general-flow completeness statement under that hypothesis is not
formalized here. Removing the admission by this specialization is not a proof of that
more general claim. The checked example above refutes the original sequential-only
claims; it does not refute Cruz's stronger claim. The lemma
`counterexampleFlow_not_strong` also verifies that the example is excluded by the
new strength hypothesis.

The kernel-density stability proofs in Section 6.5 do not use either completeness
statement and are unaffected by this counterexample or the stronger hypotheses.
