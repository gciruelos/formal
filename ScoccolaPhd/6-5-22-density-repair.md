# Repair of Theorem 6.5.22 and its downstream application

The corrected Theorem 6.5.22 is `kdf_uniformContinuous` in
[`Chapter6Section5KernelStability.lean`](Chapter6Section5KernelStability.lean).
Its uniform-kernel clause is `kdf_uniformKernel_lipschitz`. Neither uses an admission.

## The problem with the extension of Lemma 6.5.8

The thesis defines density on weighted dissimilarity spaces by the layer integral

```
ρ_X(s,x) = ∫_(0,∞) M_X(x, s K⁻¹(t)) dt.
```

For `t ≥ K(0)`, the inverse kernel is zero. Thus positive zero-radius mass produces
an infinite tail, even when every ball mass is bounded by a fixed finite constant.
The category `wDiss` allows such functions. The proof of Lemma 6.5.20 silently
discards this tail when restricting the integral to the kernel's height.

The repaired `WDiss.density` integrates over `(0, K(0)]`. The printed formula is
retained as `WDiss.untruncatedDensity` for comparison. The repaired density satisfies
`ρ_X(s,x) ≤ B K(0)` for every space bounded by `B`. No extra axiom is imposed on
`WDiss`, so its powers, pullbacks, and existing quotient-distance results remain available.

## Why the downstream filtration is unchanged

`WDiss.density_eq_untruncated` proves agreement whenever `M_X(x,0) = 0`.
For every metric probability space, the open ball of radius zero is empty;
`CompactMPS.toWDiss_mass_zero` and `CompactMPS.density_eq_untruncated` verify this
specialization in Lean. Thus this change to the weighted extension does not change
the filtration on the compact metric probability spaces in Theorem 6.5.1.

## Persistent structures and coordinates

The previous Lean outline allowed arbitrary locally persistent structures on both
categories and an arbitrary diagram with the correct objects. This did not specify
the intended distance or the diagram's structure maps. These are now fixed explicitly:

- `wDissLPCat` is change of enrichment of `wDissLQPCat` along `(1,1)`.
- `kdfCurried` is the actual filtration, written as `ℝ ⥤ ℝ ⥤ Diss`.
- The second increasing coordinate is `t = -k`, replacing the decreasing density
  threshold `k`. `kdfParameters` makes this index change explicit, and
  `kdfCurried_uncurry` proves equality with the product-indexed `kdfFunctor`
  after uncurrying and changing coordinates.
- `kdfLPCat` shifts bandwidth and `t` by `ε` and allows spatial distortion `ε`.
  Equivalently, it increases bandwidth, lowers the density threshold, and permits
  spatial error, all by `ε`: the thesis's direction `(1,1,1)`.
- `kdfAcyclic` means acyclic at every pair of parameters. `kdfMap_acyclic` proves
  that the filtration preserves acyclic maps.

These are concrete structures, not assumed continuity or interleaving estimates.

## Proof of the corrected stability theorem

For an approximate weighted map with error `δ`, choose a level `0 < a < K(0)`.
The inverse kernel is positive there. Given a bandwidth allowance `η`, assume
`δ ≤ η K⁻¹(a)`. For `0 < t ≤ a`, monotonicity of the inverse kernel gives

```
s K⁻¹(t) + δ ≤ (s + η) K⁻¹(t).
```

Integrate the weighted-morphism inequality over this interval. Bound the remaining
layer interval `(a,K(0)]` using the input mass bound `B`. This gives

```
ρ_X(s,x) ≤ ρ_Y(s+η,f(x)) + δ a + B (K(0)-a).
```

This is `WDiss.density_morphism_le`, the bounded-domain version of Lemma 6.5.20.
It follows the source's inverse-kernel comparison, but bounds a short tail rather
than rescaling the integration variable. Choose `a` close enough to `K(0)` to
make the tail small, then choose a positive `δ` small enough to control bandwidth,
spatial error, and the density threshold. `kdf_modulus` makes those choices explicit.

Apply the resulting maps in both directions of an input interleaving. Their
composites satisfy the interleaving equations because their underlying functions
are the original ones. Finally use the existing characterization of the input
quotient distance by interleavings of acyclic covers. Those covers inherit the
mass bound, and their images are again acyclic covers. This proves
`kdf_uniformContinuous` for every existing kernel and every bounded weighted space.

For the uniform kernel, the repaired density is exactly `M_X(x,s)`. The original
weighted-morphism inequality therefore gives the same output error as input error,
without a mass bound. This proves `kdf_uniformKernel_lipschitz`.

## Downstream results and the flow specialization

Theorem 6.5.1 (Theorem H) is now proved as `kdf_ghp_uniformContinuous`, by combining
Theorem 6.5.22 with the existing Theorem 6.5.23. Its uniform-kernel 2-Lipschitz clause
is `kdf_ghp_uniformKernel_lipschitz`. The source's next application, Corollary 6.5.2,
still requires the omitted persistent-homology construction; it has no Lean statement here.

Neither stability proof uses general flow completeness (Theorem 5.2.20) or the false
filtered-distance equality (Theorem 6.4.6). A subsequent checked counterexample showed
that the sequential-preservation hypotheses printed in Theorem 5.2.20 and Proposition
5.2.21 are insufficient. Both formalized statements now require preservation of all
categorical limits and a strong (induced) flow, and their restricted completeness
conclusions are proved without admissions. The unrestricted general-flow claim under
Cruz's preservation hypothesis is not formalized here. See
[`5-2-21-weak-power-completeness-counterexample.md`](5-2-21-weak-power-completeness-counterexample.md).
