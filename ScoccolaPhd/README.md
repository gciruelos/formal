# L. N. Scoccola, *Locally Persistent Categories and Metric Properties of Interleaving Distances*

PhD thesis, Western University, 2020 (advisor: J. Daniel Christensen).
Source: [`ScoccolaPhd.pdf`](ScoccolaPhd.pdf). Build: `lake build ScoccolaPhd` from the project root.

The thesis gives one categorical framework, *locally persistent categories*, for the distances
used in topological data analysis, and proves stability, completeness and path-metric results
for all of them at once.

## Main results

1. **Theorem A (4.2.2).** A functor that preserves approximate morphisms and acyclic morphisms
   is 1-Lipschitz for the quotient interleaving distances.
2. **Theorem B (4.1.4).** The quotient interleaving distance between `x` and `y` is the
   infimum of `ε` such that some `x' ≃ x` and `y' ≃ y` are `ε`-interleaved.
3. **Theorem C (4.3.3).** Under limit hypotheses, the quotient interleaving distance is
   complete.
4. **Theorem D (4.4.2).** If the underlying category has finite limits, the quotient
   interleaving distance is intrinsic (a path metric).

<!-- BEGIN GENERATED: main -->

| Result | Lean | Open `sorry` declarations | Status |
|:---|:---|---:|:---|
| Theorem A (4.2.2) | `LPFunctor.quotientInterleavingDist_le_of_acyclic` | 0 | **proved** |
| Theorem B (4.1.4) | `quotientInterleavingDist_eq_inf_quotientInterleaved` | 0 | **proved** |
| Theorem B (4.1.4 with Lemma 4.1.5) | `quotientInterleavingDist_eq_inf_acyclicCover_of_powered` | 0 | **proved** |
| Theorem C (4.3.3) | `quotientInterleavingDist_complete` | 0 | **proved** |
| Theorem C (4.3.3 with Prop. 3.2.15 and Lemma 4.1.5) | `quotientInterleavingDist_complete_of_powered` | 0 | **proved** |
| Prop. 3.2.12 (weighted pullbacks) | `exists_weightedPullback` | 0 | **proved** |
| Prop. 3.2.15 (weighted sequential limits) | `hasWeightedSeqLimits_of_powered` | 0 | **proved** |
| Prop. 3.2.19 (terminal midpoints) | `hasTerminalMidpoints_of_powered` | 0 | **proved** |
| Theorem D (4.4.2) | `interleavingDist_intrinsic` | 0 | **proved** |
| Theorem D (4.4.2 with Prop. 3.2.19) | `interleavingDist_intrinsic_of_powered` | 0 | **proved** |

*Open `sorry` declarations* counts distinct declarations in this project that contain `sorry`
and are reached through the result's statement or proof, including the result itself when it
contains `sorry`. A **proved** result uses only `propext`,
`Classical.choice` and `Quot.sound`, unless other axioms are listed.

<!-- END GENERATED: main -->

## The results in brief

Topological data analysis compares shapes through algebraic or geometric invariants:
persistence modules, filtered spaces, metric spaces up to isometry. Each has its own
distance: the interleaving distance, the homotopy interleaving distance, the Gromov–Hausdorff
distance. Two objects are *`ε`-interleaved* when there are maps between them that are inverse
"up to a shift by `ε`". The interleaving distance is the least such `ε`.

A **locally persistent category** abstracts this. It is a category whose morphisms carry a
non-negative index (an `ε`-morphism is a morphism "up to error `ε`"), with composition adding
indices. It defines an interleaving distance on its objects. Many distances, however, should
not distinguish objects that are "the same" in a weaker sense: homotopy equivalent, or
isometric after completion. So one also fixes a class `W` of *acyclic* morphisms (for example
weak equivalences) and passes to the **quotient interleaving distance**: the largest distance
below the interleaving distance that is zero on objects related by `W`. The homotopy
interleaving distance and the Gromov–Hausdorff distance are both of this form.

* **Theorem A (stability).** A functor between such categories that preserves acyclic
  morphisms cannot increase distances. Stability theorems of TDA (an invariant varies
  continuously with the data) become instances of this one statement.
* **Theorem B (characterization).** The quotient distance, defined abstractly as a quotient
  metric, can be computed by replacing `x` and `y` with equivalent objects and interleaving
  those. This turns the abstract definition into something one can calculate with, and it
  drives the other proofs.
* **Theorem C (completeness).** If the category has pullbacks and sequential limits and `W` is
  stable under them, Cauchy sequences converge. This generalizes Cruz's completeness of the
  interleaving distance to quotient distances such as the homotopy interleaving distance.
* **Theorem D (intrinsic).** If the underlying category has finite limits, the distance between
  two objects is the infimum of lengths of paths between them. This generalizes the classical
  fact for persistence modules.

Chapters 5–6 apply the framework to flows, change of enrichment, dissimilarities,
filtrations, clustering and kernel density estimates.

## Per-file statistics

<!-- BEGIN GENERATED: stats -->

| Prefix | File | Lines | Statements | Defs | Types | `sorry`s | Max statement DAG (statement) | Max proof DAG (proof) | Max proof dependency footprint | Theorems with `sorry` |
|:---|:---|---:|---:|---:|---:|---:|:---|:---|:---|:---|
| **Chapter2Section1** | [Metric.lean](Chapter2Section1Metric.lean) | 1,761 | 59 | 31 | 2 | 0 | 198 (<code>exists_path_of_retract</code>) | 5,553 (<code>glue_isPathOn</code>) | [<code>isCompactEP_iff_complete_and_totallyBounded</code>](Chapter2Section1Metric.lean#L114) | — |
| **Chapter2Section4** | [EnrichedPersistent.lean](Chapter2Section4EnrichedPersistent.lean) | 1,529 | 33 | 45 | 13 | 0 | 767 (<code>HomotopicalAlgebra.AttachCells.flatten._proof_6</code>) | 20,031 (<code>isLeftKanExtension_yoneda</code>) | [<code>exists_modelStructure_chainComplex</code>](Chapter2Section4EnrichedPersistent.lean#L935) | — |
| **Chapter3Section1** | [LPCategories.lean](Chapter3Section1LPCategories.lean) | 1,378 | 36 | 31 | 13 | 0 | 646 (<code>LPFunctor.mk.injEq</code>) | 45,489 (<code>TerminalMidpoint.factor</code>) | [<code>tailSum_succ</code>](Chapter3Section1LPCategories.lean#L833) | — |
| **Chapter3Section2** | [PowersLimits.lean](Chapter3Section2PowersLimits.lean) | 1,971 | 108 | 39 | 0 | 0 | 692 (<code>PersistentObjects.copowTo_app</code>) | 7,902 (<code>coneElt_comp_h</code>) | [<code>tail_eq_sum_add</code>](Chapter3Section2PowersLimits.lean#L747) | — |
| **Chapter4Section1** | [QuotientDistances.lean](Chapter4Section1QuotientDistances.lean) | 1,412 | 62 | 18 | 5 | 0 | 475 (<code>TopologizedHoms.mk.injEq</code>) | 6,331 (<code>interleavingFunctor_rightContinuous</code>) | [<code>nonempty_of_topologized_rc</code>](Chapter4Section1QuotientDistances.lean#L948) | — |
| **Chapter4Section3** | [CompletenessObservable.lean](Chapter4Section3CompletenessObservable.lean) | 1,057 | 58 | 28 | 5 | 0 | 554 (<code>RowStep.mk.injEq</code>) | 4,091 (<code>exists_cat_structure</code>) | [<code>interleavingDist_complete_of_powered</code>](Chapter4Section3CompletenessObservable.lean#L1042) | — |
| **Chapter5Section1** | [ChangeOfEnrichment.lean](Chapter5Section1ChangeOfEnrichment.lean) | 1,709 | 93 | 35 | 7 | 0 | 1,642 (<code>QCopoweredByRepresentables.mk.injEq</code>) | 27,095 (<code>exists_lpcat_sublinear</code>) | [<code>exists_pos_le_smul</code>](Chapter5Section1ChangeOfEnrichment.lean#L309) | — |
| **Chapter5Section2** | [Flows.lean](Chapter5Section2Flows.lean) | 1,633 | 82 | 42 | 2 | 0 | 1,705 (<code>QFlow.mk.inj</code>) | 4,817 (<code>QFlow.mk.injEq</code>) | [<code>Flow.interleavingDist_intrinsic_complete</code>](Chapter5Section2Flows.lean#L995) | — |
| **Chapter6Section1** | [DissimilarityFiltrations.lean](Chapter6Section1DissimilarityFiltrations.lean) | 1,727 | 49 | 34 | 5 | 0 | 1,084 (<code>fdPullback._proof_4</code>) | 17,027 (<code>vrStar_lipschitz</code>) | [<code>Diss.quotientInterleavingDist_spec</code>](Chapter6Section1DissimilarityFiltrations.lean#L943) | — |
| **Chapter6Section2** | [MetricSpaces.lean](Chapter6Section2MetricSpaces.lean) | 1,287 | 47 | 17 | 0 | 0 | 332 (<code>epMetToDiss._proof_10</code>) | 3,694 (<code>epMet_factorization_with</code>) | [<code>epMetc_gh_geodesic</code>](Chapter6Section2MetricSpaces.lean#L803) | — |
| **Chapter6Section5** | [ClusteringDiagrams.lean](Chapter6Section5ClusteringDiagrams.lean) | 2,034 | 59 | 50 | 6 | 0 | 788 (<code>HCl.limitConeIsLimit._proof_3</code>) | 13,303 (<code>instCategoryHCl._proof_9</code>) | [<code>hCl_quotientInterleavingDist_eq</code>](Chapter6Section5ClusteringDiagrams.lean#L1965) | — |
|  | [KernelStability.lean](Chapter6Section5KernelStability.lean) | 474 | 19 | 11 | 0 | 0 | 1,039 (<code>kdfApproxMap._proof_10</code>) | 5,774 (<code>kdfCurried._proof_23</code>) | [<code>CompactMPS.toWDiss_bounded</code>](Chapter6Section5KernelStability.lean#L435) | — |
| **Chapter6Section7** | [PersistentSetMetric.lean](Chapter6Section7PersistentSetMetric.lean) | 508 | 28 | 11 | 1 | 0 | 1,121 (<code>qtame_structureMap_of_interleaved</code>) | 8,531 (<code>qtame_structureMap_of_interleaved</code>) | [<code>natPointVal_closed</code>](Chapter6Section7PersistentSetMetric.lean#L96) | — |
|  | [PersistentSets.lean](Chapter6Section7PersistentSets.lean) | 1,593 | 55 | 34 | 4 | 0 | 1,090 (<code>ffsPowered._proof_21</code>) | 17,942 (<code>ffsPowered._proof_20</code>) | [<code>finiteCost_rightContinuous</code>](Chapter6Section7PersistentSets.lean#L1013) | — |
| **FlowCompletenessCounterexample** | [.lean](FlowCompletenessCounterexample.lean) | 325 | 17 | 13 | 1 | 0 | 452 (<code>FlowCompletenessCounterexample.thickening._proof_9</code>) | 1,760 (<code>FlowCompletenessCounterexample.thickeningConeIsLimit._proof_4</code>) | [<code>FlowCompletenessCounterexample.counterexampleFlow_not_strong</code>](FlowCompletenessCounterexample.lean#L271) | — |
| **PreliminariesAckerman** | [.lean](PreliminariesAckerman.lean) | 218 | 5 | 6 | 0 | 0 | 135 (<code>singleLinkage_equivalence</code>) | 1,242 (<code>singleLinkage_full</code>) | [<code>singleLinkage_equivalence</code>](PreliminariesAckerman.lean#L196) | — |
| **PreliminariesProjectiveChainComplexes** | [.lean](PreliminariesProjectiveChainComplexes.lean) | 1,003 | 59 | 30 | 0 | 0 | 728 (<code>ProjectiveGenerators.surjective_quasiIso_boundaryLift</code>) | 8,661 (<code>ProjectiveGenerators.coverContraction._proof_2</code>) | [<code>ProjectiveGenerators.generatingTrivialCofibrations_hasSmallObjectArgument</code>](PreliminariesProjectiveChainComplexes.lean#L838) | — |
| **ScoccolaPhd** | [.lean](../ScoccolaPhd.lean) | 17 | 0 | 0 | 0 | 0 | — | — | — | — |
| **Total / maximum** | | **21,636** | **869** | **475** | **64** | **0** | **1,705** (<code>QFlow.mk.inj</code>) | **45,489** (<code>TerminalMidpoint.factor</code>) | | |

The shared **Prefix** is the chapter/section; append **File** to recover the filename. The root
module appears last.

- **Lines** includes blank lines and comments.
- **Statements** counts `theorem`, `lemma` and `instance` commands, including private ones.
- **Defs** counts `def`, `abbrev` and `opaque`; **Types** counts `inductive`, `structure` and
  `class`. Generated declarations, constructors and fields are not counted.
- **`sorry`s** counts explicit tokens outside comments, strings and quoted identifiers.
- **Max statement DAG (statement)** is the size of the largest elaborated theorem type;
  **Max proof DAG (proof)** the largest theorem body (hash-consed expression DAG), each with
  the declaration's name. Both include compiler-generated theorems.
- **Max proof dependency footprint** shows the highest absolute proof/vocabulary DAG ratio among
  sorry-free user-written theorems in the file, excluding projections, Lean-recognized
  automatic declarations and names absent from their reported source location. Each cell links to the selected theorem.
  This measures the chosen proof's dependency footprint, not mathematical value or shortest-proof
  complexity. Both sides recursively include dependencies
  from the work, Mathlib and Lean, counting each declaration once per side. The numerator
  expands proof bodies, dependency types and definitions; the denominator expands the statement
  and its vocabulary (including definition bodies, but excluding theorem proofs). Inductive
  constructors and recursor rules count too. Expression DAG sizes are summed per declaration;
  axioms contribute their types but no proof bodies. The name links to the Lean statement.
- **Theorems with `sorry`** lists declarations (of any kind) whose own term contains `sorryAx`.

Generated by [`scripts/update_stats.py`](../scripts/update_stats.py).

<!-- END GENERATED: stats -->

## Gaps found during formalization

<!-- BEGIN GENERATED: gaps -->

| Severity | Where | Kind | Lean | Status | Note |
|:---|:---|:---|:---|:---|:---|
| high | Proposition 3.2.14 | error | [`WeightedSeqLimit.interleaving`](Chapter3Section2PowersLimits.lean#L1248) | formalized | The thesis defines `δ̄_i = ∑_{j < i} δ_j` (and similarly `ε̄_i` as a prefix sum), which is false (e.g., if `δ_0 = 1` and `δ_j = 0` for `j ≥ 1`, then `δ̄_0 = 0`, which contradicts `k_0 : x_0 →_{δ̄_0} l` and the identity `δ̄_i = δ_i + δ̄_{i+1}` used in the proof). Lean sums over the tail `j ≥ i` (`tailSum`). |
| high | Definition 4.4.1 | error | [`CoherentFactorization`](Chapter4Section1QuotientDistances.lean#L395) | formalized | Definition 4.4.1 requires `z 0 = x` and `z ε = y` on the nose (so `f_{0,ε} = f`), which is impossible when `ε = 0` and `x ≠ y` are distinct `0`-interleaved objects; moreover, p. 78 asserts without proof that terminal midpoints yield coherent factorizations (Proposition 3.2.18), whereas midpoint constructions only produce `0`-interleaved endpoints and do not establish the triple composition identities `f_{r',r''} ∘ f_{r,r'} = f_{r,r''}`. |
| high | Lemma 5.1.14 | error | [`ProjectionHom`](Chapter5Section1ChangeOfEnrichment.lean#L1615) | formalized | Lemma 5.1.14 states `R(A)(ε) = Nat(Y(ε) ∘ F, A) ≅ ⨿_{q ∈ Q, F(q) ≤ ε} A(q)`. Because `Y(ε)(s)` is `{*}` when `ε ≤ s` and empty otherwise, `Nat(Y(ε) ∘ F, A)` is the limit `lim_{ε ≤ F(q)} A(q)`, not the coproduct over `F(q) ≤ ε`. Lean defines `ProjectionHom` directly using the coproduct `Σ q : {q // F q ≤ ε}, A q` (yielding the `ε`-morphisms described in Remark 5.1.16). |
| high | Theorem 5.2.20 | error | [`interleavingDist_complete`](Chapter5Section2Flows.lean#L1114) | formalized | The printed sequential-preservation hypothesis is insufficient. Positive-real-labelled sets have sequential limits and label thickenings preserving them, but singleton labels `1/(n+1)` have no metric limit. This is checked by `FlowCompletenessCounterexample.flow_counterexample`. The example fails terminal-object preservation and therefore does not refute Cruz's stronger hypothesis. To repair the statement, Lean requires a strong flow (its unit and multiplication transformations are invertible) and retains preservation of all categorical limits, restoring the preservation hypothesis of [Cru19]. The proof uses only sequential-limit preservation through `interleavingDist_complete_of_strong`. See [`5-2-21-weak-power-completeness-counterexample.md`](5-2-21-weak-power-completeness-counterexample.md). |
| high | Proposition 5.2.21 | error | [`interleavingDist_complete_of_weakPower`](Chapter5Section2Flows.lean#L1611) | formalized | The printed sequential-preservation hypothesis is refuted by `FlowCompletenessCounterexample.weak_power_counterexample`: positive-real-labelled sets have sequential limits and weak powers preserving them, but their interleaving distance is incomplete. To repair the statement, Lean requires the flow induced by the chosen weak power structure to be strong, and requires weak powers to preserve all categorical limits; the completeness conclusion is unchanged. See [`5-2-21-weak-power-completeness-counterexample.md`](5-2-21-weak-power-completeness-counterexample.md). |
| high | Theorem 6.4.6 | error | [`ghInterleaving_eq_filteredDist`](Chapter6Section1DissimilarityFiltrations.lean#L1547) | formalized | The printed equality for arbitrary dissimilarity-valued diagrams is false: a levelwise acyclic cover can introduce late distance-zero copies of an early point. For a two-point space at distance 1 with births 0 and 10, and a singleton born at 0, the correspondence distance is 10 but the original quotient distance is at most 1. Lean replaces the ambient diagram category by `FilteredDiss`, with fixed labels and birth values, and requires acyclic maps to preserve births as well as distances exactly (approximate maps allow the same error in births and distances); completeness of the new category is not asserted. See [`6-4-6-filtered-distance-counterexample.md`](6-4-6-filtered-distance-counterexample.md). |
| high | extension of Lemma 6.5.8 in Section 6.5.3 | error | [`WDiss.density`](Chapter6Section5ClusteringDiagrams.lean#L462) | formalized | The printed untruncated integral `∫_0^∞ M_X(x, s K⁻¹(r)) dr` on `wDiss` diverges to `∞` whenever `M x 0 > 0`, because above `K(0)` the inverse kernel is zero (whereas `WDiss` does not require `M x 0 = 0`), contradicting Lemma 6.5.20's bound `M · K(0)`. Lean integrates only over `(0, K(0)]`; this agrees with the printed formula whenever `M x 0 = 0` (in particular for every metric probability space with open-ball mass), and keeps the full category of weighted spaces with its powers and pullbacks. |
| high | Theorem 6.7.10 | error | [`singleLinkage_equivalence`](PreliminariesAckerman.lean#L184) | formalized | The thesis claims the completeness equivalence without total boundedness. On `ℕ`, put `d(n,m) = 0` for `n = m`, and `1 + 1/(min(n,m)+1)` otherwise. Every Cauchy sequence is eventually constant, so this ultrametric is complete. At radius `1` the clusters are singletons, whereas the compatible tail clusters at radii `s > 1` have empty intersection; hence single linkage is not right continuous. Ackerman distinguishes ordinary Cauchy completeness from strong Cauchy completeness (§2.3, especially Theorem 2.20); they cannot be identified here. We restrict the final assertion to totally bounded spaces, where the compactness argument of Theorem 6.7.11 establishes the claimed equivalence. |
| high | — | missing hypothesis | [`shift_iso_internalHom_yoneda`](Chapter2Section4EnrichedPersistent.lean#L1028) | formalized | The thesis states this for an arbitrary monoidal poset `P`, whereas `G^r(s) = G(r ⊗ s)` and `[Y(r), G]_Day(s) ≅ G(s ⊗ r)` require `P` to be commutative (`r ⊗ s = s ⊗ r`). Lean assumes `AddCommMonoid P`. |
| high | — | missing hypothesis | [`internalHom_obj_iso`](Chapter2Section4EnrichedPersistent.lean#L1075) | formalized | As in `shift_iso_internalHom_yoneda`, `[F, G]_Day(r) = Nat(F, G^r)` uses commutativity of the monoidal poset `P` (`r + s = s + r`), which the thesis leaves unstated and Lean assumes via `AddCommMonoid P`. |
| high | Proposition 2.6.10 | missing hypothesis | [`internalHom_isRightContinuous`](Chapter2Section4EnrichedPersistent.lean#L1304) | formalized | The proof uses `lim_{r' > r} G^{r'} ≅ G^r`, i.e. that `r' ↦ r' + t` maps `{r' > r}` coinitially into `{q > r + t}`, and that `{r' > r}` is codirected, as well as commutativity of `P`. This holds for `ℝ≥0` and `ℝ`, but fails for an arbitrary monoidal poset `P` (e.g. `P = ℝ≥0` with `x ⊗ y = x + y` if `x + y ≤ 1` else `2`, `F = Y(1)`, and `G(x) = ∅` for `x < 1.5`, `PUnit` for `x ≥ 1.5`). Lean states it for commutative `P` (`AddCommMonoid P`), totally ordered (`hlin`), with the coinitiality condition `hP`, all of which hold for `ℝ≥0` and `ℝ`. |
| high | — | missing hypothesis | [`exists_path_of_coherentFactorizations`](Chapter4Section1QuotientDistances.lean#L457) | formalized | Theorem 4.4.2 asserts a map `[0, δ] → (obj C, d_I)` sending `0 ↦ x` and `δ ↦ y` for every `δ ∈ ℝ_+`, which is impossible at `δ = 0` when `x ≠ y` since `[0, 0] = {0}`. Lean adds the hypothesis `hδ : 0 < δ`. |
| high | Theorem 4.5.14 | missing hypothesis | [`—`](Chapter4Section1QuotientDistances.lean#L1031) | formalized | The thesis deduces that the structure maps of `H(δ) = Hom(x, y)_δ × Hom(y, x)_δ` are closed from the same fact for each factor; but a product of closed maps need not be closed (a closed map to a point from a non-compact space, times an identity). We assume it. |
| high | Theorem 4.5.18 | missing hypothesis | [`exists_acyclic_cover_of_dist_eq`](Chapter4Section1QuotientDistances.lean#L1389) | formalized | The thesis states this for a relative locally persistent category, but the persistent set `QI(x, y)` is only defined (Definition 4.5.17) when `W` is stable under weighted pullbacks, which the proof also uses (through Section 4.1). We assume it. |
| high | Lemma 5.1.5 | missing hypothesis | [`poweredByRepresentables_of_changeOfEnrichment`](Chapter5Section1ChangeOfEnrichment.lean#L515) | formalized | Lemma 5.1.5 states `Q` is an arbitrary monoidal poset, whereas defining powers in a `Set^Q`-enriched category requires `Q` to be commutative (`[AddCommMonoid Q]`) for the naturality law `q + (δ + r) = δ + (q + r)`. |
| high | Lemma 5.1.5 | missing hypothesis | [`copoweredByRepresentables_of_changeOfEnrichment`](Chapter5Section1ChangeOfEnrichment.lean#L527) | formalized | Lemma 5.1.5 states `Q` is an arbitrary monoidal poset, whereas Lean assumes `[AddCommMonoid Q]`. |
| high | Proposition 5.1.9 | missing hypothesis | [`persistent_quotient_dist`](Chapter5Section1ChangeOfEnrichment.lean#L1511) | formalized | Proposition 5.1.9 assumes `(C, W)` is a relative locally persistent category without stating that `W` is stable under base change (pullbacks); its proof invokes Theorem 4.1.4 and Theorem 4.3.3 via Lemma 4.1.5, which require `W` to be stable under pullbacks. We add `[W.IsStableUnderBaseChange]`. |
| high | Proposition 5.1.15 | missing hypothesis | [`exists_lpcat_sublinear`](Chapter5Section1ChangeOfEnrichment.lean#L1629) | formalized | In `LPCat`, `homZero` requires a bijection `(X ⟶ Y) ≃ hom X Y 0`. Here `hom X Y 0` is `ProjectionHom F ... 0 = Σ q : {q // F q ≤ 0}, X ⟶ Y ∘ q`. Unless `F q ≤ 0 ↔ q = 0`, this sigma type contains extra components for each translation with measure 0, so it is not in bijection with `X ⟶ Y`. Proposition 5.1.15 assumes only an arbitrary monotone sublinear projection `F` (which only forces `F 0 = 0`, not `F q = 0 → q = 0`), without assuming definiteness. We add the hypothesis `hF : F q ≤ 0 → q = 0`. |
| high | Lemma 5.2.15 | missing hypothesis | [`exists_weakPower`](Chapter5Section2Flows.lean#L720) | formalized | The thesis states this for any flow. Its map `wp_{ε,0}` is postcomposition by `μ 0 ε` (followed by reindexing), and need not be bijective. For example, take the constant writer flow `T ε X = M × X` on sets, for a two-element monoid `M`. For `x = y = Unit`, the source and target of `wp_{ε,0}` have respectively four and two elements. We assume the flow is semi-strong: the invertible unit then makes `μ 0 ε` invertible by the unit law. No invertibility of positive-degree multiplications is assumed. |
| high | text after Proposition 5.2.11 | missing hypothesis | [`exists_flow_kleisli`](Chapter5Section2Flows.lean#L928) | formalized | The thesis says any flow can be normalized to a semi-strong flow with these object assignments. This fails for the constant writer flow `T ε X = M × X` for a two-element monoid `M`: in the Kleisli category of `T 0`, any composite `T 0 Unit →_{Kl} Unit →_{Kl} T 0 Unit` is constant in its `M`-valued coordinate and therefore cannot equal `id_{T 0 Unit}` (whose second coordinate is the identity on `M`), so `Unit ≇ T 0 Unit` in `Kl(T 0)`. Lean assumes the original flow is semi-strong and proves the stated normalization by transport along the unit equivalence; the unrestricted transport without a semi-strong conclusion is not asserted. |
| medium | Theorem 2.2.27 | proof gap | [`two_mul_gromovHausdorff_eq`](Chapter2Section1Metric.lean#L1713) | formalized | In the reverse direction, the thesis constructs `Z = P ⊔ Q` with `d_Z(p, q) = inf { d_P(p, p') + d_Q(q', q) + r : (p', q') ∈ R }` for `dist(R) = 2r` and calls `Z` a metric space. When `dist(R) = 0` (e.g. `P = Q = {*}`), `d_Z(p, q) = 0` for distinct `p ∈ P` and `q ∈ Q`, so `Z` is only a pseudo metric space (and one must also handle `dist(R) = ∞`). Lean avoids the separation issue by infimizing over `PseudoEMetricSpace Z` in `gromovHausdorff`, which agrees with the infimum over metric spaces when `P` and `Q` are metric spaces (via metric quotienting of `range i ∪ range j` when `hausdorffDist < ∞`). |
| medium | Proposition 6.2.18 | proof gap | [`epMet_coherentFactorizations_compact`](Chapter6Section2MetricSpaces.lean#L629) | formalized | The source's convex interpolation on the graph of an interleaving bijection need not be compact: swapping `1/2` and `3/4` in `[0,1]` gives a discontinuous bijection. Its graph closure is compact and has the same distortion bound, but its endpoint projections are surjective isometries, not necessarily bijections. |
| medium | Proposition 6.2.15 | proof gap | [`epMetc_gromovHausdorff`](Chapter6Section2MetricSpaces.lean#L1108) | formalized | The source infers compactness merely from uniform convergence of metrics on a fixed underlying set. This does not establish completeness of the limiting metric. Lean instead builds the limit on a compact space of compatible strings in closed correspondences and proves continuity into the limiting metric. |
| medium | Theorem 6.7.5 | proof gap | [`rtSet_geodesic_complete`](Chapter6Section7PersistentSetMetric.lean#L484) | formalized | The source asserts without proof that the shifted image `im(Nat(X, Y^ε) → Nat(X, Y^δ))` is isomorphic to the sequential limit of the images `im(Nat(X, Y^ε) → Nat(X&#124;_n, Y^δ&#124;_n))`, and omits checking closedness/product-closedness of structure maps for Theorem 4.5.14. Lean uses pointwise discrete coordinates and compact closures of shifted hom-space images for the compactness argument, avoiding these assertions. |
| medium | Theorem 6.7.11 | proof gap | [`singleLinkage_compact`](Chapter6Section7PersistentSets.lean#L555) | formalized | The source's compactness proof appeals to Theorem 6.7.10's unrestricted completeness characterization ("complete iff right continuous"), which fails in general without the positive-radius/finitary restriction (see `singleLinkage_equivalence` in `PreliminariesAckerman.lean`). |
| medium | Lemma 6.8.2 | proof gap | [`ffsCpx_limits`](Chapter6Section7PersistentSets.lean#L864) | formalized | The thesis uses `max` for the product and pullback filtrations. With its morphism convention `F_X σ ≤ F_Y (f σ)`, the projections instead require `min`. For example, for singleton complexes with constant filtrations `0` and `1`, the proposed `max` product has no projection to the first complex. We use `min` and verify the universal properties directly. |
| medium | Lemma 6.8.6 | proof gap | [`ffsCpx_reflects`](Chapter6Section7PersistentSets.lean#L1161) | formalized | The proof's displayed `QI` definition writes `epMetc` instead of `ffsCpx`, and says that `f, g` interleave the endpoints rather than the intermediate objects `Z, Z'`. |
| low | Example 2.5.9 | imprecise | [`exists_modelStructure_chainComplex`](Chapter2Section4EnrichedPersistent.lean#L918) | formalized | The statement does not say which chain complexes are meant; Lean takes the connective (`ℕ`-indexed) ones, with positive-degree surjections as fibrations. |
| low | Definition 4.1.2 | imprecise | [`IsStableUnderWeightedPullbacks`](Chapter3Section1LPCategories.lean#L708) | formalized | The thesis says "the pullback … is again a morphism in `E`"; weighted pullbacks are only determined up to isomorphism, so we require every one of them to be in `E`. |
| low | Lemma 2.2.21 | typo | [`chainDist`](Chapter2Section1Metric.lean#L510) | formalized | The thesis quantifies over `y₀, …, y_N, y'₀, …, y'_N` with `p R y₀`, `y'_i R y_{i+1}`, `y'_N R p'`, but prints the sum starting at `i = 1` (`∑_{i=1}^N d_P(y_i, y'_i)`). Taken literally, `y₀` and `y'₀` are unconstrained in the sum, collapsing the infimum to `0` (take `N = 1`, `y₀ = p`, `y'₀ = y₁ = y'₁ = p'`). Lean sums over `i = 0, …, N` (`Finset.range (N + 1)`), matching the thesis's proof. |
| low | Definition 2.5.2 | typo | [`FunctorialWFS`](Chapter2Section4EnrichedPersistent.lean#L319) | formalized | The thesis states the second condition with "left lifting property" twice; the right lifting property is meant. |
| low | Lemma 2.6.13 | typo | [`sharpUnit_injective_after_shift`](Chapter2Section4EnrichedPersistent.lean#L1506) | formalized | Lemma 2.6.13 prints `a, b ∈ ℝ_+(s)` instead of `a, b ∈ F(s)`. Lean states `a b : F.obj s`. |
| low | Definition 4.5.6 | typo | [`IsCompatibleFamily`](Chapter4Section1QuotientDistances.lean#L697) | formalized | The thesis writes `s ≤ r`; for the posets `(ℕ, ≥)` of Proposition 4.5.7 this is the same condition. |
| low | — | typo | [`QuotientInterleavingData`](Chapter4Section1QuotientDistances.lean#L1352) | formalized | Definition 4.5.17 writes that `f` and `g` form a `δ`-interleaving between `x` and `y` instead of between the covering objects `x'` and `y'`. Lean types `f : hom x' y' δ` and `g : hom y' x' δ`. |
| low | Example 5.1.17 | typo | [`exists_sublinearProjection_lawvere`](Chapter5Section1ChangeOfEnrichment.lean#L1686) | formalized | Example 5.1.17 prints codomain `Trans_P → R_+`, whereas a Lawvere metric `d` and its supremum can take the value `∞` (as in Proposition 5.1.15's codomain `[0, ∞]`). Lean uses `ℝ≥0∞`. |
| low | Proposition 5.2.2 | typo | [`lpCat`](Chapter5Section2Flows.lean#L202) | formalized | Proposition 5.2.2 prints "Identities are given by `T_0(x) ∈ Hom_C(x, T_0(x))`" instead of the monad unit `u_x : x → T_0(x)`. Lean uses `F.monad.η.app x`. |

*Severity*: **high** means Lean cannot state what the source prints: the statement or definition
is false, ill-stated or needs an unstated assumption, so Lean states a corrected version;
**medium** means the statement is right as printed but its proof is wrong, incomplete or
missing, and Lean supplies one; **low** means the mathematics is unaffected (an ambiguity Lean
resolves, a notation slip). *Status* is *formalized* when the declaration carrying the note is
`sorry`-free.

<!-- END GENERATED: gaps -->

## Changes to the source

<!-- BEGIN GENERATED: changes -->

_No changes recorded yet._

<!-- END GENERATED: changes -->
