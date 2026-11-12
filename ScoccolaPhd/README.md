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
| **Chapter2Section1** | [Metric.lean](Chapter2Section1Metric.lean) | 1,737 | 59 | 31 | 2 | 0 | 198 (<code>exists_path_of_retract</code>) | 5,553 (<code>glue_isPathOn</code>) | [<code>isCompactEP_iff_complete_and_totallyBounded</code>](Chapter2Section1Metric.lean#L114) | — |
| **Chapter2Section4** | [EnrichedPersistent.lean](Chapter2Section4EnrichedPersistent.lean) | 1,494 | 33 | 45 | 13 | 0 | 767 (<code>HomotopicalAlgebra.AttachCells.flatten._proof_6</code>) | 20,031 (<code>isLeftKanExtension_yoneda</code>) | [<code>exists_modelStructure_chainComplex</code>](Chapter2Section4EnrichedPersistent.lean#L913) | — |
| **Chapter3Section1** | [LPCategories.lean](Chapter3Section1LPCategories.lean) | 1,365 | 36 | 31 | 13 | 0 | 646 (<code>LPFunctor.mk.injEq</code>) | 45,489 (<code>TerminalMidpoint.factor</code>) | [<code>tailSum_succ</code>](Chapter3Section1LPCategories.lean#L825) | — |
| **Chapter3Section2** | [PowersLimits.lean](Chapter3Section2PowersLimits.lean) | 1,954 | 108 | 39 | 0 | 0 | 692 (<code>PersistentObjects.copowTo_app</code>) | 7,902 (<code>coneElt_comp_h</code>) | [<code>tail_eq_sum_add</code>](Chapter3Section2PowersLimits.lean#L735) | — |
| **Chapter4Section1** | [QuotientDistances.lean](Chapter4Section1QuotientDistances.lean) | 1,402 | 62 | 18 | 5 | 0 | 475 (<code>TopologizedHoms.mk.injEq</code>) | 6,331 (<code>interleavingFunctor_rightContinuous</code>) | [<code>nonempty_of_topologized_rc</code>](Chapter4Section1QuotientDistances.lean#L942) | — |
| **Chapter4Section3** | [CompletenessObservable.lean](Chapter4Section3CompletenessObservable.lean) | 1,044 | 58 | 28 | 5 | 0 | 554 (<code>RowStep.mk.injEq</code>) | 4,091 (<code>exists_cat_structure</code>) | [<code>interleavingDist_complete_of_powered</code>](Chapter4Section3CompletenessObservable.lean#L1029) | — |
| **Chapter5Section1** | [ChangeOfEnrichment.lean](Chapter5Section1ChangeOfEnrichment.lean) | 1,691 | 93 | 35 | 7 | 0 | 1,642 (<code>QCopoweredByRepresentables.mk.injEq</code>) | 27,095 (<code>exists_lpcat_sublinear</code>) | [<code>exists_pos_le_smul</code>](Chapter5Section1ChangeOfEnrichment.lean#L306) | — |
| **Chapter5Section2** | [Flows.lean](Chapter5Section2Flows.lean) | 1,315 | 69 | 35 | 2 | 3 | 1,705 (<code>QFlow.mk.inj</code>) | 4,817 (<code>QFlow.mk.injEq</code>) | [<code>Flow.interleavingDist_intrinsic_complete</code>](Chapter5Section2Flows.lean#L707) | <code>Flow.exists_flow_kleisli</code>, <code>Flow.exists_weakPower</code>, <code>Flow.interleavingDist_complete</code> |
| **Chapter6Section1** | [DissimilarityFiltrations.lean](Chapter6Section1DissimilarityFiltrations.lean) | 1,817 | 57 | 36 | 4 | 4 | 431 (<code>Diss.limitConeIsLimit._proof_4</code>) | 17,027 (<code>vrStar_lipschitz</code>) | [<code>Diss.quotientInterleavingDist_spec</code>](Chapter6Section1DissimilarityFiltrations.lean#L940) | <code>epMet_coherentFactorizations_compact</code>, <code>epMet_quotientInterleavingDist</code>, <code>epMetc_gromovHausdorff</code>, <code>ghInterleaving_eq_filteredDist</code> |
| **Chapter6Section5** | [ClusteringDiagrams.lean](Chapter6Section5ClusteringDiagrams.lean) | 1,092 | 19 | 25 | 6 | 4 | 422 (<code>instCategoryHCl._proof_9</code>) | 13,303 (<code>instCategoryHCl._proof_9</code>) | [<code>uniformKernel_integral</code>](Chapter6Section5ClusteringDiagrams.lean#L74) | <code>hCl_quotientInterleavingDist_eq</code>, <code>hCl_quotientInterleavingDist_spec</code>, <code>hCl_structure</code>, <code>kdf_uniformContinuous</code> |
| **Chapter6Section7** | [PersistentSets.lean](Chapter6Section7PersistentSets.lean) | 1,246 | 47 | 23 | 4 | 4 | 1,090 (<code>ffsPowered._proof_25</code>) | 17,942 (<code>ffsPowered._proof_22</code>) | [<code>finiteCost_rightContinuous</code>](Chapter6Section7PersistentSets.lean#L676) | <code>rtSet_geodesic_complete</code>, <code>rtSet_structure</code>, <code>singleLinkage_compact</code>, <code>singleLinkage_equivalence</code> |
| **PreliminariesProjectiveChainComplexes** | [.lean](PreliminariesProjectiveChainComplexes.lean) | 1,003 | 59 | 30 | 0 | 0 | 728 (<code>ProjectiveGenerators.surjective_quasiIso_boundaryLift</code>) | 8,661 (<code>ProjectiveGenerators.coverContraction._proof_2</code>) | [<code>ProjectiveGenerators.generatingTrivialCofibrations_hasSmallObjectArgument</code>](PreliminariesProjectiveChainComplexes.lean#L838) | — |
| **ScoccolaPhd** | [.lean](../ScoccolaPhd.lean) | 12 | 0 | 0 | 0 | 0 | — | — | — | — |
| **Total / maximum** | | **17,172** | **700** | **376** | **61** | **15** | **1,705** (<code>QFlow.mk.inj</code>) | **45,489** (<code>TerminalMidpoint.factor</code>) | | |

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
| high | Lemma 6.8.2 | error | [`ffsCpx_limits`](Chapter6Section7PersistentSets.lean#L534) | formalized | The thesis uses `max` for the product and pullback filtrations. With its morphism convention `F_X σ ≤ F_Y (f σ)`, the projections instead require `min`. For example, for singleton complexes with constant filtrations `0` and `1`, the proposed `max` product has no projection to the first complex. We use `min` and verify the universal properties directly. |
| high | Proposition 2.6.10 | missing hypothesis | [`internalHom_isRightContinuous`](Chapter2Section4EnrichedPersistent.lean#L1274) | formalized | The proof uses `lim_{r' > r} G^{r'} ≅ G^r`, i.e. that `r' ↦ r' + t` maps `{r' > r}` coinitially into `{q > r + t}`, and that `{r' > r}` is codirected. This holds for `ℝ≥0` and `ℝ`, but not for an arbitrary monoidal poset `P`. We state it for `P` totally ordered (`hlin`) with the coinitiality condition `hP`, both of which hold for `ℝ≥0` and `ℝ`. |
| high | Theorem 4.5.14 | missing hypothesis | [`—`](Chapter4Section1QuotientDistances.lean#L1025) | formalized | The thesis deduces that the structure maps of `H(δ) = Hom(x, y)_δ × Hom(y, x)_δ` are closed from the same fact for each factor; but a product of closed maps need not be closed (a closed map to a point from a non-compact space, times an identity). We assume it. |
| high | Theorem 4.5.18 | missing hypothesis | [`exists_acyclic_cover_of_dist_eq`](Chapter4Section1QuotientDistances.lean#L1379) | formalized | The thesis states this for a relative locally persistent category, but the persistent set `QI(x, y)` is only defined (Definition 4.5.17) when `W` is stable under weighted pullbacks, which the proof also uses (through Section 4.1). We assume it. |
| high | Proposition 5.1.9 | missing hypothesis | [`persistent_quotient_dist`](Chapter5Section1ChangeOfEnrichment.lean#L1506) | formalized | Proposition 5.1.9 assumes `(C, W)` is a relative locally persistent category without stating that `W` is stable under base change (pullbacks); its proof invokes Theorem 4.1.4 and Theorem 4.3.3 via Lemma 4.1.5, which require `W` to be stable under pullbacks. We add `[W.IsStableUnderBaseChange]`. |
| high | Proposition 5.1.15 | missing hypothesis | [`exists_lpcat_sublinear`](Chapter5Section1ChangeOfEnrichment.lean#L1615) | formalized | In `LPCat`, `homZero` requires a bijection `(X ⟶ Y) ≃ hom X Y 0`. Here `hom X Y 0` is `ProjectionHom F ... 0 = Σ q : {q // F q ≤ 0}, X ⟶ Y ∘ q`. Unless `F q ≤ 0 ↔ q = 0`, this sigma type contains extra components for each translation with measure 0, so it is not in bijection with `X ⟶ Y`. The thesis assumes a metric where `d(x, Γ x) = 0` forces `Γ = id`, but `SublinearProjection` does not require definiteness. We add the hypothesis `hF : F q ≤ 0 → q = 0`. |
| high | Lemma 5.2.15 | missing hypothesis | [`exists_weakPower`](Chapter5Section2Flows.lean#L345) | open (`sorry`) | The thesis states that any flow induces a weak power structure on `C^T`. However, `WeakPowerStructure` requires `wp_{ε, 0}` to be a bijection, which means `x ⟶ T 0 (T ε y)` is naturally isomorphic to `x ⟶ T ε y` via `μ ε 0`. This requires `μ ε 0 : T ε ∘ T 0 ⟶ T ε` to be an isomorphism, which fails for arbitrary lax monoidal flows unless the flow is semi-strong (as Scoccola notes in Diagram 5.2.8, where the equivalence is with semi-strong flows `FlCATs.strong`). |
| high | Proposition 5.2.11 | missing hypothesis | [`exists_flow_kleisli`](Chapter5Section2Flows.lean#L661) | open (`sorry`) | Without a commutativity/compatibility assumption relating `T δ (μ_{0, δ})` and `μ_{δ, 0}`, backward transfer of strong interleavings from `Kleisli F.monad` to `C` can fail (for example, for a non-commutative writer monad). |
| high | Theorem 5.2.20 | missing hypothesis | [`interleavingDist_complete`](Chapter5Section2Flows.lean#L810) | open (`sorry`) | Without `F.IsStrong`, `limit D` need not be a limit of the geometric interleaving sequence (counterexample: `C = Type`, `T 0 X = X`, `T ε X = X × Fin 2` for `ε > 0`, `a k = Unit`). |
| high | Proposition 6.2.18 | missing hypothesis | [`epMet_coherentFactorizations_compact`](Chapter6Section1DissimilarityFiltrations.lean#L1218) | open (`sorry`) | The Lean statement is also corrected: the thesis tacitly needs `0 < ε`, and the endpoints of the factorization are only `0`-interleaved with `P` and `Q` (they have a different underlying set, so they cannot be *equal* to them). |
| medium | Proposition 5.1.4 | proof gap | [`interleavingDist_biLipschitz`](Chapter5Section1ChangeOfEnrichment.lean#L394) | formalized | In the thesis proof (page 98), the inequality `ε₂ w ≤ v` is claimed to give a `(c * δ)`-interleaving for `w` from a `δ`-interleaving for `v`. But `ε₂ w ≤ v` bounds `w` by `v`, so shifting an `ε v`-morphism up to a `w`-morphism requires `v ≤ c w` (the other inequality `ε₁ v ≤ w`, yielding factor `1 / ε₁`). |
| medium | Proposition 6.2.18 | proof gap | [`epMet_coherentFactorizations_compact`](Chapter6Section1DissimilarityFiltrations.lean#L1218) | open (`sorry`) | The thesis argues that a sequence in `M_γ` "has a subsequence that converges in `P`, which in turn has a subsequence that converges in `Q`, and thus converges in `M_γ`". This uses continuity of the bijection `f`, which an `ε`-interleaving does not provide (`f` may distort distances by `ε`). For instance, take `P = Q = [0,1]` and `f` swapping `1/2` and `3/4` (an `ε`-interleaving for `ε = 1/4`): for `0 < γ < ε` the sequence `1/2 + 1/n` has no convergent subsequence in `M_γ`, so `M_γ` is not compact. Taking the closure of the graph of `f` in `P × Q` repairs compactness, but then the maps of the factorization are no longer bijections, which `IsInterleavingPair` requires; a correct proof needs a different argument. |
| medium | Theorem 6.2.20 | proof gap | [`epMet_quotientInterleavingDist`](Chapter6Section1DissimilarityFiltrations.lean#L1241) | open (`sorry`) | The thesis proof relies on Proposition 6.2.18 (`epMet_coherentFactorizations_compact`), which fails as stated without additional hypotheses (such as compactness and passing to the T0 quotient). |
| medium | Theorem 6.2.20 | proof gap | [`epMetc_gromovHausdorff`](Chapter6Section1DissimilarityFiltrations.lean#L1253) | open (`sorry`) | The thesis proof relies on Proposition 6.2.18 (`epMet_coherentFactorizations_compact`) to apply Theorem 4.5.16. |
| medium | Theorem 6.4.6 | proof gap | [`ghInterleaving_eq_filteredDist`](Chapter6Section1DissimilarityFiltrations.lean#L1697) | open (`sorry`) | In the `≥` direction, Scoccola's proof (p. 142) claims that if `y'' ∈ T(r')` (`r' < r - ε`) maps to the same point `y ∈ Y` as `φ(x') ∈ T(r + ε)`, then `y''` maps to `φ(x')` under `T(r') → T(r + ε)`. This fails when `T` is an arbitrary `Diss`-valued persistence module with distinct points at distance `0` (counterexample: `X = {x₁, x}` with `d(x₁, x) = 1`, `f_X(x₁) = 0`, `f_X(x) = 10`, and `Y = {y}` with `f_Y(y) = 0`, which gives `D(X, Y) = 10` while `X.sublevel` and `Y.sublevel` are `1`-interleaved via an acyclic cover `Y'` splitting `y` into two distance-`0` points at `r = 9`). |
| low | Example 2.5.9 | imprecise | [`exists_modelStructure_chainComplex`](Chapter2Section4EnrichedPersistent.lean#L896) | formalized | The statement does not say which chain complexes are meant; Lean takes the connective (`ℕ`-indexed) ones, with positive-degree surjections as fibrations. |
| low | Definition 4.1.2 | imprecise | [`IsStableUnderWeightedPullbacks`](Chapter3Section1LPCategories.lean#L700) | formalized | The thesis says "the pullback … is again a morphism in `E`"; weighted pullbacks are only determined up to isomorphism, so we require every one of them to be in `E`. |
| low | Definition 4.4.1 | imprecise | [`CoherentFactorization`](Chapter4Section1QuotientDistances.lean#L395) | formalized | Definition 4.4.1 requires `z 0 = x` and `z ε = y` on the nose, which fails for `ε = 0` between distinct isomorphic objects, and midpoint constructions only produce endpoint isomorphisms (`0`-interleavings). Furthermore, the composition identities `f_{r',r''} ∘ f_{r,r'} = f_{r,r''}` are neither used in Theorem 4.4.2 nor proved in the thesis for terminal midpoints (the thesis on p. 78 asserts without proof that midpoints give coherent factorizations; see also p. 64). We formalize the factorization with endpoint `0`-interleavings and interleaving pairs `(f_{r,r'}, g_{r,r'})`. |
| low | Definition 2.5.2 | typo | [`FunctorialWFS`](Chapter2Section4EnrichedPersistent.lean#L301) | formalized | The thesis states the second condition with "left lifting property" twice; the right lifting property is meant. |
| low | Definition 4.5.6 | typo | [`IsCompatibleFamily`](Chapter4Section1QuotientDistances.lean#L691) | formalized | The thesis writes `s ≤ r`; for the posets `(ℕ, ≥)` of Proposition 4.5.7 this is the same condition. |
| low | Lemma 6.8.6 | typo | [`ffsCpx_reflects`](Chapter6Section7PersistentSets.lean#L824) | formalized | The displayed `QI` definition writes `epMetc` instead of `ffsCpx`, and says that `f, g` interleave the endpoints rather than the intermediate objects `Z, Z'`. |

*Severity*: **high** means the printed statement is false or needs an unstated assumption;
**medium** means the statement is right but its proof is wrong, incomplete or missing;
**low** means an ambiguity or typo that a careful reader resolves. *Status* is *formalized*
when the declaration carrying the note is `sorry`-free.

<!-- END GENERATED: gaps -->

## Changes to the source

<!-- BEGIN GENERATED: changes -->

| Where | Lean | Change |
|:---|:---|:---|
| Example 2.5.9 | [`exists_modelStructure_chainComplex`](Chapter2Section4EnrichedPersistent.lean#L896) | To show that maps lifting against the fibrations are quasi-isomorphisms, we factor through `X ⊞ P(Y)`, where `P(Y)` is an explicit contractible cover of `Y` surjective in positive degrees. The lifting property makes the original map a retract of the homotopy equivalence `X → X ⊞ P(Y)`. This avoids a separate homology calculation for transfinite cell complexes. |
| Definition 6.4.3 | [`ghInterleaving_spec`](Chapter6Section1DissimilarityFiltrations.lean#L1649) | Specializes the locally `(ℝ≥0 × ℝ≥0)`-persistent structure from an arbitrary `LR` to `persistentLQPCat Diss.{u}` so `persistent_quotient_dist` applies. |
| Theorem 6.4.7 | [`vrStar_lipschitz`](Chapter6Section1DissimilarityFiltrations.lean#L1716) | Adds `v : ℝ≥0 × ℝ≥0` and hypotheses `hL₁`, `hL₂` witnessing that the `LPCat` structures on `ℝ ⥤ Diss` and `ℝ ⥤ (ℝ ⥤ TopCat)` arise by change of enrichment along `pairFamily v` from `persistentLQPCat` (using `persistentLPCat TopCat` on `ℝ ⥤ TopCat`), instead of unrelated arbitrary `LPCat` instances. |
| Lemma 6.5.17 | [`isStableUnderWeightedPullbacks_acyclicWDiss`](Chapter6Section5ClusteringDiagrams.lean#L366) | Specializes the locally bi-persistent structure from an arbitrary `LW` satisfying `hLW` to `wDissLQPCat`, so that `exists_powered_of_changeOfEnrichment` applies. |
| Theorem 6.5.23 | [`quotientInterleavingDist_wDiss_le_ghp`](Chapter6Section5ClusteringDiagrams.lean#L533) | Specializes `LW` to `wDissLQPCat` (as in `isStableUnderWeightedPullbacks_acyclicWDiss`) so `IsChangeOfEnrichment` determines composition and units. |

<!-- END GENERATED: changes -->
