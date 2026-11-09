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

| Result | Lean | `sorry`s it depends on | Status |
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

*`sorry`s it depends on* counts the other declarations of this project with an explicit
`sorry` that the result reaches through its statement and proof. For a result whose own proof
is still `sorry` this only covers its statement. A **proved** result uses only `propext`,
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

| Prefix | File | Lines | Statements | Defs | Types | `sorry`s | Max statement DAG (statement) | Max proof DAG (proof) | Theorems with `sorry` |
|:---|:---|---:|---:|---:|---:|---:|:---|:---|:---|
| **Chapter2Section1** | [Metric.lean](Chapter2Section1Metric.lean) | 1,737 | 59 | 31 | 2 | 0 | 198 (<code>exists_path_of_retract</code>) | 5,553 (<code>glue_isPathOn</code>) | — |
| **Chapter2Section4** | [EnrichedPersistent.lean](Chapter2Section4EnrichedPersistent.lean) | 1,494 | 33 | 45 | 13 | 0 | 767 (<code>HomotopicalAlgebra.AttachCells.flatten._proof_6</code>) | 20,031 (<code>isLeftKanExtension_yoneda</code>) | — |
| **Chapter3Section1** | [LPCategories.lean](Chapter3Section1LPCategories.lean) | 1,365 | 36 | 31 | 13 | 0 | 646 (<code>LPFunctor.mk.injEq</code>) | 45,489 (<code>TerminalMidpoint.factor</code>) | — |
| **Chapter3Section2** | [PowersLimits.lean](Chapter3Section2PowersLimits.lean) | 1,954 | 108 | 39 | 0 | 0 | 692 (<code>PersistentObjects.copowTo_app</code>) | 7,902 (<code>coneElt_comp_h</code>) | — |
| **Chapter4Section1** | [QuotientDistances.lean](Chapter4Section1QuotientDistances.lean) | 1,402 | 62 | 18 | 5 | 0 | 475 (<code>TopologizedHoms.mk.injEq</code>) | 6,331 (<code>interleavingFunctor_rightContinuous</code>) | — |
| **Chapter4Section3** | [CompletenessObservable.lean](Chapter4Section3CompletenessObservable.lean) | 1,044 | 58 | 28 | 5 | 0 | 554 (<code>RowStep.mk.injEq</code>) | 4,091 (<code>exists_cat_structure</code>) | — |
| **Chapter5Section1** | [ChangeOfEnrichment.lean](Chapter5Section1ChangeOfEnrichment.lean) | 1,614 | 91 | 35 | 7 | 1 | 1,642 (<code>QCopoweredByRepresentables.mk.injEq</code>) | 27,095 (<code>exists_lpcat_sublinear</code>) | <code>persistent_quotient_dist</code> |
| **Chapter5Section2** | [Flows.lean](Chapter5Section2Flows.lean) | 1,205 | 63 | 34 | 2 | 4 | 1,705 (<code>QFlow.mk.inj</code>) | 4,817 (<code>QFlow.mk.injEq</code>) | <code>Flow.exists_flow_kleisli</code>, <code>Flow.exists_weakPower</code>, <code>Flow.interleavingDist_complete</code>, <code>interleavingDist_complete_of_weakPower</code> |
| **Chapter6Section1** | [DissimilarityFiltrations.lean](Chapter6Section1DissimilarityFiltrations.lean) | 1,444 | 57 | 36 | 4 | 10 | 431 (<code>Diss.limitConeIsLimit._proof_4</code>) | 4,064 (<code>Diss.exists_copowered</code>) | <code>epMet_coherentFactorizations_compact</code>, <code>epMet_quotientInterleavingDist</code>, <code>epMetc_gromovHausdorff</code>, <code>ghInterleaving_eq_filteredDist</code>, <code>ghInterleaving_spec</code>, <code>gromovHausdorff_universal</code>, <code>homotopyInterleavingDist_intrinsic_complete</code>, <code>homotopyInterleavingDist_persistent</code>, <code>vrStar_lipschitz</code>, <code>weaklyEquivalent_tFib_of_fibrant</code> |
| **Chapter6Section5** | [ClusteringDiagrams.lean](Chapter6Section5ClusteringDiagrams.lean) | 1,359 | 49 | 38 | 10 | 15 | 454 (<code>pdLPCat._proof_36</code>) | 47,386 (<code>ffsCpx_powered</code>) | <code>ffsCpx_limits</code>, <code>ffsCpx_quotientInterleavingDist_eq</code>, <code>ffsCpx_reflects</code>, <code>hCl_quotientInterleavingDist_eq</code>, <code>hCl_quotientInterleavingDist_spec</code>, <code>hCl_structure</code>, <code>isStableUnderWeightedPullbacks_acyclicFFSCpx</code>, <code>isStableUnderWeightedPullbacks_acyclicWDiss</code>, <code>kdf_uniformContinuous</code>, <code>quotientInterleavingDist_wDiss_le_ghp</code>, <code>rtSet_geodesic_complete</code>, <code>rtSet_structure</code>, <code>singleLinkage_compact</code>, <code>singleLinkage_equivalence</code> |
| **PreliminariesProjectiveChainComplexes** | [.lean](PreliminariesProjectiveChainComplexes.lean) | 1,003 | 59 | 30 | 0 | 0 | 728 (<code>ProjectiveGenerators.surjective_quasiIso_boundaryLift</code>) | 8,661 (<code>ProjectiveGenerators.coverContraction._proof_2</code>) | — |
| **ScoccolaPhd** | [.lean](../ScoccolaPhd.lean) | 11 | 0 | 0 | 0 | 0 | — | — | — |
| **Total / maximum** | | **15,632** | **675** | **365** | **61** | **30** | **1,705** (<code>QFlow.mk.inj</code>) | **47,386** (<code>ffsCpx_powered</code>) | |

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
- **Theorems with `sorry`** lists declarations (of any kind) whose own term contains `sorryAx`.

Generated by [`scripts/update_stats.py`](../scripts/update_stats.py).

<!-- END GENERATED: stats -->

## Gaps found during formalization

<!-- BEGIN GENERATED: gaps -->

| Severity | Where | Kind | Lean | Status | Note |
|:---|:---|:---|:---|:---|:---|
| high | Proposition 2.6.10 | missing hypothesis | [`internalHom_isRightContinuous`](Chapter2Section4EnrichedPersistent.lean#L1274) | formalized | The proof uses `lim_{r' > r} G^{r'} ≅ G^r`, i.e. that `r' ↦ r' + t` maps `{r' > r}` coinitially into `{q > r + t}`, and that `{r' > r}` is codirected. This holds for `ℝ≥0` and `ℝ`, but not for an arbitrary monoidal poset `P`. We state it for `P` totally ordered (`hlin`) with the coinitiality condition `hP`, both of which hold for `ℝ≥0` and `ℝ`. |
| high | Theorem 4.5.14 | missing hypothesis | [`—`](Chapter4Section1QuotientDistances.lean#L1025) | formalized | The thesis deduces that the structure maps of `H(δ) = Hom(x, y)_δ × Hom(y, x)_δ` are closed from the same fact for each factor; but a product of closed maps need not be closed (a closed map to a point from a non-compact space, times an identity). We assume it. |
| high | Theorem 4.5.18 | missing hypothesis | [`exists_acyclic_cover_of_dist_eq`](Chapter4Section1QuotientDistances.lean#L1379) | formalized | The thesis states this for a relative locally persistent category, but the persistent set `QI(x, y)` is only defined (Definition 4.5.17) when `W` is stable under weighted pullbacks, which the proof also uses (through Section 4.1). We assume it. |
| high | Proposition 5.1.15 | missing hypothesis | [`exists_lpcat_sublinear`](Chapter5Section1ChangeOfEnrichment.lean#L1538) | formalized | In `LPCat`, `homZero` requires a bijection `(X ⟶ Y) ≃ hom X Y 0`. Here `hom X Y 0` is `ProjectionHom F ... 0 = Σ q : {q // F q ≤ 0}, X ⟶ Y ∘ q`. Unless `F q ≤ 0 ↔ q = 0`, this sigma type contains extra components for each translation with measure 0, so it is not in bijection with `X ⟶ Y`. The thesis assumes a metric where `d(x, Γ x) = 0` forces `Γ = id`, but `SublinearProjection` does not require definiteness. We add the hypothesis `hF : F q ≤ 0 → q = 0`. |
| high | Lemma 5.2.15 | missing hypothesis | [`exists_weakPower`](Chapter5Section2Flows.lean#L343) | open (`sorry`) | The thesis states that any flow induces a weak power structure on `C^T`. However, `WeakPowerStructure` requires `wp_{ε, 0}` to be a bijection, which means `x ⟶ T 0 (T ε y)` is naturally isomorphic to `x ⟶ T ε y` via `μ ε 0`. This requires `μ ε 0 : T ε ∘ T 0 ⟶ T ε` to be an isomorphism, which fails for arbitrary lax monoidal flows unless the flow is semi-strong (as Scoccola notes in Diagram 5.2.8, where the equivalence is with semi-strong flows `FlCATs.strong`). |
| high | Proposition 6.2.18 | missing hypothesis | [`epMet_coherentFactorizations_compact`](Chapter6Section1DissimilarityFiltrations.lean#L994) | open (`sorry`) | The Lean statement is also corrected: the thesis tacitly needs `0 < ε`, and the endpoints of the factorization are only `0`-interleaved with `P` and `Q` (they have a different underlying set, so they cannot be *equal* to them). |
| medium | Proposition 5.1.4 | proof gap | [`interleavingDist_biLipschitz`](Chapter5Section1ChangeOfEnrichment.lean#L394) | formalized | In the thesis proof (page 98), the inequality `ε₂ w ≤ v` is claimed to give a `(c * δ)`-interleaving for `w` from a `δ`-interleaving for `v`. But `ε₂ w ≤ v` bounds `w` by `v`, so shifting an `ε v`-morphism up to a `w`-morphism requires `v ≤ c w` (the other inequality `ε₁ v ≤ w`, yielding factor `1 / ε₁`). |
| medium | Proposition 6.2.18 | proof gap | [`epMet_coherentFactorizations_compact`](Chapter6Section1DissimilarityFiltrations.lean#L994) | open (`sorry`) | The thesis argues that a sequence in `M_γ` "has a subsequence that converges in `P`, which in turn has a subsequence that converges in `Q`, and thus converges in `M_γ`". This uses continuity of the bijection `f`, which an `ε`-interleaving does not provide (`f` may distort distances by `ε`). For instance, take `P = Q = [0,1]` and `f` swapping `1/2` and `3/4` (an `ε`-interleaving for `ε = 1/4`): for `0 < γ < ε` the sequence `1/2 + 1/n` has no convergent subsequence in `M_γ`, so `M_γ` is not compact. Taking the closure of the graph of `f` in `P × Q` repairs compactness, but then the maps of the factorization are no longer bijections, which `IsInterleavingPair` requires; a correct proof needs a different argument. |
| low | Example 2.5.9 | imprecise | [`exists_modelStructure_chainComplex`](Chapter2Section4EnrichedPersistent.lean#L896) | formalized | The statement does not say which chain complexes are meant; Lean takes the connective (`ℕ`-indexed) ones, with positive-degree surjections as fibrations. |
| low | Definition 4.1.2 | imprecise | [`IsStableUnderWeightedPullbacks`](Chapter3Section1LPCategories.lean#L700) | formalized | The thesis says "the pullback … is again a morphism in `E`"; weighted pullbacks are only determined up to isomorphism, so we require every one of them to be in `E`. |
| low | Definition 4.4.1 | imprecise | [`CoherentFactorization`](Chapter4Section1QuotientDistances.lean#L395) | formalized | Definition 4.4.1 requires `z 0 = x` and `z ε = y` on the nose, which fails for `ε = 0` between distinct isomorphic objects, and midpoint constructions only produce endpoint isomorphisms (`0`-interleavings). Furthermore, the composition identities `f_{r',r''} ∘ f_{r,r'} = f_{r,r''}` are neither used in Theorem 4.4.2 nor proved in the thesis for terminal midpoints (the thesis on p. 78 asserts without proof that midpoints give coherent factorizations; see also p. 64). We formalize the factorization with endpoint `0`-interleavings and interleaving pairs `(f_{r,r'}, g_{r,r'})`. |
| low | Definition 2.5.2 | typo | [`FunctorialWFS`](Chapter2Section4EnrichedPersistent.lean#L301) | formalized | The thesis states the second condition with "left lifting property" twice; the right lifting property is meant. |
| low | Definition 4.5.6 | typo | [`IsCompatibleFamily`](Chapter4Section1QuotientDistances.lean#L691) | formalized | The thesis writes `s ≤ r`; for the posets `(ℕ, ≥)` of Proposition 4.5.7 this is the same condition. |

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

<!-- END GENERATED: changes -->
