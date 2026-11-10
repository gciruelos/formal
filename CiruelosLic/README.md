# G. Ciruelos Rodríguez, *Factorizing Derivations via Intersection Types*

Licenciatura thesis, Universidad de Buenos Aires, 2018 (advisor: Pablo Barenbaum).
Source: [`CiruelosLic.pdf`](CiruelosLic.pdf) (also at [gciruelos.com](https://gciruelos.com/static/thesis-gciruelos.pdf); LaTeX in [`gciruelos/th`](https://github.com/gciruelos/th/tree/master/document)).
Build: `lake build CiruelosLic` from the project root.

The thesis builds a confluent, non-idempotent intersection type system for the λ-calculus whose
reduction tracks β-reduction exactly, and uses it to factor the derivation space of any λ-term
into garbage-free derivations followed by garbage.

## Main results

1. **Corollary 2.27 (Confluence).** The distributive λ-calculus `λ^dist`, whose terms are typing
   derivations, is confluent (and strongly normalizing).
2. **Theorem 3.27.** The derivation space of every `λ^dist` term is a
   distributive lattice, representable as a ring of sets of names.
3. **Proposition 4.9.** A λ-term has a head normal form if and only if it has a refinement
   in `λ^dist`.
4. **Lemma 4.19 (generalized cube lemma).** Simulation residuals commute with projection:
   `(ρ/t')/(σ/t') ≡ (ρ/σ)/(t'/σ)`.
5. **Theorem 5.22 (Factorization).** The derivation space `𝔻_λ(t)` is isomorphic to the Grothendieck
   construction `∫_𝔽 𝔾` of the garbage semilattices over the lattice of garbage-free derivations.

<!-- BEGIN GENERATED: main -->

| Result | Lean | Open `sorry` declarations | Status |
|:---|:---|---:|:---|
| Corollary 2.27 (Confluence) | `confluence` | 0 | **proved** |
| Theorem 3.27 (distributive lattice) | `distRS.instDistribLattice` | 0 | **proved** |
| Proposition 4.9 (refinability) | `has_hnf_iff_refinable` | 0 | **proved** |
| Lemma 4.19 (generalized cube lemma) | `generalized_cube_lemma` | 0 | **proved** |
| Theorem 5.22 (Factorization) | `factorization` | 0 | **proved** |

*Open `sorry` declarations* counts distinct declarations in this project that contain `sorry`
and are reached through the result's statement or proof, including the result itself when it
contains `sorry`. A **proved** result uses only `propext`,
`Classical.choice` and `Quot.sound`, unless other axioms are listed.

<!-- END GENERATED: main -->

## The results in brief

In the λ-calculus, the derivations (reduction sequences) from a term, taken up to permutation
equivalence, form an upper semilattice. Lévy, Laneve and Melliès studied its structure, but it is
not a lattice in general. The thesis introduces `λ^dist`, a calculus whose terms are typing
derivations of a non-idempotent intersection type system with labels. A `λ^dist` term
*refines* a λ-term, and its reduction simulates β-reduction step by step. Unlike the
λ-calculus, `λ^dist` is confluent and terminating, and its derivation spaces are distributive
lattices.

Simulation transports derivations of a λ-term `t` to a refinement `t'`. It is an algebraic
morphism, and it makes precise which steps of a derivation are *garbage*: steps that `t'` does
not see. Every derivation factors uniquely as a garbage-free part followed by garbage. This
makes `𝔻_λ(t)` a Grothendieck construction: a lattice of garbage-free derivations, over which
semilattices of garbage vary lax-functorially.

The formalization proves every result of the thesis without `sorry`. It also proves the
background result the thesis cites from Melliès, orthogonality of β-reduction
(`PreliminariesLambdaOrthogonality.lean`). The gaps below are places where the TeX proof needed repair.

## Per-file statistics

<!-- BEGIN GENERATED: stats -->

| Prefix | File | Lines | Statements | Defs | Types | `sorry`s | Max statement DAG (statement) | Max proof DAG (proof) | Most interesting result ([interestingness](https://arxiv.org/abs/2609.28603)) | Theorems with `sorry` |
|:---|:---|---:|---:|---:|---:|---:|:---|:---|:---|:---|
| **Chapter1** | [Preliminaries.lean](Chapter1Preliminaries.lean) | 1,887 | 110 | 39 | 8 | 0 | 292 (<code>LaxFunctor.mk.injEq</code>) | 4,209 (<code>ResidualSystem.completeDevelopment_unique</code>) | [<code>LTerm.betaStep_iff_beta</code>](Chapter1Preliminaries.lean#L1441) (135.71) | — |
| **Chapter2Section1** | [Calculus.lean](Chapter2Section1Calculus.lean) | 1,068 | 63 | 29 | 11 | 0 | 193 (<code>DTerm.subst._unary.eq_def</code>) | 8,575 (<code>PSubst.inverse</code>) | [<code>Correct.var</code>](Chapter2Section1Calculus.lean#L570) (130.33) | — |
| **Chapter2Section4** | [Properties.lean](Chapter2Section4Properties.lean) | 1,296 | 62 | 1 | 1 | 0 | 110 (<code>PSubst.correct</code>) | 5,124 (<code>PSubst.typing</code>) | [<code>DStep.subject_reduction</code>](Chapter2Section4Properties.lean#L490) (129.74) | — |
| **Chapter3** | [ResidualTheory.lean](Chapter3ResidualTheory.lean) | 1,409 | 87 | 14 | 2 | 0 | 181 (<code>distRS.meetAux_names._proof_1_6</code>) | 5,658 (<code>DStep.creation_case</code>) | [<code>distRS.orthogonal_core</code>](Chapter3ResidualTheory.lean#L403) (755.67) | — |
| **Chapter4Section1** | [SimulationExpansion.lean](Chapter4Section1SimulationExpansion.lean) | 1,533 | 88 | 16 | 8 | 0 | 129 (<code>cut_compose_root</code>) | 7,183 (<code>PSubst.compose_cut</code>) | [<code>HasType.of_shift</code>](Chapter4Section1SimulationExpansion.lean#L1205) (125.45) | — |
| **Chapter4Section2** | [Simulation.lean](Chapter4Section2Simulation.lean) | 1,525 | 72 | 4 | 1 | 0 | 155 (<code>simRes.match_1.eq_6</code>) | 9,513 (<code>cube_trace</code>) | [<code>cube_trace</code>](Chapter4Section2Simulation.lean#L813) (104.54) | — |
| **Chapter5Section1** | [Garbage.lean](Chapter5Section1Garbage.lean) | 1,344 | 64 | 10 | 0 | 0 | 128 (<code>order_preserved</code>) | 3,672 (<code>leftmost_least</code>) | [<code>garbage_duplicates_core</code>](Chapter5Section1Garbage.lean#L416) (52.94) | — |
| **Chapter5Section4** | [Factorization.lean](Chapter5Section4Factorization.lean) | 1,033 | 55 | 6 | 1 | 0 | 448 (<code>factorization</code>) | 4,026 (<code>groth_isLUB</code>) | [<code>GF.finite</code>](Chapter5Section4Factorization.lean#L391) (48.60) | — |
| **PreliminariesLambdaOrthogonality** | [.lean](PreliminariesLambdaOrthogonality.lean) | 2,152 | 131 | 13 | 2 | 0 | 328 (<code>Marked.MT.resid.induct_unfolding</code>) | 16,888 (<code>Marked.MT.Cube_aux</code>) | [<code>Marked.MT.Cube_aux</code>](PreliminariesLambdaOrthogonality.lean#L453) (375.29) | — |
| **CiruelosLic** | [.lean](../CiruelosLic.lean) | 33 | 0 | 0 | 0 | 0 | — | — | — | — |
| **Total / maximum** | | **13,280** | **732** | **132** | **34** | **0** | **448** (<code>factorization</code>) | **16,888** (<code>Marked.MT.Cube_aux</code>) | | |

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
- **Most interesting result** shows the highest proof DAG size divided by statement DAG size among
  sorry-free user-written theorems in the file. The name links to the Lean statement.
- **Theorems with `sorry`** lists declarations (of any kind) whose own term contains `sorryAx`.

Generated by [`scripts/update_stats.py`](../scripts/update_stats.py).

<!-- END GENERATED: stats -->

## Gaps found during formalization

<!-- BEGIN GENERATED: gaps -->

| Severity | Where | Kind | Lean | Status | Note |
|:---|:---|:---|:---|:---|:---|
| medium | Lemma A.20 | proof gap | [`subject_expansion`](Chapter2Section1Calculus.lean#L988) | formalized | `03-03-the-calculus.tex` (line 23) defines `t{x := s⃗}` only on correct terms, yet `refinement_substitution_inverse` invokes subject expansion in order to prove that `(λ^ℓ x. t')s⃗'` is correct, which is circular. Here subject expansion is a typing statement on raw terms, with no correctness hypothesis. |
| medium | Lemma A.21 | proof gap | [`backwards_simulation`](Chapter4Section1SimulationExpansion.lean#L1434) | formalized | The proof in `08-15-has-hnf-has-refinement.tex` chooses fresh labels for the reconstructed redexes without saying fresh with respect to what, and reconstructs sibling arguments independently, so labels chosen in different siblings can collide; it also does not track that strong sequentiality (needed for correctness of the expanded term) survives expansion inside an arbitrary context. We choose labels fresh for the whole current term (`exists_fresh_label`, `DTerm.labelSupport`), reconstruct siblings sequentially, and track disjoint free subterms exactly (`FreeCut`, `PSubst.track_beta_cut`, `DCtx.track_cut`, `subject_expansion_strong`). |
| medium | Lemma 4.19 | proof gap | [`generalized_cube_lemma`](Chapter4Section2Simulation.lean#L1453) | formalized | The TeX proof (`05-04-simulation-residuals.tex`, lines 353–407) first proves a partial result (2) for a single step `R` by induction on `σ`, then the general case by induction on `ρ = Rρ'`. Three steps fail. (i) Line 6 of the chain needs `(σ/R)/(t'/R) ≡ (σ/t')/(R/t')`, i.e. (2) with the roles swapped, which neither (2) nor the induction hypothesis provides. (ii) (2) is proved for one step but used for the set `R/σ` (a complete development), and its proof reads a family of per-residual derivations as one development without argument. (iii) Line 4 cites (2) for `(t'/σ)/(R/σ) = (t'/R)/(σ/R)`, which actually follows from item 1 of Compatibility. The underlying issue: projecting `Rρ'` over `τ` leaves `ρ'` to be projected over `τ/R`, a development of a set, so an induction on single steps does not close. |
| medium | Lemma A.29 | proof gap | [`leftmost_least`](Chapter5Section1Garbage.lean#L1100) | formalized | The proof (`08-19-garbage-some-properties.tex`, lines 464–533) inducts on `σ = Sσ₁` and applies the induction hypothesis to the residual `R₁` of the leftmost coarse step `R₀`, but only checks that `R₁` is *coarse* for `(ρ/S, t'/S)` (lines 511–530), not that it is *leftmost*. This is not automatic: `S` can create redexes, copy residuals of steps in its argument, and make a previously non-coarse step coarse. Fix: read "leftmost" as the pre-order `≺` on positions (ancestors first, then left to right; `PosLt`) and carry the invariant "`R₀ ≺ S'` for every other coarse step `S'`" through the induction, using that created redexes lie at or below `S` or at its parent (`created_position`, `not_isRedexAt_parent`), that steps outside the argument of `S` have one residual (`residuals_card_one`), and that contraction preserves `≺` (`order_preserved`). |
| low | Lemma A.16 | imprecise | [`subject_expansion`](Chapter2Section1Calculus.lean#L988) | formalized | `08-15-has-hnf-has-refinement.tex` (lines 22–26) leaves implicit that the arguments are typable and that their types match the occurrences of `x`, `T_x(t) = T(s⃗)` (in the thesis this hides in the partial operation `t{x := s⃗}`), and does not say which substitution is meant. With the type-directed substitution `DTerm.subst` the statement is false when `s⃗` has repeated types (`typeDirected_subject_expansion_counterexample`). We state it for the partition-based relation `PSubst`, which records the matching and typability, and show `PSubst` agrees with `DTerm.subst` under sequentiality (`PSubst.eq_subst`). |
| low | Lemma A.21 | typo | [`backwards_simulation`](Chapter4Section1SimulationExpansion.lean#L1434) | formalized | `08-15-has-hnf-has-refinement.tex`: line 17 writes `s₁ … sₙ` for `s₁ … sₘ`; line 407 cites `\rprop{simulation}` where `\rprop{reverse_simulation}` is applied. |
| low | Lemma 4.8 | typo | [`hnf_has_strong_refinement`](Chapter4Section1SimulationExpansion.lean#L1503) | formalized | `08-14-hnf-has-refinement.tex`: line 84 says that when `x₁ = y` and `x₁ ≠ xᵢ` (`i > 1`), `ℓ` is "the external label of `y`", but `ℓ` decorates `λ^ℓ x₁` and is chosen fresh in both subcases (as line 99 says); line 104 writes the premise context as `{y : τ₁}`, whereas for `y = xᵢ` with `i > 1` it is empty. In both cases `x₁ ∉ dom(Γ)`, so `Γ ⊢ λ^ℓ x₁. s' : [] →ℓ τ` holds uniformly. |
| low | Lemma A.29 | typo | [`leftmost_least`](Chapter5Section1Garbage.lean#L1100) | formalized | `08-19-garbage-some-properties.tex`, line 489: "`R` is to the left of `S`" should be "`R₀` is to the left of `S`". |

*Severity*: **high** means the printed statement is false or needs an unstated assumption;
**medium** means the statement is right but its proof is wrong, incomplete or missing;
**low** means an ambiguity or typo that a careful reader resolves. *Status* is *formalized*
when the declaration carrying the note is `sorry`-free.

<!-- END GENERATED: gaps -->

## Changes to the source

<!-- BEGIN GENERATED: changes -->

| Where | Lean | Change |
|:---|:---|:---|
| Lemma 4.19 | [`generalized_cube_lemma`](Chapter4Section2Simulation.lean#L1453) | We prove the equivalent statement on names, `names((ρ/σ)/(t'/σ)) = names(ρ/t') \ names(σ/t')` (`gen_names`), in three claims: a step after a derivation (`cube_gen`, by induction using the basic cube lemma `cube_sets`); a derivation after a complete development of a set `M`, by induction on `ρ` generalizing over `M` (`single_gen`, with `simNames_complete`); and the statement itself, by induction on `σ`. The lemma then follows by `distRS.permEq_iff_names`. |
| Lemma A.29 | [`leftmost_least`](Chapter5Section1Garbage.lean#L1100) | Instead of `#(R₀/σ) ≤ 1` we prove the form the sieve uses: if a prefix `ρ ⊑ ω` already contracts every λ^dist-redex simulating `p`, then `p ⊑ ρ`. The induction and the invariant are those of the fixed proof. |

<!-- END GENERATED: changes -->
