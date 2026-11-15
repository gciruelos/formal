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

| Prefix | File | Lines | Statements | Defs | Types | `sorry`s | Max statement DAG (statement) | Max proof DAG (proof) | Max proof dependency footprint | Theorems with `sorry` |
|:---|:---|---:|---:|---:|---:|---:|:---|:---|:---|:---|
| **Chapter1** | [Preliminaries.lean](Chapter1Preliminaries.lean) | 1,906 | 110 | 39 | 8 | 0 | 292 (<code>LaxFunctor.mk.injEq</code>) | 4,209 (<code>ResidualSystem.completeDevelopment_unique</code>) | [<code>LTerm.mem_subPos</code>](Chapter1Preliminaries.lean#L311) | — |
| **Chapter2Section1** | [Calculus.lean](Chapter2Section1Calculus.lean) | 1,086 | 63 | 29 | 11 | 0 | 193 (<code>DTerm.subst._unary.eq_def</code>) | 8,575 (<code>PSubst.inverse</code>) | [<code>Ctx.shift_single</code>](Chapter2Section1Calculus.lean#L425) | — |
| **Chapter2Section4** | [Properties.lean](Chapter2Section4Properties.lean) | 1,310 | 62 | 1 | 1 | 0 | 110 (<code>PSubst.correct</code>) | 5,124 (<code>PSubst.typing</code>) | [<code>DTerm.shift_shift</code>](Chapter2Section4Properties.lean#L814) | — |
| **Chapter3** | [ResidualTheory.lean](Chapter3ResidualTheory.lean) | 1,419 | 87 | 14 | 2 | 0 | 181 (<code>distRS.meetAux_names._proof_1_6</code>) | 5,658 (<code>DStep.creation_case</code>) | [<code>distRS.names_cons</code>](Chapter3ResidualTheory.lean#L471) | — |
| **Chapter4Section1** | [SimulationExpansion.lean](Chapter4Section1SimulationExpansion.lean) | 1,537 | 88 | 16 | 8 | 0 | 129 (<code>cut_compose_root</code>) | 7,183 (<code>PSubst.compose_cut</code>) | [<code>Ctx.remove_zero_remove_succ</code>](Chapter4Section1SimulationExpansion.lean#L193) | — |
| **Chapter4Section2** | [Simulation.lean](Chapter4Section2Simulation.lean) | 1,529 | 72 | 4 | 1 | 0 | 155 (<code>simRes.match_1.eq_6</code>) | 9,513 (<code>cube_trace</code>) | [<code>Refines.shift</code>](Chapter4Section2Simulation.lean#L24) | — |
| **Chapter5Section1** | [Garbage.lean](Chapter5Section1Garbage.lean) | 1,362 | 64 | 10 | 0 | 0 | 128 (<code>order_preserved</code>) | 3,672 (<code>leftmost_least</code>) | [<code>PosLt.lt_parent</code>](Chapter5Section1Garbage.lean#L1056) | — |
| **Chapter5Section4** | [Factorization.lean](Chapter5Section4Factorization.lean) | 1,065 | 55 | 6 | 1 | 0 | 448 (<code>factorization</code>) | 4,026 (<code>groth_isLUB</code>) | [<code>lax_prefix_core</code>](Chapter5Section4Factorization.lean#L635) | — |
| **PreliminariesLambdaOrthogonality** | [.lean](PreliminariesLambdaOrthogonality.lean) | 2,154 | 131 | 13 | 2 | 0 | 328 (<code>Marked.MT.resid.induct_unfolding</code>) | 16,888 (<code>Marked.MT.Cube_aux</code>) | [<code>Marked.MT.Raise_Raise</code>](PreliminariesLambdaOrthogonality.lean#L103) | — |
| **CiruelosLic** | [.lean](../CiruelosLic.lean) | 33 | 0 | 0 | 0 | 0 | — | — | — | — |
| **Total / maximum** | | **13,401** | **732** | **132** | **34** | **0** | **448** (<code>factorization</code>) | **16,888** (<code>Marked.MT.Cube_aux</code>) | | |

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
| high | §1.2 | error | [`residuals`](Chapter1Preliminaries.lean#L284) | formalized | The thesis (p. 3, Case 2 of descendant for `t = C⟨u⟩ → C⟨u'⟩` with `C&#124;_r = □`) states that `q` is a descendant of `p` iff `p = rp'`, `q = rq'`, and `q'` is a descendant of `p'` in `u → u'`, omitting positions `p` not under `r` (which remain at `p`; §1.2 also writes "positive integers" and omits `ε` from `pos(ts)` and `pos(λx.t)` while using `0`, `1`, and `ε`). Here positions outside `q` stay at `{p}`. |
| high | §1.2 | error | [`proj_append_right`](Chapter1Preliminaries.lean#L1673) | formalized | The table of residual identities on p. 3 writes `ρ/στ = (ρ/σ)/τ` with literal equality `=`. This is false as list equality on canonical developments (for `t = (λx.(λy.yx)x)((λz.z)w)`, `ρ = [[1]]`, `σ = [[]]`, `τ = [[]]`, one side orders the two residuals as `[[0], [1]]` and the other as `[[1], [0]]`). Lean states permutation equivalence `PermEq` (`≡`). |
| high | §1.2 | error | [`proj_join`](Chapter1Preliminaries.lean#L1782) | formalized | The table of residual identities on p. 3 writes `(ρ ⊔ σ)/τ = (ρ/τ) ⊔ (σ/τ)` with literal equality `=`. This is false as list equality on canonical developments (for `t = (λx.(λy.yx)x)((λz.z)w)`, `ρ = [[]]`, `σ = [[1]]`, `τ = [[0, 0]]`, one side yields `[[], [1], [0]]` and the other yields `[[], [0], [1]]`). Lean states permutation equivalence `PermEq` (`≡`). |
| high | Lemma 2.14 | error | [`subst_subst`](Chapter2Section4Properties.lean#L1208) | formalized | On p. 10, the thesis asserts `t{{x := s̄}}{{y := ū}} = t{{y := ū}}{{x := s̄{{y := ū}}}}` (`x ∉ fv(ū)`) with one side defined iff the other is. This fails when `s̄` contains an argument unused in `t` on which `{{y := ū}}` is undefined (e.g., `t = z^σ`, `s̄ = [y^τ]`, `ū = []`: the LHS is `z^σ`, while `s̄{{y := []}}` on the RHS is undefined). Lean adds `hd : t.SubstDefined 0 ss` and `ht : ∀ s ∈ ss, (s.subst k us).ty = s.ty`. |
| high | §1.2 | missing hypothesis | [`Orthogonal`](Chapter1Preliminaries.lean#L151) | formalized | Axiom 3 (Finite Developments, p. 2) states that all developments of "a set `M` of coinitial steps" are finite, omitting the hypothesis that `M` is finite (false for an infinite set of pairwise independent steps). Lean restricts `M` to `Finset R.Adr`. |
| high | Lemma 2.13 | missing hypothesis | [`PSubst.eq_subst_of_subset`](Chapter2Section1Calculus.lean#L1031) | formalized | On p. 10, the thesis states `t{x := s̄} = t{{x := s̄'}}` assuming only `T_x(t) = T(s̄)` and `s̄` a sub-list of `s̄'`, without requiring `T(s̄')` to be sequential (needed in step 1 of its proof so that `s` is the unique term of type `τ` in `s̄'`). Lean adds `(env.map DTerm.ty).Nodup`. |
| medium | Lemma A.20 | proof gap | [`subject_expansion`](Chapter2Section1Calculus.lean#L1004) | formalized | `03-03-the-calculus.tex` (line 23) defines `t{x := s⃗}` only on correct terms, yet `refinement_substitution_inverse` invokes subject expansion in order to prove that `(λ^ℓ x. t')s⃗'` is correct, which is circular. Here subject expansion is a typing statement on raw terms, with no correctness hypothesis. |
| medium | Lemma A.21 | proof gap | [`backwards_simulation`](Chapter4Section1SimulationExpansion.lean#L1438) | formalized | The proof in `08-15-has-hnf-has-refinement.tex` chooses fresh labels for the reconstructed redexes without saying fresh with respect to what, and reconstructs sibling arguments independently, so labels chosen in different siblings can collide; it also does not track that strong sequentiality (needed for correctness of the expanded term) survives expansion inside an arbitrary context. We choose labels fresh for the whole current term (`exists_fresh_label`, `DTerm.labelSupport`), reconstruct siblings sequentially, and track disjoint free subterms exactly (`FreeCut`, `PSubst.track_beta_cut`, `DCtx.track_cut`, `subject_expansion_strong`). |
| medium | Lemma 4.19 | proof gap | [`generalized_cube_lemma`](Chapter4Section2Simulation.lean#L1457) | formalized | The TeX proof (`05-04-simulation-residuals.tex`, lines 353–407) first proves a partial result (2) for a single step `R` by induction on `σ`, then the general case by induction on `ρ = Rρ'`. Three steps fail. (i) Line 6 of the chain needs `(σ/R)/(t'/R) ≡ (σ/t')/(R/t')`, i.e. (2) with the roles swapped, which neither (2) nor the induction hypothesis provides. (ii) (2) is proved for one step but used for the set `R/σ` (a complete development), and its proof reads a family of per-residual derivations as one development without argument. (iii) Line 4 cites (2) for `(t'/σ)/(R/σ) = (t'/R)/(σ/R)`, which actually follows from item 1 of Compatibility. The underlying issue: projecting `Rρ'` over `τ` leaves `ρ'` to be projected over `τ/R`, a development of a set, so an induction on single steps does not close. |
| medium | Lemma A.29 | proof gap | [`leftmost_least`](Chapter5Section1Garbage.lean#L1118) | formalized | The proof (`08-19-garbage-some-properties.tex`, lines 464–533) inducts on `σ = Sσ₁` and applies the induction hypothesis to the residual `R₁` of the leftmost coarse step `R₀`, but only checks that `R₁` is *coarse* for `(ρ/S, t'/S)` (lines 511–530), not that it is *leftmost*. This is not automatic: `S` can create redexes, copy residuals of steps in its argument, and make a previously non-coarse step coarse. Fix: read "leftmost" as the pre-order `≺` on positions (ancestors first, then left to right; `PosLt`) and carry the invariant "`R₀ ≺ S'` for every other coarse step `S'`" through the induction, using that created redexes lie at or below `S` or at its parent (`created_position`, `not_isRedexAt_parent`), that steps outside the argument of `S` have one residual (`residuals_card_one`), and that contraction preserves `≺` (`order_preserved`). |
| low | Lemma A.16 | imprecise | [`subject_expansion`](Chapter2Section1Calculus.lean#L1004) | formalized | `08-15-has-hnf-has-refinement.tex` (lines 22–26) leaves implicit that the arguments are typable and that their types match the occurrences of `x`, `T_x(t) = T(s⃗)` (in the thesis this hides in the partial operation `t{x := s⃗}`), and does not say which substitution is meant. With the type-directed substitution `DTerm.subst` the statement is false when `s⃗` has repeated types (`typeDirected_subject_expansion_counterexample`). We state it for the partition-based relation `PSubst`, which records the matching and typability, and show `PSubst` agrees with `DTerm.subst` under sequentiality (`PSubst.eq_subst`). |
| low | Definition 5.8 | imprecise | [`sieve`](Chapter5Section1Garbage.lean#L50) | formalized | Definition 5.8 (p. 46) selects "the leftmost coarse step" `R₀` without specifying the order on redex positions; Lean fixes the required pre-order `PosLt` (ancestors first, then left to right; `redexes_sorted`), without which Lemma A.29 and `sieve_least` fail when an outer step duplicates a step in its argument. |
| low | Definition 5.20 | typo | [`LaxFunctor`](Chapter1Preliminaries.lean#L35) | formalized | On p. 49, item 1 writes `B(a ↪ a) = id_a` instead of `id_{B(a)}`; Lean states `map (le_refl a) x = x`. |
| low | Definition 2.12 | typo | [`subst`](Chapter2Section1Calculus.lean#L256) | formalized | On p. 9 (`03-03-the-calculus.tex`), for `Γ, x : [τ₁,...,τₙ] ⊢ t : σ` and `Δᵢ ⊢ sᵢ : ρᵢ` (`1 ≤ i ≤ m`), the condition "`[σ₁,...,σₙ]` is sequential" is a typo for "`[ρ₁,...,ρₘ]` is sequential" (sequentiality of `[τ₁,...,τₙ]` does not guarantee distinct external types in `s̄` when `m > n`). Here `DTerm.subst` is defined totally via `find?`, and distinct argument types are required where needed (`PSubst.eq_subst_of_subset`, `PSubst.eq_subst`). |
| low | Appendix A.14 | typo | [`backwards_simulation`](Chapter4Section1SimulationExpansion.lean#L1438) | formalized | On p. 81 (Lemma A.15), `y s₁ … sₙ` is written for `y s₁ … sₘ`; on p. 86 (Proposition 4.9, `1 ⇒ 3`), Simulation (Proposition 4.3) is cited where Reverse Simulation (Proposition 4.5) is applied. |
| low | Lemma 4.8 | typo | [`hnf_has_strong_refinement`](Chapter4Section1SimulationExpansion.lean#L1507) | formalized | `08-14-hnf-has-refinement.tex`: line 84 says that when `x₁ = y` and `x₁ ≠ xᵢ` (`i > 1`), `ℓ` is "the external label of `y`", but `ℓ` decorates `λ^ℓ x₁` and is chosen fresh in both subcases (as line 99 says); line 104 writes the premise context as `{y : τ₁}`, whereas for `y = xᵢ` with `i > 1` it is empty. In both cases `x₁ ∉ dom(Γ)`, so `Γ ⊢ λ^ℓ x₁. s' : [] →ℓ τ` holds uniformly. |
| low | Lemma A.29 | typo | [`leftmost_least`](Chapter5Section1Garbage.lean#L1118) | formalized | `08-19-garbage-some-properties.tex`, line 489 (p. 98, item 2.1): "`R` is to the left of `S`" should be "`R₀` is to the left of `S`" (and item 2.1 prints `S/t₀ = ∅` for `S/t₀ ≠ ∅`). |
| low | Lemma 5.13 | typo | [`garbage_only_duplicates_garbage`](Chapter5Section4Factorization.lean#L99) | formalized | On p. 47 (and Lemma A.28(2), p. 97), the thesis concludes that `S` is `(t'/R)`-garbage, even though `S` is coinitial with `R` (`src(S) = src(R)`) while `t'/R ⋉ tgt(R)`. Because `R` is `t'`-garbage, `t'/R = t'` as a term and `S` is `t'`-garbage (`IsGarbage t' [q]`). |
| low | Theorem 5.17 | typo | [`simple_factorization`](Chapter5Section4Factorization.lean#L230) | formalized | On p. 48, item 3 (and Lemma A.35(3), p. 103) writes that `ρ₂` is `t'`-garbage, whereas `ρ₂` starts at `tgt(ρ₁)` where `t'/ρ₁ ⋉ tgt(ρ₁)`. The text after Theorem 5.22 (p. 50) gives the intended `(t'/ρ₁)`-garbage, which Lean states. |

*Severity*: **high** means Lean cannot state what the source prints: the statement or definition
is false, ill-stated or needs an unstated assumption, so Lean states a corrected version;
**medium** means the statement is right as printed but its proof is wrong, incomplete or
missing, and Lean supplies one; **low** means the mathematics is unaffected (an ambiguity Lean
resolves, a notation slip). *Status* is *formalized* when the declaration carrying the note is
`sorry`-free.

<!-- END GENERATED: gaps -->

## Changes to the source

<!-- BEGIN GENERATED: changes -->

| Where | Lean | Change |
|:---|:---|:---|
| — | [`LTerm`](Chapter1Preliminaries.lean#L216) | Uses de Bruijn indices (`var n`, `lam t`, `app t s`) instead of named variables modulo α-equivalence. |
| — | [`Ty`](Chapter2Section1Calculus.lean#L39) | Base type variables are indexed by `ℕ`, and arrow domains use `List Ty` instead of `Multiset Ty` because Lean cannot nest an inductive type through `Multiset`. |
| — | [`DTerm`](Chapter2Section1Calculus.lean#L151) | Uses de Bruijn indices (`var n τ`) instead of named variables modulo α-equivalence. |
| — | [`HasType`](Chapter2Section1Calculus.lean#L205) | Rule `→I` produces the canonically sorted domain `Ty.canon M` and binds index `0` via `Ctx.cons M Γ`, and rule `→E` matches the argument type list `σs` up to permutation (`σs.Perm L`) to represent multiset domains. |
| — | [`subst`](Chapter2Section1Calculus.lean#L256) | Definition 2.12 defines `t{{x := s̄}}` partially under typing and sequentiality hypotheses; `DTerm.subst` is a total de Bruijn function on raw terms using `List.find?` (leaving `var k τ` unchanged if no matching type is found). |
| — | [`meetAux`](Chapter3ResidualTheory.lean#L252) | Uses structural recursion on `fuel := σ.length` instead of well-founded recursion on `&#124;ρ&#124;`, and picks `Nat.find h` (the least common label) as the deterministic choice. |
| Theorem 3.29 | [`namesHom`](Chapter3ResidualTheory.lean#L1399) | Targets `Finset Label` instead of `𝒫(ℒ)` (`Set Label`). |
| — | [`Refines`](Chapter4Section1SimulationExpansion.lean#L25) | Definition 4.2 (p. 31) restricts `t'` to `T^#` and uses named variables; `Refines` is defined on raw de Bruijn terms (passing `Correct` / `CTerm` where needed). |
| Definition 5.8 | [`sieve`](Chapter5Section1Garbage.lean#L50) | Implemented via bounded recursion `sieveAux` with explicit fuel `(simDeriv t' σ).length` (shown fuel-independent in `sieving_is_well_defined`) and the `PosLt`-sorted redex list `redexes t`. |
| Theorem 5.22 | [`laxG`](Chapter5Section4Factorization.lean#L649) | Uses `Quotient.out` representatives (`rep`) for `obj`/`map` (and `psi`) rather than lifting `[α] ↦ [ρα/σ]` across all three equivalence classes as in Appendix A.20 (1.2, p. 104). |

A *change* is a departure from the source that exists only because of Lean's ergonomics (a
representation Mathlib makes easier, avoiding index arithmetic); the source is not wrong and the
mathematics is the same. Defects are listed under *Gaps*.

<!-- END GENERATED: changes -->
