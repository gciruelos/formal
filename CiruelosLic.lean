import CiruelosLic.Chapter1Preliminaries
import CiruelosLic.Chapter2Section1Calculus
import CiruelosLic.Chapter2Section4Properties
import CiruelosLic.Chapter3ResidualTheory
import CiruelosLic.Chapter4Section1SimulationExpansion
import CiruelosLic.Chapter4Section2Simulation
import CiruelosLic.Chapter5Section1Garbage
import CiruelosLic.Chapter5Section4Factorization
import CiruelosLic.PreliminariesLambdaOrthogonality

/-!
# G. Ciruelos Rodríguez, *Factorizing Derivations via Intersection Types* (2018)

Ported from `github.com/gciruelos/th/lean`, where each chapter was split into
`Defs → Appendix → Main` modules; here these are regrouped into 1k–2k-line files in chapter
order. `PreliminariesLambdaOrthogonality` proves the background result the thesis cites (orthogonality of
β-reduction, via marked terms, Huet's commutation theorem, Lévy's cube lemma and de Vrijer's
finite developments). The Chapter 1 results that rest on it close that file.

Representation choices:
* de Bruijn indices for both λ (`LTerm`) and λ^dist (`DTerm`).
* Steps are an object plus an address: a position (`Pos = List ℕ`) for λ, a λ-label
  (`Label = ℕ`) for λ^dist. Derivations are lists of addresses with a separate `Valid`.
* Projection is defined through projection after a multistep (`projM`), using a canonical
  complete development (`dev`).
* Multisets inside types (`Ty.arrow`) are `List Ty` (Lean cannot nest an inductive through
  `Multiset`); `→E` matches argument types up to permutation.
* Substitution in λ^dist is both the type-directed `DTerm.subst` (used in `DStep`) and the
  partition-based relation `PSubst` (used for subject expansion); they agree under
  sequentiality (`PSubst.eq_subst`).
* `ResidualSystem` instances (`lambdaRS`, `distRS`) are `abbrev`s, and orthogonality is a
  `Fact` instance.
-/
