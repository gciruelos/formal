# Counterexample to Theorem 6.4.6

This concerns `ghInterleaving_eq_filteredDist`. The claimed equality fails even for the
canonical locally persistent structure on dissimilarity-valued diagrams, with `v = (1, 1)`.
The false diagram equality has been replaced by a proved equality in the corrected
category described below; no admission of the original statement remains.

Let `X = {a, b}` have `d(a, b) = 1`, with filtration values `f(a) = 0` and `f(b) = 10`.
Let `Y = {y}` have filtration value `f(y) = 0`. Sublevel sets use strict inequalities.

Every correspondence between `X` and `Y` contains both `(a, y)` and `(b, y)`. Its spatial
distortion is `1` and its filtration distortion is `10`, so `FFMet.dist X Y = 10`.

Define a dissimilarity-valued diagram `V` on two possible vertices `u, v`:

- `V(r)` is empty for `r ≤ 0`;
- `V(r) = {u}` for `0 < r ≤ 9`;
- `V(r) = {u, v}` for `9 < r`.

Every distance in `V(r)` is zero, and its structure maps are inclusions. Sending every
vertex to `y` gives a natural transformation `V → Y.sublevel`. At every parameter this
map is surjective and distance preserving, so it is levelwise acyclic.

The following maps give a `1`-interleaving between `X.sublevel` and `V`:

- `X.sublevel(r) → V(r + 1)` sends `a ↦ u` and `b ↦ v` when present;
- `V(r) → X.sublevel(r + 1)` sends `u ↦ a` and `v ↦ b` when present.

The second map is well defined on `v` because `r > 9` implies `r + 1 > 10`. Both maps
are natural. The first does not increase distances, and the second increases them by
at most `1`. Their shifted composites are exactly the structure maps to parameter `r + 2`.

Consequently, replacing `Y.sublevel` by its acyclic cover `V` gives quotient interleaving
distance at most `1`, while the claimed equal quantity is `10`.

The invalid step in the source proof is on thesis page 142: equality of images under an
acyclic map does not identify two distinct, distance-zero lifts. Here `u` and `v` have
the same image `y`, while only `u` exists at early parameters.

## Ways to repair the result

The main category repair below is implemented and proved in Lean. The remaining
options describe alternative repairs, not additional formalized theorems.

### Implemented repair: change the ambient category

The author's intended repair is to change the category slightly, rather than impose
extra hypotheses on the finite filtered metric spaces. The implemented repair uses a
category of **filtered dissimilarity spaces**. An object is a fixed set `E`, a
dissimilarity `d_E`, and a birth function `b_E : E → ℝ`. In particular, copies of a
point are individual labels with fixed birth values, not points that can be added
arbitrarily to a levelwise cover of a diagram.

An `ε`-morphism is a function `h : E → F` satisfying

```
d_F(h(e), h(e')) ≤ d_E(e, e') + ε
b_F(h(e)) ≤ b_E(e) + ε.
```

Lean directly implements the diagonal choice `(1, 1)`, using one error parameter
for both bounds. Composition adds the errors. Define acyclic maps to be surjections
preserving distances **and birth values exactly**. Finite filtered metric spaces embed directly in this category;
their correspondence covers are filtered pseudometric spaces in it.

This is stronger than remembering only a diagram up to levelwise acyclic maps.
The map `V → Y.sublevel` in the counterexample is no longer acyclic: its late label
has birth `9`, while its image has birth `0`.

The corrected theorem proves equality of `D` with the quotient interleaving
distance in this new category. Its correspondence-cover proof follows the source:

1. A correspondence `R` gives two objects on `R`, with distances and birth values
   pulled back from the respective factors. Their projections are acyclic, and the
   identity functions give an interleaving bounded by the filtered distortion.
2. Conversely, an interleaving of two such acyclic covers consists of mutually inverse
   underlying functions. Project their matched labels to `X × Y`. Surjectivity makes
   this a correspondence; the two morphism inequalities bound both distortions.

Lean also proves stability of acyclic maps under all weighted pullbacks and applies
the quotient-distance theorem, so this is an equality for the actual categorical
quotient distance, not only a newly defined cover infimum. The implementation is in
[Chapter6Section1DissimilarityFiltrations.lean](Chapter6Section1DissimilarityFiltrations.lean),
from `FilteredDiss` through `ghInterleaving_eq_filteredDist`. Empty carriers and infinite
distances are included. Completeness and the other results for the old diagram category
are not asserted to transfer automatically.
The construction below describes the same birth-preserving covers in diagram language.

### Retain the valid inequality

For the canonical persistent structure, the source's correspondence construction still
gives `d_quot(X.sublevel, Y.sublevel) ≤ FFMet.dist X Y`. A correspondence supplies two
pseudometric covers on the same set, with filtering functions pulled back from `X` and
`Y`; its filtered distortion bounds their interleaving parameter. This is the smallest
correction to the conclusion. There is no universal finite multiplicative bound in the
reverse direction: replace the birth value `10` above by arbitrarily large `A > 1`, and
let `v` appear at `A - 1`. The same construction gives `d_quot ≤ 1` but `D = A`.

### Restrict covers so copies retain the original birth times

A proposed replacement is an infimum over interleavings of the following special covers,
rather than over arbitrary levelwise acyclic covers:

- Choose a fixed set `E`, a surjection `p : E → X`, and distances pulled back from `X`.
- At parameter `r`, retain exactly the labels `e` with `f_X(p(e)) < r`.
- Use inclusions as structure maps. Make the analogous choices for `Y`.

Every label over `x` then appears at `f_X(x)`: no new copy may be introduced later.
Correspondence covers in the forward proof satisfy this requirement. For the reverse
proof, an interleaving induces a bijection of the eventual label sets. Matched labels
have birth values differing by at most the interleaving parameter, by existence of the
two shifted maps; their projected pairs form a correspondence with the required spatial
and filtration distortion bounds. With strict sublevels, obtain the birth inequalities
by taking parameters arbitrarily close to each birth from above.

This describes a candidate cover-infimum characterization of `D`, with a proof route.
It changes the allowed covers and hence does **not** prove the original quotient-distance
equality. Identifying it with a categorical quotient would additionally require proving
the appropriate replacement and quotient properties; these are not established here.

Merely requiring injective structure maps is insufficient: the counterexample already
uses inclusions. Requiring all covers to be metric spaces would instead exclude the
pseudometric correspondence covers used in the forward proof, so it is not an immediate
repair either.

### Restrict the filtering functions

If both functions are constant with the same value `c`, the proposed equality reduces
to the unfiltered correspondence-distortion theorem: the diagrams are empty before
`c` and constant afterwards. The upper bound uses correspondence covers with the same
birth value; for the lower bound, evaluate interleaved acyclic covers at a parameter
after `c`, where the target sublevel spaces are the whole spaces, and extract an
ordinary correspondence. This restricted statement still needs a Lean proof.

Even requiring both filtering functions to be 1-Lipschitz does not suffice. Take two
points of `X` at distance `1`, born at `0` and `1`, and a singleton `Y` born at `-1`.
Then `D = 2`. A zero-distance cover of `Y` with labels born at `-1` and `0` is
1-interleaved with `X.sublevel`, by the same maps as above, so `d_quot ≤ 1`.

### Fix the persistent structure explicitly

Independently of the counterexample, the Lean statement quantifies over an arbitrary
`LR : LQPCat ...`. Any corrected result about the intended distance should use
`persistentLQPCat Diss` and its change of enrichment along `(1, 1)`, as
`ghInterleaving_spec` does. Fixing this alone does not restore the false equality.
