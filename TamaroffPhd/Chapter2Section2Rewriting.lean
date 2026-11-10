import Mathlib

/-!
# Chapter 2, §2.1–2.4: rewriting systems, Gröbner bases and monomial algebras

Recollections from Chapter 2 of the thesis (Section 2, "Recollections", Subsections 2.1–2.4),
used in Chapters 3 and 6.

## Contents

* `FreeAlg`: the free algebra `k⟨X⟩`, realized as the monoid algebra of the free monoid `⟨X⟩`,
  so that monomials form its basis and `supp` is the support of the coefficient function.
* Definitions 1–6: rewriting systems, basic reductions and reductions, irreducible elements and
  normal forms, pseudo-reductions and termination, compatible rewriting orderings, the ordering
  `<_Σ`, convergence.
* The algebras `A_Σ = k⟨X | w - f(w)⟩` and `A_Σ⁰ = k⟨X | W⟩` (the monomial algebra of `Σ`).
* §2.2: the rewriting system `xyz ↦ x³ + y³ + z³`, terminating although it comes from no total
  order.

-/

noncomputable section

namespace TamaroffPhd

open MonoidAlgebra Classical

section FreeAlgebra

variable (k : Type) [Field k] (X : Type)

/-- The free associative algebra `k⟨X⟩` (§2.1), realized as the monoid algebra `k[⟨X⟩]` of the
free monoid `⟨X⟩`. Its elements are finite linear combinations of monomials. -/
abbrev FreeAlg := MonoidAlgebra k (FreeMonoid X)

variable {k X}

/-- The monomial `m ∈ ⟨X⟩` as an element of `k⟨X⟩`. -/
noncomputable abbrev mono (m : FreeMonoid X) : FreeAlg k X := MonoidAlgebra.single m 1

/-- `supp(g)`: the monomials appearing in `g` with nonzero coefficient (§2.1). -/
def supp (g : FreeAlg k X) : Finset (FreeMonoid X) := g.coeff.support

/-- The linear map on `k⟨X⟩` determined by its values on monomials. -/
noncomputable def linOnMonomials {M : Type} [AddCommGroup M] [Module k M]
    (v : FreeMonoid X → M) : FreeAlg k X →ₗ[k] M :=
  Finsupp.linearCombination k v ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

/-- `v` is a divisor of `u` in `⟨X⟩`: `u = a v b` (§2.6). -/
def IsDivisor (v u : FreeMonoid X) : Prop := ∃ a b : FreeMonoid X, u = a * v * b

end FreeAlgebra

section Rewriting

variable (k : Type) [Field k] (X : Type)

/-- **Definition 1 (Rewriting system).** A rewriting system on `k⟨X⟩` is a set `W ⊆ ⟨X⟩` of
monomials with a function `f` on `W` with values in `k⟨X⟩` (only the values on `W` matter).

**Change.** The thesis fixes `X` finite; the definitions here do not need it, and it is assumed
where the statements need it. -/
structure RewritingSystem where
  /-- The monomials that can be rewritten. -/
  W : Set (FreeMonoid X)
  /-- The rewriting rules `w ↦ f(w)`. -/
  f : FreeMonoid X → FreeAlg k X

variable {k X}

namespace RewritingSystem

variable (S : RewritingSystem k X)

/-- The relations `R = {w - f(w) : w ∈ W}`, as a relation on `k⟨X⟩` for `RingQuot`. -/
def rel : FreeAlg k X → FreeAlg k X → Prop := fun a b => ∃ w ∈ S.W, a = mono w ∧ b = S.f w

/-- The algebra `A_Σ = k⟨X | R⟩` presented by the rewriting system (§2.1). -/
abbrev Alg := RingQuot S.rel

/-- The quotient map `k⟨X⟩ → A_Σ`. -/
noncomputable def toAlg : FreeAlg k X →ₐ[k] S.Alg := RingQuot.mkAlgHom k S.rel

/-- The rewriting system `Σ⁰ = (X, W, 0)` (§2.1). -/
def zero : RewritingSystem k X := ⟨S.W, fun _ => 0⟩

/-- The monomial algebra `A_Σ⁰ = k⟨X | W⟩` associated to `Σ` (§2.1). -/
abbrev monomialAlg := S.zero.Alg

/-- **Definition 2 (Basic reduction).** The basic reduction associated to `(a, w, b)` with
`w ∈ W`: the linear endomorphism of `k⟨X⟩` sending `awb` to `a f(w) b` and fixing every other
monomial. -/
noncomputable def basicReduction (a w b : FreeMonoid X) : FreeAlg k X →ₗ[k] FreeAlg k X :=
  linOnMonomials fun m => if m = a * w * b then mono a * S.f w * mono b else mono m

/-- The basic reductions of `Σ`, as a set of endomorphisms. -/
def basicReductions : Set (FreeAlg k X →ₗ[k] FreeAlg k X) :=
  {ρ | ∃ a w b, w ∈ S.W ∧ ρ = S.basicReduction a w b}

/-- **Definition 2 (Reduction).** A finite sequence of basic reductions, composed in the given
order (the first one applied first). -/
noncomputable def reduction (ρs : List (FreeAlg k X →ₗ[k] FreeAlg k X)) :
    FreeAlg k X →ₗ[k] FreeAlg k X :=
  ρs.foldl (fun acc ρ => ρ ∘ₗ acc) LinearMap.id

/-- A list of basic reductions of `Σ`. -/
def IsReductionList (ρs : List (FreeAlg k X →ₗ[k] FreeAlg k X)) : Prop :=
  ∀ ρ ∈ ρs, ρ ∈ S.basicReductions

/-- **Definition 3 (Irreducible).** `g` is irreducible if every basic reduction fixes it. -/
def IsIrreducible (g : FreeAlg k X) : Prop := ∀ ρ ∈ S.basicReductions, ρ g = g

/-- **Definition 3 (Normal form).** An irreducible element with the same coset in `A_Σ`. -/
def IsNormalForm (g gbar : FreeAlg k X) : Prop := S.IsIrreducible gbar ∧ S.toAlg gbar = S.toAlg g

/-- **Definition 4 (Reduction finite).** `g` is reduction finite if for every pseudo-reduction
`(ρ₁, ρ₂, …)` (an infinite sequence of basic reductions) the sequence
`ρ₁ g, ρ₂ ρ₁ g, …` is eventually constant. -/
def IsReductionFinite (g : FreeAlg k X) : Prop :=
  ∀ ρ : ℕ → FreeAlg k X →ₗ[k] FreeAlg k X, (∀ n, ρ n ∈ S.basicReductions) →
    ∃ N, ∀ n ≥ N, reduction ((List.range (n + 1)).map ρ) g =
      reduction ((List.range (N + 1)).map ρ) g

/-- **Definition 4 (Terminating).** All elements of `k⟨X⟩` are reduction finite. -/
def IsTerminating : Prop := ∀ g, S.IsReductionFinite g

/-- **Definition 5 (Compatible rewriting ordering).** A partial order `le` on `⟨X⟩` that is
multiplicative, well-founded, and such that every monomial of `f(w)` is smaller than `w`. -/
structure IsCompatibleOrdering (le : FreeMonoid X → FreeMonoid X → Prop) : Prop where
  /-- `le` is a partial order. -/
  isPartialOrder : IsPartialOrder (FreeMonoid X) le
  /-- (1) multiplicativity. -/
  mul : ∀ m m' a b, le m m' ∧ m ≠ m' → le (a * m * b) (a * m' * b) ∧ a * m * b ≠ a * m' * b
  /-- (2) well-ordering: every nonempty set of monomials has a minimal element. -/
  wf : WellFounded fun m m' => le m m' ∧ m ≠ m'
  /-- (3) compatibility with `Σ`. -/
  compat : ∀ w ∈ S.W, ∀ w' ∈ supp (S.f w), le w' w ∧ w' ≠ w

/-- The one-step relation generating `<_Σ`: `a w' b` is below `a w b` when `w ∈ W` and
`w' ∈ supp(f(w))`. -/
def stepLT (m m' : FreeMonoid X) : Prop :=
  ∃ a b w w', w ∈ S.W ∧ w' ∈ supp (S.f w) ∧ m = a * w' * b ∧ m' = a * w * b

/-- The relation `<_Σ` (§2.1): the smallest transitive multiplicative relation compatible with
`Σ`. -/
def lt : FreeMonoid X → FreeMonoid X → Prop := Relation.TransGen S.stepLT

/-- **Definition 6 (Convergent).** `Σ` is terminating and every element has exactly one normal
form. -/
def IsConvergent : Prop := S.IsTerminating ∧ ∀ g, ∃! gbar, S.IsNormalForm g gbar

/-- Irreducible monomials: those not divisible by any element of `W` (§2.1). -/
def IrreducibleMonomials : Set (FreeMonoid X) := {m | ∀ w ∈ S.W, ¬ IsDivisor w m}

/-- **§2.1.** Irreducible monomials form a basis of the monomial algebra `A_Σ⁰`: their images
are linearly independent and span. -/
theorem irreducibleMonomials_basis :
    LinearIndependent k (fun m : S.IrreducibleMonomials => S.zero.toAlg (mono (m : FreeMonoid X)))
      ∧ Submodule.span k (Set.range fun m : S.IrreducibleMonomials =>
          S.zero.toAlg (mono (m : FreeMonoid X))) = ⊤ := by
  sorry

/-- **§2.3.** A terminating `Σ` is convergent if and only if the images of the irreducible
monomials in `A_Σ` are linearly independent (equivalently, the map `A_Σ⁰ → A_Σ` sending each
irreducible monomial to its coset is a linear isomorphism). -/
theorem isConvergent_iff_linearIndependent (hS : S.IsTerminating) :
    S.IsConvergent ↔
      LinearIndependent k (fun m : S.IrreducibleMonomials => S.toAlg (mono (m : FreeMonoid X))) := by
  sorry

end RewritingSystem

/-- **§2.2.** A rewriting system is a Gröbner basis if some total order satisfies the three
conditions of Definition 5. -/
def RewritingSystem.IsGroebner (S : RewritingSystem k X) : Prop :=
  ∃ le : FreeMonoid X → FreeMonoid X → Prop, S.IsCompatibleOrdering le ∧ ∀ m m', le m m' ∨ le m' m

end Rewriting

section Example

/-- The three variables of the example of §2.2. -/
inductive XYZ | x | y | z
  deriving DecidableEq

variable (k : Type) [Field k]

/-- **§2.2 (example).** The rewriting system on `k⟨x, y, z⟩` with the single rule
`xyz ↦ x³ + y³ + z³`. -/
noncomputable def xyzSystem : RewritingSystem k XYZ where
  W := {FreeMonoid.of .x * FreeMonoid.of .y * FreeMonoid.of .z}
  f _ := mono (FreeMonoid.of .x ^ 3) + mono (FreeMonoid.of .y ^ 3) + mono (FreeMonoid.of .z ^ 3)

/-- **§2.2.** The rewriting system `xyz ↦ x³ + y³ + z³` is terminating: `Φ(m) = 3A(m) + B(m)`
strictly decreases, where `A(m)` counts the divisors `xyz` of `m` and `B(m)` the letters `y`. -/
theorem xyzSystem_isTerminating : (xyzSystem k).IsTerminating := by
  sorry

/-- **§2.2.** No total order makes `xyz ↦ x³ + y³ + z³` a Gröbner basis: for a total
multiplicative order, `xyz < max(x³, y³, z³)`. -/
theorem xyzSystem_not_isGroebner : ¬ (xyzSystem k).IsGroebner := by
  sorry

end Example

end TamaroffPhd

end
