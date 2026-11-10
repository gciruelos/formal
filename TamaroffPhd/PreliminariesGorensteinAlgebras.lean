import TamaroffPhd.Chapter5Section1PerfectPaths

/-!
# Cited results on Gorenstein algebras and finitistic dimensions

Background that Chapter 5 cites without proof.

## Contents

* Zaks [182]: for a Gorenstein algebra the two injective dimensions agree.
* Finitistic dimensions (5.41), and the facts quoted in §5.5.1: they are finite for monomial
  algebras (Igusa–Zacharia [97], Green–Kirkman–Kuzmanovich [75]), bounded by
  `n_Λ = min(dim r, dim Λ/r^K)` (Zimmermann-Huisgen [184, §3]), and equal to the Gorenstein
  dimension for Gorenstein algebras [98].
-/

noncomputable section

namespace TamaroffPhd

open Classical CategoryTheory Quiv

variable {Q : Quiv} (R : Set (List Q.A)) (k : Type) [Field k]

/-- **Zaks [182] (§5.1.1).** If `injdim Λ_Λ` and `injdim _ΛΛ` are both finite, they are equal. -/
theorem zaks (hfin : Module.Finite k (Q.PathAlg k R)) (h : IsGorenstein R k) :
    injectiveDimension (rightReg R k) = injectiveDimension (leftReg R k) := by
  sorry

/-- **(5.41).** The (little) right finitistic dimension: the supremum of the finite projective
dimensions of finitely generated right modules. -/
def rfindim : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{0} (Q.PathAlg k R)ᵐᵒᵖ) (_ : Module.Finite (Q.PathAlg k R)ᵐᵒᵖ M)
    (_ : projectiveDimension M ≠ ⊤), projectiveDimension M

/-- The left finitistic dimension. -/
def lfindim : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{0} (Q.PathAlg k R)) (_ : Module.Finite (Q.PathAlg k R) M)
    (_ : projectiveDimension M ≠ ⊤), projectiveDimension M

/-- **[97, 75] (§5.5.1).** The finitistic dimensions of a finite-dimensional monomial algebra
are finite. -/
theorem findim_finite (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R)) :
    rfindim R k ≠ ⊤ ∧ lfindim R k ≠ ⊤ := by
  sorry

/-- **[98] (§5.5.1).** For a Gorenstein algebra, `rfindim Λ = lfindim Λ = dim Λ`. -/
theorem findim_eq_gorDim (hfin : Module.Finite k (Q.PathAlg k R)) (h : IsGorenstein R k) :
    rfindim R k = gorDim R k ∧ lfindim R k = gorDim R k := by
  sorry

/-- The radical `r = rad Λ`, spanned by the non-trivial paths. -/
def radIdeal : Submodule k (Q.PathAlg k R) :=
  Submodule.span k (Set.range fun p : {p : List Q.A // Q.IsPath p} => pathElt (k := k) R p.val)

/-- The bound `n_Λ = min(dim_k r, dim_k Λ / r^K)` of (5.42), with `K` minimal such that
`r^{K+1} = 0`; here `r^K` is spanned by the paths of length at least `K`. -/
def nBound : ℕ :=
  let K := sInf {K : ℕ | ∀ p, Q.IsPath p → K + 1 ≤ p.length → pathElt (k := k) R p = 0}
  min (Module.finrank k (radIdeal R k))
    (Module.finrank k (Q.PathAlg k R ⧸ Submodule.span k
      (Set.range fun p : {p : List Q.A // Q.IsPath p ∧ K ≤ p.length} => pathElt (k := k) R p.val)))

/-- **Zimmermann-Huisgen [184, §3] (§5.5.1).** `rfindim Λ ≤ n_Λ` for monomial algebras. -/
theorem rfindim_le_nBound (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R)) :
    rfindim R k ≤ (nBound R k : WithBot ℕ∞) := by
  sorry

end TamaroffPhd

end
