import TamaroffPhd.Chapter5Section1PerfectPaths

/-!
# Cited results of Chen–Shen–Zhou on Gorenstein-projective modules

Chen, Shen and Zhou [39] classify the indecomposable Gorenstein-projective modules over a monomial
algebra by perfect paths. Chapter 5 cites:

* Theorem 5.1.1 ([39, Th. 4.1]): `p ↦ pΛ` is a bijection from perfect paths to the isomorphism
  classes `GP(Λ)` of non-projective indecomposable Gorenstein-projective right modules;
* Lemma 5.1.4 ([39, Lem. 3.1, Prop. 4.6]): when `pΛ` (or `Λq`) is Gorenstein-projective or
  projective, in terms of `R(p)` and `L(q)`.
-/

noncomputable section

namespace TamaroffPhd

open Classical CategoryTheory Quiv

variable {Q : Quiv} (R : Set (List Q.A)) (k : Type) [Field k]

/-- **Theorem 1.1 ([39, Th. 4.1]).** For a finite-dimensional monomial algebra, each perfect
path `p` gives a non-projective indecomposable Gorenstein-projective module `pΛ`; every such
module is isomorphic to `pΛ` for a unique perfect path `p`. -/
theorem chenShenZhou_classification (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R)) :
    (∀ p, IsPerfect R p → IsGorensteinProjective R k (pathIdeal R k p) ∧
        ¬ Projective (pathIdeal R k p) ∧
        ∀ (M N : ModuleCat (Q.PathAlg k R)ᵐᵒᵖ), Nonempty (pathIdeal R k p ≅ M ⊞ N) →
          Limits.IsZero M ∨ Limits.IsZero N) ∧
    (∀ M : ModuleCat (Q.PathAlg k R)ᵐᵒᵖ, Module.Finite (Q.PathAlg k R)ᵐᵒᵖ M →
        IsGorensteinProjective R k M → ¬ Projective M → ¬ Limits.IsZero M →
        (∀ (M₁ M₂ : ModuleCat (Q.PathAlg k R)ᵐᵒᵖ), Nonempty (M ≅ M₁ ⊞ M₂) → Limits.IsZero M₁ ∨ Limits.IsZero M₂) →
        ∃! p, IsPerfect R p ∧ Nonempty (M ≅ pathIdeal R k p)) := by
  sorry

/-- **Lemma 1.4 ([39, Lem. 3.1, Prop. 4.6]).** For a non-trivial path `p` of a monomial
algebra: (1) `pΛ` is Gorenstein-projective and not projective iff `R(p) = {q}` for a perfect
path `q`; (3) `pΛ` is projective iff `R(p)` is empty. -/
theorem chenShenZhou_lemma_1_4 (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (p : List Q.A) (hp : IsNzPath R p) :
    ((IsGorensteinProjective R k (pathIdeal R k p) ∧ ¬ Projective (pathIdeal R k p)) ↔
      ∃ q, rightCof R p = {q} ∧ IsPerfect R q) ∧
    (Projective (pathIdeal R k p) ↔ rightCof R p = ∅) := by
  sorry

/-- **Lemma 1.4 (2), (4) ([39]).** Dually, `Λq` is projective iff `L(q)` is empty. -/
theorem chenShenZhou_lemma_1_4_left (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (q : List Q.A) (hq : IsNzPath R q) :
    Projective (pathIdealLeft R k q) ↔ leftCof R q = ∅ := by
  sorry

end TamaroffPhd

end
