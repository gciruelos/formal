import TamaroffPhd.Chapter5Section2FGConditions

/-!
# Cited result: FG implies Gorenstein

Erdmann, Holloway, Snashall, Solberg and Taillefer [59, Th. 1.5]: a finite-dimensional algebra
satisfying the finite generation conditions FG is Gorenstein. Theorem 5.4.3 cites it for one
implication.

-/

noncomputable section

namespace TamaroffPhd

open Classical Quiv

variable {Q : Quiv} (R : Set (List Q.A)) (k : Type) [Field k]

/-- **[59, Th. 1.5].** A finite-dimensional (monomial) algebra satisfying FG is Gorenstein.

**Change.** FG is replaced by the equivalent conditions FG′ on the Yoneda algebra
(Proposition 5.2.3; see `Chapter5Section2FGConditions`). -/
theorem fg_isGorenstein (hR : (Q.data R).IsMinimal) (hfin : Module.Finite k (Q.PathAlg k R))
    (h : FG' k Q R) : IsGorenstein R k := by
  sorry

end TamaroffPhd

end
