import TamaroffPhd.PreliminariesAnickChains

/-!
# Chapter 3, §1: the bar construction of a monomial algebra and its contraction

The homotopy retract `Tor_A ⇄ B A` of §3.1.1, from which the thesis obtains the A∞-coalgebra
structure on `Tor_A` (Theorem 3.2.1) and the minimal model (Theorem 3.2.6) by homotopy
transfer. The straightening terms are proved non-attached, giving the side conditions
`p h = 0` and `h h = 0`; the homotopy identity and exchange rule remain open.

## Contents

* `BarSpace`: the (normalized) bar construction `B A = T^c(s Ā)` of `A = k⟨X⟩/(W)`, with basis
  the bar terms `[u₀ | ⋯ | u_r]` of non-empty normal words, its differential `barDiff` and the
  deconcatenation coproduct `barDelta`.
* `MonomialData.straighten`: the straightening algorithm of Lemma 3.1.2, which follows the
  unique path of the Morse graph from an attached bar term to a chain.
* `barH` (the homotopy `h`), `barP` (the projection `p`), `barE = i p`: Lemma 3.1.2.
* `barContraction`: `1 - ip = dh + hd`, `pi = 1`, with the side conditions (§2.2.9).

## Conventions

The thesis writes a bar term `[u₀ | ⋯ | u_r]` in homological degree `r + 1`. Bar terms are lists
of words, and the generators of `A` are the letters `x ∈ X`. Only the one-vertex case is stated;
the quiver case (§3.2.3) changes nothing but concatenability.
-/

noncomputable section

namespace TamaroffPhd

open Classical

variable (k : Type) [Field k] {X : Type}

/-! ## The bar construction -/

/-- The bar construction `B A` of the monomial algebra of `W`: finite linear combinations of
bar terms. Terms that are not bar terms (a word is empty or reducible) span nothing; every map
below is defined on a basis and set to `0` off the bar terms. -/
abbrev BarSpace (X : Type) := List (List X) →₀ k

/-- The basis element `[u₀ | ⋯ | u_r]`. -/
def bar (us : List (List X)) : BarSpace k X := Finsupp.single us 1

/-- The linear extension of a function on bar terms, which is `0` on lists that are not bar
terms. -/
def barExtend {V : Type} [AddCommGroup V] [Module k V] (W : Set (List X))
    (f : List (List X) → V) : BarSpace k X →ₗ[k] V :=
  Finsupp.linearCombination k fun us => if (MonomialData.ofRelations W).IsBarTerm us then f us else 0

/-- The signed merge of the bars `i - 1` and `i` of `[u₀ | ⋯ | u_r]`: `0` if the product
`u_{i-1} u_i` contains a relation (it is zero in `A`). The sign is `(-1)^i`, the standard sign of the bar
differential.

**Note.** The proof of Lemma 3.1.2 says the sign is `(-1)^N`, `N` the number of terms preceding
the first factor. Counting the terms up to and including the first factor, `N = i`, matches the
signs `(-1)^{i+1}` of the terms `γᵃ` there: with it `d γ¹ = Γ¹ + ⋯`, which is what
`1 - e = d h + h d` needs (checked on `[yx]` in `k⟨x, y⟩/(xy)`). -/
def mergeAt (W : Set (List X)) (us : List (List X)) (i : ℕ) : BarSpace k X :=
  if (MonomialData.ofRelations W).ProdZero (us.getD (i - 1) []) (us.getD i []) then 0
  else (-1 : k) ^ i • bar k ((us.take (i - 1)) ++ [us.getD (i - 1) [] ++ us.getD i []] ++
    us.drop (i + 1))

/-- **The differential of `B A`.** `d[u₀ | ⋯ | u_r] = ∑_{i=1}^{r} (-1)^{i} [⋯ | u_{i-1} u_i | ⋯]`
(Subsection 2.2.8). Here `A` is augmented, so the end terms of the bar differential vanish. -/
def barDiff (W : Set (List X)) : BarSpace k X →ₗ[k] BarSpace k X :=
  barExtend k W fun us => ∑ i ∈ Finset.Icc 1 (us.length - 1), mergeAt k W us i

/-- **The coproduct `Δ'₂` of `B A`** (§3.1.1): the deconcatenation
`[u₀ | ⋯ | u_r] ↦ ∑_{j=1}^{r} [u₀ | ⋯ | u_{j-1}] ⊗ [u_j | ⋯ | u_r]`, without signs. -/
def barDelta (W : Set (List X)) : BarSpace k X →ₗ[k] (List (List X) × List (List X) →₀ k) :=
  barExtend k W fun us => ∑ j ∈ Finset.Icc 1 (us.length - 1),
    Finsupp.single (us.take j, us.drop j) 1

/-! ## The straightening algorithm (Lemma 3.1.2) -/

namespace MonomialData

variable (M : MonomialData X)

/-- `Splits us i a b`: the `i`-th bar of `us` is `a b` with `a`, `b` non-empty, and
`[u₀ | ⋯ | u_{i-1} | a]` is a critical bar term, i.e. an Anick chain with its bar structure. -/
def Splits (us : List (List X)) (i : ℕ) (a b : List X) : Prop :=
  us[i]? = some (a ++ b) ∧ a ≠ [] ∧ b ≠ [] ∧ M.IsCriticalBarTerm (us.take i ++ [a])

/-- The largest `i ≥ lo` for which the `i`-th bar can be split as in `Splits`, together with
the split (§3.1.2: "there is a largest `i₁` such that `uᵢ = u'ᵢ u''ᵢ` and `[u₀ | ⋯ | u'ᵢ]` is a
chain"). The split of a given bar is unique: `a` is the shortest prefix such that
`u_{i-1} a` contains a relation. -/
def lastSplit (lo : ℕ) (us : List (List X)) : Option (ℕ × List X × List X) :=
  if h : ∃ i, lo ≤ i ∧ ∃ a b, M.Splits us i a b then
    let i := Nat.findGreatest (fun i => lo ≤ i ∧ ∃ a b, M.Splits us i a b) us.length
    if h' : ∃ a b, M.Splits us i a b then some (i, h'.choose, h'.choose_spec.choose) else none
  else none

/-- One step of the algorithm: from `γ = [u₀ | ⋯ | u_r]` with split `(i, a, b)` produce
`γ¹ = (-1)^{i+1} [u₀ | ⋯ | a | b | u_{i+1} | ⋯ | u_r]` and
`Γ¹ = [u₀ | ⋯ | a | b u_{i+1} | ⋯ | u_r]`, which is `none` when `i = r` or when `b u_{i+1}`
contains a relation (then `Γ¹` is zero). -/
def stepTerms (us : List (List X)) (i : ℕ) (a b : List X) :
    (ℤ × List (List X)) × Option (List (List X)) :=
  (((-1) ^ (i + 1), us.take i ++ [a, b] ++ us.drop (i + 1)),
    match us[i + 1]? with
    | none => none
    | some v => if (∃ w ∈ M.W, w <:+: b ++ v) then none
        else some (us.take i ++ [a, b ++ v] ++ us.drop (i + 2)))

/-- **Lemma 3.1.2 (algorithm).** `straighten fuel lo γ` is the pair of the list of terms
`γ¹, γ², …` (with signs) and the final term `Γ` (`none` if it is zero). The indices of the
successive splits are strictly increasing, which is why the search starts at `lo`; `fuel`
bounds the number of steps (at most the number of bars). -/
def straighten : ℕ → ℕ → List (List X) → List (ℤ × List (List X)) × Option (List (List X))
  | 0, _, us => ([], if M.IsCriticalBarTerm us then some us else none)
  | fuel + 1, lo, us =>
      match M.lastSplit lo us with
      | none => ([], if M.IsCriticalBarTerm us then some us else none)
      | some (i, a, b) =>
          match M.stepTerms us i a b with
          | (g, none) => ([g], none)
          | (g, some Γ) =>
              let r := straighten fuel (i + 1) Γ
              (g :: r.1, r.2)

end MonomialData

/-! ## The contraction -/

section Contraction

variable (W : Set (List X))

/-- **Lemma 3.1.2 (the homotopy `h`).** On an attached bar term, `h(γ) = ∑ γⁱ`; it vanishes on
terms that are not attached (those are sources of matched edges of the Morse graph) and on
critical terms. -/
def barH : BarSpace k X →ₗ[k] BarSpace k X :=
  barExtend k W fun us =>
    if (MonomialData.ofRelations W).IsAttached us then
      ((MonomialData.ofRelations W).straighten us.length 0 us).1.foldr
        (fun g acc => (g.1 : k) • bar k g.2 + acc) 0
    else 0

/-- **Lemma 3.1.2 (the projection `p`).** On an attached bar term, `p(γ) = Γ`, the chain at the
end of the algorithm (`0` if it ends at a zero term); `p` vanishes on non-attached terms. As a
map to `B A` its image lies in the span of the critical terms. -/
def barP : BarSpace k X →ₗ[k] BarSpace k X :=
  barExtend k W fun us =>
    if (MonomialData.ofRelations W).IsAttached us then
      match ((MonomialData.ofRelations W).straighten us.length 0 us).2 with
      | some Γ => bar k Γ
      | none => 0
    else 0

/-- The span of the critical bar terms: the chains with their bar structure, a copy of `Tor_A`
inside `B A` (§3.1.1; the inclusion `i`). -/
def critSpan : Submodule k (BarSpace k X) :=
  Submodule.span k {b | ∃ us, (MonomialData.ofRelations W).IsCriticalBarTerm us ∧ b = bar k us}

variable (W : Set (List X)) in
/-- `barExtend` on a basis element. -/
theorem barExtend_bar {V : Type} [AddCommGroup V] [Module k V] (f : List (List X) → V)
    (us : List (List X)) :
    barExtend k W f (bar k us) = if (MonomialData.ofRelations W).IsBarTerm us then f us else 0 := by
  simp [barExtend, bar, Finsupp.linearCombination_single]

/-- A critical bar term admits no split: `[u₀ | ⋯ | a]` critical forces `ProdZeroMinimally`
on the last pair, which fails as soon as `a` is a proper prefix of `u_i`. -/
theorem lastSplit_critical (lo : ℕ) (us : List (List X))
    (h : (MonomialData.ofRelations W).IsCriticalBarTerm us) :
    (MonomialData.ofRelations W).lastSplit lo us = none := by
  have key : ∀ i a b, ¬ (MonomialData.ofRelations W).Splits us i a b := by
    intro i a b ⟨hi, ha, hb, hcrit⟩
    obtain ⟨hbar, ⟨x, u, hxu⟩, hch⟩ := h
    obtain ⟨hbar', ⟨y, v, hyv⟩, hch'⟩ := hcrit
    rcases i with _ | i
    · subst hxu
      simp at hyv hi
      have hay : a = [y] := by simpa using hyv.1
      subst hay
      have h2 : ([x] : List X).length = ([y] ++ b).length := by rw [hi]
      simp at h2
      exact hb h2
    · have hlen : i + 1 < us.length := by
        by_contra hc; simp [List.getElem?_eq_none (by omega : us.length ≤ i + 1)] at hi
      have h1 := List.isChain_iff_getElem.1 hch i (by omega)
      have h2 := List.isChain_iff_getElem.1 hch' i (by simp; omega)
      have hget : us[i + 1] = a ++ b := by
        rw [List.getElem?_eq_getElem hlen] at hi; exact Option.some.inj hi
      simp only [List.getElem_append, List.getElem_take, List.length_take] at h2
      have hl : ¬ (i + 1 < min (i + 1) us.length) := by omega
      have h2' := h2.1
      simp [hl] at h2'
      rw [dif_pos (by omega)] at h2'
      refine h1.2 a ?_ ?_ h2'
      · rw [hget]; exact List.prefix_append _ _
      · rw [hget]; intro e
        have := congrArg List.length e
        simp at this
        exact hb this
  unfold MonomialData.lastSplit
  rw [dif_neg]
  rintro ⟨i, -, a, b, hs⟩
  exact key i a b hs

theorem straighten_critical (fuel lo : ℕ) (us : List (List X))
    (h : (MonomialData.ofRelations W).IsCriticalBarTerm us) :
    (MonomialData.ofRelations W).straighten fuel lo us = ([], some us) := by
  cases fuel with
  | zero => simp [MonomialData.straighten, h]
  | succ n => simp [MonomialData.straighten, lastSplit_critical W lo us h, h]

/-- The final term of the algorithm is critical (or the result is zero). -/
theorem straighten_final (M : MonomialData X) : ∀ (fuel lo : ℕ) (us : List (List X)) (Γ : List (List X)),
    (M.straighten fuel lo us).2 = some Γ → M.IsCriticalBarTerm Γ := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo us Γ h
      simp only [MonomialData.straighten] at h
      split_ifs at h with hc
      · cases h; exact hc
  | succ n ih =>
      intro lo us Γ h
      simp only [MonomialData.straighten] at h
      split at h
      · split_ifs at h with hc
        cases h; exact hc
      · rename_i i a b hs
        split at h
        · simp at h
        · exact ih _ _ _ h

theorem barH_critical (us : List (List X))
    (h : (MonomialData.ofRelations W).IsCriticalBarTerm us) : barH k W (bar k us) = 0 := by
  simp [barH, barExtend_bar, h.1, straighten_critical W _ 0 us h]

theorem barP_critical (us : List (List X))
    (h : (MonomialData.ofRelations W).IsCriticalBarTerm us)
    (hatt : (MonomialData.ofRelations W).IsAttached us) : barP k W (bar k us) = bar k us := by
  simp [barP, barExtend_bar, h.1, hatt, straighten_critical W _ 0 us h]

/-- The differential vanishes on critical bar terms: all the products `u_{i-1} u_i` contain a
relation. -/
theorem barDiff_critical (us : List (List X))
    (h : (MonomialData.ofRelations W).IsCriticalBarTerm us) : barDiff k W (bar k us) = 0 := by
  obtain ⟨hb, -, hc⟩ := h
  have hz : ∀ i ∈ Finset.Icc 1 (us.length - 1), mergeAt k W us i = 0 := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hrel := List.isChain_iff_getElem.1 hc (i - 1) (by omega)
    have e : i - 1 + 1 = i := by omega
    simp only [e] at hrel
    have hz : (MonomialData.ofRelations W).ProdZero (us.getD (i - 1) []) (us.getD i []) := by
      rw [List.getD_eq_getElem _ _ (by omega : i - 1 < us.length),
        List.getD_eq_getElem _ _ (by omega : i < us.length)]
      exact hrel.1
    rw [mergeAt, if_pos hz]
  simp only [barDiff, bar, barExtend, Finsupp.linearCombination_single, one_smul, hb, if_true]
  exact Finset.sum_eq_zero hz

theorem isAttached_of_critical (us : List (List X))
    (h : (MonomialData.ofRelations W).IsCriticalBarTerm us) :
    (MonomialData.ofRelations W).IsAttached us :=
  h.2.2.imp fun _ _ hh => hh.1

theorem barP_mem (x : BarSpace k X) : barP k W x ∈ critSpan k W := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | single us r =>
      have : Finsupp.single us r = r • bar k us := by simp [bar]
      rw [this, map_smul]
      refine Submodule.smul_mem _ _ ?_
      simp only [barP, barExtend_bar]
      split_ifs with h1 h2
      · split
        · rename_i Γ hΓ
          exact Submodule.subset_span ⟨Γ, straighten_final _ _ _ _ _ hΓ, rfl⟩
        · exact zero_mem _
      · exact zero_mem _
      · exact zero_mem _

theorem critSpan_props :
    ∀ x ∈ critSpan k W, barP k W x = x ∧ barDiff k W x = 0 ∧ barH k W x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨us, hus, rfl⟩ := hy
      exact ⟨barP_critical k W us hus (isAttached_of_critical W us hus), barDiff_critical k W us hus,
        barH_critical k W us hus⟩
  | zero => simp
  | add x y _ _ hx hy => simp [hx.1, hy.1, hx.2.1, hy.2.1, hx.2.2, hy.2.2]
  | smul r x _ hx => simp [hx.1, hx.2.1, hx.2.2]

theorem not_prodZero_of_isNormal (M : MonomialData X) {a b : List X} (h : M.IsNormal (a ++ b)) :
    ¬ M.ProdZero a b := by
  intro ⟨w, hw, hdiv⟩
  exact h.2 w hw hdiv

theorem isNormal_prefix (W : Set (List X)) {u v : List X} (hp : u <+: v) (hu : u ≠ [])
    (hv : (MonomialData.ofRelations W).IsNormal v) :
    (MonomialData.ofRelations W).IsNormal u := by
  refine ⟨hu, fun w hw ⟨s, t, hst⟩ => ?_⟩
  obtain ⟨r, rfl⟩ := hp
  refine hv.2 w hw ⟨s, t ++ r, ?_⟩
  rw [← List.append_assoc, ← hst, List.append_assoc, List.append_assoc]

theorem isBarTerm_stepTerms_gamma (W : Set (List X)) {us : List (List X)} {i : ℕ} {a b : List X}
    (hbar : (MonomialData.ofRelations W).IsBarTerm us)
    (hsp : (MonomialData.ofRelations W).Splits us i a b)
    {Γ : List (List X)}
    (hΓ : ((MonomialData.ofRelations W).stepTerms us i a b).2 = some Γ) :
    (MonomialData.ofRelations W).IsBarTerm Γ := by
  intro u hu
  unfold MonomialData.stepTerms at hΓ
  dsimp at hΓ
  split at hΓ
  · contradiction
  · rename_i v hv
    by_cases hw : ∃ w ∈ (MonomialData.ofRelations W).W, w <:+: b ++ v
    · simp [hw] at hΓ
    · simp [hw] at hΓ
      cases hΓ
      simp only [List.mem_append, List.mem_cons] at hu
      have hget : us[i]? = some (a ++ b) := hsp.1
      have hi : i < us.length := by
        by_contra hc; simp [List.getElem?_eq_none (by omega : us.length ≤ i)] at hget
      have hget' : us[i] = a ++ b := by
        rw [List.getElem?_eq_getElem hi] at hget; exact Option.some.inj hget
      rcases hu with (hu | hu | hu | hu)
      · have : u ∈ us := List.mem_of_mem_take hu; exact hbar u this
      · rw [hu]
        refine ⟨hsp.2.1, ?_⟩
        have hnorm_ab : (MonomialData.ofRelations W).IsNormal (a ++ b) := by
          have : a ++ b ∈ us := by rw [← hget']; exact List.getElem_mem hi
          exact (hbar _ this).2
        exact isNormal_prefix W (List.prefix_append a b) hsp.2.1 hnorm_ab
      · rw [hu]
        have hbv : b ++ v ≠ [] := by cases b with | nil => exact (hsp.2.2.1 rfl).elim | cons _ _ => intro; contradiction
        refine ⟨hbv, ⟨hbv, fun w hw' hdiv => hw ⟨w, hw', hdiv⟩⟩⟩
      · have : u ∈ us := List.mem_of_mem_drop hu; exact hbar u this

theorem not_isAttached_stepTerms (M : MonomialData X) {us : List (List X)} {i : ℕ} {a b : List X}
    (hi : i < us.length) (_hab : us[i] = a ++ b) (hnorm : M.IsNormal (a ++ b)) :
    ¬ M.IsAttached (us.take i ++ [a, b] ++ us.drop (i + 1)) := by
  intro hatt
  have e_assoc : us.take i ++ [a, b] ++ us.drop (i + 1) = us.take i ++ ([a, b] ++ us.drop (i + 1)) := by
    rw [List.append_assoc]
  rw [e_assoc] at hatt
  have hlen_take : (us.take i).length = i := List.length_take_of_le (by omega)
  have hch := List.isChain_iff_getElem.1 hatt i (by
    rw [List.length_append, List.length_append, List.length_drop, hlen_take]
    simp; omega)
  simp only [List.getElem_append] at hch
  have hl1 : ¬ (i < (us.take i).length) := by rw [hlen_take]; omega
  have hl2 : ¬ (i + 1 < (us.take i).length) := by rw [hlen_take]; omega
  simp only [hl1, hl2, dite_false] at hch
  have e1 : i - (us.take i).length = 0 := by rw [hlen_take]; omega
  have e2 : i + 1 - (us.take i).length = 1 := by rw [hlen_take]; omega
  simp only [e1, e2] at hch
  exact not_prodZero_of_isNormal M hnorm hch

theorem splits_of_lastSplit (M : MonomialData X) {lo : ℕ} {us : List (List X)} {i : ℕ} {a b : List X}
    (h : M.lastSplit lo us = some (i, a, b)) : M.Splits us i a b := by
  unfold MonomialData.lastSplit at h
  split_ifs at h with h1
  dsimp only at h
  split_ifs at h with h2
  · cases h
    exact h2.choose_spec.choose_spec

theorem straighten_not_attached (fuel lo : ℕ) (us : List (List X))
    (hus : (MonomialData.ofRelations W).IsBarTerm us) :
    ∀ g ∈ ((MonomialData.ofRelations W).straighten fuel lo us).1,
      ¬ (MonomialData.ofRelations W).IsAttached g.2 := by
  induction fuel generalizing lo us with
  | zero => simp [MonomialData.straighten]
  | succ fuel ih =>
    intro g hg
    cases hs : (MonomialData.ofRelations W).lastSplit lo us with
    | none => simp [MonomialData.straighten, hs] at hg
    | some split =>
      obtain ⟨i, a, b⟩ := split
      have hsp := splits_of_lastSplit (MonomialData.ofRelations W) hs
      have hi : i < us.length := by
        by_contra hc
        have he := hsp.1
        rw [List.getElem?_eq_none (by omega)] at he
        contradiction
      have hab : us[i] = a ++ b := by
        have he := hsp.1
        rw [List.getElem?_eq_getElem hi] at he
        exact Option.some.inj he
      have hnot := not_isAttached_stepTerms (MonomialData.ofRelations W) hi hab
        (hus _ (by rw [← hab]; exact List.getElem_mem hi)).2
      cases ht : ((MonomialData.ofRelations W).stepTerms us i a b).2 with
      | none =>
        have he : (MonomialData.ofRelations W).stepTerms us i a b =
            (((-1) ^ (i + 1), us.take i ++ [a, b] ++ us.drop (i + 1)), none) :=
          Prod.ext rfl ht
        simp only [MonomialData.straighten, hs, he, List.mem_singleton] at hg
        subst g
        exact hnot
      | some Γ =>
        have he : (MonomialData.ofRelations W).stepTerms us i a b =
            (((-1) ^ (i + 1), us.take i ++ [a, b] ++ us.drop (i + 1)), some Γ) :=
          Prod.ext rfl ht
        simp only [MonomialData.straighten, hs, he, List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact hnot
        · exact ih (i + 1) Γ (isBarTerm_stepTerms_gamma W hus hsp ht) g hg

theorem barP_of_not_isAttached (us : List (List X))
    (h : ¬ (MonomialData.ofRelations W).IsAttached us) : barP k W (bar k us) = 0 := by
  simp [barP, barExtend_bar, h]

theorem barH_of_not_isAttached (us : List (List X))
    (h : ¬ (MonomialData.ofRelations W).IsAttached us) : barH k W (bar k us) = 0 := by
  simp [barH, barExtend_bar, h]

/-- **Lemma 3.1.2, `1 - e = d h + h d`.** The core of the contraction; not yet proved. -/
theorem barContraction_homotopy (hW : (MonomialData.ofRelations W).IsMinimal) :
    barDiff k W ∘ₗ barH k W + barH k W ∘ₗ barDiff k W = LinearMap.id - barP k W := by
  sorry

/-- A linear map vanishing on non-attached terms kills the homotopy, since each
straightening term splits a normal word into two factors with nonzero product. Used for
the side conditions of the contraction. -/
theorem comp_barH_eq_zero (F : BarSpace k X →ₗ[k] BarSpace k X)
    (hF : ∀ us, ¬ (MonomialData.ofRelations W).IsAttached us → F (bar k us) = 0) :
    F ∘ₗ barH k W = 0 := by
  apply Finsupp.lhom_ext
  intro us c
  have he : Finsupp.single us c = c • bar k us := by simp [bar]
  rw [he]
  simp only [map_smul, LinearMap.comp_apply, LinearMap.zero_apply]
  apply congrArg (c • ·)
  by_cases hus : (MonomialData.ofRelations W).IsBarTerm us
  · by_cases hatt : (MonomialData.ofRelations W).IsAttached us
    · rw [barH, barExtend_bar, ite_eq_left hus, ite_eq_left hatt]
      have hterms := straighten_not_attached W us.length 0 us hus
      generalize hr : ((MonomialData.ofRelations W).straighten us.length 0 us).1 = gs at *
      clear hr
      induction gs with
      | nil => simp
      | cons g gs ih =>
        simp only [List.foldr_cons, map_add, map_smul]
        rw [hF g.2 (hterms g (by simp)), ih (fun g hg => hterms g (by simp [hg]))]
        simp
    · rw [barH_of_not_isAttached k W us hatt, map_zero]
  · rw [barH, barExtend_bar, ite_eq_right hus, map_zero]

/-- **§2.2.9 side conditions** `p h = 0`, `h h = 0`. -/
theorem barContraction_side (_hW : (MonomialData.ofRelations W).IsMinimal) :
    barP k W ∘ₗ barH k W = 0 ∧ barH k W ∘ₗ barH k W = 0 := by
  exact ⟨comp_barH_eq_zero k W (barP k W) (barP_of_not_isAttached k W),
    comp_barH_eq_zero k W (barH k W) (barH_of_not_isAttached k W)⟩

/-- **§3.1.1 (contraction).** For `A = k⟨X⟩/(W)` with `W` minimal, `(i, p, h)` is a homotopy
retract of `B A` onto `Tor_A`, written in terms of `e = i p`:
* `1 - e = d h + h d`;
* `p` takes values in the critical terms and is the identity on them (`p i = 1`);
* `Tor_A` has zero differential (`d` vanishes on critical terms);
* the side conditions `h i = 0`, `p h = 0`, `h h = 0` (§2.2.9). -/
theorem barContraction (hW : (MonomialData.ofRelations W).IsMinimal) :
    (barDiff k W ∘ₗ barH k W + barH k W ∘ₗ barDiff k W = LinearMap.id - barP k W) ∧
    (∀ x, barP k W x ∈ critSpan k W) ∧
    (∀ x ∈ critSpan k W, barP k W x = x ∧ barDiff k W x = 0 ∧ barH k W x = 0) ∧
    barP k W ∘ₗ barH k W = 0 ∧ barH k W ∘ₗ barH k W = 0 :=
  ⟨barContraction_homotopy k W hW, barP_mem k W, critSpan_props k W,
    (barContraction_side k W hW).1, (barContraction_side k W hW).2⟩

/-- Apply a map of `B A` to the left tensor factor of `B A ⊗ B A`, identified with finitely
supported functions on pairs of bar terms. -/
def mapLeft (f : BarSpace k X →ₗ[k] BarSpace k X) :
    (List (List X) × List (List X) →₀ k) →ₗ[k] (List (List X) × List (List X) →₀ k) :=
  Finsupp.linearCombination k fun ab =>
    (f (bar k ab.1)).sum fun c r => r • Finsupp.single (c, ab.2) 1

/-- Evaluation on a pure tensor, used in Corollary 3.1.5. -/
theorem mapLeft_single (f : BarSpace k X →ₗ[k] BarSpace k X) (us vs : List (List X)) :
    mapLeft k f (Finsupp.single (us, vs) 1) =
      Finsupp.lmapDomain k k (fun cs => (cs, vs)) (f (bar k us)) := by
  simp [mapLeft, Finsupp.linearCombination_single, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain, Finsupp.smul_single, mul_one]

/-- Acting on a fixed right tensor factor, used in Corollary 3.1.5. -/
theorem mapLeft_lmapDomain (f : BarSpace k X →ₗ[k] BarSpace k X)
    (vs : List (List X)) (x : BarSpace k X) :
    mapLeft k f (Finsupp.lmapDomain k k (fun cs => (cs, vs)) x) =
      Finsupp.lmapDomain k k (fun cs => (cs, vs)) (f x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single us c =>
    have he : Finsupp.single us c = c • bar k us := by simp [bar]
    rw [he]
    simp only [map_smul]
    congr 1
    simp [mapLeft, bar, Finsupp.linearCombination_single, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain, Finsupp.smul_single, mul_one]

/-- Tensoring on the right preserves composition, used in Corollary 3.1.5. -/
theorem mapLeft_comp (f g : BarSpace k X →ₗ[k] BarSpace k X) :
    mapLeft k f ∘ₗ mapLeft k g = mapLeft k (f ∘ₗ g) := by
  apply Finsupp.lhom_ext
  rintro ⟨us, vs⟩ c
  have he : Finsupp.single (us, vs) c = c • Finsupp.single (us, vs) 1 := by simp
  rw [he]
  simp only [map_smul, LinearMap.comp_apply]
  congr 1
  rw [mapLeft_single, mapLeft_lmapDomain, mapLeft_single]
  rfl

/-- `Tor_A ⊗ B A` inside `B A ⊗ B A`: pairs whose left factor is a critical bar term. -/
def torTensorBar : Submodule k (List (List X) × List (List X) →₀ k) :=
  Submodule.span k {t | ∃ us vs, (MonomialData.ofRelations W).IsCriticalBarTerm us ∧
    t = Finsupp.single (us, vs) 1}

/-- **Lemma 3.1.4 (exchange rule).** On an attached bar term, `Δ'₂ h = (h ⊗ 1) Δ'₂`
modulo `Tor_A ⊗ B A`. -/
theorem barDelta_barH_exchange (us : List (List X))
    (hus : (MonomialData.ofRelations W).IsBarTerm us ∧ (MonomialData.ofRelations W).IsAttached us) :
    barDelta k W (barH k W (bar k us)) - mapLeft k (barH k W) (barDelta k W (bar k us)) ∈
      torTensorBar k W := by
  sorry

/-- **Corollary 3.1.5.** `(h ⊗ 1) Δ'₂ h = 0` on attached bar terms. -/
theorem mapLeft_barH_barDelta_barH (us : List (List X))
    (hus : (MonomialData.ofRelations W).IsBarTerm us ∧ (MonomialData.ofRelations W).IsAttached us) :
    mapLeft k (barH k W) (barDelta k W (barH k W (bar k us))) = 0 := by
  have hkill : ∀ x ∈ torTensorBar k W, mapLeft k (barH k W) x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨us, vs, hus, rfl⟩ := hx
      rw [mapLeft_single, barH_critical k W us hus, map_zero]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  have hsq : barH k W ∘ₗ barH k W = 0 :=
    comp_barH_eq_zero k W (barH k W) (barH_of_not_isAttached k W)
  have hleftsq : mapLeft k (barH k W) ∘ₗ mapLeft k (barH k W) = 0 := by
    rw [mapLeft_comp, hsq]
    ext x
    simp [mapLeft]
  have he := hkill _ (barDelta_barH_exchange k W us hus)
  rw [map_sub] at he
  have hz := LinearMap.congr_fun hleftsq (barDelta k W (bar k us))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  rwa [hz, sub_zero] at he

end Contraction

end TamaroffPhd

end
