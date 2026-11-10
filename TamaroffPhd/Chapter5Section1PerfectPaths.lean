import TamaroffPhd.Chapter3MinimalModels

/-!
# Chapter 5, §5.1: perfect paths and Gorenstein algebras (definitions)

Throughout, `Λ = kQ/(R)` is a monomial quiver algebra (Chapter 2, §1.2): `Q` finite, `R` a
minimal set of relation paths, `Λ` finite dimensional. Modules are right modules, that is
modules over `Λᵐᵒᵖ`.

## Contents

* Minimal left and right zero cofactors `L(p)`, `R(p)` (5.4–5.5), perfect pairs (Definition 10),
  perfect cycles and their period (Definition 11), perfect paths, perfect walks (Definition 12).
* Gorenstein algebras and the Gorenstein dimension; Gorenstein-projective modules
  (characterised by (5.2)); the right ideals `pΛ`.
* Lemma 1.9, Proposition 1.10 and Corollary 1.11: extending Anick chains.
* Proposition 1.3: syzygies of `k` from the Anick resolution.
* Examples 1 and 2 (`k[t]/(tⁿ)`).

-/

noncomputable section

namespace TamaroffPhd

open Classical MonomialData CategoryTheory Quiv

variable {Q : Quiv} (R : Set (List Q.A))

/-! ## Zero cofactors and perfect paths -/

/-- A non-trivial non-zero path of `Λ`: an element of `P_Λ` (5.3) of positive length. -/
def IsNzPath (p : List Q.A) : Prop := (Q.data R).IsNormal p

/-- **(5.4).** The minimal left zero cofactors `L(p)` of `p`: non-trivial non-zero paths `q`
with `qp` a path, `qp = 0`, and no proper end segment `q'` of `q` with `q'p = 0`. -/
def leftCof (p : List Q.A) : Set (List Q.A) :=
  {q | IsNzPath R q ∧ Q.IsPath (q ++ p) ∧ (Q.data R).ProdZero q p ∧
    ∀ q', q' <:+ q → q' ≠ q → q' ≠ [] → ¬ (Q.data R).ProdZero q' p}

/-- **(5.5).** The minimal right zero cofactors `R(p)` of `p`. -/
def rightCof (p : List Q.A) : Set (List Q.A) :=
  {q | IsNzPath R q ∧ Q.IsPath (p ++ q) ∧ (Q.data R).ProdZero p q ∧
    ∀ q', q' <+: q → q' ≠ q → q' ≠ [] → ¬ (Q.data R).ProdZero p q'}

/-- **Definition 10 (Perfect pair).** `(p, q)` is perfect if `R(p) = {q}` and `L(q) = {p}`. -/
def IsPerfectPair (p q : List Q.A) : Prop :=
  IsNzPath R p ∧ IsNzPath R q ∧ rightCof R p = {q} ∧ leftCof R q = {p}

/-- **Definition 11 (Perfect cycle).** A non-empty cyclic sequence `(p₀, …, p_{r-1})` with all
consecutive pairs `(pᵢ, p_{i+1})` (indices mod `r`) perfect. -/
def IsPerfectCycle (ps : List (List Q.A)) : Prop :=
  ps ≠ [] ∧ ∀ i < ps.length, IsPerfectPair R (ps.getD i []) (ps.getD ((i + 1) % ps.length) [])

/-- **Definition 11 (Period).** The period of a perfect cycle: the least `r ≥ 1` with
`p_{i+r} = pᵢ` for all `i`. -/
def cyclePeriod (ps : List (List Q.A)) : ℕ :=
  sInf {r | 0 < r ∧ ∀ i, ps.getD ((i + r) % ps.length) [] = ps.getD (i % ps.length) []}

/-- **Definition 11.** A path is *perfect* if it occurs in a perfect cycle. -/
def IsPerfect (p : List Q.A) : Prop := ∃ ps, IsPerfectCycle R ps ∧ p ∈ ps

/-- **Definition 12 (Perfect walk).** A sequence `(p₀, …, p_{l-1})`, `l ≥ 1`, that extends
(by periodicity) to a perfect cycle. -/
def IsPerfectWalk (ws : List (List Q.A)) : Prop :=
  ws ≠ [] ∧ ∃ ps, IsPerfectCycle R ps ∧ ∀ i < ws.length, ws.getD i [] = ps.getD (i % ps.length) []

/-- **§5.1.4.** In a perfect walk the next and previous paths are determined:
`R(pᵢ) = {p_{i+1}}` and `L(pᵢ) = {p_{i-1}}`. -/
theorem IsPerfectWalk.rightCof_eq {ws : List (List Q.A)} (h : IsPerfectWalk R ws) (i : ℕ)
    (hi : i + 1 < ws.length) : rightCof R (ws.getD i []) = {ws.getD (i + 1) []} := by
  obtain ⟨_, ps, hps, hws⟩ := h
  have hlen : 0 < ps.length := List.length_pos_iff.mpr hps.1
  have hp := hps.2 (i % ps.length) (Nat.mod_lt _ hlen)
  rw [hws i (by omega), hws (i + 1) hi]
  simpa only [Nat.add_mod, Nat.mod_mod] using hp.2.2.1

/-! ## Extending Anick chains (§5.1.4) -/

/-- **Lemma 1.9 (Extending Anick chains).** (i) `γₙ p` is an `(n+1)`-chain with tail `p` iff
`p ∈ R(t_{γₙ})`. (ii) `q γₙ` is a left `(n+1)`-chain with head `q` iff `q ∈ L(h_{γₙ})`. -/
theorem lemma_1_9 (hR : (Q.data R).IsMinimal) {n : ℕ} {γ : List Q.A} (hγ : γ ∈ (Q.data R).Chains n)
    (p q : List Q.A) :
    ((Q.data R).IsChain (n + 1) (γ ++ p) p ↔ p ∈ rightCof R ((Q.data R).tail n γ)) ∧
    ((Q.data R).IsLeftChain (n + 1) (q ++ γ) q ↔ q ∈ leftCof R ((Q.data R).head n γ)) := by
  sorry

/-- **Proposition 1.10 (Weak unique extension property).** (i) If `t_{γₙ} = p₀` is perfect,
with `R(p₀) = {p₁}`, then `γₙ p₁` is the unique right extension of `γₙ` to an `(n+1)`-chain, with
tail `p₁`. (ii) Dually on the left. -/
theorem prop_1_10 (hR : (Q.data R).IsMinimal) {n : ℕ} {γ : List Q.A}
    (hγ : γ ∈ (Q.data R).Chains n) {p₀ p₁ : List Q.A} (hp : IsPerfectPair R p₀ p₁)
    (ht : (Q.data R).tail n γ = p₀) :
    (Q.data R).IsChain (n + 1) (γ ++ p₁) p₁ ∧
      ∀ α, γ ++ α ∈ (Q.data R).Chains (n + 1) → α = p₁ := by
  have hmem : p₁ ∈ rightCof R ((Q.data R).tail n γ) := by
    rw [ht, hp.2.2.1]
    exact Set.mem_singleton _
  refine ⟨((lemma_1_9 R hR hγ p₁ p₁).1).2 hmem, ?_⟩
  intro α hα
  obtain ⟨t, htchain⟩ := hα
  have hfull := htchain
  obtain ⟨_, _, ⟨c', t', hc', heq, _⟩, _⟩ := htchain
  obtain ⟨tγ, hγchain⟩ := hγ
  have hprefix : c' = γ := by
    have hp₁ : c' <+: γ ++ α := ⟨t, heq.symm⟩
    have hp₂ : γ <+: γ ++ α := List.prefix_append _ _
    rcases List.prefix_or_prefix_of_prefix hp₁ hp₂ with h₁ | h₂
    · by_contra hne
      exact hγchain.not_prefix h₁ hne hc'
    · by_contra hne
      exact hc'.not_prefix h₂ (Ne.symm hne) hγchain
  have htail : t = α := by
    rw [hprefix] at heq
    exact List.append_cancel_left heq.symm
  have htα : (Q.data R).IsChain (n + 1) (γ ++ α) α := by
    simpa only [htail] using hfull
  have hcof := ((lemma_1_9 R hR ⟨tγ, hγchain⟩ α α).1).1 htα
  rw [ht, hp.2.2.1, Set.mem_singleton_iff] at hcof
  exact hcof

/-- **Corollary 1.11 (Unique extension property).** (i) If `t_γ = p₀` is perfect, extended to a
perfect walk `(p₀, p₁, …)`, then `γα` is an `(n+k)`-chain for some `k ≥ 1` iff
`α = p₁ ⋯ p_k`, in which case `t_{γα} = p_k`. (Part (ii) is dual.) -/
theorem cor_1_11 (hR : (Q.data R).IsMinimal) {n : ℕ} {γ : List Q.A}
    (hγ : γ ∈ (Q.data R).Chains n) {ws : List (List Q.A)} (hw : IsPerfectWalk R ws)
    (ht : (Q.data R).tail n γ = ws.getD 0 []) (α : List Q.A) (hα : α ≠ []) :
    (∃ k, 1 ≤ k ∧ γ ++ α ∈ (Q.data R).Chains (n + k)) ↔
      ∃ k, 1 ≤ k ∧ k < ws.length ∧ α = ((ws.drop 1).take k).flatten := by
  sorry

/-- **Corollary 1.11 (ii).** If `h_γ = q₀` is perfect, extended to a perfect walk
`(…, q₋₁, q₀)`, then `αγ` is an `(n+k)`-chain for some `k ≥ 1` iff `α = q₋ₖ ⋯ q₋₁`. -/
theorem cor_1_11_left (hR : (Q.data R).IsMinimal) {n : ℕ} {γ : List Q.A}
    (hγ : γ ∈ (Q.data R).Chains n) {ws : List (List Q.A)} (hw : IsPerfectWalk R ws)
    (hh : (Q.data R).head n γ = ws.getLastD []) (α : List Q.A) (hα : α ≠ []) :
    (∃ k, 1 ≤ k ∧ α ++ γ ∈ (Q.data R).Chains (n + k)) ↔
      ∃ k, 1 ≤ k ∧ k < ws.length ∧ α = ((ws.dropLast.reverse.take k).reverse).flatten := by
  sorry

/-! ## Modules over `Λ` -/

variable (k : Type) [Field k]

/-- The right regular module `Λ_Λ`. -/
abbrev rightReg : ModuleCat (Q.PathAlg k R)ᵐᵒᵖ := ModuleCat.of _ (Q.PathAlg k R)

/-- The left regular module `_Λ Λ`. -/
abbrev leftReg : ModuleCat (Q.PathAlg k R) := ModuleCat.of _ (Q.PathAlg k R)

/-- **§5.1.1 (Gorenstein algebra).** `Λ` is Gorenstein if `injdim Λ_Λ` and `injdim _ΛΛ` are
finite. -/
def IsGorenstein : Prop :=
  injectiveDimension (rightReg R k) ≠ ⊤ ∧ injectiveDimension (leftReg R k) ≠ ⊤

/-- **§5.1.1.** `Λ` is Gorenstein of dimension at most `d`. -/
def IsGorensteinLE (d : ℕ) : Prop :=
  injectiveDimension (rightReg R k) ≤ d ∧ injectiveDimension (leftReg R k) ≤ d

/-- **§5.1.1 (Gorenstein dimension).** `dim Λ`, the common value of the two injective
dimensions (Zaks), taken as the right one. -/
def gorDim : WithBot ℕ∞ := injectiveDimension (rightReg R k)

/-- The right ideal `pΛ` generated by a path, as a right module. -/
abbrev pathIdeal (p : List Q.A) : ModuleCat (Q.PathAlg k R)ᵐᵒᵖ :=
  ModuleCat.of _ (Submodule.span (Q.PathAlg k R)ᵐᵒᵖ {pathElt (k := k) R p})

/-- The left ideal `Λq` generated by a path, as a left module. -/
abbrev pathIdealLeft (q : List Q.A) : ModuleCat (Q.PathAlg k R) :=
  ModuleCat.of _ (Submodule.span (Q.PathAlg k R) {pathElt (k := k) R q})

/-- The dual `M* = Hom_Λ(M, Λ)` of a right module, a left module. -/
abbrev dualRight (M : ModuleCat (Q.PathAlg k R)ᵐᵒᵖ) : ModuleCat (Q.PathAlg k R) :=
  ModuleCat.of _ (M →ₗ[(Q.PathAlg k R)ᵐᵒᵖ] Q.PathAlg k R)

/-- The dual of a left module, a right module. -/
abbrev dualLeft (N : ModuleCat (Q.PathAlg k R)) : ModuleCat (Q.PathAlg k R)ᵐᵒᵖ :=
  ModuleCat.of _ (N →ₗ[Q.PathAlg k R] Q.PathAlg k R)

/-- The evaluation map `M → M**`, `m ↦ (f ↦ f m)`. -/
def evalDD (M : ModuleCat (Q.PathAlg k R)ᵐᵒᵖ) : M → dualLeft R k (dualRight R k M) :=
  fun m => { toFun := fun f => f m, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

/-- **(5.2) (Gorenstein-projective).** `Extⁱ_Λ(M, Λ) = 0` and `Extⁱ_{Λᵒᵖ}(M*, Λ) = 0` for
`i > 0`, and `M` is reflexive.

**Change.** The thesis defines Gorenstein-projective modules by complete
resolutions and quotes the equivalent condition (5.2) [35, Ch. 4]: `Extⁱ(M, Λ) = 0`,
`Extⁱ(M*, Λ) = 0` for `i > 0`, and `M` reflexive. We take (5.2) as the definition, since
Mathlib has `Ext` but no complete resolutions. -/
def IsGorensteinProjective (M : ModuleCat (Q.PathAlg k R)ᵐᵒᵖ) : Prop :=
  (∀ i, 0 < i → Subsingleton (Abelian.Ext M (rightReg R k) i)) ∧
  (∀ i, 0 < i → Subsingleton (Abelian.Ext (dualRight R k M) (leftReg R k) i)) ∧
  Function.Bijective (evalDD R k M)

/-! ## Syzygies of `k` (Proposition 1.3) -/

/-- **Proposition 1.3.** For `n ≥ 1`, the image `Ωⁿk` of `kC_n ⊗ Λ → kC_{n-1} ⊗ Λ` in the
Anick resolution is `⨁_{γ ∈ C_n} t_γ Λ`: its component at an `(n-1)`-chain `γ'` is the sum of
the `t_γ Λ` over the chains `γ = γ' t_γ`, and that sum is direct. -/
theorem syzygy_eq (hR : (Q.data R).IsMinimal) (n : ℕ) :
    (∀ g, (∃ f ∈ Quiv.anickTerm k Q R (n + 1), Quiv.anickDiff k Q R n f = g) ↔
      g ∈ Quiv.anickTerm k Q R n ∧ ∀ c, g c ∈ Submodule.span (Q.PathAlg k R)ᵐᵒᵖ
        ((fun γ => pathElt (k := k) R ((Q.data R).tail (n + 1) γ)) ''
          {γ | γ ∈ (Q.data R).Chains (n + 1) ∧ γ = c ++ (Q.data R).tail (n + 1) γ})) ∧
    ∀ γ₁ ∈ (Q.data R).Chains (n + 1), ∀ γ₂ ∈ (Q.data R).Chains (n + 1), γ₁ ≠ γ₂ →
      ∀ x y : Q.PathAlg k R, pathElt R ((Q.data R).tail (n + 1) γ₁) * x =
        pathElt R ((Q.data R).tail (n + 1) γ₂) * y → pathElt R ((Q.data R).tail (n + 1) γ₁) * x = 0 := by
  sorry

/-! ## Examples (§5.1.4) -/

/-- The one-loop quiver of `k[t]`. -/
def loopQuiver : Quiv where
  V := Unit
  A := Unit
  src _ := ()
  tgt _ := ()

/-- The relation `tⁿ` of `k[t]/(tⁿ)`. -/
def truncRel (n : ℕ) : Set (List loopQuiver.A) := {List.replicate n ()}

/-- **Example 1.** In `k[t]/(tⁿ)` (`n ≥ 2`), `t^{kn}` is a perfect walk in two ways,
`(t, t^{n-1}, …, t, t^{n-1})` and `(t^{n-1}, t, …, t^{n-1}, t)`. -/
theorem example_1 (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : 1 ≤ j) :
    IsPerfectWalk (truncRel n) ((List.replicate j [List.replicate 1 (), List.replicate (n - 1) ()]).flatten) ∧
    IsPerfectWalk (truncRel n) ((List.replicate j [List.replicate (n - 1) (), List.replicate 1 ()]).flatten) := by
  sorry

/-- **Example 1.** `t^{jn}` is an Anick `(2j - 1)`-chain of `k[t]/(tⁿ)`. -/
theorem example_1_chain (n : ℕ) (hn : 2 ≤ n) (j : ℕ) (hj : 1 ≤ j) :
    List.replicate (j * n) () ∈ (loopQuiver.data (truncRel n)).Chains (2 * j - 1) := by
  sorry

/-- **Example 2.** For `n ≥ 3`, `(t^{n-1}, t, t^{n-1})` is a perfect walk of `k[t]/(tⁿ)` but
`t^{2n-1}` is not an Anick chain. -/
theorem example_2 (n : ℕ) (hn : 3 ≤ n) :
    IsPerfectWalk (truncRel n) [List.replicate (n - 1) (), [()], List.replicate (n - 1) ()] ∧
    ∀ m, List.replicate (2 * n - 1) () ∉ (loopQuiver.data (truncRel n)).Chains m := by
  sorry

end TamaroffPhd

end
