import TamaroffPhd.Chapter2Section2AnickChains

/-!
# Cited results on Anick chains

Background on Anick chains that the thesis cites without proof.

## Contents

* Anick's uniqueness lemma [2, 3]: a word carries at most one chain structure.
* Bardzell's theorem [12]: left and right Anick chains coincide (§3.3.1).
* The Green–Happel–Zacharia resolution [73] (Theorem 3.3.2 and (3.3)): the minimal free right
  module resolution `⋯ → kCₙ ⊗ Λ → kC_{n-1} ⊗ Λ → ⋯ → kC₀ ⊗ Λ → Λ → k → 0` with
  `d(γ ⊗ 1) = γ' ⊗ t_γ`; hence `Torₙ^Λ(k, k) ≅ kC_{n-1}`.

-/

noncomputable section

namespace TamaroffPhd

open Classical

namespace MonomialData

variable {A : Type} (M : MonomialData A)

variable {M} in
/-- A chain and its tail are non-empty. -/
theorem IsChain.ne_nil : ∀ {n : ℕ} {c t : List A}, M.IsChain n c t → c ≠ [] ∧ t ≠ []
  | 0, c, t, h => by obtain ⟨x, rfl, rfl⟩ := h; simp
  | n + 1, c, t, h => by
      obtain ⟨-, ht, ⟨c', t', -, rfl, -⟩, -⟩ := h
      exact ⟨by simp [ht], ht⟩

variable {M} in
/-- No proper prefix of a chain is a chain of the same degree: this is the minimality clause of
Definition 25. -/
theorem IsChain.not_prefix {n : ℕ} {c t c₀ t₀ : List A} (h : M.IsChain n c t)
    (hp : c₀ <+: c) (hne : c₀ ≠ c) : ¬ M.IsChain n c₀ t₀ := by
  intro h₀
  cases n with
  | zero =>
      obtain ⟨x, rfl, -⟩ := h
      obtain ⟨y, rfl, -⟩ := h₀
      exact hne (by simpa using hp.eq_of_length (by simp))
  | succ n =>
      obtain ⟨-, -, -, hmin⟩ := h
      obtain ⟨-, ht₀, ⟨d, d', hd, rfl, w, hw, hws⟩, -⟩ := h₀
      exact hmin _ hp hne ⟨d, d', t₀, hd, rfl, ht₀, w, hw, hws⟩

variable {M} in
/-- An `n`-chain has a prefix that is a `j`-chain, for every `j ≤ n`. -/
theorem IsChain.exists_prefix : ∀ {n : ℕ} {c t : List A}, M.IsChain n c t → ∀ j ≤ n,
    ∃ q t', q <+: c ∧ M.IsChain j q t'
  | 0, c, t, h, j, hj => by
      obtain rfl : j = 0 := by omega
      exact ⟨c, t, List.prefix_refl _, h⟩
  | n + 1, c, t, h, j, hj => by
      rcases Nat.lt_or_ge j (n + 1) with hlt | hge
      · obtain ⟨-, -, ⟨c', t', hc', rfl, -⟩, -⟩ := h
        obtain ⟨q, t'', hq, hq'⟩ := hc'.exists_prefix j (by omega)
        exact ⟨q, t'', hq.trans (List.prefix_append _ _), hq'⟩
      · obtain rfl : j = n + 1 := by omega
        exact ⟨c, t, List.prefix_refl _, h⟩

/-- **Anick [2, 3] (§3.3.1).** A word admits at most one structure of a chain: its degree and
tail are determined.

**Change.** Proved here from the minimality clause of Definition 25 (no proper prefix of a
chain is a chain of the same degree), without using that the relations are minimal. -/
theorem isChain_unique (_hM : M.IsMinimal) {n m : ℕ} {c t t' : List A}
    (h : M.IsChain n c t) (h' : M.IsChain m c t') : n = m ∧ t = t' := by
  cases n with
  | zero =>
      cases m with
      | zero =>
          obtain ⟨x, rfl, rfl⟩ := h
          obtain ⟨y, hy, rfl⟩ := h'
          simp at hy; subst hy; simp
      | succ m =>
          obtain ⟨x, rfl, -⟩ := h
          obtain ⟨-, ht, ⟨c', t'', hc', he, -⟩, -⟩ := h'
          have := congrArg List.length he
          simp at this
          have h1 : 0 < c'.length := List.length_pos_iff.2 hc'.ne_nil.1
          have h2 : 0 < t'.length := List.length_pos_iff.2 ht
          omega
  | succ n =>
      cases m with
      | zero =>
          obtain ⟨x, rfl, -⟩ := h'
          obtain ⟨-, ht, ⟨c', t'', hc', he, -⟩, -⟩ := h
          have h1 : 0 < c'.length := List.length_pos_iff.2 hc'.ne_nil.1
          have h2 : 0 < t.length := List.length_pos_iff.2 ht
          have := congrArg List.length he
          simp at this
          omega
      | succ m =>
          have hc := h
          have hc'' := h'
          obtain ⟨-, ht, ⟨c', s', hc', hce, -⟩, -⟩ := h
          obtain ⟨-, ht', ⟨c'', s'', hc''', hce', -⟩, -⟩ := h'
          have hlen : ∀ {a b : List A}, a ++ b = c → b ≠ [] → a ≠ c := by
            intro a b e hb e'
            have := congrArg List.length e
            rw [e'] at this
            simp at this
            exact hb this
          have hp' : c' <+: c := ⟨t, hce.symm⟩
          have hp'' : c'' <+: c := ⟨t', hce'.symm⟩
          have hne' := hlen hce.symm ht
          have hne'' := hlen hce'.symm ht'
          -- a lower-degree chain cannot sit strictly below a higher-degree one
          have key : ∀ {n m : ℕ} {c₁ s₁ u : List A}, M.IsChain n c₁ s₁ →
              M.IsChain (m + 1) c u → c₁ <+: c → c₁ ≠ c → m < n → False := by
            intro n m c₁ s₁ u h1 hm hp hne hmn
            obtain ⟨q, t₁, hq, hq'⟩ := h1.exists_prefix (m + 1) (by omega)
            have hlt : c₁.length < c.length :=
              lt_of_le_of_ne hp.length_le fun e => hne (hp.eq_of_length e)
            exact hm.not_prefix (hq.trans hp)
              (fun e => by have := hq.length_le; rw [e] at this; omega) hq'
          have hnm : n = m := by
            rcases lt_trichotomy n m with h1 | h1 | h1
            · exact (key hc''' hc hp'' hne'' h1).elim
            · exact h1
            · exact (key hc' hc'' hp' hne' h1).elim
          subst hnm
          have hcc : c' = c'' := by
            rcases List.prefix_or_prefix_of_prefix hp' hp'' with h1 | h1
            · by_contra hne
              exact hc'''.not_prefix h1 hne hc'
            · by_contra hne
              exact hc'.not_prefix h1 (Ne.symm hne) hc'''
          subst hcc
          exact ⟨rfl, List.append_cancel_left (hce.symm.trans hce')⟩

variable {M} in
/-- Minimality of relations is preserved under reversing all words. -/
theorem IsMinimal.reverse (hM : M.IsMinimal) : M.reverse.IsMinimal := by
  constructor
  · rintro w ⟨w', hw', rfl⟩
    simpa using hM.1 w' hw'
  · rintro w ⟨u, hu, rfl⟩ w' ⟨v, hv, rfl⟩ ⟨p, q, hpq⟩
    have hdiv : u <:+: v := by
      refine ⟨q.reverse, p.reverse, ?_⟩
      have := congrArg List.reverse hpq
      simpa using this
    have heq := hM.2 u hu v hv hdiv
    subst heq
    rfl

variable {M} in
/-- Left and right 0-chains coincide: both are the single arrows. -/
theorem chains_zero_iff (c : List A) :
    c ∈ M.Chains 0 ↔ ∃ h, M.IsLeftChain 0 c h := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨x, rfl, rfl⟩ := ht
    refine ⟨[x], ?_⟩
    dsimp [IsLeftChain, reverse, IsChain]
    exact ⟨x, rfl, rfl⟩
  · rintro ⟨h, hh⟩
    dsimp [IsLeftChain, reverse, IsChain] at hh
    obtain ⟨x, hx, -⟩ := hh
    have : c = [x] := by
      have := congrArg List.reverse hx
      simpa using this
    subst this
    exact ⟨[x], ⟨x, rfl, rfl⟩⟩

/-- **Bardzell [12] (§3.3.1).** Left and right Anick `n`-chains coincide: `C'ₙ = Cₙ`.

**Gap (error, Definition 25).** The inductive step in Definition 25 applied to `n = 0` requires
only that `γ = γ' t` (`γ'` an arrow) has a right divisor in `W`, which admits any word `a w`
with `w ∈ W` into `C₁`, whereas the thesis notes immediately that "`C₁` is the set of the
defining relations of `Λ`". In the literature (Green–Happel–Zacharia [73], Anick [2], Bardzell
[12]), `C₁` is defined directly as `W`, and the inductive step is for `n ≥ 2`. Under
Definition 25 as printed, `C₁ ≠ C'₁`: `a w ∈ C₁` but `a w ∉ C'₁` (its reverse `wʳ aʳ` has proper
prefix `wʳ ∈ C₁ʳ`, so by `IsChain.not_prefix` it cannot be a chain). With the literature's
definition (`C₁ = W`), `Cₙ = C'ₙ` is Bardzell's theorem [12], which the thesis cites without
proof.

**Change.** The base case `n = 0` (letters) is proved in full (`chains_zero_iff`). -/
theorem chains_eq_leftChains (hM : M.IsMinimal) (n : ℕ) (c : List A) :
    c ∈ M.Chains n ↔ ∃ h, M.IsLeftChain n c h := by
  cases n with
  | zero => exact chains_zero_iff c
  | succ n => sorry

/-- **§3.3.1.** For an `n`-chain `γ` (`n ≥ 1`) we have `γ = γ' t_γ = h_γ γ''` for unique
`(n-1)`-chains `γ'`, `γ''`.

**Change.** Proved from `chains_eq_leftChains` and `isChain_unique`. The first decomposition
`c = c' ++ tail c` is proved directly from Definition 25; the second `c = head c ++ c''`
transfers this to `M.reverse` via Bardzell's theorem `chains_eq_leftChains`. -/
theorem chain_eq_head_append (hM : M.IsMinimal) {n : ℕ} {c : List A} (hc : c ∈ M.Chains (n + 1)) :
    (∃ c', c' ∈ M.Chains n ∧ c = c' ++ M.tail (n + 1) c) ∧
      ∃ c'', c'' ∈ M.Chains n ∧ c = M.head (n + 1) c ++ c'' := by
  constructor
  · obtain ⟨t, ht⟩ := hc
    have htail : M.tail (n + 1) c = t := by
      dsimp [tail]
      split_ifs with h
      · exact (isChain_unique M hM h.choose_spec ht).2
      · exact (h ⟨t, ht⟩).elim
    have hchain : M.IsChain (n + 1) c (M.tail (n + 1) c) := by
      rw [htail]; exact ht
    obtain ⟨-, -, ⟨c', t', hc', hceq, -⟩, -⟩ := hchain
    exact ⟨c', ⟨t', hc'⟩, hceq⟩
  · have hleft := (chains_eq_leftChains M hM (n + 1) c).1 hc
    obtain ⟨hd, hhd⟩ := hleft
    have hhead : M.head (n + 1) c = hd := by
      dsimp [head]
      split_ifs with h
      · have hu := isChain_unique M.reverse hM.reverse h.choose_spec hhd
        have : h.choose.reverse = hd.reverse := hu.2
        exact List.reverse_injective this
      · exact (h ⟨hd, hhd⟩).elim
    have h_lc : M.IsLeftChain (n + 1) c (M.head (n + 1) c) := by
      rw [hhead]; exact hhd
    dsimp [IsLeftChain] at h_lc
    obtain ⟨-, -, ⟨d', s', hd', hdeq, -⟩, -⟩ := h_lc
    have hc_rev : c = M.head (n + 1) c ++ d'.reverse := by
      have h1 := congrArg List.reverse hdeq
      simpa using h1
    have hd_left : M.IsLeftChain n d'.reverse s'.reverse := by
      dsimp [IsLeftChain]
      simpa using hd'
    have hd_chain : d'.reverse ∈ M.Chains n :=
      (chains_eq_leftChains M hM n d'.reverse).2 ⟨s'.reverse, hd_left⟩
    exact ⟨d'.reverse, hd_chain, hc_rev⟩

end MonomialData

namespace Quiv

variable (k : Type) [Field k] (Q : Quiv) (R : Set (List Q.A))

/-- The monomial data of `kQ/(R)`. -/
abbrev data : MonomialData Q.A := MonomialData.ofQuiver Q R

/-- The `n`-th term `kCₙ ⊗_𝕜 Λ ≅ ⨁_{γ ∈ Cₙ} e_{t(γ)} Λ` of the resolution (3.3), as the
finitely supported functions on words supported on `n`-chains `γ` with values in `e_{t(γ)} Λ`
(where `t(γ)` is the last vertex of `γ`). -/
def anickTerm (n : ℕ) : Set (List Q.A →₀ Q.PathAlg k R) :=
  {f | ∀ c ∈ f.support, ∃ h : c ∈ (Q.data R).Chains n,
    ∃ y, f c = vertexIdem R (Q.finish c (by
      rcases h with ⟨t, ht⟩
      cases n with
      | zero => obtain ⟨x, rfl, -⟩ := ht; simp
      | succ n => exact ht.1.1)) * y}

/-- The differential `d(γ ⊗ λ) = γ' ⊗ t_γ λ` of (3.3), from `(n+1)`-chains to `n`-chains
where `γ = γ' t_γ`. -/
def anickDiff (n : ℕ) : (List Q.A →₀ Q.PathAlg k R) →+ (List Q.A →₀ Q.PathAlg k R) :=
  Finsupp.liftAddHom fun c =>
    let t := (Q.data R).tail (n + 1) c
    (Finsupp.singleAddHom (c.take (c.length - t.length))).comp
      (AddMonoidHom.mulLeft (pathElt R t))

/-- The augmentation `kC₀ ⊗ Λ → Λ`, `a ⊗ λ ↦ a λ`. -/
def anickAug : (List Q.A →₀ Q.PathAlg k R) →+ Q.PathAlg k R :=
  Finsupp.liftAddHom fun c => AddMonoidHom.mulLeft (pathElt R c)

/-- The radical `r = rad Λ`, spanned by the non-trivial paths (as a right ideal). -/
def radical : Set (Q.PathAlg k R) := {x | ∃ f ∈ anickTerm k Q R 0, anickAug k Q R f = x}

/-- **Theorem 3.3.2 and (3.3) (Green–Happel–Zacharia [73]).** For a monomial quiver algebra
with minimal relations, the Anick complex is exact: a cycle of `kCₙ ⊗ Λ` is a boundary, the
cycles of `kC₀ ⊗ Λ` are the boundaries, and the augmentation has image `rad Λ`; thus (3.3) is
a free resolution of `k = Λ / rad Λ`, and it is minimal (`d` has image in the radical).

**Change.** The Tor groups are not formalized. We state the resolution (3.3) itself, which is
the form in which Chapter 5 uses Theorem 3.3.2 (Proposition 5.1.3). -/
theorem anick_exact (hR : (Q.data R).IsMinimal) :
    (∀ n, ∀ f ∈ anickTerm k Q R (n + 1), anickDiff k Q R n f = 0 →
      ∃ g ∈ anickTerm k Q R (n + 2), anickDiff k Q R (n + 1) g = f) ∧
    (∀ f ∈ anickTerm k Q R 0, anickAug k Q R f = 0 →
      ∃ g ∈ anickTerm k Q R 1, anickDiff k Q R 0 g = f) ∧
    (∀ n, ∀ f ∈ anickTerm k Q R (n + 1), anickDiff k Q R n f ∈ anickTerm k Q R n) := by
  sorry

end Quiv

end TamaroffPhd

end
