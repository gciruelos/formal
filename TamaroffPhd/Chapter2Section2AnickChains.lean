import TamaroffPhd.Chapter2Section2Rewriting

/-!
# Chapter 2, §2.4–2.8 and §3.3.1: monomial relations, quivers and Anick chains

The combinatorics shared by Chapters 3, 5 and 6: words and paths, monomial relations, the
monomial (quiver) algebras they present, normal words, Anick chains with their tails and heads,
and decompositions of chains (§3.2.1).

## Contents

* `Quiv`: a finite quiver; paths are words in the arrows (§1.2 of Chapter 2).
* `MonomialData`: an alphabet with a set of monomial relations and a composability predicate
  (the one-vertex case takes every word to be a path).
* `MonomialData.IsChain`: Anick chains with tails, by induction on `n` (§3.3.1, Definition 25);
  the prechain description of §2.6.
* `MonomialData.IsLeftChain`: left Anick chains (heads), §3.3.1.
* `MonomialData.IsDecomposition`: decompositions of a chain (§3.2.1).
* `Quiv.PathAlg`: the path algebra modulo monomial relations, `Λ = kQ/(R)`.
* §2.8: attached bar terms, `uv = 0` minimally, and the critical bar terms of the Morse matching.

-/

noncomputable section

namespace TamaroffPhd

open Classical

/-! ## Quivers and monomial data -/

/-- A finite quiver `Q = (Q₀, Q₁, s, t)` (§2.1.2). Arrows `a` go from `src a` to `tgt a`. -/
structure Quiv where
  /-- Vertices `Q₀`. -/
  V : Type
  /-- Arrows `Q₁`. -/
  A : Type
  [finV : Fintype V]
  [finA : Fintype A]
  /-- Source of an arrow. -/
  src : A → V
  /-- Target of an arrow. -/
  tgt : A → V

attribute [instance] Quiv.finV Quiv.finA

namespace Quiv

variable (Q : Quiv)

/-- A word in the arrows is a (non-trivial) path when consecutive arrows compose.

**Change.** All paths are words read left to right, so that the word `p ++ q` is the
product `pq`. The thesis uses both conventions: Chapter 3 writes `t(aᵢ) = s(aᵢ₊₁)` for bar
terms, Chapter 5 writes `s(p) = t(q)` for a product `pq`. Here both become "`p ++ q` is a
path". Only composability depends on the convention; the combinatorics of chains does not. -/
def IsPath (p : List Q.A) : Prop := p ≠ [] ∧ p.IsChain fun a b => Q.tgt a = Q.src b

/-- First vertex of a non-trivial path (the source of its first arrow). -/
def start (p : List Q.A) (h : p ≠ []) : Q.V := Q.src (p.head h)

/-- Last vertex of a non-trivial path (the target of its last arrow). -/
def finish (p : List Q.A) (h : p ≠ []) : Q.V := Q.tgt (p.getLast h)

end Quiv

/-- An alphabet `A` with a set `W` of monomial relations and a predicate saying which words are
paths. For algebras (one-vertex quivers) every non-empty word is a path. -/
structure MonomialData (A : Type) where
  /-- The monomial relations. -/
  W : Set (List A)
  /-- Which words are paths. -/
  IsPath : List A → Prop

namespace MonomialData

variable {A : Type} (M : MonomialData A)

/-- The data of a one-vertex quiver: every non-empty word is a path. -/
def ofRelations (W : Set (List A)) : MonomialData A := ⟨W, fun p => p ≠ []⟩

/-- The data of a monomial quiver algebra `kQ/(R)`. -/
def ofQuiver (Q : Quiv) (R : Set (List Q.A)) : MonomialData Q.A := ⟨R, Q.IsPath⟩

/-- `v` is a divisor (subword) of `u`. -/
def Divides (v u : List A) : Prop := v <:+: u

/-- The relations are *minimal* (§6.4.2, §3.2.3): no relation has length `< 2`, and no relation
divides another one. -/
def IsMinimal : Prop :=
  (∀ w ∈ M.W, 2 ≤ w.length) ∧ ∀ w ∈ M.W, ∀ w' ∈ M.W, Divides w w' → w = w'

/-- A path is *normal* (nonzero in the monomial algebra) when no relation divides it (§2.8,
(5.3)). -/
def IsNormal (p : List A) : Prop := M.IsPath p ∧ ∀ w ∈ M.W, ¬ Divides w p

/-- The product `uv` of two normal words is zero (contains a relation), §2.8. -/
def ProdZero (u v : List A) : Prop := ∃ w ∈ M.W, Divides w (u ++ v)

/-- `uv = 0` *minimally* (§2.8): `uv` contains a relation, and `uv'` is normal for every proper
prefix `v'` of `v`. -/
def ProdZeroMinimally (u v : List A) : Prop :=
  M.ProdZero u v ∧ ∀ v', v' <+: v → v' ≠ v → ¬ M.ProdZero u v'

/-! ## Anick chains -/

/-- **Definition 25 (Anick chain), §3.3.1.** `IsChain n c t` says that `c` is an Anick
`n`-chain with tail `t`:

* a `0`-chain is a single letter (an arrow), which is its own tail;
* an `(n+1)`-chain is a path `c = c' t` with `c'` an `n`-chain of tail `t'` such that `t' t` has
  a right divisor in `W`, and no proper left divisor of `c` has these two properties. -/
def IsChain : ℕ → List A → List A → Prop
  | 0, c, t => ∃ x, c = [x] ∧ t = [x]
  | n + 1, c, t =>
      M.IsPath c ∧ t ≠ [] ∧
      (∃ c' t', IsChain n c' t' ∧ c = c' ++ t ∧ ∃ w ∈ M.W, w <:+ t' ++ t) ∧
      ∀ c₀, c₀ <+: c → c₀ ≠ c →
        ¬ ∃ c' t' t₀, IsChain n c' t' ∧ c₀ = c' ++ t₀ ∧ t₀ ≠ [] ∧ ∃ w ∈ M.W, w <:+ t' ++ t₀

/-- The set `Cₙ` of Anick `n`-chains. -/
def Chains (n : ℕ) : Set (List A) := {c | ∃ t, M.IsChain n c t}

/-- The tail `t_γ` of an `n`-chain (well defined by Anick's uniqueness lemma,
`PreliminariesAnickChains`). -/
def tail (n : ℕ) (c : List A) : List A :=
  if h : ∃ t, M.IsChain n c t then h.choose else []

/-- The data with every word reversed: left notions are right notions for the reversed data. -/
def reverse : MonomialData A := ⟨List.reverse '' M.W, fun p => M.IsPath p.reverse⟩

/-- **§3.3.1.** `IsLeftChain n c h`: `c` is a left Anick `n`-chain with head `h`, defined by
considering heads instead of tails. -/
def IsLeftChain (n : ℕ) (c h : List A) : Prop := M.reverse.IsChain n c.reverse h.reverse

/-- The head `h_γ` of a (left) `n`-chain. -/
def head (n : ℕ) (c : List A) : List A :=
  if h : ∃ hd, M.IsLeftChain n c hd then h.choose else []

/-- **§2.6 (prechain).** An `n`-prechain (`n ≥ 1`): a path `x₁ ⋯ x_t` with interlaced strictly
increasing sequences `a₁ = 1 < a₂ < ⋯`, `b₁ < ⋯ < bₙ = t`, `a_{i+1} ≤ b_i`, such that each
`x_{a_j} ⋯ x_{b_j}` is a relation. Indices are `0`-based and inclusive here. -/
def IsPrechain (n : ℕ) (c : List A) : Prop :=
  M.IsPath c ∧ 1 ≤ n ∧ ∃ a b : Fin n → ℕ,
    StrictMono a ∧ StrictMono b ∧ (∀ h : 0 < n, a ⟨0, h⟩ = 0 ∧ b ⟨n - 1, by omega⟩ + 1 = c.length) ∧
    (∀ i : Fin n, ∀ h : i.val + 1 < n, a ⟨i.val + 1, h⟩ ≤ b i) ∧
    ∀ j : Fin n, (c.drop (a j)).take (b j + 1 - a j) ∈ M.W

/-- **§2.6.** The `n`-chains in Anick's original sense: prechains such that the sequences can
be chosen with `x₁ ⋯ x_s` not an `m`-prechain for any `s < b_m`, `m ≤ n`. -/
def IsAnickChain (n : ℕ) (c : List A) : Prop :=
  M.IsPrechain n c ∧ ∃ b : Fin n → ℕ, (∀ i : Fin n, b i < c.length) ∧
    ∀ m : Fin n, ∀ s, s < b m + 1 → ¬ M.IsPrechain (m.val + 1) (c.take s)

/-- **§2.6 vs §3.3.1.** For `n ≥ 1`, the prechain description of `n`-chains agrees with the
inductive one of Definition 25 (Anick's `n`-chains are our `n`-chains). -/
theorem isAnickChain_iff (n : ℕ) (c : List A) :
    M.IsAnickChain (n + 1) c ↔ c ∈ M.Chains (n + 1) := by
  sorry

/-! ## Decompositions -/

/-- A chain together with its Anick degree. -/
abbrev Chain := {p : ℕ × List A // p.2 ∈ M.Chains p.1}

/-- The Anick degree of a chain. -/
def Chain.deg {M : MonomialData A} (γ : M.Chain) : ℕ := γ.val.1

/-- The underlying word of a chain. -/
def Chain.word {M : MonomialData A} (γ : M.Chain) : List A := γ.val.2

/-- **§3.2.1 (Decomposition).** A decomposition of an `r`-chain `γ` is a list
`(γ₁, …, γₙ)`, `n ≥ 2`, of chains whose concatenation is `γ` and with
`r₁ + ⋯ + rₙ = r - 1`. -/
def IsDecomposition (γ : M.Chain) (ds : List M.Chain) : Prop :=
  2 ≤ ds.length ∧ (ds.map Chain.word).flatten = γ.word ∧ (ds.map Chain.deg).sum + 1 = γ.deg

/-- The decompositions of a chain. -/
abbrev Decomposition (γ : M.Chain) := {ds : List M.Chain // M.IsDecomposition γ ds}

/-! ## Bar terms (§2.8) -/

/-- A bar term `[u₀ | ⋯ | u_r]` of the bar construction of the monomial algebra: a list of
non-empty normal words. -/
def IsBarTerm (us : List (List A)) : Prop := ∀ u ∈ us, u ≠ [] ∧ M.IsNormal u

/-- **§3.1.2.** A bar term is *attached* if `u_{i-1} u_i = 0` for all `i`. -/
def IsAttached (us : List (List A)) : Prop := us.IsChain fun u v => M.ProdZero u v

/-- **Lemma 2.3 (monomial case), §2.8.** The critical bar terms of the Morse matching: the
letters `[x]`, and the terms `[x | u₁ | ⋯ | u_r]` with `x` a letter and `u_j u_{j+1} = 0`
minimally for `j = 0, …, r - 1` (with `u₀ = x`). -/
def IsCriticalBarTerm (us : List (List A)) : Prop :=
  M.IsBarTerm us ∧ (∃ x u, us = [x] :: u) ∧ us.IsChain fun u v => M.ProdZeroMinimally u v

/-- **§2.8.** Critical bar terms with `r + 1` bars are exactly the `r`-chains with their bar
structure: `[x | u₁ | ⋯ | u_r]` is critical if and only if `x u₁ ⋯ u_r` is an `r`-chain, and then
the bar structure is determined by the chain. -/
theorem isCriticalBarTerm_iff (us : List (List A)) (r : ℕ) (hlen : us.length = r + 1)
    (hM : M.IsMinimal) :
    M.IsCriticalBarTerm us ↔ us.flatten ∈ M.Chains r ∧ ∀ v ∈ us, v ≠ [] := by
  sorry

end MonomialData

/-! ## Monomial path algebras -/

namespace Quiv

variable (k : Type) [Field k] (Q : Quiv)

/-- The relations presenting `kQ/(R)` as a quotient of the free algebra on vertices and arrows:
the `e_v` are orthogonal idempotents summing to `1`, `e_{s(a)} a = a = a e_{t(a)}`, and every
relation path is zero. -/
def pathRel (R : Set (List Q.A)) : FreeAlg k (Q.V ⊕ Q.A) → FreeAlg k (Q.V ⊕ Q.A) → Prop :=
  fun x y =>
    (∃ v w : Q.V, x = mono (FreeMonoid.of (.inl v)) * mono (FreeMonoid.of (.inl w)) ∧
      y = if v = w then mono (FreeMonoid.of (.inl v)) else 0) ∨
    (x = ∑ v : Q.V, mono (FreeMonoid.of (.inl v)) ∧ y = 1) ∨
    (∃ a : Q.A, x = mono (FreeMonoid.of (.inl (Q.src a))) * mono (FreeMonoid.of (.inr a)) ∧
      y = mono (FreeMonoid.of (.inr a))) ∨
    (∃ a : Q.A, x = mono (FreeMonoid.of (.inr a)) * mono (FreeMonoid.of (.inl (Q.tgt a))) ∧
      y = mono (FreeMonoid.of (.inr a))) ∨
    (∃ r ∈ R, x = mono (FreeMonoid.ofList (r.map Sum.inr)) ∧ y = 0)

/-- **§2.1.2, §3.2.3.** The monomial quiver algebra `Λ = kQ/(R)`. -/
abbrev PathAlg (R : Set (List Q.A)) := RingQuot (Q.pathRel k R)

variable {k Q}

/-- The image in `Λ` of a path (a word in the arrows). -/
def pathElt (R : Set (List Q.A)) (p : List Q.A) : Q.PathAlg k R :=
  RingQuot.mkAlgHom k (Q.pathRel k R) (mono (FreeMonoid.ofList (p.map Sum.inr)))

/-- The idempotent `e_v` of a vertex. -/
def vertexIdem (R : Set (List Q.A)) (v : Q.V) : Q.PathAlg k R :=
  RingQuot.mkAlgHom k (Q.pathRel k R) (mono (FreeMonoid.of (.inl v)))

/-- **(5.3).** The non-zero paths of `Λ` (the trivial paths `e_v` and the normal non-trivial
paths) form a basis of `Λ`; in particular a non-trivial path is zero in `Λ` iff a relation
divides it. -/
theorem pathElt_eq_zero_iff (R : Set (List Q.A)) (p : List Q.A) (hp : Q.IsPath p) :
    pathElt (k := k) R p = 0 ↔ ∃ w ∈ R, MonomialData.Divides w p := by
  sorry

end Quiv

end TamaroffPhd

end
