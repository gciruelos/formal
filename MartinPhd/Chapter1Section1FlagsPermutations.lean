import Mathlib

/-!
# Chapter 1, Section 1.1 (flags and permutations)

Contents:
* Chapter1Section1
-/

section Chapter1Section1

/-
Formalization outline of

  Fernando Daniel Martin, *Aspectos homológicos de la teoría de especies*,
  PhD thesis, Universidad de Buenos Aires, 2024 (advisor: M. Suárez-Álvarez).

# Chapter 1 — La cohomología de las GL-especies de banderas

This file is an **outline**: every definition, lemma, proposition, theorem and
corollary of Chapter 1 appears with its thesis number, statements are as
faithful as we could make them, and proofs are `sorry` except in §1.1
(`Chapter1Section1.lean`, which is fully proved, with no `sorry`).

## Conventions and modelling choices

* `F` is a finite field with `ℓ = Fintype.card F` elements; `k` is a field of
  characteristic zero. Everything lives in `Type` (universe 0).
* Thesis indices `⟦n⟧ = {1,…,n}` become `Fin n = {0,…,n-1}`; we say so where it
  changes a formula.
* A **flag** is stored as the finite *set* of its subspaces (a chain containing
  `⊥` and `⊤`). Then the reduction `red`, restriction `F|_S`, projection
  `F|_{V/S}` and push-forward along a linear iso are plain images, and
  repetitions disappear on their own. `F.nth i` recovers the thesis's `Fᵢ`.
* A **GL-species** is a functor `Core (FGModuleCat F) ⥤ ModuleCat k`. The thesis
  asks for finite-dimensional values (`Fin_k`); we drop that, as nothing below
  depends on it.
* **e-bicomodules** use the coordinate description (1.7) by restriction and
  projection maps, as the thesis does from §1.3 on. Their cohomology is
  *defined* through the reduced cobar complex (1.9)–(1.12), in coordinates
  (1.11). The thesis defines `H•(x) = Ext•(x, e)` and notes that this complex
  computes it; that comparison is `TODO` below.
* Mathlib has no spectral sequences. §1.7 defines the pages `E_r` of the filtered
  cobar complex by hand, with the usual `Z_r / B_r` formulas. We index by
  `(p, n)` with total degree `n = p + q`.
-/

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §1.1 Preliminares sobre banderas y permutaciones -/

section Compositions

/-- Refinement of compositions: `k ⪯ k'` iff the partial sums of `k` are among
those of `k'`. Mathlib's `Composition.boundaries` also contains `0`, which both
sides share, so the two definitions agree. -/
def Composition.Refines {n : ℕ} (c c' : Composition n) : Prop :=
  c.boundaries ⊆ c'.boundaries

/-- The `i`-th block of the standard ordered partition of `Fin n` of type `c`:
`{c₁ + ⋯ + c_{i-1}, …, c₁ + ⋯ + cᵢ - 1}` (0-indexed). -/
def stdBlock {n : ℕ} (c : Composition n) (i : Fin c.length) : Finset (Fin n) :=
  Finset.univ.filter fun j => c.sizeUpTo i ≤ j.val ∧ j.val < c.sizeUpTo (i.val + 1)

/-- Ordered partitions (compositions) of a finite set `X` of type `c`: a sequence
of pairwise disjoint subsets covering `X`, the `i`-th one of size `cᵢ`. -/
@[ext]
structure OrderedPartition (X : Type*) [Fintype X] {n : ℕ} (c : Composition n) where
  block : Fin c.length → Finset X
  disjoint : Pairwise fun i j => Disjoint (block i) (block j)
  cover : (Finset.univ.biUnion block) = Finset.univ
  card_block : ∀ i, (block i).card = c.blocksFun i

/-- The standard ordered partition `π^{0,c}` of `Fin n` of type `c`. -/
def stdPartition {n : ℕ} (c : Composition n) : OrderedPartition (Fin n) c where
  block := stdBlock c
  disjoint := by
    have key : ∀ i j : Fin c.length, i < j → Disjoint (stdBlock c i) (stdBlock c j) := by
      intro i j hij
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [stdBlock, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have := c.monotone_sizeUpTo (show i.val + 1 ≤ j.val from hij)
      omega
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  cover := by
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    exact ⟨c.index j, by
      simp only [stdBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c.sizeUpTo_index_le j, c.lt_sizeUpTo_index_succ j⟩⟩
  card_block := by
    intro i
    have h1 : (stdBlock c i).map Fin.valEmbedding =
        Finset.Ico (c.sizeUpTo i) (c.sizeUpTo (i.val + 1)) := by
      ext x
      simp only [stdBlock, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_Ico]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hx
        have : x < n := lt_of_lt_of_le hx.2 (c.sizeUpTo_le _)
        exact ⟨⟨x, this⟩, hx, rfl⟩
    have := congrArg Finset.card h1
    rw [Finset.card_map, Nat.card_Ico, c.sizeUpTo_succ' i] at this
    omega

/-- `S_n` acts on ordered partitions of `Fin n` by `σ · (A₁,…,A_l) = (σA₁,…,σA_l)`. -/
instance {n : ℕ} (c : Composition n) : MulAction (Equiv.Perm (Fin n)) (OrderedPartition (Fin n) c) where
  smul σ P :=
    { block := fun i => (P.block i).map σ.toEmbedding
      disjoint := fun i j hij => Finset.disjoint_map _ |>.2 (P.disjoint hij)
      cover := by
        refine Finset.eq_univ_iff_forall.2 fun x => ?_
        have hx := (Finset.ext_iff.1 P.cover (σ.symm x)).2 (Finset.mem_univ _)
        simp only [Finset.mem_biUnion] at hx ⊢
        obtain ⟨i, -, hi⟩ := hx
        exact ⟨i, Finset.mem_univ _, Finset.mem_map.2 ⟨σ.symm x, hi, by simp⟩⟩
      card_block := fun i => by rw [Finset.card_map]; exact P.card_block i }
  one_smul P := by
    ext i x
    simp [HSMul.hSMul, SMul.smul, Equiv.Perm.one_def]
  mul_smul σ τ P := by
    ext i x
    simp only [HSMul.hSMul, SMul.smul, Finset.mem_map_equiv, Equiv.Perm.mul_def,
      Equiv.symm_trans_apply]

/-- The Young subgroup `Y_c ≤ S_n`: the stabilizer of the standard ordered
partition of type `c`. -/
def youngSubgroup {n : ℕ} (c : Composition n) : Subgroup (Equiv.Perm (Fin n)) :=
  MulAction.stabilizer _ (stdPartition c)

theorem mem_stdBlock_iff {n : ℕ} (c : Composition n) (i : Fin c.length) (a : Fin n) :
    a ∈ stdBlock c i ↔ c.index a = i := by
  constructor
  · intro ha
    by_contra hne
    have hdis := (stdPartition c).disjoint (Ne.symm hne)
    have hmem : a ∈ stdBlock c (c.index a) := by
      simp only [stdBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c.sizeUpTo_index_le a, c.lt_sizeUpTo_index_succ a⟩
    exact (Finset.disjoint_left.1 hdis) ha hmem
  · rintro rfl
    simp only [stdBlock, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c.sizeUpTo_index_le a, c.lt_sizeUpTo_index_succ a⟩

theorem mem_youngSubgroup_iff {n : ℕ} (c : Composition n) (σ : Equiv.Perm (Fin n)) :
    σ ∈ youngSubgroup c ↔ ∀ a, c.index (σ a) = c.index a := by
  unfold youngSubgroup
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h a
    have h1 : σ a ∈ ((stdPartition c).block (c.index a)).map σ.toEmbedding :=
      Finset.mem_map.2 ⟨a, (mem_stdBlock_iff c _ a).2 rfl, rfl⟩
    have h2 : ((σ • stdPartition c).block (c.index a)) = (stdPartition c).block (c.index a) := by
      rw [h]
    have h3 : σ a ∈ (stdPartition c).block (c.index a) := by
      rw [← h2]; exact h1
    exact (mem_stdBlock_iff c _ _).1 h3
  · intro h
    ext i x
    show x ∈ ((stdPartition c).block i).map σ.toEmbedding ↔ x ∈ (stdPartition c).block i
    rw [Finset.mem_map_equiv]
    show σ.symm x ∈ stdBlock c i ↔ x ∈ stdBlock c i
    rw [mem_stdBlock_iff, mem_stdBlock_iff]
    have := h (σ.symm x)
    rw [Equiv.apply_symm_apply] at this
    rw [this]

/-- `Y_c ≅ S_{c₁} × ⋯ × S_{c_l}`. -/
theorem youngSubgroup_equiv {n : ℕ} (c : Composition n) :
    Nonempty (youngSubgroup c ≃* ((i : Fin c.length) → Equiv.Perm (Fin (c.blocksFun i)))) := by
  have hcard : ∀ i : Fin c.length, Fintype.card {a : Fin n // c.index a = i} = c.blocksFun i := by
    intro i
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun a : Fin n => c.index a = i) = stdBlock c i := by
      ext a; simp [mem_stdBlock_iff]
    rw [this]
    exact (stdPartition c).card_block i
  let E : (i : Fin c.length) → {a : Fin n // c.index a = i} ≃ Fin (c.blocksFun i) :=
    fun i => Fintype.equivFinOfCardEq (hcard i)
  let P : (i : Fin c.length) → Equiv.Perm {a : Fin n // c.index a = i} ≃*
      Equiv.Perm (Fin (c.blocksFun i)) := fun i =>
    { toFun := (E i).permCongr
      invFun := (E i).symm.permCongr
      left_inv := fun p => by ext x; simp [Equiv.permCongr_apply]
      right_inv := fun p => by ext x; simp [Equiv.permCongr_apply]
      map_mul' := fun p q => by ext x; simp [Equiv.permCongr_apply] }
  let Y : youngSubgroup c ≃* ((i : Fin c.length) → Equiv.Perm {a : Fin n // c.index a = i}) :=
    { toFun := fun σ i => Equiv.Perm.subtypePerm σ.1 fun a => by
        rw [(mem_youngSubgroup_iff c σ.1).1 σ.2 a]
      invFun := fun g => ⟨DomMulAct.stabilizerEquiv_invFun_aux g, by
        rw [mem_youngSubgroup_iff]
        intro a
        exact DomMulAct.comp_stabilizerEquiv_invFun g a⟩
      left_inv := fun σ => by
        apply Subtype.ext
        refine Equiv.ext fun a => ?_
        rfl
      right_inv := fun g => by
        refine funext fun i => Equiv.ext fun a => Subtype.ext ?_
        dsimp only
        exact DomMulAct.stabilizerEquiv_invFun_eq (f := c.index) g a.2
      map_mul' := fun σ τ => rfl }
  exact ⟨Y.trans (MulEquiv.piCongrRight P)⟩

end Compositions

section Flags

variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

/-- A flag in `V`: a strictly increasing chain `0 = F₀ < F₁ < ⋯ < F_n = V`,
stored as its finite set of members. -/
@[ext]
structure Flag where
  carrier : Finset (Submodule K V)
  isChain : IsChain (· ≤ ·) (carrier : Set (Submodule K V))
  bot_mem : ⊥ ∈ carrier
  top_mem : ⊤ ∈ carrier

variable {K V}

namespace Flag

/-- The length `len F` (number of strict steps). -/
def len (F : Flag K V) : ℕ := F.carrier.card - 1

/-- Refinement `F ⪯ G`: `F ⊆ G` as sequences of subspaces. -/
instance : LE (Flag K V) := ⟨fun F G => F.carrier ⊆ G.carrier⟩

/-- `G` refines `F` directly: `F ⪯ G` and `len G = len F + 1`. -/
def DirectlyRefines (F G : Flag K V) : Prop := F ≤ G ∧ G.len = F.len + 1

/-- Position of a member `A` of the chain: how many members lie strictly below. -/
def index (F : Flag K V) (A : Submodule K V) : ℕ := (F.carrier.filter (· < A)).card

/-- The `i`-th member `Fᵢ` of the flag (`F₀ = 0`, `F_{len F} = V`); junk value `⊤`
out of range. -/
def nth (F : Flag K V) (i : ℕ) : Submodule K V :=
  if h : ∃ A ∈ F.carrier, F.index A = i then h.choose else ⊤

/-- The trivial flag `(0, V)`; it has length `1` if `V ≠ 0` and `0` if `V = 0`. -/
def trivial : Flag K V where
  carrier := {⊥, ⊤}
  isChain := by
    simp only [Finset.coe_insert, Finset.coe_singleton]
    exact IsChain.pair le_top
  bot_mem := by simp
  top_mem := by simp

/-- The flag `(0, S, V)` for a subspace `S`. -/
def ofSubspace (S : Submodule K V) : Flag K V where
  carrier := {⊥, S, ⊤}
  isChain := by
    intro a ha b hb _
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;> simp
  bot_mem := by simp
  top_mem := by simp

/-- The reduction `red(G₀,…,G_n)` of an increasing sequence with `G₀ = 0`,
`G_n = V`: drop repetitions. -/
def red {n : ℕ} (G : Fin (n + 1) → Submodule K V) (hG : Monotone G)
    (h0 : G 0 = ⊥) (hn : G (Fin.last n) = ⊤) : Flag K V where
  carrier := Finset.univ.image G
  isChain := by
    intro a ha b hb _
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    rcases le_total i j with h | h
    · exact Or.inl (hG h)
    · exact Or.inr (hG h)
  bot_mem := Finset.mem_image.2 ⟨0, Finset.mem_univ _, h0⟩
  top_mem := Finset.mem_image.2 ⟨Fin.last n, Finset.mem_univ _, hn⟩

/-- `red` returns a flag of length `n` iff the sequence was already a flag. -/
theorem len_red {n : ℕ} (G : Fin (n + 1) → Submodule K V) (hG : Monotone G)
    (h0 : G 0 = ⊥) (hn : G (Fin.last n) = ⊤) :
    (red G hG h0 hn).len = n ↔ StrictMono G := by
  have hpos : 0 < (Finset.univ.image G).card :=
    Finset.card_pos.2 ⟨G 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hle : (Finset.univ.image G).card ≤ n + 1 := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin (n + 1)))) (f := G)
  unfold len red
  simp only
  rw [hG.strictMono_iff_injective]
  constructor
  · intro h
    have : (Finset.univ.image G).card = (Finset.univ : Finset (Fin (n + 1))).card := by
      simp only [Finset.card_univ, Fintype.card_fin]; omega
    exact fun a b hab => Finset.card_image_iff.1 this (Finset.mem_coe.2 (Finset.mem_univ a))
      (Finset.mem_coe.2 (Finset.mem_univ b)) hab
  · intro h
    rw [Finset.card_image_of_injective _ h]; simp

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Push-forward `φ_*` along a linear isomorphism. (The thesis defines `φ_*F` for any
linear `φ`, as a flag in `φ(V)`; only isomorphisms are used.) -/
def map (φ : V ≃ₗ[K] W) (F : Flag K V) : Flag K W where
  carrier := F.carrier.image (Submodule.map (φ : V →ₗ[K] W))
  isChain := by
    rw [Finset.coe_image]
    exact F.isChain.image_of_map_rel (· ≤ ·) (· ≤ ·) _ (fun x y h => Submodule.map_mono h)
  bot_mem := Finset.mem_image.2 ⟨⊥, F.bot_mem, Submodule.map_bot _⟩
  top_mem := Finset.mem_image.2 ⟨⊤, F.top_mem, by
    rw [Submodule.map_top]; exact LinearEquiv.range φ⟩

/-- Restriction `F|_S = i^*(F)` to a subspace `S ≤ V`. -/
def restrict (F : Flag K V) (S : Submodule K V) : Flag K S where
  carrier := F.carrier.image (Submodule.comap S.subtype)
  isChain := by
    rw [Finset.coe_image]
    exact F.isChain.image_of_map_rel (· ≤ ·) (· ≤ ·) _ (fun x y h => Submodule.comap_mono h)
  bot_mem := Finset.mem_image.2 ⟨⊥, F.bot_mem, by simp⟩
  top_mem := Finset.mem_image.2 ⟨⊤, F.top_mem, Submodule.comap_top _⟩

/-- Projection `F|_{V/S} = π_*(F)` to the quotient `V/S`. -/
def project (F : Flag K V) (S : Submodule K V) : Flag K (V ⧸ S) where
  carrier := F.carrier.image (Submodule.map S.mkQ)
  isChain := by
    rw [Finset.coe_image]
    exact F.isChain.image_of_map_rel (· ≤ ·) (· ≤ ·) _ (fun x y h => Submodule.map_mono h)
  bot_mem := Finset.mem_image.2 ⟨⊥, F.bot_mem, Submodule.map_bot _⟩
  top_mem := Finset.mem_image.2 ⟨⊤, F.top_mem, by
    rw [Submodule.map_top, Submodule.range_mkQ]⟩

/-- Erase an intermediate member: the middle faces `∂ᵢ`, `0 < i < len F`. -/
def erase (F : Flag K V) (A : Submodule K V) (hA : A ≠ ⊥ ∧ A ≠ ⊤) : Flag K V where
  carrier := F.carrier.erase A
  isChain := F.isChain.mono (by simp)
  bot_mem := Finset.mem_erase.2 ⟨hA.1.symm, F.bot_mem⟩
  top_mem := Finset.mem_erase.2 ⟨hA.2.symm, F.top_mem⟩

/-- Insert a subspace comparable with every member (used for refinements). -/
def insert (F : Flag K V) (A : Submodule K V)
    (hA : ∀ B ∈ F.carrier, A ≤ B ∨ B ≤ A) : Flag K V where
  carrier := Insert.insert A F.carrier
  isChain := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact (hA b hb)
    · exact (hA a ha).symm
    · exact F.isChain ha hb hab
  bot_mem := Finset.mem_insert_of_mem F.bot_mem
  top_mem := Finset.mem_insert_of_mem F.top_mem

theorem len_map (φ : V ≃ₗ[K] W) (F : Flag K V) : (F.map φ).len = F.len := by
  unfold len map
  simp only
  rw [Finset.card_image_of_injective]
  exact Submodule.map_injective_of_injective φ.injective

/-- `len (F|_S) ≤ len F`, and similarly for projections. -/
theorem len_restrict_le (F : Flag K V) (S : Submodule K V) : (F.restrict S).len ≤ F.len :=
  Nat.sub_le_sub_right Finset.card_image_le 1
theorem len_project_le (F : Flag K V) (S : Submodule K V) : (F.project S).len ≤ F.len :=
  Nat.sub_le_sub_right Finset.card_image_le 1

/-- The general linear group `GL(V)` acts on flags by push-forward. -/
instance : MulAction (V ≃ₗ[K] V) (Flag K V) where
  smul g F := F.map g
  one_smul F := by
    ext A
    show A ∈ (F.map 1).carrier ↔ _
    simp only [Flag.map, Finset.mem_image]
    constructor
    · rintro ⟨B, hB, rfl⟩
      convert hB
      ext x; simp
    · intro hA
      exact ⟨A, hA, by ext x; simp⟩
  mul_smul g h F := by
    ext A
    simp only [HSMul.hSMul, SMul.smul, Flag.map, Finset.mem_image]
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B.map (h : V →ₗ[K] V), ⟨B, hB, rfl⟩, by
        rw [← Submodule.map_comp]; rfl⟩
    · rintro ⟨_, ⟨B, hB, rfl⟩, rfl⟩
      exact ⟨B, hB, by rw [← Submodule.map_comp]; rfl⟩

/-- The type of a flag: the composition `(dim F₁/F₀, …, dim F_l/F_{l-1})`. -/
def typeList [FiniteDimensional K V] (F : Flag K V) : List ℕ :=
  (List.range F.len).map fun i => finrank K (F.nth (i + 1)) - finrank K (F.nth i)

/-- `F ∈ Fl_c(V)`: the flag has type `c`. -/
def IsOfType [FiniteDimensional K V] {n : ℕ} (F : Flag K V) (c : Composition n) : Prop :=
  F.typeList = c.blocks

/-- Complete flags `Fl⁺(V)`: maximal length, i.e. type `(1,…,1)`. -/
def IsComplete [FiniteDimensional K V] (F : Flag K V) : Prop := F.len = finrank K V

/-- An ordered basis `b` is adapted to `F` if every `Fᵢ` is spanned by an initial
segment of `b`. -/
def IsAdapted {ι : Type*} [LinearOrder ι] (b : Basis ι K V) (F : Flag K V) : Prop :=
  ∀ A ∈ F.carrier, A = ⊤ ∨ ∃ m : ι, A = Submodule.span K (b '' Set.Iio m)

theorem index_injOn (F : Flag K V) {A B : Submodule K V} (hA : A ∈ F.carrier)
    (hB : B ∈ F.carrier) (h : F.index A = F.index B) : A = B := by
  by_contra hne
  have key : ∀ {A B : Submodule K V}, A ∈ F.carrier → B ∈ F.carrier → A < B →
      F.index A < F.index B := by
    intro A B hA hB hlt
    apply Finset.card_lt_card
    refine ⟨fun x hx => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hlt⟩
    · have := hsub (Finset.mem_filter.2 ⟨hA, hlt⟩)
      simp at this
  rcases F.isChain hA hB hne with hle | hle
  · have := key hA hB (lt_of_le_of_ne hle hne); omega
  · have := key hB hA (lt_of_le_of_ne hle (Ne.symm hne)); omega

theorem nth_index (F : Flag K V) {A : Submodule K V} (hA : A ∈ F.carrier) :
    F.nth (F.index A) = A := by
  have h : ∃ B ∈ F.carrier, F.index B = F.index A := ⟨A, hA, rfl⟩
  unfold nth
  rw [dif_pos h]
  exact F.index_injOn h.choose_spec.1 hA h.choose_spec.2

theorem index_map (φ : V ≃ₗ[K] W) (F : Flag K V) {A : Submodule K V} (hA : A ∈ F.carrier) :
    (F.map φ).index (A.map (φ : V →ₗ[K] W)) = F.index A := by
  unfold index map
  simp only
  rw [← Finset.card_image_of_injective (F.carrier.filter (· < A))
    (Submodule.map_injective_of_injective (f := (φ : V →ₗ[K] W)) φ.injective)]
  congr 1
  ext B
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨C, hC, rfl⟩, hlt⟩
    exact ⟨C, ⟨hC, (Submodule.map_lt_map_iff_of_injective φ.injective).1 hlt⟩, rfl⟩
  · rintro ⟨C, ⟨hC, hlt⟩, rfl⟩
    exact ⟨⟨C, hC, rfl⟩, (Submodule.map_lt_map_iff_of_injective φ.injective).2 hlt⟩

theorem index_red {n : ℕ} (G : Fin (n + 1) → Submodule K V) (hG : Monotone G)
    (h0 : G 0 = ⊥) (hn : G (Fin.last n) = ⊤) (hs : StrictMono G) (i : Fin (n + 1)) :
    (red G hG h0 hn).index (G i) = i.val := by
  unfold index red
  simp only
  have : (Finset.univ.image G).filter (· < G i) = (Finset.Iio i).image G := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Iio]
    constructor
    · rintro ⟨⟨j, rfl⟩, hlt⟩
      exact ⟨j, hs.lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, hs hj⟩
  rw [this, Finset.card_image_of_injective _ hs.injective, Fin.card_Iio]

theorem nth_red {n : ℕ} (G : Fin (n + 1) → Submodule K V) (hG : Monotone G)
    (h0 : G 0 = ⊥) (hn : G (Fin.last n) = ⊤) (hs : StrictMono G) (i : Fin (n + 1)) :
    (red G hG h0 hn).nth i.val = G i := by
  have := nth_index (red G hG h0 hn) (A := G i)
    (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  rwa [index_red G hG h0 hn hs] at this

theorem nth_map (φ : V ≃ₗ[K] W) (F : Flag K V) (i : ℕ) :
    (F.map φ).nth i = (F.nth i).map (φ : V →ₗ[K] W) := by
  by_cases h : ∃ A ∈ F.carrier, F.index A = i
  · obtain ⟨A, hA, rfl⟩ := h
    rw [nth_index F hA, ← index_map φ F hA]
    exact nth_index (F.map φ) (Finset.mem_image_of_mem _ hA)
  · have h' : ¬ ∃ B ∈ (F.map φ).carrier, (F.map φ).index B = i := by
      rintro ⟨B, hB, hi⟩
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
      exact h ⟨A, hA, by rw [← index_map φ F hA]; exact hi⟩
    unfold nth
    rw [dif_neg h, dif_neg h']
    rw [Submodule.map_top]; exact (LinearEquiv.range φ).symm


theorem index_lt_index (F : Flag K V) {A B : Submodule K V} (hA : A ∈ F.carrier)
    (_hB : B ∈ F.carrier) (hlt : A < B) : F.index A < F.index B := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hlt⟩
  · have := hsub (Finset.mem_filter.2 ⟨hA, hlt⟩)
    simp at this

theorem index_lt_card (F : Flag K V) {A : Submodule K V} (hA : A ∈ F.carrier) :
    F.index A < F.carrier.card :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨A, hA, lt_irrefl A⟩)

theorem exists_index_eq (F : Flag K V) {i : ℕ} (hi : i < F.carrier.card) :
    ∃ A ∈ F.carrier, F.index A = i := by
  have hinj : Set.InjOn F.index (F.carrier : Set (Submodule K V)) :=
    fun A hA B hB h => F.index_injOn hA hB h
  have himg : F.carrier.image F.index = Finset.range F.carrier.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hj
      exact Finset.mem_range.2 (F.index_lt_card hA)
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have : i ∈ F.carrier.image F.index := by rw [himg]; exact Finset.mem_range.2 hi
  obtain ⟨A, hA, h⟩ := Finset.mem_image.1 this
  exact ⟨A, hA, h⟩

theorem nth_mem (F : Flag K V) {i : ℕ} (hi : i < F.carrier.card) :
    F.nth i ∈ F.carrier ∧ F.index (F.nth i) = i := by
  obtain ⟨A, hA, rfl⟩ := F.exists_index_eq hi
  rw [F.nth_index hA]
  exact ⟨hA, rfl⟩

theorem nth_lt_nth (F : Flag K V) {i j : ℕ} (hij : i < j) (hj : j < F.carrier.card) :
    F.nth i < F.nth j := by
  obtain ⟨hA, hAi⟩ := F.nth_mem (hij.trans hj)
  obtain ⟨hB, hBj⟩ := F.nth_mem hj
  by_contra hnot
  by_cases heq : F.nth i = F.nth j
  · rw [heq] at hAi; omega
  · rcases F.isChain hA hB heq with h | h
    · exact hnot (lt_of_le_of_ne h heq)
    · have := F.index_lt_index hB hA (lt_of_le_of_ne h (Ne.symm heq))
      omega

theorem carrier_card_pos (F : Flag K V) : 0 < F.carrier.card :=
  Finset.card_pos.2 ⟨_, F.bot_mem⟩

theorem card_eq_len_succ (F : Flag K V) : F.carrier.card = F.len + 1 := by
  have := F.carrier_card_pos
  unfold len; omega

theorem nth_zero (F : Flag K V) : F.nth 0 = ⊥ := by
  have h : F.index ⊥ = 0 := by
    unfold index
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun x _ => not_lt_bot
  rw [← h]; exact F.nth_index F.bot_mem

theorem nth_len (F : Flag K V) : F.nth F.len = ⊤ := by
  have h : F.index ⊤ = F.len := by
    unfold index len
    have : F.carrier.filter (· < ⊤) = F.carrier.erase ⊤ := by
      ext x; simp [lt_top_iff_ne_top, and_comm]
    rw [this, Finset.card_erase_of_mem F.top_mem]
  rw [← h]; exact F.nth_index F.top_mem

theorem carrier_eq_image_nth (F : Flag K V) :
    F.carrier = (Finset.range F.carrier.card).image F.nth := by
  ext A
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · intro hA
    exact ⟨F.index A, F.index_lt_card hA, F.nth_index hA⟩
  · rintro ⟨i, hi, rfl⟩
    exact (F.nth_mem hi).1

theorem typeList_length [FiniteDimensional K V] (F : Flag K V) : F.typeList.length = F.len := by
  simp [typeList]

theorem typeList_getElem? [FiniteDimensional K V] (F : Flag K V) (i : ℕ) :
    F.typeList[i]? = if i < F.len then
      some (finrank K (F.nth (i + 1)) - finrank K (F.nth i)) else none := by
  by_cases hi : i < F.len
  · unfold typeList
    rw [List.getElem?_map, List.getElem?_range hi]
    simp [hi]
  · simp [typeList, hi]

theorem finrank_nth_lt [FiniteDimensional K V] (F : Flag K V) {i : ℕ} (hi : i < F.len) :
    finrank K (F.nth i) < finrank K (F.nth (i + 1)) :=
  Submodule.finrank_lt_finrank_of_lt (F.nth_lt_nth (Nat.lt_succ_self i) (by
    rw [card_eq_len_succ]; omega))

theorem dims_eq_of_typeList_eq [FiniteDimensional K V] {F G : Flag K V}
    (h : F.typeList = G.typeList) :
    F.len = G.len ∧ ∀ i ≤ F.len, finrank K (F.nth i) = finrank K (G.nth i) := by
  have hlen : F.len = G.len := by
    rw [← typeList_length F, ← typeList_length G, h]
  refine ⟨hlen, fun i hi => ?_⟩
  induction i with
  | zero => rw [nth_zero, nth_zero]
  | succ i ih =>
    have hi' : i < F.len := hi
    have ih := ih hi'.le
    have h1 := congrArg (fun L => L[i]?) h
    simp only [typeList_getElem?, hi', hlen ▸ hi', ite_true, Option.some.injEq] at h1
    have h2 := F.finrank_nth_lt hi'
    have h3 := G.finrank_nth_lt (hlen ▸ hi')
    omega

end Flag

theorem flag_cons_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ} {W : Submodule K V}
    (v : V) (bW : Module.Basis (Fin n) K W) {hli hsp} (k : Fin (n + 1)) :
    (Module.Basis.mkFinCons v bW hli hsp).flag k.succ =
      Submodule.span K {v} ⊔ (bW.flag k).map W.subtype := by
  apply le_antisymm
  · rw [Module.Basis.flag_le_iff]
    intro i hi
    induction i using Fin.cases with
    | zero =>
      simp only [Module.Basis.coe_mkFinCons, Fin.cons_zero]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    | succ j =>
      simp only [Module.Basis.coe_mkFinCons, Fin.cons_succ, Function.comp_apply]
      exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := W.subtype)
        (Module.Basis.self_mem_flag (b := bW) (i := j) (k := k)
          (by simpa [Fin.lt_def] using hi)))
  · exact sup_le (Module.Basis.span_singleton_le_mkFinCons_flag_succ k)
      (Module.Basis.map_flag_le_mkFinCons_flag_succ k)

theorem exists_adapted_basis (K : Type*) [Field K] :
    ∀ (d : ℕ) (V : Type _) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = d → ∀ C : Finset (Submodule K V), IsChain (· ≤ ·) (C : Set (Submodule K V)) →
      ∃ b : Module.Basis (Fin d) K V, ∀ A ∈ C, ∃ k, b.flag k = A := by
  intro d
  induction d with
  | zero =>
    intro V _ _ _ hd C _
    haveI : Subsingleton V := Module.finrank_zero_iff.1 hd
    refine ⟨Module.Basis.empty V, fun A _ => ⟨0, ?_⟩⟩
    rw [Module.Basis.flag_zero]
    exact (Subsingleton.elim _ _)
  | succ d ih =>
    intro V _ _ _ hd C hC
    by_cases hex : ∃ A ∈ C, A ≠ ⊥
    · obtain ⟨A0, hA0C, hA0⟩ := hex
      obtain ⟨A1, hA1S, hmin'⟩ := Finset.exists_min_image (C.filter (· ≠ ⊥))
        (fun B => finrank K B) ⟨A0, Finset.mem_filter.2 ⟨hA0C, hA0⟩⟩
      obtain ⟨hA1C, hA1⟩ := Finset.mem_filter.1 hA1S
      have hle : ∀ A ∈ C, A ≠ ⊥ → A1 ≤ A := by
        intro A hA hAbot
        by_cases hAA : A = A1
        · exact hAA ▸ le_rfl
        · rcases hC hA1C hA (Ne.symm hAA) with h | h
          · exact h
          · exact (Submodule.eq_of_le_of_finrank_eq h
              (le_antisymm (Submodule.finrank_mono h)
                (hmin' A (Finset.mem_filter.2 ⟨hA, hAbot⟩)))).ge
      obtain ⟨v, hvA1, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA1
      obtain ⟨W, hW⟩ := Submodule.exists_isCompl (Submodule.span K {v})
      have hdim : finrank K W = d := by
        have := Submodule.finrank_add_eq_of_isCompl hW
        rw [finrank_span_singleton hv0] at this
        omega
      haveI : FiniteDimensional K W := inferInstance
      have hCW : IsChain (· ≤ ·) ((C.image (Submodule.comap W.subtype) : Finset (Submodule K W)) :
          Set (Submodule K W)) := by
        rw [Finset.coe_image]
        exact hC.image_of_map_rel (· ≤ ·) (· ≤ ·) _ (fun x y h => Submodule.comap_mono h)
      obtain ⟨bW, hbW⟩ := ih W hdim (C.image (Submodule.comap W.subtype)) hCW
      have hli : ∀ c : K, ∀ x ∈ W, c • v + x = 0 → c = 0 := by
        intro c x hx hcx
        have h1 : c • v ∈ Submodule.span K {v} := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
        have h2 : c • v ∈ W := by
          have : c • v = -x := eq_neg_of_add_eq_zero_left hcx
          rw [this]; exact W.neg_mem hx
        have h3 : c • v = 0 := by
          have := hW.disjoint.le_bot ⟨h1, h2⟩
          simpa using this
        rcases smul_eq_zero.1 h3 with h | h
        · exact h
        · exact absurd h hv0
      have hsp : ∀ z : V, ∃ c : K, z + c • v ∈ W := by
        intro z
        have : z ∈ Submodule.span K {v} ⊔ W := by rw [hW.sup_eq_top]; trivial
        obtain ⟨l, hl, w, hw, rfl⟩ := Submodule.mem_sup.1 this
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hl
        exact ⟨-c, by simpa using hw⟩
      refine ⟨Module.Basis.mkFinCons v bW hli hsp, fun A hA => ?_⟩
      by_cases hAbot : A = ⊥
      · exact ⟨0, by rw [Module.Basis.flag_zero, hAbot]⟩
      · have hvA : Submodule.span K {v} ≤ A :=
          Submodule.span_singleton_le_iff_mem _ _ |>.2 (hle A hA hAbot hvA1)
        obtain ⟨k, hk⟩ := hbW _ (Finset.mem_image_of_mem _ hA)
        refine ⟨k.succ, ?_⟩
        rw [flag_cons_eq, hk, Submodule.map_comap_subtype, ← sup_inf_assoc_of_le _ hvA]
        rw [hW.sup_eq_top, top_inf_eq]
    · push Not at hex
      obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (d + 1)) K V) :=
        ⟨Module.finBasisOfFinrankEq K V hd⟩
      exact ⟨b, fun A hA => ⟨0, by rw [Module.Basis.flag_zero, hex A hA]⟩⟩

theorem finrank_flag {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {d : ℕ}
    (b : Module.Basis (Fin d) K V) (k : Fin (d + 1)) : finrank K (b.flag k) = k.val := by
  unfold Module.Basis.flag
  have hli : LinearIndependent K (fun j : {i : Fin d // i.castSucc < k} => b j) :=
    b.linearIndependent.comp (Subtype.val : {i : Fin d // i.castSucc < k} → Fin d)
      Subtype.val_injective
  rw [show (b '' {i | i.castSucc < k}) = Set.range (fun j : {i : Fin d // i.castSucc < k} => b j) by
    ext x; simp]
  rw [finrank_span_eq_card hli, Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin d => i.castSucc < k) =
      Finset.univ.filter fun i : Fin d => i.val < k.val := by
    ext i; simp [Fin.lt_def]
  rw [this]
  simp [Fin.card_filter_val_lt, Nat.lt_succ_iff.1 k.2]

theorem Flag.exists_map_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (F G : Flag K V) (hlen : F.len = G.len)
    (hd : ∀ i ≤ F.len, finrank K (F.nth i) = finrank K (G.nth i)) :
    ∃ g : V ≃ₗ[K] V, g • F = G := by
  obtain ⟨bF, hbF⟩ := exists_adapted_basis K (finrank K V) V rfl F.carrier F.isChain
  obtain ⟨bG, hbG⟩ := exists_adapted_basis K (finrank K V) V rfl G.carrier G.isChain
  let e : V ≃ₗ[K] V := bF.equiv bG (Equiv.refl _)
  have hmapb : bF.map e = bG := by
    rw [show e = bF.equiv bG (Equiv.refl _) from rfl, Module.Basis.map_equiv]; ext i; simp
  have hnth : ∀ i ≤ F.len, (F.nth i).map (e : V →ₗ[K] V) = G.nth i := by
    intro i hi
    have hiF : i < F.carrier.card := by rw [Flag.card_eq_len_succ]; omega
    have hiG : i < G.carrier.card := by rw [Flag.card_eq_len_succ]; omega
    obtain ⟨k, hk⟩ := hbF _ (F.nth_mem hiF).1
    obtain ⟨k', hk'⟩ := hbG _ (G.nth_mem hiG).1
    have h1 : k.val = finrank K (F.nth i) := by rw [← hk, finrank_flag]
    have h2 : k'.val = finrank K (G.nth i) := by rw [← hk', finrank_flag]
    have hkk : k = k' := Fin.ext (by rw [h1, h2]; exact hd i hi)
    rw [← hk, ← hk', ← hkk, ← Module.Basis.flag_map, hmapb]
  refine ⟨e, Flag.ext ?_⟩
  show F.carrier.image (Submodule.map (e : V →ₗ[K] V)) = G.carrier
  have hcF := F.carrier_eq_image_nth
  have hcG := G.carrier_eq_image_nth
  rw [Flag.card_eq_len_succ] at hcF hcG
  rw [hcF, Finset.image_image, hcG, ← hlen]
  refine Finset.image_congr fun i hi => ?_
  exact hnth i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))


/-- The `GL(V)`-sets `Fl⁺(V)`, `Fl_l(V)` and `Fl_c(V)` are invariant, and `GL(V)`
acts transitively on `Fl_c(V)`. -/
theorem Flag.isOfType_smul [FiniteDimensional K V] {n : ℕ} (c : Composition n)
    (g : V ≃ₗ[K] V) (F : Flag K V) : (g • F).IsOfType c ↔ F.IsOfType c := by
  have h : (g • F).typeList = F.typeList := by
    show (F.map g).typeList = F.typeList
    unfold Flag.typeList
    rw [Flag.len_map]
    refine List.map_congr_left fun i _ => ?_
    rw [Flag.nth_map, Flag.nth_map, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]
  unfold Flag.IsOfType
  rw [h]

theorem Flag.transitive_ofType [FiniteDimensional K V] {n : ℕ} (c : Composition n)
    (F G : Flag K V) (hF : F.IsOfType c) (hG : G.IsOfType c) :
    ∃ g : V ≃ₗ[K] V, g • F = G := by
  have h : F.typeList = G.typeList := hF.trans hG.symm
  obtain ⟨hlen, hd⟩ := Flag.dims_eq_of_typeList_eq h
  exact Flag.exists_map_eq F G hlen hd

/-- An element stabilizing a flag fixes each of its members (it preserves dimensions
and the members form a chain). -/
theorem Flag.fix_of_smul_eq [FiniteDimensional K V] {G : Flag K V} {g : V ≃ₗ[K] V}
    (hg : g • G = G) {A : Submodule K V} (hA : A ∈ G.carrier) :
    A.map (g : V →ₗ[K] V) = A := by
  have hmem : A.map (g : V →ₗ[K] V) ∈ G.carrier := by
    have : A.map (g : V →ₗ[K] V) ∈ (g • G).carrier := Finset.mem_image_of_mem _ hA
    rwa [hg] at this
  have hfr : finrank K (A.map (g : V →ₗ[K] V)) = finrank K A := LinearEquiv.finrank_map_eq g A
  by_cases heq : A.map (g : V →ₗ[K] V) = A
  · exact heq
  · rcases G.isChain hmem hA heq with h | h
    · exact Submodule.eq_of_le_of_finrank_eq h hfr
    · exact (Submodule.eq_of_le_of_finrank_eq h hfr.symm).symm

theorem Flag.smul_eq_of_le [FiniteDimensional K V] {F G : Flag K V} {g : V ≃ₗ[K] V}
    (hFG : F ≤ G) (hg : g • G = G) : g • F = F := by
  have h2 : F.carrier.image (Submodule.map (g : V →ₗ[K] V)) = F.carrier :=
    (Finset.image_congr (g := id) (fun A hA => Flag.fix_of_smul_eq hg (hFG hA))).trans
      Finset.image_id
  ext B
  show B ∈ F.carrier.image (Submodule.map (g : V →ₗ[K] V)) ↔ B ∈ F.carrier
  rw [h2]

/-- If `A` is not a member of `G`, some element of `Stab G` moves `A`. -/
theorem Flag.exists_stab_moving [FiniteDimensional K V] (G : Flag K V) {A : Submodule K V}
    (hA : A ∉ G.carrier) : ∃ g : V ≃ₗ[K] V, g • G = G ∧ A.map (g : V →ₗ[K] V) ≠ A := by
  have hAbot : A ≠ ⊥ := fun h => hA (h ▸ G.bot_mem)
  -- the smallest member of `G` containing `A`
  obtain ⟨Gi, hGi, hmin'⟩ := Finset.exists_min_image (G.carrier.filter (A ≤ ·))
    (fun B => finrank K B) ⟨⊤, Finset.mem_filter.2 ⟨G.top_mem, le_top⟩⟩
  have hmin : ∀ x ∈ G.carrier.filter (A ≤ ·), ¬ x < Gi := fun x hx hlt =>
    absurd (hmin' x hx) (not_le.2 (Submodule.finrank_lt_finrank_of_lt hlt))
  obtain ⟨hGiG, hAGi⟩ := Finset.mem_filter.1 hGi
  have hAlt : A < Gi := lt_of_le_of_ne hAGi fun h => hA (h ▸ hGiG)
  have hGibot : ⊥ < Gi := lt_of_le_of_lt bot_le hAlt
  -- the largest member of `G` strictly below `Gi`
  obtain ⟨H, hH, hHmax'⟩ := Finset.exists_max_image (G.carrier.filter (· < Gi))
    (fun B => finrank K B) ⟨⊥, Finset.mem_filter.2 ⟨G.bot_mem, hGibot⟩⟩
  have hHmax : ∀ x ∈ G.carrier.filter (· < Gi), ¬ H < x := fun x hx hlt =>
    absurd (hHmax' x hx) (not_le.2 (Submodule.finrank_lt_finrank_of_lt hlt))
  obtain ⟨hHG, hHlt⟩ := Finset.mem_filter.1 hH
  have hAH : ¬ A ≤ H := fun h =>
    hmin H (Finset.mem_filter.2 ⟨hHG, h⟩) hHlt
  have hcomp : ∀ B ∈ G.carrier, B ≤ H ∨ Gi ≤ B := by
    intro B hB
    by_cases hBGi : B < Gi
    · left
      have hBP : B ∈ G.carrier.filter (· < Gi) := Finset.mem_filter.2 ⟨hB, hBGi⟩
      by_contra hBH
      rcases G.isChain hHG hB (fun h => hBH (h ▸ le_rfl)) with h | h
      · exact hHmax B hBP (lt_of_le_of_ne h fun e => hBH (e ▸ le_rfl))
      · exact hBH h
    · right
      rcases eq_or_ne B Gi with rfl | hne
      · exact le_rfl
      · rcases G.isChain hB hGiG hne with h | h
        · exact absurd (lt_of_le_of_ne h hne) hBGi
        · exact h
  -- a vector `w ∈ Gi \ A`, in `H` if possible
  have hGiA : ¬ Gi ≤ A := fun h => hAlt.ne (le_antisymm hAGi h)
  obtain ⟨w, hwGi, hwA, hwcase⟩ : ∃ w, w ∈ Gi ∧ w ∉ A ∧ ((¬ H ≤ A → w ∈ H)) := by
    by_cases hHA : H ≤ A
    · obtain ⟨w, hw, hwA⟩ := SetLike.not_le_iff_exists.1 hGiA
      exact ⟨w, hw, hwA, fun h => absurd hHA h⟩
    · obtain ⟨w, hw, hwA⟩ := SetLike.not_le_iff_exists.1 hHA
      exact ⟨w, hHlt.le hw, hwA, fun _ => hw⟩
  -- a vector `x ∈ A` outside `H ⊔ ⟨w⟩`
  obtain ⟨x, hxA, hxU⟩ : ∃ x ∈ A, x ∉ H ⊔ Submodule.span K {w} := by
    obtain ⟨x, hxA, hxH⟩ := SetLike.not_le_iff_exists.1 hAH
    refine ⟨x, hxA, fun hx => ?_⟩
    obtain ⟨h, hh, y, hy, hxy⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    by_cases hc : c = 0
    · subst hc
      simp at hxy
      exact hxH (hxy ▸ hh)
    · by_cases hHA : H ≤ A
      · apply hwA
        have : c • w ∈ A := by
          have : c • w = x - h := by rw [← hxy]; abel
          rw [this]; exact A.sub_mem hxA (hHA hh)
        simpa [hc] using A.smul_mem c⁻¹ this
      · have hwH := hwcase hHA
        exact hxH (hxy ▸ H.add_mem hh (H.smul_mem c hwH))
  obtain ⟨ℓ, hℓx, hℓU⟩ := Submodule.exists_le_ker_of_notMem hxU
  have hℓw : ℓ w = 0 := hℓU (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  have hℓH : ∀ y ∈ H, ℓ y = 0 := fun y hy => hℓU (Submodule.mem_sup_left hy)
  refine ⟨LinearEquiv.transvection (f := ℓ) (v := w) hℓw, ?_, ?_⟩
  · have hfix : ∀ B ∈ G.carrier,
        B.map (LinearEquiv.transvection (f := ℓ) (v := w) hℓw : V →ₗ[K] V) = B := by
      intro B hB
      have hle : B.map (LinearEquiv.transvection (f := ℓ) (v := w) hℓw : V →ₗ[K] V) ≤ B := by
        rintro _ ⟨y, hy, rfl⟩
        show LinearEquiv.transvection hℓw y ∈ B
        rw [LinearEquiv.transvection.apply]
        rcases hcomp B hB with h | h
        · rw [hℓH y (h hy)]; simpa using hy
        · exact B.add_mem hy (B.smul_mem _ (h hwGi))
      exact Submodule.eq_of_le_of_finrank_eq hle
        (LinearEquiv.finrank_map_eq (LinearEquiv.transvection hℓw) B)
    have h2 : G.carrier.image
        (Submodule.map (LinearEquiv.transvection (f := ℓ) (v := w) hℓw : V →ₗ[K] V)) =
        G.carrier := (Finset.image_congr (g := id) hfix).trans Finset.image_id
    ext B
    show B ∈ G.carrier.image
        (Submodule.map (LinearEquiv.transvection (f := ℓ) (v := w) hℓw : V →ₗ[K] V)) ↔
      B ∈ G.carrier
    rw [h2]
  · intro hmap
    have hmem : LinearEquiv.transvection hℓw x ∈ A := by
      rw [← hmap]; exact ⟨x, hxA, rfl⟩
    rw [LinearEquiv.transvection.apply] at hmem
    have : ℓ x • w ∈ A := by simpa using A.sub_mem hmem hxA
    apply hwA
    simpa [hℓx] using A.smul_mem (ℓ x)⁻¹ this

/-- **Lemma 1.1.** `Stab G ≤ Stab F ↔ F ⪯ G`; and `F = G` iff the stabilizers agree. -/
theorem Flag.stabilizer_le_iff [Finite K] [FiniteDimensional K V] (F G : Flag K V) :
    MulAction.stabilizer (V ≃ₗ[K] V) G ≤ MulAction.stabilizer (V ≃ₗ[K] V) F ↔ F ≤ G := by
  constructor
  · intro h A hA
    by_contra hAG
    obtain ⟨g, hgG, hgA⟩ := Flag.exists_stab_moving G hAG
    exact hgA (Flag.fix_of_smul_eq (h hgG) hA)
  · intro h g hg
    exact Flag.smul_eq_of_le h hg

theorem Flag.eq_iff_stabilizer_eq [Finite K] [FiniteDimensional K V] (F G : Flag K V) :
    F = G ↔ MulAction.stabilizer (V ≃ₗ[K] V) F = MulAction.stabilizer (V ≃ₗ[K] V) G := by
  constructor
  · rintro rfl; rfl
  · intro h
    exact Flag.ext (Finset.Subset.antisymm ((Flag.stabilizer_le_iff F G).1 h.ge)
      ((Flag.stabilizer_le_iff G F).1 h.le))

/-- `⟨e₁,…,eᵢ⟩ ≤ Kⁿ` (the first `i` standard basis vectors). -/
def stdSpan (K : Type*) [Field K] (n i : ℕ) : Submodule K (Fin n → K) :=
  Submodule.span K (Set.range fun j : {j : Fin n // j.val < i} => Pi.single (j : Fin n) (1 : K))

section StdSpan
variable (K : Type*) [Field K] (n : ℕ)

theorem stdSpan_mono {i i' : ℕ} (h : i ≤ i') : stdSpan K n i ≤ stdSpan K n i' := by
  apply Submodule.span_mono
  rintro _ ⟨⟨j, hj⟩, rfl⟩
  exact ⟨⟨j, lt_of_lt_of_le hj h⟩, rfl⟩

theorem stdSpan_zero : stdSpan K n 0 = ⊥ := by
  unfold stdSpan
  rw [Submodule.span_eq_bot]
  rintro _ ⟨⟨j, hj⟩, rfl⟩
  omega

theorem stdSpan_top : stdSpan K n n = ⊤ := by
  unfold stdSpan
  rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨⟨j, j.2⟩, by simp⟩

theorem finrank_stdSpan {i : ℕ} (hi : i ≤ n) : finrank K (stdSpan K n i) = i := by
  unfold stdSpan
  have hli : LinearIndependent K
      (fun j : {j : Fin n // j.val < i} => (Pi.single (j : Fin n) (1 : K) : Fin n → K)) := by
    have := (Pi.basisFun K (Fin n)).linearIndependent
    have h2 := this.comp (Subtype.val : {j : Fin n // j.val < i} → Fin n) Subtype.val_injective
    convert h2 using 2
    simp
  rw [finrank_span_eq_card hli, Fintype.card_subtype]
  simp [Fin.card_filter_val_lt, hi]

theorem stdSpan_inj {i i' : ℕ} (hi : i ≤ n) (hi' : i' ≤ n)
    (h : stdSpan K n i = stdSpan K n i') : i = i' := by
  rw [← finrank_stdSpan K n hi, ← finrank_stdSpan K n hi', h]

theorem stdSpan_lt_iff {i i' : ℕ} (hi : i ≤ n) (hi' : i' ≤ n) :
    stdSpan K n i < stdSpan K n i' ↔ i < i' := by
  constructor
  · intro h
    have := Submodule.finrank_lt_finrank_of_lt h
    rwa [finrank_stdSpan K n hi, finrank_stdSpan K n hi'] at this
  · intro h
    refine lt_of_le_of_ne (stdSpan_mono K n h.le) fun he => ?_
    exact h.ne (stdSpan_inj K n hi hi' he)

end StdSpan

/-- The standard complete flag `F⁰` in `Kⁿ`: `F⁰ᵢ = ⟨e₁,…,eᵢ⟩`. -/
def stdFlag (K : Type*) [Field K] (n : ℕ) : Flag K (Fin n → K) where
  carrier := (Finset.range (n + 1)).image (stdSpan K n)
  isChain := by
    intro a ha b hb _
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨i, -, rfl⟩ := ha
    obtain ⟨j, -, rfl⟩ := hb
    rcases le_total i j with h | h
    · exact Or.inl (stdSpan_mono K n h)
    · exact Or.inr (stdSpan_mono K n h)
  bot_mem := Finset.mem_image.2 ⟨0, by simp, stdSpan_zero K n⟩
  top_mem := Finset.mem_image.2 ⟨n, by simp, stdSpan_top K n⟩

/-- The standard flag `F^{0,c}` of type `c`: the unique flag of type `c` refined by
`F⁰`, namely the members of `F⁰` at the partial sums of `c`. -/
def stdFlagOfType (K : Type*) [Field K] {n : ℕ} (c : Composition n) : Flag K (Fin n → K) where
  carrier := c.boundaries.image fun i => stdSpan K n i.val
  isChain := by
    intro a ha b hb _
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨i, -, rfl⟩ := ha
    obtain ⟨j, -, rfl⟩ := hb
    rcases le_total i.val j.val with h | h
    · exact Or.inl (stdSpan_mono K n h)
    · exact Or.inr (stdSpan_mono K n h)
  bot_mem := Finset.mem_image.2 ⟨0, by
    simpa using c.toCompositionAsSet.zero_mem, by simpa using stdSpan_zero K n⟩
  top_mem := Finset.mem_image.2 ⟨Fin.last n, c.toCompositionAsSet.getLast_mem, by
    simpa using stdSpan_top K n⟩

theorem stdFlagOfType_eq_red (K : Type*) [Field K] {n : ℕ} (c : Composition n) :
    ∃ (hG : Monotone fun j : Fin (c.length + 1) => stdSpan K n (c.sizeUpTo j))
      (h0 : stdSpan K n (c.sizeUpTo (0 : Fin (c.length + 1))) = ⊥)
      (hn : stdSpan K n (c.sizeUpTo (Fin.last c.length : Fin (c.length + 1))) = ⊤),
      stdFlagOfType K c = Flag.red _ hG h0 hn := by
  have hG : Monotone fun j : Fin (c.length + 1) => stdSpan K n (c.sizeUpTo j) :=
    fun a b hab => stdSpan_mono K n (c.monotone_sizeUpTo hab)
  have h0 : stdSpan K n (c.sizeUpTo (0 : Fin (c.length + 1))) = ⊥ := by
    rw [Fin.val_zero, Composition.sizeUpTo_zero]; exact stdSpan_zero K n
  have hn : stdSpan K n (c.sizeUpTo (Fin.last c.length : Fin (c.length + 1))) = ⊤ := by
    rw [Fin.val_last, Composition.sizeUpTo_length]; exact stdSpan_top K n
  refine ⟨hG, h0, hn, Flag.ext ?_⟩
  show c.boundaries.image (fun i => stdSpan K n i.val) = Finset.univ.image _
  unfold Composition.boundaries
  rw [Finset.map_eq_image, Finset.image_image]
  rfl

theorem stdFlagOfType_isOfType (K : Type*) [Field K] {n : ℕ} (c : Composition n) :
    (stdFlagOfType K c).IsOfType c := by
  obtain ⟨hG, h0, hn, heq⟩ := stdFlagOfType_eq_red K c
  have hs : StrictMono fun j : Fin (c.length + 1) => stdSpan K n (c.sizeUpTo j) := by
    intro a b hab
    rw [stdSpan_lt_iff K n (c.sizeUpTo_le _) (c.sizeUpTo_le _)]
    have hb : (b : ℕ) ≤ c.length := Nat.lt_succ_iff.1 b.2
    rcases Nat.lt_or_ge (a : ℕ) c.length with ha | ha
    · exact c.sizeUpTo_strict_mono ha |>.trans_le (c.monotone_sizeUpTo (show (a:ℕ) + 1 ≤ b from hab))
    · exact absurd hab (by intro h; have : (a : ℕ) < b := h; omega)
  have hlen : (stdFlagOfType K c).len = c.length := by
    rw [heq]; exact (Flag.len_red _ hG h0 hn).2 hs
  have hnth : ∀ i : Fin (c.length + 1), (stdFlagOfType K c).nth i.val = stdSpan K n (c.sizeUpTo i) := by
    intro i; rw [heq]; exact Flag.nth_red _ hG h0 hn hs i
  unfold Flag.IsOfType Flag.typeList
  rw [hlen]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < c.length := by simpa using h1
    rw [List.getElem_map, List.getElem_range]
    rw [hnth ⟨i + 1, by omega⟩, hnth ⟨i, by omega⟩, finrank_stdSpan K n (c.sizeUpTo_le _),
      finrank_stdSpan K n (c.sizeUpTo_le _)]
    simp only
    rw [c.sizeUpTo_succ hi]
    simp

theorem stdFlagOfType_le_stdFlag (K : Type*) [Field K] {n : ℕ} (c : Composition n) :
    stdFlagOfType K c ≤ stdFlag K n := by
  intro A hA
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
  exact Finset.mem_image.2 ⟨i.val, Finset.mem_range.2 i.2, rfl⟩

/-- `F^{0,c} ⪯ F^{0,c'}` iff `c ⪯ c'`. -/
theorem stdFlagOfType_le_iff (K : Type*) [Field K] {n : ℕ} (c c' : Composition n) :
    stdFlagOfType K c ≤ stdFlagOfType K c' ↔ Composition.Refines c c' := by
  constructor
  · intro h i hi
    obtain ⟨i', hi', he⟩ := Finset.mem_image.1 (h (Finset.mem_image.2 ⟨i, hi, rfl⟩))
    have := stdSpan_inj K n (Nat.lt_succ_iff.1 i'.2) (Nat.lt_succ_iff.1 i.2) he
    rwa [show i' = i from Fin.ext this] at hi'
  · intro h A hA
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hA
    exact Finset.mem_image.2 ⟨i, h hi, rfl⟩

/-- Over a finite field a finite-dimensional space has finitely many subspaces. -/
instance Submodule.finite_of_finite [Finite K] [FiniteDimensional K V] :
    Finite (Submodule K V) := by
  haveI : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (SetLike.coe : Submodule K V → Set V) SetLike.coe_injective

instance Flag.finite [Finite K] [FiniteDimensional K V] : Finite (Flag K V) :=
  Finite.of_injective (Flag.carrier : Flag K V → Finset (Submodule K V))
    fun F G h => Flag.ext h

instance [Finite K] [FiniteDimensional K V] : Fintype (Submodule K V) := Fintype.ofFinite _
instance [Finite K] [FiniteDimensional K V] : Fintype (Flag K V) := Fintype.ofFinite _

end Flags

section Shuffles

/-- The number of inversions `inv(σ) = #{(i,j) : i < j, σ i > σ j}`. -/
def inv {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card

theorem shuffle_aux {n : ℕ} (X : Finset (Fin n)) {i : Fin n} (h : ¬ i.val < X.card) :
    i.val - X.card < Xᶜ.card := by
  rw [Finset.card_compl, Fintype.card_fin]
  have := i.2
  omega

/-- The shuffle `sh(X)` of `X ⊆ Fin n` with `#X = k`: the unique permutation with
`σ(Fin k) = X` that is increasing on `Fin k` and on its complement. -/
def shuffleFun {n : ℕ} (X : Finset (Fin n)) (i : Fin n) : Fin n :=
  if h : i.val < X.card then X.orderEmbOfFin rfl ⟨i.val, h⟩
  else Xᶜ.orderEmbOfFin rfl ⟨i.val - X.card, shuffle_aux X h⟩

theorem shuffleFun_injective {n : ℕ} (X : Finset (Fin n)) : Function.Injective (shuffleFun X) := by
  intro i j hij
  unfold shuffleFun at hij
  by_cases hi : i.val < X.card <;> by_cases hj : j.val < X.card
  · rw [dif_pos hi, dif_pos hj] at hij
    have := (X.orderEmbOfFin rfl).injective hij
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · rw [dif_pos hi, dif_neg hj] at hij
    exfalso
    have h1 := X.orderEmbOfFin_mem rfl ⟨i.val, hi⟩
    have h2 := Xᶜ.orderEmbOfFin_mem rfl ⟨j.val - X.card, shuffle_aux X hj⟩
    rw [hij] at h1
    exact (Finset.mem_compl.1 h2) h1
  · rw [dif_neg hi, dif_pos hj] at hij
    exfalso
    have h1 := Xᶜ.orderEmbOfFin_mem rfl ⟨i.val - X.card, shuffle_aux X hi⟩
    have h2 := X.orderEmbOfFin_mem rfl ⟨j.val, hj⟩
    rw [hij] at h1
    exact (Finset.mem_compl.1 h1) h2
  · rw [dif_neg hi, dif_neg hj] at hij
    have := (Xᶜ.orderEmbOfFin rfl).injective hij
    have h3 := congrArg Fin.val this
    simp only at h3
    exact Fin.ext (by omega)

def shuffle {n : ℕ} (X : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (shuffleFun X) (Finite.injective_iff_bijective.1 (shuffleFun_injective X))

theorem shuffle_apply_of_lt {n : ℕ} (X : Finset (Fin n)) {i : Fin n} (h : i.val < X.card) :
    shuffle X i = X.orderEmbOfFin rfl ⟨i.val, h⟩ := by
  show shuffleFun X i = _
  unfold shuffleFun; rw [dif_pos h]

theorem shuffle_apply_of_ge {n : ℕ} (X : Finset (Fin n)) {i : Fin n} (h : ¬ i.val < X.card) :
    shuffle X i = Xᶜ.orderEmbOfFin rfl ⟨i.val - X.card, shuffle_aux X h⟩ := by
  show shuffleFun X i = _
  unfold shuffleFun; rw [dif_neg h]

theorem shuffle_mem_iff {n : ℕ} (X : Finset (Fin n)) (i : Fin n) :
    shuffle X i ∈ X ↔ i.val < X.card := by
  by_cases h : i.val < X.card
  · rw [shuffle_apply_of_lt X h]; simp [h, X.orderEmbOfFin_mem]
  · rw [shuffle_apply_of_ge X h]
    have := Xᶜ.orderEmbOfFin_mem rfl ⟨i.val - X.card, shuffle_aux X h⟩
    simp only [h, iff_false]
    exact Finset.mem_compl.1 this

/-- `sh(X)` is characterized by `σ(Fin k) = X` and monotonicity on both pieces. -/
theorem shuffle_unique {n : ℕ} (X : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (h₁ : ∀ i : Fin n, i.val < X.card → σ i ∈ X)
    (h₂ : ∀ i j : Fin n, i < j → (i.val < X.card ↔ j.val < X.card) → σ i < σ j) :
    σ = shuffle X := by
  have hk : X.card ≤ n := by simpa using Finset.card_le_univ X
  -- σ maps the first block onto X
  have hout : ∀ i : Fin n, ¬ i.val < X.card → σ i ∉ X := by
    intro i hi hmem
    let T : Finset (Fin n) := Finset.univ.filter fun j => j.val < X.card
    have hT : T.card = X.card := by simp [T, Fin.card_filter_val_lt, hk]
    have himg : T.image σ = X := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
        exact h₁ j (by simpa [T] using hj)
      · rw [Finset.card_image_of_injective _ σ.injective, hT]
    rw [← himg] at hmem
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 hmem
    have := σ.injective hji
    subst this
    exact hi (by simpa [T] using hj)
  refine Equiv.ext fun i => ?_
  by_cases h : i.val < X.card
  · rw [shuffle_apply_of_lt X h]
    have := Finset.orderEmbOfFin_unique (s := X) (k := X.card) rfl
      (f := fun r : Fin X.card => σ ⟨r.val, lt_of_lt_of_le r.2 hk⟩)
      (fun r => h₁ _ r.2) (by
        intro a b hab
        exact h₂ _ _ (by simpa using hab) (by simp [a.2, b.2]))
    exact congrFun this ⟨i.val, h⟩
  · rw [shuffle_apply_of_ge X h]
    have hc : Xᶜ.card = n - X.card := by rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.orderEmbOfFin_unique (s := Xᶜ) (k := Xᶜ.card) rfl
      (f := fun r : Fin Xᶜ.card => σ ⟨r.val + X.card, by have := r.2; omega⟩)
      (fun r => Finset.mem_compl.2 (hout _ (by simp only; omega))) (by
        intro a b hab
        refine h₂ _ _ (by simpa using hab) ?_
        simp)
    have h3 := congrFun this ⟨i.val - X.card, shuffle_aux X h⟩
    simp only at h3
    have : (⟨i.val - X.card + X.card, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
    rw [this] at h3
    exact h3

theorem shuffle_lt {n : ℕ} (X : Finset (Fin n)) {i j : Fin n} (hij : i < j)
    (h : i.val < X.card ↔ j.val < X.card) : shuffle X i < shuffle X j := by
  by_cases hi : i.val < X.card
  · have hj := h.1 hi
    rw [shuffle_apply_of_lt X hi, shuffle_apply_of_lt X hj]
    exact (X.orderEmbOfFin rfl).strictMono (by simpa using hij)
  · have hj : ¬ j.val < X.card := fun hj => hi (h.2 hj)
    rw [shuffle_apply_of_ge X hi, shuffle_apply_of_ge X hj]
    refine (Xᶜ.orderEmbOfFin rfl).strictMono ?_
    have : i.val < j.val := hij
    show i.val - X.card < j.val - X.card
    omega

theorem inv_shuffle_eq {n : ℕ} (X : Finset (Fin n)) :
    inv (shuffle X) = ∑ u ∈ X, (Xᶜ.filter (· < u)).card := by
  have hk : X.card ≤ n := by simpa using Finset.card_le_univ X
  set σ := shuffle X with hσ
  have key : inv σ = ((X ×ˢ Xᶜ).filter fun p : Fin n × Fin n => p.2 < p.1).card := by
    unfold inv
    refine Finset.card_bij (fun p _ => (σ p.1, σ p.2)) ?_ ?_ ?_
    · rintro ⟨i, j⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hij, hlt⟩ := hp
      have hside : i.val < X.card ∧ ¬ j.val < X.card := by
        by_contra hnot
        have hiff : i.val < X.card ↔ j.val < X.card := by
          have : i.val < j.val := hij
          by_cases hi : i.val < X.card <;> by_cases hj : j.val < X.card <;> simp_all <;> omega
        exact absurd (shuffle_lt X hij hiff) (not_lt.2 hlt.le)
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl]
      exact ⟨⟨(shuffle_mem_iff X i).2 hside.1, fun h => hside.2 ((shuffle_mem_iff X j).1 h)⟩, hlt⟩
    · rintro ⟨i, j⟩ - ⟨i', j'⟩ - h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (σ.injective h.1) (σ.injective h.2)
    · rintro ⟨u, v⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl] at hp
      obtain ⟨⟨hu, hv⟩, hlt⟩ := hp
      have h1 : (σ.symm u).val < X.card := by
        rw [← shuffle_mem_iff X]; simpa [hσ] using hu
      have h2 : ¬ (σ.symm v).val < X.card := by
        rw [← shuffle_mem_iff X]; simpa [hσ] using hv
      refine ⟨(σ.symm u, σ.symm v), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
      exact ⟨by show (σ.symm u).val < (σ.symm v).val; omega, hlt⟩
  rw [key, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.card_filter]

theorem sum_filter_lt_self {n : ℕ} (X : Finset (Fin n)) :
    ∑ u ∈ X, (X.filter (· < u)).card = X.card.choose 2 := by
  have h1 : ∑ u ∈ X, (X.filter (· < u)).card = ∑ u ∈ X, ∑ v ∈ X, if v < u then 1 else 0 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.card_filter]
  have h2 : ∑ u ∈ X, ∑ v ∈ X, (if v < u then 1 else 0) = ∑ u ∈ X, ∑ v ∈ X, (if u < v then 1 else 0) := by
    rw [Finset.sum_comm]
  have h3 : ∑ u ∈ X, ∑ v ∈ X, ((if v < u then 1 else 0) + (if u < v then 1 else 0) + (if u = v then 1 else 0)) = X.card * X.card := by
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => (show ((if v < u then 1 else 0) + (if u < v then 1 else 0) + (if u = v then 1 else 0) : ℕ) = 1 by
      rcases lt_trichotomy u v with h | h | h
      · simp [h, h.not_gt, h.ne]
      · simp [h]
      · simp [h, h.not_gt, h.ne']), ]
    simp [Finset.sum_const, mul_comm]
  have h4 : ∑ u ∈ X, ∑ v ∈ X, (if u = v then 1 else 0 : ℕ) = X.card := by
    simp
  simp only [Finset.sum_add_distrib] at h3
  rw [h1]
  have hA : 2 * (∑ u ∈ X, ∑ v ∈ X, (if v < u then 1 else 0 : ℕ)) + X.card = X.card * X.card := by
    rw [← h3, h4, ← h2]; ring
  rw [Nat.choose_two_right]
  have : X.card * (X.card - 1) = X.card * X.card - X.card := Nat.mul_sub_one _ _
  omega

/-- **Lemma 1.2.** `inv(sh X) = ∑_{x ∈ X} x − C(k+1, 2)`, with `x` counted from `1`
(hence the `+ 1` in 0-indexed `Fin n`). In particular it does not depend on `n`.
(Checked against the thesis example: `X = {3,5,6} ⊆ ⟦7⟧` gives `14 − 6 = 8`.) -/
theorem inv_shuffle {n : ℕ} (X : Finset (Fin n)) :
    inv (shuffle X) + (X.card + 1).choose 2 = ∑ x ∈ X, (x.val + 1) := by
  rw [inv_shuffle_eq]
  have hsplit : ∀ u ∈ X, (Xᶜ.filter (· < u)).card + (X.filter (· < u)).card = u.val := by
    intro u _
    have := Finset.card_filter_add_card_filter_not (s := Finset.Iio u) (fun v => v ∈ X)
    have e1 : (Finset.Iio u).filter (fun v => v ∈ X) = X.filter (· < u) := by
      ext v; simp [and_comm]
    have e2 : (Finset.Iio u).filter (fun v => ¬ v ∈ X) = Xᶜ.filter (· < u) := by
      ext v; simp [and_comm]
    rw [e1, e2, Fin.card_Iio] at this
    omega
  have hs : ∑ u ∈ X, (Xᶜ.filter (· < u)).card + ∑ u ∈ X, (X.filter (· < u)).card = ∑ u ∈ X, u.val := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl hsplit
  rw [sum_filter_lt_self] at hs
  have hc : (X.card + 1).choose 2 = X.card.choose 2 + X.card := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring
  rw [Finset.sum_add_distrib, hc]
  simp
  omega

end Shuffles


/-! ## Generic helper: subquotients -/

/-- The subquotient `A / (A ⊓ B)` of a module; used for every (co)homology group and
spectral-sequence page below. -/
abbrev Subquot {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (A B : Submodule R M) :=
  A ⧸ B.comap A.subtype

/-- The class in `Subquot A B` of an element of `A`. -/
def Subquot.mk {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {A B : Submodule R M}
    (a : M) (ha : a ∈ A) : Subquot A B :=
  Submodule.Quotient.mk ⟨a, ha⟩

/-- A linear map induces a map of subquotients. -/
def Subquot.map {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] {A B : Submodule R M} {A' B' : Submodule R N} (f : M →ₗ[R] N)
    (hA : A ≤ A'.comap f) (hB : B ⊓ A ≤ B'.comap f) : Subquot A B →ₗ[R] Subquot A' B' :=
  Submodule.mapQ _ _ (f.restrict hA) (by
    intro a ha
    exact hB ⟨ha, a.2⟩)

end MartinPhd

end
end Chapter1Section1
