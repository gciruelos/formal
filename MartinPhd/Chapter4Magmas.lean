import Mathlib
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient

/-!
# Chapter 4 (2-step nilpotent magmas: trees, the complex, the Laplacian, Trees)

Contents:
* Trees
* Complex
* Laplacian
* TreesCat
* LieComplex
-/

section Trees

/-
Outline of

  Fernando Daniel Martin, *Aspectos homológicos de la teoría de especies*,
  PhD thesis, Universidad de Buenos Aires, 2024 (advisor: M. Suárez-Álvarez).

# Chapter 4 — Álgebras nilpotentes en 2 pasos (§4.1–4.2: magmas and trees)

Outline pass: definitions and statements with the thesis numbering; proofs are `sorry`.

## Modelling choices

* Operads are not in Mathlib. The operads `OM`, `OL` of 2-step nilpotent magmas and Lie algebras
  appear only through their algebras (`Mag2`, `Lie2`) and through the complexes the thesis
  extracts from their Koszul duals (`T•`, `C•`, in later files).
* The free monoid `⟨λ, ρ⟩` is `List Bool` (`false = λ`, `true = ρ`). A word `λw` is
  `false :: w`; "closed under suffixes" is `w₁ ++ w₂ ∈ τ → w₂ ∈ τ`.
-/

open scoped TensorProduct BigOperators

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §4.1 Magmas and Lie algebras nilpotent in 2 steps -/

section Magmas

variable (k : Type) [Field k]

/-- A **magma nilpotent in 2 steps**: a vector space with a bilinear `μ` such that
`μ(μ(x,y),z) = μ(x,μ(y,z)) = 0` (4.3). -/
structure Mag2 where
  A : Type
  [addCommGroup : AddCommGroup A]
  [module : Module k A]
  μ : A →ₗ[k] A →ₗ[k] A
  μ_left : ∀ x y z, μ (μ x y) z = 0
  μ_right : ∀ x y z, μ x (μ y z) = 0

attribute [instance] Mag2.addCommGroup Mag2.module

/-- A **Lie algebra nilpotent in 2 steps**: a `Mag2` whose operation is antisymmetric
(the Jacobi identity then holds automatically). -/
structure Lie2 extends Mag2 k where
  antisymm : ∀ x y, μ x y = - μ y x

end Magmas

/-! ## §4.2 Trees -/

/-- Words in the free monoid `⟨λ, ρ⟩`: `false = λ`, `true = ρ`. -/
abbrev Word := List Bool

/-- A **tree**: a nonempty finite subset of `⟨λ, ρ⟩` closed under suffixes and *full*
(`λw ∈ τ ↔ ρw ∈ τ`). The root is the empty word. -/
structure Tree where
  carrier : Finset Word
  nonempty : carrier.Nonempty
  suffix_closed : ∀ w₁ w₂ : Word, w₁ ++ w₂ ∈ carrier → w₂ ∈ carrier
  full : ∀ w : Word, (false :: w) ∈ carrier ↔ (true :: w) ∈ carrier

namespace Tree

@[ext] theorem ext' {τ σ : Tree} (h : τ.carrier = σ.carrier) : τ = σ := by
  cases τ; cases σ; simp_all

lemma nil_mem (τ : Tree) : [] ∈ τ.carrier := by
  obtain ⟨w, hw⟩ := τ.nonempty
  exact τ.suffix_closed w [] (by simpa using hw)

/-- A vertex is a **leaf** if it has no children. -/
def IsLeaf (τ : Tree) (v : Word) : Prop := v ∈ τ.carrier ∧ (false :: v) ∉ τ.carrier

/-- The leaves of a tree. -/
def leaves (τ : Tree) : Finset Word := τ.carrier.filter fun v => (false :: v) ∉ τ.carrier

/-- The **arity** `|τ|`: the number of leaves. -/
def arity (τ : Tree) : ℕ := τ.leaves.card

/-- The trivial tree `{ε}`. -/
def triv : Tree where
  carrier := {[]}
  nonempty := ⟨[], by simp⟩
  suffix_closed := by
    intro w₁ w₂ h
    simp only [Finset.mem_singleton, List.append_eq_nil_iff] at h ⊢
    exact h.2
  full := by simp

/-- The unique tree `V = {ε, λ, ρ}` of arity 2. -/
def V : Tree where
  carrier := {[], [false], [true]}
  nonempty := ⟨[], by simp⟩
  suffix_closed := by
    intro w₁ w₂ h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h
    · simp only [List.append_eq_nil_iff] at h; left; exact h.2
    · cases w₁ with
      | nil => simp only [List.nil_append] at h; right; left; exact h
      | cons x xs =>
        cases xs with
        | nil =>
          cases w₂ with
          | nil => left; rfl
          | cons y ys => simp at h
        | cons z zs => simp at h
    · cases w₁ with
      | nil => simp only [List.nil_append] at h; right; right; exact h
      | cons x xs =>
        cases xs with
        | nil =>
          cases w₂ with
          | nil => left; rfl
          | cons y ys => simp at h
        | cons z zs => simp at h
  full := by
    intro w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    cases w with
    | nil => simp
    | cons b w =>
      simp only [List.cons.injEq]
      constructor
      · intro h
        rcases h with h | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
      · intro h
        rcases h with h | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h

theorem mem_induced_aux {τ : Tree} {v : Word} {w : Word} :
    w ∈ (τ.carrier.filter fun u => v <:+ u).image
        (fun u => u.take (u.length - v.length)) ↔ w ++ v ∈ τ.carrier := by
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, t, rfl⟩, rfl⟩
    simpa using hu
  · intro h
    exact ⟨w ++ v, ⟨h, w, rfl⟩, by simp⟩

/-- The **tree induced by a vertex**: `τ/v = {w : wv ∈ τ}`. -/
def induced (τ : Tree) (v : Word) (hv : v ∈ τ.carrier) : Tree where
  carrier := (τ.carrier.filter fun u => v <:+ u).image fun u => u.take (u.length - v.length)
  nonempty := by
    refine ⟨[], Finset.mem_image.mpr ⟨v, ?_, ?_⟩⟩
    · simp [hv]
    · simp
  suffix_closed := by
    intro w₁ w₂ h
    rw [mem_induced_aux] at h ⊢
    exact τ.suffix_closed w₁ (w₂ ++ v) (by simpa [List.append_assoc] using h)
  full := by
    intro w
    rw [mem_induced_aux, mem_induced_aux]
    simpa using τ.full (w ++ v)

/-- **Juxtaposition** `τ ⌣ τ' = {ε} ∪ {wλ : w ∈ τ} ∪ {w'ρ : w' ∈ τ'}` (4.4); here `wλ` is
`w ++ [false]`. -/
def juxt (τ τ' : Tree) : Tree where
  carrier := insert [] ((τ.carrier.image fun w => w ++ [false]) ∪
    (τ'.carrier.image fun w => w ++ [true]))
  nonempty := ⟨[], by simp⟩
  suffix_closed := by
    intro w₁ w₂ h
    induction w₂ using List.reverseRecOn with
    | nil => simp
    | append_singleton xs b =>
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image] at h ⊢
      rw [← List.append_assoc] at h
      rcases h with h_nil | ⟨u, hu, h_eq⟩ | ⟨u, hu, h_eq⟩
      · simp at h_nil
      · obtain ⟨h1, h2⟩ := List.append_inj h_eq (by have hlen := congrArg List.length h_eq; simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hlen ⊢; omega)
        have hb : b = false := by simpa using (congrArg List.head? h2).symm
        subst hb
        right; left
        refine ⟨xs, ?_, rfl⟩
        exact τ.suffix_closed w₁ xs (h1 ▸ hu)
      · obtain ⟨h1, h2⟩ := List.append_inj h_eq (by have hlen := congrArg List.length h_eq; simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hlen ⊢; omega)
        have hb : b = true := by simpa using (congrArg List.head? h2).symm
        subst hb
        right; right
        refine ⟨xs, ?_, rfl⟩
        exact τ'.suffix_closed w₁ xs (h1 ▸ hu)
  full := by
    intro w
    induction w using List.reverseRecOn with
    | nil =>
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      constructor
      · intro _
        right; right
        exact ⟨[], τ'.nil_mem, rfl⟩
      · intro _
        right; left
        exact ⟨[], τ.nil_mem, rfl⟩
    | append_singleton xs b =>
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      cases b with
      | false =>
        constructor
        · intro h
          rcases h with h | ⟨u, hu, h_eq⟩ | ⟨u, hu, h_eq⟩
          · simp at h
          · rw [← List.cons_append] at h_eq
            obtain ⟨h1, -⟩ := List.append_inj h_eq (by have hlen := congrArg List.length h_eq; simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hlen ⊢; omega)
            subst h1
            right; left
            refine ⟨true :: xs, (τ.full xs).mp hu, ?_⟩
            rw [List.cons_append]
          · rw [← List.cons_append] at h_eq
            obtain ⟨-, h2⟩ := List.append_inj h_eq (by have hlen := congrArg List.length h_eq; simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hlen ⊢; omega)
            cases h2
        · intro h
          rcases h with h | ⟨u, hu, h_eq⟩ | ⟨u, hu, h_eq⟩
          · simp at h
          · rw [← List.cons_append] at h_eq
            obtain ⟨h1, -⟩ := List.append_inj h_eq (by have hlen := congrArg List.length h_eq; simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hlen ⊢; omega)
            subst h1
            right; left
            refine ⟨false :: xs, (τ.full xs).mpr hu, ?_⟩
            rw [List.cons_append]
          · rw [← List.cons_append] at h_eq
            obtain ⟨-, h2⟩ := List.append_inj h_eq (by have hlen := congrArg List.length h_eq; simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hlen ⊢; omega)
            cases h2
      | true =>
        constructor
        · intro h
          rcases h with h | ⟨u, hu, h_eq⟩ | ⟨u, hu, h_eq⟩
          · simp at h
          · rw [← List.cons_append] at h_eq
            obtain ⟨-, h2⟩ := List.append_inj h_eq (by have hlen := congrArg List.length h_eq; simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hlen ⊢; omega)
            cases h2
          · rw [← List.cons_append] at h_eq
            obtain ⟨h1, -⟩ := List.append_inj h_eq (by have hlen := congrArg List.length h_eq; simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hlen ⊢; omega)
            subst h1
            right; right
            refine ⟨true :: xs, (τ'.full xs).mp hu, ?_⟩
            rw [List.cons_append]
        · intro h
          rcases h with h | ⟨u, hu, h_eq⟩ | ⟨u, hu, h_eq⟩
          · simp at h
          · rw [← List.cons_append] at h_eq
            obtain ⟨-, h2⟩ := List.append_inj h_eq (by have hlen := congrArg List.length h_eq; simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hlen ⊢; omega)
            cases h2
          · rw [← List.cons_append] at h_eq
            obtain ⟨h1, -⟩ := List.append_inj h_eq (by have hlen := congrArg List.length h_eq; simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at hlen ⊢; omega)
            subst h1
            right; right
            refine ⟨false :: xs, (τ'.full xs).mpr hu, ?_⟩
            rw [List.cons_append]

@[inherit_doc] scoped infixl:70 " ⌣ " => Tree.juxt

/-- The left and right branches `τ/λ`, `τ/ρ` of a nontrivial tree. -/
def left (τ : Tree) (h : [false] ∈ τ.carrier) : Tree := τ.induced [false] h

/-- See `Tree.left`. -/
def right (τ : Tree) (h : [true] ∈ τ.carrier) : Tree := τ.induced [true] h

/-- Descendant relation `w ⇝ v`: `v = z w`. -/
def Descends (w v : Word) : Prop := w <:+ v

/-- The involution `ṽ` on words: swap the last letter, `λ ↔ ρ` (`wλ ↦ wρ`, `wρ ↦ wλ`,
`ε ↦ ε`). -/
def tilde : Word → Word
  | [] => []
  | v => (v.dropLast) ++ [!(v.getLast?.getD false)]

@[simp] theorem tilde_append_singleton (w : Word) (b : Bool) :
    tilde (w ++ [b]) = w ++ [!b] := by
  simp [tilde, List.dropLast_append_cons]

@[simp] theorem tilde_involutive (w : Word) : tilde (tilde w) = w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b => simp

@[simp] theorem tilde_length (w : Word) : (tilde w).length = w.length := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b => simp

/-- `flip_v : M → M`, sending `z v ↦ z̃ v` and fixing everything else. -/
def flipWord (v w : Word) : Word :=
  if v <:+ w then (tilde (w.take (w.length - v.length))) ++ v else w

@[simp] theorem flipWord_append (v z : Word) :
    flipWord v (z ++ v) = tilde z ++ v := by
  simp [flipWord]

@[simp] theorem flipWord_involutive (v w : Word) : flipWord v (flipWord v w) = w := by
  by_cases h : v <:+ w
  · obtain ⟨z, rfl⟩ := h
    simp
  · simp [flipWord, h]

@[simp] theorem flipWord_length (v w : Word) : (flipWord v w).length = w.length := by
  by_cases h : v <:+ w
  · obtain ⟨z, rfl⟩ := h
    simp
  · simp [flipWord, h]

/-- Flips preserve the ancestor relation on words. -/
theorem flipWord_suffix (v a w : Word) (h : a <:+ w) :
    flipWord v a <:+ flipWord v w := by
  by_cases ha : v <:+ a
  · obtain ⟨z, rfl⟩ := ha
    obtain ⟨u, rfl⟩ := h
    rw [flipWord_append, ← List.append_assoc, flipWord_append]
    induction z using List.reverseRecOn with
    | nil => simpa [tilde] using (List.suffix_append (tilde u) v)
    | append_singleton z b =>
      simp only [← List.append_assoc, tilde_append_singleton]
      exact ⟨u, by simp [List.append_assoc]⟩
  · by_cases hw : v <:+ w
    · have hav : a <:+ v := (List.suffix_or_suffix_of_suffix h hw).resolve_right ha
      obtain ⟨z, rfl⟩ := hw
      rw [flipWord_append]
      simp only [flipWord, ha, ↓reduceIte]
      exact hav.trans (List.suffix_append _ _)
    · simpa [flipWord, ha, hw] using h

/-- A flip sends each child to a child of the image of its parent. -/
theorem flipWord_cons (v w : Word) (b : Bool) :
    ∃ c : Bool, flipWord v (b :: w) = c :: flipWord v w := by
  have h := flipWord_suffix v w (b :: w) (List.suffix_cons b w)
  obtain ⟨u, hu⟩ := h
  have hl := congrArg List.length hu
  simp only [List.length_append, flipWord_length, List.length_cons] at hl
  have : u.length = 1 := by omega
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp this
  exact ⟨c, hu.symm⟩

/-- The flip of a tree at a vertex: `flip_v(τ) = {flip_v(w) : w ∈ τ}`. -/
def flip (v : Word) (τ : Tree) : Tree where
  carrier := τ.carrier.image (flipWord v)
  nonempty := τ.nonempty.image _
  suffix_closed := by
    intro w₁ w₂ h
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h
    have hs : w₂ <:+ flipWord v w := ⟨w₁, heq.symm⟩
    have hs' := flipWord_suffix v w₂ (flipWord v w) hs
    rw [flipWord_involutive] at hs'
    obtain ⟨u, hu⟩ := hs'
    apply Finset.mem_image.mpr
    refine ⟨flipWord v w₂, ?_, flipWord_involutive v w₂⟩
    apply τ.suffix_closed u (flipWord v w₂)
    simpa [hu] using hw
  full := by
    intro w
    have hmem (z : Word) : z ∈ τ.carrier.image (flipWord v) ↔ flipWord v z ∈ τ.carrier := by
      constructor
      · intro hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        simpa using hu
      · intro hz
        exact Finset.mem_image.mpr ⟨flipWord v z, hz, flipWord_involutive v z⟩
    rw [hmem, hmem]
    obtain ⟨a, ha⟩ := flipWord_cons v w false
    obtain ⟨b, hb⟩ := flipWord_cons v w true
    have hab : a ≠ b := by
      intro heq
      have he : flipWord v (false :: w) = flipWord v (true :: w) := by rw [ha, hb, heq]
      have he' := congrArg (flipWord v) he
      simp at he'
    rw [ha, hb]
    cases a <;> cases b <;> simp_all [τ.full]

/-- A vertex is **internal** if it is not a leaf. -/
def IsInternal (τ : Tree) (v : Word) : Prop := v ∈ τ.carrier ∧ (false :: v) ∈ τ.carrier

/-- An internal vertex `v` is a **symmetry vertex** if `flip_v τ = τ`. -/
def IsSymmetry (τ : Tree) (v : Word) : Prop := τ.IsInternal v ∧ flip v τ = τ

end Tree

/-! ## The reverse lexicographic order, surface vertices, contraction (§4.3) -/

namespace Tree

/-- Reverse lexicographic order on words: `w₁ ⪯ w₂` iff `w₂ = z w₁`, or `w₁ = v₁ s`,
`w₂ = v₂ s` with `s` the longest common suffix and `v₁` starting with `λ`. -/
def revLex (w₁ w₂ : Word) : Prop :=
  w₁ <:+ w₂ ∨ ∃ s v₁ v₂, w₁ = v₁ ++ s ∧ w₂ = v₂ ++ s ∧ v₁.head? = some false ∧
    v₂.head? = some true

/-- A vertex `v` is **superficial** if both `λv` and `ρv` are leaves. -/
def IsSuperficial (τ : Tree) (v : Word) : Prop :=
  τ.IsLeaf (false :: v) ∧ τ.IsLeaf (true :: v)

/-- The set `supf τ` of superficial vertices. -/
def supf (τ : Tree) : Finset Word := τ.carrier.filter fun v => τ.IsSuperficial v

/-- The position `pos_τ(v)` of a superficial vertex: the number of leaves `w ≺ λv`. -/
def pos (τ : Tree) (v : Word) : ℕ := (τ.leaves.filter fun w => revLex w (false :: v) ∧
  w ≠ false :: v).card

/-- Contraction of a tree at a superficial vertex: `c_v τ = τ \ {λv, ρv}`.

**Note.** The thesis contracts only superficial vertices. For an arbitrary
vertex, deleting its children can leave their descendants, so the result need not be suffix-closed.
We require the vertex to be superficial. -/
def contract (τ : Tree) (v : Word) (hv : τ.IsSuperficial v) : Tree where
  carrier := τ.carrier \ {false :: v, true :: v}
  nonempty := by
    refine ⟨[], ?_⟩
    simp [τ.nil_mem]
  suffix_closed := by
    have no_desc (b : Bool) (hb : τ.IsLeaf (b :: v)) (xs : Word)
        (hx : xs ++ b :: v ∈ τ.carrier) : xs = [] := by
      induction xs using List.reverseRecOn with
      | nil => rfl
      | append_singleton ys c =>
        have hc : c :: b :: v ∈ τ.carrier := by
          apply τ.suffix_closed ys
          simpa [List.append_assoc] using hx
        cases c with
        | false => exact (hb.2 hc).elim
        | true => exact (hb.2 ((τ.full (b :: v)).mpr hc)).elim
    intro w₁ w₂ h
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at h ⊢
    refine ⟨τ.suffix_closed w₁ w₂ h.1, ?_, ?_⟩
    · intro heq
      subst w₂
      have := no_desc false hv.1 w₁ h.1
      subst w₁
      exact h.2.1 rfl
    · intro heq
      subst w₂
      have := no_desc true hv.2 w₁ h.1
      subst w₁
      exact h.2.2 rfl
  full := by
    intro w
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or,
      List.cons.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and, not_false_eq_true,
      true_and]
    rw [τ.full w]
    simp

end Tree

end MartinPhd

end
end Trees

section Complex

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 4 — §4.3 The complex `T•(A)`

For a magma `A` nilpotent in 2 steps, `T_n(A) = ⨁_{|τ| = n} A(τ)` with `A(τ) ≅ A^{⊗|τ|}`.
-/

open scoped TensorProduct BigOperators

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {k : Type} [Field k]

/-- `A(τ)`: for the outline we use the canonical identification `A(τ) ≅ A^{⊗|τ|}`
(thesis (4.5) defines it recursively by `A(τ) = A(τ/λ) ⊗ A(τ/ρ)`). -/
abbrev treeObj (A : Mag2 k) (τ : Tree) : Type := ⨂[k] _ : Fin τ.arity, A.A

/-- `T_n(A) = ⨁_{|τ| = n} A(τ)`. -/
abbrev Tn (A : Mag2 k) (n : ℕ) : Type := {τ : Tree // τ.arity = n} →₀ (⨂[k] _ : Fin n, A.A)

/-- `T_n(A)` is a trivial extension by its tensor-power model: generated in arity `n`
by trees of arity `n`. -/
theorem Tree.arity_contract (τ : Tree) (v : Word) (h : τ.IsSuperficial v) :
    (τ.contract v h).arity + 1 = τ.arity := by
  have hv : v ∈ τ.carrier := τ.suffix_closed [false] v (by simpa using h.1.1)
  have hf : false :: v ∈ τ.leaves := by simp [Tree.leaves, h.1.1, h.1.2]
  have ht : true :: v ∈ τ.leaves := by simp [Tree.leaves, h.2.1, h.2.2]
  have hvnot : v ∉ τ.leaves := by simp [Tree.leaves, h.1.1]
  have heq : (τ.contract v h).leaves = insert v (τ.leaves \ {false :: v, true :: v}) := by
    ext w
    simp only [Tree.leaves, Tree.contract, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, not_or, List.cons.injEq,
      Bool.false_eq_true, Bool.true_eq_false, false_and, not_false_eq_true, true_and]
    by_cases hw : w = v
    · subst w
      simp [hv, h.1.1]
    · simp [hw]
      aesop
  rw [Tree.arity, heq, Finset.card_insert_of_notMem]
  · rw [Finset.card_sdiff_of_subset]
    · have hc : 2 ≤ τ.leaves.card := by
        have hs : ({false :: v, true :: v} : Finset Word) ⊆ τ.leaves := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        simpa using Finset.card_le_card hs
      simp only [Finset.card_insert_of_notMem, Finset.card_singleton, Finset.mem_singleton,
        List.cons.injEq, Bool.false_eq_true, false_and, not_false_eq_true, Tree.arity]
      omega
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
  · simp [hvnot]

/-- The multilinear map `a₁ ⊗ ⋯ ⊗ aₙ ↦ a₁ ⊗ ⋯ ⊗ μ(aᵢ, aᵢ₊₁) ⊗ ⋯ ⊗ aₙ` (position `i`
counted from `0`; the junk value for `i + 1 ≥ n` is `0`).

**Note.** The thesis only contracts at a superficial
vertex, where `i + 1 < n`. This outline accepts arbitrary `n` and `i`, but the displayed
formula does not give a multilinear map in general: for `n = 1`, the empty tensor product
makes the formula constant at `1`, independently of the input. The proof fields remain open
until the construction is restricted to valid positions or its invalid cases are redefined. -/
def contractML (A : Mag2 k) (n i : ℕ) :
    MultilinearMap k (fun _ : Fin n => A.A) (⨂[k] _ : Fin (n - 1), A.A) where
  toFun a :=
    let a' : ℕ → A.A := fun m => if h : m < n then a ⟨m, h⟩ else 0
    PiTensorProduct.tprod k fun j : Fin (n - 1) =>
      if (j : ℕ) < i then a' j else if (j : ℕ) = i then A.μ (a' i) (a' (i + 1)) else a' (j + 1)
  map_update_add' := sorry
  map_update_smul' := sorry

/-- Contraction `c_v` of the decoration at position `i`. -/
def contractMap (A : Mag2 k) (n i : ℕ) : (⨂[k] _ : Fin n, A.A) →ₗ[k] ⨂[k] _ : Fin (n - 1), A.A :=
  PiTensorProduct.lift (contractML A n i)

/-- The differential of `T•(A)` by the explicit formula of **Proposition 4.2**:
`d(x) = ∑_{v ∈ supf τ} (-1)^{pos_τ(v)} c_v(x)`. -/
def dT (A : Mag2 k) (n : ℕ) : Tn A n →ₗ[k] Tn A (n - 1) :=
  Finsupp.lsum k fun τ : {τ : Tree // τ.arity = n} =>
    ∑ v ∈ τ.1.supf.attach, ((-1 : k) ^ τ.1.pos v.1) •
      (Finsupp.lsingle (R := k) ⟨τ.1.contract v.1 (Finset.mem_filter.mp v.2).2, by
        have h := Tree.arity_contract τ.1 v.1 (Finset.mem_filter.mp v.2).2
        have ht := τ.2
        omega⟩ ∘ₗ
        contractMap A n (τ.1.pos v.1))

/-- The homology `H_n(A)` of `T•(A)`. -/
abbrev HomologyT (A : Mag2 k) (n : ℕ) : Type :=
  LinearMap.ker (dT A n) ⧸ (LinearMap.range (dT A (n + 1))).comap (LinearMap.ker (dT A n)).subtype

/-- **Proposition 4.1.** `d_{n-1} ∘ d_n = 0`. -/
theorem dT_comp_dT (A : Mag2 k) (n : ℕ) : dT A (n - 1) ∘ₗ dT A n = 0 := sorry

/-- Base cases of the recursion (4.6) used by the thesis as definition: `d₁ = 0` and
`d₂ = μ` (the Leibniz rule `d(x ⊗ y) = d(x) ⊗ y + (-1)^{|τ/λ|} x ⊗ d(y)` on
`A(τ/λ) ⊗ A(τ/ρ)` determines the rest, and agrees with Proposition 4.2).

**Change (Proposition 4.2).** We *define* `d` by the explicit formula of Proposition 4.2
and state (4.6) as a lemma, rather than the converse; the two agree. -/
theorem dT_two (A : Mag2 k) (a b : A.A) :
    dT A 2 (Finsupp.single ⟨Tree.V, by decide⟩ (PiTensorProduct.tprod k ![a, b])) =
      Finsupp.single ⟨Tree.triv, by decide⟩ (PiTensorProduct.tprod k fun _ => A.μ a b) := sorry

/-- The juxtaposition product `⌣ : T_n(A) × T_m(A) → T_{n+m}(A)` (4.8); `d` is a graded
derivation for it as soon as `n + m > 2`
(`d(x ⌣ y) = d(x) ⌣ y + (-1)^n x ⌣ d(y)`; it fails for `n = m = 1`). -/
def juxtT (A : Mag2 k) (n m : ℕ) : Tn A n →ₗ[k] Tn A m →ₗ[k] Tn A (n + m) := sorry

end MartinPhd

end
end Complex

section Laplacian

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 4 — §4.4 The Laplacian, §4.5 homology of 2-step nilpotent magmas, §4.6 examples

The Laplacian argument of the thesis (after Kostant) is carried out over `ℝ` with inner
products. The thesis allows any field with a *strongly nondegenerate* bilinear form; we state
the real case, which is the one used for every computation (Props 4.7, 4.12, examples).
-/

open scoped TensorProduct BigOperators RealInnerProductSpace

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §4.4 The Laplacian of a complex of finite-dimensional inner product spaces -/

/-- A chain complex of finite-dimensional real inner product spaces, with `d n : C (n+1) → C n`. -/
structure FDChain where
  C : ℕ → Type
  [normed : ∀ n, NormedAddCommGroup (C n)]
  [inner : ∀ n, InnerProductSpace ℝ (C n)]
  [fd : ∀ n, FiniteDimensional ℝ (C n)]
  d : ∀ n, C (n + 1) →ₗ[ℝ] C n
  d_d : ∀ n, d n ∘ₗ d (n + 1) = 0

attribute [instance] FDChain.normed FDChain.inner FDChain.fd

namespace FDChain

variable (K : FDChain)

/-- The adjoint `∂ n : C n → C (n+1)` of `d n`. -/
def adj (n : ℕ) : K.C n →ₗ[ℝ] K.C (n + 1) := LinearMap.adjoint (K.d n)

/-- The **Laplacian** `Δ = ∂d + d∂`. -/
def laplacian : ∀ n, K.C n →ₗ[ℝ] K.C n
  | 0 => K.d 0 ∘ₗ K.adj 0
  | n + 1 => K.d (n + 1) ∘ₗ K.adj (n + 1) + K.adj n ∘ₗ K.d n

/-- Cycles `Z_n`. -/
def cycles : ∀ n, Submodule ℝ (K.C n)
  | 0 => ⊤
  | n + 1 => LinearMap.ker (K.d n)

/-- Homology `H_n`. -/
abbrev homology (n : ℕ) : Type :=
  K.cycles n ⧸ (LinearMap.range (K.d n)).comap (K.cycles n).subtype

theorem inner_adj_left (n : ℕ) (y : K.C n) (x : K.C (n + 1)) :
    Inner.inner ℝ (K.adj n y) (x) = Inner.inner ℝ (y) (K.d n x) :=
  LinearMap.adjoint_inner_left (K.d n) x y

theorem inner_adj_right (n : ℕ) (x : K.C (n + 1)) (y : K.C n) :
    Inner.inner ℝ (x) (K.adj n y) = Inner.inner ℝ (K.d n x) (y) :=
  LinearMap.adjoint_inner_right (K.d n) x y

theorem inner_laplacian_zero (x : K.C 0) :
    Inner.inner ℝ (K.laplacian 0 x) (x) = ‖K.adj 0 x‖ ^ 2 := by
  simp only [laplacian, LinearMap.comp_apply]
  rw [← K.inner_adj_right 0 (K.adj 0 x) x, real_inner_self_eq_norm_sq]

theorem inner_laplacian_succ (n : ℕ) (x : K.C (n + 1)) :
    Inner.inner ℝ (K.laplacian (n + 1) x) (x) = ‖K.adj (n + 1) x‖ ^ 2 + ‖K.d n x‖ ^ 2 := by
  simp only [laplacian, LinearMap.add_apply, LinearMap.comp_apply]
  rw [inner_add_left, ← K.inner_adj_right (n + 1) (K.adj (n + 1) x) x,
    K.inner_adj_left n (K.d n x) x, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- **Proposition 4.3.** Every element of `ker Δ_n` is a cycle, and the inclusion induces an
isomorphism `ker Δ_n ≅ H_n`. -/
theorem ker_laplacian_le_cycles (n : ℕ) : LinearMap.ker (K.laplacian n) ≤ K.cycles n := by
  cases n with
  | zero => intro x _; trivial
  | succ n =>
    intro x hx
    have h := K.inner_laplacian_succ n x
    rw [LinearMap.mem_ker.1 hx, inner_zero_left] at h
    have h1 : ‖K.d n x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖K.adj (n + 1) x‖, sq_nonneg ‖K.d n x‖]
    exact LinearMap.mem_ker.2 (norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1))

/-- Harmonic elements are annihilated by `∂`. -/
theorem adj_eq_zero_of_laplacian (n : ℕ) (x : K.C n) (hx : K.laplacian n x = 0) : K.adj n x = 0 := by
  cases n with
  | zero =>
    have h := K.inner_laplacian_zero x
    rw [hx, inner_zero_left] at h
    exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h.symm)
  | succ n =>
    have h := K.inner_laplacian_succ n x
    rw [hx, inner_zero_left] at h
    have h1 : ‖K.adj (n + 1) x‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖K.adj (n + 1) x‖, sq_nonneg ‖K.d n x‖]
    exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h1)

/-- **Proposition 4.3** (harmonic representatives). -/
theorem ker_laplacian_equiv_homology (n : ℕ) :
    Nonempty (LinearMap.ker (K.laplacian n) ≃ₗ[ℝ] K.homology n) := by
  let f : LinearMap.ker (K.laplacian n) →ₗ[ℝ] K.homology n :=
    (Submodule.mkQ ((LinearMap.range (K.d n)).comap (K.cycles n).subtype)) ∘ₗ
      Submodule.inclusion (K.ker_laplacian_le_cycles n)
  refine ⟨LinearEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hb : (⟨x.1, K.ker_laplacian_le_cycles n x.2⟩ : K.cycles n) ∈
        (LinearMap.range (K.d n)).comap (K.cycles n).subtype := by
      simpa [f, Submodule.Quotient.mk_eq_zero] using hx
    obtain ⟨y, hy⟩ := hb
    have hz : K.adj n x.1 = 0 := K.adj_eq_zero_of_laplacian n x.1 (LinearMap.mem_ker.1 x.2)
    have h2 : Inner.inner ℝ x.1 x.1 = 0 := by
      calc Inner.inner ℝ x.1 x.1 = Inner.inner ℝ (K.d n y) x.1 := by rw [hy]; rfl
        _ = Inner.inner ℝ y (K.adj n x.1) := (K.inner_adj_right n y x.1).symm
        _ = 0 := by rw [hz, inner_zero_right]
    exact Subtype.ext (inner_self_eq_zero.1 h2)
  · intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    set R : Submodule ℝ (K.C n) := LinearMap.range (K.d n) with hR
    have hsup : R ⊔ Rᗮ = ⊤ := (Submodule.isCompl_orthogonal_of_hasOrthogonalProjection (K := R)).sup_eq_top
    obtain ⟨r, hr, w, hw, hrw⟩ : ∃ r ∈ R, ∃ w ∈ Rᗮ, r + w = z.1 :=
      Submodule.mem_sup.1 (by rw [hsup]; trivial)
    have hadj : K.adj n w = 0 := by
      have h0 : Inner.inner ℝ (K.d n (K.adj n w)) w = 0 :=
        (Submodule.mem_orthogonal _ _).1 hw _ ⟨K.adj n w, rfl⟩
      rw [← K.inner_adj_right n (K.adj n w) w] at h0
      exact inner_self_eq_zero.1 h0
    obtain ⟨y, rfl⟩ := hr
    have hlap : K.laplacian n w = 0 := by
      cases n with
      | zero => simp [laplacian, hadj]
      | succ m =>
        have hz : K.d m z.1 = 0 := z.2
        have hdd : K.d m (K.d (m + 1) y) = 0 := by
          simpa using LinearMap.congr_fun (K.d_d m) y
        have hdw : K.d m w = 0 := by
          have : w = z.1 - K.d (m + 1) y := by rw [← hrw]; abel
          rw [this, map_sub, hz, hdd, sub_zero]
        simp [laplacian, hadj, hdw]
    refine ⟨⟨w, LinearMap.mem_ker.2 hlap⟩, ?_⟩
    simp only [f, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    refine ⟨-y, ?_⟩
    change K.d n (-y) = w - z.1
    rw [map_neg, ← hrw]
    abel

end FDChain

/-! ## §4.5 Homology of 2-step nilpotent magmas

**Not stated.** Propositions 4.4 (`∂(x ⌣ y) = ∂x ⌣ y + (-1)ⁿ x ⌣ ∂y`) and 4.5
(`Δ(x ⌣ y) = Δx ⌣ y + x ⌣ Δy`) are statements about the inner product structure of `T_n(A)`,
which the outline does not construct (`TChain` is a placeholder); their only consequences used
later are the homological Corollary 4.6 and Proposition 4.7 below. -/

variable {k : Type} [Field k]

/-- Morphisms (isomorphisms) of magmas. -/
structure Mag2.Equiv (A B : Mag2 k) where
  e : A.A ≃ₗ[k] B.A
  map_μ : ∀ x y, e (A.μ x y) = B.μ (e x) (e y)

/-- The multiplication `A ⊗ A → A`. -/
def Mag2.mulMap (A : Mag2 k) : A.A ⊗[k] A.A →ₗ[k] A.A := TensorProduct.lift A.μ

/-- The **free** magma nilpotent in 2 steps `F(V) = V ⊕ (V ⊗ V)` with
`μ((v,w),(v',w')) = (0, v ⊗ v')`. -/
def freeMag2 (V : Type) [AddCommGroup V] [Module k V] : Mag2 k where
  A := V × (V ⊗[k] V)
  μ := LinearMap.mk₂ k (fun x y => (0, x.1 ⊗ₜ y.1))
    (by intros; simp [TensorProduct.add_tmul])
    (by intros; simp [TensorProduct.smul_tmul'])
    (by intros; simp [TensorProduct.tmul_add])
    (by intros; simp [TensorProduct.tmul_smul])
  μ_left := by intros; simp
  μ_right := by intros; simp

/-- A 2-step nilpotent magma is **free** if it is isomorphic to some `F(V)`. -/
def Mag2.IsFree (A : Mag2 k) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module k V), Nonempty (Mag2.Equiv A (freeMag2 V))

/-- **Corollary 4.6.** Over `ℝ`, `H_n(A) ≠ 0` for all `n ≥ 1` iff `H_1(A) ≠ 0` and
`H_2(A) ≠ 0`. -/
theorem homologyT_ne_zero_iff (A : Mag2 ℝ) [FiniteDimensional ℝ A.A] :
    (∀ n ≥ 1, Nontrivial (HomologyT A n)) ↔
      Nontrivial (HomologyT A 1) ∧ Nontrivial (HomologyT A 2) := by
  constructor
  · intro h
    exact ⟨h 1 (by omega), h 2 (by omega)⟩
  · sorry

/-- **Proposition 4.7.** Over `ℝ`, `ker Δ_n = ⨁_{i=1}^{n-1} ker Δ_i ⌣ ker Δ_{n-i}` for `n > 2`;
in terms of dimensions of homology, `dim H_n = ∑_{i=1}^{n-1} dim H_i · dim H_{n-i}`. -/
theorem finrank_homologyT_rec (A : Mag2 ℝ) [FiniteDimensional ℝ A.A] (n : ℕ) (hn : 2 < n) :
    Module.finrank ℝ (HomologyT A n) =
      ∑ i ∈ Finset.Ioo 0 n, Module.finrank ℝ (HomologyT A i) * Module.finrank ℝ (HomologyT A (n - i)) :=
  sorry

/-- **Proposition 4.8.** Let `W = μ(A,A)` and `V` a complement of `W` in `A`. Then
`dim H₂(A) = (dim V)² - dim W` and `(V ⊗ V) ∩ ker μ ≅ H₂(A)`. -/
theorem prop_4_8 (A : Mag2 k) [FiniteDimensional k A.A] (V : Submodule k A.A)
    (hV : IsCompl V (LinearMap.range A.mulMap)) :
    Module.finrank k (HomologyT A 2) =
      Module.finrank k V ^ 2 - Module.finrank k (LinearMap.range A.mulMap) ∧
    Nonempty ((LinearMap.range (TensorProduct.map V.subtype V.subtype) ⊓
      LinearMap.ker A.mulMap : Submodule k (A.A ⊗[k] A.A)) ≃ₗ[k] HomologyT A 2) := sorry

/-- **Corollary 4.9.** If `A ≠ 0` and `H_n(A) = 0` for some `n ≥ 2`, then `A` is free. -/
theorem isFree_of_homology_eq_zero (A : Mag2 k) [Nontrivial A.A] (n : ℕ) (hn : 2 ≤ n)
    (h : Subsingleton (HomologyT A n)) : A.IsFree := sorry

/-- **Corollary 4.10.** A nonzero 2-step nilpotent magma is free iff `H_n(A) = 0` for all
`n ≥ 2`; otherwise `H_n(A) ≠ 0` for all `n`. -/
theorem isFree_iff_homology_eq_zero (A : Mag2 ℝ) [FiniteDimensional ℝ A.A] [Nontrivial A.A] :
    A.IsFree ↔ ∀ n ≥ 2, Subsingleton (HomologyT A n) := by
  constructor
  · sorry
  · intro h
    exact isFree_of_homology_eq_zero A 2 (by omega) (h 2 (by omega))

/-- **Corollary 4.11.** The operad `OM` of 2-step nilpotent magmas is Koszul; in the language
of the Ginzburg–Kapranov criterion, `H_n(F) = 0` for `n ≥ 2` and every free 2-step nilpotent
magma `F = F(V)`.

**Change.** Operads and Koszulness are not in Mathlib; we state the homological
criterion, which is how the thesis proves the corollary. -/
theorem homology_freeMag2_eq_zero (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (n : ℕ) (hn : 2 ≤ n) : Subsingleton (HomologyT (freeMag2 (k := ℝ) V) n) := sorry

/-! ## §4.6 Examples -/

/-- **§4.6.1.** `H_1(F(V)) ≅ V` and `H_n(F(V)) = 0` for `n ≥ 2` (Spec Δ₁ = {0,1}, Spec Δ₂ = {1,2}). -/
theorem homology_one_freeMag2 (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :
    Nonempty (HomologyT (freeMag2 (k := ℝ) V) 1 ≃ₗ[ℝ] V) := sorry

/-- The **Heisenberg Lie algebra** `𝔥ₙ` of dimension `2n + 1` with basis
`x₁..xₙ, y₁..yₙ, z` and `[xᵢ, yᵢ] = z`. -/
def heisenberg (n : ℕ) : Lie2 ℝ where
  A := (Fin n ⊕ Fin n ⊕ Unit) → ℝ
  μ := LinearMap.mk₂ ℝ
    (fun x y => fun j => match j with
      | Sum.inr (Sum.inr ()) => ∑ i, (x (Sum.inl i) * y (Sum.inr (Sum.inl i)) -
          x (Sum.inr (Sum.inl i)) * y (Sum.inl i))
      | _ => 0)
    (by intros; ext j; rcases j with i | i | ⟨⟩ <;> simp only [Pi.add_apply, Pi.zero_apply, add_zero, mul_zero, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intros; ring)
    (by intros; ext j; rcases j with i | i | ⟨⟩ <;> simp only [Pi.smul_apply, Pi.zero_apply, add_zero, mul_zero, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intros; ring)
    (by intros; ext j; rcases j with i | i | ⟨⟩ <;> simp only [Pi.add_apply, Pi.zero_apply, add_zero, mul_zero, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intros; ring)
    (by intros; ext j; rcases j with i | i | ⟨⟩ <;> simp only [Pi.smul_apply, Pi.zero_apply, add_zero, mul_zero, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intros; ring)
  μ_left := by intros; ext j; rcases j with i | i | ⟨⟩ <;> simp
  μ_right := by intros; ext j; rcases j with i | i | ⟨⟩ <;> simp
  antisymm := by
    intros; ext j; rcases j with i | i | ⟨⟩ <;> simp only [Pi.neg_apply, LinearMap.mk₂_apply, neg_zero, ← Finset.sum_neg_distrib];
    apply Finset.sum_congr rfl; intros; ring

/-- **§4.6.2.** `dim H₁(𝔥ₙ) = 2n` and `dim H₂(𝔥ₙ) = 4n² - 1` (`Spec Δ₁ = {0, 2n}`,
`Spec Δ₂ = {0, 2n, 4n}`). Higher dimensions follow from Proposition 4.7, e.g.
`dim H₃ = 16n³ - 4n`, `dim H₄ = 80n⁴ - 24n² + 1`.

**Gap (missing hypothesis).** The formulas require `n > 0`: at `n = 0`, the asserted
second dimension is `-1`, while a vector space dimension is nonnegative. -/
theorem finrank_homology_heisenberg (n : ℕ) (hn : 0 < n) :
    Module.finrank ℝ (HomologyT (heisenberg n).toMag2 1) = 2 * n ∧
    (Module.finrank ℝ (HomologyT (heisenberg n).toMag2 2) : ℤ) = 4 * n ^ 2 - 1 ∧
    (Module.finrank ℝ (HomologyT (heisenberg n).toMag2 3) : ℤ) = 16 * n ^ 3 - 4 * n ∧
    (Module.finrank ℝ (HomologyT (heisenberg n).toMag2 4) : ℤ) = 80 * n ^ 4 - 24 * n ^ 2 + 1 :=
  sorry

/-- A basis `{x₁..xₛ, y₁..yₜ}` is **nice** if `μ(xᵢ, xⱼ) = λᵢⱼ y_{σ(i,j)}`, every product
involving some `yᵢ` vanishes, and `im μ = ⟨y₁..yₜ⟩`. It is **tabular** if the `λᵢⱼ ∈ {0,1}`,
and **Lie-tabular** (for Lie algebras) if `λᵢⱼ ∈ {0, ±1}`. -/
structure NiceBasis (A : Mag2 ℝ) (s t : ℕ) where
  x : Fin s → A.A
  y : Fin t → A.A
  basis : Module.Basis (Fin s ⊕ Fin t) ℝ A.A
  basis_x : ∀ i, basis (Sum.inl i) = x i
  basis_y : ∀ j, basis (Sum.inr j) = y j
  σ : Fin s → Fin s → Fin t
  coeff : Fin s → Fin s → ℝ
  μ_x : ∀ i j, A.μ (x i) (x j) = coeff i j • y (σ i j)
  μ_y_left : ∀ a j, A.μ a (y j) = 0
  μ_y_right : ∀ j a, A.μ (y j) a = 0
  range_μ : LinearMap.range A.mulMap = Submodule.span ℝ (Set.range y)

/-- **Proposition 4.12.** For a (Lie-)tabular algebra with nice basis (orthonormal for the
inner product), `Δ₁` and `Δ₂` have integer spectrum, `dim ker Δ₁ = s`, `dim ker Δ₂ = s² - t`;
that is `dim H₁ = s`, `dim H₂ = s² - t`. -/
theorem tabular_homology_dims (A : Mag2 ℝ) (s t : ℕ) (B : NiceBasis A s t)
    (hB : ∀ i j, B.coeff i j = 0 ∨ B.coeff i j = 1 ∨ B.coeff i j = -1) :
    Module.finrank ℝ (HomologyT A 1) = s ∧ Module.finrank ℝ (HomologyT A 2) = s ^ 2 - t :=
  sorry

end MartinPhd

end
end Laplacian

section TreesCat

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 4 — §4.7 The category `Trees` of trees and flips, §4.8 groupoids and coinvariants
-/

open CategoryTheory

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §4.7 The category `Trees` -/

/-- Arrows of the generating quiver: `(v, τ) : τ → flip_v τ` for an internal vertex `v`. -/
structure FlipArrow (τ σ : Tree) where
  v : Word
  internal : τ.IsInternal v
  eq : Tree.flip v τ = σ

/-- The quiver whose vertices are trees and whose arrows are flips. -/
def TreeQuiver : Type := Tree

instance : Quiver TreeQuiver := ⟨FlipArrow⟩

/-- The relations (4.11)–(4.13) defining `Trees`:
(4.11) `(v, flip_v τ) ∘ (v, τ) = id`;
(4.12) `(w, flip_v τ) ∘ (v, τ) = (v, flip_w τ) ∘ (w, τ)` if `λ ⇝ v` and `ρ ⇝ w`;
(4.13) `(ṽ, flip_ε η) ∘ (ε, η) = (ε, flip_v η) ∘ (v, η)` for `v ≠ ε`. -/
inductive TreesRel : ∀ {τ σ : Paths TreeQuiver}, (τ ⟶ σ) → (τ ⟶ σ) → Prop
  | inv {τ σ : Tree} (a : FlipArrow τ σ) (b : FlipArrow σ τ) (h : a.v = b.v) :
      TreesRel ((Paths.of TreeQuiver).map a ≫ (Paths.of TreeQuiver).map b) (𝟙 _)
  | commute {τ τ₁ τ₂ σ : Tree} (a₁ : FlipArrow τ τ₁) (a₂ : FlipArrow τ₁ σ)
      (b₁ : FlipArrow τ τ₂) (b₂ : FlipArrow τ₂ σ)
      (h1 : a₁.v = b₂.v) (h2 : a₂.v = b₁.v) (hv : Tree.Descends [false] a₁.v)
      (hw : Tree.Descends [true] a₂.v) :
      TreesRel ((Paths.of TreeQuiver).map a₁ ≫ (Paths.of TreeQuiver).map a₂) ((Paths.of TreeQuiver).map b₁ ≫ (Paths.of TreeQuiver).map b₂)
  | root {η τ₁ τ₂ σ : Tree} (a₁ : FlipArrow η τ₁) (a₂ : FlipArrow τ₁ σ)
      (b₁ : FlipArrow η τ₂) (b₂ : FlipArrow τ₂ σ) (h1 : a₁.v = []) (h2 : a₂.v = Tree.tilde b₁.v)
      (h3 : b₂.v = []) (hne : b₁.v ≠ []) :
      TreesRel ((Paths.of TreeQuiver).map a₁ ≫ (Paths.of TreeQuiver).map a₂) ((Paths.of TreeQuiver).map b₁ ≫ (Paths.of TreeQuiver).map b₂)

/-- The relation (4.11)–(4.13) as a `HomRel`. -/
def treesRel : HomRel (Paths TreeQuiver) := @TreesRel

/-- The category `Trees`. -/
def Trees : Type := Quotient treesRel

instance : Category.{0} Trees := inferInstanceAs (Category (Quotient treesRel))

/-- `Trees` is a groupoid (4.11). -/
instance : Groupoid.{0} Trees := sorry

/-- The object of `Trees` given by a tree. -/
def Trees.of (τ : Tree) : Trees := (⟨τ⟩ : Quotient treesRel)

/-- The symmetric-vertex flip as an endomorphism: for a symmetry vertex `v` of `τ`,
`(v, τ) ∈ Aut(τ)` (using `flip_v τ = τ`). -/
def Trees.flipHom (τ : Tree) (v : Word) (hv : τ.IsSymmetry v) : Trees.of τ ⟶ Trees.of τ :=
  (Quotient.functor treesRel).map ((Paths.of TreeQuiver).map ⟨v, hv.1, hv.2⟩)

/-- A nontrivial tree is **regular** if `τ/λ = τ/ρ` or `τ/λ ≇ τ/ρ` in `Trees`. -/
def Tree.IsRegular (τ : Tree) : Prop :=
  τ ≠ Tree.triv ∧ ∀ (hl : [false] ∈ τ.carrier) (hr : [true] ∈ τ.carrier),
    τ.left hl = τ.right hr ∨
      IsEmpty (Trees.of (τ.left hl) ≅ Trees.of (τ.right hr))

/-- A tree is **recursively regular** if `τ/v` is regular for every internal vertex `v` (and
the trivial tree is, vacuously). -/
def Tree.IsRecursivelyRegular (τ : Tree) : Prop :=
  ∀ v (hv : v ∈ τ.carrier), τ.IsInternal v → (τ.induced v hv).IsRegular

/-- The functor `leaves : Trees → Set`, `leaves(v,τ) = flip_v |_{leaves τ}`. -/
def Trees.leaves : Trees ⥤ Type := sorry

/-- **Proposition 4.13.** If `τ` is recursively regular, every `φ ∈ Aut(τ)` is a composite
`(v_n, τ) ∘ ⋯ ∘ (v_1, τ)` of flips at symmetry vertices `v_i` with `v_i ≺ v_j` for `i < j`
(reverse lexicographic order). -/
theorem Trees.aut_factorization (τ : Tree) (hτ : τ.IsRecursivelyRegular)
    (φ : Trees.of τ ⟶ Trees.of τ) :
    ∃ vs : List {v : Word // τ.IsSymmetry v},
      vs.Pairwise (fun v w => Tree.revLex v.1 w.1 ∧ v.1 ≠ w.1) ∧
      φ = (vs.map fun v => Trees.flipHom τ v.1 v.2).foldr (· ≫ ·) (𝟙 _) := sorry

/-- **Proposition 4.14.** The functor `leaves` is faithful and injective on objects. -/
theorem Trees.leaves_faithful : Trees.leaves.Faithful := sorry

/-- **Proposition 4.14** (injective on objects). -/
theorem Trees.leaves_obj_injective :
    Function.Injective fun τ : Trees => (Trees.leaves.obj τ) := sorry

/-- **Proposition 4.15.** The factorization of Proposition 4.13 is unique. -/
theorem Trees.aut_factorization_unique (τ : Tree) (hτ : τ.IsRecursivelyRegular)
    (vs ws : List {v : Word // τ.IsSymmetry v})
    (hvs : vs.Pairwise (fun v w => Tree.revLex v.1 w.1 ∧ v.1 ≠ w.1))
    (hws : ws.Pairwise (fun v w => Tree.revLex v.1 w.1 ∧ v.1 ≠ w.1))
    (h : (vs.map fun v => Trees.flipHom τ v.1 v.2).foldr (· ≫ ·) (𝟙 _) =
      (ws.map fun v => Trees.flipHom τ v.1 v.2).foldr (· ≫ ·) (𝟙 _)) : vs = ws := sorry

/-- **Corollary 4.16.** For `τ` recursively regular with at least 3 leaves,
`Aut(τ) ≅ Aut(τ/λ) × Aut(τ/ρ)` if `ε` is **not** a symmetry vertex of `τ`, and
`Aut(τ) ≅ (Aut(τ/λ) × Aut(τ/ρ)) ⋊ ⟨(ε,τ)⟩ ≅ Aut(τ/λ) ≀ ℤ/2` if it is.

**Gap (typo, Corollary 4.16).** The thesis prints the two cases the other way around; the
proof of Proposition 4.18 (and `Aut(V) ≅ ℤ/2`, `Aut(V ⌣ V) ≅ (ℤ/2 × ℤ/2) ⋊ ℤ/2`) uses the
version stated here. -/
theorem Trees.aut_nonsymmetric (τ : Tree) (hτ : τ.IsRecursivelyRegular) (h3 : 3 ≤ τ.arity)
    (hε : ¬ τ.IsSymmetry []) (hl : [false] ∈ τ.carrier) (hr : [true] ∈ τ.carrier) :
    Nonempty (Aut (Trees.of τ) ≃* Aut (Trees.of (τ.left hl)) × Aut (Trees.of (τ.right hr))) :=
  sorry

/-- The wreath product `G ≀ ℤ/2 = (G × G) ⋊ ℤ/2`, with `ℤ/2` swapping the factors. -/
def WreathZ2 (G : Type) [Group G] : Type :=
  SemidirectProduct (G × G) (Multiplicative (ZMod 2)) sorry

instance (G : Type) [Group G] : Group (WreathZ2 G) := inferInstanceAs (Group (SemidirectProduct (G × G) (Multiplicative (ZMod 2)) _))

/-- **Corollary 4.16** (symmetric case): the wreath product. -/
theorem Trees.aut_symmetric (τ : Tree) (hτ : τ.IsRecursivelyRegular) (h3 : 3 ≤ τ.arity)
    (hε : τ.IsSymmetry []) (hl : [false] ∈ τ.carrier) (hr : [true] ∈ τ.carrier) :
    Nonempty (Aut (Trees.of τ) ≃* WreathZ2 (Aut (Trees.of (τ.left hl)))) := sorry

/-! ## Otter trees -/

namespace Tree

/-- The total order on trees: first by arity, then by `τ/λ ≺ τ'/λ`, then by `τ/ρ ≺ τ'/ρ`. -/
def prec (τ τ' : Tree) : Prop := τ.arity < τ'.arity ∨ sorry

end Tree

/-- **Otter trees** of arity `n`: the minimal trees (for `≺`) in each flip-equivalence class
(Otter's enumeration of unordered binary trees [Ott48]). -/
def Ott (n : ℕ) : Set Tree := {τ | τ.arity = n ∧ ∀ σ, σ.arity = n → Nonempty (Trees.of τ ≅ Trees.of σ) →
  ¬ Tree.prec σ τ}

/-- The number of Otter trees `|Ott n|`: `1, 1, 1, 2, 3, 6, 11, 23, 47` for `n = 1..9`. -/
theorem ncard_Ott : (Ott 4).ncard = 2 ∧ (Ott 5).ncard = 3 ∧ (Ott 6).ncard = 6 ∧
    (Ott 7).ncard = 11 ∧ (Ott 8).ncard = 23 ∧ (Ott 9).ncard = 47 := sorry

/-- Otter trees are recursively regular. -/
theorem Ott_isRecursivelyRegular (n : ℕ) (τ) (h : τ ∈ Ott n) : Tree.IsRecursivelyRegular τ := sorry

/-! ## §4.8 Groupoids and coinvariants -/

section Coinvariants

variable (k : Type) [Field k]

/-- The coinvariants `V_G = V / ⟨v - g v⟩` of a representation. -/
abbrev coinvariants (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module k V]
    [DistribMulAction G V] : Type :=
  V ⧸ Submodule.span k {w | ∃ (g : G) (v : V), w = v - g • v}

/-- The coinvariants `F_X(X)` of a functor `F : X → Vect_k` on a groupoid at an object `X`:
the quotient of the orbit `⨁_{Y ≅ X} F(Y)` by `⟨w - F(f)(w)⟩`. -/
abbrev groupoidCoinvariants {𝒳 : Type} [Groupoid 𝒳] (F : 𝒳 ⥤ ModuleCat k) (X : 𝒳) : Type :=
  DirectSum {Y : 𝒳 // Nonempty (X ≅ Y)} (fun Y => F.obj Y.1) ⧸
    (Submodule.span k {w | ∃ (Y Z : {Y : 𝒳 // Nonempty (X ≅ Y)})
      (f : Y.1 ⟶ Z.1) (v : F.obj Y.1),
      w = DirectSum.of (fun Y : {Y : 𝒳 // Nonempty (X ≅ Y)} => F.obj Y.1) Y v -
        DirectSum.of (fun Y : {Y : 𝒳 // Nonempty (X ≅ Y)} => F.obj Y.1) Z (F.map f v)})

/-- The automorphism group of `X` acts on `F(X)`. -/
instance {𝒳 : Type} [Groupoid 𝒳] (F : 𝒳 ⥤ ModuleCat k) (X : 𝒳) :
    DistribMulAction (Aut X) (F.obj X) where
  smul g v := F.map g.asIso.hom v
  one_smul v := by
    change F.map (𝟙 X) v = v
    rw [F.map_id]
    rfl
  mul_smul g h v := by
    change F.map (h.asIso.hom ≫ g.asIso.hom) v = F.map g.asIso.hom (F.map h.asIso.hom v)
    rw [F.map_comp]
    rfl
  smul_zero g := map_zero _
  smul_add g v w := map_add _ _ _

/-- **Proposition 4.17.** The inclusion `F(X) ↪ O(X)` induces an isomorphism
`F(X)_{Aut(X)} ≅ F_𝒳(X)`. -/
theorem coinvariants_aut_iso {𝒳 : Type} [Groupoid 𝒳] (F : 𝒳 ⥤ ModuleCat k) (X : 𝒳) :
    Nonempty (coinvariants k (Aut X) (F.obj X) ≃ₗ[k] groupoidCoinvariants k F X) := sorry

end Coinvariants

end MartinPhd

end
end TreesCat

section LieComplex

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 4 — §4.9 The functor `A`, §4.10 The complex `C•(A)` for Lie algebras
-/

open scoped TensorProduct BigOperators
open CategoryTheory

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {k : Type} [Field k]

/-! ## §4.9 The functor `A : Trees → Vect_k` -/

/-- `A(v, τ) = flip_{(v,τ)} : A(τ) → A(flip_v τ)`, the linear map defined recursively by
`id` on the trivial tree, `(-1)^{lr} flip_ε τ(a_{l+1,n} ⊗ a_{1,l})` at the root, and the
induced map on the branch containing `v` otherwise. (Construction deferred in the outline.) -/
def flipMap (A : Mag2 k) (τ : Tree) (v : Word) :
    treeObj A τ →ₗ[k] treeObj A (Tree.flip v τ) := sorry

/-- The functor `A : Trees → Vect_k` extending `τ ↦ A(τ)` to the arrows of `Trees`
(compatibility with (4.11)–(4.13) is the omitted verification). -/
def treesFunctor (A : Mag2 k) : Trees ⥤ ModuleCat k := sorry

/-- `Aut(τ)` acts on `A(τ)` through the functor `A`. -/
instance (A : Mag2 k) (τ : Tree) : DistribMulAction (Aut (Trees.of τ)) (treeObj A τ) := sorry

/-- The functor `Γ_τ` of **Proposition 4.18**, for a recursively regular tree `τ`:
`Γ_τ = id` if `τ` is trivial; `Γ_{τ/λ} ⊗ Γ_{τ/ρ}` if `τ/λ ≠ τ/ρ`; `S²(Γ_{τ/λ})` if
`τ/λ = τ/ρ` with `|τ/λ|` even; `Λ²(Γ_{τ/λ})` if `|τ/λ|` is odd. -/
def Gamma (A : Mag2 k) : Tree → ModuleCat k := sorry

/-- **Proposition 4.18.** For recursively regular `τ`, the identification `A^{⊗|τ|} ≅ A(τ)`
induces an isomorphism `Γ_τ(A) ≅ A(τ)_{Aut(τ)} ≅ A(τ)_{Trees}`. -/
theorem gamma_iso_coinvariants (A : Mag2 k) (τ : Tree) (hτ : τ.IsRecursivelyRegular) :
    Nonempty (Gamma A τ ≃ₗ[k] coinvariants k (Aut (Trees.of τ)) (treeObj A τ)) := sorry

/-! ## §4.10 The complex `C•(A)` -/

/-- The subspace `R_n(A) ⊆ T_n(A)` spanned by `x - flip_{(v,τ)}(x)`, over trees `τ` of arity
`n`, internal vertices `v`, and `x ∈ A(τ)`. -/
def Rn (A : Mag2 k) (n : ℕ) : Submodule k (Tn A n) := sorry

/-- `C_n(A) = T_n(A) / R_n(A)`: the coinvariants, and the chains of the Koszul complex of the
operad `OL` of Lie algebras nilpotent in 2 steps. -/
abbrev Cn (A : Mag2 k) (n : ℕ) : Type := Tn A n ⧸ Rn A n

/-- **Proposition 4.19.** `R_•(A)` is an ideal for juxtaposition: if `x ∈ R_n(A)` and
`y ∈ T_m(A)` then `x ⌣ y` and `y ⌣ x` lie in `R_{n+m}(A)`. -/
theorem juxt_mem_Rn (A : Mag2 k) (n m : ℕ) (x : Tn A n) (hx : x ∈ Rn A n) (y : Tn A m) :
    juxtT A n m x y ∈ Rn A (n + m) ∧ juxtT A m n y x ∈ Rn A (m + n) := sorry

/-- **Theorem 4.20.** If `(A, μ)` is a Lie algebra nilpotent in 2 steps, the differential
`d_n : T_n(A) → T_{n-1}(A)` satisfies `d_n(R_n(A)) ⊆ R_{n-1}(A)`, hence induces a
differential on `C•(A)`.

**Note.** The hypothesis `A : Lie2` (antisymmetry of `μ`) is used
only in degree 2 (the base case `d(R₂) = 0`). -/
theorem dT_mem_Rn (A : Lie2 k) (n : ℕ) (x : Tn A.toMag2 n) (hx : x ∈ Rn A.toMag2 n) :
    dT A.toMag2 n x ∈ Rn A.toMag2 (n - 1) := sorry

/-- The induced differential of `C•(A)`. -/
def dC (A : Lie2 k) (n : ℕ) : Cn A.toMag2 n →ₗ[k] Cn A.toMag2 (n - 1) :=
  Submodule.mapQ _ _ (dT A.toMag2 n) (fun x hx => dT_mem_Rn A n x hx)

/-- The decomposition of `T_n(A)` over Otter trees: `T_n(A) = ⨁_{η ∈ Ott(n)} ⨁_{τ ≅ η} A(τ)`
and `R_n = ⨁_η R_η`; consequently `C_n(A) ≅ ⨁_{η ∈ Ott(n)} A(η)_{Aut(η)}`. -/
theorem Cn_equiv_otter (A : Mag2 k) (n : ℕ) :
    Nonempty (Cn A n ≃ₗ[k] DirectSum (Ott n) fun η =>
      coinvariants k (Aut (Trees.of η.1)) (treeObj A η.1)) := sorry

end MartinPhd

end
end LieComplex
