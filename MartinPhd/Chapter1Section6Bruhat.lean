import Mathlib
import MartinPhd.Chapter1Section5SubspacesFlagVarieties
import MartinPhd.Chapter1Section1FlagsPermutations

/-!
# Chapter 1, Section 1.6 (Bruhat decomposition, parabolics, partial flags, subspaces)

Contents:
* Bruhat
* Count
* DoubleCosets
* Orbits
* Parabolic
* Partial
* Generators
* Partitions
* PermCross
* A simple representation with inverse-invariant character is self-dual
* Subspaces
-/

section Bruhat

/-! Orbit classification and double-coset helpers for Proposition 1.11. -/

open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

section
variable {F : Type} [Field F] [Fintype F]

omit [Fintype F] in
/-- Transporting the basis transports its complete flag. -/
theorem bruhat_smul_jhFlag {n : ℕ} (b : Basis (Fin n) F (Fin n → F))
    (g : GLn F n) : g • jhFlag b = jhFlag (b.map g) :=
  ST.smul_flagOf b g

omit [Fintype F] in
/-- An isomorphism sending each vector of one basis to the corresponding vector of
another basis sends both their flags and their equally reindexed flags to each other. -/
theorem bruhat_basis_pair {n : ℕ} (b b' : Basis (Fin n) F (Fin n → F))
    (σ : Equiv.Perm (Fin n)) :
    ∃ g : GLn F n, g • jhFlag b = jhFlag b' ∧
      g • jhFlag (b.reindex σ.symm) = jhFlag (b'.reindex σ.symm) := by
  let g := b.equiv b' (Equiv.refl (Fin n))
  have hb : b.map g = b' := by
    apply Basis.eq_of_apply_eq
    intro i
    simp [g]
  have hr : (b.reindex σ.symm).map g = b'.reindex σ.symm := by
    apply Basis.eq_of_apply_eq
    intro i
    simp [g]
  exact ⟨g, by rw [bruhat_smul_jhFlag, hb], by rw [bruhat_smul_jhFlag, hr]⟩

omit [Fintype F] in
/-- The distance classifies pairs of complete flags, by choosing the common adapted
bases of Proposition 1.10. -/
theorem bruhat_pair_orbit (n : ℕ) (F₁ G₁ F₂ G₂ : Flag F (Fin n → F))
    (h₁ : F₁.IsComplete) (h₂ : G₁.IsComplete) (h₃ : F₂.IsComplete)
    (h₄ : G₂.IsComplete) :
    (∃ g : GLn F n, g • F₁ = F₂ ∧ g • G₁ = G₂) ↔
      jh n F₁ G₁ = jh n F₂ G₂ := by
  constructor
  · rintro ⟨g, rfl, rfl⟩
    exact (jh_smul n F₁ G₁ g).symm
  · intro he
    have hn : finrank F (Fin n → F) = n := by simp
    obtain ⟨b, hbF, hbG⟩ := (jh_characterization n hn F₁ G₁ h₁ h₂).2.1
    obtain ⟨b', hbF', hbG'⟩ := (jh_characterization n hn F₂ G₂ h₃ h₄).2.1
    rw [← he] at hbG'
    rw [jhFlag_eq_of_adapted b F₁ h₁ hn hbF,
      jhFlag_eq_of_adapted (b.reindex _) G₁ h₂ hn hbG,
      jhFlag_eq_of_adapted b' F₂ h₃ hn hbF',
      jhFlag_eq_of_adapted (b'.reindex _) G₂ h₄ hn hbG']
    exact bruhat_basis_pair b b' _

/-- The standard flag is complete, also in dimension zero. -/
theorem bruhat_std_complete (n : ℕ) : (stdFlag F n).IsComplete := by
  rw [stdFlag_eq_flagOf]
  change (ST.flagOf _).len = _
  rw [ST.len_flagOf]
  simp

omit [Fintype F] in
/-- Transport preserves completeness. -/
theorem bruhat_complete_smul {n : ℕ} (g : GLn F n) (A : Flag F (Fin n → F))
    (hA : A.IsComplete) : (g • A).IsComplete := by
  change (A.map g).len = _
  rw [Flag.len_map]
  exact hA

/-- The explicit double coset, expressed without the definitions in Section 1.6. -/
def bruhatDC {n : ℕ} (g : GLn F n) : Set (GLn F n) :=
  {h | ∃ b₁ ∈ MulAction.stabilizer (GLn F n) (stdFlag F n),
    ∃ b₂ ∈ MulAction.stabilizer (GLn F n) (stdFlag F n), h = b₁ * g * b₂}

/-- A double coset is the fibre of the Weyl distance. -/
theorem bruhatDC_mem_iff {n : ℕ} (g h : GLn F n) :
    h ∈ bruhatDC g ↔
      jh n (stdFlag F n) (g • stdFlag F n) =
        jh n (stdFlag F n) (h • stdFlag F n) := by
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    change b₁ • stdFlag F n = stdFlag F n at hb₁
    change b₂ • stdFlag F n = stdFlag F n at hb₂
    simpa only [mul_smul, hb₁, hb₂] using
      (jh_smul n (stdFlag F n) (g • stdFlag F n) b₁).symm
  · intro he
    obtain ⟨b, hb, hbg⟩ := (bruhat_pair_orbit n _ _ _ _
      (bruhat_std_complete n) (bruhat_complete_smul g _ (bruhat_std_complete n))
      (bruhat_std_complete n) (bruhat_complete_smul h _ (bruhat_std_complete n))).2 he
    refine ⟨b, hb, (b * g)⁻¹ * h, ?_, ?_⟩
    · change ((b * g)⁻¹ * h) • stdFlag F n = stdFlag F n
      rw [mul_smul, ← hbg]
      simpa only [mul_smul] using inv_smul_smul (b * g) (stdFlag F n)
    · simp only [mul_inv_cancel_left]

/-- Equality of double cosets is equality of Weyl distances. -/
theorem bruhatDC_eq_iff {n : ℕ} (g h : GLn F n) :
    bruhatDC g = bruhatDC h ↔
      jh n (stdFlag F n) (g • stdFlag F n) =
        jh n (stdFlag F n) (h • stdFlag F n) := by
  constructor
  · intro he
    have hh : h ∈ bruhatDC h :=
      (bruhatDC_mem_iff h h).2 rfl
    exact (bruhatDC_mem_iff g h).1 (he ▸ hh)
  · intro he
    ext x
    rw [bruhatDC_mem_iff, bruhatDC_mem_iff, he]

/-- The double coset of an element has its Jordan–Hölder permutation as representative. -/
theorem bruhatDC_eq_perm {n : ℕ} (g : GLn F n) :
    bruhatDC g = bruhatDC (permToGL F (jh n (stdFlag F n) (g • stdFlag F n))) := by
  apply (bruhatDC_eq_iff _ _).2
  rw [jh_std_perm]

/-- The permutation labelling an element's Bruhat cell is unique. -/
theorem bruhatDC_existsUnique (n : ℕ) (g : GLn F n) :
    ∃! σ : Equiv.Perm (Fin n), g ∈ bruhatDC (permToGL F σ) := by
  refine ⟨jh n (stdFlag F n) (g • stdFlag F n), ?_, ?_⟩
  · dsimp only
    rw [bruhatDC_mem_iff, jh_std_perm]
  · intro σ hσ
    simpa only [jh_std_perm] using (bruhatDC_mem_iff _ _).1 hσ

end
end MartinPhd

end
end Bruhat

section Count

/-! The multinomial count of Young-subgroup cosets used in Lemma 1.18. -/

noncomputable section
namespace MartinPhd
open scoped BigOperators

/-- The order of a Young subgroup is the product of the block factorials. -/
theorem youngSubgroup_card {n : ℕ} (c : Composition n) :
    Nat.card (youngSubgroup c) = ∏ i, (c.blocksFun i).factorial := by
  obtain ⟨e⟩ := youngSubgroup_equiv c
  rw [Nat.card_congr e.toEquiv, Nat.card_pi]
  simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

/-- The left cosets of the Young subgroup are counted by the multinomial coefficient. -/
theorem youngSubgroup_quotient_card {n : ℕ} (c : Composition n) :
    Nat.card (Equiv.Perm (Fin n) ⧸ youngSubgroup c) =
      Nat.multinomial Finset.univ c.blocksFun := by
  rw [← Subgroup.index_eq_card, Subgroup.index_eq_card_div, youngSubgroup_card]
  simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
    Nat.multinomial, Composition.sum_blocksFun]

end MartinPhd

end
end Count

section DoubleCosets

/-! Elementary double-coset manipulations used in the parabolic Bruhat decomposition. -/

namespace MartinPhd

/-- The explicit double coset for two possibly different subgroups. -/
def twoSidedCoset {G : Type*} [Group G] (B P : Subgroup G) (g : G) : Set G :=
  {x | ∃ b ∈ B, ∃ p ∈ P, x = b * g * p}

section
variable {G W : Type*} [Group G] [Group W]
    (B P : Subgroup G) (hBP : B ≤ P) (r : W →* G) (Y : Subgroup W)

/-- Membership of a representative in its own double coset. -/
theorem mem_twoSidedCoset (g : G) : g ∈ twoSidedCoset B P g := by
  exact ⟨1, B.one_mem, 1, P.one_mem, by simp⟩

/-- Representatives related by the right subgroup have the same double coset. -/
theorem twoSidedCoset_eq_of_inv_mul_mem (g h : G) (hgh : g⁻¹ * h ∈ P) :
    twoSidedCoset B P g = twoSidedCoset B P h := by
  have hrev : h⁻¹ * g ∈ P := by
    simpa only [mul_inv_rev, inv_inv] using P.inv_mem hgh
  have incl (g h : G) (hgh : g⁻¹ * h ∈ P) :
      twoSidedCoset B P h ⊆ twoSidedCoset B P g := by
    rintro x ⟨b, hb, p, hp, rfl⟩
    refine ⟨b, hb, (g⁻¹ * h) * p, P.mul_mem hgh hp, ?_⟩
    simp [mul_assoc]
  exact Set.Subset.antisymm (incl h g hrev) (incl g h hgh)

include hBP in
/-- Borel double-coset coverage induces coverage by right parabolic double cosets. -/
theorem parabolic_coset_coverage
    (hcov : ∀ g : G, ∃ w : W, g ∈ twoSidedCoset B B (r w)) :
    ∀ g : G, ∃ w : W, g ∈ twoSidedCoset B P (r w) := by
  intro g
  obtain ⟨w, b, hb, b', hb', he⟩ := hcov g
  exact ⟨w, b, hb, b', hBP hb', he⟩

/-- The separation property determines equality of parabolic double cosets. -/
theorem parabolic_coset_eq_iff
    (hmem : ∀ w : W, r w ∈ P ↔ w ∈ Y)
    (hsep : ∀ σ τ : W, ∀ b ∈ B, (r σ)⁻¹ * b * r τ ∈ P → σ⁻¹ * τ ∈ Y)
    (σ τ : W) :
    twoSidedCoset B P (r σ) = twoSidedCoset B P (r τ) ↔ σ⁻¹ * τ ∈ Y := by
  constructor
  · intro he
    have ht : r τ ∈ twoSidedCoset B P (r σ) :=
      he ▸ mem_twoSidedCoset B P (r τ)
    obtain ⟨b, hb, p, hp, ht⟩ := ht
    apply hsep σ τ b⁻¹ (B.inv_mem hb)
    have hcan : (r σ)⁻¹ * b⁻¹ * r τ = p := by
      rw [ht]
      group
    rwa [hcan]
  · intro h
    apply twoSidedCoset_eq_of_inv_mul_mem
    simpa only [map_mul, map_inv] using (hmem (σ⁻¹ * τ)).2 h

/-- Membership of one representative in another representative's parabolic double
coset is the Young-subgroup coset relation. -/
theorem parabolic_coset_mem_iff
    (hmem : ∀ w : W, r w ∈ P ↔ w ∈ Y)
    (hsep : ∀ σ τ : W, ∀ b ∈ B, (r σ)⁻¹ * b * r τ ∈ P → σ⁻¹ * τ ∈ Y)
    (σ τ : W) :
    r σ ∈ twoSidedCoset B P (r τ) ↔ σ⁻¹ * τ ∈ Y := by
  constructor
  · rintro ⟨b, hb, p, hp, he⟩
    apply hsep σ τ b hb
    have hcan : (r σ)⁻¹ * b * r τ = p⁻¹ := by
      rw [he]
      group
    rw [hcan]
    exact P.inv_mem hp
  · intro h
    rw [← parabolic_coset_eq_iff B P r Y hmem hsep σ τ] at h
    rw [← h]
    exact mem_twoSidedCoset B P (r σ)

include hBP in
/-- A parabolic is exactly the union of Borel cells whose representative belongs to it. -/
theorem parabolic_eq_union_cells
    (hmem : ∀ w : W, r w ∈ P ↔ w ∈ Y)
    (hcov : ∀ g : G, ∃ w : W, g ∈ twoSidedCoset B B (r w)) :
    (P : Set G) = ⋃ w ∈ Y, twoSidedCoset B B (r w) := by
  ext g
  constructor
  · intro hg
    obtain ⟨w, b, hb, b', hb', he⟩ := hcov g
    have hr : r w ∈ P := by
      have hm := P.mul_mem (P.mul_mem (P.inv_mem (hBP hb)) hg)
        (P.inv_mem (hBP hb'))
      have hc : b⁻¹ * g * b'⁻¹ = r w := by
        rw [he]
        group
      rwa [hc] at hm
    exact Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨(hmem w).1 hr, b, hb, b', hb', he⟩⟩
  · intro hg
    obtain ⟨w, hg⟩ := Set.mem_iUnion.1 hg
    obtain ⟨hw, b, hb, b', hb', rfl⟩ := Set.mem_iUnion.1 hg
    exact P.mul_mem (P.mul_mem (hBP hb) ((hmem w).2 hw)) (hBP hb')

end
end MartinPhd

end DoubleCosets

section Orbits

/-! Double cosets and orbit quotients used in the Schubert-cell count. -/
noncomputable section
namespace MartinPhd

/-- Equality of subgroup orbits on a coset space is double-coset membership. -/
theorem doubleOrbit_eq_iff {G : Type*} [Group G] (B P : Subgroup G) (g h : G) :
    (Quotient.mk'' (g : G ⧸ P) : MulAction.orbitRel.Quotient B (G ⧸ P)) =
      Quotient.mk'' (h : G ⧸ P) ↔ ∃ b ∈ B, ∃ p ∈ P, g = b * h * p := by
  constructor
  · intro he
    obtain ⟨b, hb⟩ := Quotient.exact he
    change ((b.1 * h : G) : G ⧸ P) = (g : G ⧸ P) at hb
    have hp := QuotientGroup.leftRel_apply.mp (Quotient.exact hb)
    exact ⟨b.1, b.2, (b.1 * h)⁻¹ * g, hp, (mul_inv_cancel_left (b.1 * h) g).symm⟩
  · rintro ⟨b, hb, p, hp, rfl⟩
    apply Quotient.sound
    refine ⟨⟨b, hb⟩, ?_⟩
    change ((b * h : G) : G ⧸ P) = ((b * h * p : G) : G ⧸ P)
    exact Quotient.sound' ((QuotientGroup.leftRel_apply (s := P)).2
      (by simpa only [inv_mul_cancel_left] using hp))

/-- A family of double-coset representatives with precisely the left-coset relation
induces an equivalence of the corresponding quotient spaces. -/
theorem doubleOrbit_equiv {G W : Type*} [Group G] [Group W]
    (B P : Subgroup G) (Y : Subgroup W) (r : W → G)
    (hcover : ∀ g : G, ∃ w, ∃ b ∈ B, ∃ p ∈ P, g = b * r w * p)
    (hrel : ∀ v w : W,
      (∃ b ∈ B, ∃ p ∈ P, r v = b * r w * p) ↔ v⁻¹ * w ∈ Y) :
    Nonempty (W ⧸ Y ≃ MulAction.orbitRel.Quotient B (G ⧸ P)) := by
  let f : W ⧸ Y → MulAction.orbitRel.Quotient B (G ⧸ P) :=
    Quotient.lift (fun w => Quotient.mk'' (r w : G ⧸ P)) (by
      intro v w hvw
      apply (doubleOrbit_eq_iff B P _ _).2
      exact (hrel v w).2 (QuotientGroup.leftRel_apply.mp hvw))
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro x y
    induction x using Quotient.inductionOn with
    | h v =>
      induction y using Quotient.inductionOn with
      | h w =>
        intro hvw
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        exact (hrel v w).1 ((doubleOrbit_eq_iff B P _ _).1 hvw)
  · intro x
    induction x using Quotient.inductionOn with
    | h q =>
      induction q using Quotient.inductionOn with
      | h g =>
        obtain ⟨w, b, hb, p, hp, hg⟩ := hcover g
        refine ⟨w, ?_⟩
        exact ((doubleOrbit_eq_iff B P g (r w)).2 ⟨b, hb, p, hp, hg⟩).symm

end MartinPhd

end
end Orbits

section Parabolic

/-! Order properties of the standard parabolic stabilizers in Lemma 1.13. -/

open Module

noncomputable section
namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable (F : Type) [Field F] [Fintype F]

/-- The standard Borel stabilizes every standard partial flag. -/
theorem stdFlag_stabilizer_le {n : ℕ} (c : Composition n) :
    MulAction.stabilizer (GLn F n) (stdFlag F n) ≤
      MulAction.stabilizer (GLn F n) (stdFlagOfType F c) :=
  (Flag.stabilizer_le_iff _ _).2 (stdFlagOfType_le_stdFlag F c)

/-- The stabilizers of standard partial flags reverse and reflect refinement. -/
theorem stdFlagOfType_stabilizer_le_iff {n : ℕ} (c c' : Composition n) :
    MulAction.stabilizer (GLn F n) (stdFlagOfType F c') ≤
      MulAction.stabilizer (GLn F n) (stdFlagOfType F c) ↔ Composition.Refines c c' := by
  rw [Flag.stabilizer_le_iff, stdFlagOfType_le_iff]

omit [Fintype F] in
/-- The standard partial flag determines its composition. -/
theorem stdFlagOfType_injective (n : ℕ) : Function.Injective (stdFlagOfType F (n := n)) := by
  intro c c' h
  apply (compositionEquiv n).injective
  apply CompositionAsSet.ext
  exact Finset.Subset.antisymm
    ((stdFlagOfType_le_iff F c c').1 (fun A hA => h ▸ hA))
    ((stdFlagOfType_le_iff F c' c).1 (fun A hA => h.symm ▸ hA))

/-- Different standard partial flags have different stabilizers. -/
theorem stdFlagOfType_stabilizer_injective (n : ℕ) :
    Function.Injective (fun c : Composition n =>
      MulAction.stabilizer (GLn F n) (stdFlagOfType F c)) := by
  intro c c' h
  exact stdFlagOfType_injective F n ((Flag.eq_iff_stabilizer_eq _ _).2 h)

omit [Fintype F] in
/-- Membership in a standard partial flag stabilizer is equivalent to fixing its
standard boundary subspaces individually. -/
theorem mem_stdFlagOfType_stabilizer_iff {n : ℕ} (c : Composition n) (g : GLn F n) :
    g ∈ MulAction.stabilizer (GLn F n) (stdFlagOfType F c) ↔
      ∀ i ∈ c.boundaries, (stdSpan F n i.val).map g.toLinearMap = stdSpan F n i.val := by
  constructor
  · intro hg i hi
    exact Flag.fix_of_smul_eq hg (Finset.mem_image.2 ⟨i, hi, rfl⟩)
  · intro h
    change (stdFlagOfType F c).map g = stdFlagOfType F c
    apply Flag.ext
    change ((stdFlagOfType F c).carrier.image (Submodule.map g.toLinearMap)) =
      (stdFlagOfType F c).carrier
    rw [show (stdFlagOfType F c).carrier.image (Submodule.map g.toLinearMap) =
        (stdFlagOfType F c).carrier.image id from Finset.image_congr (by
      intro A hA
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hA
      exact h i hi)]
    exact Finset.image_id

omit [Fintype F] in
/-- The standard subspaces fixed by a subgroup form the finest standard partial
flag stabilized by it. This is the maximal-refinement choice in the proof of Lemma 1.13. -/
theorem exists_finest_standard_fixedFlag {n : ℕ} (P : Subgroup (GLn F n)) :
    ∃ c : Composition n, ∀ d : Composition n,
      P ≤ MulAction.stabilizer (GLn F n) (stdFlagOfType F d) ↔ Composition.Refines d c := by
  let C : CompositionAsSet n :=
    { boundaries := Finset.univ.filter fun i =>
        ∀ g ∈ P, (stdSpan F n i.val).map g.toLinearMap = stdSpan F n i.val
      zero_mem := by simp [stdSpan_zero]
      getLast_mem := by simp [stdSpan_top] }
  let c := (compositionEquiv n).symm C
  have hc : c.boundaries = C.boundaries :=
    congrArg CompositionAsSet.boundaries ((compositionEquiv n).apply_symm_apply C)
  refine ⟨c, fun d => ?_⟩
  change (∀ g ∈ P, g ∈ MulAction.stabilizer (GLn F n) (stdFlagOfType F d)) ↔ _
  simp only [mem_stdFlagOfType_stabilizer_iff]
  change (∀ g ∈ P, ∀ i ∈ d.boundaries,
    (stdSpan F n i.val).map g.toLinearMap = stdSpan F n i.val) ↔ d.boundaries ⊆ c.boundaries
  rw [hc]
  constructor
  · intro h i hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun g hg => h g hg i hi⟩
  · intro h g hg i hi
    exact (Finset.mem_filter.1 (h hi)).2 g hg

/-- A subgroup containing the standard Borel contains an element exactly when
it contains the permutation representative of its Bruhat double coset. -/
theorem subgroup_mem_iff_bruhat_perm {n : ℕ} (P : Subgroup (GLn F n))
    (hP : MulAction.stabilizer (GLn F n) (stdFlag F n) ≤ P) (g : GLn F n) :
    g ∈ P ↔ permToGL F (jh n (stdFlag F n) (g • stdFlag F n)) ∈ P := by
  let σ := jh n (stdFlag F n) (g • stdFlag F n)
  have hg : g ∈ bruhatDC (permToGL F σ) := by
    rw [bruhatDC_mem_iff, jh_std_perm]
  obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hg
  constructor
  · intro hgP
    have he' : permToGL F σ = b₁⁻¹ * g * b₂⁻¹ := by
      calc permToGL F σ = b₁⁻¹ * (b₁ * permToGL F σ * b₂) * b₂⁻¹ := by group
        _ = b₁⁻¹ * g * b₂⁻¹ := by rw [← he]
    rw [he']
    exact P.mul_mem (P.mul_mem (P.inv_mem (hP hb₁)) hgP) (P.inv_mem (hP hb₂))
  · intro hσ
    rw [he]
    exact P.mul_mem (P.mul_mem (hP hb₁) hσ) (hP hb₂)

/-- The permutation representatives contained in a subgroup form a subgroup of
`Sₙ`. -/
def parabolicWeylSubgroup {n : ℕ} (P : Subgroup (GLn F n)) :
    Subgroup (Equiv.Perm (Fin n)) :=
  P.comap
    { toFun := permToGL F
      map_one' := by ext v i; rfl
      map_mul' := permToGL_mul F }

end MartinPhd

end
end Parabolic

section Partial

/-! Coordinate arguments for §1.6, Lemmas 1.16–1.17. -/
open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

variable (F : Type) [Field F] [Fintype F]

omit [Fintype F] in
theorem partial_mem_stdSpan {n d : ℕ} (v : Fin n → F) :
    v ∈ stdSpan F n d ↔ ∀ j : Fin n, d ≤ j.val → v j = 0 := by
  have he : Set.range (fun j : {j : Fin n // j.val < d} => Pi.single (j : Fin n) (1 : F)) =
      (Pi.basisFun F (Fin n)) '' {j : Fin n | j.val < d} := by
    ext v
    simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq, Pi.basisFun_apply]
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩; exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
  rw [stdSpan, he, (Pi.basisFun F (Fin n)).mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Pi.basisFun_repr,
    Set.mem_ofPred_eq]
  constructor
  · intro h j hj
    by_contra hv
    exact (not_lt_of_ge hj) (h j hv)
  · intro h j hj
    by_contra hd
    exact hj (h j (by omega))

omit [Fintype F] in
theorem partial_single_mem_stdSpan {n d : ℕ} (i : Fin n) :
    (Pi.single i (1 : F) : Fin n → F) ∈ stdSpan F n d ↔ i.val < d := by
  rw [partial_mem_stdSpan]
  constructor
  · intro h
    by_contra hi
    have := h i (by omega)
    simp at this
  · intro hi j hj
    have : j ≠ i := by intro h; subst j; omega
    simp [Pi.single_eq_of_ne this]

omit [Fintype F] in
theorem partial_borel_diagonal_ne_zero {n : ℕ} (b : GLn F n)
    (hb : b ∈ MulAction.stabilizer (GLn F n) (stdFlag F n)) (i : Fin n) :
    b (Pi.single i 1) i ≠ 0 := by
  have hmem (d : ℕ) (hd : d ≤ n) : stdSpan F n d ∈ (stdFlag F n).carrier :=
    Finset.mem_image.mpr ⟨d, Finset.mem_range.mpr (by omega), rfl⟩
  have hfix (d : ℕ) (hd : d ≤ n) :
      (stdSpan F n d).map b.toLinearMap = stdSpan F n d :=
    Flag.fix_of_smul_eq hb (hmem d hd)
  have he : (Pi.single i (1 : F) : Fin n → F) ∈ stdSpan F n (i.val + 1) :=
    (partial_single_mem_stdSpan F i).2 (by omega)
  have hbe : b (Pi.single i 1) ∈ stdSpan F n (i.val + 1) := by
    rw [← hfix (i.val + 1) (by omega)]
    exact Submodule.mem_map.mpr ⟨_, he, rfl⟩
  intro hz
  have hbei : b (Pi.single i 1) ∈ stdSpan F n i.val := by
    rw [partial_mem_stdSpan] at hbe ⊢
    intro j hj
    rcases eq_or_lt_of_le hj with hh | hh
    · have : j = i := Fin.ext hh.symm
      simpa [this] using hz
    · exact hbe j (by omega)
  rw [← hfix i.val (by omega)] at hbei
  obtain ⟨v, hv, heq⟩ := Submodule.mem_map.mp hbei
  have hvi : v = Pi.single i 1 := b.injective heq
  rw [hvi, partial_single_mem_stdSpan] at hv
  omega

omit [Fintype F] in
private theorem partial_sizeUpTo_mem {n : ℕ} (c : Composition n) (r : ℕ) (hr : r ≤ c.length) :
    stdSpan F n (c.sizeUpTo r) ∈ (stdFlagOfType F c).carrier := by
  obtain ⟨hG, h0, hn, heq⟩ := stdFlagOfType_eq_red F c
  rw [heq]
  exact Finset.mem_image.mpr ⟨⟨r, by omega⟩, Finset.mem_univ _, rfl⟩

private theorem partial_young_of_prefix {n : ℕ} (c : Composition n) (π : Equiv.Perm (Fin n))
    (h : ∀ r ≤ c.length, ∀ i : Fin n, i.val < c.sizeUpTo r → (π i).val < c.sizeUpTo r) :
    π ∈ youngSubgroup c := by
  have he (r : ℕ) (hr : r ≤ c.length) (i : Fin n) :
      (π i).val < c.sizeUpTo r ↔ i.val < c.sizeUpTo r := by
    let s : Finset (Fin n) := Finset.univ.filter (fun i => i.val < c.sizeUpTo r)
    have hsub : s.map π.toEmbedding ⊆ s := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h r hr j (Finset.mem_filter.mp hj).2⟩
    have heq : s.map π.toEmbedding = s := Finset.eq_of_subset_of_card_le hsub (by simp)
    constructor
    · intro hi
      have hx : π i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [← heq] at hx
      obtain ⟨j, hj, hij⟩ := Finset.mem_map.mp hx
      have : j = i := π.injective hij
      simpa [this] using (Finset.mem_filter.mp hj).2
    · exact h r hr i
  rw [mem_youngSubgroup_iff]
  intro i
  apply (mem_stdBlock_iff c (c.index i) (π i)).mp
  simp only [stdBlock, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · have hx := c.sizeUpTo_index_le i
    by_contra hbad
    have hx' := (he (c.index i).val (by omega) i).mp (by omega)
    omega
  · exact (he ((c.index i).val + 1) (by omega) i).mpr (c.lt_sizeUpTo_index_succ i)

/-- The nonzero diagonal coefficient of an upper triangular transformation survives
permutation of its rows. This is the coordinate argument of Lemma 1.17. -/
theorem partial_bruhat_young {n : ℕ} (c : Composition n) (σ τ : Equiv.Perm (Fin n))
    (b : GLn F n) (hb : b ∈ MulAction.stabilizer (GLn F n) (stdFlag F n))
    (hp : (permToGL F σ)⁻¹ * b * permToGL F τ ∈
      MulAction.stabilizer (GLn F n) (stdFlagOfType F c)) :
    σ⁻¹ * τ ∈ youngSubgroup c := by
  apply partial_young_of_prefix c (σ⁻¹ * τ)
  intro r hr i hi
  let p := (permToGL F σ)⁻¹ * b * permToGL F τ
  have hfix : (stdSpan F n (c.sizeUpTo r)).map p.toLinearMap =
      stdSpan F n (c.sizeUpTo r) := Flag.fix_of_smul_eq hp (partial_sizeUpTo_mem F c r hr)
  have hm : p (Pi.single i 1) ∈ stdSpan F n (c.sizeUpTo r) := by
    rw [← hfix]
    exact Submodule.mem_map.mpr ⟨_, (partial_single_mem_stdSpan F i).mpr hi, rfl⟩
  have hdiag := partial_borel_diagonal_ne_zero F b hb (τ i)
  by_contra hbad
  have hz := (partial_mem_stdSpan F _).mp hm ((σ⁻¹ * τ) i) (by omega)
  apply hdiag
  change ((permToGL F σ).symm (b (permToGL F τ (Pi.single i 1)))) ((σ⁻¹ * τ) i) = 0 at hz
  rw [permToGL_single] at hz
  simpa [permToGL, LinearEquiv.funCongrLeft_apply, Equiv.Perm.mul_apply] using hz

/-- A permutation matrix fixes the standard partial flag precisely when it preserves
its ordered blocks, as used at the end of the thesis's proof of Lemma 1.16. -/
theorem partial_perm_stabilizer_iff {n : ℕ} (c : Composition n) (σ : Equiv.Perm (Fin n)) :
    permToGL F σ ∈ MulAction.stabilizer (GLn F n) (stdFlagOfType F c) ↔
      σ ∈ youngSubgroup c := by
  constructor
  · intro h
    have hone : permToGL F (1 : Equiv.Perm (Fin n)) = 1 := by ext v j; rfl
    have hp := partial_bruhat_young F c 1 σ 1 (by simp) (by simpa [hone] using h)
    simpa using hp
  · intro hσ
    have hi := (mem_youngSubgroup_iff c σ).mp hσ
    have hprefix (r : ℕ) (hr : r ≤ c.length) (i : Fin n) (hx : i.val < c.sizeUpTo r) :
        (σ i).val < c.sizeUpTo r := by
      have hindex : (c.index i).val < r := by
        by_contra hh
        have hm := c.monotone_sizeUpTo (show r ≤ (c.index i).val by omega)
        have hl := c.sizeUpTo_index_le i
        omega
      have hm := c.monotone_sizeUpTo (show (c.index i).val + 1 ≤ r by omega)
      have hl := c.lt_sizeUpTo_index_succ (σ i)
      rw [hi i] at hl
      exact lt_of_lt_of_le hl hm
    have hfix (r : ℕ) (hr : r ≤ c.length) :
        (stdSpan F n (c.sizeUpTo r)).map (permToGL F σ).toLinearMap =
          stdSpan F n (c.sizeUpTo r) := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.map_le_iff_le_comap, stdSpan, Submodule.span_le]
        rintro v ⟨⟨i, hx⟩, rfl⟩
        change permToGL F σ (Pi.single i 1) ∈ stdSpan F n (c.sizeUpTo r)
        rw [permToGL_single, partial_single_mem_stdSpan]
        exact hprefix r hr i hx
      · exact LinearEquiv.finrank_map_eq _ _
    change (stdFlagOfType F c).map (permToGL F σ) = stdFlagOfType F c
    apply Flag.ext
    obtain ⟨hG, h0, hn, heq⟩ := stdFlagOfType_eq_red F c
    have hmem : ∀ A ∈ (stdFlagOfType F c).carrier,
        A.map (permToGL F σ).toLinearMap = A := by
      intro A hA
      rw [heq] at hA
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hA
      exact hfix r.val (by omega)
    exact (Finset.image_congr (g := id) hmem).trans Finset.image_id

end MartinPhd

end
end Partial

section Generators

/-! Elementary generators for the classification of standard parabolic subgroups. -/
open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable (F : Type) [Field F] [Fintype F]

def parabolicElementary {n : ℕ} (i j : Fin n) (hij : i ≠ j) (t : F) : GLn F n :=
  LinearEquiv.transvection (f := LinearMap.proj j) (v := Pi.single i t) (by
    simp [LinearMap.proj_apply, Pi.single_eq_of_ne (Ne.symm hij)])

omit [Fintype F] in
theorem parabolicElementary_apply {n : ℕ} (i j : Fin n) (hij : i ≠ j) (t : F)
    (v : Fin n → F) (k : Fin n) :
    parabolicElementary F i j hij t v k = v k + v j * ((Pi.single i t : Fin n → F) k) := by
  rfl

omit [Fintype F] in
private theorem parabolic_upper_mem_borel {n : ℕ} (g : GLn F n)
    (h : ∀ d ≤ n, ∀ x ∈ stdSpan F n d, g x ∈ stdSpan F n d) :
    g ∈ MulAction.stabilizer (GLn F n) (stdFlag F n) := by
  have hf (d : ℕ) (hd : d ≤ n) : (stdSpan F n d).map g.toLinearMap = stdSpan F n d := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      exact h d hd x hx
    · exact LinearEquiv.finrank_map_eq _ _
  change (stdFlag F n).map g = stdFlag F n
  apply Flag.ext
  have hm : ∀ A ∈ (stdFlag F n).carrier, A.map g.toLinearMap = A := by
    intro A hA
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hA
    exact hf d (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))
  exact (Finset.image_congr (g := id) hm).trans Finset.image_id

omit [Fintype F] in
theorem parabolicElementary_upper {n : ℕ} (i j : Fin n) (hij : i < j) (t : F) :
    parabolicElementary F i j (ne_of_lt hij) t ∈
      MulAction.stabilizer (GLn F n) (stdFlag F n) := by
  apply parabolic_upper_mem_borel F
  intro d hd x hx
  rw [partial_mem_stdSpan] at hx ⊢
  intro k hk
  rw [parabolicElementary_apply, hx k hk, zero_add]
  by_cases hki : k = i
  · subst k
    rw [hx j (by omega), zero_mul]
  · simp [Pi.single_eq_of_ne hki]

private def parabolicSign {n : ℕ} (j : Fin n) : GLn F n :=
  LinearEquiv.piCongrRight (fun k : Fin n =>
    if k = j then (LinearEquiv.neg F : F ≃ₗ[F] F) else LinearEquiv.refl F F)

omit [Fintype F] in
private theorem parabolicSign_apply {n : ℕ} (j k : Fin n) (v : Fin n → F) :
    parabolicSign F j v k = if k = j then -v k else v k := by
  by_cases hk : k = j <;> simp [parabolicSign, hk]

omit [Fintype F] in
private theorem parabolicSign_mem_borel {n : ℕ} (j : Fin n) :
    parabolicSign F j ∈ MulAction.stabilizer (GLn F n) (stdFlag F n) := by
  apply parabolic_upper_mem_borel F
  intro d hd x hx
  rw [partial_mem_stdSpan] at hx ⊢
  intro k hk
  simp [parabolicSign_apply, hx k hk]

omit [Fintype F] in
private theorem parabolicElementary_swap_factor {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    permToGL F (Equiv.swap i j) = parabolicSign F j *
      parabolicElementary F i j hij 1 * parabolicElementary F j i hij.symm (-1) *
        parabolicElementary F i j hij 1 := by
  ext v k
  by_cases hki : k = i
  · subst k
    simp [LinearEquiv.mul_apply, parabolicSign_apply, parabolicElementary_apply,
      permToGL, LinearEquiv.funCongrLeft_apply, hij, hij.symm]
  · by_cases hkj : k = j
    · subst k
      simp [LinearEquiv.mul_apply, parabolicSign_apply, parabolicElementary_apply,
        permToGL, LinearEquiv.funCongrLeft_apply, hij.symm]
    · simp [LinearEquiv.mul_apply, parabolicSign_apply, parabolicElementary_apply,
        permToGL, LinearEquiv.funCongrLeft_apply, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

omit [Fintype F] in
private theorem parabolicElementary_conj {n : ℕ} (π : Equiv.Perm (Fin n))
    (i j : Fin n) (hij : i ≠ j) (t : F) :
    permToGL F π * parabolicElementary F i j hij t * (permToGL F π)⁻¹ =
      parabolicElementary F (π i) (π j) (π.injective.ne hij) t := by
  ext v k
  simp [LinearEquiv.mul_apply, parabolicElementary_apply, permToGL,
    LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]

omit [Fintype F] in
/-- An inversion of a permutation in a subgroup containing the standard Borel
supplies the transposition of the inverted images. -/
theorem parabolic_inversion_swap {n : ℕ} (P : Subgroup (GLn F n))
    (hP : MulAction.stabilizer (GLn F n) (stdFlag F n) ≤ P)
    (π : Equiv.Perm (Fin n)) (hπ : permToGL F π ∈ P)
    (a b : Fin n) (hab : a < b) (hinv : π b < π a) :
    permToGL F (Equiv.swap (π b) (π a)) ∈ P := by
  have hel : parabolicElementary F (π a) (π b) (ne_of_gt hinv) (-1) ∈ P := by
    have he := P.mul_mem (P.mul_mem hπ (hP (parabolicElementary_upper F a b hab (-1))))
      (P.inv_mem hπ)
    rw [parabolicElementary_conj] at he
    exact he
  rw [parabolicElementary_swap_factor F (π b) (π a) (ne_of_lt hinv)]
  exact P.mul_mem (P.mul_mem (P.mul_mem (hP (parabolicSign_mem_borel F (π a)))
    (hP (parabolicElementary_upper F (π b) (π a) hinv 1))) hel)
      (hP (parabolicElementary_upper F (π b) (π a) hinv 1))

end MartinPhd

end
end Generators

section Partitions

/-! Orbit–stabilizer helpers for ordered partitions (§1.6, Lemma 1.15). -/
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

private theorem partition_mem_exists {n : ℕ} {c : Composition n}
    (P : OrderedPartition (Fin n) c) (x : Fin n) : ∃ i, x ∈ P.block i := by
  have h := Finset.mem_univ x
  rw [← P.cover] at h
  simpa using h

private def partitionIndex {n : ℕ} {c : Composition n}
    (P : OrderedPartition (Fin n) c) (x : Fin n) : Fin c.length :=
  Classical.choose (partition_mem_exists P x)

private theorem partitionIndex_mem {n : ℕ} {c : Composition n}
    (P : OrderedPartition (Fin n) c) (x : Fin n) : x ∈ P.block (partitionIndex P x) :=
  Classical.choose_spec (partition_mem_exists P x)

private theorem partitionIndex_eq {n : ℕ} {c : Composition n}
    (P : OrderedPartition (Fin n) c) {x : Fin n} {i : Fin c.length}
    (h : x ∈ P.block i) : partitionIndex P x = i := by
  by_contra hn
  exact Finset.disjoint_left.mp (P.disjoint hn) (partitionIndex_mem P x) h

private def partitionCoordinates {n : ℕ} {c : Composition n}
    (P : OrderedPartition (Fin n) c) :
    Fin n ≃ Σ i, {x : Fin n // x ∈ P.block i} where
  toFun x := ⟨partitionIndex P x, x, partitionIndex_mem P x⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨i, x, hx⟩
    dsimp
    have hi := partitionIndex_eq P hx
    cases hi
    rfl

/-- Ordered partitions with the same block sizes lie in one permutation orbit.
This supplies the transitivity used in the thesis's proof of Lemma 1.15. -/
theorem orderedPartition_transitive {n : ℕ} (c : Composition n)
    (P Q : OrderedPartition (Fin n) c) : ∃ σ : Equiv.Perm (Fin n), σ • P = Q := by
  let e : (i : Fin c.length) → {x : Fin n // x ∈ P.block i} ≃
      {x : Fin n // x ∈ Q.block i} := fun i =>
    Fintype.equivOfCardEq (by simp only [Fintype.card_coe, P.card_block, Q.card_block])
  let σ : Equiv.Perm (Fin n) :=
    (partitionCoordinates P).trans ((Equiv.sigmaCongrRight e).trans (partitionCoordinates Q).symm)
  have hm (i : Fin c.length) (x : Fin n) (hx : x ∈ P.block i) : σ x ∈ Q.block i := by
    have hi := partitionIndex_eq P hx
    change (e (partitionIndex P x) ⟨x, partitionIndex_mem P x⟩).1 ∈ Q.block i
    subst i
    exact (e (partitionIndex P x) ⟨x, partitionIndex_mem P x⟩).2
  refine ⟨σ, ?_⟩
  ext i x
  change x ∈ (P.block i).map σ.toEmbedding ↔ x ∈ Q.block i
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hm i y hy
  · intro hx
    refine Finset.mem_map.mpr ⟨σ.symm x, ?_, σ.apply_symm_apply x⟩
    have h := hm (partitionIndex P (σ.symm x)) (σ.symm x) (partitionIndex_mem P _)
    rw [σ.apply_symm_apply] at h
    have hi : partitionIndex P (σ.symm x) = i := by
      by_contra hn
      exact Finset.disjoint_left.mp (Q.disjoint hn) h hx
    simpa only [hi] using partitionIndex_mem P (σ.symm x)

end MartinPhd

end
end Partitions

section PermCross

open Equiv

namespace MartinPhd

/-- If a permutation `σ` maps some index below `m` to an index at least `m`,
then there exists an inversion `i < j` with `σ j < σ i` crossing `m`,
i.e. `(σ j).val < m` and `m ≤ (σ i).val`. -/
theorem perm_cross {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ)
    (h : ∃ i : Fin n, i.val < m ∧ m ≤ (σ i).val) :
    ∃ i j : Fin n, i < j ∧ σ j < σ i ∧ (σ j).val < m ∧ m ≤ (σ i).val := by
  obtain ⟨i, hi_lt, hi_le⟩ := h
  have hj : ∃ j : Fin n, m ≤ j.val ∧ (σ j).val < m := by
    by_contra! h_all
    let S : Finset (Fin n) := Finset.univ.filter (fun j => m ≤ j.val)
    have h_sub : S.image σ ⊆ S := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, h_all y hy.2⟩
    have h_card : (S.image σ).card = S.card :=
      Finset.card_image_of_injective S σ.injective
    have h_eq : S.image σ = S :=
      Finset.eq_of_subset_of_card_le h_sub (le_of_eq h_card.symm)
    have h_σi_in : σ i ∈ S := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hi_le⟩
    have h_σi_in_img : σ i ∈ S.image σ := by
      rw [h_eq]
      exact h_σi_in
    rw [Finset.mem_image] at h_σi_in_img
    obtain ⟨k, hk, hk_eq⟩ := h_σi_in_img
    have hk_i : k = i := σ.injective hk_eq
    subst hk_i
    rw [Finset.mem_filter] at hk
    omega
  obtain ⟨j, hj_ge, hj_lt⟩ := hj
  refine ⟨i, j, ?_, ?_, hj_lt, hi_le⟩
  · exact Fin.lt_def.2 (by omega)
  · exact Fin.lt_def.2 (by omega)

end MartinPhd

end PermCross

section SelfDualAbs

/-!
## A simple representation with inverse-invariant character is self-dual

Abstract lemma (characteristic `0`, finite group): if `ρ` is a simple (no proper nonzero
subrepresentation), nonzero, finite-dimensional representation with `χ(g⁻¹) = χ(g)` for all `g`,
then `ρ ≅ ρ*`. Used for the Steinberg module (Lemma 1.22).
-/

open Module Representation
noncomputable section
namespace MartinPhd

theorem selfDual_of_simple_char {G k V : Type*} [Group G] [Finite G] [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k G V)
    (hsimple : ∀ W : Submodule k V, (∀ g, W.map (ρ g) ≤ W) → W = ⊥ ∨ W = ⊤)
    (hchar : ∀ g, ρ.character g⁻¹ = ρ.character g) : Nonempty (ρ.Equiv ρ.dual) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : k) := invertibleOfNonzero (by
    have : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast this.ne')
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ.dual
  have h2 := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  simp only [char_dual, hchar] at h1 h2
  have hdim : finrank k (IntertwiningMap ρ ρ.dual) = finrank k (IntertwiningMap ρ ρ) := by
    exact_mod_cast h1.symm.trans h2
  haveI : Module.Finite k (IntertwiningMap ρ ρ) :=
    Module.Finite.equiv (invariantsEquivIntertwiningMap ρ ρ)
  haveI : Module.Finite k (IntertwiningMap ρ ρ.dual) :=
    Module.Finite.equiv (invariantsEquivIntertwiningMap ρ ρ.dual)
  have hpos : 0 < finrank k (IntertwiningMap ρ ρ) := by
    haveI : Nontrivial (IntertwiningMap ρ ρ) := ⟨⟨IntertwiningMap.id ρ, 0, fun h => by
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have := congrArg (fun f : IntertwiningMap ρ ρ => f v) h
      exact hv (by simpa using this)⟩⟩
    exact Module.finrank_pos
  have hpos' : 0 < finrank k (IntertwiningMap ρ ρ.dual) := hdim ▸ hpos
  obtain ⟨f, hf⟩ := Module.finrank_pos_iff_exists_ne_zero (R := k) (M := IntertwiningMap ρ ρ.dual) |>.1 hpos'
  have hinj : Function.Injective f.toLinearMap := by
    rw [← LinearMap.ker_eq_bot]
    rcases hsimple (LinearMap.ker f.toLinearMap) (fun g => by
      rintro _ ⟨v, hv, rfl⟩
      have hv' : f.toLinearMap v = 0 := hv
      show f.toLinearMap (ρ g v) = 0
      have := LinearMap.congr_fun (f.isIntertwining' g) v
      simp only [LinearMap.comp_apply] at this
      rw [this, hv', map_zero]) with h | h
    · exact h
    · exfalso
      apply hf
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      have : v ∈ LinearMap.ker f.toLinearMap := by rw [h]; trivial
      exact this
  have hbij : Function.Bijective f.toLinearMap := by
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := k) (V := V)).symm).1 hinj
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective f.toLinearMap hbij) f.isIntertwining'⟩

end MartinPhd

end
end SelfDualAbs

section Subspaces

open Module FiniteDimensional

variable {F : Type*} [Field F] [Fintype F]

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-- Cardinality of the dual space of a finite-dimensional vector space over a finite field. -/
theorem card_dual_eq_pow {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M] :
    Nat.card (M →ₗ[F] F) = (Fintype.card F) ^ (finrank F M) := by
  let b := finBasis F M
  have e := b.dualBasis.equivFun.toEquiv
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin, Fintype.card_eq_nat_card]

/-- Submodules of dimension `d` are in bijection under a linear equivalence. -/
def submoduleEquivOfLinearEquiv {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (e : V ≃ₗ[F] W) (d : ℕ) :
    {S : Submodule F V // finrank F S = d} ≃ {S : Submodule F W // finrank F S = d} where
  toFun S := ⟨S.1.map e.toLinearMap, by rw [LinearEquiv.finrank_map_eq, S.2]⟩
  invFun S := ⟨S.1.map e.symm.toLinearMap, by rw [LinearEquiv.finrank_map_eq, S.2]⟩
  left_inv S := Subtype.ext (by ext x; simp)
  right_inv S := Subtype.ext (by ext x; simp)

theorem card_submodule_eq_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (e : V ≃ₗ[F] W) (d : ℕ) :
    Nat.card {S : Submodule F V // finrank F S = d} =
      Nat.card {S : Submodule F W // finrank F S = d} :=
  Nat.card_congr (submoduleEquivOfLinearEquiv e d)

def submoduleProdEquivProd {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (p : Submodule R M) (q : Submodule R N) :
    Submodule.prod p q ≃ₗ[R] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_submodule_prod {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (p : Submodule F F) (q : Submodule F W) :
    finrank F (Submodule.prod p q) = finrank F p + finrank F q := by
  have e := submoduleProdEquivProd p q
  rw [e.finrank_eq, Module.finrank_prod]

theorem finrank_top_self : finrank F (⊤ : Submodule F F) = 1 := by
  rw [finrank_top, finrank_self]

/-- The graph of a linear functional on a subspace `W' ≤ W` as a submodule of `F × W`. -/
def graphSubmodule {W : Type*} [AddCommGroup W] [Module F W]
    (W' : Submodule F W) (f : W' →ₗ[F] F) : Submodule F (F × W) :=
  LinearMap.range (LinearMap.prod f W'.subtype)

theorem one_not_mem_graphSubmodule {W : Type*} [AddCommGroup W] [Module F W]
    (W' : Submodule F W) (f : W' →ₗ[F] F) :
    (1, (0 : W)) ∉ graphSubmodule W' f := by
  intro h
  rcases h with ⟨w, hw⟩
  have h2 : w.1 = 0 := congrArg Prod.snd hw
  have hw0 : w = 0 := Subtype.ext h2
  have h1 : f w = 1 := congrArg Prod.fst hw
  rw [hw0, map_zero] at h1
  exact zero_ne_one h1

theorem finrank_graphSubmodule {W : Type*} [AddCommGroup W] [Module F W]
    (W' : Submodule F W) (f : W' →ₗ[F] F) :
    finrank F (graphSubmodule W' f) = finrank F W' := by
  apply LinearMap.finrank_range_of_inj
  intro x y hxy
  have h2 : x.1 = y.1 := congrArg Prod.snd hxy
  exact Subtype.ext h2

theorem graphSubmodule_map_snd {W : Type*} [AddCommGroup W] [Module F W]
    (W' : Submodule F W) (f : W' →ₗ[F] F) :
    (graphSubmodule W' f).map (LinearMap.snd F F W) = W' := by
  ext w
  constructor
  · rintro ⟨x, ⟨v, rfl⟩, rfl⟩
    exact v.2
  · intro hw
    refine ⟨(f ⟨w, hw⟩, w), ?_, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

theorem ker_snd_comp_subtype {W : Type*} [AddCommGroup W] [Module F W]
    (S : Submodule F (F × W)) (h1 : (1, (0 : W)) ∉ S) :
    LinearMap.ker ((LinearMap.snd F F W).comp S.subtype) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro ⟨⟨c, w⟩, hs⟩ hker
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply,
    LinearMap.snd_apply] at hker
  subst hker
  by_cases hc : c = 0
  · subst hc; rfl
  · exfalso
    have : (1, (0 : W)) = c⁻¹ • (c, (0 : W)) := by
      ext <;> simp [hc]
    apply h1
    rw [this]
    exact S.smul_mem c⁻¹ hs

theorem prod_top_map_snd {W : Type*} [AddCommGroup W] [Module F W]
    (W' : Submodule F W) :
    (Submodule.prod (⊤ : Submodule F F) W').map (LinearMap.snd F F W) = W' := by
  ext w
  constructor
  · rintro ⟨⟨c, x⟩, ⟨-, hx⟩, rfl⟩
    exact hx
  · intro hw
    exact ⟨(0, w), ⟨trivial, hw⟩, rfl⟩

theorem eq_prod_top_of_mem {W : Type*} [AddCommGroup W] [Module F W]
    (S : Submodule F (F × W)) (h1 : (1, (0 : W)) ∈ S) :
    S = Submodule.prod (⊤ : Submodule F F) (S.map (LinearMap.snd F F W)) := by
  ext ⟨c, w⟩
  constructor
  · intro hs
    exact ⟨trivial, ⟨(c, w), hs, rfl⟩⟩
  · rintro ⟨-, ⟨⟨c', w'⟩, hs, rfl⟩⟩
    simp only [LinearMap.snd_apply]
    have hc : (c - c', (0 : W)) ∈ S := by
      have : (c - c', (0 : W)) = (c - c') • (1, (0 : W)) := by
        ext <;> simp
      rw [this]
      exact S.smul_mem _ h1
    have : (c, w') = (c', w') + (c - c', (0 : W)) := by
      ext <;> simp
    rw [this]
    exact S.add_mem hs hc

def equivWithOne {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] (k : ℕ) :
    {S : Submodule F (F × W) // finrank F S = k + 1 ∧ (1, (0 : W)) ∈ S} ≃
      {W' : Submodule F W // finrank F W' = k} where
  toFun S := ⟨S.1.map (LinearMap.snd F F W), by
    have hS := eq_prod_top_of_mem S.1 S.2.2
    have hdim : finrank F S.1 = 1 + finrank F (S.1.map (LinearMap.snd F F W)) := by
      conv_lhs => rw [hS]
      rw [finrank_submodule_prod, finrank_top_self]
    have hSdim := S.2.1
    omega⟩
  invFun W' := ⟨Submodule.prod (⊤ : Submodule F F) W'.1, by
    have hdim : finrank F (Submodule.prod (⊤ : Submodule F F) W'.1) = k + 1 := by
      rw [finrank_submodule_prod, finrank_top_self, W'.2]
      omega
    exact ⟨hdim, ⟨trivial, W'.1.zero_mem⟩⟩⟩
  left_inv S := Subtype.ext (by
    have := (eq_prod_top_of_mem S.1 S.2.2).symm
    exact this)
  right_inv W' := Subtype.ext (prod_top_map_snd W'.1)

noncomputable def linearEquivOfNotMem {W : Type*} [AddCommGroup W] [Module F W]
    (S : Submodule F (F × W)) (h1 : (1, (0 : W)) ∉ S) :
    S ≃ₗ[F] S.map (LinearMap.snd F F W) :=
  let T : S →ₗ[F] W := (LinearMap.snd F F W).comp S.subtype
  have hT : Function.Injective T := LinearMap.ker_eq_bot.mp (ker_snd_comp_subtype S h1)
  (LinearEquiv.ofInjective T hT).trans (LinearEquiv.ofEq _ _ (by ext; simp [T, Submodule.mem_map]))

noncomputable def funcOfSubmodule {W : Type*} [AddCommGroup W] [Module F W]
    (S : Submodule F (F × W)) (h1 : (1, (0 : W)) ∉ S) :
    S.map (LinearMap.snd F F W) →ₗ[F] F :=
  let e := linearEquivOfNotMem S h1
  (LinearMap.fst F F W).comp (S.subtype.comp e.symm.toLinearMap)

theorem linearEquivOfNotMem_symm_apply {W : Type*} [AddCommGroup W] [Module F W]
    (S : Submodule F (F × W)) (h1 : (1, (0 : W)) ∉ S) (w : S.map (LinearMap.snd F F W)) :
    ((linearEquivOfNotMem S h1).symm w).1 = (funcOfSubmodule S h1 w, w.1) := by
  have hs := (linearEquivOfNotMem S h1).apply_symm_apply w
  refine Prod.ext rfl ?_
  exact congrArg Subtype.val hs

theorem graphSubmodule_funcOfSubmodule_eq {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (S : Submodule F (F × W)) (h1 : (1, (0 : W)) ∉ S) :
    graphSubmodule (S.map (LinearMap.snd F F W)) (funcOfSubmodule S h1) = S := by
  have hle : graphSubmodule (S.map (LinearMap.snd F F W)) (funcOfSubmodule S h1) ≤ S := by
    rintro ⟨c, w⟩ ⟨v, hv⟩
    have heq : (c, w) = ((linearEquivOfNotMem S h1).symm v).1 := by
      rw [← hv, linearEquivOfNotMem_symm_apply]
      rfl
    rw [heq]
    exact ((linearEquivOfNotMem S h1).symm v).2
  have hdim : finrank F (graphSubmodule (S.map (LinearMap.snd F F W)) (funcOfSubmodule S h1)) =
      finrank F S := by
    rw [finrank_graphSubmodule, (linearEquivOfNotMem S h1).finrank_eq.symm]
  exact Submodule.eq_of_le_of_finrank_eq hle hdim

instance finite_submodule {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] :
    Finite (Submodule F W) := by
  have : Finite W := Module.finite_of_finite F
  exact Finite.of_injective (fun (S : Submodule F W) => (S : Set W)) SetLike.coe_injective

abbrev SubWithoutOne (W : Type*) [AddCommGroup W] [Module F W] (k : ℕ) :=
  {S : Submodule F (F × W) // finrank F S = k + 1 ∧ (1, (0 : W)) ∉ S}

abbrev SubWithOne (W : Type*) [AddCommGroup W] [Module F W] (k : ℕ) :=
  {S : Submodule F (F × W) // finrank F S = k + 1 ∧ (1, (0 : W)) ∈ S}

def sndPr {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] (k : ℕ)
    (s : SubWithoutOne (F := F) W k) :
    {W' : Submodule F W // finrank F W' = k + 1} :=
  ⟨s.1.map (LinearMap.snd F F W), by
    rw [← (linearEquivOfNotMem s.1 s.2.2).finrank_eq, s.2.1]⟩

noncomputable def fiberEquiv {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] (k : ℕ)
    (W' : {W' : Submodule F W // finrank F W' = k + 1}) :
    {s : SubWithoutOne (F := F) W k // sndPr k s = W'} ≃
      (W'.1 →ₗ[F] F) := by
  let g : (W'.1 →ₗ[F] F) → {s : SubWithoutOne (F := F) W k // sndPr k s = W'} :=
    fun f => ⟨⟨graphSubmodule W'.1 f, ⟨by rw [finrank_graphSubmodule, W'.2], one_not_mem_graphSubmodule W'.1 f⟩⟩,
      Subtype.ext (graphSubmodule_map_snd W'.1 f)⟩
  have hg_inj : Function.Injective g := by
    intro f₁ f₂ hg
    have heq : graphSubmodule W'.1 f₁ = graphSubmodule W'.1 f₂ := by
      have := congrArg (fun x : {s // sndPr k s = W'} => x.1.1) hg
      exact this
    apply LinearMap.ext
    intro w
    have hw : (f₁ w, w.1) ∈ graphSubmodule W'.1 f₂ := by
      have : (f₁ w, w.1) ∈ graphSubmodule W'.1 f₁ := ⟨w, rfl⟩
      rw [heq] at this
      exact this
    rcases hw with ⟨w', hw'⟩
    have hw1 : w'.1 = w.1 := congrArg Prod.snd hw'
    have hw0 : w' = w := Subtype.ext hw1
    have hf : f₂ w' = f₁ w := congrArg Prod.fst hw'
    rw [hw0] at hf
    exact hf.symm
  have hg_surj : Function.Surjective g := by
    intro s
    obtain ⟨⟨S, ⟨hdim, hone⟩⟩, hfib⟩ := s
    dsimp [sndPr] at hfib
    have hW : S.map (LinearMap.snd F F W) = W'.1 := congrArg Subtype.val hfib
    let eW : W'.1 ≃ₗ[F] S.map (LinearMap.snd F F W) := LinearEquiv.ofEq _ _ hW.symm
    let f : W'.1 →ₗ[F] F := (funcOfSubmodule S hone).comp eW.toLinearMap
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    dsimp [g]
    have hgraph : graphSubmodule W'.1 f = graphSubmodule (S.map (LinearMap.snd F F W)) (funcOfSubmodule S hone) := by
      ext p
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨eW v, ?_⟩
        ext <;> rfl
      · rintro ⟨v, rfl⟩
        refine ⟨eW.symm v, ?_⟩
        ext
        · simp [f, eW.apply_symm_apply]
        · rfl
    rw [hgraph, graphSubmodule_funcOfSubmodule_eq S hone]
  exact (Equiv.ofBijective g ⟨hg_inj, hg_surj⟩).symm

theorem card_without_one {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] (k : ℕ) :
    Nat.card (SubWithoutOne (F := F) W k) =
      (Fintype.card F) ^ (k + 1) * Nat.card {W' : Submodule F W // finrank F W' = k + 1} := by
  have : Finite W := Module.finite_of_finite F
  have : Finite (Submodule F W) := inferInstance
  have : Finite {W' : Submodule F W // finrank F W' = k + 1} := inferInstance
  cases nonempty_fintype {W' : Submodule F W // finrank F W' = k + 1}
  have e := (Equiv.sigmaFiberEquiv (sndPr (F := F) (W := W) k)).symm
  rw [Nat.card_congr e, Nat.card_sigma]
  have hfib (W' : {W' : Submodule F W // finrank F W' = k + 1}) :
      Nat.card {s : SubWithoutOne (F := F) W k // sndPr k s = W'} = (Fintype.card F) ^ (k + 1) := by
    have : FiniteDimensional F W'.1 := inferInstance
    rw [Nat.card_congr (fiberEquiv k W'), card_dual_eq_pow, W'.2]
  simp_rw [hfib]
  simp [Nat.card_eq_fintype_card, mul_comm]

theorem card_with_one {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] (k : ℕ) :
    Nat.card (SubWithOne (F := F) W k) =
      Nat.card {W' : Submodule F W // finrank F W' = k} :=
  Nat.card_congr (equivWithOne k)

noncomputable def splitOneEquiv {W : Type*} [AddCommGroup W] [Module F W] (k : ℕ) :
    {S : Submodule F (F × W) // finrank F S = k + 1} ≃
      SubWithOne (F := F) W k ⊕ SubWithoutOne (F := F) W k where
  toFun S :=
    if h : (1, (0 : W)) ∈ S.1 then
      Sum.inl ⟨S.1, ⟨S.2, h⟩⟩
    else
      Sum.inr ⟨S.1, ⟨S.2, h⟩⟩
  invFun := Sum.elim (fun S => ⟨S.1, S.2.1⟩) (fun S => ⟨S.1, S.2.1⟩)
  left_inv S := by
    dsimp
    split_ifs <;> rfl
  right_inv := by
    rintro (⟨S, ⟨hdim, hone⟩⟩ | ⟨S, ⟨hdim, hone⟩⟩) <;> dsimp
    · rw [dite_eq_left hone]
    · rw [dite_eq_right hone]

theorem card_submodules_succ_succ {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] (k : ℕ) :
    Nat.card {S : Submodule F (F × W) // finrank F S = k + 1} =
      Nat.card {W' : Submodule F W // finrank F W' = k} +
        (Fintype.card F) ^ (k + 1) * Nat.card {W' : Submodule F W // finrank F W' = k + 1} := by
  have e := splitOneEquiv (F := F) (W := W) k
  rw [Nat.card_congr e, Nat.card_sum, card_with_one, card_without_one]

omit [Fintype F] in
theorem eq_bot_of_finrank_zero {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {S : Submodule F V} (hS : finrank F S = 0) : S = ⊥ := by
  ext x
  simp only [Submodule.mem_bot]
  constructor
  · intro hx
    have : (⟨x, hx⟩ : S) = 0 := (finrank_zero_iff_forall_zero.mp hS) ⟨x, hx⟩
    exact Subtype.ext_iff.mp this
  · rintro rfl; exact S.zero_mem

omit [Fintype F] in
theorem card_submodules_zero {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] :
    Nat.card {S : Submodule F V // finrank F S = 0} = 1 := by
  have : Unique {S : Submodule F V // finrank F S = 0} := by
    refine ⟨⟨⟨⊥, finrank_bot F V⟩⟩, ?_⟩
    rintro ⟨S, hS⟩
    apply Subtype.ext
    exact eq_bot_of_finrank_zero hS
  exact Nat.card_unique

omit [Fintype F] in
theorem card_submodules_of_gt {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {n i : ℕ} (hn : finrank F V = n) (h : n < i) :
    Nat.card {S : Submodule F V // finrank F S = i} = 0 := by
  have : IsEmpty {S : Submodule F V // finrank F S = i} := by
    refine ⟨fun ⟨S, hS⟩ => ?_⟩
    have hle := Submodule.finrank_le S
    omega
  exact Nat.card_eq_zero.mpr (Or.inl this)

omit [Fintype F] in
noncomputable def equivProd {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (n : ℕ) (hn : finrank F V = n + 1) : V ≃ₗ[F] F × (Fin n → F) :=
  LinearEquiv.ofFinrankEq V (F × (Fin n → F)) (by
    rw [hn, Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun, add_comm])

end MartinPhd

end Subspaces
