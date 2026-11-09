import MartinPhd.Chapter1Section2Cauchy

/-!
# Background: the Solomon–Tits theorem (Theorem 1.7, cited in Section 1.5)

Contents:
* The Solomon–Tits theorem, at the level of chains
-/

section SolomonTits

/-!
## The Solomon–Tits theorem, at the level of chains

Proof of Theorem 1.7 for the augmented chain complex of flags of an arbitrary
finite-dimensional space `V` over a finite field (the thesis cites it without proof). The
proof is by induction on `dim V`, purely algebraic:

* Fix `v ≠ 0` and `L = ⟨v⟩`. For a flag `G` let `A(G)` be its largest member not containing
  `v` and `X(G) = A(G) ⊔ L`. A flag is *bad* if `X(G) = V`; then `A(G)` is a hyperplane
  complementary to `L` and `G` is a flag of `A(G)` followed by `V` (`ext`).
* The operator `h` inserting `X(G)` (when it is not already a member) satisfies
  `∂h + h∂ = id − (bad part)` up to terms with fewer members avoiding `v` (`key`). Filtering
  by that number shows the good flags form an acyclic complex (`good_acyclic`).
* The bad flags are `⊔_H (flags of H)` over the `q^{n-1}` complements `H` of `L`, compatibly
  with `∂` up to good terms. This transfers exactness from the `H` to `V`, and gives
  `St(V) ≅ ⊕_H St(H)`, hence `dim St(V) = q^{n-1} q^{C(n-1,2)} = q^{C(n,2)}`.
-/

open scoped BigOperators
open Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ST

variable {F : Type} [Field F] (k : Type) [Field k]

section Boundary

variable {V : Type} [AddCommGroup V] [Module F V]

/-- The face of `G` obtained by erasing the member `W` (zero unless `W` is intermediate). -/
def face (G : Flag F V) (W : Submodule F V) : Flag F V →₀ k :=
  if h : W ≠ ⊥ ∧ W ≠ ⊤ then ((-1 : k) ^ G.index W) • Finsupp.single (G.erase W h) 1 else 0

/-- The boundary `∂ e_G = ∑_{0<i<len G} (-1)ⁱ e_{G ∖ Gᵢ}` on `k[Fl(V)]`. -/
def bd : (Flag F V →₀ k) →ₗ[k] (Flag F V →₀ k) :=
  Finsupp.linearCombination k fun G => ∑ W ∈ G.carrier, face k G W

theorem bd_single (G : Flag F V) : bd k (Finsupp.single G 1) = ∑ W ∈ G.carrier, face k G W := by
  simp [bd]

/-- Flags of length `m`. -/
def deg (V : Type) [AddCommGroup V] [Module F V] (m : ℕ) : Submodule k (Flag F V →₀ k) :=
  Finsupp.supported k k {G : Flag F V | G.len = m}

theorem map_supported_le {α M : Type*} [AddCommGroup M] [Module k M] (f : (α →₀ k) →ₗ[k] M)
    (S : Set α) (P : Submodule k M) (h : ∀ a ∈ S, f (Finsupp.single a 1) ∈ P) :
    ∀ x ∈ Finsupp.supported k k S, f x ∈ P := by
  intro x hx
  rw [Finsupp.supported_eq_span_single] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    exact h a ha
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact P.add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact P.smul_mem c hx

theorem erase_carrier (G : Flag F V) (W : Submodule F V) (h : W ≠ ⊥ ∧ W ≠ ⊤) :
    (G.erase W h).carrier = G.carrier.erase W := rfl

theorem len_erase (G : Flag F V) {W : Submodule F V} (h : W ≠ ⊥ ∧ W ≠ ⊤)
    (hW : W ∈ G.carrier) : (G.erase W h).len + 1 = G.len := by
  unfold Flag.len
  rw [erase_carrier, Finset.card_erase_of_mem hW]
  have := Finset.card_lt_card (Finset.erase_ssubset (s := G.carrier) G.bot_mem)
  have h2 : 2 ≤ G.carrier.card := by
    have : ({⊥, ⊤} : Finset (Submodule F V)) ⊆ G.carrier := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact G.bot_mem
      · exact G.top_mem
    have hne : (⊥ : Submodule F V) ≠ ⊤ := fun h' => h.1 (by rw [eq_bot_iff, h']; exact le_top)
    calc 2 = ({⊥, ⊤} : Finset (Submodule F V)).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card this
  omega

theorem index_erase (G : Flag F V) {A : Submodule F V} (hA : A ≠ ⊥ ∧ A ≠ ⊤)
    (hAG : A ∈ G.carrier) (B : Submodule F V) :
    G.index B = (G.erase A hA).index B + if A < B then 1 else 0 := by
  unfold Flag.index
  rw [erase_carrier, Finset.filter_erase]
  split_ifs with h
  · rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hAG, h⟩)]
    have : 0 < (G.carrier.filter (· < B)).card :=
      Finset.card_pos.2 ⟨A, Finset.mem_filter.2 ⟨hAG, h⟩⟩
    omega
  · rw [Finset.erase_eq_of_notMem (by simp [h])]; rfl

theorem erase_erase (G : Flag F V) {A B : Submodule F V} (hA : A ≠ ⊥ ∧ A ≠ ⊤)
    (hB : B ≠ ⊥ ∧ B ≠ ⊤) : (G.erase A hA).erase B hB = (G.erase B hB).erase A hA := by
  apply Flag.ext
  simp only [erase_carrier]
  exact Finset.erase_right_comm

/-- `∂ ∂ = 0`. -/
theorem bd_bd (x : Flag F V →₀ k) : bd k (bd k x) = 0 := by
  suffices h : ∀ G : Flag F V, bd k (bd k (Finsupp.single G 1)) = 0 by
    have := map_supported_le k ((bd k) ∘ₗ (bd k)) Set.univ ⊥ (fun G _ => by simpa using h G)
      x (by simp)
    simpa using this
  intro G
  rw [bd_single, map_sum]
  -- rewrite as a sum over ordered pairs of distinct members
  let t : Submodule F V × Submodule F V → (Flag F V →₀ k) := fun p =>
    if hA : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤ then if hB : p.2 ≠ ⊥ ∧ p.2 ≠ ⊤ then if p.1 ≠ p.2 then
      ((-1 : k) ^ G.index p.1 * (-1 : k) ^ (G.erase p.1 hA).index p.2) •
        Finsupp.single ((G.erase p.1 hA).erase p.2 hB) 1 else 0 else 0 else 0
  have hsum : ∑ W ∈ G.carrier, bd k (face k G W) = ∑ p ∈ G.carrier ×ˢ G.carrier, t p := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun A hA => ?_
    unfold face
    by_cases hmA : A ≠ ⊥ ∧ A ≠ ⊤
    · rw [dif_pos hmA, map_smul, bd_single, Finset.smul_sum, erase_carrier,
        ← Finset.sum_erase_add _ _ hA]
      rw [show t (A, A) = 0 by simp [t], add_zero]
      refine Finset.sum_congr rfl fun B hB => ?_
      have hBA : A ≠ B := (Finset.ne_of_mem_erase hB).symm
      simp only [t, dif_pos hmA, ne_eq, hBA, not_false_eq_true, if_true]
      unfold face
      split_ifs with hmB
      · rw [smul_smul]
      · simp
    · rw [dif_neg hmA, map_zero]
      symm
      exact Finset.sum_eq_zero fun B _ => by simp [t, dif_neg hmA]
  rw [hsum]
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ (fun p hp => by
    simpa [Finset.mem_product, and_comm] using hp) (fun p _ => rfl)
  · intro p hp
    obtain ⟨A, B⟩ := p
    simp only [Finset.mem_product] at hp
    simp only [t]
    by_cases hA : A ≠ ⊥ ∧ A ≠ ⊤
    · by_cases hB : B ≠ ⊥ ∧ B ≠ ⊤
      · by_cases hAB : A ≠ B
        · rw [dif_pos hA, dif_pos hB, if_pos hAB, dif_pos hB, dif_pos hA, if_pos (Ne.symm hAB),
            erase_erase G hB hA, ← add_smul]
          convert zero_smul k _
          have e1 := index_erase G hA hp.1 B
          have e2 := index_erase G hB hp.2 A
          rcases G.isChain hp.1 hp.2 hAB with hle | hle
          · have hlt : A < B := lt_of_le_of_ne hle hAB
            rw [if_pos hlt] at e1
            rw [if_neg (not_lt_of_ge hle)] at e2
            rw [add_zero] at e2
            rw [e2, e1, pow_succ]
            ring
          · have hlt : B < A := lt_of_le_of_ne hle (Ne.symm hAB)
            rw [if_pos hlt] at e2
            rw [if_neg (not_lt_of_ge hle)] at e1
            rw [add_zero] at e1
            rw [e1, e2, pow_succ]
            ring
        · simp at hAB; simp [hAB]
      · simp [dif_neg hB]
    · simp [dif_neg hA]
  · intro p _ hp heq
    obtain ⟨A, B⟩ := p
    simp only [Prod.mk.injEq] at heq
    apply hp
    simp [t, heq.1]

end Boundary

section Line

variable {V : Type} [AddCommGroup V] [Module F V] (v : V)

/-- Members of `G` not containing `v`. -/
def Aset (G : Flag F V) : Finset (Submodule F V) := G.carrier.filter (fun W => v ∉ W)

/-- The filtration degree: how many members of `G` avoid `v`. -/
def mu (G : Flag F V) : ℕ := (Aset v G).card

/-- The largest member of `G` not containing `v`. -/
def Am (G : Flag F V) : Submodule F V := (Aset v G).sup id

/-- `X(G) = A(G) ⊔ ⟨v⟩`. -/
def Xm (G : Flag F V) : Submodule F V := Am v G ⊔ Submodule.span F {v}

variable {v}

theorem Am_mem (hv : v ≠ 0) (G : Flag F V) : Am v G ∈ Aset v G := by
  have := Finset.sup_mem (↑(Aset v G) : Set (Submodule F V))
    (by simp [Aset, G.bot_mem, hv]) (by
      intro x hx y hy
      simp only [Aset, Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      by_cases hxy : x = y
      · subst hxy; simpa [Aset] using hx
      rcases G.isChain hx.1 hy.1 hxy with h | h
      · rw [sup_eq_right.2 h]; simpa [Aset] using hy
      · rw [sup_eq_left.2 h]; simpa [Aset] using hx) (Aset v G) id (fun i hi => hi)
  exact this

theorem Am_carrier (hv : v ≠ 0) (G : Flag F V) : Am v G ∈ G.carrier :=
  (Finset.mem_filter.1 (Am_mem hv G)).1

theorem v_notMem_Am (hv : v ≠ 0) (G : Flag F V) : v ∉ Am v G :=
  (Finset.mem_filter.1 (Am_mem hv G)).2

theorem le_Am (G : Flag F V) {W : Submodule F V} (hW : W ∈ G.carrier) (hv : v ∉ W) :
    W ≤ Am v G :=
  Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hW, hv⟩)

theorem Am_le (hv0 : v ≠ 0) (G : Flag F V) {W : Submodule F V} (hW : W ∈ G.carrier)
    (hv : v ∈ W) : Am v G ≤ W := by
  have hne : Am v G ≠ W := fun h => v_notMem_Am hv0 G (h ▸ hv)
  rcases G.isChain (Am_carrier hv0 G) hW hne with h | h
  · exact h
  · exact absurd (h hv) (v_notMem_Am hv0 G)

theorem v_mem_Xm (G : Flag F V) : v ∈ Xm v G :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)

theorem Xm_le (hv0 : v ≠ 0) (G : Flag F V) {W : Submodule F V} (hW : W ∈ G.carrier)
    (hv : v ∈ W) : Xm v G ≤ W :=
  sup_le (Am_le hv0 G hW hv) ((Submodule.span_singleton_le_iff_mem _ _).2 hv)

theorem Am_lt_Xm (hv0 : v ≠ 0) (G : Flag F V) : Am v G < Xm v G :=
  lt_of_le_of_ne le_sup_left fun h => v_notMem_Am hv0 G (h ▸ v_mem_Xm G)

theorem lt_Xm_iff (hv0 : v ≠ 0) (G : Flag F V) {W : Submodule F V} (hW : W ∈ G.carrier) :
    W < Xm v G ↔ v ∉ W := by
  constructor
  · intro h hv
    exact absurd (Xm_le hv0 G hW hv) (not_le_of_gt h)
  · intro hv
    exact lt_of_le_of_lt (le_Am G hW hv) (Am_lt_Xm hv0 G)

theorem Xm_ne_bot (G : Flag F V) (hv0 : v ≠ 0) : Xm v G ≠ ⊥ := fun h =>
  hv0 (by simpa [h] using v_mem_Xm (v := v) G)

theorem Xm_comparable (hv0 : v ≠ 0) (G : Flag F V) :
    ∀ B ∈ G.carrier, Xm v G ≤ B ∨ B ≤ Xm v G := by
  intro B hB
  by_cases hv : v ∈ B
  · exact Or.inl (Xm_le hv0 G hB hv)
  · exact Or.inr (lt_Xm_iff hv0 G hB |>.2 hv).le

/-- `G` with `X(G)` inserted. -/
def insertX (hv0 : v ≠ 0) (G : Flag F V) : Flag F V := G.insert (Xm v G) (Xm_comparable hv0 G)

theorem insertX_carrier (hv0 : v ≠ 0) (G : Flag F V) :
    (insertX hv0 G).carrier = insert (Xm v G) G.carrier := rfl

theorem Aset_erase (G : Flag F V) {W : Submodule F V} (h : W ≠ ⊥ ∧ W ≠ ⊤) :
    Aset v (G.erase W h) = (Aset v G).erase W := by
  simp [Aset, erase_carrier, Finset.filter_erase]

theorem Aset_erase_of_mem (G : Flag F V) {W : Submodule F V} (h : W ≠ ⊥ ∧ W ≠ ⊤)
    (hv : v ∈ W) : Aset v (G.erase W h) = Aset v G := by
  rw [Aset_erase, Finset.erase_eq_of_notMem]
  simp [Aset, hv]

theorem Aset_insertX (hv0 : v ≠ 0) (G : Flag F V) : Aset v (insertX hv0 G) = Aset v G := by
  simp [Aset, insertX_carrier, Finset.filter_insert, v_mem_Xm]

theorem Xm_eq_of_Aset {G G' : Flag F V} (h : Aset v G' = Aset v G) : Xm v G' = Xm v G := by
  simp [Xm, Am, h]

theorem mu_eq_of_Aset {G G' : Flag F V} (h : Aset v G' = Aset v G) : mu v G' = mu v G := by
  simp [mu, h]

theorem filter_lt_Xm (hv0 : v ≠ 0) (G : Flag F V) :
    G.carrier.filter (· < Xm v G) = Aset v G := by
  ext W
  simp only [Finset.mem_filter, Aset]
  exact ⟨fun h => ⟨h.1, (lt_Xm_iff hv0 G h.1).1 h.2⟩, fun h => ⟨h.1, (lt_Xm_iff hv0 G h.1).2 h.2⟩⟩

theorem index_Xm (hv0 : v ≠ 0) (G : Flag F V) : G.index (Xm v G) = mu v G := by
  unfold Flag.index; rw [filter_lt_Xm hv0]; rfl

theorem index_insertX_Xm (hv0 : v ≠ 0) (G : Flag F V) :
    (insertX hv0 G).index (Xm v G) = mu v G := by
  unfold Flag.index
  rw [insertX_carrier, Finset.filter_insert, if_neg (lt_irrefl _), filter_lt_Xm hv0]; rfl

theorem index_insertX (hv0 : v ≠ 0) (G : Flag F V) (hX : Xm v G ∉ G.carrier)
    (W : Submodule F V) :
    (insertX hv0 G).index W = G.index W + if Xm v G < W then 1 else 0 := by
  unfold Flag.index
  rw [insertX_carrier, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hX])]
  · rfl

/-- The insertion operator on basis vectors. -/
def hval (hv0 : v ≠ 0) (G : Flag F V) : Flag F V →₀ k :=
  if Xm v G ∉ G.carrier then ((-1 : k) ^ mu v G) • Finsupp.single (insertX hv0 G) 1 else 0

/-- The insertion operator `h`. -/
def hop (hv0 : v ≠ 0) : (Flag F V →₀ k) →ₗ[k] (Flag F V →₀ k) :=
  Finsupp.linearCombination k (hval k hv0)

theorem hop_single (hv0 : v ≠ 0) (G : Flag F V) :
    hop k hv0 (Finsupp.single G 1) = hval k hv0 G := by
  simp [hop]

variable (v) in
/-- Chains supported on flags with fewer than `d` members avoiding `v`. -/
def low (V : Type) [AddCommGroup V] [Module F V] (v : V) (d : ℕ) :
    Submodule k (Flag F V →₀ k) :=
  Finsupp.supported k k {G : Flag F V | mu v G < d}

theorem single_mem_low {G : Flag F V} {d : ℕ} (h : mu v G < d) :
    Finsupp.single G (1 : k) ∈ low k V v d :=
  Finsupp.single_mem_supported k _ h

theorem hval_mem_low (hv0 : v ≠ 0) {G : Flag F V} {d : ℕ} (h : mu v G < d) :
    hval k hv0 G ∈ low k V v d := by
  unfold hval
  by_cases hX : Xm v G ∈ G.carrier
  · rw [if_neg (not_not.2 hX)]; exact zero_mem _
  · rw [if_pos hX]
    refine Submodule.smul_mem _ _ (single_mem_low k ?_)
    rwa [mu_eq_of_Aset (Aset_insertX hv0 G)]

theorem face_mem_low (G : Flag F V) {W : Submodule F V} (hW : W ∈ G.carrier) (hv : v ∉ W) :
    face k G W ∈ low k V v (mu v G) := by
  unfold face
  split_ifs with h
  · refine Submodule.smul_mem _ _ (single_mem_low k ?_)
    unfold mu
    rw [Aset_erase]
    exact Finset.card_erase_lt_of_mem (Finset.mem_filter.2 ⟨hW, hv⟩)
  · exact zero_mem _

theorem hop_face_mem_low (hv0 : v ≠ 0) (G : Flag F V) {W : Submodule F V} (hW : W ∈ G.carrier)
    (hv : v ∉ W) : hop k hv0 (face k G W) ∈ low k V v (mu v G) := by
  unfold face
  split_ifs with h
  · rw [map_smul, hop_single]
    refine Submodule.smul_mem _ _ (hval_mem_low k hv0 ?_)
    unfold mu
    rw [Aset_erase]
    exact Finset.card_erase_lt_of_mem (Finset.mem_filter.2 ⟨hW, hv⟩)
  · simp

theorem neg_one_pow_mul_self (n : ℕ) : (-1 : k) ^ n * (-1 : k) ^ n = 1 := by
  rw [← mul_pow]; simp

/-- **Key identity.** `∂h + h∂ = id − (bad part)` modulo chains with smaller `mu`. -/
theorem key (hv0 : v ≠ 0) (G : Flag F V) :
    bd k (hop k hv0 (Finsupp.single G 1)) + hop k hv0 (bd k (Finsupp.single G 1)) -
      (if Xm v G = ⊤ then 0 else Finsupp.single G 1) ∈ low k V v (mu v G) := by
  rw [hop_single, bd_single, map_sum]
  by_cases hX : Xm v G ∈ G.carrier
  · -- saturated
    have h0 : hval k hv0 G = 0 := by simp [hval, hX]
    rw [h0, map_zero, zero_add, ← Finset.add_sum_erase _ _ hX]
    have hXX : hop k hv0 (face k G (Xm v G)) = if Xm v G = ⊤ then 0 else Finsupp.single G 1 := by
      unfold face
      split_ifs with h1 h2 h2
      · exact absurd h2 h1.2
      · rw [map_smul, hop_single]
        have hA := Aset_erase_of_mem G h1 (v_mem_Xm G)
        have hXe := Xm_eq_of_Aset hA
        have hnot : Xm v (G.erase (Xm v G) h1) ∉ (G.erase (Xm v G) h1).carrier := by
          rw [hXe, erase_carrier]; simp
        rw [hval, if_pos hnot, smul_smul, mu_eq_of_Aset hA, index_Xm hv0, neg_one_pow_mul_self,
          one_smul]
        congr 1
        apply Flag.ext
        rw [insertX_carrier, hXe, erase_carrier, Finset.insert_erase hX]
      · simp
      · simp at h1; exact absurd (h1 (Xm_ne_bot G hv0)) h2
    rw [hXX, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun W hW => ?_
    have hWG := Finset.mem_of_mem_erase hW
    by_cases hv : v ∈ W
    · unfold face
      split_ifs with h
      · rw [map_smul, hop_single]
        have hA := Aset_erase_of_mem G h hv
        have : hval k hv0 (G.erase W h) = 0 := by
          rw [hval, if_neg]; push Not
          rw [Xm_eq_of_Aset hA, erase_carrier]
          exact Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hW).symm, hX⟩
        rw [this, smul_zero]; exact zero_mem _
      · simp
    · exact hop_face_mem_low k hv0 G hWG hv
  · -- unsaturated
    have hXt : Xm v G ≠ ⊤ := fun h => hX (h ▸ G.top_mem)
    have hmid : Xm v G ≠ ⊥ ∧ Xm v G ≠ ⊤ := ⟨Xm_ne_bot G hv0, hXt⟩
    rw [hval, if_pos hX, if_neg hXt, map_smul, bd_single, insertX_carrier,
      Finset.sum_insert hX, smul_add]
    have hface : ((-1 : k) ^ mu v G) • face k (insertX hv0 G) (Xm v G) = Finsupp.single G 1 := by
      unfold face
      rw [dif_pos hmid, smul_smul, index_insertX_Xm hv0, neg_one_pow_mul_self, one_smul]
      congr 1
      apply Flag.ext
      rw [erase_carrier, insertX_carrier, Finset.erase_insert hX]
    rw [hface, add_assoc, add_sub_cancel_left, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Submodule.sum_mem _ fun W hW => ?_
    by_cases hv : v ∈ W
    · unfold face
      split_ifs with h
      · rw [map_smul, hop_single]
        have hA := Aset_erase_of_mem G h hv
        have hXe := Xm_eq_of_Aset hA
        have hnot : Xm v (G.erase W h) ∉ (G.erase W h).carrier := by
          rw [hXe, erase_carrier]; exact fun h' => hX (Finset.mem_of_mem_erase h')
        have hXW : Xm v G ≠ W := fun h' => hX (h' ▸ hW)
        have hXlt : Xm v G < W := lt_of_le_of_ne (Xm_le hv0 G hW hv) hXW
        rw [hval, if_pos hnot, smul_smul, smul_smul, mu_eq_of_Aset hA,
          index_insertX hv0 G hX, if_pos hXlt]
        have hflag : (insertX hv0 G).erase W h = insertX hv0 (G.erase W h) := by
          apply Flag.ext
          rw [erase_carrier, insertX_carrier, insertX_carrier, hXe, erase_carrier,
            Finset.erase_insert_of_ne hXW]
        rw [hflag, ← add_smul]
        convert zero_mem (low k V v (mu v G))
        convert zero_smul k _
        rw [pow_succ]; ring
      · simp
    · refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (hop_face_mem_low k hv0 G hW hv)
      have := face_mem_low k (insertX hv0 G) (Finset.mem_insert_of_mem hW) hv
      rwa [mu_eq_of_Aset (Aset_insertX hv0 G)] at this

end Line

section Good

variable {V : Type} [AddCommGroup V] [Module F V] {v : V}

variable (v) in
/-- Chains supported on good flags (`X(G) ≠ V`). -/
def goodS (V : Type) [AddCommGroup V] [Module F V] (v : V) : Submodule k (Flag F V →₀ k) :=
  Finsupp.supported k k {G : Flag F V | Xm v G ≠ ⊤}

theorem Xm_erase_le (G : Flag F V) {W : Submodule F V} (h : W ≠ ⊥ ∧ W ≠ ⊤) :
    Xm v (G.erase W h) ≤ Xm v G := by
  unfold Xm Am
  rw [Aset_erase]
  exact sup_le_sup_right (Finset.sup_mono (Finset.erase_subset _ _)) _

theorem face_mem_goodS (G : Flag F V) (hG : Xm v G ≠ ⊤) (W : Submodule F V) :
    face k G W ∈ goodS k V v := by
  unfold face
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported k _
      (fun h' => hG (top_le_iff.1 (h' ▸ Xm_erase_le G h))))
  · exact zero_mem _

theorem bd_mem_goodS {z : Flag F V →₀ k} (hz : z ∈ goodS k V v) : bd k z ∈ goodS k V v :=
  map_supported_le k (bd k) _ _ (fun G hG => by
    rw [bd_single]; exact Submodule.sum_mem _ fun W _ => face_mem_goodS k G hG W) z hz

theorem hop_mem_goodS (hv0 : v ≠ 0) {z : Flag F V →₀ k} (hz : z ∈ goodS k V v) :
    hop k hv0 z ∈ goodS k V v :=
  map_supported_le k (hop k hv0) _ _ (fun G hG => by
    rw [hop_single, hval]
    by_cases hX : Xm v G ∈ G.carrier
    · rw [if_neg (not_not.2 hX)]; exact zero_mem _
    · rw [if_pos hX]
      refine Submodule.smul_mem _ _ (Finsupp.single_mem_supported k _ ?_)
      show Xm v (insertX hv0 G) ≠ ⊤
      rwa [Xm_eq_of_Aset (Aset_insertX hv0 G)]) z hz

theorem face_mem_deg (G : Flag F V) {m : ℕ} (hG : G.len = m + 1) {W : Submodule F V}
    (hW : W ∈ G.carrier) : face k G W ∈ deg k V m := by
  unfold face
  split_ifs with h
  · refine Submodule.smul_mem _ _ (Finsupp.single_mem_supported k _ ?_)
    show (G.erase W h).len = m
    have := len_erase G h hW; omega
  · exact zero_mem _

theorem bd_mem_deg {m : ℕ} {z : Flag F V →₀ k} (hz : z ∈ deg k V (m + 1)) :
    bd k z ∈ deg k V m :=
  map_supported_le k (bd k) _ _ (fun G hG => by
    rw [bd_single]; exact Submodule.sum_mem _ fun W hW => face_mem_deg k G hG hW) z hz

theorem len_insertX (hv0 : v ≠ 0) (G : Flag F V) (hX : Xm v G ∉ G.carrier) :
    (insertX hv0 G).len = G.len + 1 := by
  unfold Flag.len
  rw [insertX_carrier, Finset.card_insert_of_notMem hX]
  have := G.carrier_card_pos
  omega

theorem hop_mem_deg (hv0 : v ≠ 0) {m : ℕ} {z : Flag F V →₀ k} (hz : z ∈ deg k V m) :
    hop k hv0 z ∈ deg k V (m + 1) :=
  map_supported_le k (hop k hv0) _ _ (fun G hG => by
    rw [hop_single, hval]
    by_cases hX : Xm v G ∈ G.carrier
    · rw [if_neg (not_not.2 hX)]; exact zero_mem _
    · rw [if_pos hX]
      refine Submodule.smul_mem _ _ (Finsupp.single_mem_supported k _ ?_)
      show (insertX hv0 G).len = m + 1
      rw [len_insertX hv0 G hX]; simpa using hG) z hz

theorem low_mono {d e : ℕ} (h : d ≤ e) : low (F := F) k V v d ≤ low k V v e :=
  Finsupp.supported_mono fun _ hG => lt_of_lt_of_le hG h

theorem step_mem_low (hv0 : v ≠ 0) (d : ℕ) {z : Flag F V →₀ k} (hzg : z ∈ goodS k V v)
    (hzl : z ∈ low k V v (d + 1)) :
    bd k (hop k hv0 z) + hop k hv0 (bd k z) - z ∈ low k V v d := by
  have hz : z ∈ Finsupp.supported k k ({G : Flag F V | Xm v G ≠ ⊤} ∩ {G | mu v G < d + 1}) := by
    rw [Finsupp.supported_inter]; exact ⟨hzg, hzl⟩
  have := map_supported_le k ((bd k) ∘ₗ (hop k hv0) + (hop k hv0) ∘ₗ (bd k) - LinearMap.id) _
    (low k V v d) (fun G hG => by
      have hk := key k hv0 G
      rw [if_neg hG.1] at hk
      simpa using low_mono k (Nat.lt_succ_iff.1 hG.2) hk) z hz
  simpa using this

/-- The good flags form an acyclic (augmented) complex. -/
theorem good_acyclic (hv0 : v ≠ 0) {m : ℕ} {z : Flag F V →₀ k} (hzg : z ∈ goodS k V v)
    (hzd : z ∈ deg k V m) (hz : bd k z = 0) :
    ∃ y ∈ goodS k V v, y ∈ deg k V (m + 1) ∧ bd k y = z := by
  suffices H : ∀ d (z : Flag F V →₀ k), z ∈ goodS k V v → z ∈ deg k V m → z ∈ low k V v d →
      bd k z = 0 → ∃ y ∈ goodS k V v, y ∈ deg k V (m + 1) ∧ bd k y = z by
    refine H (z.support.sup (mu v) + 1) z hzg hzd ?_ hz
    intro G hG
    exact Nat.lt_succ_of_le (Finset.le_sup (f := mu v) hG)
  intro d
  induction d with
  | zero =>
    intro z _ _ hl _
    have : z = 0 := by
      ext G
      by_contra h
      exact absurd (hl (Finsupp.mem_support_iff.2 h)) (Nat.not_lt_zero _)
    exact ⟨0, zero_mem _, zero_mem _, by simp [this]⟩
  | succ d ih =>
    intro z hg hd hl hz
    set w := bd k (hop k hv0 z) - z with hw
    have hwl : w ∈ low k V v d := by
      have := step_mem_low k hv0 d hg hl
      rwa [hz, map_zero, add_zero] at this
    have hwg : w ∈ goodS k V v :=
      Submodule.sub_mem _ (bd_mem_goodS k (hop_mem_goodS k hv0 hg)) hg
    have hwd : w ∈ deg k V m := Submodule.sub_mem _ (bd_mem_deg k (hop_mem_deg k hv0 hd)) hd
    have hwz : bd k w = 0 := by rw [hw, map_sub, bd_bd, hz, sub_zero]
    obtain ⟨y, hyg, hyd, hy⟩ := ih w hwg hwd hwl hwz
    refine ⟨hop k hv0 z - y, Submodule.sub_mem _ (hop_mem_goodS k hv0 hg) hyg,
      Submodule.sub_mem _ (hop_mem_deg k hv0 hd) hyd, ?_⟩
    rw [map_sub, hy, hw]; abel

end Good

section Ext

variable {V : Type} [AddCommGroup V] [Module F V]

/-- A flag of `H ≤ V` followed by `V`. -/
def ext (H : Submodule F V) (F' : Flag F H) : Flag F V where
  carrier := insert ⊤ (F'.carrier.image (Submodule.map H.subtype))
  isChain := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
      Finset.mem_coe] at ha hb
    rcases ha with rfl | ⟨x, hx, rfl⟩
    · exact Or.inr le_top
    rcases hb with rfl | ⟨y, hy, rfl⟩
    · exact Or.inl le_top
    have hxy : x ≠ y := fun h => hab (h ▸ rfl)
    rcases F'.isChain hx hy hxy with h | h
    · exact Or.inl (Submodule.map_mono h)
    · exact Or.inr (Submodule.map_mono h)
  bot_mem := Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⊥, F'.bot_mem, Submodule.map_bot _⟩)
  top_mem := Finset.mem_insert_self _ _

theorem ext_carrier (H : Submodule F V) (F' : Flag F H) :
    (ext H F').carrier = insert ⊤ (F'.carrier.image (Submodule.map H.subtype)) := rfl

theorem map_subtype_injective (H : Submodule F V) :
    Function.Injective (Submodule.map H.subtype) :=
  Submodule.map_injective_of_injective H.injective_subtype

theorem top_notMem_image {H : Submodule F V} (hH : H ≠ ⊤) (F' : Flag F H) :
    (⊤ : Submodule F V) ∉ F'.carrier.image (Submodule.map H.subtype) := by
  simp only [Finset.mem_image, not_exists, not_and]
  intro x _ hx
  exact hH (top_le_iff.1 (hx ▸ Submodule.map_subtype_le H x))

theorem ext_injective {H : Submodule F V} (hH : H ≠ ⊤) : Function.Injective (ext H) := by
  intro F₁ F₂ h
  apply Flag.ext
  have hc := congrArg Flag.carrier h
  rw [ext_carrier, ext_carrier] at hc
  have : F₁.carrier.image (Submodule.map H.subtype) = F₂.carrier.image (Submodule.map H.subtype) := by
    ext W
    constructor
    · intro hW
      have h1 : W ∈ insert ⊤ (F₂.carrier.image (Submodule.map H.subtype)) :=
        hc ▸ Finset.mem_insert_of_mem hW
      rcases Finset.mem_insert.1 h1 with rfl | h1
      · exact absurd hW (top_notMem_image hH F₁)
      · exact h1
    · intro hW
      have h1 : W ∈ insert ⊤ (F₁.carrier.image (Submodule.map H.subtype)) :=
        hc.symm ▸ Finset.mem_insert_of_mem hW
      rcases Finset.mem_insert.1 h1 with rfl | h1
      · exact absurd hW (top_notMem_image hH F₂)
      · exact h1
  exact Finset.image_injective (map_subtype_injective H) this

theorem len_ext {H : Submodule F V} (hH : H ≠ ⊤) (F' : Flag F H) :
    (ext H F').len = F'.len + 1 := by
  unfold Flag.len
  rw [ext_carrier, Finset.card_insert_of_notMem (top_notMem_image hH F'),
    Finset.card_image_of_injective _ (map_subtype_injective H)]
  have := F'.carrier_card_pos
  omega

variable {v : V}

theorem ne_top_of_notMem {H : Submodule F V} (hvH : v ∉ H) : H ≠ ⊤ := fun h => hvH (h ▸ trivial)

theorem Aset_ext {H : Submodule F V} (hvH : v ∉ H) (F' : Flag F H) :
    Aset v (ext H F') = F'.carrier.image (Submodule.map H.subtype) := by
  unfold Aset
  rw [ext_carrier, Finset.filter_insert, if_neg (by simp), Finset.filter_true_of_mem]
  intro W hW hv
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hW
  exact hvH (Submodule.map_subtype_le H x hv)

theorem Am_ext {H : Submodule F V} (hvH : v ∉ H) (F' : Flag F H) : Am v (ext H F') = H := by
  unfold Am
  rw [Aset_ext hvH]
  apply le_antisymm
  · exact Finset.sup_le fun W hW => by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hW
      exact Submodule.map_subtype_le H x
  · have : H ∈ F'.carrier.image (Submodule.map H.subtype) :=
      Finset.mem_image.2 ⟨⊤, F'.top_mem, Submodule.map_subtype_top H⟩
    exact Finset.le_sup (f := id) this

theorem Xm_ext {H : Submodule F V} (hvH : v ∉ H) (hHv : H ⊔ Submodule.span F {v} = ⊤)
    (F' : Flag F H) : Xm v (ext H F') = ⊤ := by
  rw [Xm, Am_ext hvH, hHv]

/-- A bad flag is a flag of the hyperplane `A(G)`, followed by `V`. -/
theorem bad_eq_ext (hv0 : v ≠ 0) {G : Flag F V} (hG : Xm v G = ⊤) :
    ext (Am v G) (G.restrict (Am v G)) = G := by
  apply Flag.ext
  rw [ext_carrier]
  simp only [Flag.restrict, Finset.image_image]
  have hfun : (Submodule.map (Am v G).subtype ∘ Submodule.comap (Am v G).subtype) =
      fun W => Am v G ⊓ W := by
    funext W; exact Submodule.map_comap_subtype _ _
  rw [hfun]
  ext W
  simp only [Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨W₀, hW₀, rfl⟩)
    · exact G.top_mem
    · by_cases hv : v ∈ W₀
      · have : W₀ = ⊤ := top_le_iff.1 (hG ▸ Xm_le hv0 G hW₀ hv)
        rw [this, inf_top_eq]; exact Am_carrier hv0 G
      · rw [inf_eq_right.2 (le_Am G hW₀ hv)]; exact hW₀
  · intro hW
    by_cases hv : v ∈ W
    · exact Or.inl (top_le_iff.1 (hG ▸ Xm_le hv0 G hW hv))
    · exact Or.inr ⟨W, hW, inf_eq_right.2 (le_Am G hW hv)⟩

theorem map_lt_map_iff (H : Submodule F V) (A W : Submodule F H) :
    A.map H.subtype < W.map H.subtype ↔ A < W := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne,
    Submodule.map_le_map_iff_of_injective H.injective_subtype, (map_subtype_injective H).ne_iff]

theorem index_ext (H : Submodule F V) (hH : H ≠ ⊤) (F' : Flag F H) (W : Submodule F H) :
    (ext H F').index (W.map H.subtype) = F'.index W := by
  unfold Flag.index
  rw [ext_carrier, Finset.filter_insert, if_neg (not_lt_of_ge le_top)]
  have : (F'.carrier.image (Submodule.map H.subtype)).filter (· < W.map H.subtype) =
      (F'.carrier.filter (· < W)).image (Submodule.map H.subtype) := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨A, hA, rfl⟩, hlt⟩
      exact ⟨A, ⟨hA, (map_lt_map_iff H A W).1 hlt⟩, rfl⟩
    · rintro ⟨A, ⟨hA, hlt⟩, rfl⟩
      exact ⟨⟨A, hA, rfl⟩, (map_lt_map_iff H A W).2 hlt⟩
  rw [this, Finset.card_image_of_injective _ (map_subtype_injective H)]

theorem ext_erase (H : Submodule F V) (F' : Flag F H) {W : Submodule F H}
    (hW : W ≠ ⊥ ∧ W ≠ ⊤) (hW' : W.map H.subtype ≠ ⊥ ∧ W.map H.subtype ≠ ⊤) :
    (ext H F').erase (W.map H.subtype) hW' = ext H (F'.erase W hW) := by
  apply Flag.ext
  rw [erase_carrier, ext_carrier, ext_carrier, erase_carrier,
    Finset.erase_insert_of_ne (Ne.symm hW'.2), Finset.image_erase (map_subtype_injective H)]

end Ext

section Transfer

variable [Finite F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {v : V}

/-- Hyperplanes complementary to `⟨v⟩`. -/
abbrev Hyp (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] (v : V) :=
  {H : Submodule F V // v ∉ H ∧ H ⊔ Submodule.span F {v} = ⊤}

variable (v) in
/-- `Theta (u_H)_H = ∑_H ext_H(u_H)`. -/
def Theta : (∀ H : Hyp F V v, Flag F H.1 →₀ k) →ₗ[k] (Flag F V →₀ k) :=
  ∑ H : Hyp F V v, (Finsupp.lmapDomain k k (ext H.1)) ∘ₗ LinearMap.proj H

variable (v) in
/-- `rho x = (x ∘ ext_H)_H`. -/
def rho : (Flag F V →₀ k) →ₗ[k] (∀ H : Hyp F V v, Flag F H.1 →₀ k) :=
  LinearMap.pi fun H : Hyp F V v =>
    Finsupp.lcomapDomain (ext H.1) (ext_injective (ne_top_of_notMem H.2.1))

variable (v) in
/-- The boundary on `∏_H k[Fl(H)]`. -/
def bdP : (∀ H : Hyp F V v, Flag F H.1 →₀ k) →ₗ[k] (∀ H : Hyp F V v, Flag F H.1 →₀ k) :=
  LinearMap.pi fun H => bd k ∘ₗ LinearMap.proj H

theorem bdP_apply (u : ∀ H : Hyp F V v, Flag F H.1 →₀ k) (H : Hyp F V v) :
    bdP k v u H = bd k (u H) := rfl

theorem rho_apply (x : Flag F V →₀ k) (H : Hyp F V v) (F' : Flag F H.1) :
    rho k v x H F' = x (ext H.1 F') := by
  simp [rho, Finsupp.lcomapDomain, Finsupp.comapDomain_apply]

theorem Theta_eq (u : ∀ H : Hyp F V v, Flag F H.1 →₀ k) :
    Theta k v u = ∑ H : Hyp F V v, Finsupp.mapDomain (ext H.1) (u H) := by
  simp [Theta, LinearMap.sum_apply]

theorem Theta_apply (u : ∀ H : Hyp F V v, Flag F H.1 →₀ k) (G : Flag F V) :
    Theta k v u G = ∑ H : Hyp F V v, Finsupp.mapDomain (ext H.1) (u H) G := by
  rw [Theta_eq, Finsupp.finsetSum_apply]

theorem Hyp_eq_of_ext {H₁ H₂ : Hyp F V v} {F₁ : Flag F H₁.1} {F₂ : Flag F H₂.1}
    (h : ext H₁.1 F₁ = ext H₂.1 F₂) : H₁ = H₂ := by
  apply Subtype.ext
  have := congrArg (Am v) h
  rwa [Am_ext H₁.2.1, Am_ext H₂.2.1] at this

theorem Theta_ext (u : ∀ H : Hyp F V v, Flag F H.1 →₀ k) (H : Hyp F V v) (F' : Flag F H.1) :
    Theta k v u (ext H.1 F') = u H F' := by
  rw [Theta_apply, Finset.sum_eq_single H]
  · exact Finsupp.mapDomain_apply_of_injective (ext_injective (ne_top_of_notMem H.2.1)) _ _
  · intro b _ hb
    apply Finsupp.mapDomain_notin_range
    rintro ⟨F'', h⟩
    exact hb (Hyp_eq_of_ext h)
  · simp

theorem Theta_good (u : ∀ H : Hyp F V v, Flag F H.1 →₀ k) {G : Flag F V} (hG : Xm v G ≠ ⊤) :
    Theta k v u G = 0 := by
  rw [Theta_apply]
  refine Finset.sum_eq_zero fun H _ => Finsupp.mapDomain_notin_range _ _ ?_
  rintro ⟨F', rfl⟩
  exact hG (Xm_ext H.2.1 H.2.2 F')

theorem sub_Thetarho_mem_goodS (hv0 : v ≠ 0) (x : Flag F V →₀ k) :
    x - Theta k v (rho k v x) ∈ goodS k V v := by
  intro G hG
  show Xm v G ≠ ⊤
  intro hb
  apply Finsupp.mem_support_iff.1 hG
  let H : Hyp F V v := ⟨Am v G, v_notMem_Am hv0 G, hb⟩
  have hG' : ext H.1 (G.restrict (Am v G)) = G := bad_eq_ext hv0 hb
  rw [← hG', Finsupp.sub_apply, Theta_ext, rho_apply, sub_self]

theorem rho_goodS {x : Flag F V →₀ k} (hx : x ∈ goodS k V v) : rho k v x = 0 := by
  funext H
  ext F'
  rw [rho_apply]
  simp only [Pi.zero_apply, Finsupp.coe_zero]
  by_contra h
  exact hx (Finsupp.mem_support_iff.2 h) (Xm_ext H.2.1 H.2.2 F')

theorem rho_Theta (u : ∀ H : Hyp F V v, Flag F H.1 →₀ k) : rho k v (Theta k v u) = u := by
  funext H
  ext F'
  rw [rho_apply, Theta_ext]

theorem finrank_Hyp (hv0 : v ≠ 0) (H : Hyp F V v) : finrank F H.1 + 1 = finrank F V := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq H.1 (Submodule.span F {v})
  rw [H.2.2, finrank_top, finrank_span_singleton hv0,
    disjoint_iff.1 ((Submodule.disjoint_span_singleton' hv0).2 H.2.1), finrank_bot] at h
  omega

theorem Xm_ext_erase (hv0 : v ≠ 0) (H : Hyp F V v) (F' : Flag F H.1) (h : H.1 ≠ ⊥ ∧ H.1 ≠ ⊤) :
    Xm v ((ext H.1 F').erase H.1 h) ≠ ⊤ := by
  intro hX
  set G' := (ext H.1 F').erase H.1 h
  have hmem := Am_mem hv0 G'
  rw [Aset_erase, Aset_ext H.2.1] at hmem
  have hne : Am v G' ≠ H.1 := Finset.ne_of_mem_erase hmem
  obtain ⟨x, _, hx⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hmem)
  have hle : Am v G' ≤ H.1 := hx ▸ Submodule.map_subtype_le H.1 x
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (Am v G') (Submodule.span F {v})
  rw [show Am v G' ⊔ Submodule.span F {v} = ⊤ from hX, finrank_top,
    finrank_span_singleton hv0] at h2
  have := finrank_Hyp hv0 H
  omega

theorem bd_ext_sub (hv0 : v ≠ 0) (H : Hyp F V v) (y : Flag F H.1 →₀ k) :
    bd k (Finsupp.lmapDomain k k (ext H.1) y) - Finsupp.lmapDomain k k (ext H.1) (bd k y) ∈
      goodS k V v := by
  have := map_supported_le k ((bd k) ∘ₗ (Finsupp.lmapDomain k k (ext H.1)) -
    (Finsupp.lmapDomain k k (ext H.1)) ∘ₗ (bd k)) Set.univ (goodS k V v) ?_ y (by simp)
  · simpa using this
  intro F' _
  have hHt := ne_top_of_notMem H.2.1
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, bd_single, ext_carrier,
    Finset.sum_insert (top_notMem_image hHt F'),
    Finset.sum_image (fun x _ y _ h => map_subtype_injective H.1 h), map_sum]
  have h0 : face k (ext H.1 F') ⊤ = 0 := by simp [face]
  rw [h0, zero_add, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun W' _ => ?_
  by_cases hWt : W' = ⊤
  · subst hWt
    have : face k F' ⊤ = 0 := by simp [face]
    rw [this, Finsupp.mapDomain_zero, sub_zero, Submodule.map_subtype_top]
    unfold face
    split_ifs with h
    · exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported k _ (Xm_ext_erase hv0 H F' h))
    · exact zero_mem _
  by_cases hWb : W' = ⊥
  · subst hWb
    simp [face]
  have hW : W' ≠ ⊥ ∧ W' ≠ ⊤ := ⟨hWb, hWt⟩
  have hW' : W'.map H.1.subtype ≠ ⊥ ∧ W'.map H.1.subtype ≠ ⊤ := by
    refine ⟨fun h => hWb ?_, fun h => hHt (top_le_iff.1 (h.symm.le.trans (Submodule.map_subtype_le H.1 W')))⟩
    exact map_subtype_injective H.1 (h.trans (Submodule.map_bot _).symm)
  unfold face
  rw [dif_pos hW', dif_pos hW, Finsupp.mapDomain_smul, Finsupp.mapDomain_single,
    ext_erase H.1 F' hW hW', index_ext H.1 hHt, sub_self]
  exact zero_mem _

theorem bd_Theta_sub (hv0 : v ≠ 0) (u : ∀ H : Hyp F V v, Flag F H.1 →₀ k) :
    bd k (Theta k v u) - Theta k v (bdP k v u) ∈ goodS k V v := by
  rw [Theta_eq, Theta_eq, map_sum, ← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun H _ => by simpa [bdP_apply] using bd_ext_sub k hv0 H (u H)

theorem rho_bd (hv0 : v ≠ 0) (z : Flag F V →₀ k) : rho k v (bd k z) = bdP k v (rho k v z) := by
  have hg := sub_Thetarho_mem_goodS k hv0 z
  have h1 := rho_goodS k (bd_mem_goodS k hg)
  have h2 := rho_goodS k (bd_Theta_sub k hv0 (rho k v z))
  rw [map_sub, rho_Theta, sub_eq_zero] at h2
  rw [map_sub, map_sub, sub_eq_zero] at h1
  rw [h1, h2]

theorem rho_deg {m : ℕ} {z : Flag F V →₀ k} (hz : z ∈ deg k V (m + 1)) (H : Hyp F V v) :
    rho k v z H ∈ deg k H.1 m := by
  intro F' hF'
  rw [Finset.mem_coe, Finsupp.mem_support_iff, rho_apply] at hF'
  have := hz (Finsupp.mem_support_iff.2 hF')
  simp only [Set.mem_setOf_eq, len_ext (ne_top_of_notMem H.2.1)] at this
  simpa using this

theorem rho_deg_zero {z : Flag F V →₀ k} (hz : z ∈ deg k V 0) : rho k v z = 0 := by
  funext H
  ext F'
  rw [rho_apply]
  simp only [Pi.zero_apply, Finsupp.coe_zero]
  by_contra h
  have := hz (Finsupp.mem_support_iff.2 h)
  simp [len_ext (ne_top_of_notMem H.2.1)] at this

theorem Theta_deg {m : ℕ} {u : ∀ H : Hyp F V v, Flag F H.1 →₀ k} (hu : ∀ H, u H ∈ deg k H.1 m) :
    Theta k v u ∈ deg k V (m + 1) := by
  rw [Theta_eq]
  refine Submodule.sum_mem _ fun H _ => ?_
  rw [← Finsupp.lmapDomain_apply (M := k) (R := k)]
  exact map_supported_le k (Finsupp.lmapDomain k k (ext H.1)) _ _ (fun F' hF' => by
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    refine Finsupp.single_mem_supported k _ ?_
    show (ext H.1 F').len = m + 1
    rw [len_ext (ne_top_of_notMem H.2.1)]; simpa using hF') (u H) (hu H)

end Transfer

section Eps

/-- `(-1)^{inv σ}` is the sign of `σ` (as computed by `Equiv.Perm.signAux`). -/
theorem negOnePow_inv {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    (-1 : k) ^ inv σ = ((Equiv.Perm.signAux σ : ℤ) : k) := by
  have h : ((Equiv.Perm.signAux σ : ℤˣ) : ℤ) = (-1) ^ inv σ := by
    rw [Equiv.Perm.signAux, Units.coe_prod]
    simp only [apply_ite (fun u : ℤˣ => (u : ℤ)), Units.val_neg, Units.val_one]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 1
    unfold inv
    refine Finset.card_bij (fun x _ => (x.2, x.1)) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Equiv.Perm.mem_finPairsLT] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hx.1, lt_of_le_of_ne hx.2 (fun h => (ne_of_gt hx.1) (σ.injective h))⟩
    · intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      exact Sigma.ext h.2 (heq_of_eq h.1)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨⟨p.2, p.1⟩, by simpa [Equiv.Perm.mem_finPairsLT] using ⟨hp.1, hp.2.le⟩, rfl⟩
  rw [h]; push_cast; rfl

theorem negOnePow_inv_mul_swap {d : ℕ} (σ : Equiv.Perm (Fin d)) {a b : Fin d} (hab : a ≠ b) :
    (-1 : k) ^ inv (σ * Equiv.swap a b) = -(-1 : k) ^ inv σ := by
  rw [negOnePow_inv, negOnePow_inv, Equiv.Perm.signAux_mul, Equiv.Perm.signAux_swap hab]
  push_cast; ring

variable {V : Type} [AddCommGroup V] [Module F V]

/-- The flag `(⟨b₁⟩ < ⟨b₁,b₂⟩ < ⋯)` of a basis. -/
def flagOf {d : ℕ} (b : Module.Basis (Fin d) F V) : Flag F V where
  carrier := Finset.univ.image b.flag
  isChain := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact b.isChain_range_flag
  bot_mem := Finset.mem_image.2 ⟨0, Finset.mem_univ _, b.flag_zero⟩
  top_mem := Finset.mem_image.2 ⟨Fin.last d, Finset.mem_univ _, b.flag_last⟩

theorem flagOf_carrier {d : ℕ} (b : Module.Basis (Fin d) F V) :
    (flagOf b).carrier = Finset.univ.image b.flag := rfl

theorem len_flagOf {d : ℕ} (b : Module.Basis (Fin d) F V) : (flagOf b).len = d := by
  unfold Flag.len
  rw [flagOf_carrier, Finset.card_image_of_injective _ b.flag_strictMono.injective]
  simp

theorem index_flagOf {d : ℕ} (b : Module.Basis (Fin d) F V) (i : Fin (d + 1)) :
    (flagOf b).index (b.flag i) = i.val := by
  unfold Flag.index
  rw [flagOf_carrier]
  have : (Finset.univ.image b.flag).filter (· < b.flag i) =
      (Finset.univ.filter (· < i)).image b.flag := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, rfl⟩, h⟩; exact ⟨j, b.flag_strictMono.lt_iff_lt.1 h, rfl⟩
    · rintro ⟨j, h, rfl⟩; exact ⟨⟨j, rfl⟩, b.flag_strictMono h⟩
  rw [this, Finset.card_image_of_injective _ b.flag_strictMono.injective,
    Finset.filter_gt_eq_Iio, Fin.card_Iio]

theorem flagOf_mid {d : ℕ} (b : Module.Basis (Fin d) F V) (i : Fin (d + 1)) :
    (b.flag i ≠ ⊥ ∧ b.flag i ≠ ⊤) ↔ (0 < i.val ∧ i.val < d) := by
  rw [← b.flag_zero, ← b.flag_last, b.flag_strictMono.injective.ne_iff,
    b.flag_strictMono.injective.ne_iff, Ne, Ne, Fin.ext_iff, Fin.ext_iff]
  simp only [Fin.val_zero, Fin.val_last]
  omega

/-- `ε_b = ∑_σ (-1)^{inv σ} e_{flag(b∘σ)}`. -/
def eps {d : ℕ} (b : Module.Basis (Fin d) F V) : Flag F V →₀ k :=
  ∑ σ : Equiv.Perm (Fin d), ((-1 : k) ^ inv σ) • Finsupp.single (flagOf (b.reindex σ.symm)) 1

theorem eps_mem_deg {d : ℕ} (b : Module.Basis (Fin d) F V) : eps k b ∈ deg k V d :=
  Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _
    (Finsupp.single_mem_supported k _ (len_flagOf _))

/-- The adjacent transposition `(i-1, i)` for an intermediate position `i`. -/
def adjSwap {d : ℕ} (i : Fin (d + 1)) : Equiv.Perm (Fin d) :=
  if h : 0 < i.val ∧ i.val < d then Equiv.swap ⟨i.val - 1, by omega⟩ ⟨i.val, h.2⟩ else 1

theorem flag_reindex_swap {d : ℕ} (b : Module.Basis (Fin d) F V) (σ : Equiv.Perm (Fin d))
    (i j : Fin (d + 1)) (hij : j ≠ i) :
    (b.reindex (σ * adjSwap i).symm).flag j = (b.reindex σ.symm).flag j := by
  unfold Module.Basis.flag
  congr 1
  have hinv : ∀ m : Fin d, (adjSwap i m).castSucc < j ↔ m.castSucc < j := by
    intro m
    unfold adjSwap
    split_ifs with h
    · rw [Equiv.swap_apply_def]
      split_ifs with h1 h2 <;> simp only [Fin.lt_def, Fin.coe_castSucc] at * <;>
        (try subst h1) <;> (try subst h2) <;> simp_all [Fin.ext_iff] <;> omega
    · rfl
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Module.Basis.reindex_apply, Equiv.symm_symm,
    Equiv.Perm.coe_mul, Function.comp_apply]
  constructor
  · rintro ⟨m, hm, rfl⟩; exact ⟨adjSwap i m, (hinv m).2 hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨adjSwap i m, ?_, ?_⟩
    · exact (hinv m).2 hm
    · unfold adjSwap; split_ifs <;> simp

theorem erase_flagOf_swap {d : ℕ} (b : Module.Basis (Fin d) F V) (σ : Equiv.Perm (Fin d))
    (i : Fin (d + 1)) (h₁ h₂) :
    (flagOf (b.reindex (σ * adjSwap i).symm)).erase
        ((b.reindex (σ * adjSwap i).symm).flag i) h₁ =
      (flagOf (b.reindex σ.symm)).erase ((b.reindex σ.symm).flag i) h₂ := by
  apply Flag.ext
  rw [erase_carrier, erase_carrier, flagOf_carrier, flagOf_carrier,
    ← Finset.image_erase (b.reindex _).flag_strictMono.injective,
    ← Finset.image_erase (b.reindex _).flag_strictMono.injective]
  exact Finset.image_congr fun j hj => flag_reindex_swap b σ i j (Finset.ne_of_mem_erase hj)

theorem bd_eps {d : ℕ} (b : Module.Basis (Fin d) F V) : bd k (eps k b) = 0 := by
  unfold eps
  simp only [map_sum, map_smul, bd_single, flagOf_carrier]
  simp only [Finset.sum_image (fun x _ y _ h => (Module.Basis.flag_strictMono _).injective h),
    Finset.smul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => (p.1 * adjSwap p.2, p.2)) ?_ ?_ (by simp) ?_
  · rintro ⟨σ, i⟩ _
    simp only
    unfold face
    by_cases hm : 0 < i.val ∧ i.val < d
    · have h₁ := (flagOf_mid (b.reindex (σ * adjSwap i).symm) i).2 hm
      have h₂ := (flagOf_mid (b.reindex σ.symm) i).2 hm
      rw [dif_pos h₂, dif_pos h₁, erase_flagOf_swap b σ i h₁ h₂, index_flagOf, index_flagOf,
        smul_smul, smul_smul, ← add_smul]
      have hs : adjSwap i = Equiv.swap (⟨i.val - 1, by omega⟩ : Fin d) ⟨i.val, hm.2⟩ := by
        simp [adjSwap, hm]
      rw [hs, negOnePow_inv_mul_swap k σ (by simp [Fin.ext_iff]; omega)]
      simp
    · have h₁ : ¬ ((b.reindex σ.symm).flag i ≠ ⊥ ∧ (b.reindex σ.symm).flag i ≠ ⊤) :=
        fun h => hm ((flagOf_mid _ i).1 h)
      have h₂ : ¬ ((b.reindex (σ * adjSwap i).symm).flag i ≠ ⊥ ∧
          (b.reindex (σ * adjSwap i).symm).flag i ≠ ⊤) := fun h => hm ((flagOf_mid _ i).1 h)
      rw [dif_neg h₁, dif_neg h₂]; simp
  · rintro ⟨σ, i⟩ _ hne heq
    apply hne
    simp only [Prod.mk.injEq, mul_eq_left] at heq
    unfold face
    by_cases hm : 0 < i.val ∧ i.val < d
    · exfalso
      have : adjSwap i ≠ 1 := by
        simp only [adjSwap, hm, and_self, dite_true, ne_eq, Equiv.swap_eq_one_iff]
        simp [Fin.ext_iff]; omega
      exact this heq.1
    · rw [dif_neg (fun h => hm ((flagOf_mid _ i).1 h))]; simp
  · rintro ⟨σ, i⟩ _
    simp only [Prod.mk.injEq, and_true, mul_assoc]
    unfold adjSwap
    split_ifs <;> simp

theorem eps_mem_St {d : ℕ} (b : Module.Basis (Fin d) F V) :
    eps k b ∈ deg k V d ⊓ LinearMap.ker (bd k) :=
  ⟨eps_mem_deg k b, bd_eps k b⟩

theorem smul_flagOf {d : ℕ} (b : Module.Basis (Fin d) F V) (g : V ≃ₗ[F] V) :
    g • flagOf b = flagOf (b.map g) := by
  apply Flag.ext
  show (Flag.map g (flagOf b)).carrier = _
  simp only [Flag.map, flagOf_carrier, Finset.image_image]
  exact Finset.image_congr fun i _ => (Module.Basis.flag_map b g i).symm

theorem lmapDomain_smul_eps {d : ℕ} (b : Module.Basis (Fin d) F V) (g : V ≃ₗ[F] V) :
    Finsupp.lmapDomain k k (g • ·) (eps k b) = eps k (b.map g) := by
  unfold eps
  simp only [map_sum, map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, smul_flagOf]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3

end Eps

section Gen

/-- Extend a permutation of `Fin n` by fixing `last n`. -/
def liftPerm {n : ℕ} (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.lastCases (Fin.last n) (fun j => (τ j).castSucc)
  invFun := Fin.lastCases (Fin.last n) (fun j => (τ.symm j).castSucc)
  left_inv i := by cases i using Fin.lastCases <;> simp
  right_inv i := by cases i using Fin.lastCases <;> simp

@[simp] theorem liftPerm_last {n : ℕ} (τ : Equiv.Perm (Fin n)) : liftPerm τ (Fin.last n) = Fin.last n := by
  simp [liftPerm]

@[simp] theorem liftPerm_castSucc {n : ℕ} (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    liftPerm τ j.castSucc = (τ j).castSucc := by
  simp [liftPerm]

theorem liftPerm_injective {n : ℕ} : Function.Injective (liftPerm (n := n)) := by
  intro τ₁ τ₂ h
  refine Equiv.ext fun j => ?_
  have := congrArg (fun σ => σ j.castSucc) h
  simpa using this

theorem inv_liftPerm {n : ℕ} (τ : Equiv.Perm (Fin n)) : inv (liftPerm τ) = inv τ := by
  unfold inv
  symm
  refine Finset.card_bij (fun p _ => (p.1.castSucc, p.2.castSucc)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    simpa using hp
  · intro p _ q _ h
    simp only [Prod.mk.injEq, Fin.castSucc_inj] at h
    exact Prod.ext h.1 h.2
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨a, b⟩ := p
    cases b using Fin.lastCases with
    | last =>
      exfalso
      cases a using Fin.lastCases with
      | last => exact lt_irrefl _ hp.1
      | cast a' =>
        have h2 := hp.2
        simp only [liftPerm_last, liftPerm_castSucc] at h2
        exact absurd h2 (not_lt_of_ge (Fin.castSucc_lt_last _).le)
    | cast b' =>
      cases a using Fin.lastCases with
      | last => exact absurd hp.1 (not_lt_of_ge (Fin.castSucc_lt_last _).le)
      | cast a' =>
        refine ⟨(a', b'), ?_, rfl⟩
        simpa using hp

theorem filter_fix_last {n : ℕ} :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n) = Fin.last n) =
      Finset.univ.image liftPerm := by
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    have hne : ∀ j : Fin n, σ j.castSucc ≠ Fin.last n := fun j hj =>
      (Fin.castSucc_lt_last j).ne (σ.injective (hj.trans h.symm))
    let τ : Equiv.Perm (Fin n) :=
      { toFun := fun j => (σ j.castSucc).castPred (hne j)
        invFun := fun j => (σ.symm j.castSucc).castPred (fun hj => (Fin.castSucc_lt_last j).ne
          (by rw [← h, ← hj, Equiv.apply_symm_apply]))
        left_inv := fun j => by simp
        right_inv := fun j => by simp }
    refine ⟨τ, ?_⟩
    ext i
    cases i using Fin.lastCases <;> simp [τ, h]
  · rintro ⟨τ, rfl⟩; simp

variable [Finite F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {v : V}

/-- The basis `(b'₁, …, b'ₙ, v)` of `V` for a basis `b'` of a complement `H` of `⟨v⟩`. -/
def consBasis {n : ℕ} (H : Hyp F V v) (b' : Module.Basis (Fin n) F H.1) :
    Module.Basis (Fin (n + 1)) F V :=
  (Module.Basis.mkFinCons v b'
    (fun c x hx h => by
      by_contra hc
      apply H.2.1
      have hcv : c • v ∈ H.1 := by rw [eq_neg_of_add_eq_zero_left h]; exact H.1.neg_mem hx
      have := H.1.smul_mem c⁻¹ hcv
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this)
    (fun z => by
      have hz : z ∈ H.1 ⊔ Submodule.span F {v} := by rw [H.2.2]; exact Submodule.mem_top
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
      exact ⟨-a, by rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]; exact hy⟩)
    ).reindex (finRotate (n + 1)).symm

theorem consBasis_apply {n : ℕ} (H : Hyp F V v) (b' : Module.Basis (Fin n) F H.1)
    (i : Fin (n + 1)) : consBasis H b' i = @Fin.snoc n (fun _ => V) (fun j => (b' j : V)) v i := by
  rw [consBasis, Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.coe_mkFinCons,
    Fin.snoc_eq_cons_rotate]
  rfl

theorem reindex_apply' {d : ℕ} (b : Module.Basis (Fin d) F V) (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    b.reindex σ.symm i = b (σ i) := by
  rw [Module.Basis.reindex_apply, Equiv.symm_symm]

theorem good_of_not_fix (hv0 : v ≠ 0) {n : ℕ} (H : Hyp F V v) (b' : Module.Basis (Fin n) F H.1)
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : σ (Fin.last n) ≠ Fin.last n) :
    Xm v (flagOf ((consBasis H b').reindex σ.symm)) ≠ ⊤ := by
  set c := (consBasis H b').reindex σ.symm
  set M := c.flag (Fin.last n).castSucc
  have hMmem : M ∈ (flagOf c).carrier := Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
  have hvM : v ∈ M := by
    have hi : (σ.symm (Fin.last n)).castSucc < (Fin.last n).castSucc := by
      rw [Fin.castSucc_lt_castSucc_iff, Fin.lt_last_iff_ne_last]
      intro h; apply hσ
      have := congrArg σ h; rw [Equiv.apply_symm_apply] at this; exact this.symm
    have := c.self_mem_flag hi
    rwa [show c (σ.symm (Fin.last n)) = v by
      rw [reindex_apply', Equiv.apply_symm_apply, consBasis_apply, Fin.snoc_last]] at this
  have hMt : M ≠ ⊤ := by
    rw [← c.flag_last]
    exact (c.flag_strictMono (Fin.castSucc_lt_last _)).ne
  intro hX
  exact hMt (top_le_iff.1 (hX ▸ Xm_le hv0 _ hMmem hvM))

theorem flag_lift_castSucc {n : ℕ} (H : Hyp F V v) (b' : Module.Basis (Fin n) F H.1)
    (τ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    ((consBasis H b').reindex (liftPerm τ).symm).flag j.castSucc =
      ((b'.reindex τ.symm).flag j).map H.1.subtype := by
  unfold Module.Basis.flag
  rw [Submodule.map_span]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, reindex_apply', Fin.castSucc_lt_castSucc_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    cases m using Fin.lastCases with
    | last => exact absurd hm (not_lt_of_ge (Fin.le_last _))
    | cast m' =>
      refine ⟨b' (τ m'), ⟨m', hm, rfl⟩, ?_⟩
      rw [liftPerm_castSucc, consBasis_apply, Fin.snoc_castSucc]; rfl
  · rintro ⟨y, ⟨m', hm, rfl⟩, rfl⟩
    refine ⟨m'.castSucc, hm, ?_⟩
    rw [liftPerm_castSucc, consBasis_apply, Fin.snoc_castSucc]; rfl

theorem flagOf_lift {n : ℕ} (H : Hyp F V v) (b' : Module.Basis (Fin n) F H.1)
    (τ : Equiv.Perm (Fin n)) :
    flagOf ((consBasis H b').reindex (liftPerm τ).symm) = ext H.1 (flagOf (b'.reindex τ.symm)) := by
  apply Flag.ext
  rw [flagOf_carrier, ext_carrier, flagOf_carrier, Finset.image_image]
  ext W
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    cases i using Fin.lastCases with
    | last => left; exact Module.Basis.flag_last _
    | cast j => right; exact ⟨j, (flag_lift_castSucc H b' τ j).symm⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨Fin.last _, Module.Basis.flag_last _⟩
    · exact ⟨j.castSucc, flag_lift_castSucc H b' τ j⟩

theorem rho_single_ext (H : Hyp F V v) (F' : Flag F H.1) :
    rho k v (Finsupp.single (ext H.1 F') 1) = Pi.single H (Finsupp.single F' 1) := by
  funext H'
  ext F''
  rw [rho_apply]
  by_cases h : H' = H
  · subst h
    simp only [Pi.single_eq_same, Finsupp.single_apply,
      (ext_injective (ne_top_of_notMem H'.2.1)).eq_iff]
  · rw [Pi.single_eq_of_ne h, Finsupp.single_apply, if_neg (fun he => h (Hyp_eq_of_ext he).symm)]
    rfl

theorem rho_eps_cons (hv0 : v ≠ 0) {n : ℕ} (H : Hyp F V v) (b' : Module.Basis (Fin n) F H.1) :
    rho k v (eps k (consBasis H b')) = Pi.single H (eps k b') := by
  unfold eps
  rw [map_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n) = Fin.last n)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun σ => ¬ _) (fun σ hσ => by
    rw [map_smul, rho_goodS k (Finsupp.single_mem_supported k _
      (good_of_not_fix hv0 H b' (Finset.mem_filter.1 hσ).2)), smul_zero]), add_zero,
    filter_fix_last, Finset.sum_image (fun x _ y _ h => liftPerm_injective h)]
  have hs : ∀ (f : Equiv.Perm (Fin n) → (Flag F H.1 →₀ k)),
      (Pi.single H (∑ τ, f τ) : ∀ H : Hyp F V v, Flag F H.1 →₀ k) = ∑ τ, Pi.single H (f τ) :=
    fun f => map_sum (LinearMap.single k (fun H : Hyp F V v => Flag F H.1 →₀ k) H) f _
  rw [hs]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_smul, flagOf_lift, rho_single_ext, inv_liftPerm, Pi.single_smul]

end Gen

section Main

variable [Fintype F]

theorem natCard_Hyp {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {v : V}
    (hv0 : v ≠ 0) : Nat.card (Hyp F V v) = Fintype.card F ^ (finrank F V - 1) := by
  set p := Submodule.span F {v}
  have e1 : Hyp F V v ≃ {H : Submodule F V // IsCompl p H} :=
    Equiv.subtypeEquivRight fun H => by
      rw [isCompl_iff, disjoint_comm, Submodule.disjoint_span_singleton' hv0, codisjoint_iff,
        sup_comm]
  obtain ⟨K0, hK⟩ := Submodule.exists_isCompl p
  have e3 : {f : V →ₗ[F] p // ∀ x : p, f x = x} ≃ (K0 →ₗ[F] p) :=
    { toFun := fun f => f.1 ∘ₗ K0.subtype
      invFun := fun g => ⟨LinearMap.ofIsCompl hK LinearMap.id g,
        fun x => by simp [LinearMap.ofIsCompl_apply_left]⟩
      left_inv := fun f => Subtype.ext (LinearMap.ofIsCompl_eq' hK (by ext x; simp [f.2]) rfl)
      right_inv := fun g => by ext x; simp [LinearMap.ofIsCompl_apply_right] }
  rw [Nat.card_congr (e1.trans ((Submodule.isComplEquivProj p).trans e3))]
  haveI : Finite (K0 →ₗ[F] p) := Module.finite_of_finite F
  letI := Fintype.ofFinite (K0 →ₗ[F] p)
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F) (V := K0 →ₗ[F] p),
    Module.finrank_linearMap,
    finrank_span_singleton hv0, mul_one]
  have := Submodule.finrank_add_eq_of_isCompl hK
  rw [finrank_span_singleton hv0] at this
  congr 1; omega

theorem len_le_finrank {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (G : Flag F V) : G.len ≤ finrank F V := by
  have h : ∀ i ≤ G.len, i ≤ finrank F (G.nth i) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have := G.finrank_nth_lt (i := i) (by omega)
      have := ih (by omega)
      omega
  have := h G.len le_rfl
  rwa [G.nth_len, finrank_top] at this

variable (F) in
/-- Top-degree cycles `St(V) = H̃_{n-2}`. -/
def St (V : Type) [AddCommGroup V] [Module F V] (n : ℕ) : Submodule k (Flag F V →₀ k) :=
  deg (F := F) k V n ⊓ LinearMap.ker (bd k)

variable (F) in
/-- The statement proved by induction on `n = dim V`. -/
def Claim (V : Type) [AddCommGroup V] [Module F V] (n : ℕ) : Prop :=
  (∀ m, m ≠ n → ∀ z ∈ deg (F := F) k V m, bd k z = 0 → ∃ y ∈ deg k V (m + 1), bd k y = z) ∧
    finrank k (St F k V n) = Fintype.card F ^ n.choose 2 ∧
    St F k V n = Submodule.span k (Set.range fun b : Module.Basis (Fin n) F V => eps k b)

theorem free_sub {M : Type} [AddCommGroup M] [Module k M] (p : Submodule k M) :
    Module.Free k p := inferInstance

theorem claim_zero (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : finrank F V = 0) : Claim F k V 0 := by
  haveI : Subsingleton V := finrank_zero_iff.1 hV
  have hsub : ∀ W : Submodule F V, W = ⊥ := fun W => Submodule.eq_bot_of_subsingleton
  have hcar : ∀ G : Flag F V, G.carrier = {⊥} := fun G => by
    ext W; rw [hsub W]; simp [G.bot_mem]
  have hlen : ∀ G : Flag F V, G.len = 0 := fun G => by simp [Flag.len, hcar G]
  have hbd : ∀ z : Flag F V →₀ k, bd k z = 0 := fun z => by
    have := map_supported_le k (bd k) Set.univ ⊥ (fun G _ => by
      rw [bd_single]
      refine Finset.sum_eq_zero fun W _ => ?_
      simp [face, hsub W]) z (by simp)
    simpa using this
  haveI : Unique (Flag F V) := ⟨⟨Flag.trivial⟩, fun G => Flag.ext (by rw [hcar, hcar])⟩
  have htop : St F k V 0 = ⊤ := by
    rw [St, eq_top_iff]
    intro z _
    exact ⟨fun G _ => hlen G, hbd z⟩
  refine ⟨fun m hm z hz _ => ⟨0, zero_mem _, ?_⟩, ?_, ?_⟩
  · have : z = 0 := by
      refine Finsupp.ext fun G => ?_
      by_contra h
      exact hm ((hz (Finsupp.mem_support_iff.2 h)).symm.trans (hlen G))
    simp [this]
  · rw [htop, finrank_top, Module.finrank_finsupp_self, Fintype.card_unique]
    simp
  · rw [htop, eq_comm, eq_top_iff]
    intro z _
    let b0 : Module.Basis (Fin 0) F V := Module.finBasisOfFinrankEq F V hV
    have he : eps k b0 = Finsupp.single (flagOf b0) 1 := by
      simp [eps, inv, Subsingleton.elim (flagOf (b0.reindex _)) (flagOf b0)]
    have hz : z = z (flagOf b0) • eps k b0 := by
      rw [he]; refine Finsupp.ext fun G => ?_; rw [Subsingleton.elim G (flagOf b0)]; simp
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b0, rfl⟩)

theorem claim_succ (n : ℕ)
    (ih : ∀ (W : Type) [AddCommGroup W] [Module F W] [FiniteDimensional F W],
      finrank F W = n → Claim F k W n)
    (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : finrank F V = n + 1) : Claim F k V (n + 1) := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨v, hv0⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
  have hH : ∀ H : Hyp F V v, finrank F H.1 = n := fun H => by
    have := finrank_Hyp hv0 H; omega
  have IH : ∀ H : Hyp F V v, Claim F k H.1 n := fun H => ih H.1 (hH H)
  -- no flags of length `n + 2`
  have hnone : ∀ y ∈ deg (F := F) k V (n + 2), y = 0 := by
    intro y hy
    ext G; by_contra h
    have := hy (Finsupp.mem_support_iff.2 h)
    have := len_le_finrank G
    simp_all
  have hzero : ∀ z ∈ St F k V (n + 1), rho k v z = 0 → z = 0 := by
    intro z hz h0
    have hg : z ∈ goodS k V v := by simpa [h0] using sub_Thetarho_mem_goodS k hv0 z
    obtain ⟨y, _, hyd, hy⟩ := good_acyclic k hv0 hg hz.1 hz.2
    rw [← hy, hnone y hyd, map_zero]
  have hrhoSt : ∀ z ∈ St F k V (n + 1), ∀ H : Hyp F V v, rho k v z H ∈ St F k H.1 n := by
    intro z hz H
    refine ⟨rho_deg k hz.1 H, ?_⟩
    have := congrFun (rho_bd k hv0 z) H
    rw [hz.2, map_zero] at this
    exact this.symm
  refine ⟨?_, ?_, ?_⟩
  · -- exactness
    intro m hm z hz hbz
    have hb : bdP k v (rho k v z) = 0 := by rw [← rho_bd k hv0, hbz, map_zero]
    have hu : ∀ H : Hyp F V v, ∃ y ∈ deg k H.1 m, bd k y = rho k v z H := by
      intro H
      cases m with
      | zero => exact ⟨0, zero_mem _, by rw [rho_deg_zero k hz]; simp⟩
      | succ m₀ =>
        exact (IH H).1 m₀ (by omega) _ (rho_deg k hz H) (congrFun hb H)
    choose u' hu'd hu'b using hu
    set z' := z - bd k (Theta k v u') with hz'
    have hrho : rho k v z' = 0 := by
      rw [hz', map_sub, rho_bd k hv0, rho_Theta, sub_eq_zero]
      funext H; exact (hu'b H).symm
    have hz'g : z' ∈ goodS k V v := by
      simpa [hrho] using sub_Thetarho_mem_goodS k hv0 z'
    have hz'd : z' ∈ deg k V m := Submodule.sub_mem _ hz (bd_mem_deg k (Theta_deg k hu'd))
    have hz'b : bd k z' = 0 := by rw [hz', map_sub, bd_bd, hbz, sub_zero]
    obtain ⟨y, _, hyd, hy⟩ := good_acyclic k hv0 hz'g hz'd hz'b
    refine ⟨y + Theta k v u', Submodule.add_mem _ hyd (Theta_deg k hu'd), ?_⟩
    rw [map_add, hy, hz', sub_add_cancel]
  · -- dimension: `St(V) ≅ ∏_H St(H)`
    let f : St F k V (n + 1) →ₗ[k] (∀ H : Hyp F V v, St F k H.1 n) :=
      LinearMap.pi fun H =>
        { toFun := fun z => ⟨rho k v z.1 H, hrhoSt z.1 z.2 H⟩
          map_add' := fun x y => by ext; simp
          map_smul' := fun c x => by ext; simp }
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      have h0 : rho k v z.1 = 0 := by
        funext H
        have := congrFun hz H
        simpa [f] using congrArg Subtype.val this
      ext1; exact hzero z.1 z.2 h0
    have hsurj : Function.Surjective f := by
      intro w
      let u : ∀ H : Hyp F V v, Flag F H.1 →₀ k := fun H => (w H).1
      have hud : ∀ H, u H ∈ deg k H.1 n := fun H => (w H).2.1
      have hbu : bdP k v u = 0 := by funext H; exact (w H).2.2
      have hg := bd_Theta_sub k hv0 u
      rw [hbu, map_zero, sub_zero] at hg
      have hgd : bd k (Theta k v u) ∈ deg k V n := bd_mem_deg k (Theta_deg k hud)
      obtain ⟨y, hyg, hyd, hy⟩ := good_acyclic k hv0 hg hgd (bd_bd k _)
      refine ⟨⟨Theta k v u - y, Submodule.sub_mem _ (Theta_deg k hud) hyd, ?_⟩, ?_⟩
      · show bd k (Theta k v u - y) = 0
        rw [map_sub, hy, sub_self]
      · funext H
        apply Subtype.ext
        show rho k v (Theta k v u - y) H = u H
        rw [map_sub, rho_Theta, rho_goodS k hyg, sub_zero]
    have e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
    haveI : ∀ H : Hyp F V v, Module.Free k (St F k H.1 n) := fun H => free_sub k _
    haveI : ∀ H : Hyp F V v, Module.Finite k (St F k H.1 n) :=
      fun _ => FiniteDimensional.finiteDimensional_submodule _
    rw [e.finrank_eq, Module.finrank_pi_fintype]
    simp only [fun H => (IH H).2.1, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Nat.card_eq_fintype_card, natCard_Hyp hv0, hV, Nat.add_sub_cancel, ← pow_add,
      Nat.choose_succ_succ, Nat.choose_one_right]
  · -- generation by the `ε_b`
    set S := Submodule.span k (Set.range fun b : Module.Basis (Fin (n + 1)) F V => eps k b)
    have hS : S ≤ St F k V (n + 1) :=
      Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact eps_mem_St k b)
    refine le_antisymm ?_ hS
    intro z hz
    let L : ∀ H : Hyp F V v, (Flag F H.1 →₀ k) →ₗ[k] (∀ H : Hyp F V v, Flag F H.1 →₀ k) :=
      fun H => LinearMap.single k (fun H : Hyp F V v => Flag F H.1 →₀ k) H
    have hsingle : ∀ H : Hyp F V v, ∀ x ∈ St F k H.1 n, L H x ∈ S.map (rho k v) := by
      intro H x hx
      rw [(IH H).2.2] at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b', rfl⟩ := hy
        exact ⟨eps k (consBasis H b'), Submodule.subset_span ⟨_, rfl⟩, rho_eps_cons k hv0 H b'⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
    have hmem : rho k v z ∈ S.map (rho k v) := by
      rw [← Finset.univ_sum_single (rho k v z)]
      exact Submodule.sum_mem _ fun H _ => hsingle H _ (hrhoSt z hz H)
    obtain ⟨s, hs, hsz⟩ := hmem
    have : z - s = 0 :=
      hzero (z - s) (Submodule.sub_mem _ hz (hS hs)) (by rw [map_sub, hsz, sub_self])
    rw [sub_eq_zero.1 this]; exact hs

theorem claim (n : ℕ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : finrank F V = n) : Claim F k V n := by
  induction n generalizing V with
  | zero => exact claim_zero k V hV
  | succ n ih => exact claim_succ k n (fun W _ _ _ hW => ih W hW) V hV

end Main

end ST

end MartinPhd

end
end SolomonTits
