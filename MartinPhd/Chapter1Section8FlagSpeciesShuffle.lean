import MartinPhd.Chapter1Section7SpectralSequence
import MartinPhd.Chapter1Section4Cohomology
import MartinPhd.Chapter1Section5SubspacesFlagVarieties

/-!
# Chapter 1, Section 1.8 (flag species) and the shuffle lemmas of Section 1.9

Contents:
* Chapter1Section8
* Shuffle
-/

section Chapter1Section8

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §1.8 Especies de banderas -/

section FlagSpecies

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The product `μ(F ⊗ G)` of the flag species: for `F` a flag in `S` and `G` a flag in
`V/S`, the flag `(F₀, …, F_l, π⁻¹(G₁), …, π⁻¹(G_k))` in `V`. -/
def Flag.concat {S : Submodule K V} (F : Flag K S) (G : Flag K (V ⧸ S)) : Flag K V where
  carrier := F.carrier.image (Submodule.map S.subtype) ∪ G.carrier.image (Submodule.comap S.mkQ)
  isChain := by
    intro a ha b hb hab
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image] at ha hb
    have h1 : ∀ A : Submodule K S, Submodule.map S.subtype A ≤ S :=
      fun A => Submodule.map_subtype_le S A
    have h2 : ∀ B : Submodule K (V ⧸ S), S ≤ Submodule.comap S.mkQ B := fun B x hx => by
      simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero S).2 hx]
    rcases ha with ⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩ <;> rcases hb with ⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩
    · by_cases h : A = B
      · subst h; exact absurd rfl hab
      · rcases F.isChain hA hB h with h | h
        · exact Or.inl (Submodule.map_mono h)
        · exact Or.inr (Submodule.map_mono h)
    · exact Or.inl ((h1 A).trans (h2 B))
    · exact Or.inr ((h1 B).trans (h2 A))
    · by_cases h : A = B
      · subst h; exact absurd rfl hab
      · rcases G.isChain hA hB h with h | h
        · exact Or.inl (Submodule.comap_mono h)
        · exact Or.inr (Submodule.comap_mono h)
  bot_mem := Finset.mem_union_left _ (Finset.mem_image.2 ⟨⊥, F.bot_mem, Submodule.map_bot _⟩)
  top_mem := Finset.mem_union_right _ (Finset.mem_image.2 ⟨⊤, G.top_mem, Submodule.comap_top _⟩)

/-- The convolution `F ∗ S = μ(F|_S ⊗ F|_{V/S})` of (1.4) with `l = 1`, for the flag
species. -/
def Flag.convSub (F : Flag K V) (S : Submodule K V) : Flag K V :=
  (F.restrict S).concat (F.project S)

/-- The Tits product (projection) `F ∗ G` of [AB08, §4.9]: the reduction of the family
`F_{i-1} + (F_i ∩ G_j)`, i.e. `F` refined "as naturally as possible" by `G`. -/
def Flag.tits (F G : Flag K V) : Flag K V where
  carrier := (F.carrier ×ˢ G.carrier).image fun AB =>
    F.nth (F.index AB.1 - 1) ⊔ (AB.1 ⊓ AB.2)
  isChain := by
    intro a ha b hb hab
    simp only [Finset.coe_image, Finset.coe_product, Set.mem_image, Set.mem_prod,
      Finset.mem_coe] at ha hb
    obtain ⟨⟨A, B⟩, ⟨hA, hB⟩, rfl⟩ := ha
    obtain ⟨⟨A', B'⟩, ⟨hA', hB'⟩, rfl⟩ := hb
    have hle : ∀ (A B : Submodule K V), A ∈ F.carrier →
        F.nth (F.index A - 1) ⊔ (A ⊓ B) ≤ A := fun A B hA =>
      sup_le (F.pred_le hA) inf_le_left
    by_cases hAA : A = A'
    · subst hAA
      rcases G.isChain hB hB' (fun h => hab (by rw [h])) with h | h
      · exact Or.inl (sup_le_sup_left (inf_le_inf_left _ h) _)
      · exact Or.inr (sup_le_sup_left (inf_le_inf_left _ h) _)
    · rcases F.isChain hA hA' hAA with h | h
      · exact Or.inl ((hle A B hA).trans ((F.le_pred hA hA' (lt_of_le_of_ne h hAA)).trans le_sup_left))
      · exact Or.inr ((hle A' B' hA').trans ((F.le_pred hA' hA (lt_of_le_of_ne h (Ne.symm hAA))).trans le_sup_left))
  bot_mem := Finset.mem_image.2 ⟨(⊥, ⊥), Finset.mem_product.2 ⟨F.bot_mem, G.bot_mem⟩, by
    simp [F.index_bot, F.nth_zero]⟩
  top_mem := Finset.mem_image.2 ⟨(⊤, ⊤), Finset.mem_product.2 ⟨F.top_mem, G.top_mem⟩, by
    simp⟩

lemma ofSubspace_carrier_eq (S : Submodule K V) :
    (Flag.ofSubspace S).carrier = {⊥, S, ⊤} := rfl

lemma ofSubspace_index_bot (S : Submodule K V) :
    (Flag.ofSubspace S).index ⊥ = 0 := Flag.index_bot _

lemma ofSubspace_index_S {S : Submodule K V} (hSbot : S ≠ ⊥) :
    (Flag.ofSubspace S).index S = 1 := by
  dsimp [Flag.index]
  have : (Flag.ofSubspace S).carrier.filter (· < S) = {⊥} := by
    ext Y
    simp only [Flag.ofSubspace, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hlt⟩
      · simp
      · exact (hlt.ne rfl).elim
      · exact (not_le_of_gt hlt le_top).elim
    · rintro rfl
      exact ⟨by simp, bot_le.lt_of_ne' hSbot⟩
  rw [this, Finset.card_singleton]

lemma ofSubspace_index_top_of_ne {S : Submodule K V} (hSbot : S ≠ ⊥) (hStop : S ≠ ⊤) :
    (Flag.ofSubspace S).index ⊤ = 2 := by
  dsimp [Flag.index]
  have : (Flag.ofSubspace S).carrier.filter (· < ⊤) = {⊥, S} := by
    ext Y
    simp only [Flag.ofSubspace, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl, hlt⟩
      · simp
      · simp
      · exact (hlt.ne rfl).elim
    · rintro (rfl | rfl)
      · exact ⟨by simp, (bot_le.lt_of_ne' hSbot).trans (le_top.lt_of_ne hStop)⟩
      · exact ⟨by simp, le_top.lt_of_ne hStop⟩
  rw [this, Finset.card_insert_of_notMem (by simp [hSbot.symm]), Finset.card_singleton]

lemma ofSubspace_nth_top_sub_one_of_top (S : Submodule K V) (h : S = ⊤ ∨ S = ⊥) :
    (Flag.ofSubspace S).nth ((Flag.ofSubspace S).index ⊤ - 1) = ⊥ := by
  have hle : (Flag.ofSubspace S).index ⊤ ≤ 1 := by
    dsimp [Flag.index]
    have : (Flag.ofSubspace S).carrier.filter (· < ⊤) ⊆ {⊥} := by
      intro Y
      simp only [Flag.ofSubspace, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      rintro ⟨rfl | rfl | rfl, hlt⟩ <;> rcases h with rfl | rfl <;> simp_all
    exact (Finset.card_le_card this).trans (by simp)
  have : (Flag.ofSubspace S).index ⊤ - 1 = 0 := by omega
  rw [this, Flag.nth_zero]

lemma ofSubspace_nth_one {S : Submodule K V} (hSbot : S ≠ ⊥) :
    (Flag.ofSubspace S).nth 1 = S := by
  have hS_mem : S ∈ (Flag.ofSubspace S).carrier := by simp [Flag.ofSubspace]
  have hidxS := ofSubspace_index_S hSbot
  exact (congrArg (Flag.nth (Flag.ofSubspace S)) hidxS).symm.trans (Flag.nth_index (Flag.ofSubspace S) hS_mem)

theorem Flag.convSub_carrier (F : Flag K V) (S : Submodule K V) :
    (F.convSub S).carrier =
      (F.carrier.image (fun B => S ⊓ B)) ∪ (F.carrier.image (fun B => S ⊔ B)) := by
  ext X
  simp only [Flag.convSub, Flag.concat, Flag.restrict, Flag.project,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨A, ⟨B, hB, rfl⟩, rfl⟩ | ⟨A, ⟨B, hB, rfl⟩, rfl⟩)
    · rw [Submodule.map_comap_subtype]
      exact Or.inl ⟨B, hB, rfl⟩
    · rw [Submodule.comap_map_mkQ]
      exact Or.inr ⟨B, hB, rfl⟩
  · rintro (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
    · left
      refine ⟨Submodule.comap S.subtype B, ⟨B, hB, rfl⟩, ?_⟩
      rw [Submodule.map_comap_subtype]
    · right
      refine ⟨Submodule.map S.mkQ B, ⟨B, hB, rfl⟩, ?_⟩
      rw [Submodule.comap_map_mkQ]

theorem Flag.tits_ofSubspace_carrier (F : Flag K V) (S : Submodule K V) :
    ((Flag.ofSubspace S).tits F).carrier =
      (F.carrier.image (fun B => S ⊓ B)) ∪ (F.carrier.image (fun B => S ⊔ B)) := by
  ext X
  simp only [Flag.tits, Finset.mem_image, Finset.mem_product, Prod.exists, Finset.mem_union]
  constructor
  · rintro ⟨A, B, ⟨hA, hB⟩, rfl⟩
    simp only [Flag.ofSubspace, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with h1 | h2 | h3
    · subst A
      left
      refine ⟨⊥, F.bot_mem, ?_⟩
      simp [ofSubspace_index_bot, Flag.nth_zero]
    · subst A
      by_cases hSbot : S = ⊥
      · subst hSbot
        left
        refine ⟨⊥, F.bot_mem, ?_⟩
        simp [ofSubspace_index_bot, Flag.nth_zero]
      · left
        refine ⟨B, hB, ?_⟩
        simp [ofSubspace_index_S hSbot, Flag.nth_zero]
    · subst A
      by_cases hStop : S = ⊤
      · subst hStop
        left
        refine ⟨B, hB, ?_⟩
        simp [ofSubspace_nth_top_sub_one_of_top (⊤ : Submodule K V) (Or.inl rfl)]
      · by_cases hSbot : S = ⊥
        · subst hSbot
          right
          refine ⟨B, hB, ?_⟩
          simp [ofSubspace_nth_top_sub_one_of_top (⊥ : Submodule K V) (Or.inr rfl)]
        · right
          refine ⟨B, hB, ?_⟩
          have hidx := ofSubspace_index_top_of_ne hSbot hStop
          have hnth := ofSubspace_nth_one hSbot
          simp [hidx, hnth]
  · rintro (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
    · by_cases hS : S = ⊥
      · subst hS
        rw [bot_inf_eq]
        refine ⟨⊥, ⊥, ⟨by simp [Flag.ofSubspace], F.bot_mem⟩, ?_⟩
        simp [ofSubspace_index_bot, Flag.nth_zero]
      · refine ⟨S, B, ⟨by simp [Flag.ofSubspace], hB⟩, ?_⟩
        simp [ofSubspace_index_S hS, Flag.nth_zero]
    · by_cases hStop : S = ⊤
      · subst hStop
        rw [top_sup_eq]
        refine ⟨⊤, ⊤, ⟨by simp [Flag.ofSubspace], F.top_mem⟩, ?_⟩
        simp [ofSubspace_nth_top_sub_one_of_top (⊤ : Submodule K V) (Or.inl rfl)]
      · by_cases hSbot : S = ⊥
        · subst hSbot
          rw [bot_sup_eq]
          refine ⟨⊤, B, ⟨by simp [Flag.ofSubspace], hB⟩, ?_⟩
          simp [ofSubspace_nth_top_sub_one_of_top (⊥ : Submodule K V) (Or.inr rfl)]
        · refine ⟨⊤, B, ⟨by simp [Flag.ofSubspace], hB⟩, ?_⟩
          have hidx := ofSubspace_index_top_of_ne hSbot hStop
          have hnth := ofSubspace_nth_one hSbot
          simp [hidx, hnth]

/-- For the flag species the convolution product (1.4) is the Tits product. -/
theorem Flag.convSub_eq_tits (F : Flag K V) (S : Submodule K V) :
    F.convSub S = (Flag.ofSubspace S).tits F := by
  apply Flag.ext
  rw [Flag.convSub_carrier, Flag.tits_ofSubspace_carrier]

theorem Flag.finrank_lt_of_lt [FiniteDimensional K V] {A B : Submodule K V} (h : A < B) :
    finrank K A < finrank K B := Submodule.finrank_lt_finrank_of_lt h

theorem Flag.len_le_finrank [FiniteDimensional K V] (F : Flag K V) : F.len ≤ finrank K V := by
  have key : ∀ i, i < F.carrier.card → i ≤ finrank K (F.nth i) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have := ih (by omega)
      have h2 := Flag.finrank_lt_of_lt (F.nth_lt_nth (by omega : i < i + 1) hi)
      omega
  have h := key F.len (by have := F.card_eq_len_succ; omega)
  rw [F.nth_len, finrank_top] at h
  exact h

/-- A flag with a member of every dimension is complete. -/
theorem Flag.isComplete_of_forall_dim [FiniteDimensional K V] (G : Flag K V)
    (h : ∀ j ≤ finrank K V, ∃ A ∈ G.carrier, finrank K A = j) : G.IsComplete := by
  apply le_antisymm G.len_le_finrank
  have hsub : Finset.range (finrank K V + 1) ⊆ G.carrier.image (fun A : Submodule K V => finrank K A) := by
    intro j hj
    obtain ⟨A, hA, hAj⟩ := h j (by simpa [Nat.lt_succ_iff] using hj)
    exact Finset.mem_image.2 ⟨A, hA, hAj⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  simp only [Finset.card_range] at this
  have h2 := G.card_eq_len_succ
  omega

theorem Flag.isComplete_map {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    [FiniteDimensional K W] (e : V ≃ₗ[K] W) (F : Flag K V) (hF : F.IsComplete) :
    (F.map e).IsComplete := by
  unfold Flag.IsComplete at *
  rw [Flag.len_map, hF, e.finrank_eq]

/-- The intermediate value argument for a step function. -/
theorem exists_eq_of_step (g : ℕ → ℕ) (h0 : g 0 = 0) (d : ℕ)
    (hstep : ∀ i < d, g i ≤ g (i + 1) ∧ g (i + 1) ≤ g i + 1) :
    ∀ i ≤ d, ∀ j ≤ g i, ∃ i' ≤ i, g i' = j := by
  intro i
  induction i with
  | zero => intro _ j hj; exact ⟨0, le_rfl, by omega⟩
  | succ i ih =>
    intro hi j hj
    have hs := hstep i (by omega)
    by_cases hji : j ≤ g i
    · obtain ⟨i', hi', h⟩ := ih (by omega) j hji
      exact ⟨i', by omega, h⟩
    · exact ⟨i + 1, le_rfl, by omega⟩

theorem Flag.finrank_nth_of_isComplete [FiniteDimensional K V] {F : Flag K V}
    (hF : F.IsComplete) {i : ℕ} (hi : i ≤ F.len) : finrank K (F.nth i) = i := by
  have hlow : ∀ i, i < F.carrier.card → i ≤ finrank K (F.nth i) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have := ih (by omega)
      have h2 := Flag.finrank_lt_of_lt (F.nth_lt_nth (by omega : i < i + 1) hi)
      omega
  have hup : ∀ m i, i + m < F.carrier.card → finrank K (F.nth i) + m ≤ finrank K (F.nth (i + m)) := by
    intro m
    induction m with
    | zero => intro i _; simp
    | succ m ih =>
      intro i hi
      have := ih i (by omega)
      have h2 := Flag.finrank_lt_of_lt (F.nth_lt_nth (by omega : i + m < i + m + 1) (by omega))
      have e : i + (m + 1) = i + m + 1 := rfl
      rw [e]
      omega
  have h1 := hlow i (by have := F.card_eq_len_succ; omega)
  have h2 := hup (F.len - i) i (by have := F.card_eq_len_succ; omega)
  have h3 : i + (F.len - i) = F.len := by omega
  rw [h3, F.nth_len, finrank_top] at h2
  unfold Flag.IsComplete at hF
  omega

theorem finrank_comap_subtype [FiniteDimensional K V] (A S : Submodule K V) :
    finrank K (S.comap A.subtype) = finrank K (A ⊓ S : Submodule K V) := by
  rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem finrank_map_mkQ_add [FiniteDimensional K V] (A S : Submodule K V) :
    finrank K (A.map S.mkQ) + finrank K (A ⊓ S : Submodule K V) = finrank K A := by
  have := LinearMap.finrank_range_add_finrank_ker (S.mkQ ∘ₗ A.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp, Submodule.ker_mkQ,
    finrank_comap_subtype] at this
  exact this

theorem Flag.dim_step [FiniteDimensional K V] (F : Flag K V) (hF : F.IsComplete) (S : Submodule K V)
    {i : ℕ} (hi : i < F.len) :
    finrank K (F.nth i ⊓ S : Submodule K V) ≤ finrank K (F.nth (i + 1) ⊓ S : Submodule K V) ∧
    finrank K (F.nth (i + 1) ⊓ S : Submodule K V) ≤ finrank K (F.nth i ⊓ S : Submodule K V) + 1 := by
  have hc : i + 1 < F.carrier.card := by have := F.card_eq_len_succ; omega
  have hle : F.nth i ≤ F.nth (i + 1) := (F.nth_lt_nth (by omega : i < i + 1) hc).le
  refine ⟨Submodule.finrank_mono (inf_le_inf_right _ hle), ?_⟩
  set B := F.nth (i + 1) ⊓ S
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq B (F.nth i)
  have hinf : B ⊓ F.nth i = F.nth i ⊓ S := by
    ext x; simp only [B, Submodule.mem_inf]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hle h.1, h.2⟩, h.1⟩⟩
  have hsup : finrank K (B ⊔ F.nth i : Submodule K V) ≤ i + 1 := by
    have : B ⊔ F.nth i ≤ F.nth (i + 1) := sup_le inf_le_left hle
    have := Submodule.finrank_mono this
    rwa [F.finrank_nth_of_isComplete hF (by omega)] at this
  rw [hinf] at hsum
  have := F.finrank_nth_of_isComplete hF (le_of_lt hi)
  omega

theorem Flag.isComplete_restrict [FiniteDimensional K V] (F : Flag K V) (S : Submodule K V)
    (hF : F.IsComplete) : (F.restrict S).IsComplete := by
  haveI : FiniteDimensional K S := inferInstance
  apply Flag.isComplete_of_forall_dim
  intro j hj
  let g : ℕ → ℕ := fun i => finrank K (F.nth i ⊓ S : Submodule K V)
  have h0 : g 0 = 0 := by
    show finrank K (F.nth 0 ⊓ S : Submodule K V) = 0
    rw [F.nth_zero]; simp
  have hgd : g F.len = finrank K S := by
    show finrank K (F.nth F.len ⊓ S : Submodule K V) = _
    rw [F.nth_len, top_inf_eq]
  obtain ⟨i, hi, hgi⟩ := exists_eq_of_step g h0 F.len (fun i hi => F.dim_step hF S hi) F.len le_rfl j
    (by rw [hgd]; exact hj)
  refine ⟨(F.nth i).comap S.subtype, Finset.mem_image.2 ⟨F.nth i, ?_, rfl⟩, ?_⟩
  · exact (F.nth_mem (by have := F.card_eq_len_succ; omega)).1
  · rw [finrank_comap_subtype, inf_comm]
    exact hgi

theorem Flag.isComplete_project [FiniteDimensional K V] (F : Flag K V) (S : Submodule K V)
    (hF : F.IsComplete) : (F.project S).IsComplete := by
  apply Flag.isComplete_of_forall_dim
  intro j hj
  let g : ℕ → ℕ := fun i => finrank K (F.nth i) - finrank K (F.nth i ⊓ S : Submodule K V)
  have hdim : ∀ i ≤ F.len, finrank K (F.nth i) = i := fun i hi => F.finrank_nth_of_isComplete hF hi
  have hle : ∀ i, finrank K (F.nth i ⊓ S : Submodule K V) ≤ finrank K (F.nth i) :=
    fun i => Submodule.finrank_mono inf_le_left
  have h0 : g 0 = 0 := by
    show finrank K (F.nth 0) - finrank K (F.nth 0 ⊓ S : Submodule K V) = 0
    rw [F.nth_zero]; simp
  have hgd : g F.len = finrank K (V ⧸ S) := by
    have := S.finrank_quotient_add_finrank
    show finrank K (F.nth F.len) - finrank K (F.nth F.len ⊓ S : Submodule K V) = _
    rw [F.nth_len, top_inf_eq, finrank_top]
    omega
  obtain ⟨i, hi, hgi⟩ := exists_eq_of_step g h0 F.len (fun i hi => by
      have h1 := F.dim_step hF S hi
      have h2 := hdim i hi.le
      have h3 := hdim (i + 1) hi
      have h4 := hle i
      have h5 := hle (i + 1)
      simp only [g]; omega) F.len le_rfl j (by rw [hgd]; exact hj)
  refine ⟨(F.nth i).map S.mkQ, Finset.mem_image.2 ⟨F.nth i, ?_, rfl⟩, ?_⟩
  · exact (F.nth_mem (by have := F.card_eq_len_succ; omega)).1
  · have := finrank_map_mkQ_add (F.nth i) S
    simp only [g] at hgi
    omega

theorem Flag.isComplete_concat [FiniteDimensional K V] {S : Submodule K V} (F : Flag K S)
    (G : Flag K (V ⧸ S)) (hF : F.IsComplete) (hG : G.IsComplete) : (F.concat G).IsComplete := by
  apply Flag.isComplete_of_forall_dim
  intro j hj
  by_cases hjS : j ≤ finrank K S
  · obtain ⟨A, hA, hAj⟩ := (⟨F.nth j, (F.nth_mem (by have := F.card_eq_len_succ; unfold Flag.IsComplete at hF; omega)).1,
      F.finrank_nth_of_isComplete hF (by unfold Flag.IsComplete at hF; omega)⟩ :
      ∃ A ∈ F.carrier, finrank K A = j)
    refine ⟨A.map S.subtype, Finset.mem_union_left _ (Finset.mem_image.2 ⟨A, hA, rfl⟩), ?_⟩
    rw [Submodule.finrank_map_subtype_eq, hAj]
  · obtain ⟨B, hB, hBj⟩ := (by
      have hq : j - finrank K S ≤ finrank K (V ⧸ S) := by
        have := S.finrank_quotient_add_finrank
        omega
      exact ⟨G.nth (j - finrank K S), (G.nth_mem (by
          have := G.card_eq_len_succ; unfold Flag.IsComplete at hG; omega)).1,
        G.finrank_nth_of_isComplete hG (by unfold Flag.IsComplete at hG; omega)⟩ :
      ∃ A ∈ G.carrier, finrank K A = j - finrank K S)
    refine ⟨B.comap S.mkQ, Finset.mem_union_right _ (Finset.mem_image.2 ⟨B, hB, rfl⟩), ?_⟩
    have := finrank_map_mkQ_add (B.comap S.mkQ) S
    rw [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective S)] at this
    have hinf : (B.comap S.mkQ ⊓ S : Submodule K V) = S := by
      apply le_antisymm inf_le_right
      exact le_inf (fun x hx => by simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero S).2 hx]) le_rfl
    rw [hinf] at this
    omega

theorem lmap_comp₃ {α β γ δ : Type*} {k : Type} [Field k] (h : α → β) (f : β → γ) (g : γ → δ) :
    (Finsupp.lmapDomain k k g) ∘ₗ (Finsupp.lmapDomain k k f) ∘ₗ (Finsupp.lmapDomain k k h) =
      Finsupp.lmapDomain k k (g ∘ f ∘ h) := by
  rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]

theorem lmap_comm {α β γ δ : Type*} {k : Type} [Field k] (f : α → β) (g : β → γ) (h : α → δ)
    (l : δ → γ) (H : ∀ a, g (f a) = l (h a)) :
    (Finsupp.lmapDomain k k g) ∘ₗ (Finsupp.lmapDomain k k f) =
      (Finsupp.lmapDomain k k l) ∘ₗ (Finsupp.lmapDomain k k h) := by
  rw [← Finsupp.lmapDomain_comp, ← Finsupp.lmapDomain_comp]
  congr 2
  funext a
  exact H a

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

variable (F k) in
/-- The **flag species** `Σ`: `Σ(V) = k Fl(V)`, `Σ(φ)(F) = φ_*(F)`. -/
def flagSpecies : GLSpecies F k where
  obj V := ModuleCat.of k (Flag F V.of →₀ k)
  map φ := ModuleCat.ofHom (Finsupp.lmapDomain k k (Flag.map (FGModuleCat.isoToLinearEquiv φ.iso)))
  map_id V := by
    apply ModuleCat.hom_ext
    change Finsupp.lmapDomain k k (Flag.map (LinearEquiv.refl F V.of)) = LinearMap.id
    apply Finsupp.lhom_ext
    intro G b
    simp [Flag.map_refl]
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    change Finsupp.lmapDomain k k (Flag.map ((FGModuleCat.isoToLinearEquiv φ.iso).trans
        (FGModuleCat.isoToLinearEquiv ψ.iso))) =
      (Finsupp.lmapDomain k k (Flag.map (FGModuleCat.isoToLinearEquiv ψ.iso))).comp
        (Finsupp.lmapDomain k k (Flag.map (FGModuleCat.isoToLinearEquiv φ.iso)))
    apply Finsupp.lhom_ext
    intro G b
    simp [Flag.map_trans]

theorem lmapDomain_flag_map_refl {k : Type} [Field k] :
    Finsupp.lmapDomain k k (Flag.map (LinearEquiv.refl K V)) = LinearMap.id := by
  have : (Flag.map (LinearEquiv.refl K V) : Flag K V → Flag K V) = id := funext Flag.map_refl
  rw [this]; exact Finsupp.lmapDomain_id k k

theorem flagSpecies_mapEquiv {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) :
    (flagSpecies F k).mapEquiv e = Finsupp.lmapDomain k k (Flag.map e) := rfl

variable (F k) in
/-- The species `L` of **complete flags**: `L(V) = k Fl⁺(V) ⊆ Σ(V)`. -/
def completeFlagSpecies : GLSpecies F k where
  obj V := ModuleCat.of k ↥(Finsupp.supported k k {G : Flag F V.of | G.IsComplete})
  map φ := ModuleCat.ofHom <|
    (Finsupp.lmapDomain k k (Flag.map (FGModuleCat.isoToLinearEquiv φ.iso))).restrict (by
      intro x hx
      exact lmapDomain_mem_supported _ _ _ (fun G hG => Flag.isComplete_map _ G hG) x hx)
  map_id V := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change Finsupp.lmapDomain k k (Flag.map (LinearEquiv.refl F V.of)) x.1 = x.1
    rw [lmapDomain_flag_map_refl]; rfl
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change Finsupp.lmapDomain k k (Flag.map ((FGModuleCat.isoToLinearEquiv φ.iso).trans
        (FGModuleCat.isoToLinearEquiv ψ.iso))) x.1 =
      Finsupp.lmapDomain k k (Flag.map (FGModuleCat.isoToLinearEquiv ψ.iso))
        (Finsupp.lmapDomain k k (Flag.map (FGModuleCat.isoToLinearEquiv φ.iso)) x.1)
    have key := fun G => Flag.map_trans G (FGModuleCat.isoToLinearEquiv φ.iso)
      (FGModuleCat.isoToLinearEquiv ψ.iso)
    have : Flag.map ((FGModuleCat.isoToLinearEquiv φ.iso).trans
        (FGModuleCat.isoToLinearEquiv ψ.iso)) =
        Flag.map (FGModuleCat.isoToLinearEquiv ψ.iso) ∘
          Flag.map (FGModuleCat.isoToLinearEquiv φ.iso) := funext key
    rw [this, Finsupp.lmapDomain_comp]; rfl

variable (F k) in
/-- The inclusion `L → Σ`. -/
def completeFlagInclusion : completeFlagSpecies F k ⟶ flagSpecies F k where
  app V := ModuleCat.ofHom (Submodule.subtype _)
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

variable (F k) in
/-- `Σ` as an `e`-bicomodule: `λ(F) = ∑_S e_S ⊗ F|_{V/S}`, `ρ(F) = ∑_S F|_S ⊗ e_{V/S}`. -/
def flagBicomod : EBicomod F k where
  X := flagSpecies F k
  res V S := Finsupp.lmapDomain k k (fun G : Flag F V => G.restrict S)
  proj V S := Finsupp.lmapDomain k k (fun G : Flag F V => G.project S)
  res_natural := by
    intro V W e S
    exact lmap_comm _ _ _ _ (fun G => (Flag.restrict_map G e S).symm)
  proj_natural := by
    intro V W e S
    exact lmap_comm _ _ _ _ (fun G => (Flag.project_map G e S).symm)
  proj_proj := by
    intro V T S h
    rw [flagSpecies_mapEquiv]
    change (Finsupp.lmapDomain k k _) ∘ₗ (Finsupp.lmapDomain k k (fun G : Flag F (V ⧸ T) =>
        G.project (S.map T.mkQ))) ∘ₗ (Finsupp.lmapDomain k k (fun G : Flag F V => G.project T)) = _
    rw [lmap_comp₃]
    congr 1
    funext G
    exact Flag.project_project G T S h
  res_res := by
    intro V T S h
    rw [flagSpecies_mapEquiv]
    change (Finsupp.lmapDomain k k _) ∘ₗ (Finsupp.lmapDomain k k (fun G : Flag F S =>
        G.restrict (T.comap S.subtype))) ∘ₗ (Finsupp.lmapDomain k k (fun G : Flag F V => G.restrict S)) = _
    rw [lmap_comp₃]
    congr 1
    funext G
    exact Flag.restrict_restrict G T S h
  proj_bot := by
    intro V
    rw [flagSpecies_mapEquiv]
    congr 1
  res_top := by
    intro V
    rw [flagSpecies_mapEquiv]
    congr 1
    funext G
    exact Flag.restrict_top G
  proj_res := by
    intro V T S h
    rw [flagSpecies_mapEquiv]
    change (Finsupp.lmapDomain k k _) ∘ₗ (Finsupp.lmapDomain k k (fun G : Flag F S =>
        G.project (T.comap S.subtype))) ∘ₗ (Finsupp.lmapDomain k k (fun G : Flag F V => G.restrict S)) =
      (Finsupp.lmapDomain k k (fun G : Flag F (V ⧸ T) => G.restrict (S.map T.mkQ))) ∘ₗ
        (Finsupp.lmapDomain k k (fun G : Flag F V => G.project T))
    rw [lmap_comp₃, ← Finsupp.lmapDomain_comp]
    congr 1
    funext G
    exact Flag.project_restrict G T S h

theorem tmap_smul_tmul {A B C D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] {k : Type} [Field k] [Module k A] [Module k B] [Module k C] [Module k D]
    (f : A →ₗ[k] C) (g : B →ₗ[k] D) (c : k) (a : A) (b : B) :
    TensorProduct.map f g (c • (a ⊗ₜ[k] b)) = c • (f a ⊗ₜ[k] g b) := by
  rw [map_smul, TensorProduct.map_tmul]

variable (F k) in
/-- The comultiplication of `Σ`: `Δ_S(H) = H|_S ⊗ H|_{V/S}`. -/
def flagComul (V : FGModuleCat.{0} F) (S : Submodule F V) :
    (Flag F V →₀ k) →ₗ[k] TensorProduct k (Flag F S →₀ k) (Flag F (V ⧸ S) →₀ k) :=
  Finsupp.linearCombination k fun H : Flag F V =>
    (Finsupp.single (H.restrict S) (1 : k)) ⊗ₜ[k] (Finsupp.single (H.project S) (1 : k))

theorem flagComul_single (V : FGModuleCat.{0} F) (S : Submodule F V) (H : Flag F V) (c : k) :
    flagComul F k V S (Finsupp.single H c) =
      c • ((Finsupp.single (H.restrict S) (1 : k)) ⊗ₜ[k] (Finsupp.single (H.project S) (1 : k))) :=
  Finsupp.linearCombination_single _ _ _

variable (F k) in
/-- `Σ` as a coalgebra: `Δ(H) = ∑_{S ≤ V} H|_S ⊗ H|_{V/S}`. (Also a bialgebra with
`μ = Flag.concat` and unit/counit concentrated at `V = 0`.) -/
def flagCoalg : EBicomodCoalg F k where
  toEBicomod := flagBicomod F k
  comul V S := flagComul F k V S
  comul_natural := by
    intro V W e S
    apply Finsupp.lhom_ext
    intro H c
    change TensorProduct.map (Finsupp.lmapDomain k k (Flag.map (e.submoduleMap S)))
        (Finsupp.lmapDomain k k (Flag.map (Submodule.Quotient.equiv S (S.map (e : V →ₗ[F] W)) e rfl)))
        (flagComul F k V S (Finsupp.single H c)) =
      flagComul F k W (S.map (e : V →ₗ[F] W))
        (Finsupp.lmapDomain k k (Flag.map e) (Finsupp.single H c))
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, flagComul_single, flagComul_single,
      tmap_smul_tmul]
    simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [Flag.restrict_map, Flag.project_map]
  comul_proj := by
    intro V T S h
    apply Finsupp.lhom_ext
    intro H c
    change TensorProduct.map (Finsupp.lmapDomain k k (Flag.map (subQuotIso T S)))
        (Finsupp.lmapDomain k k (Flag.map (T.quotientQuotientEquivQuotient S h).symm))
        (TensorProduct.map (Finsupp.lmapDomain k k (fun G : Flag F (sub S) => G.project (T.comap S.subtype)))
          LinearMap.id (flagComul F k V S (Finsupp.single H c))) =
      flagComul F k (quo T) (S.map T.mkQ)
        (Finsupp.lmapDomain k k (fun G : Flag F V => G.project T) (Finsupp.single H c))
    rw [flagComul_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, flagComul_single,
      map_smul, map_smul, TensorProduct.map_tmul, TensorProduct.map_tmul]
    simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, LinearMap.id_apply]
    rw [show Flag.map (subQuotIso T S) ((H.restrict S).project (T.comap S.subtype)) =
        (H.project T).restrict (S.map T.mkQ) from Flag.project_restrict H T S h,
      ← Flag.eq_map_symm (Flag.project_project H T S h)]
  comul_res := by
    intro V T S h
    apply Finsupp.lhom_ext
    intro H c
    change TensorProduct.map (Finsupp.lmapDomain k k (Flag.map (Submodule.comapSubtypeEquivOfLe h)))
        (Finsupp.lmapDomain k k (Flag.map (subQuotIso T S)))
        (flagComul F k (sub S) (T.comap S.subtype)
          (Finsupp.lmapDomain k k (fun G : Flag F V => G.restrict S) (Finsupp.single H c))) =
      TensorProduct.map LinearMap.id
        (Finsupp.lmapDomain k k (fun G : Flag F (quo T) => G.restrict (S.map T.mkQ)))
        (flagComul F k V T (Finsupp.single H c))
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, flagComul_single, flagComul_single]
    erw [map_smul, map_smul, TensorProduct.map_tmul, TensorProduct.map_tmul]
    simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, LinearMap.id_apply]
    rw [show Flag.map (subQuotIso T S) ((H.restrict S).project (T.comap S.subtype)) =
        (H.project T).restrict (S.map T.mkQ) from Flag.project_restrict H T S h,
      Flag.restrict_restrict H T S h]
  comul_res_proj := by
    intro V T S h
    apply Finsupp.lhom_ext
    intro H c
    change TensorProduct.map (Finsupp.lmapDomain k k (Flag.map (Submodule.comapSubtypeEquivOfLe h)))
        LinearMap.id
        (TensorProduct.map (Finsupp.lmapDomain k k (fun G : Flag F (sub S) => G.restrict (T.comap S.subtype)))
          LinearMap.id (flagComul F k V S (Finsupp.single H c))) =
      TensorProduct.map LinearMap.id
        (Finsupp.lmapDomain k k (Flag.map (T.quotientQuotientEquivQuotient S h)))
        (TensorProduct.map LinearMap.id
          (Finsupp.lmapDomain k k (fun G : Flag F (quo T) => G.project (S.map T.mkQ)))
          (flagComul F k V T (Finsupp.single H c)))
    rw [flagComul_single, flagComul_single]
    rw [tmap_smul_tmul, tmap_smul_tmul, tmap_smul_tmul, tmap_smul_tmul]
    simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, LinearMap.id_apply]
    rw [Flag.restrict_restrict H T S h, Flag.project_project H T S h]

variable (F k) in
/-- `L` as a sub-`e`-bicomodule of `Σ`. -/
def completeFlagBicomod : EBicomod F k where
  X := completeFlagSpecies F k
  res V S := (Finsupp.lmapDomain k k (fun G : Flag F V => G.restrict S)).restrict (by
    intro x hx
    exact lmapDomain_mem_supported _ _ _ (fun G hG => Flag.isComplete_restrict G S hG) x hx)
  proj V S := (Finsupp.lmapDomain k k (fun G : Flag F V => G.project S)).restrict (by
    intro x hx
    exact lmapDomain_mem_supported _ _ _ (fun G hG => Flag.isComplete_project G S hG) x hx)
  res_natural := by
    intro V W e S
    apply LinearMap.ext; intro x; apply Subtype.ext
    exact LinearMap.congr_fun ((flagBicomod F k).res_natural e S) x.1
  proj_natural := by
    intro V W e S
    apply LinearMap.ext; intro x; apply Subtype.ext
    exact LinearMap.congr_fun ((flagBicomod F k).proj_natural e S) x.1
  proj_proj := by
    intro V T S h
    apply LinearMap.ext; intro x; apply Subtype.ext
    exact LinearMap.congr_fun ((flagBicomod F k).proj_proj V T S h) x.1
  res_res := by
    intro V T S h
    apply LinearMap.ext; intro x; apply Subtype.ext
    exact LinearMap.congr_fun ((flagBicomod F k).res_res V T S h) x.1
  proj_bot := by
    intro V
    apply LinearMap.ext; intro x; apply Subtype.ext
    exact LinearMap.congr_fun ((flagBicomod F k).proj_bot V) x.1
  res_top := by
    intro V
    apply LinearMap.ext; intro x; apply Subtype.ext
    exact LinearMap.congr_fun ((flagBicomod F k).res_top V) x.1
  proj_res := by
    intro V T S h
    apply LinearMap.ext; intro x; apply Subtype.ext
    exact LinearMap.congr_fun ((flagBicomod F k).proj_res V T S h) x.1

variable (F k) in
/-- The comultiplication of `L`. -/
def completeComul (V : FGModuleCat.{0} F) (S : Submodule F V) :
    (Finsupp.supported k k {G : Flag F V | G.IsComplete}) →ₗ[k]
      TensorProduct k (Finsupp.supported k k {G : Flag F S | G.IsComplete})
        (Finsupp.supported k k {G : Flag F (V ⧸ S) | G.IsComplete}) :=
  Finsupp.linearCombination k (fun H : {G : Flag F V // G.IsComplete} =>
      (⟨Finsupp.single (H.1.restrict S) (1 : k),
            Finsupp.single_mem_supported k 1 (Flag.isComplete_restrict H.1 S H.2)⟩ :
          Finsupp.supported k k {G : Flag F S | G.IsComplete}) ⊗ₜ[k]
        (⟨Finsupp.single (H.1.project S) (1 : k),
            Finsupp.single_mem_supported k 1 (Flag.isComplete_project H.1 S H.2)⟩ :
          Finsupp.supported k k {G : Flag F (V ⧸ S) | G.IsComplete})) ∘ₗ
    (Finsupp.supportedEquivFinsupp {G : Flag F V | G.IsComplete}).toLinearMap

theorem map_incl_map {k : Type} [Field k] {M N M' N' P P' Q Q' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [AddCommGroup P] [AddCommGroup P'] [AddCommGroup Q] [AddCommGroup Q']
    [Module k M] [Module k N] [Module k M'] [Module k N'] [Module k P] [Module k P']
    [Module k Q] [Module k Q']
    (f : M →ₗ[k] N) (g : P →ₗ[k] Q) (f' : M' →ₗ[k] N') (g' : P' →ₗ[k] Q')
    (iM : M →ₗ[k] M') (iN : N →ₗ[k] N') (iP : P →ₗ[k] P') (iQ : Q →ₗ[k] Q')
    (hf : iN ∘ₗ f = f' ∘ₗ iM) (hg : iQ ∘ₗ g = g' ∘ₗ iP) :
    TensorProduct.map iN iQ ∘ₗ TensorProduct.map f g =
      TensorProduct.map f' g' ∘ₗ TensorProduct.map iM iP := by
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, hf, hg]

variable (F k) in
/-- `Δ` on `L` agrees with `Δ` on `Σ` after including. -/
theorem completeComul_incl (V : FGModuleCat.{0} F) (S : Submodule F V) :
    TensorProduct.map (Submodule.subtype _) (Submodule.subtype _) ∘ₗ completeComul F k V S =
      flagComul F k V S ∘ₗ Submodule.subtype _ := by
  have : (TensorProduct.map (Submodule.subtype (Finsupp.supported k k {G : Flag F S | G.IsComplete}))
      (Submodule.subtype (Finsupp.supported k k {G : Flag F (V ⧸ S) | G.IsComplete})) ∘ₗ
        completeComul F k V S) ∘ₗ
        (Finsupp.supportedEquivFinsupp (R := k) {G : Flag F V | G.IsComplete}).symm.toLinearMap =
      (flagComul F k V S ∘ₗ Submodule.subtype _) ∘ₗ
        (Finsupp.supportedEquivFinsupp (R := k) {G : Flag F V | G.IsComplete}).symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro H c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    unfold completeComul
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      Finsupp.linearCombination_single, map_smul, TensorProduct.map_tmul, Submodule.subtype_apply]
    rw [Finsupp.supportedEquivFinsupp_symm_single]
    rw [flagComul_single]
  apply LinearMap.ext
  intro x
  have := LinearMap.congr_fun this ((Finsupp.supportedEquivFinsupp (R := k)
    {G : Flag F V | G.IsComplete}) x)
  simpa using this

variable (F k) in
/-- Inclusion of complete flags into all flags. -/
def inclC (X : Type) [AddCommGroup X] [Module F X] [FiniteDimensional F X] :=
  (Finsupp.supported k k {G : Flag F X | G.IsComplete}).subtype

theorem tmap_subtype_inj {k : Type} [Field k] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] (A : Submodule k M) (B : Submodule k N) :
    Function.Injective (TensorProduct.map A.subtype B.subtype) :=
  TensorProduct.map_injective_of_flat_flat _ _ A.injective_subtype B.injective_subtype

variable (F k) in
/-- `L` as a sub-coalgebra of `Σ`. -/
def completeFlagCoalg : EBicomodCoalg F k where
  toEBicomod := completeFlagBicomod F k
  comul V S := completeComul F k V S
  comul_proj := by
    intro V T S h
    apply LinearMap.ext
    intro x
    apply tmap_subtype_inj
    have hc := LinearMap.congr_fun (completeComul_incl F k V S) x
    have h1 := fun y => LinearMap.congr_fun (map_incl_map
      ((completeFlagBicomod F k).proj (sub S) (T.comap S.subtype)) LinearMap.id
      ((flagBicomod F k).proj (sub S) (T.comap S.subtype)) LinearMap.id
      (inclC F k ↥S) (inclC F k (↥S ⧸ T.comap S.subtype)) (inclC F k (↑V ⧸ S))
      (inclC F k (↑V ⧸ S))
      rfl rfl) y
    have h2 := fun y => LinearMap.congr_fun (map_incl_map
      ((completeFlagBicomod F k).X.mapEquiv (V := quo (V := sub S) (T.comap S.subtype))
        (W := sub (V := quo T) (S.map T.mkQ)) (subQuotIso T S))
      ((completeFlagBicomod F k).X.mapEquiv (V := quo S) (W := quo (V := quo T) (S.map T.mkQ))
        (T.quotientQuotientEquivQuotient S h).symm)
      ((flagBicomod F k).X.mapEquiv (V := quo (V := sub S) (T.comap S.subtype))
        (W := sub (V := quo T) (S.map T.mkQ)) (subQuotIso T S))
      ((flagBicomod F k).X.mapEquiv (V := quo S) (W := quo (V := quo T) (S.map T.mkQ))
        (T.quotientQuotientEquivQuotient S h).symm)
      (inclC F k (↥S ⧸ T.comap S.subtype)) (inclC F k ↥(S.map T.mkQ)) (inclC F k (↑V ⧸ S))
      (inclC F k ((↑V ⧸ T) ⧸ S.map T.mkQ))
      rfl rfl) y
    have h3 := LinearMap.congr_fun (completeComul_incl F k (quo T) (S.map T.mkQ))
      ((completeFlagBicomod F k).proj V T x)
    have h4 := LinearMap.congr_fun ((flagCoalg F k).comul_proj V T S h) x.1
    simp only [LinearMap.comp_apply] at h1 h2 h3 h4 hc ⊢
    erw [h2, h1, hc]
    erw [h3]
    exact h4
  comul_res := by
    intro V S U h
    apply LinearMap.ext
    intro x
    apply tmap_subtype_inj
    have h2 := fun y => LinearMap.congr_fun (map_incl_map
      ((completeFlagBicomod F k).X.mapEquiv (V := sub (V := sub U) (S.comap U.subtype)) (W := sub S)
        (Submodule.comapSubtypeEquivOfLe h))
      ((completeFlagBicomod F k).X.mapEquiv (V := quo (V := sub U) (S.comap U.subtype))
        (W := sub (V := quo S) (U.map S.mkQ)) (subQuotIso S U))
      ((flagBicomod F k).X.mapEquiv (V := sub (V := sub U) (S.comap U.subtype)) (W := sub S)
        (Submodule.comapSubtypeEquivOfLe h))
      ((flagBicomod F k).X.mapEquiv (V := quo (V := sub U) (S.comap U.subtype))
        (W := sub (V := quo S) (U.map S.mkQ)) (subQuotIso S U))
      (inclC F k ↥(S.comap U.subtype)) (inclC F k ↥S) (inclC F k (↥U ⧸ S.comap U.subtype))
      (inclC F k ↥(U.map S.mkQ)) rfl rfl) y
    have h3 := LinearMap.congr_fun (completeComul_incl F k (sub U) (S.comap U.subtype))
      ((completeFlagBicomod F k).res V U x)
    have h1 := fun y => LinearMap.congr_fun (map_incl_map
      (LinearMap.id : ↑((completeFlagBicomod F k).X.ev (sub S)) →ₗ[k] _)
      ((completeFlagBicomod F k).res (quo S) (U.map S.mkQ))
      (LinearMap.id : ↑((flagBicomod F k).X.ev (sub S)) →ₗ[k] _)
      ((flagBicomod F k).res (quo S) (U.map S.mkQ))
      (inclC F k ↥S) (inclC F k ↥S) (inclC F k (↑V ⧸ S)) (inclC F k ↥(U.map S.mkQ))
      rfl rfl) y
    have hc := LinearMap.congr_fun (completeComul_incl F k V S) x
    have h4 := LinearMap.congr_fun ((flagCoalg F k).comul_res V S U h) x.1
    simp only [LinearMap.comp_apply] at h1 h2 h3 h4 hc ⊢
    erw [h2, h3, h1, hc]
    exact h4
  comul_res_proj := by
    intro V T S h
    apply LinearMap.ext
    intro x
    apply tmap_subtype_inj
    have L1 := fun y => LinearMap.congr_fun (map_incl_map
      ((completeFlagBicomod F k).res (sub S) (T.comap S.subtype))
      (LinearMap.id : ↑((completeFlagBicomod F k).X.ev (quo S)) →ₗ[k] _)
      ((flagBicomod F k).res (sub S) (T.comap S.subtype))
      (LinearMap.id : ↑((flagBicomod F k).X.ev (quo S)) →ₗ[k] _)
      (inclC F k ↥S) (inclC F k ↥(T.comap S.subtype)) (inclC F k (↑V ⧸ S))
      (inclC F k (↑V ⧸ S)) rfl rfl) y
    have L2 := fun y => LinearMap.congr_fun (map_incl_map
      ((completeFlagBicomod F k).X.mapEquiv (V := sub (V := sub S) (T.comap S.subtype))
        (W := sub T) (Submodule.comapSubtypeEquivOfLe h))
      (LinearMap.id : ↑((completeFlagBicomod F k).X.ev (quo S)) →ₗ[k] _)
      ((flagBicomod F k).X.mapEquiv (V := sub (V := sub S) (T.comap S.subtype))
        (W := sub T) (Submodule.comapSubtypeEquivOfLe h))
      (LinearMap.id : ↑((flagBicomod F k).X.ev (quo S)) →ₗ[k] _)
      (inclC F k ↥(T.comap S.subtype)) (inclC F k ↥T) (inclC F k (↑V ⧸ S))
      (inclC F k (↑V ⧸ S)) rfl rfl) y
    have R1 := fun y => LinearMap.congr_fun (map_incl_map
      (LinearMap.id : ↑((completeFlagBicomod F k).X.ev (sub T)) →ₗ[k] _)
      ((completeFlagBicomod F k).proj (quo T) (S.map T.mkQ))
      (LinearMap.id : ↑((flagBicomod F k).X.ev (sub T)) →ₗ[k] _)
      ((flagBicomod F k).proj (quo T) (S.map T.mkQ))
      (inclC F k ↥T) (inclC F k ↥T) (inclC F k (↑V ⧸ T))
      (inclC F k ((↑V ⧸ T) ⧸ S.map T.mkQ)) rfl rfl) y
    have R2 := fun y => LinearMap.congr_fun (map_incl_map
      (LinearMap.id : ↑((completeFlagBicomod F k).X.ev (sub T)) →ₗ[k] _)
      ((completeFlagBicomod F k).X.mapEquiv (V := quo (V := quo T) (S.map T.mkQ))
        (W := quo S) (Submodule.quotientQuotientEquivQuotient T S h))
      (LinearMap.id : ↑((flagBicomod F k).X.ev (sub T)) →ₗ[k] _)
      ((flagBicomod F k).X.mapEquiv (V := quo (V := quo T) (S.map T.mkQ))
        (W := quo S) (Submodule.quotientQuotientEquivQuotient T S h))
      (inclC F k ↥T) (inclC F k ↥T) (inclC F k ((↑V ⧸ T) ⧸ S.map T.mkQ))
      (inclC F k (↑V ⧸ S)) rfl rfl) y
    have hcS := LinearMap.congr_fun (completeComul_incl F k V S) x
    have hcT := LinearMap.congr_fun (completeComul_incl F k V T) x
    have h4 := LinearMap.congr_fun ((flagCoalg F k).comul_res_proj V T S h) x.1
    simp only [LinearMap.comp_apply] at L1 L2 R1 R2 hcS hcT h4 ⊢
    erw [L2, L1, hcS, R2, R1, hcT]
    exact h4
  comul_natural := by
    intro V W e S
    have hext : ∀ {M : Type} [AddCommGroup M] [Module k M]
        (φ ψ : (Finsupp.supported k k {G : Flag F V | G.IsComplete}) →ₗ[k] M),
        (∀ (H : {G : Flag F V // G.IsComplete}) (c : k),
          φ ((Finsupp.supportedEquivFinsupp (R := k) {G : Flag F V | G.IsComplete}).symm
            (Finsupp.single H c)) =
          ψ ((Finsupp.supportedEquivFinsupp (R := k) {G : Flag F V | G.IsComplete}).symm
            (Finsupp.single H c))) → φ = ψ := by
      intro M _ _ φ ψ h
      have : φ ∘ₗ (Finsupp.supportedEquivFinsupp (R := k) {G : Flag F V | G.IsComplete}).symm.toLinearMap =
          ψ ∘ₗ (Finsupp.supportedEquivFinsupp (R := k) {G : Flag F V | G.IsComplete}).symm.toLinearMap :=
        Finsupp.lhom_ext fun H c => h H c
      apply LinearMap.ext
      intro x
      have := LinearMap.congr_fun this ((Finsupp.supportedEquivFinsupp (R := k)
        {G : Flag F V | G.IsComplete}) x)
      simpa using this
    apply hext
    intro H c
    have hm : (completeFlagBicomod F k).X.mapEquiv e
        ((Finsupp.supportedEquivFinsupp (R := k) {G : Flag F V | G.IsComplete}).symm
          (Finsupp.single H c)) =
        (Finsupp.supportedEquivFinsupp (R := k) {G : Flag F W | G.IsComplete}).symm
          (Finsupp.single ⟨H.1.map e, Flag.isComplete_map e H.1 H.2⟩ c) := by
      apply Subtype.ext
      erw [Finsupp.supportedEquivFinsupp_symm_single]
      change Finsupp.lmapDomain k k (Flag.map e) (↑((Finsupp.supportedEquivFinsupp (R := k)
        {G : Flag F V | G.IsComplete}).symm (Finsupp.single H c))) = _
      rw [Finsupp.supportedEquivFinsupp_symm_single, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single]
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hm]
    erw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single]
    erw [map_smul, TensorProduct.map_tmul]
    congr 1
    refine congrArg₂ (TensorProduct.tmul k) ?_ ?_
    · apply Subtype.ext
      change Finsupp.lmapDomain k k (Flag.map (e.submoduleMap S))
        (Finsupp.single (H.1.restrict S) 1) = Finsupp.single ((H.1.map e).restrict (S.map (e : V →ₗ[F] W))) 1
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Flag.restrict_map]
    · apply Subtype.ext
      change Finsupp.lmapDomain k k (Flag.map (Submodule.Quotient.equiv S (S.map (e : V →ₗ[F] W)) e rfl))
        (Finsupp.single (H.1.project S) 1) = Finsupp.single ((H.1.map e).project (S.map (e : V →ₗ[F] W))) 1
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Flag.project_map]

end FlagSpecies

end MartinPhd

end
end Chapter1Section8

section Shuffle

open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

/-! ## Enumerations by a monotone block, and shuffles (for Lemma 1.33) -/

section Enum

variable {n : ℕ}

/-- The block `[a, a + c)` of `Fin n`. -/
def blockSet (n a c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun l : Fin n => a ≤ l.val ∧ l.val < a + c

theorem card_blockSet {a c : ℕ} (h : a + c ≤ n) : (blockSet n a c).card = c := by
  have : (blockSet n a c).image Fin.val = Finset.Ico a (a + c) := by
    ext x
    simp only [blockSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact hl
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, this]
  simp

/-- A monotone injection of the block `[a, a + c)` onto `Y` enumerates initial segments:
the elements of `Y` below `i` are the images of the first `m = #(Y ∩ [0,i))` block positions. -/
theorem enum_initial (σ : Fin n → Fin n) (a c : ℕ) (Y : Finset (Fin n)) (hc : a + c ≤ n)
    (hinj : Function.Injective σ)
    (hmem : ∀ l : Fin n, a ≤ l.val → l.val < a + c → σ l ∈ Y)
    (hmono : ∀ l l' : Fin n, a ≤ l.val → l < l' → l'.val < a + c → σ l < σ l')
    (hcard : Y.card = c) (i : ℕ) (x : Fin n) :
    (x ∈ Y ∧ x.val < i) ↔
      ∃ l : Fin n, a ≤ l.val ∧ l.val < a + (Y.filter fun y => y.val < i).card ∧ σ l = x := by
  set m := (Y.filter fun y => y.val < i).card with hm
  have himg : (blockSet n a c).image σ = Y := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hy
      simp only [blockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exact hmem l hl.1 hl.2
    · rw [Finset.card_image_of_injective _ hinj, card_blockSet hc, hcard]
  constructor
  · rintro ⟨hxY, hxi⟩
    rw [← himg] at hxY
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hxY
    simp only [blockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    refine ⟨l, hl.1, ?_, rfl⟩
    -- the positions `a ≤ l' ≤ l` inject into `{y ∈ Y | y < i}`
    have hsub : ((blockSet n a c).filter fun l' => l'.val ≤ l.val).image σ ⊆
        Y.filter fun y => y.val < i := by
      intro y hy
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 hy
      simp only [blockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hl'
      refine Finset.mem_filter.2 ⟨hmem l' hl'.1.1 hl'.1.2, ?_⟩
      rcases eq_or_lt_of_le hl'.2 with h | h
      · rw [Fin.ext h]; exact hxi
      · exact lt_trans (Fin.lt_def.1 (hmono l' l hl'.1.1 (Fin.lt_def.2 h) hl.2)) hxi
    have hcardle := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hcardle
    have hc2 : ((blockSet n a c).filter fun l' => l'.val ≤ l.val).card = l.val + 1 - a := by
      have : ((blockSet n a c).filter fun l' => l'.val ≤ l.val).image Fin.val =
          Finset.Ico a (l.val + 1) := by
        ext y
        simp only [blockSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_Ico]
        constructor
        · rintro ⟨l', ⟨⟨h1, h2⟩, h3⟩, rfl⟩; exact ⟨h1, by omega⟩
        · intro hy
          exact ⟨⟨y, by have := l.isLt; omega⟩, ⟨⟨hy.1, by show y < a + c; omega⟩, by simp; omega⟩, rfl⟩
      rw [← Finset.card_image_of_injective _ Fin.val_injective, this]
      simp
    omega
  · rintro ⟨l, hla, hlm, rfl⟩
    have hlc : l.val < a + c := by
      have : m ≤ c := hcard ▸ Finset.card_filter_le _ _
      omega
    refine ⟨hmem l hla hlc, ?_⟩
    by_contra hge
    push Not at hge
    -- every `y ∈ Y` below `i` is `σ l'` with `a ≤ l' < l`
    have hsub : (Y.filter fun y => y.val < i) ⊆
        ((blockSet n a c).filter fun l' => l'.val < l.val).image σ := by
      intro y hy
      obtain ⟨hyY, hyi⟩ := Finset.mem_filter.1 hy
      rw [← himg] at hyY
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 hyY
      simp only [blockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hl'
      refine Finset.mem_image.2 ⟨l', ?_, rfl⟩
      simp only [blockSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hl', ?_⟩
      by_contra hnot
      push Not at hnot
      rcases eq_or_lt_of_le hnot with h | h
      · have : σ l' = σ l := congrArg σ (Fin.ext h.symm)
        omega
      · have := Fin.lt_def.1 (hmono l l' hla (Fin.lt_def.2 h) hl'.2)
        omega
    have hcardle := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hcardle
    have hc2 : ((blockSet n a c).filter fun l' => l'.val < l.val).card = l.val - a := by
      have : ((blockSet n a c).filter fun l' => l'.val < l.val).image Fin.val =
          Finset.Ico a l.val := by
        ext y
        simp only [blockSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_Ico]
        constructor
        · rintro ⟨l', ⟨⟨h1, h2⟩, h3⟩, rfl⟩; exact ⟨h1, h3⟩
        · intro hy
          exact ⟨⟨y, by have := l.isLt; omega⟩, ⟨⟨hy.1, by show y < a + c; omega⟩, hy.2⟩, rfl⟩
      rw [← Finset.card_image_of_injective _ Fin.val_injective, this]
      simp
    omega

end Enum

section ShuffleEnum

variable {n : ℕ}

theorem shuffle_initial_X (X : Finset (Fin n)) (i : ℕ) (x : Fin n) :
    (x ∈ X ∧ x.val < i) ↔
      ∃ l : Fin n, 0 ≤ l.val ∧ l.val < 0 + (X.filter fun y => y.val < i).card ∧ shuffle X l = x := by
  apply enum_initial (shuffle X) 0 X.card X (by simpa using Finset.card_le_univ X)
    (shuffle X).injective
  · intro l _ hl; exact (shuffle_mem_iff X l).2 (by omega)
  · intro l l' _ hll' hl'
    rw [shuffle_apply_of_lt X (by omega), shuffle_apply_of_lt X (by omega)]
    exact (X.orderEmbOfFin rfl).strictMono (Fin.lt_def.2 (Fin.lt_def.1 hll'))
  · rfl

theorem shuffle_initial_Xc (X : Finset (Fin n)) (i : ℕ) (x : Fin n) :
    (x ∈ Xᶜ ∧ x.val < i) ↔
      ∃ l : Fin n, X.card ≤ l.val ∧
        l.val < X.card + (Xᶜ.filter fun y => y.val < i).card ∧ shuffle X l = x := by
  apply enum_initial (shuffle X) X.card (n - X.card) Xᶜ
    (by have := Finset.card_le_univ X; simp at this; omega) (shuffle X).injective
  · intro l hl _
    have : ¬ (shuffle X l ∈ X) := by rw [shuffle_mem_iff]; omega
    exact Finset.mem_compl.2 this
  · intro l l' hl hll' hl'
    rw [shuffle_apply_of_ge X (by omega), shuffle_apply_of_ge X (by have := Fin.lt_def.1 hll'; omega)]
    exact (Xᶜ.orderEmbOfFin rfl).strictMono (Fin.lt_def.2 (by have := Fin.lt_def.1 hll'; simp; omega))
  · simp [Finset.card_compl]

end ShuffleEnum

section LemmaA

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {n : ℕ}

omit [FiniteDimensional K V] in
theorem flag_eq_span (b : Module.Basis (Fin n) K V) (k : Fin (n + 1)) :
    b.flag k = Submodule.span K (b '' {j : Fin n | j.val < k.val}) := by
  unfold Module.Basis.flag
  congr 2

omit [FiniteDimensional K V] in
theorem reindex_flag_eq (b : Module.Basis (Fin n) K V) (σ : Equiv.Perm (Fin n)) (m : Fin (n + 1)) :
    (b.reindex σ.symm).flag m =
      Submodule.span K (b '' (σ '' {l : Fin n | l.val < m.val})) := by
  rw [flag_eq_span, Set.image_image]
  congr 2
  ext j
  simp [Module.Basis.reindex_apply]

omit [FiniteDimensional K V] in
theorem jhFlag_card (b : Module.Basis (Fin n) K V) : (jhFlag b).carrier.card = n + 1 := by
  show (Finset.univ.image b.flag).card = n + 1
  rw [Finset.card_image_of_injective _ b.flag_strictMono.injective]
  simp

theorem convSub_jhFlag (b : Module.Basis (Fin n) K V) (hn : finrank K V = n)
    (X : Finset (Fin n)) :
    (jhFlag b).convSub (Submodule.span K (b '' (X : Set (Fin n)))) =
      jhFlag (b.reindex (shuffle X).symm) := by
  set S := Submodule.span K (b '' (X : Set (Fin n))) with hS
  set σ := shuffle X with hσ
  have hcomp : ((jhFlag b).convSub S).IsComplete := by
    refine Flag.isComplete_concat _ _ (Flag.isComplete_restrict _ _ ?_)
      (Flag.isComplete_project _ _ ?_) <;>
    · unfold Flag.IsComplete Flag.len; rw [jhFlag_card, hn]; rfl
  have hXn : X.card ≤ n := by simpa using Finset.card_le_univ X
  have hXcn : Xᶜ.card = n - X.card := by simp [Finset.card_compl]
  have key1 : ∀ i : Fin (n + 1), ∃ m : Fin (n + 1),
      S ⊓ b.flag i = (b.reindex σ.symm).flag m := by
    intro i
    have hm : (X.filter fun y => y.val < i.val).card < n + 1 := by
      have := Finset.card_filter_le X (fun y => y.val < i.val); omega
    refine ⟨⟨_, hm⟩, ?_⟩
    rw [flag_eq_span, reindex_flag_eq, hS, jh_span_inf]
    congr 2
    ext x
    have := shuffle_initial_X X i.val x
    simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_ofPred_eq, Set.mem_image]
    rw [this]
    simp [hσ]
  have key2 : ∀ i : Fin (n + 1), ∃ m : Fin (n + 1),
      S ⊔ b.flag i = (b.reindex σ.symm).flag m := by
    intro i
    have hm : X.card + (Xᶜ.filter fun y => y.val < i.val).card < n + 1 := by
      have := Finset.card_filter_le Xᶜ (fun y => y.val < i.val); omega
    refine ⟨⟨_, hm⟩, ?_⟩
    rw [flag_eq_span, reindex_flag_eq, hS, ← Submodule.span_union, ← Set.image_union]
    congr 2
    ext x
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, Set.mem_image]
    have h1 := shuffle_initial_Xc X i.val x
    rw [← hσ] at h1
    have h2 : x ∈ X ↔ (σ.symm x).val < X.card := by
      have := shuffle_mem_iff X (σ.symm x)
      rwa [← hσ, Equiv.apply_symm_apply] at this
    constructor
    · rintro (hx | hx)
      · refine ⟨σ.symm x, ?_, by simp [hσ]⟩
        have := h2.1 hx
        omega
      · by_cases hxX : x ∈ X
        · refine ⟨σ.symm x, ?_, by simp [hσ]⟩
          have := h2.1 hxX
          omega
        · obtain ⟨l, hl1, hl2, hl3⟩ := h1.1 ⟨Finset.mem_compl.2 hxX, hx⟩
          exact ⟨l, hl2, hl3⟩
    · rintro ⟨l, hl, rfl⟩
      by_cases hlX : l.val < X.card
      · left; exact (shuffle_mem_iff X l).2 hlX
      · right
        exact (h1.2 ⟨l, by omega, hl, rfl⟩).2
  apply Flag.ext
  apply Finset.eq_of_subset_of_card_le
  · intro A hA
    rw [Flag.convSub_carrier] at hA
    obtain ⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩ := Finset.mem_union.1 hA |>.elim
      (fun h => Or.inl (Finset.mem_image.1 h)) (fun h => Or.inr (Finset.mem_image.1 h))
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hB
      obtain ⟨m, hm⟩ := key1 i
      exact Finset.mem_image.2 ⟨m, Finset.mem_univ _, hm.symm⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hB
      obtain ⟨m, hm⟩ := key2 i
      exact Finset.mem_image.2 ⟨m, Finset.mem_univ _, hm.symm⟩
  · rw [jhFlag_card]
    have := ((jhFlag b).convSub S).card_eq_len_succ
    unfold Flag.IsComplete at hcomp
    omega

theorem finrank_span_basis_image {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Module.Basis (Fin n) K V) (X : Finset (Fin n)) :
    finrank K (Submodule.span K (b '' (X : Set (Fin n)))) = X.card := by
  have h := finrank_span_eq_card (R := K) (b := fun x : X => b x.1)
    (b.linearIndependent.comp _ Subtype.val_injective)
  have hr : Set.range (fun x : X => b x.1) = b '' (X : Set (Fin n)) := by
    ext y; simp
  rw [hr] at h
  simpa using h

end LemmaA

section SchNat

variable {n : ℕ}

theorem filter_lt_split (X : Finset (Fin n)) (i : Fin n) :
    (Xᶜ.filter fun y => y.val < i.val).card + (X.filter fun y => y.val < i.val).card = i.val := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.Iio i) (fun v => v ∈ X)
  have e1 : (Finset.Iio i).filter (fun v => v ∈ X) = X.filter fun y => y.val < i.val := by
    ext v; simp [and_comm]
  have e2 : (Finset.Iio i).filter (fun v => ¬ v ∈ X) = Xᶜ.filter fun y => y.val < i.val := by
    ext v; simp [and_comm]
  rw [e1, e2, Fin.card_Iio] at this
  omega

theorem filter_lt_succ (X : Finset (Fin n)) (i : Fin n) :
    (X.filter fun y => y.val < i.val + 1).card =
      (X.filter fun y => y.val < i.val).card + if i ∈ X then 1 else 0 := by
  by_cases hi : i ∈ X
  · have : (X.filter fun y => y.val < i.val + 1) = insert i (X.filter fun y => y.val < i.val) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hy, hlt⟩
        by_cases h : y.val < i.val
        · exact Or.inr ⟨hy, h⟩
        · exact Or.inl (Fin.ext (by omega))
      · rintro (rfl | ⟨hy, hlt⟩)
        · exact ⟨hi, by omega⟩
        · exact ⟨hy, by omega⟩
    rw [this, Finset.card_insert_of_notMem (by simp), ite_eq_left hi]
  · have : (X.filter fun y => y.val < i.val + 1) = X.filter fun y => y.val < i.val := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hy, hlt⟩
        refine ⟨hy, ?_⟩
        by_contra h
        exact hi (by rwa [show y = i from Fin.ext (by omega)] at hy)
      · rintro ⟨hy, hlt⟩; exact ⟨hy, by omega⟩
    rw [this, ite_eq_right hi]; simp

theorem sch_nat (X : Finset (Fin n)) :
    ∑ i ∈ Finset.range n, ((X.filter fun y => y.val < i + 1).card -
        (X.filter fun y => y.val < i).card) * (i - (X.filter fun y => y.val < i).card) =
      inv (shuffle X) := by
  rw [inv_shuffle_eq, Finset.sum_range (fun i => ((X.filter fun y => y.val < i + 1).card -
        (X.filter fun y => y.val < i).card) * (i - (X.filter fun y => y.val < i).card))]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i ∈ X)]
  have h1 : ∀ i ∈ Finset.univ.filter (fun i : Fin n => i ∈ X),
      ((X.filter fun y => y.val < i.val + 1).card - (X.filter fun y => y.val < i.val).card) *
        (i.val - (X.filter fun y => y.val < i.val).card) = (Xᶜ.filter (· < i)).card := by
    intro i hi
    have hiX : i ∈ X := (Finset.mem_filter.1 hi).2
    rw [filter_lt_succ, ite_eq_left hiX]
    have := filter_lt_split X i
    have e : (Xᶜ.filter fun y => y.val < i.val) = Xᶜ.filter (· < i) := by
      ext y; simp
    rw [e] at this
    simp only [Nat.add_sub_cancel_left, one_mul]
    omega
  have h2 : ∀ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i ∈ X),
      ((X.filter fun y => y.val < i.val + 1).card - (X.filter fun y => y.val < i.val).card) *
        (i.val - (X.filter fun y => y.val < i.val).card) = 0 := by
    intro i hi
    have hiX : i ∉ X := (Finset.mem_filter.1 hi).2
    rw [filter_lt_succ, ite_eq_right hiX]; simp
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, add_zero]
  simp

end SchNat

section ConvSubBasis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {n : ℕ}

theorem exists_basis_convSub (hn : finrank K V = n) (H : Flag K V) (hH : H.IsComplete)
    (S : Submodule K V) :
    ∃ (b : Module.Basis (Fin n) K V) (X : Finset (Fin n)), H = jhFlag b ∧
      S = Submodule.span K (b '' (X : Set (Fin n))) ∧
      H.convSub S = jhFlag (b.reindex (shuffle X).symm) := by
  have hcomp : (H.convSub S).IsComplete :=
    Flag.isComplete_concat _ _ (Flag.isComplete_restrict _ _ hH) (Flag.isComplete_project _ _ hH)
  obtain ⟨b, σ, hHb, hGb⟩ := jh_exists_common_permutation n hn H (H.convSub S) hH hcomp
  have hSmem : S ∈ (H.convSub S).carrier := by
    rw [Flag.convSub_carrier]
    refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨⊤, H.top_mem, ?_⟩)
    simp
  rw [hGb] at hSmem
  obtain ⟨m, _, hm⟩ := Finset.mem_image.1 hSmem
  rw [reindex_flag_eq] at hm
  set X : Finset (Fin n) := Finset.univ.filter fun x => ∃ l : Fin n, l.val < m.val ∧ σ l = x
    with hX
  have hXS : S = Submodule.span K (b '' (X : Set (Fin n))) := by
    rw [← hm]; congr 2; ext x
    simp only [hX, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Set.mem_image]
  refine ⟨b, X, hHb, hXS, ?_⟩
  rw [hXS, hHb]
  exact convSub_jhFlag b hn X

omit [FiniteDimensional K V] in
theorem finrank_inf_flag (b : Module.Basis (Fin n) K V) (X : Finset (Fin n)) (k : Fin (n + 1)) :
    finrank K ↥(Submodule.span K (b '' (X : Set (Fin n))) ⊓ b.flag k) =
      (X.filter fun y => y.val < k.val).card := by
  rw [flag_eq_span, jh_span_inf]
  have : ((X : Set (Fin n)) ∩ {j : Fin n | j.val < k.val}) =
      ((X.filter fun y => y.val < k.val : Finset (Fin n)) : Set (Fin n)) := by
    ext y; simp
  rw [this, finrank_span_basis_image]

omit [FiniteDimensional K V] in
theorem finrank_flag' (b : Module.Basis (Fin n) K V) (k : Fin (n + 1)) :
    finrank K ↥(b.flag k) = k.val := by
  have := finrank_inf_flag b Finset.univ k
  have h1 : Submodule.span K (b '' ((Finset.univ : Finset (Fin n)) : Set (Fin n))) = ⊤ := by
    simp
  rw [h1, top_inf_eq] at this
  rw [this]
  have hk : k.val ≤ n := Nat.lt_succ_iff.1 k.isLt
  have := card_blockSet (n := n) (a := 0) (c := k.val) (by omega)
  simpa [blockSet] using this

end ConvSubBasis

end MartinPhd

end
end Shuffle
