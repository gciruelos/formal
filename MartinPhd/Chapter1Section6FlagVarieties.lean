import Mathlib
import MartinPhd.Chapter1Section2Cauchy
import MartinPhd.Chapter1Section6Bruhat
import MartinPhd.Chapter1Section5SubspacesFlagVarieties
import MartinPhd.Chapter1Section1FlagsPermutations

/-!
# Chapter 1, Section 1.6 (flag varieties and the Steinberg module)

Contents:
* Trace
* Types
* Chapter1Section6
* Dimension of `St^H` via traces
* YoungGen
* YoungGeneration
-/

section Trace

open Module
noncomputable section
namespace MartinPhd

/-! ## Additivity of the trace on short exact sequences -/

section Trace

variable {K : Type*} [Field K] {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B]
  [Module K B] [FiniteDimensional K A] [FiniteDimensional K B]

/-- `tr(g_A) = tr(g_A|_{ker f}) + tr(g_B)` for an equivariant surjection `f : A → B`. -/
theorem trace_ses (gA : A →ₗ[K] A) (gB : B →ₗ[K] B) (f : A →ₗ[K] B) (hf : Function.Surjective f)
    (hg : f ∘ₗ gA = gB ∘ₗ f) (hW : ∀ w ∈ LinearMap.ker f, gA w ∈ LinearMap.ker f) :
    LinearMap.trace K A gA = LinearMap.trace K (LinearMap.ker f) (gA.restrict hW) +
      LinearMap.trace K B gB := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.2 hf)
  -- the projection `π = s ∘ f` and its complement, which lands in `ker f`
  have hq : ∀ a, a - s (f a) ∈ LinearMap.ker f := fun a => by
    rw [LinearMap.mem_ker, map_sub]
    have := LinearMap.congr_fun hs (f a)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let q : A →ₗ[K] LinearMap.ker f := LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ f)
    (fun a => by simpa using hq a)
  have e1 : gA = (gA ∘ₗ (LinearMap.ker f).subtype) ∘ₗ q + (gA ∘ₗ s) ∘ₗ f := by
    apply LinearMap.ext; intro a
    simp [q]
  have t1 : LinearMap.trace K A ((gA ∘ₗ (LinearMap.ker f).subtype) ∘ₗ q) =
      LinearMap.trace K (LinearMap.ker f) (gA.restrict hW) := by
    rw [LinearMap.trace_comp_comm']
    congr 1
    apply LinearMap.ext; intro w
    apply Subtype.ext
    have hw : f w.1 = 0 := w.2
    have hfg : f (gA w.1) = 0 := by
      have := LinearMap.congr_fun hg w.1
      simp only [LinearMap.comp_apply] at this
      rw [this, hw, map_zero]
    simp [q, LinearMap.restrict_apply, hfg]
  have t2 : LinearMap.trace K A ((gA ∘ₗ s) ∘ₗ f) = LinearMap.trace K B gB := by
    rw [LinearMap.trace_comp_comm']
    have : f ∘ₗ (gA ∘ₗ s) = gB := by
      rw [← LinearMap.comp_assoc, hg, LinearMap.comp_assoc, hs, LinearMap.comp_id]
    rw [this]
  conv_lhs => rw [e1]
  rw [map_add, t1, t2]

end Trace

section PermTrace

variable {k : Type} [Field k]

/-- The trace of a map of finitely supported functions induced by a self-map counts fixed points. -/
theorem trace_lmapDomain {α : Type} [Fintype α] [DecidableEq α] (f : α → α) :
    LinearMap.trace k (α →₀ k) (Finsupp.lmapDomain k k f) =
      (Nat.card {a // f a = a} : k) := by
  rw [Nat.card_eq_fintype_card, LinearMap.trace_eq_matrix_trace k (Finsupp.basisSingleOne : Basis α k (α →₀ k))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.basisSingleOne_repr,
    LinearEquiv.refl_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_boole, Fintype.card_subtype]

theorem trace_supported {α : Type} [Fintype α] [DecidableEq α] (S : Set α) (f : α → α)
    (hS : ∀ a ∈ S, f a ∈ S)
    (h : ∀ v ∈ Finsupp.supported k k S, Finsupp.lmapDomain k k f v ∈ Finsupp.supported k k S) :
    LinearMap.trace k (Finsupp.supported k k S) ((Finsupp.lmapDomain k k f).restrict h) =
      (Nat.card {a : α // a ∈ S ∧ f a = a} : k) := by
  classical
  let e := Finsupp.supportedEquivFinsupp (M := k) (R := k) S
  let fS : S → S := fun a => ⟨f a, hS a a.2⟩
  have hconj : e.conj ((Finsupp.lmapDomain k k f).restrict h) = Finsupp.lmapDomain k k fS := by
    apply Finsupp.lhom_ext
    intro a c
    simp only [LinearEquiv.conj_apply_apply]
    have h1 : ((e.symm (Finsupp.single a c) : Finsupp.supported k k S) : α →₀ k) =
        Finsupp.single a.1 c := Finsupp.supportedEquivFinsupp_symm_single S a c
    have h2 : ((Finsupp.lmapDomain k k f).restrict h (e.symm (Finsupp.single a c))) =
        e.symm (Finsupp.single (fS a) c) := by
      apply Subtype.ext
      rw [LinearMap.restrict_coe_apply, h1, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        Finsupp.supportedEquivFinsupp_symm_single]
    rw [h2, LinearEquiv.apply_symm_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  have htr := LinearMap.trace_conj' (R := k) (M := Finsupp.supported k k S) (N := S →₀ k)
    ((Finsupp.lmapDomain k k f).restrict h) e
  rw [hconj] at htr
  rw [← htr, trace_lmapDomain]
  congr 1
  refine Nat.card_congr
    { toFun := fun a => ⟨a.1.1, a.1.2, congrArg Subtype.val a.2⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, Subtype.ext a.2.2⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }

end PermTrace

section TraceSub

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- Additivity of the trace for submodules of one ambient space:
`A ⊇ W = A ∩ ker dd` and `Bd = dd(A)`, all stable under `φ`, with `dd` commuting with `φ`. -/
theorem trace_ses_sub (φ dd : M →ₗ[K] M) (hcomm : dd ∘ₗ φ = φ ∘ₗ dd)
    (A W Bd : Submodule K M) (hA : ∀ a ∈ A, φ a ∈ A) (hW : ∀ w ∈ W, φ w ∈ W)
    (hB : ∀ b ∈ Bd, φ b ∈ Bd) (hWA : W = A ⊓ LinearMap.ker dd) (hBd : Bd = A.map dd) :
    LinearMap.trace K A (φ.restrict hA) = LinearMap.trace K W (φ.restrict hW) +
      LinearMap.trace K Bd (φ.restrict hB) := by
  subst hBd hWA
  let f : A →ₗ[K] (A.map dd) := LinearMap.codRestrict (A.map dd) (dd ∘ₗ A.subtype)
    (fun a => ⟨a.1, a.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨a, ha, hab⟩ := b.2
    exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  have hg : f ∘ₗ φ.restrict hA = φ.restrict hB ∘ₗ f := by
    apply LinearMap.ext; intro a
    apply Subtype.ext
    simp only [f, LinearMap.comp_apply, LinearMap.restrict_apply, LinearMap.codRestrict_apply,
      Submodule.subtype_apply]
    exact LinearMap.congr_fun hcomm a.1
  have hker : ∀ w ∈ LinearMap.ker f, φ.restrict hA w ∈ LinearMap.ker f := by
    intro w hw
    have := LinearMap.congr_fun hg w
    simp only [LinearMap.comp_apply] at this
    rw [LinearMap.mem_ker] at hw ⊢
    rw [this, hw, map_zero]
  have h1 := trace_ses (φ.restrict hA) (φ.restrict hB) f hf hg hker
  -- identify `ker f` with `A ⊓ ker dd`
  let e : LinearMap.ker f ≃ₗ[K] (A ⊓ LinearMap.ker dd : Submodule K M) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, by
        have this := x.2
        rw [LinearMap.mem_ker] at this
        exact congrArg Subtype.val this⟩
      invFun := fun w => ⟨⟨w.1, w.2.1⟩, by
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        exact w.2.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl
      left_inv := fun x => rfl
      right_inv := fun w => rfl }
  have h3 : LinearMap.trace K (A ⊓ LinearMap.ker dd : Submodule K M) (φ.restrict hW) =
      LinearMap.trace K (LinearMap.ker f) ((φ.restrict hA).restrict hker) := by
    have := LinearMap.trace_conj' ((φ.restrict hA).restrict hker) e
    rw [← this]
    congr 1
  rw [h3]
  exact h1

end TraceSub

section Euler

variable {k : Type} [Field k]

/-- Alternating sum for an exact complex whose only homology is in degree `n`. -/
theorem euler_alt (tC tZ tB : ℕ → k) (n : ℕ) (F0 : tC 0 = tZ 0)
    (F1 : ∀ m, tC (m + 1) = tZ (m + 1) + tB m) (F2 : ∀ m, m ≠ n → tZ m = tB m) :
    ∑ i ∈ Finset.range (n + 1), (-1 : k) ^ i * tC i = (-1 : k) ^ n * tZ n := by
  have key : ∀ N, N < n → ∑ i ∈ Finset.range (N + 1), (-1 : k) ^ i * tC i = (-1 : k) ^ N * tB N := by
    intro N
    induction N with
    | zero =>
      intro hN
      simp [F0, F2 0 (by omega)]
    | succ N ih =>
      intro hN
      rw [Finset.sum_range_succ, ih (by omega), F1, F2 (N + 1) (by omega)]
      ring
  cases n with
  | zero => simp [F0]
  | succ N =>
    rw [Finset.sum_range_succ, key N (by omega), F1]
    ring

end Euler

end MartinPhd

end
end Trace

section Types

open Module FiniteDimensional

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem finrank_comap_subtype [FiniteDimensional K V] (A S : Submodule K V) :
    finrank K (S.comap A.subtype) = finrank K (A ⊓ S : Submodule K V) := by
  rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

private theorem finrank_map_mkQ_add [FiniteDimensional K V] (A S : Submodule K V) :
    finrank K (A.map S.mkQ) + finrank K (A ⊓ S : Submodule K V) = finrank K A := by
  have := LinearMap.finrank_range_add_finrank_ker (S.mkQ ∘ₗ A.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp, Submodule.ker_mkQ,
    finrank_comap_subtype] at this
  exact this

theorem finrank_comap_mkQ [FiniteDimensional K V] (W : Submodule K V) (B : Submodule K (V ⧸ W)) :
    finrank K (Submodule.comap W.mkQ B) = finrank K W + finrank K B := by
  have hle : W ≤ Submodule.comap W.mkQ B := by
    intro x hx; simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero W).2 hx]
  have hmap := Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective W) B
  have hinf : Submodule.comap W.mkQ B ⊓ W = W := inf_eq_right.2 hle
  have h := finrank_map_mkQ_add (Submodule.comap W.mkQ B) W
  rw [hmap, hinf] at h
  omega

theorem comap_mkQ_injective (W : Submodule K V) :
    Function.Injective (Submodule.comap W.mkQ) := by
  intro A B h
  have hA := Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective W) A
  have hB := Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective W) B
  rw [← hA, ← hB, h]

theorem not_mem_image_comap_mkQ_bot {W : Submodule K V} (hW : W ≠ ⊥)
    (G : Flag K (V ⧸ W)) :
    ⊥ ∉ G.carrier.image (Submodule.comap W.mkQ) := by
  intro h
  obtain ⟨B, _, hB⟩ := Finset.mem_image.1 h
  have hle : W ≤ Submodule.comap W.mkQ B := by
    intro x hx; simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero W).2 hx]
  rw [hB] at hle
  exact hW (le_bot_iff.1 hle)

/-- Prepend a subspace `W` to a flag `G` in `V/W`. -/
def Flag.consSub (W : Submodule K V) (G : Flag K (V ⧸ W)) : Flag K V where
  carrier := Insert.insert ⊥ (G.carrier.image (Submodule.comap W.mkQ))
  isChain := by
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_image] at ha hb
    rcases ha with rfl | ⟨A, hA, rfl⟩
    · exact Or.inl bot_le
    rcases hb with rfl | ⟨B, hB, rfl⟩
    · exact Or.inr bot_le
    by_cases hAB : A = B
    · subst hAB; exact absurd rfl hab
    rcases G.isChain hA hB hAB with h | h
    · exact Or.inl (Submodule.comap_mono h)
    · exact Or.inr (Submodule.comap_mono h)
  bot_mem := Finset.mem_insert_self _ _
  top_mem := by
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⊤, G.top_mem, ?_⟩)
    exact Submodule.comap_top _

theorem Flag.consSub_carrier (W : Submodule K V) (G : Flag K (V ⧸ W)) :
    (Flag.consSub W G).carrier = Insert.insert ⊥ (G.carrier.image (Submodule.comap W.mkQ)) :=
  rfl

theorem Flag.len_consSub {W : Submodule K V} (hW : W ≠ ⊥) (G : Flag K (V ⧸ W)) :
    (Flag.consSub W G).len = G.len + 1 := by
  unfold Flag.len Flag.consSub
  simp only
  rw [Finset.card_insert_of_notMem (not_mem_image_comap_mkQ_bot hW G)]
  rw [Finset.card_image_of_injective _ (comap_mkQ_injective W)]
  have hc := G.card_eq_len_succ
  omega

theorem comap_mkQ_le_comap_mkQ_iff (W : Submodule K V) (A B : Submodule K (V ⧸ W)) :
    Submodule.comap W.mkQ A ≤ Submodule.comap W.mkQ B ↔ A ≤ B := by
  have hA := Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective W) A
  have hB := Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective W) B
  constructor
  · intro h
    have := Submodule.map_mono (f := W.mkQ) h
    rwa [hA, hB] at this
  · exact Submodule.comap_mono

theorem comap_mkQ_lt_comap_mkQ_iff (W : Submodule K V) (A B : Submodule K (V ⧸ W)) :
    Submodule.comap W.mkQ A < Submodule.comap W.mkQ B ↔ A < B := by
  simp only [lt_iff_le_not_ge, comap_mkQ_le_comap_mkQ_iff]

theorem Flag.index_consSub {W : Submodule K V} (hW : W ≠ ⊥) (G : Flag K (V ⧸ W))
    {B : Submodule K (V ⧸ W)} (_hB : B ∈ G.carrier) :
    (Flag.consSub W G).index (Submodule.comap W.mkQ B) = G.index B + 1 := by
  unfold Flag.index
  rw [Flag.consSub_carrier]
  have hne : Submodule.comap W.mkQ B ≠ ⊥ := by
    intro h
    have hle : W ≤ Submodule.comap W.mkQ B := by
      intro x hx; simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero W).2 hx]
    rw [h] at hle
    exact hW (le_bot_iff.1 hle)
  have hfilter : (Insert.insert (⊥ : Submodule K V) (G.carrier.image (Submodule.comap W.mkQ))).filter
      (· < Submodule.comap W.mkQ B) =
      Insert.insert ⊥ ((G.carrier.filter (· < B)).image (Submodule.comap W.mkQ)) := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨rfl | ⟨C, hC, rfl⟩, hlt⟩
      · exact Or.inl rfl
      · rw [comap_mkQ_lt_comap_mkQ_iff] at hlt
        exact Or.inr ⟨C, ⟨hC, hlt⟩, rfl⟩
    · rintro (rfl | ⟨C, ⟨hC, hlt⟩, rfl⟩)
      · exact ⟨Or.inl rfl, bot_lt_iff_ne_bot.2 hne⟩
      · rw [comap_mkQ_lt_comap_mkQ_iff]
        exact ⟨Or.inr ⟨C, hC, rfl⟩, hlt⟩
  rw [hfilter, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ (comap_mkQ_injective W)]
  · intro h
    obtain ⟨C, _, hC⟩ := Finset.mem_image.1 h
    have hle : W ≤ Submodule.comap W.mkQ C := by
      intro x hx; simp [Submodule.mem_comap, (Submodule.Quotient.mk_eq_zero W).2 hx]
    rw [hC] at hle
    exact hW (le_bot_iff.1 hle)

theorem Flag.nth_consSub {W : Submodule K V} (hW : W ≠ ⊥) (G : Flag K (V ⧸ W))
    {q : ℕ} (hq : q ≤ G.len) :
    (Flag.consSub W G).nth (q + 1) = Submodule.comap W.mkQ (G.nth q) := by
  have hmem : G.nth q ∈ G.carrier := Flag.nth_mem' G hq
  have hmem' : Submodule.comap W.mkQ (G.nth q) ∈ (Flag.consSub W G).carrier := by
    rw [Flag.consSub_carrier]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hmem)
  have hidx := Flag.index_consSub hW G hmem
  rw [G.index_nth hq] at hidx
  have hnth := (Flag.consSub W G).nth_index hmem'
  rwa [hidx] at hnth

theorem Flag.nth_consSub_zero {W : Submodule K V} (G : Flag K (V ⧸ W)) :
    (Flag.consSub W G).nth 0 = ⊥ :=
  Flag.nth_zero _

theorem Flag.nth_consSub_one {W : Submodule K V} (hW : W ≠ ⊥) (G : Flag K (V ⧸ W)) :
    (Flag.consSub W G).nth 1 = W := by
  have h := Flag.nth_consSub hW G (q := 0) (Nat.zero_le _)
  rw [G.nth_zero] at h
  have : Submodule.comap W.mkQ (⊥ : Submodule K (V ⧸ W)) = W := Submodule.ker_mkQ W
  rw [this] at h
  exact h

theorem Flag.project_consSub (W : Submodule K V) (G : Flag K (V ⧸ W)) :
    (Flag.consSub W G).project W = G := by
  apply Flag.ext
  ext B
  simp only [Flag.project, Flag.consSub_carrier, Finset.mem_image, Finset.mem_insert]
  constructor
  · rintro ⟨A, rfl | ⟨C, hC, rfl⟩, rfl⟩
    · rw [Submodule.map_bot]
      exact G.bot_mem
    · rw [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective W)]
      exact hC
  · intro hB
    refine ⟨Submodule.comap W.mkQ B, Or.inr ⟨B, hB, rfl⟩, ?_⟩
    rw [Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective W)]

theorem Flag.consSub_project (F : Flag K V) (hl : 1 ≤ F.len) :
    Flag.consSub (F.nth 1) (F.project (F.nth 1)) = F := by
  apply Flag.ext
  set W := F.nth 1
  rw [Flag.consSub_carrier, Flag.project_carrier F hl W rfl, Finset.image_image]
  have h_img : Finset.image (Submodule.comap W.mkQ ∘ Submodule.map W.mkQ) (F.carrier.erase ⊥) =
      F.carrier.erase ⊥ := by
    ext B
    simp only [Finset.mem_image, Finset.mem_erase, Function.comp_apply]
    constructor
    · rintro ⟨C, ⟨hC0, hC⟩, rfl⟩
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 (F.nth_one_le hC hC0)]
      exact ⟨hC0, hC⟩
    · intro ⟨hB0, hB⟩
      refine ⟨B, ⟨hB0, hB⟩, ?_⟩
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 (F.nth_one_le hB hB0)]
  rw [h_img, Finset.insert_erase F.bot_mem]

theorem Flag.typeList_consSub [FiniteDimensional K V] {W : Submodule K V} (hW : W ≠ ⊥)
    (G : Flag K (V ⧸ W)) :
    (Flag.consSub W G).typeList = finrank K W :: G.typeList := by
  unfold Flag.typeList
  rw [Flag.len_consSub hW G, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  have h0 : finrank K ((Flag.consSub W G).nth 1) - finrank K ((Flag.consSub W G).nth 0) = finrank K W := by
    rw [Flag.nth_consSub_one hW G, Flag.nth_consSub_zero, finrank_bot, Nat.sub_zero]
  rw [h0]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  dsimp only [Function.comp_def]
  have hi_le : i + 1 ≤ G.len := Nat.succ_le_of_lt (List.mem_range.1 hi)
  have hi_le' : i ≤ G.len := (Nat.le_succ i).trans hi_le
  rw [Flag.nth_consSub hW G hi_le, Flag.nth_consSub hW G hi_le',
    finrank_comap_mkQ, finrank_comap_mkQ, Nat.add_sub_add_left]

theorem flag_head_dim_of_typeList [FiniteDimensional K V] {F : Flag K V} {a : ℕ} {t : List ℕ}
    (h : F.typeList = a :: t) : finrank K (F.nth 1) = a ∧ 1 ≤ F.len := by
  have hlen : F.typeList.length = F.len := by simp [Flag.typeList]
  rw [h] at hlen
  have hl : 1 ≤ F.len := by rw [← hlen]; simp
  have hrange : List.range F.len = 0 :: List.map Nat.succ (List.range (F.len - 1)) := by
    have : F.len = (F.len - 1) + 1 := by omega
    conv_lhs => rw [this]
    exact List.range_succ_eq_map
  have hhead : F.typeList.head? = some (finrank K (F.nth 1)) := by
    unfold Flag.typeList
    rw [hrange]
    simp only [List.map_cons, List.head?_cons, Option.some.injEq]
    rw [Flag.nth_zero, finrank_bot, Nat.sub_zero]
  rw [h] at hhead
  simp only [List.head?_cons, Option.some.injEq] at hhead
  exact ⟨hhead.symm, hl⟩

theorem flag_tail_typeList [FiniteDimensional K V] {F : Flag K V} {a : ℕ} (ha : 0 < a) {t : List ℕ}
    (h : F.typeList = a :: t) : (F.project (F.nth 1)).typeList = t := by
  have ⟨hdim, hl⟩ := flag_head_dim_of_typeList h
  have hne : F.nth 1 ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdim
    omega
  have hcons := Flag.consSub_project F hl
  have htype := Flag.typeList_consSub hne (F.project (F.nth 1))
  rw [hcons] at htype
  rw [h, hdim] at htype
  exact (List.cons.inj htype).2.symm

/-- Fiber equivalence: flags of type `a :: t` with first member `W` are in bijection
with flags of type `t` in `V/W`. -/
def flagFiberEquiv [FiniteDimensional K V] {a : ℕ} (ha : 0 < a) (t : List ℕ)
    (W : {W : Submodule K V // finrank K W = a}) :
    {F : Flag K V // F.typeList = a :: t ∧ F.nth 1 = W.1} ≃
      {G : Flag K (V ⧸ W.1) // G.typeList = t} where
  toFun F := ⟨F.1.project W.1, by
    have h1 := F.2.2
    have h2 := flag_tail_typeList ha F.2.1
    rwa [h1] at h2⟩
  invFun G := ⟨Flag.consSub W.1 G.1, by
    have hne : W.1 ≠ ⊥ := by
      intro h; have := W.2; rw [h, finrank_bot] at this; omega
    refine ⟨?_, Flag.nth_consSub_one hne G.1⟩
    rw [Flag.typeList_consSub hne, W.2, G.2]⟩
  left_inv F := by
    apply Subtype.ext
    have hl := (flag_head_dim_of_typeList F.2.1).2
    have hW := F.2.2
    have hcons := Flag.consSub_project F.1 hl
    rwa [hW] at hcons
  right_inv G := by
    apply Subtype.ext
    exact Flag.project_consSub W.1 G.1

/-- Equiv between the fiber of `pi` and flags with `F.nth 1 = W.1`. -/
def fiberSubtypeEquiv [FiniteDimensional K V] {a : ℕ} {t : List ℕ}
    (W : {W : Submodule K V // finrank K W = a}) :
    {F : {F : Flag K V // F.typeList = a :: t} // (⟨F.1.nth 1, (flag_head_dim_of_typeList F.2).1⟩ : {W : Submodule K V // finrank K W = a}) = W} ≃
      {F : Flag K V // F.typeList = a :: t ∧ F.nth 1 = W.1} where
  toFun F := ⟨F.1.1, ⟨F.1.2, Subtype.ext_iff.1 F.2⟩⟩
  invFun F := ⟨⟨F.1, F.2.1⟩, Subtype.ext F.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def flagFiberEquiv' [FiniteDimensional K V] {a : ℕ} (ha : 0 < a) (t : List ℕ)
    (W : {W : Submodule K V // finrank K W = a}) :
    {F : {F : Flag K V // F.typeList = a :: t} // (⟨F.1.nth 1, (flag_head_dim_of_typeList F.2).1⟩ : {W : Submodule K V // finrank K W = a}) = W} ≃
      {G : Flag K (V ⧸ W.1) // G.typeList = t} :=
  (fiberSubtypeEquiv W).trans (flagFiberEquiv ha t W)

theorem Flag.typeList_map [FiniteDimensional K V] {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (e : V ≃ₗ[K] W) (G : Flag K V) : (G.map e).typeList = G.typeList := by
  unfold Flag.typeList
  rw [Flag.len_map]
  refine List.map_congr_left fun i _ => ?_
  rw [Flag.nth_map, Flag.nth_map, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]

def flagEquivOfLinearEquiv [FiniteDimensional K V] {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (e : V ≃ₗ[K] W) (l : List ℕ) :
    {G : Flag K V // G.typeList = l} ≃ {G : Flag K W // G.typeList = l} where
  toFun G := ⟨G.1.map e, by rw [Flag.typeList_map, G.2]⟩
  invFun G := ⟨G.1.map e.symm, by rw [Flag.typeList_map, G.2]⟩
  left_inv G := by
    apply Subtype.ext
    apply Flag.ext
    ext B
    simp only [Flag.map, Finset.mem_image]
    have hcomp : ∀ C : Submodule K V, Submodule.map (e.symm : W →ₗ[K] V) (Submodule.map (e : V →ₗ[K] W) C) = C := by
      intro C
      rw [← Submodule.map_comp]
      have : (e.symm : W →ₗ[K] V).comp (e : V →ₗ[K] W) = LinearMap.id := by ext x; simp
      rw [this, Submodule.map_id]
    constructor
    · rintro ⟨_, ⟨C, hC, rfl⟩, rfl⟩
      rw [hcomp]
      exact hC
    · intro hB
      exact ⟨Submodule.map (e : V →ₗ[K] W) B, ⟨B, hB, rfl⟩, hcomp B⟩
  right_inv G := by
    apply Subtype.ext
    apply Flag.ext
    ext B
    simp only [Flag.map, Finset.mem_image]
    have hcomp : ∀ C : Submodule K W, Submodule.map (e : V →ₗ[K] W) (Submodule.map (e.symm : W →ₗ[K] V) C) = C := by
      intro C
      rw [← Submodule.map_comp]
      have : (e : V →ₗ[K] W).comp (e.symm : W →ₗ[K] V) = LinearMap.id := by ext x; simp
      rw [this, Submodule.map_id]
    constructor
    · rintro ⟨_, ⟨C, hC, rfl⟩, rfl⟩
      rw [hcomp]
      exact hC
    · intro hB
      exact ⟨Submodule.map (e.symm : W →ₗ[K] V) B, ⟨B, hB, rfl⟩, hcomp B⟩

theorem card_flag_eq_of_linearEquiv [FiniteDimensional K V] {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (e : V ≃ₗ[K] W) (l : List ℕ) :
    Nat.card {G : Flag K V // G.typeList = l} = Nat.card {G : Flag K W // G.typeList = l} :=
  Nat.card_congr (flagEquivOfLinearEquiv e l)

theorem flag_len_zero_carrier (G : Flag K V) (hl : G.len = 0) : G.carrier = {⊥} := by
  have hc : G.carrier.card = 1 := by have := G.card_eq_len_succ; omega
  ext x
  simp only [Finset.mem_singleton]
  constructor
  · intro hx
    by_contra hne
    have hbot : ⊥ < x := bot_lt_iff_ne_bot.2 hne
    have := G.index_lt_index G.bot_mem hx hbot
    have h0 : G.index ⊥ = 0 := Flag.index_bot G
    have hx_idx : G.index x < G.carrier.card := G.index_lt_card hx
    omega
  · rintro rfl; exact G.bot_mem

theorem card_flags_nil [FiniteDimensional K V] (hn : finrank K V = 0) :
    Nat.card {G : Flag K V // G.typeList = []} = 1 := by
  have h_len : ∀ G : Flag K V, G.typeList = [] → G.len = 0 := by
    intro G hG
    have := congrArg List.length hG
    simp [Flag.typeList] at this
    exact this
  have hall : ∀ x : V, x = 0 := finrank_zero_iff_forall_zero.1 hn
  have h_top_bot : (⊤ : Submodule K V) = (⊥ : Submodule K V) := by
    ext x; simp [hall x]
  have htriv_len : (Flag.trivial : Flag K V).len = 0 := by
    unfold Flag.len Flag.trivial
    simp only
    have : ({⊥, ⊤} : Finset (Submodule K V)) = {⊥} := by
      ext x; simp [h_top_bot]
    rw [this, Finset.card_singleton]
  have h_triv : (Flag.trivial : Flag K V).typeList = [] := by
    unfold Flag.typeList
    rw [htriv_len]; rfl
  have : Unique {G : Flag K V // G.typeList = []} := by
    refine @Unique.mk' _ ⟨⟨Flag.trivial, h_triv⟩⟩ ⟨fun ⟨G₁, h₁⟩ ⟨G₂, h₂⟩ => ?_⟩
    apply Subtype.ext
    apply Flag.ext
    rw [flag_len_zero_carrier G₁ (h_len G₁ h₁), flag_len_zero_carrier G₂ (h_len G₂ h₂)]
  exact Nat.card_unique

end MartinPhd

end
end Types

section Chapter1Section6

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §1.6 Variedades de banderas parciales y el módulo de Steinberg -/

section FlagVarieties

variable (F : Type) [Field F] [Fintype F] (k : Type) [Field k]

/-- The standard Borel subgroup `B ≤ GL(Fⁿ)`: the stabilizer of the standard complete
flag (upper triangular matrices). -/
def borel (n : ℕ) : Subgroup (GLn F n) := MulAction.stabilizer (GLn F n) (stdFlag F n)

/-- A (standard) parabolic subgroup: any subgroup containing `B`. -/
def IsParabolic {n : ℕ} (P : Subgroup (GLn F n)) : Prop := borel F n ≤ P

/-- The standard parabolic of type `c`: the stabilizer of `F^{0,c}`. -/
def parabolic {n : ℕ} (c : Composition n) : Subgroup (GLn F n) :=
  MulAction.stabilizer (GLn F n) (stdFlagOfType F c)

variable {F}

/-- **Proposition 1.10.** For complete flags `F, G` in `V` with `dim V = n`:
`d` is `GL(V)`-invariant, and `d(F,G)` is the unique `σ` such that some ordered basis
`(v₁,…,vₙ)` adapted to `F` has `(v_{σ(1)},…,v_{σ(n)})` adapted to `G`. -/
theorem prop_1_10 {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (n : ℕ) (hn : finrank K V = n) (F G : Flag K V) (hF : F.IsComplete) (hG : G.IsComplete) :
    (∀ g : V ≃ₗ[K] V, jh n (g • F) (g • G) = jh n F G) ∧
    (∃ b : Basis (Fin n) K V, Flag.IsAdapted b F ∧ Flag.IsAdapted (b.reindex (jh n F G).symm) G) ∧
    (∀ σ : Equiv.Perm (Fin n),
      (∃ b : Basis (Fin n) K V, Flag.IsAdapted b F ∧ Flag.IsAdapted (b.reindex σ.symm) G) → σ = jh n F G) :=
  jh_characterization n hn F G hF hG

/-- Consequence noted after Proposition 1.10: `d(F⁰, σF⁰) = σ`.

**Gap (missing hypothesis, Proposition 1.10).** The thesis states this for an arbitrary
complete flag `F`, where `σ` acts through the matrix permuting the basis. That is false:
over `𝔽₂`, the swap of `F²` fixes the flag `0 < ⟨(1,1)⟩ < F²`, so `d(F, σF) = 1 ≠ σ`.
It holds for the standard flag `F⁰`, which is the case used later. -/
theorem jh_perm_smul (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    jh n (stdFlag F n) (permToGL F σ • stdFlag F n) = σ :=
  jh_std_perm F n σ

/-- The double coset `BgB`. -/
def doubleCoset {n : ℕ} (g : GLn F n) : Set (GLn F n) :=
  {h | ∃ b₁ ∈ borel F n, ∃ b₂ ∈ borel F n, h = b₁ * g * b₂}

/-- The Bruhat cell `BσB` of a permutation. -/
def bruhatCell {n : ℕ} (σ : Equiv.Perm (Fin n)) : Set (GLn F n) := doubleCoset (permToGL F σ)

/-- **Proposition 1.11 (Bruhat decomposition, [Abe91, 4.2]).**
`BgB = BhB ⟺ d(F⁰, gF⁰) = d(F⁰, hF⁰)`; then `BgB = BσB` for that `σ`; and
`G = ⨆_{σ ∈ Sₙ} BσB`.

**Gap (typo, Proposition 1.11).** If `φ(eᵢ) = vᵢ`, the common adapted basis
gives `φσF⁰ = gF⁰`, not the printed `σφF⁰ = gF⁰`. Consequently the element
of `B` is `σ⁻¹φ⁻¹g`. The proof uses this corrected order of composition. -/
theorem bruhat (n : ℕ) :
    (∀ g h : GLn F n, doubleCoset g = doubleCoset h ↔
      jh n (stdFlag F n) (g • stdFlag F n) = jh n (stdFlag F n) (h • stdFlag F n)) ∧
    (∀ g : GLn F n, doubleCoset g = bruhatCell (jh n (stdFlag F n) (g • stdFlag F n))) ∧
    (∀ g : GLn F n, ∃! σ : Equiv.Perm (Fin n), g ∈ bruhatCell σ) :=
  ⟨bruhatDC_eq_iff, bruhatDC_eq_perm, bruhatDC_existsUnique n⟩

/-- **Corollary 1.12.** `d` is a complete invariant of `G`-orbits on pairs of complete
flags. -/
theorem cor_1_12 (n : ℕ) (F₁ G₁ F₂ G₂ : Flag F (Fin n → F)) (h₁ : F₁.IsComplete)
    (h₂ : G₁.IsComplete) (h₃ : F₂.IsComplete) (h₄ : G₂.IsComplete) :
    (∃ g : GLn F n, g • F₁ = F₂ ∧ g • G₁ = G₂) ↔ jh n F₁ G₁ = jh n F₂ G₂ :=
  bruhat_pair_orbit n F₁ G₁ F₂ G₂ h₁ h₂ h₃ h₄

/-- The rank `|P|` of the parabolic of type `c` is the length of `c`. -/
abbrev parabolicRank {n : ℕ} (c : Composition n) : ℕ := c.length

/-- **Lemma 1.14.** `G/P ≅ Fl_c(Fⁿ)`, `g ↦ g · F^{0,c}` (the partial flag variety). -/
theorem lemma_1_14 {n : ℕ} (c : Composition n) :
    ∃ e : GLn F n ⧸ parabolic F c ≃ {G : Flag F (Fin n → F) // G.IsOfType c},
      ∀ g : GLn F n, (e g).1 = g • stdFlagOfType F c :=
  by
    let f : GLn F n ⧸ parabolic F c → {G : Flag F (Fin n → F) // G.IsOfType c} :=
      fun q => ⟨MulAction.ofQuotientStabilizer _ (stdFlagOfType F c) q, by
        induction q using Quotient.inductionOn' with
        | h g =>
          exact (Flag.isOfType_smul c g _).2 (stdFlagOfType_isOfType F c)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y h
        exact MulAction.injective_ofQuotientStabilizer _ _ (congrArg Subtype.val h)
      · intro G
        obtain ⟨g, hg⟩ := Flag.transitive_ofType c (stdFlagOfType F c) G.1
          (stdFlagOfType_isOfType F c) G.2
        exact ⟨g, Subtype.ext hg⟩
    exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

/-- **Lemma 1.15.** `Sₙ/Y_c ≅ Π_c`, `σ ↦ σ · π^{0,c}`. -/
theorem lemma_1_15 {n : ℕ} (c : Composition n) :
    ∃ e : Equiv.Perm (Fin n) ⧸ youngSubgroup c ≃ OrderedPartition (Fin n) c,
      ∀ σ : Equiv.Perm (Fin n), e σ = σ • stdPartition c :=
  by
    let f : Equiv.Perm (Fin n) ⧸ youngSubgroup c → OrderedPartition (Fin n) c :=
      MulAction.ofQuotientStabilizer _ (stdPartition c)
    have hf : Function.Bijective f := ⟨MulAction.injective_ofQuotientStabilizer _ _, by
      intro P
      obtain ⟨σ, hσ⟩ := orderedPartition_transitive c (stdPartition c) P
      exact ⟨σ, hσ⟩⟩
    exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

/-- The permutation-matrix homomorphism, for the double-coset arguments below. -/
private def section6PermHom (n : ℕ) : Equiv.Perm (Fin n) →* GLn F n where
  toFun := permToGL F
  map_one' := by ext v j; rfl
  map_mul' := permToGL_mul F

/-- **Lemma 1.16.** `P = ⨆_{σ ∈ Y_c} BσB`. -/
theorem lemma_1_16 {n : ℕ} (c : Composition n) :
    (parabolic F c : Set (GLn F n)) = ⋃ σ ∈ youngSubgroup c, bruhatCell (F := F) σ :=
  parabolic_eq_union_cells (borel F n) (parabolic F c) (stdFlag_stabilizer_le F c)
    (section6PermHom n) (youngSubgroup c) (partial_perm_stabilizer_iff F c)
    (fun g => (bruhatDC_existsUnique n g).exists)

/-- **Lemma 1.17.** If `σ⁻¹ b τ ∈ P` for some `b ∈ B`, then `σ⁻¹ τ ∈ Y_c`. -/
theorem lemma_1_17 {n : ℕ} (c : Composition n) (σ τ : Equiv.Perm (Fin n)) (b : GLn F n)
    (hb : b ∈ borel F n) (h : (permToGL F σ)⁻¹ * b * permToGL F τ ∈ parabolic F c) :
    σ⁻¹ * τ ∈ youngSubgroup c :=
  partial_bruhat_young F c σ τ b hb h

/-- The set `BσP`. -/
def borelPermParabolic {n : ℕ} (c : Composition n) (σ : Equiv.Perm (Fin n)) : Set (GLn F n) :=
  {g | ∃ b ∈ borel F n, ∃ p ∈ parabolic F c, g = b * permToGL F σ * p}

/-- The decomposition `G = ⨆_{[σ] ∈ Sₙ/Y_c} BσP` from the proof of Lemma 1.18.

**Gap (typo, Lemma 1.18).** In the reverse implication the thesis writes
`τσ⁻¹ ∈ P`; the required membership is `τ⁻¹σ ∈ P`, obtained by inverting
`σ⁻¹τ ∈ P`. The double-coset argument uses this inverse. -/
theorem bruhat_parabolic {n : ℕ} (c : Composition n) :
    (∀ g : GLn F n, ∃ σ, g ∈ borelPermParabolic c σ) ∧
    (∀ σ τ : Equiv.Perm (Fin n),
      borelPermParabolic (F := F) c σ = borelPermParabolic c τ ↔ σ⁻¹ * τ ∈ youngSubgroup c) :=
  ⟨parabolic_coset_coverage (borel F n) (parabolic F c) (stdFlag_stabilizer_le F c)
      (section6PermHom n) (fun g => (bruhatDC_existsUnique n g).exists),
    parabolic_coset_eq_iff (borel F n) (parabolic F c) (section6PermHom n)
      (youngSubgroup c) (partial_perm_stabilizer_iff F c) (partial_bruhat_young F c)⟩

/-- **Lemma 1.18.** `G/P` has `n!/(c₁!⋯c_l!)` Schubert cells (`B`-orbits). -/
theorem lemma_1_18 {n : ℕ} (c : Composition n) :
    Nat.card (MulAction.orbitRel.Quotient (borel F n) (GLn F n ⧸ parabolic F c)) =
      Nat.multinomial Finset.univ c.blocksFun :=
  by
    obtain ⟨e⟩ := doubleOrbit_equiv (borel F n) (parabolic F c) (youngSubgroup c)
      (permToGL F) (bruhat_parabolic (F := F) c).1
      (parabolic_coset_mem_iff (borel F n) (parabolic F c) (section6PermHom n)
        (youngSubgroup c) (partial_perm_stabilizer_iff F c) (partial_bruhat_young F c))
    rw [← Nat.card_congr e]
    exact youngSubgroup_quotient_card c

/-! ### Gauss polynomials -/

open Polynomial

/-- `[n]_ħ = 1 + ħ + ⋯ + ħ^{n-1}`. -/
def qInt (n : ℕ) : ℤ[X] := ∑ i ∈ Finset.range n, X ^ i

/-- `[n]_ħ! = [1]_ħ ⋯ [n]_ħ`. -/
def qFact : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => qFact n * qInt (n + 1)

/-- The Gauss polynomial (ħ-binomial) `[n choose i]_ħ`, defined by the ħ-Pascal rule so
that it is visibly in `ℤ[ħ]`; `gauss_spec` recovers the thesis's definition. -/
def gauss : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, i + 1 => gauss n i + X ^ (i + 1) * gauss n (i + 1)

/-- `[n choose i]_ħ = [n]_ħ! / ([i]_ħ! [n-i]_ħ!)` ([Kas95, IV.2.1]). -/
theorem qInt_add (a b : ℕ) : qInt (a + b) = qInt a + X ^ a * qInt b := by
  unfold qInt
  rw [Finset.sum_range_add, Finset.mul_sum]
  simp [pow_add]

theorem gauss_eq_zero : ∀ n i : ℕ, n < i → gauss n i = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | n + 1, 0, h => absurd h (by omega)
  | n + 1, i + 1, h => by
    simp only [gauss]
    rw [gauss_eq_zero n i (by omega), gauss_eq_zero n (i + 1) (by omega)]
    simp

theorem gauss_self : ∀ n : ℕ, gauss n n = 1
  | 0 => rfl
  | n + 1 => by
    simp only [gauss]
    rw [gauss_self n, gauss_eq_zero n (n + 1) (by omega)]
    simp

theorem gauss_spec (n i : ℕ) (h : i ≤ n) : qFact i * qFact (n - i) * gauss n i = qFact n := by
  induction n generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst this
    simp [qFact, gauss]
  | succ n ih =>
    cases i with
    | zero => simp [qFact, gauss]
    | succ i =>
      rcases Nat.lt_or_ge i n with hlt | hge
      · have h1 := ih i (by omega)
        have h2 := ih (i + 1) (by omega)
        have e1 : n - i = (n - (i + 1)) + 1 := by omega
        have e2 : n + 1 - (i + 1) = n - i := by omega
        have hb : qFact (n - i) = qFact (n - (i + 1)) * qInt (n - i) := by
          rw [e1]
          rfl
        have hQ : qInt (n + 1) = qInt (i + 1) + X ^ (i + 1) * qInt (n - i) := by
          rw [← qInt_add]; congr 1; omega
        have ha : qFact (i + 1) = qFact i * qInt (i + 1) := rfl
        rw [e2]
        simp only [gauss]
        have hn : qFact (n + 1) = qFact n * qInt (n + 1) := rfl
        rw [hn, hQ, ha]
        rw [ha] at h2
        linear_combination (qInt (i + 1)) * h1 + (X ^ (i + 1) * qInt (n - i)) * h2 +
          (X ^ (i + 1) * qFact i * qInt (i + 1) * gauss n (i + 1)) * hb
      · have hin : i = n := by omega
        subst hin
        simp only [gauss, Nat.sub_self, gauss_self, gauss_eq_zero i (i + 1) (by omega)]
        simp [qFact]

/-- ħ-multinomial of a list of block sizes, via the product formula (1.14). -/
def qMultinomialList : List ℕ → ℤ[X]
  | [] => 1
  | a :: l => gauss (a + l.sum) a * qMultinomialList l

/-- The ħ-multinomial `[n choose c]_ħ`. -/
def qMultinomial {n : ℕ} (c : Composition n) : ℤ[X] := qMultinomialList c.blocks

/-- `[n choose c]_ħ = [n]_ħ! / ([c₁]_ħ! ⋯ [c_l]_ħ!)`, i.e. (1.14). -/
theorem qMultinomialList_spec : ∀ l : List ℕ,
    qFact l.sum = qMultinomialList l * (l.map qFact).prod
  | [] => by simp [qMultinomialList, qFact]
  | a :: l => by
    have h := gauss_spec (a + l.sum) a (Nat.le_add_right _ _)
    rw [Nat.add_sub_cancel_left] at h
    simp only [List.sum_cons, List.map_cons, List.prod_cons, qMultinomialList]
    rw [← h, qMultinomialList_spec l]
    ring

theorem qMultinomial_spec {n : ℕ} (c : Composition n) :
    qFact n = qMultinomial c * (c.blocks.map qFact).prod := by
  have := qMultinomialList_spec c.blocks
  rw [c.blocks_sum] at this
  exact this

/-- `[n choose i]_ħ` evaluates to `(n.choose i)` at `ħ = 1`. -/
theorem eval_one_gauss : ∀ n i : ℕ, (gauss n i).eval 1 = (n.choose i : ℤ)
  | _, 0 => by simp [gauss]
  | 0, i + 1 => by simp [gauss]
  | n + 1, i + 1 => by
    simp only [gauss, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, one_mul, eval_one_gauss n i, eval_one_gauss n (i + 1),
      Nat.choose_succ_succ]
    push_cast; ring

/-- Evaluation of `[n choose i]_ħ` at `ħ = |F|` counts `i`-dimensional subspaces of `V`. -/
theorem card_submodules_eq_gauss (n : ℕ) : ∀ (i : ℕ) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V], finrank F V = n →
    (gauss n i).eval (Fintype.card F : ℤ) = (Nat.card {S : Submodule F V // finrank F S = i} : ℤ) := by
  induction n with
  | zero =>
    intro i V _ _ _ hn
    cases i with
    | zero => rw [gauss, Polynomial.eval_one, card_submodules_zero]; rfl
    | succ i =>
      rw [gauss, Polynomial.eval_zero]
      rw [card_submodules_of_gt hn (by omega)]; rfl
  | succ n ih =>
    intro i V _ _ _ hn
    cases i with
    | zero => rw [gauss, Polynomial.eval_one, card_submodules_zero]; rfl
    | succ k =>
      have e := equivProd n hn
      rw [card_submodule_eq_of_linearEquiv e]
      let W : Type := Fin n → F
      have hW : finrank F W = n := Module.finrank_fin_fun F
      have hsucc := card_submodules_succ_succ (F := F) (W := W) k
      have ih1 := ih k hW
      have ih2 := ih (k + 1) hW
      simp only [gauss, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hsucc]
      push_cast
      rw [← ih1, ← ih2]

/-- **Lemma 1.19 ([Sta12, 1.3.18]).** `[n choose i]_ħ` at `ħ = ℓ` counts `i`-dimensional
subspaces of an `n`-dimensional `F`-space; at `ħ = 1` it counts `i`-subsets of an
`n`-set. -/
theorem lemma_1_19 {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (n i : ℕ) (hn : finrank F V = n) :
    (gauss n i).eval (Fintype.card F : ℤ) = Nat.card {S : Submodule F V // finrank F S = i} ∧
    (gauss n i).eval 1 = n.choose i :=
  ⟨card_submodules_eq_gauss n i hn, eval_one_gauss n i⟩

theorem eval_one_qFact (n : ℕ) : (qFact n).eval 1 = (n.factorial : ℤ) := by
  induction n with
  | zero => simp [qFact]
  | succ n ih =>
    simp [qFact, ih, Nat.factorial_succ, qInt]
    ring

theorem eval_one_qMultinomial {n : ℕ} (c : Composition n) :
    (qMultinomial c).eval 1 = (Nat.multinomial Finset.univ c.blocksFun : ℤ) := by
  have h := congrArg (Polynomial.eval 1) (qMultinomial_spec c)
  rw [Polynomial.eval_mul, eval_one_qFact] at h
  have hp : ((c.blocks.map qFact).prod).eval 1 = ∏ i, ((c.blocksFun i).factorial : ℤ) := by
    rw [Polynomial.eval_list_prod, List.map_map]
    have : (c.blocks.map ((fun p => Polynomial.eval 1 p) ∘ qFact)) =
        List.ofFn (fun i => ((c.blocksFun i).factorial : ℤ)) := by
      rw [← c.ofFn_blocksFun, List.map_ofFn]
      congr 1; funext i; simp [Function.comp, eval_one_qFact]
    rw [this, List.prod_ofFn]
  rw [hp] at h
  have hm := Nat.multinomial_spec Finset.univ c.blocksFun
  have hm' : (∏ i, ((c.blocksFun i).factorial : ℤ)) * (Nat.multinomial Finset.univ c.blocksFun : ℤ) =
      (n.factorial : ℤ) := by
    have := congrArg (Nat.cast (R := ℤ)) hm
    push_cast at this
    rw [c.sum_blocksFun] at this
    exact this
  have hne : (∏ i, ((c.blocksFun i).factorial : ℤ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  exact mul_left_cancel₀ hne (by rw [hm']; linarith)

theorem card_flags_of_typeList :
    ∀ (l : List ℕ) (_hl : ∀ x ∈ l, 0 < x)
      (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (_hn : finrank F V = l.sum),
      (Nat.card {G : Flag F V // G.typeList = l} : ℤ) = (qMultinomialList l).eval (Fintype.card F : ℤ)
  | [], _, V, _, _, _, hn => by
    simp only [qMultinomialList, Polynomial.eval_one]
    rw [card_flags_nil hn]
    rfl
  | a :: t, hl, V, _, _, _, hn => by
    have ha : 0 < a := hl a (List.mem_cons.2 (Or.inl rfl))
    have ht_pos : ∀ x ∈ t, 0 < x := fun x hx => hl x (List.mem_cons.2 (Or.inr hx))
    let pi : {F' : Flag F V // F'.typeList = a :: t} → {W : Submodule F V // finrank F W = a} :=
      fun F' => ⟨F'.1.nth 1, (flag_head_dim_of_typeList F'.2).1⟩
    have e := (Equiv.sigmaFiberEquiv pi).symm
    have : Finite V := Module.finite_of_finite F
    have : Finite (Submodule F V) := inferInstance
    have : Finite {W : Submodule F V // finrank F W = a} := inferInstance
    cases nonempty_fintype {W : Submodule F V // finrank F W = a}
    have : Finite (Flag F V) := Finite.of_injective Flag.carrier (fun A B h => Flag.ext h)
    have : Finite {F' : Flag F V // F'.typeList = a :: t} := inferInstance
    have (W : {W : Submodule F V // finrank F W = a}) :
        Finite {F' : {F' : Flag F V // F'.typeList = a :: t} // pi F' = W} := inferInstance
    have h_card_sigma : Nat.card {F' : Flag F V // F'.typeList = a :: t} =
        ∑ W : {W : Submodule F V // finrank F W = a},
          Nat.card {F' : {F' : Flag F V // F'.typeList = a :: t} // pi F' = W} := by
      rw [Nat.card_congr e, Nat.card_sigma]
    have h_card_fib (W : {W : Submodule F V // finrank F W = a}) :
        (Nat.card {F' : {F' : Flag F V // F'.typeList = a :: t} // pi F' = W} : ℤ) =
        (qMultinomialList t).eval (Fintype.card F : ℤ) := by
      have : FiniteDimensional F (V ⧸ W.1) := inferInstance
      rw [Nat.card_congr (flagFiberEquiv' ha t W)]
      have hn' : finrank F (V ⧸ W.1) = t.sum := by
        have := Submodule.finrank_quotient_add_finrank W.1
        have hW := W.2
        simp only [List.sum_cons] at hn
        omega
      exact card_flags_of_typeList t ht_pos (V ⧸ W.1) hn'
    simp only [qMultinomialList, Polynomial.eval_mul]
    have h_sum : (∑ W : {W : Submodule F V // finrank F W = a},
        (Nat.card {F' : {F' : Flag F V // F'.typeList = a :: t} // pi F' = W} : ℤ)) =
        (gauss (a + t.sum) a).eval (Fintype.card F : ℤ) * (qMultinomialList t).eval (Fintype.card F : ℤ) := by
      have : (∑ W : {W : Submodule F V // finrank F W = a},
          (Nat.card {F' : {F' : Flag F V // F'.typeList = a :: t} // pi F' = W} : ℤ)) =
          ∑ W : {W : Submodule F V // finrank F W = a}, (qMultinomialList t).eval (Fintype.card F : ℤ) := by
        refine Finset.sum_congr rfl fun W _ => h_card_fib W
      rw [this, Finset.sum_const, nsmul_eq_mul]
      have h_card_univ : ((Finset.univ : Finset {W : Submodule F V // finrank F W = a}).card : ℤ) =
          Nat.card {W : Submodule F V // finrank F W = a} := by
        exact_mod_cast (Finset.card_univ.trans (Nat.card_eq_fintype_card (α := {W : Submodule F V // finrank F W = a})).symm)
      have hgauss := (lemma_1_19 (a + t.sum) a (by simp only [List.sum_cons] at hn; exact hn)).1
      rw [h_card_univ, ← hgauss]
    rw [h_card_sigma, Nat.cast_sum, h_sum]

/-- **Lemma 1.20.** `[n choose P]_ħ` at `ħ = ℓ` is `|G/P|`; at `ħ = 1` it is the number
of ordered partitions of type `c` of an `n`-set. -/
theorem lemma_1_20 {n : ℕ} (c : Composition n) :
    (qMultinomial c).eval (Fintype.card F : ℤ) = Nat.card (GLn F n ⧸ parabolic F c) ∧
    (qMultinomial c).eval 1 = Nat.card (OrderedPartition (Fin n) c) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨e, _⟩ := lemma_1_14 (F := F) c
    rw [Nat.card_congr e]
    have hn : finrank F (Fin n → F) = c.blocks.sum := by
      rw [Module.finrank_fin_fun, c.blocks_sum]
    exact (card_flags_of_typeList c.blocks (fun x hx => c.blocks_pos hx) (Fin n → F) hn).symm
  · have ⟨e, _⟩ := lemma_1_15 c
    rw [eval_one_qMultinomial c, ← youngSubgroup_quotient_card c, Nat.card_congr e]

theorem qInt_ne_zero {n : ℕ} (hn : 0 < n) : qInt n ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 1) h
  simp [qInt] at this
  omega

theorem qFact_ne_zero : ∀ n : ℕ, qFact n ≠ 0
  | 0 => one_ne_zero
  | n + 1 => mul_ne_zero (qFact_ne_zero n) (qInt_ne_zero (Nat.succ_pos n))

theorem gauss_symm (n i : ℕ) (h : i ≤ n) : gauss n (n - i) = gauss n i := by
  have h1 := gauss_spec n i h
  have h2 := gauss_spec n (n - i) (Nat.sub_le _ _)
  rw [Nat.sub_sub_self h] at h2
  have hne : qFact i * qFact (n - i) ≠ 0 := mul_ne_zero (qFact_ne_zero _) (qFact_ne_zero _)
  refine mul_left_cancel₀ hne ?_
  linear_combination h2 - h1

/-- The ħ-binomial theorem `∏_{i<n} (1 + ħⁱ t) = ∑_j ħ^{C(j,2)} [n choose j]_ħ tʲ`. -/
theorem qbinomial_thm (n : ℕ) : ∀ t : ℤ[X],
    ∏ i ∈ Finset.range n, (1 + X ^ i * t) =
      ∑ j ∈ Finset.range (n + 1), X ^ j.choose 2 * gauss n j * t ^ j := by
  induction n with
  | zero => intro t; simp [gauss]
  | succ n ih =>
    intro t
    rw [Finset.prod_range_succ']
    have h1 : ∀ i, 1 + X ^ (i + 1) * t = 1 + X ^ i * (X * t) := fun i => by ring
    simp_rw [h1]
    rw [ih (X * t)]
    set a : ℕ → ℤ[X] := fun j => X ^ j.choose 2 * gauss n j * (X * t) ^ j with ha
    have hchoose : ∀ j, (j + 1).choose 2 = j.choose 2 + j := fun j => by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
    have hcoef : ∀ j, X ^ (j + 1).choose 2 * gauss n j * t ^ (j + 1) = t * a j := fun j => by
      rw [ha]; simp only [hchoose]; ring
    have hcoef2 : ∀ j, X ^ (j + 1).choose 2 * (X ^ (j + 1) * gauss n (j + 1)) * t ^ (j + 1) =
        a (j + 1) := fun j => by
      rw [ha]; simp only [hchoose]; ring
    rw [Finset.sum_range_succ' _ (n + 1)]
    simp only [gauss]
    have hsplit : ∀ j, X ^ (j + 1).choose 2 * (gauss n j + X ^ (j + 1) * gauss n (j + 1)) *
        t ^ (j + 1) = t * a j + a (j + 1) := fun j => by
      rw [mul_add, add_mul, hcoef, ← hcoef2]
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    have han : a (n + 1) = 0 := by
      rw [ha]; simp [gauss_eq_zero n (n + 1) (by omega)]
    have ha0 : a 0 = 1 := by simp [ha, gauss]
    have e1 : ∑ j ∈ Finset.range (n + 1), a j = 1 + ∑ j ∈ Finset.range (n + 1), a (j + 1) := by
      rw [Finset.sum_range_succ' a n, Finset.sum_range_succ _ n, han, ha0]; ring
    simp [gauss]
    rw [e1]; ring

theorem alt_gauss_sum (m : ℕ) :
    ∑ a ∈ Finset.range (m + 1), (-1 : ℤ[X]) ^ a * gauss (m + 1) (a + 1) * X ^ (m - a).choose 2 =
      X ^ (m + 1).choose 2 := by
  have h0 := qbinomial_thm (m + 1) (-1)
  have hz : ∏ i ∈ Finset.range (m + 1), (1 + X ^ i * (-1 : ℤ[X])) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.2 (Nat.succ_pos m)) (by simp)
  rw [hz] at h0
  -- reflect
  have h1 : ∑ s ∈ Finset.range (m + 2), (-1 : ℤ[X]) ^ s * gauss (m + 1) s *
      X ^ (m + 1 - s).choose 2 = 0 := by
    rw [← Finset.sum_range_reflect]
    have : ∀ j ∈ Finset.range (m + 2),
        (-1 : ℤ[X]) ^ (m + 2 - 1 - j) * gauss (m + 1) (m + 2 - 1 - j) *
          X ^ (m + 1 - (m + 2 - 1 - j)).choose 2 =
        (-1) ^ (m + 1) * (X ^ j.choose 2 * gauss (m + 1) j * (-1) ^ j) := by
      intro j hj
      have hj' : j ≤ m + 1 := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hj
      have e1 : m + 2 - 1 - j = m + 1 - j := by omega
      have e2 : m + 1 - (m + 1 - j) = j := by omega
      rw [e1, e2, gauss_symm _ _ hj']
      have : (-1 : ℤ[X]) ^ (m + 1 - j) * (-1) ^ j = (-1) ^ (m + 1) := by
        rw [← pow_add]; congr 1; omega
      have sq : ((-1 : ℤ[X]) ^ j) * (-1) ^ j = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      linear_combination ((-1 : ℤ[X]) ^ j * (X ^ j.choose 2 * gauss (m + 1) j)) * this +
        (-((-1 : ℤ[X]) ^ (m + 1 - j)) * (X ^ j.choose 2 * gauss (m + 1) j)) * sq
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← h0, mul_zero]
  rw [Finset.sum_range_succ'] at h1
  have g0 : gauss (m + 1) 0 = 1 := rfl
  simp only [Nat.sub_zero, pow_zero, mul_one, g0, one_mul, Nat.zero_add] at h1
  have e : ∀ a ∈ Finset.range (m + 1),
      (-1 : ℤ[X]) ^ (a + 1) * gauss (m + 1) (a + 1) * X ^ (m + 1 - (a + 1)).choose 2 =
        -((-1) ^ a * gauss (m + 1) (a + 1) * X ^ (m - a).choose 2) := by
    intro a _
    rw [show m + 1 - (a + 1) = m - a by omega]; ring
  rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib] at h1
  linear_combination -h1

/-- Splitting off the first block of a composition. -/
def compCons (m : ℕ) : Composition (m + 1) ≃ Σ a : Fin (m + 1), Composition (m - a) where
  toFun c :=
    have key : 1 ≤ c.blocks.headI ∧ c.blocks.headI + c.blocks.tail.sum = m + 1 ∧
        ∀ i ∈ c.blocks.tail, 0 < i := by
      obtain ⟨h, t, e⟩ := List.exists_cons_of_ne_nil
        (fun h0 => by have := c.blocks_eq_nil.1 h0; omega : c.blocks ≠ [])
      have hs := c.blocks_sum
      rw [e] at hs
      rw [e]
      simp only [List.headI_cons, List.tail_cons, List.sum_cons] at hs ⊢
      exact ⟨c.blocks_pos (by rw [e]; simp), hs, fun i hi => c.blocks_pos (by rw [e]; simp [hi])⟩
    ⟨⟨c.blocks.headI - 1, by omega⟩, ⟨c.blocks.tail, fun hi => key.2.2 _ hi, by
      show _ = m - (c.blocks.headI - 1); omega⟩⟩
  invFun p := ⟨(p.1.val + 1) :: p.2.blocks, by
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · omega
      · exact p.2.blocks_pos hi, by
      simp only [List.sum_cons, p.2.blocks_sum]; have := p.1.isLt; omega⟩
  left_inv c := by
    obtain ⟨h, t, e⟩ := List.exists_cons_of_ne_nil
      (fun h0 => by have := c.blocks_eq_nil.1 h0; omega : c.blocks ≠ [])
    apply Composition.ext
    have := c.blocks_pos (show h ∈ c.blocks by rw [e]; simp)
    simp only [e, List.headI_cons, List.tail_cons]
    congr 1; omega
  right_inv p := by
    obtain ⟨a, d⟩ := p
    have h1 : (a.val + 1 - 1) = a.val := by omega
    refine Sigma.ext (Fin.ext (by simp)) (heq_of_eq ?_)
    apply Composition.ext
    rfl

theorem sum_comp_succ {R : Type*} [AddCommMonoid R] (m : ℕ) (f : List ℕ → R) :
    ∑ c : Composition (m + 1), f c.blocks =
      ∑ a : Fin (m + 1), ∑ d : Composition (m - a), f ((a.val + 1) :: d.blocks) := by
  rw [show (∑ a : Fin (m + 1), ∑ d : Composition (m - a), f ((a.val + 1) :: d.blocks)) =
      ∑ x : (Σ a : Fin (m + 1), Composition (m - a)), f ((x.1.val + 1) :: x.2.blocks) from
    (Fintype.sum_sigma (fun x : (Σ a : Fin (m + 1), Composition (m - a)) =>
      f ((x.1.val + 1) :: x.2.blocks))).symm]
  refine Fintype.sum_equiv (compCons m) _ _ fun c => ?_
  have hne : c.blocks ≠ [] := fun h0 => by have := c.blocks_eq_nil.1 h0; omega
  obtain ⟨h, t, e⟩ := List.exists_cons_of_ne_nil hne
  have := c.blocks_pos (show h ∈ c.blocks by rw [e]; simp)
  show f c.blocks = f ((c.blocks.headI - 1 + 1) :: c.blocks.tail)
  rw [e]; simp only [List.headI_cons, List.tail_cons]
  congr 2; omega

theorem comp_signed_sum_succ (m : ℕ) :
    ∑ c : Composition (m + 1), (-1 : ℤ[X]) ^ (m + 1 - c.length) * qMultinomial c =
      ∑ a : Fin (m + 1), (-1) ^ a.val * gauss (m + 1) (a.val + 1) *
        ∑ d : Composition (m - a), (-1 : ℤ[X]) ^ (m - a - d.length) * qMultinomial d := by
  have := sum_comp_succ m (fun l => (-1 : ℤ[X]) ^ (m + 1 - l.length) * qMultinomialList l)
  simp only [qMultinomial, Composition.length] at this ⊢
  rw [this]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hlen := d.length_le
  have hsum := d.blocks_sum
  simp only [qMultinomialList, List.sum_cons, hsum, List.length_cons]
  have ha := a.isLt
  have e1 : a.val + 1 + (m - a.val) = m + 1 := by omega
  have e2 : m + 1 - (d.blocks.length + 1) = a.val + (m - a.val - d.blocks.length) := by
    unfold Composition.length at hlen; omega
  rw [e1, e2, pow_add]
  ring

/-- **Lemma 1.21 ([Sol66, Corollary 1.1]).** `∑_{P ⊇ B} ± [n choose P]_ħ = ħ^{C(n,2)}`.

**Gap (error).** The thesis prints the sign as `(-1)^{|P|}` with `|P|` = length of the
composition. That is off by `(-1)ⁿ`: for `n = 1` the left side would be `-1`, and for
`n = 3` it would be `-ħ³`. The right sign is `(-1)^{n - |P|}`, where `n − |P|` is the
number of simple reflections in the Levi factor, as in Solomon's paper. The proof in
the thesis goes through (1.15), so the error is in the bookkeeping, not the argument.
We formalize the corrected identity.

The thesis proves the identity by evaluating at `ħ = ℓ` and using the Euler characteristic of
the Tits building (Solomon–Tits). We prove it algebraically instead, by induction on the first
block of the composition and the ħ-binomial theorem (`qbinomial_thm`). -/
theorem lemma_1_21 (n : ℕ) :
    ∑ c : Composition n, (-1 : ℤ[X]) ^ (n - c.length) * qMultinomial c = X ^ n.choose 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      haveI : Subsingleton (Composition 0) := ⟨fun a b => Composition.ext (by
        rw [(Composition.blocks_eq_nil _).2 rfl, (Composition.blocks_eq_nil _).2 rfl])⟩
      rw [Fintype.sum_subsingleton _ (Composition.ones 0)]
      simp [qMultinomial, qMultinomialList]
    | succ m =>
      rw [comp_signed_sum_succ]
      have : ∀ a : Fin (m + 1), (-1 : ℤ[X]) ^ a.val * gauss (m + 1) (a.val + 1) *
          ∑ d : Composition (m - a), (-1 : ℤ[X]) ^ (m - a - d.length) * qMultinomial d =
          (-1) ^ a.val * gauss (m + 1) (a.val + 1) * X ^ (m - a).choose 2 := fun a => by
        rw [ih (m - a) (by omega)]
      rw [Finset.sum_congr rfl fun a _ => this a, Fin.sum_univ_eq_sum_range
        (fun a => (-1 : ℤ[X]) ^ a * gauss (m + 1) (a + 1) * X ^ (m - a).choose 2)]
      exact alt_gauss_sum m


/-- Specialization at `ħ = 1`: `∑_{P ⊇ B} ± n!/(c₁!⋯c_l!) = 1` (same sign correction). -/
theorem lemma_1_21_one (n : ℕ) :
    ∑ c : Composition n, (-1 : ℤ) ^ (n - c.length) * (Nat.multinomial Finset.univ c.blocksFun : ℤ)
      = 1 := by
  have h := congrArg (Polynomial.evalRingHom 1) (lemma_1_21 n)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, Polynomial.coe_evalRingHom,
    Polynomial.eval_X, one_pow] at h
  simp only [eval_one_qMultinomial] at h
  exact h

/-! ### The Steinberg module -/

variable (F)

theorem chainBoundary_single (n : ℕ) (G : Flag F (Fin n → F)) :
    chainBoundary F k n (Finsupp.single G (1 : k)) =
      ∑ A ∈ G.carrier, if h : A ≠ ⊥ ∧ A ≠ ⊤ then
        ((-1 : k) ^ G.index A) • Finsupp.single (G.erase A h) (1 : k) else 0 := by
  simp [chainBoundary]

theorem chainBoundary_flagRep (n : ℕ) (g : GLn F n) :
    (chainBoundary F k n) ∘ₗ (flagRep F k n g) = (flagRep F k n g) ∘ₗ (chainBoundary F k n) := by
  apply Finsupp.lhom_ext
  intro G b
  have hb : Finsupp.single G b = b • Finsupp.single G (1 : k) := by simp
  rw [hb]
  simp only [LinearMap.comp_apply, map_smul]
  congr 1
  have h1 : flagRep F k n g (Finsupp.single G (1 : k)) = Finsupp.single (g • G) (1 : k) := by
    simp [flagRep]
  rw [h1, chainBoundary_single, chainBoundary_single, map_sum]
  have hc : (g • G).carrier = G.carrier.image (Submodule.map (g : (Fin n → F) →ₗ[F] (Fin n → F))) :=
    rfl
  rw [hc, Finset.sum_image (fun A _ B _ h => Submodule.map_injective_of_injective g.injective h)]
  refine Finset.sum_congr rfl fun A hA => ?_
  by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
  · have h' := (Submodule.map_ne_bot_top_iff g A).2 h
    have hi : (g • G).index (A.map (g : (Fin n → F) →ₗ[F] (Fin n → F))) = G.index A :=
      Flag.index_map g G hA
    have he : (g • G).erase (A.map (g : (Fin n → F) →ₗ[F] (Fin n → F))) h' = g • (G.erase A h) :=
      Flag.erase_map G g A h h'
    rw [dif_pos h', dif_pos h, hi, he, map_smul]
    simp [flagRep]
  · have h' : ¬ (A.map (g : (Fin n → F) →ₗ[F] (Fin n → F)) ≠ ⊥ ∧
        A.map (g : (Fin n → F) →ₗ[F] (Fin n → F)) ≠ ⊤) :=
      fun hh => h ((Submodule.map_ne_bot_top_iff g A).1 hh)
    rw [dif_neg h', dif_neg h]
    simp

theorem flagRep_mem_flagDeg (n m : ℕ) (g : GLn F n) {v : FlagModule F k n}
    (hv : v ∈ flagDeg F k n m) : flagRep F k n g v ∈ flagDeg F k n m := by
  unfold flagDeg at *
  have := lmapDomain_mem_supported (k := k) (fun G : Flag F (Fin n → F) => g • G)
    {G | G.len = m} {G | G.len = m} (fun G hG => by
      simp only [Set.mem_setOf_eq] at hG ⊢
      exact (Flag.len_map g G).trans hG) v hv
  exact this

/-- The action of `g ∈ GL(Fⁿ)` on `Stₙ`. -/
def stAct {n : ℕ} (g : GLn F n) : steinberg F k n →ₗ[k] steinberg F k n :=
  (flagRep F k n g).restrict (p := steinberg F k n) (q := steinberg F k n) (by
    intro v hv
    refine ⟨flagRep_mem_flagDeg F k n n g hv.1, ?_⟩
    have := LinearMap.congr_fun (chainBoundary_flagRep F k n g) v
    simp only [LinearMap.comp_apply] at this
    rw [LinearMap.mem_ker.1 hv.2, map_zero] at this
    exact LinearMap.mem_ker.2 this)

/-- The subspace `St^H` of `H`-invariants. -/
def stFixed {n : ℕ} (H : Subgroup (GLn F n)) : Submodule k (steinberg F k n) where
  carrier := {v | ∀ h ∈ H, stAct F k h v = v}
  add_mem' := by
    intro a b ha hb h hh
    rw [map_add, ha h hh, hb h hh]
  zero_mem' := by intro h _; exact map_zero _
  smul_mem' := by
    intro r a ha h hh
    rw [map_smul, ha h hh]

theorem trace_flagDeg (n m : ℕ) (g : GLn F n) :
    LinearMap.trace k (flagDeg F k n m)
        ((flagRep F k n g).restrict (fun v hv => flagRep_mem_flagDeg F k n m g hv)) =
      (Nat.card {G : Flag F (Fin n → F) // G.len = m ∧ g • G = G} : k) := by
  have hS : ∀ G ∈ {G : Flag F (Fin n → F) | G.len = m}, g • G ∈ {G : Flag F (Fin n → F) | G.len = m} :=
    fun G hG => (Flag.len_map g G).trans hG
  exact trace_supported (k := k) {G : Flag F (Fin n → F) | G.len = m} (fun G => g • G) hS
    (fun v hv => flagRep_mem_flagDeg F k n m g hv)

/-- The character formula (1.16) ([Hum87, 1.3], [Cur66, Thm. 2]):
`χ_St = ∑_{P ⊇ B} ± χ_P`, where `χ_P(g)` is the number of fixed points of `g` on `G/P`
(so on flags of type `c`, by Lemma 1.14); sign as in `lemma_1_21`.

We derive it from the exactness of the chain complex (Solomon–Tits): the alternating sum of
the traces on the exact complex `C_n → ⋯ → C_1` is `(-1)ⁿ` times the trace on `Stₙ`, and the
trace on `C_m = k[Fl_m(Fⁿ)]` counts fixed flags of length `m`. -/
theorem steinberg_character (n : ℕ) (g : GLn F n) :
    LinearMap.trace k _ (stAct F k g) =
      ∑ c : Composition n, (-1 : k) ^ (n - c.length) *
        (Nat.card {G : Flag F (Fin n → F) // G.IsOfType c ∧ g • G = G} : k) := by
  obtain ⟨hex, -, -⟩ := ST.claim k n (Fin n → F) (Module.finrank_fin_fun F)
  set φ := flagRep F k n g with hφ
  set dd := chainBoundary F k n with hdd
  have hcomm : dd ∘ₗ φ = φ ∘ₗ dd := chainBoundary_flagRep F k n g
  have hA : ∀ m, ∀ a ∈ flagDeg F k n m, φ a ∈ flagDeg F k n m :=
    fun m a ha => flagRep_mem_flagDeg F k n m g ha
  have hZ : ∀ m, ∀ w ∈ (flagDeg F k n m ⊓ LinearMap.ker dd), φ w ∈ (flagDeg F k n m ⊓ LinearMap.ker dd) := by
    intro m w hw
    refine ⟨hA m w hw.1, ?_⟩
    have := LinearMap.congr_fun hcomm w
    simp only [LinearMap.comp_apply] at this
    rw [LinearMap.mem_ker.1 hw.2, map_zero] at this
    exact LinearMap.mem_ker.2 this
  have hB : ∀ m, ∀ b ∈ (flagDeg F k n (m + 1)).map dd, φ b ∈ (flagDeg F k n (m + 1)).map dd := by
    rintro m b ⟨c, hc, rfl⟩
    exact ⟨φ c, hA _ c hc, (LinearMap.congr_fun hcomm c)⟩
  let tC : ℕ → k := fun m => LinearMap.trace k (flagDeg F k n m) (φ.restrict (hA m))
  let tZ : ℕ → k := fun m => LinearMap.trace k
    (flagDeg F k n m ⊓ LinearMap.ker dd : Submodule k (FlagModule F k n)) (φ.restrict (hZ m))
  let tB : ℕ → k := fun m => LinearMap.trace k ((flagDeg F k n (m + 1)).map dd) (φ.restrict (hB m))
  have F1 : ∀ m, tC (m + 1) = tZ (m + 1) + tB m := fun m =>
    trace_ses_sub φ dd hcomm (flagDeg F k n (m + 1)) _ _ (hA (m + 1)) (hZ (m + 1)) (hB m) rfl rfl
  have F0 : tC 0 = tZ 0 := by
    have hb0 : (flagDeg F k n 0).map dd = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨c, hc, rfl⟩
      rw [bd_zero_of_deg_zero F k hc]; exact zero_mem _
    have hB0 : ∀ b ∈ (flagDeg F k n 0).map dd, φ b ∈ (flagDeg F k n 0).map dd := by
      rintro b ⟨c, hc, rfl⟩
      exact ⟨φ c, hA _ c hc, (LinearMap.congr_fun hcomm c)⟩
    have h1 := trace_ses_sub φ dd hcomm (flagDeg F k n 0) _ _ (hA 0) (hZ 0) hB0 rfl rfl
    haveI : Subsingleton ↥((flagDeg F k n 0).map dd) := by rw [hb0]; infer_instance
    have h2 : LinearMap.trace k ((flagDeg F k n 0).map dd) (φ.restrict hB0) = 0 := by
      rw [Subsingleton.elim (φ.restrict hB0) 0, map_zero]
    show LinearMap.trace k _ (φ.restrict (hA 0)) = _
    rw [h1, h2, add_zero]
  have F2 : ∀ m, m ≠ n → tZ m = tB m := by
    intro m hm
    have heq : flagDeg F k n m ⊓ LinearMap.ker dd = (flagDeg F k n (m + 1)).map dd := by
      apply le_antisymm
      · intro z hz
        obtain ⟨y, hy, hyz⟩ := hex m hm z hz.1 (LinearMap.mem_ker.1 hz.2)
        exact ⟨y, hy, hyz⟩
      · rintro _ ⟨c, hc, rfl⟩
        exact ⟨bd_mem_flagDeg F k hc, LinearMap.mem_ker.2 (by
          have := ST.bd_bd (F := F) (k := k) (V := Fin n → F) c
          exact this)⟩
    show LinearMap.trace k _ _ = LinearMap.trace k _ _
    have key : ∀ (S T : Submodule k (FlagModule F k n)) (h : S = T) (h1 : ∀ w ∈ S, φ w ∈ S)
        (h2 : ∀ w ∈ T, φ w ∈ T), LinearMap.trace k S (φ.restrict h1) =
          LinearMap.trace k T (φ.restrict h2) := by
      intro S T h; subst h; intro h1 h2; rfl
    exact key _ _ heq _ _
  have hE := euler_alt tC tZ tB n F0 F1 F2
  have htC : ∀ m, tC m = (Nat.card {G : Flag F (Fin n → F) // G.len = m ∧ g • G = G} : k) :=
    fun m => trace_flagDeg F k n m g
  have htZ : tZ n = LinearMap.trace k _ (stAct F k g) := rfl
  have hn : finrank F (Fin n → F) = n := Module.finrank_fin_fun F
  haveI : Finite F := inferInstance
  have hsplit : ∀ i, tC i = ∑ c ∈ (Finset.univ : Finset (Composition n)).filter
      (fun c => c.length = i), (Nat.card {G : Flag F (Fin n → F) // G.IsOfType c ∧ g • G = G} : k) := by
    intro i
    rw [htC, card_len_eq_sum_types hn (fun G => g • G = G) i]
    push_cast
    rfl
  have hsign : ∀ i ∈ Finset.range (n + 1), (-1 : k) ^ n * (-1) ^ i = (-1) ^ (n - i) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have : (-1 : k) ^ n = (-1) ^ (n - i) * (-1) ^ i := by
      rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  rw [← htZ]
  have h1 : tZ n = (-1 : k) ^ n * ∑ i ∈ Finset.range (n + 1), (-1 : k) ^ i * tC i := by
    rw [hE, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  rw [h1, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun c : Composition n => c.length)
    (s := (Finset.univ : Finset (Composition n))) (t := Finset.range (n + 1))
    (fun c _ => Finset.mem_range.2 (Nat.lt_succ_of_le c.length_le))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← mul_assoc, hsign i hi, hsplit i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  have : c.length = i := (Finset.mem_filter.1 hc).2
  rw [this]

end FlagVarieties

end MartinPhd

end
end Chapter1Section6

section StInv

/-!
## Dimension of `St^H` via traces

For a subgroup `H ≤ GL(Fⁿ)` and `char k = 0`, `dim St^H = |H|⁻¹ ∑_{h ∈ H} tr(h | St)`
(Frobenius, as used in the proof of Lemma 1.23).
-/

open Module
noncomputable section
namespace MartinPhd

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

theorem stAct_one (n : ℕ) : stAct F k (1 : GLn F n) = LinearMap.id := by
  apply LinearMap.ext; intro v
  apply Subtype.ext
  show flagRep F k n 1 v.1 = v.1
  rw [map_one]; rfl

theorem stAct_mul (n : ℕ) (g h : GLn F n) :
    stAct F k (g * h) = stAct F k g ∘ₗ stAct F k h := by
  apply LinearMap.ext; intro v
  apply Subtype.ext
  show flagRep F k n (g * h) v.1 = flagRep F k n g (flagRep F k n h v.1)
  rw [map_mul]; rfl

instance finiteGLn (n : ℕ) : Finite (GLn F n) :=
  Finite.of_injective (fun e : GLn F n => (e : (Fin n → F) → (Fin n → F))) DFunLike.coe_injective

/-- The representation of a subgroup `H` on `Stₙ`. -/
def stRep (n : ℕ) (H : Subgroup (GLn F n)) : Representation k H (steinberg F k n) where
  toFun h := stAct F k h.1
  map_one' := stAct_one n
  map_mul' g h := stAct_mul n g.1 h.1

theorem stFixed_eq_invariants (n : ℕ) (H : Subgroup (GLn F n)) :
    stFixed F k H = Representation.invariants (k := k) (G := H) (V := steinberg F k n) (stRep (F := F) (k := k) n H) := by
  ext v
  constructor
  · intro hv h; exact hv h.1 h.2
  · intro hv h hh; exact hv ⟨h, hh⟩

theorem finrank_stFixed (n : ℕ) (H : Subgroup (GLn F n)) [Fintype H] [CharZero k] :
    (finrank k (stFixed F k H) : k) =
      (Nat.card H : k)⁻¹ * ∑ h : H, LinearMap.trace k _ (stAct F k h.1) := by
  have : Invertible (Nat.card H : k) := invertibleOfNonzero (by
    have : 0 < Nat.card H := Nat.card_pos
    exact_mod_cast this.ne')
  rw [stFixed_eq_invariants, ← Representation.card_inv_mul_sum_char_eq_finrank]
  rfl

end MartinPhd

end
end StInv

section YoungGen

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-!
# Generators of the Young subgroup

We show that for any composition `c` of `n`, the Young subgroup `youngSubgroup c`
is generated by the adjacent swaps inside blocks.
-/

/-- `Composition.index` is monotone: if `i ≤ j` in `Fin n`, then `c.index i ≤ c.index j`. -/
theorem index_mono {n : ℕ} (c : Composition n) {i j : Fin n} (h : i ≤ j) :
    c.index i ≤ c.index j := by
  by_contra! hlt
  have h1 := c.monotone_sizeUpTo (show (c.index j).val + 1 ≤ (c.index i).val from hlt)
  have h2 : (j : ℕ) < c.sizeUpTo ((c.index j).val + 1) := c.lt_sizeUpTo_index_succ j
  have h3 : c.sizeUpTo (c.index i).val ≤ (i : ℕ) := c.sizeUpTo_index_le i
  have hj : (i : ℕ) ≤ (j : ℕ) := h
  omega

/-- If `c.index i = c.index j` with `i ≤ j`, then all intermediate points `k` between `i` and `j`
satisfy `c.index k = c.index i`. -/
theorem index_eq_of_between {n : ℕ} (c : Composition n) {i j k : Fin n}
    (hij : c.index i = c.index j) (hik : i ≤ k) (hkj : k ≤ j) :
    c.index k = c.index i := by
  have h1 := index_mono c hik
  have h2 := index_mono c hkj
  rw [← hij] at h2
  exact le_antisymm h2 h1

/-- For any elements `a, b : Fin n` with `c.index a = c.index b`, the swap `Equiv.swap a b`
belongs to `W`. -/
theorem swap_mem_of_index_eq {n : ℕ} (c : Composition n) (W : Subgroup (Equiv.Perm (Fin n)))
    (h : ∀ (a : ℕ) (ha : a + 1 < n), c.index ⟨a, by omega⟩ = c.index ⟨a + 1, ha⟩ →
      Equiv.swap (⟨a, by omega⟩ : Fin n) ⟨a + 1, ha⟩ ∈ W)
    (a b : Fin n) (hi : c.index a = c.index b) :
    Equiv.swap a b ∈ W := by
  have hsw : ∀ m, ∀ a b : Fin n, b.val = m → a ≤ b → c.index a = c.index b →
      Equiv.swap a b ∈ W := by
    intro m
    induction m with
    | zero =>
      intro a b hb hab _
      have : a = b := Fin.ext (by have := show a.val ≤ b.val from hab; omega)
      subst a
      rw [Equiv.swap_self]
      exact W.one_mem
    | succ m ih =>
      intro a b hb hab hi
      by_cases he : a = b
      · subst a
        rw [Equiv.swap_self]
        exact W.one_mem
      have hab' : a.val < b.val := by
        have := show a.val ≤ b.val from hab
        have : a.val ≠ b.val := fun h => he (Fin.ext h)
        omega
      have hm : m < n := by omega
      let p : Fin n := ⟨m, hm⟩
      have hap : a ≤ p := by
        show a.val ≤ p.val
        dsimp [p]
        omega
      have hpb : p ≤ b := by
        show p.val ≤ b.val
        dsimp [p]
        omega
      have hip : c.index p = c.index a :=
        index_eq_of_between c hi hap hpb
      have h1 : Equiv.swap a p ∈ W :=
        ih a p rfl hap hip.symm
      have hp_succ : m + 1 < n := by omega
      have hp_eq : p = (⟨m, by omega⟩ : Fin n) := rfl
      have hb_eq : b = (⟨m + 1, hp_succ⟩ : Fin n) := Fin.ext (by omega)
      have h2 : Equiv.swap p b ∈ W := by
        rw [hp_eq, hb_eq]
        apply h m hp_succ
        have hp_eq' : (⟨m, by omega⟩ : Fin n) = p := Fin.ext rfl
        have hb_eq' : (⟨m + 1, hp_succ⟩ : Fin n) = b := Fin.ext (by omega)
        rw [hp_eq', hb_eq']
        exact hip.trans hi
      exact SubmonoidClass.swap_mem_trans W h1 h2
  rcases le_total a b with hab | hba
  · exact hsw b.val a b rfl hab hi
  · rw [Equiv.swap_comm]
    exact hsw a.val b a rfl hba hi.symm

/-- The Young subgroup is generated by the adjacent swaps inside blocks. -/
theorem youngSubgroup_le_of_adjacent {n : ℕ} (c : Composition n) (W : Subgroup (Equiv.Perm (Fin n)))
    (h : ∀ (a : ℕ) (ha : a + 1 < n), c.index ⟨a, by omega⟩ = c.index ⟨a + 1, ha⟩ →
      Equiv.swap (⟨a, by omega⟩ : Fin n) ⟨a + 1, ha⟩ ∈ W) :
    youngSubgroup c ≤ W := by
  let S : Set (Equiv.Perm (Fin n)) :=
    {σ | ∃ a b : Fin n, a ≠ b ∧ c.index a = c.index b ∧ σ = Equiv.swap a b}
  have hS : ∀ σ ∈ S, σ.IsSwap := by
    rintro σ ⟨a, b, hab, _, rfl⟩
    exact ⟨a, b, hab, rfl⟩
  have hSW : Subgroup.closure S ≤ W := by
    rw [Subgroup.closure_le]
    rintro σ ⟨a, b, _, hi, rfl⟩
    exact swap_mem_of_index_eq c W h a b hi
  intro σ hσ
  apply hSW
  apply (mem_closure_isSwap hS).2
  refine ⟨Set.toFinite _, fun a => ?_⟩
  apply (swap_mem_closure_isSwap hS).1
  by_cases he : σ a = a
  · rw [he, Equiv.swap_self]
    exact (Subgroup.closure S).one_mem
  · exact Subgroup.subset_closure ⟨σ a, a, he, (mem_youngSubgroup_iff c σ).1 hσ a, rfl⟩

end MartinPhd

end
end YoungGen

section YoungGeneration

/-! Generators for Young subgroups needed in the parabolic classification. -/
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

/-- A subgroup containing all adjacent swaps inside each block contains the
corresponding Young subgroup. -/
theorem youngSubgroup_le_of_adjacent_swaps {n : ℕ} (c : Composition n)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : ∀ a b : Fin n, b.val = a.val + 1 → c.index a = c.index b →
      Equiv.swap a b ∈ H) : youngSubgroup c ≤ H := by
  have hsw : ∀ m, ∀ a b : Fin n, b.val = m → a ≤ b → c.index a = c.index b →
      Equiv.swap a b ∈ H := by
    intro m
    induction m with
    | zero =>
      intro a b hb hab _
      have : a = b := Fin.ext (by have := show a.val ≤ b.val from hab; omega)
      subst a
      rw [Equiv.swap_self]; exact H.one_mem
    | succ m ih =>
      intro a b hb hab hi
      by_cases he : a = b
      · subst a; rw [Equiv.swap_self]; exact H.one_mem
      have hab' : a.val < b.val := by
        have := show a.val ≤ b.val from hab
        have : a.val ≠ b.val := fun h => he (Fin.ext h)
        omega
      let p : Fin n := ⟨m, by omega⟩
      have hip : c.index p = c.index a := by
        apply (mem_stdBlock_iff c (c.index a) p).1
        simp only [stdBlock, Finset.mem_filter, Finset.mem_univ, true_and]
        have ha := c.sizeUpTo_index_le a
        have hb' := c.lt_sizeUpTo_index_succ b
        rw [← hi] at hb'
        change b.val < c.sizeUpTo ((c.index a).val + 1) at hb'
        constructor <;> dsimp [p] <;> omega
      exact SubmonoidClass.swap_mem_trans H
        (ih a p rfl (by change a.val ≤ m; omega) hip.symm)
        (hH p b (by dsimp [p]; omega) (hip.trans hi))
  have hsame : ∀ a b : Fin n, c.index a = c.index b → Equiv.swap a b ∈ H := by
    intro a b hi
    rcases le_total a b with h | h
    · exact hsw b.val a b rfl h hi
    · rw [Equiv.swap_comm]; exact hsw a.val b a rfl h hi.symm
  let S : Set (Equiv.Perm (Fin n)) :=
    {σ | ∃ a b : Fin n, a ≠ b ∧ c.index a = c.index b ∧ σ = Equiv.swap a b}
  have hS : ∀ σ ∈ S, σ.IsSwap := by
    rintro σ ⟨a, b, hab, _, rfl⟩
    exact ⟨a, b, hab, rfl⟩
  have hSH : Subgroup.closure S ≤ H := by
    rw [Subgroup.closure_le]
    rintro σ ⟨a, b, _, hi, rfl⟩
    exact hsame a b hi
  intro σ hσ
  apply hSH
  apply (mem_closure_isSwap hS).2
  refine ⟨Set.toFinite _, fun a => ?_⟩
  apply (swap_mem_closure_isSwap hS).1
  by_cases he : σ a = a
  · rw [he, Equiv.swap_self]; exact (Subgroup.closure S).one_mem
  · exact Subgroup.subset_closure ⟨σ a, a, he,
      (mem_youngSubgroup_iff c σ).1 hσ a, rfl⟩

end MartinPhd

end
end YoungGeneration
