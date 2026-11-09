import MartinPhd.Chapter1Section1FlagsPermutations

/-!
# Chapter 1, Section 1.2 (GL-species, Cauchy product), with flag lemmas for Section 1.1

Contents:
* FlagLemmas
* FlagFaces
* Cauchy
-/

section FlagLemmas

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## Auxiliary lemmas on flags (restriction, projection, push-forward) -/

section FlagLemmas

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem Flag.nth_mono (F : Flag K V) {i j : ℕ} (hij : i ≤ j) (hj : j < F.carrier.card) :
    F.nth i ≤ F.nth j := by
  rcases hij.lt_or_eq with h | h
  · exact (F.nth_lt_nth h hj).le
  · rw [h]

theorem Flag.index_bot (F : Flag K V) : F.index ⊥ = 0 := by
  unfold Flag.index
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun x _ => not_lt_bot

/-- The predecessor of a member in a flag. -/
theorem Flag.pred_le (F : Flag K V) {A : Submodule K V} (hA : A ∈ F.carrier) :
    F.nth (F.index A - 1) ≤ A := by
  conv_rhs => rw [← F.nth_index hA]
  exact F.nth_mono (Nat.sub_le _ _) (F.index_lt_card hA)

theorem Flag.le_pred {F : Flag K V} {A A' : Submodule K V} (hA : A ∈ F.carrier)
    (hA' : A' ∈ F.carrier) (h : A < A') : A ≤ F.nth (F.index A' - 1) := by
  have h1 := F.index_lt_index hA hA' h
  conv_lhs => rw [← F.nth_index hA]
  exact F.nth_mono (by omega) (by have := F.index_lt_card hA'; omega)

theorem Flag.map_refl (F : Flag K V) : F.map (LinearEquiv.refl K V) = F := by
  apply Flag.ext
  simp only [Flag.map]
  exact (Finset.image_congr (g := id) (fun A _ => Submodule.map_id A)).trans Finset.image_id

theorem Flag.map_trans {W X : Type*} [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
    (F : Flag K V) (e : V ≃ₗ[K] W) (f : W ≃ₗ[K] X) :
    F.map (e.trans f) = (F.map e).map f := by
  apply Flag.ext
  simp only [Flag.map, Finset.image_image]
  apply Finset.image_congr
  intro A _
  show _ = Submodule.map (f : W →ₗ[K] X) (Submodule.map (e : V →ₗ[K] W) A)
  rw [← Submodule.map_comp]
  rfl

theorem Flag.restrict_map {W : Type*} [AddCommGroup W] [Module K W] (G : Flag K V)
    (e : V ≃ₗ[K] W) (S : Submodule K V) :
    (G.map e).restrict (S.map (e : V →ₗ[K] W)) = (G.restrict S).map (e.submoduleMap S) := by
  apply Flag.ext
  simp only [Flag.map, Flag.restrict, Finset.image_image]
  apply Finset.image_congr
  intro A _
  apply Submodule.ext
  intro x
  simp only [Function.comp_apply, Submodule.mem_comap, Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, hax⟩
    have hx := x.2
    obtain ⟨s, hs, hsx⟩ := Submodule.mem_map.1 hx
    have : a = s := by
      apply e.injective
      simp only [LinearEquiv.coe_coe] at hax hsx
      exact hax.trans hsx.symm
    subst this
    exact ⟨⟨a, hs⟩, ha, Subtype.ext hax⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem Flag.project_map {W : Type*} [AddCommGroup W] [Module K W] (G : Flag K V)
    (e : V ≃ₗ[K] W) (S : Submodule K V) :
    (G.map e).project (S.map (e : V →ₗ[K] W)) =
      (G.project S).map (Submodule.Quotient.equiv S _ e rfl) := by
  apply Flag.ext
  simp only [Flag.map, Flag.project, Finset.image_image]
  apply Finset.image_congr
  intro A _
  simp only [Function.comp_apply]
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

theorem Flag.project_project (G : Flag K V) (T S : Submodule K V) (h : T ≤ S) :
    ((G.project T).project (S.map T.mkQ)).map (Submodule.quotientQuotientEquivQuotient T S h) =
      G.project S := by
  apply Flag.ext
  simp only [Flag.map, Flag.project, Finset.image_image]
  apply Finset.image_congr
  intro A _
  simp only [Function.comp_apply]
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

theorem Flag.restrict_restrict (G : Flag K V) (T S : Submodule K V) (h : T ≤ S) :
    ((G.restrict S).restrict (T.comap S.subtype)).map (Submodule.comapSubtypeEquivOfLe h) =
      G.restrict T := by
  apply Flag.ext
  simp only [Flag.map, Flag.restrict, Finset.image_image]
  apply Finset.image_congr
  intro A _
  apply Submodule.ext
  intro x
  simp only [Function.comp_apply, Submodule.mem_comap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨(Submodule.comapSubtypeEquivOfLe h).symm x, hx, LinearEquiv.apply_symm_apply _ x⟩

theorem Flag.project_bot (G : Flag K V) :
    G.project ⊥ = G.map (Submodule.quotEquivOfEqBot (⊥ : Submodule K V) rfl).symm := by
  apply Flag.ext
  simp only [Flag.map, Flag.project]
  apply Finset.image_congr
  intro A _
  congr 1

theorem Flag.restrict_top (G : Flag K V) :
    G.restrict ⊤ = G.map (Submodule.topEquiv (R := K) (M := V)).symm := by
  apply Flag.ext
  simp only [Flag.map, Flag.restrict]
  apply Finset.image_congr
  intro A _
  apply Submodule.ext
  intro x
  simp only [Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨x.1, hx, by ext; rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ha

/-- The isomorphism `S/(T∩S) ≃ (S+T)/T` used in the axiom `proj_res`. -/
def projResIso (T S : Submodule K V) (_h : T ≤ S) :
    (S ⧸ T.comap S.subtype) ≃ₗ[K] (S.map T.mkQ) :=
  (((Submodule.quotEquivOfEq _ _ (by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
    (T.mkQ ∘ₗ S.subtype).quotKerEquivRange).trans
    (LinearEquiv.ofEq _ _ (by
      rw [LinearMap.range_comp, Submodule.range_subtype])))

theorem projResIso_mk (T S : Submodule K V) (h : T ≤ S) (s : S) :
    ((projResIso T S h) (Submodule.Quotient.mk s) : V ⧸ T) = T.mkQ s := rfl

theorem Flag.project_restrict (G : Flag K V) (T S : Submodule K V) (h : T ≤ S) :
    ((G.restrict S).project (T.comap S.subtype)).map (projResIso T S h) =
      (G.project T).restrict (S.map T.mkQ) := by
  apply Flag.ext
  simp only [Flag.map, Flag.restrict, Flag.project, Finset.image_image]
  apply Finset.image_congr
  intro A _
  apply Submodule.ext
  intro y
  simp only [Function.comp_apply, Submodule.mem_comap, Submodule.mem_map]
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨a, ha, hay⟩
    obtain ⟨s, hs, hsy⟩ := Submodule.mem_map.1 y.2
    have hat : a - s ∈ T := by
      rw [← Submodule.Quotient.eq]
      simp only [Submodule.mkQ_apply] at hay hsy
      rw [show (Submodule.Quotient.mk a : V ⧸ T) = y from hay]
      exact hsy.symm
    have haS : a ∈ S := by
      have := h hat
      simpa using S.add_mem this hs
    refine ⟨Submodule.Quotient.mk (⟨a, haS⟩ : S), ⟨⟨a, haS⟩, ha, rfl⟩, ?_⟩
    apply Subtype.ext
    exact hay

theorem Flag.erase_map {W : Type*} [AddCommGroup W] [Module K W] (G : Flag K V)
    (e : V ≃ₗ[K] W) (A : Submodule K V) (hA : A ≠ ⊥ ∧ A ≠ ⊤)
    (hA' : A.map (e : V →ₗ[K] W) ≠ ⊥ ∧ A.map (e : V →ₗ[K] W) ≠ ⊤) :
    (G.map e).erase (A.map (e : V →ₗ[K] W)) hA' = (G.erase A hA).map e := by
  apply Flag.ext
  simp only [Flag.map, Flag.erase]
  exact (Finset.image_erase (Submodule.map_injective_of_injective e.injective) _ _).symm

theorem Submodule.map_ne_bot_top_iff {W : Type*} [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (A : Submodule K V) :
    (A.map (e : V →ₗ[K] W) ≠ ⊥ ∧ A.map (e : V →ₗ[K] W) ≠ ⊤) ↔ (A ≠ ⊥ ∧ A ≠ ⊤) := by
  have h1 : A.map (e : V →ₗ[K] W) = ⊥ ↔ A = ⊥ := by
    rw [← Submodule.map_bot (e : V →ₗ[K] W)]
    exact (Submodule.map_injective_of_injective e.injective).eq_iff
  have h2 : A.map (e : V →ₗ[K] W) = ⊤ ↔ A = ⊤ := by
    have : (⊤ : Submodule K W) = (⊤ : Submodule K V).map (e : V →ₗ[K] W) := by
      rw [Submodule.map_top]; exact (LinearEquiv.range e).symm
    rw [this]
    exact (Submodule.map_injective_of_injective e.injective).eq_iff
  rw [Ne, Ne, h1, h2]

theorem lmapDomain_mem_supported {α β : Type*} {k : Type} [Field k] (f : α → β) (s : Set α)
    (t : Set β) (h : ∀ a ∈ s, f a ∈ t) (x : α →₀ k) (hx : x ∈ Finsupp.supported k k s) :
    Finsupp.lmapDomain k k f x ∈ Finsupp.supported k k t := by
  rw [Finsupp.mem_supported] at hx ⊢
  intro b hb
  have := Finsupp.mapDomain_support (f := f) (s := x) (by simpa [Finsupp.lmapDomain_apply] using hb)
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 this
  exact h a (hx ha)

end FlagLemmas

end MartinPhd

end
end FlagLemmas

section FlagFaces

open scoped BigOperators
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## Flag faces: `nth`/`len` of erased, projected and restricted flags -/

section FlagFaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem Flag.index_nth (G : Flag K V) {p : ℕ} (hp : p ≤ G.len) : G.index (G.nth p) = p :=
  (G.nth_mem (i := p) (by have := G.card_eq_len_succ; omega)).2

theorem Flag.nth_mem' (G : Flag K V) {p : ℕ} (hp : p ≤ G.len) : G.nth p ∈ G.carrier :=
  (G.nth_mem (i := p) (by have := G.card_eq_len_succ; omega)).1

theorem Flag.ext_nth {G H : Flag K V} (hl : G.len = H.len) (h : ∀ q ≤ G.len, G.nth q = H.nth q) :
    G = H := by
  apply Flag.ext
  rw [G.carrier_eq_image_nth, H.carrier_eq_image_nth, G.card_eq_len_succ, H.card_eq_len_succ, hl]
  apply Finset.image_congr
  intro q hq
  rw [Finset.mem_coe, Finset.mem_range] at hq
  exact h q (by omega)

theorem Flag.nth_ne_bot_top (G : Flag K V) {p : ℕ}
    (h : 0 < p ∧ p < G.len) : G.nth p ≠ ⊥ ∧ G.nth p ≠ ⊤ := by
  have hc := G.card_eq_len_succ
  constructor
  · intro h0
    have := G.nth_lt_nth h.1 (by omega)
    rw [Flag.nth_zero, ← h0] at this
    exact lt_irrefl _ this
  · intro h0
    have := G.nth_lt_nth h.2 (by omega : G.len < G.carrier.card)
    rw [Flag.nth_len, ← h0] at this
    exact lt_irrefl _ this

/-- Erase the `p`-th member (junk `G` when `p` is not intermediate). -/
def Flag.eraseAt (G : Flag K V) (p : ℕ) : Flag K V :=
  if h : 0 < p ∧ p < G.len then G.erase (G.nth p) (Flag.nth_ne_bot_top G h) else G

theorem Flag.eraseAt_carrier (G : Flag K V) {p : ℕ} (h : 0 < p ∧ p < G.len) :
    (G.eraseAt p).carrier = G.carrier.erase (G.nth p) := by
  simp only [Flag.eraseAt, dif_pos h, Flag.erase]

theorem Flag.len_eraseAt (G : Flag K V) {p : ℕ} (h : 0 < p ∧ p < G.len) :
    (G.eraseAt p).len = G.len - 1 := by
  unfold Flag.len
  rw [G.eraseAt_carrier h, Finset.card_erase_of_mem (G.nth_mem' h.2.le)]

theorem Flag.index_eraseAt (G : Flag K V) {p : ℕ} (h : 0 < p ∧ p < G.len) {B : Submodule K V}
    (hB : B ∈ (G.eraseAt p).carrier) :
    (G.eraseAt p).index B = if G.nth p < B then G.index B - 1 else G.index B := by
  rw [G.eraseAt_carrier h] at hB
  unfold Flag.index
  rw [G.eraseAt_carrier h, Finset.filter_erase]
  split_ifs with hlt
  · rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨G.nth_mem' h.2.le, hlt⟩)]
  · rw [Finset.erase_eq_of_notMem]
    intro hm
    exact hlt (Finset.mem_filter.1 hm).2

theorem Flag.nth_eraseAt (G : Flag K V) {p : ℕ} (h : 0 < p ∧ p < G.len) {q : ℕ}
    (hq : q ≤ G.len - 1) :
    (G.eraseAt p).nth q = if q < p then G.nth q else G.nth (q + 1) := by
  have hlen : p ≤ G.len := h.2.le
  split_ifs with hqp
  · have hmem : G.nth q ∈ (G.eraseAt p).carrier := by
      rw [G.eraseAt_carrier h]
      refine Finset.mem_erase.2 ⟨?_, G.nth_mem' (by omega)⟩
      exact (G.nth_lt_nth hqp (by have := G.card_eq_len_succ; omega)).ne
    have hlt : ¬ G.nth p < G.nth q := fun hh =>
      absurd (G.index_lt_index (G.nth_mem' hlen) (G.nth_mem' (by omega)) hh)
        (by rw [G.index_nth hlen, G.index_nth (by omega)]; omega)
    rw [← (G.eraseAt p).nth_index hmem, G.index_eraseAt h hmem, if_neg hlt, G.index_nth (by omega)]
  · have hmem : G.nth (q + 1) ∈ (G.eraseAt p).carrier := by
      rw [G.eraseAt_carrier h]
      refine Finset.mem_erase.2 ⟨?_, G.nth_mem' (by omega)⟩
      exact (G.nth_lt_nth (by omega : p < q + 1)
        (by have := G.card_eq_len_succ; omega)).ne'
    have hlt : G.nth p < G.nth (q + 1) :=
      G.nth_lt_nth (by omega) (by have := G.card_eq_len_succ; omega)
    rw [← (G.eraseAt p).nth_index hmem, G.index_eraseAt h hmem, if_pos hlt,
      G.index_nth (by omega)]
    simp

/-- Index of an image member under an order embedding on the generating set. -/
theorem Flag.index_image {W : Type*} [AddCommGroup W] [Module K W] (H : Flag K W)
    (S : Finset (Submodule K V)) (f : Submodule K V → Submodule K W)
    (hH : H.carrier = S.image f) (hf : ∀ x ∈ S, ∀ y ∈ S, f x < f y ↔ x < y)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) {B : Submodule K V}
    (hB : B ∈ S) : H.index (f B) = (S.filter (· < B)).card := by
  unfold Flag.index
  rw [hH]
  have : (S.image f).filter (· < f B) = (S.filter (· < B)).image f := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨A, hA, rfl⟩, hlt⟩
      exact ⟨A, ⟨hA, (hf A hA B hB).1 hlt⟩, rfl⟩
    · rintro ⟨A, ⟨hA, hlt⟩, rfl⟩
      exact ⟨⟨A, hA, rfl⟩, (hf A hA B hB).2 hlt⟩
  rw [this, Finset.card_image_of_injOn]
  intro x hx y hy hxy
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
  exact hinj x hx.1 y hy.1 hxy

theorem Flag.index_pos_of_ne_bot (G : Flag K V) {B : Submodule K V} (hB : B ∈ G.carrier)
    (h : B ≠ ⊥) : 0 < G.index B := by
  by_contra h0
  apply h
  have : G.index B = G.index ⊥ := by rw [Flag.index_bot]; omega
  exact G.index_injOn hB G.bot_mem this

theorem Flag.nth_one_le (G : Flag K V) {B : Submodule K V} (hB : B ∈ G.carrier)
    (h : B ≠ ⊥) : G.nth 1 ≤ B := by
  have h1 := G.index_pos_of_ne_bot hB h
  conv_rhs => rw [← G.nth_index hB]
  exact G.nth_mono h1 (G.index_lt_card hB)

theorem Flag.le_nth_pred (G : Flag K V) {B : Submodule K V} (hB : B ∈ G.carrier)
    (h : B ≠ ⊤) : B ≤ G.nth (G.len - 1) := by
  have h1 : G.index B < G.len := by
    have h2 : G.index B < G.carrier.card := G.index_lt_card hB
    have := G.card_eq_len_succ
    by_contra hh
    apply h
    have : G.index B = G.index ⊤ := by
      have e : G.index ⊤ = G.len := by
        have hm := (G.nth_mem (i := G.len) (by omega)).2
        rwa [G.nth_len] at hm
      omega
    exact G.index_injOn hB G.top_mem this
  have hc := G.card_eq_len_succ
  conv_lhs => rw [← G.nth_index hB]
  exact G.nth_mono (by omega) (by omega)

/-! ### Projection at `G₁` -/

theorem map_mkQ_le_iff (T x y : Submodule K V) (hx : T ≤ x) (hy : T ≤ y) :
    x.map T.mkQ ≤ y.map T.mkQ ↔ x ≤ y := by
  rw [Submodule.map_le_iff_le_comap, Submodule.comap_map_mkQ, sup_eq_right.2 hy]

theorem Flag.project_carrier (G : Flag K V) (hl : 1 ≤ G.len) (T : Submodule K V)
    (hT : G.nth 1 = T) :
    (G.project T).carrier = (G.carrier.erase ⊥).image (Submodule.map T.mkQ) := by
  have hc := G.card_eq_len_succ
  have hT1 : T ∈ G.carrier.erase ⊥ := by
    subst hT
    refine Finset.mem_erase.2 ⟨?_, G.nth_mem' hl⟩
    intro h
    have := G.nth_lt_nth (by omega : 0 < 1) (by omega)
    rw [Flag.nth_zero, h] at this
    exact lt_irrefl _ this
  ext C
  simp only [Flag.project, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨B, hB, rfl⟩
    by_cases hb : B = ⊥
    · subst hb
      refine ⟨T, ⟨(Finset.mem_erase.1 hT1).1, (Finset.mem_erase.1 hT1).2⟩, ?_⟩
      rw [Submodule.map_bot, eq_bot_iff, Submodule.map_le_iff_le_comap]
      simp
    · exact ⟨B, ⟨hb, hB⟩, rfl⟩
  · rintro ⟨B, ⟨_, hB⟩, rfl⟩
    exact ⟨B, hB, rfl⟩

theorem Flag.ne_bot_of_pos (G : Flag K V) {q : ℕ} (hq : 0 < q) (hq' : q ≤ G.len) :
    G.nth q ≠ ⊥ := by
  have hc := G.card_eq_len_succ
  intro h
  have := G.nth_lt_nth hq (by omega : q < G.carrier.card)
  rw [Flag.nth_zero, h] at this
  exact lt_irrefl _ this

theorem Flag.ne_top_of_lt (G : Flag K V) {q : ℕ} (hq : q < G.len) : G.nth q ≠ ⊤ := by
  have hc := G.card_eq_len_succ
  intro h
  have := G.nth_lt_nth hq (by omega : G.len < G.carrier.card)
  rw [Flag.nth_len, h] at this
  exact lt_irrefl _ this

theorem Flag.len_project (G : Flag K V) (hl : 1 ≤ G.len) (T : Submodule K V)
    (hT : G.nth 1 = T) : (G.project T).len = G.len - 1 := by
  have hc := G.card_eq_len_succ
  have hinj : Set.InjOn (Submodule.map T.mkQ) ((G.carrier.erase ⊥ : Finset _) : Set _) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_coe.1 hx
    have hy' := Finset.mem_coe.1 hy
    rw [Finset.mem_erase] at hx' hy'
    have h1 := hT ▸ G.nth_one_le hx'.2 hx'.1
    have h2 := hT ▸ G.nth_one_le hy'.2 hy'.1
    exact le_antisymm ((map_mkQ_le_iff T x y h1 h2).1 hxy.le) ((map_mkQ_le_iff T y x h2 h1).1 hxy.ge)
  unfold Flag.len
  rw [G.project_carrier hl T hT, Finset.card_image_of_injOn hinj,
    Finset.card_erase_of_mem G.bot_mem]

theorem Flag.nth_project (G : Flag K V) (hl : 1 ≤ G.len) (T : Submodule K V)
    (hT : G.nth 1 = T) {q : ℕ} (hq : q ≤ G.len - 1) :
    (G.project T).nth q = (G.nth (q + 1)).map T.mkQ := by
  have hc := G.card_eq_len_succ
  have hB : G.nth (q + 1) ∈ G.carrier.erase ⊥ :=
    Finset.mem_erase.2 ⟨G.ne_bot_of_pos (by omega) (by omega), G.nth_mem' (by omega)⟩
  have hle : ∀ x ∈ G.carrier.erase ⊥, T ≤ x := by
    intro x hx
    rw [Finset.mem_erase] at hx
    exact hT ▸ G.nth_one_le hx.2 hx.1
  have hmem : (G.nth (q + 1)).map T.mkQ ∈ (G.project T).carrier := by
    rw [G.project_carrier hl T hT]
    exact Finset.mem_image_of_mem _ hB
  have hidx : (G.project T).index ((G.nth (q + 1)).map T.mkQ) = q := by
    rw [Flag.index_image (G.project T) (G.carrier.erase ⊥) (Submodule.map T.mkQ)
      (G.project_carrier hl T hT) ?_ ?_ hB]
    · have : (G.carrier.erase ⊥).filter (· < G.nth (q + 1)) =
          (G.carrier.filter (· < G.nth (q + 1))).erase ⊥ := by
        ext A; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
      rw [this, Finset.card_erase_of_mem]
      · have := G.index_nth (p := q + 1) (by omega)
        unfold Flag.index at this
        omega
      · refine Finset.mem_filter.2 ⟨G.bot_mem, ?_⟩
        exact bot_lt_iff_ne_bot.2 (G.ne_bot_of_pos (by omega) (by omega))
    · intro x hx y hy
      rw [lt_iff_le_not_ge, lt_iff_le_not_ge, map_mkQ_le_iff T x y (hle x hx) (hle y hy),
        map_mkQ_le_iff T y x (hle y hy) (hle x hx)]
    · intro x hx y hy hxy
      exact le_antisymm ((map_mkQ_le_iff T x y (hle x hx) (hle y hy)).1 hxy.le)
        ((map_mkQ_le_iff T y x (hle y hy) (hle x hx)).1 hxy.ge)
  have := (G.project T).nth_index hmem
  rwa [hidx] at this

/-! ### Restriction at `G_{len-1}` -/

theorem comap_subtype_le_iff (T x y : Submodule K V) (hx : x ≤ T) (hy : y ≤ T) :
    x.comap T.subtype ≤ y.comap T.subtype ↔ x ≤ y := by
  constructor
  · intro h v hv
    have := h (show (⟨v, hx hv⟩ : T) ∈ x.comap T.subtype from hv)
    exact this
  · intro h v hv
    exact h hv

theorem Flag.restrict_carrier (G : Flag K V) (hl : 1 ≤ G.len) (T : Submodule K V)
    (hT : G.nth (G.len - 1) = T) :
    (G.restrict T).carrier = (G.carrier.erase ⊤).image (Submodule.comap T.subtype) := by
  have hT1 : T ∈ G.carrier.erase ⊤ := by
    subst hT
    exact Finset.mem_erase.2 ⟨G.ne_top_of_lt (by omega), G.nth_mem' (by omega)⟩
  ext C
  simp only [Flag.restrict, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨B, hB, rfl⟩
    by_cases hb : B = ⊤
    · subst hb
      refine ⟨T, ⟨(Finset.mem_erase.1 hT1).1, (Finset.mem_erase.1 hT1).2⟩, ?_⟩
      rw [Submodule.comap_top]
      exact Submodule.comap_subtype_self T
    · exact ⟨B, ⟨hb, hB⟩, rfl⟩
  · rintro ⟨B, ⟨_, hB⟩, rfl⟩
    exact ⟨B, hB, rfl⟩

theorem Flag.len_restrict (G : Flag K V) (hl : 1 ≤ G.len) (T : Submodule K V)
    (hT : G.nth (G.len - 1) = T) : (G.restrict T).len = G.len - 1 := by
  have hc := G.card_eq_len_succ
  have hinj : Set.InjOn (Submodule.comap T.subtype) ((G.carrier.erase ⊤ : Finset _) : Set _) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_coe.1 hx
    have hy' := Finset.mem_coe.1 hy
    rw [Finset.mem_erase] at hx' hy'
    have h1 := hT ▸ G.le_nth_pred hx'.2 hx'.1
    have h2 := hT ▸ G.le_nth_pred hy'.2 hy'.1
    exact le_antisymm ((comap_subtype_le_iff T x y h1 h2).1 hxy.le)
      ((comap_subtype_le_iff T y x h2 h1).1 hxy.ge)
  unfold Flag.len
  rw [G.restrict_carrier hl T hT, Finset.card_image_of_injOn hinj,
    Finset.card_erase_of_mem G.top_mem]

theorem Flag.nth_restrict (G : Flag K V) (hl : 1 ≤ G.len) (T : Submodule K V)
    (hT : G.nth (G.len - 1) = T) {q : ℕ} (hq : q ≤ G.len - 1) :
    (G.restrict T).nth q = (G.nth q).comap T.subtype := by
  have hc := G.card_eq_len_succ
  have hB : G.nth q ∈ G.carrier.erase ⊤ :=
    Finset.mem_erase.2 ⟨G.ne_top_of_lt (by omega), G.nth_mem' (by omega)⟩
  have hle : ∀ x ∈ G.carrier.erase ⊤, x ≤ T := by
    intro x hx
    rw [Finset.mem_erase] at hx
    exact hT ▸ G.le_nth_pred hx.2 hx.1
  have hmem : (G.nth q).comap T.subtype ∈ (G.restrict T).carrier := by
    rw [G.restrict_carrier hl T hT]
    exact Finset.mem_image_of_mem _ hB
  have hidx : (G.restrict T).index ((G.nth q).comap T.subtype) = q := by
    rw [Flag.index_image (G.restrict T) (G.carrier.erase ⊤) (Submodule.comap T.subtype)
      (G.restrict_carrier hl T hT) ?_ ?_ hB]
    · have : (G.carrier.erase ⊤).filter (· < G.nth q) =
          G.carrier.filter (· < G.nth q) := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · tauto
        · rintro ⟨h1, h2⟩
          exact ⟨⟨(h2.trans_le le_top).ne_top, h1⟩, h2⟩
      rw [this]
      have := G.index_nth (p := q) (by omega)
      unfold Flag.index at this
      exact this
    · intro x hx y hy
      rw [lt_iff_le_not_ge, lt_iff_le_not_ge, comap_subtype_le_iff T x y (hle x hx) (hle y hy),
        comap_subtype_le_iff T y x (hle y hy) (hle x hx)]
    · intro x hx y hy hxy
      exact le_antisymm ((comap_subtype_le_iff T x y (hle x hx) (hle y hy)).1 hxy.le)
        ((comap_subtype_le_iff T y x (hle y hy) (hle x hx)).1 hxy.ge)
  have := (G.restrict T).nth_index hmem
  rwa [hidx] at this

/-! ### Flag identities between faces -/

theorem Flag.project_erase_of_le (G : Flag K V) (A : Submodule K V) (hA : A ∈ G.carrier)
    (h : A ≠ ⊥ ∧ A ≠ ⊤) (T : Submodule K V) (hAT : A ≤ T) :
    (G.erase A h).project T = G.project T := by
  apply Flag.ext
  simp only [Flag.project, Flag.erase]
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image (Finset.erase_subset _ _)
  · intro C hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hC
    by_cases hb : B = A
    · subst hb
      refine Finset.mem_image.2 ⟨⊥, Finset.mem_erase.2 ⟨h.1.symm, G.bot_mem⟩, ?_⟩
      rw [Submodule.map_bot, eq_comm, eq_bot_iff, Submodule.map_le_iff_le_comap]
      intro v hv
      simp only [Submodule.mem_comap, Submodule.mkQ_apply, Submodule.mem_bot,
        Submodule.Quotient.mk_eq_zero]
      exact hAT hv
    · exact Finset.mem_image.2 ⟨B, Finset.mem_erase.2 ⟨hb, hB⟩, rfl⟩

theorem Flag.restrict_erase_of_ge (G : Flag K V) (A : Submodule K V) (hA : A ∈ G.carrier)
    (h : A ≠ ⊥ ∧ A ≠ ⊤) (T : Submodule K V) (hTA : T ≤ A) :
    (G.erase A h).restrict T = G.restrict T := by
  apply Flag.ext
  simp only [Flag.restrict, Flag.erase]
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image (Finset.erase_subset _ _)
  · intro C hC
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hC
    by_cases hb : B = A
    · subst hb
      refine Finset.mem_image.2 ⟨⊤, Finset.mem_erase.2 ⟨h.2.symm, G.top_mem⟩, ?_⟩
      rw [Submodule.comap_top, eq_comm, eq_top_iff]
      intro v _
      exact hTA v.2
    · exact Finset.mem_image.2 ⟨B, Finset.mem_erase.2 ⟨hb, hB⟩, rfl⟩

theorem Flag.eraseAt_eraseAt (G : Flag K V) {i j : ℕ} (hi : 0 < i) (hij : i < j)
    (hj : j < G.len) : (G.eraseAt j).eraseAt i = (G.eraseAt i).eraseAt (j - 1) := by
  have hjm : 0 < j ∧ j < G.len := ⟨by omega, hj⟩
  have him : 0 < i ∧ i < G.len := ⟨hi, by omega⟩
  have hl1 := G.len_eraseAt hjm
  have hl2 := G.len_eraseAt him
  have hjm' : 0 < j - 1 ∧ j - 1 < (G.eraseAt i).len := ⟨by omega, by omega⟩
  have him' : 0 < i ∧ i < (G.eraseAt j).len := ⟨hi, by omega⟩
  have hl3 := (G.eraseAt j).len_eraseAt him'
  have hl4 := (G.eraseAt i).len_eraseAt hjm'
  apply Flag.ext_nth
  · omega
  · intro q hq
    rw [hl3] at hq
    rw [(G.eraseAt j).nth_eraseAt him' (by omega), (G.eraseAt i).nth_eraseAt hjm' (by omega)]
    split_ifs <;>
      simp (disch := omega) only [G.nth_eraseAt hjm, G.nth_eraseAt him] <;>
      split_ifs <;> first | rfl | omega

theorem Flag.project_eraseAt (G : Flag K V) {j : ℕ} (hj : 2 ≤ j ∧ j < G.len) (T : Submodule K V)
    (hT : G.nth 1 = T) : (G.eraseAt j).project T = (G.project T).eraseAt (j - 1) := by
  have hjm : 0 < j ∧ j < G.len := ⟨by omega, hj.2⟩
  have hl1 := G.len_eraseAt hjm
  have hE : (G.eraseAt j).nth 1 = T := by
    rw [G.nth_eraseAt hjm (by omega), if_pos (by omega), hT]
  have hlp := G.len_project (by omega) T hT
  have hjm' : 0 < j - 1 ∧ j - 1 < (G.project T).len := ⟨by omega, by omega⟩
  have hl2 := (G.project T).len_eraseAt hjm'
  apply Flag.ext_nth
  · rw [G.eraseAt j |>.len_project (by omega) T hE, hl2]; omega
  · intro q hq
    rw [(G.eraseAt j).len_project (by omega) T hE] at hq
    rw [(G.eraseAt j).nth_project (by omega) T hE (by omega),
      (G.project T).nth_eraseAt hjm' (by omega)]
    split_ifs
    · rw [G.nth_eraseAt hjm (by omega), if_pos (by omega), G.nth_project (by omega) T hT (by omega)]
    · rw [G.nth_eraseAt hjm (by omega), if_neg (by omega), G.nth_project (by omega) T hT (by omega)]

theorem Flag.restrict_eraseAt (G : Flag K V) {i : ℕ} (hi : 1 ≤ i ∧ i + 2 ≤ G.len)
    (T : Submodule K V) (hT : G.nth (G.len - 1) = T) :
    (G.eraseAt i).restrict T = (G.restrict T).eraseAt i := by
  have him : 0 < i ∧ i < G.len := ⟨by omega, by omega⟩
  have hl1 := G.len_eraseAt him
  have hE : (G.eraseAt i).nth ((G.eraseAt i).len - 1) = T := by
    rw [hl1, G.nth_eraseAt him (by omega), if_neg (by omega), ← hT]
    congr 1; omega
  have hlr := G.len_restrict (by omega) T hT
  have him' : 0 < i ∧ i < (G.restrict T).len := ⟨by omega, by omega⟩
  have hl2 := (G.restrict T).len_eraseAt him'
  apply Flag.ext_nth
  · rw [(G.eraseAt i).len_restrict (by omega) T hE, hl2]; omega
  · intro q hq
    rw [(G.eraseAt i).len_restrict (by omega) T hE] at hq
    rw [(G.eraseAt i).nth_restrict (by omega) T hE (by omega),
      (G.restrict T).nth_eraseAt him' (by omega)]
    split_ifs
    · rw [G.nth_eraseAt him (by omega), if_pos (by omega), G.nth_restrict (by omega) T hT (by omega)]
    · rw [G.nth_eraseAt him (by omega), if_neg (by omega), G.nth_restrict (by omega) T hT (by omega)]

end FlagFaces

end MartinPhd

end
end FlagFaces

section Cauchy

open scoped BigOperators TensorProduct DirectSum
open CategoryTheory Module

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §1.2 La categoría de GL-especies y su estructura monoidal -/

section Species

variable (F : Type) [Field F] (k : Type) [Field k]

/-- A **GL-species**: a functor `Fin×_F → Fin_k` from the groupoid of finite-dimensional
`F`-vector spaces and linear isomorphisms. (Codomain `ModuleCat k`, see the header.) -/
abbrev GLSpecies := Core (FGModuleCat.{0} F) ⥤ ModuleCat.{0} k

variable {F k}

/-- A subspace `S ≤ V`, as an object of `Fin_F`. -/
abbrev sub {V : FGModuleCat.{0} F} (S : Submodule F V) : FGModuleCat.{0} F := FGModuleCat.of F S

/-- The quotient `V/S`, as an object of `Fin_F`. -/
abbrev quo {V : FGModuleCat.{0} F} (S : Submodule F V) : FGModuleCat.{0} F :=
  FGModuleCat.of F (V ⧸ S)

/-- The standard space `Fⁿ`. -/
abbrev stdSpace (F : Type) [Field F] (n : ℕ) : FGModuleCat.{0} F := FGModuleCat.of F (Fin n → F)

/-- `GL(Fⁿ)`. -/
abbrev GLn (F : Type) [Field F] (n : ℕ) := (Fin n → F) ≃ₗ[F] (Fin n → F)

namespace GLSpecies

/-- The value `x(V)`. -/
abbrev ev (x : GLSpecies F k) (V : FGModuleCat.{0} F) : ModuleCat.{0} k := x.obj ⟨V⟩

/-- The map `x(φ) : x(V) → x(W)` of a linear isomorphism `φ : V ≅ W`. -/
def mapEquiv (x : GLSpecies F k) {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) :
    x.ev V →ₗ[k] x.ev W :=
  (x.map (X := ⟨V⟩) (Y := ⟨W⟩) ⟨e.toFGModuleCatIso⟩).hom

@[simp] theorem mapEquiv_refl (x : GLSpecies F k) (V : FGModuleCat.{0} F) :
    x.mapEquiv (LinearEquiv.refl F V) = LinearMap.id := by
  change (x.map (𝟙 (⟨V⟩ : Core (FGModuleCat F)))).hom = _
  simp

@[simp] theorem mapEquiv_trans (x : GLSpecies F k) {U V W : FGModuleCat.{0} F}
    (e : U ≃ₗ[F] V) (f : V ≃ₗ[F] W) :
    x.mapEquiv (e.trans f) = (x.mapEquiv f).comp (x.mapEquiv e) := by
  change (x.map ((⟨e.toFGModuleCatIso⟩ : (⟨U⟩ : Core (FGModuleCat F)) ⟶ ⟨V⟩) ≫
    ⟨f.toFGModuleCatIso⟩)).hom = _
  rw [x.map_comp]
  rfl

theorem mapEquiv_trans_apply (x : GLSpecies F k) {U V W : FGModuleCat.{0} F}
    (e : U ≃ₗ[F] V) (f : V ≃ₗ[F] W) (v : x.ev U) :
    x.mapEquiv (e.trans f) v = x.mapEquiv f (x.mapEquiv e v) :=
  DFunLike.congr_fun (mapEquiv_trans x e f) v

@[simp] theorem mapEquiv_symm_comp (x : GLSpecies F k) {V W : FGModuleCat.{0} F}
    (e : V ≃ₗ[F] W) : (x.mapEquiv e.symm).comp (x.mapEquiv e) = LinearMap.id := by
  rw [← mapEquiv_trans, LinearEquiv.self_trans_symm, mapEquiv_refl]

@[simp] theorem mapEquiv_comp_symm (x : GLSpecies F k) {V W : FGModuleCat.{0} F}
    (e : V ≃ₗ[F] W) : (x.mapEquiv e).comp (x.mapEquiv e.symm) = LinearMap.id := by
  rw [← mapEquiv_trans, LinearEquiv.symm_trans_self, mapEquiv_refl]

/-- Naturality expressed using linear isomorphisms of vector spaces. -/
theorem mapEquiv_naturality {x y : GLSpecies F k} (f : x ⟶ y)
    {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) :
    (f.app ⟨W⟩).hom.comp (x.mapEquiv e) =
      (y.mapEquiv e).comp (f.app ⟨V⟩).hom :=
  congrArg ModuleCat.Hom.hom (f.naturality ⟨e.toFGModuleCatIso⟩)

/-- `x(V)` is a `GL(V)`-module: `g · v = x(g)(v)`. On `Fⁿ` this is the representation
of `GL(Fⁿ)` attached to `x`. -/
def rep (x : GLSpecies F k) (n : ℕ) : Representation k (GLn F n) (x.ev (stdSpace F n)) where
  toFun g := x.mapEquiv (V := stdSpace F n) (W := stdSpace F n) g
  map_one' := x.mapEquiv_refl _
  map_mul' g h := by
    simpa only [LinearEquiv.mul_eq_trans, Module.End.mul_eq_comp] using x.mapEquiv_trans (U := stdSpace F n) (V := stdSpace F n)
      (W := stdSpace F n) h g

/-- The Cauchy product on objects: `(x ⊗ y)(V) = ⨁_{S ≤ V} x(S) ⊗ y(V/S)`. -/
abbrev cauchyObj (x y : GLSpecies F k) (V : FGModuleCat.{0} F) : Type :=
  DirectSum (Submodule F V) fun S => x.ev (sub S) ⊗[k] y.ev (quo S)

/-- The Cauchy product on morphisms: `(x ⊗ y)(φ) = ∑_S x(φ|_S) ⊗ y(φ|_{V/S})`. -/
def cauchyMap (x y : GLSpecies F k) {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) :
    cauchyObj x y V →ₗ[k] cauchyObj x y W :=
  DirectSum.toModule k (Submodule F V) _ fun S =>
    (DirectSum.lof k (Submodule F W) (fun T => x.ev (sub T) ⊗[k] y.ev (quo T))
        (S.map (e : V →ₗ[F] W))) ∘ₗ
      TensorProduct.map (x.mapEquiv (V := sub S) (W := sub (S.map (e : V →ₗ[F] W)))
          (e.submoduleMap S))
        (y.mapEquiv (V := quo S) (W := quo (S.map (e : V →ₗ[F] W)))
          (Submodule.Quotient.equiv S _ e rfl))

private theorem cauchy_lof_ofEq (x y : GLSpecies F k) {V : FGModuleCat.{0} F}
    {S T : Submodule F V} (h : S = T)
    (a : x.ev (sub S)) (b : y.ev (quo S)) :
    DirectSum.lof k (Submodule F V) (fun T => x.ev (sub T) ⊗[k] y.ev (quo T)) T
      (x.mapEquiv (LinearEquiv.ofEq S T h) a ⊗ₜ[k]
        y.mapEquiv (Submodule.quotEquivOfEq S T h) b) =
      DirectSum.lof k (Submodule F V) _ S (a ⊗ₜ[k] b) := by
  subst T
  have hq : Submodule.quotEquivOfEq S S rfl = LinearEquiv.refl F (V ⧸ S) := by
    ext v
    induction v using Submodule.Quotient.induction_on with
    | H v => rfl
  simp only [LinearEquiv.ofEq_rfl, hq, mapEquiv_refl x (sub S),
    mapEquiv_refl y (quo S), LinearMap.id_apply]

@[simp] theorem cauchyMap_refl (x y : GLSpecies F k) (V : FGModuleCat.{0} F) :
    cauchyMap x y (LinearEquiv.refl F V) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro S
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change cauchyMap x y (LinearEquiv.refl F V)
    (DirectSum.lof k (Submodule F V) _ S (a ⊗ₜ[k] b)) = _
  simp only [cauchyMap, DirectSum.toModule_lof, LinearMap.comp_apply, TensorProduct.map_tmul]
  have h : S = S.map (LinearEquiv.refl F V : V →ₗ[F] V) := by simp
  have hs : (LinearEquiv.refl F V).submoduleMap S = LinearEquiv.ofEq _ _ h := by
    ext v
    rfl
  rw [hs, Submodule.Quotient.equiv_refl]
  exact cauchy_lof_ofEq x y h a b

theorem cauchyMap_trans (x y : GLSpecies F k) {U V W : FGModuleCat.{0} F}
    (e : U ≃ₗ[F] V) (f : V ≃ₗ[F] W) :
    cauchyMap x y (e.trans f) = (cauchyMap x y f).comp (cauchyMap x y e) := by
  apply DirectSum.linearMap_ext
  intro S
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change cauchyMap x y (e.trans f)
    (DirectSum.lof k (Submodule F U) _ S (a ⊗ₜ[k] b)) =
      cauchyMap x y f (cauchyMap x y e
        (DirectSum.lof k (Submodule F U) _ S (a ⊗ₜ[k] b)))
  simp only [cauchyMap, DirectSum.toModule_lof, LinearMap.comp_apply, TensorProduct.map_tmul]
  let T := S.map (e.trans f : U →ₗ[F] W)
  let T' := (S.map (e : U →ₗ[F] V)).map (f : V →ₗ[F] W)
  have h : T = T' := by
    dsimp [T, T']
    rw [← Submodule.map_comp]
    rfl
  have hs : (e.submoduleMap S).trans (f.submoduleMap (S.map (e : U →ₗ[F] V))) =
      ((e.trans f).submoduleMap S).trans (LinearEquiv.ofEq T T' h) := by
    ext v
    rfl
  have hq : (Submodule.Quotient.equiv S _ e rfl).trans
      (Submodule.Quotient.equiv (S.map (e : U →ₗ[F] V)) _ f rfl) =
      (Submodule.Quotient.equiv S T (e.trans f) rfl).trans
        (Submodule.quotEquivOfEq T T' h) := by
    ext v
    induction v using Submodule.Quotient.induction_on with
    | H v => rfl
  rw [← mapEquiv_trans_apply x (U := sub S) (V := sub (S.map (e : U →ₗ[F] V)))
    (W := sub T'), ← mapEquiv_trans_apply y (U := quo S)
    (V := quo (S.map (e : U →ₗ[F] V))) (W := quo T'), hs, hq,
    mapEquiv_trans_apply x (U := sub S) (V := sub T) (W := sub T'),
    mapEquiv_trans_apply y (U := quo S) (V := quo T) (W := quo T')]
  exact (cauchy_lof_ofEq x y h _ _).symm

/-- The **Cauchy product** `x ⊗ y` of GL-species [JS95, §2]. -/
abbrev cauchy (x y : GLSpecies F k) : GLSpecies F k where
  obj V := ModuleCat.of k (cauchyObj x y V.of)
  map φ := ModuleCat.ofHom (cauchyMap x y (FGModuleCat.isoToLinearEquiv φ.iso))
  map_id V := by
    apply ModuleCat.hom_ext
    exact cauchyMap_refl x y V.of
  map_comp φ ψ := by
    apply ModuleCat.hom_ext
    exact cauchyMap_trans x y (FGModuleCat.isoToLinearEquiv φ.iso)
      (FGModuleCat.isoToLinearEquiv ψ.iso)

/-- The linear map underlying the tensor product of morphisms of species. -/
def cauchyHomMap {x x' y y' : GLSpecies F k} (f : x ⟶ x') (g : y ⟶ y')
    (V : FGModuleCat.{0} F) : cauchyObj x y V →ₗ[k] cauchyObj x' y' V :=
  DirectSum.toModule k (Submodule F V) _ fun S =>
    DirectSum.lof k (Submodule F V) (fun T => x'.ev (sub T) ⊗[k] y'.ev (quo T)) S ∘ₗ
      TensorProduct.map (f.app ⟨sub S⟩).hom (g.app ⟨quo S⟩).hom

/-- Tensor product of morphisms of species, summand by summand. -/
def cauchyHom {x x' y y' : GLSpecies F k} (f : x ⟶ x') (g : y ⟶ y') :
    cauchy x y ⟶ cauchy x' y' where
  app V := ModuleCat.ofHom (cauchyHomMap f g V.of)
  naturality {V W} φ := by
    apply ModuleCat.hom_ext
    change (cauchyHomMap f g W.of).comp (cauchyMap x y
      (FGModuleCat.isoToLinearEquiv φ.iso)) =
        (cauchyMap x' y' (FGModuleCat.isoToLinearEquiv φ.iso)).comp (cauchyHomMap f g V.of)
    apply DirectSum.linearMap_ext
    intro S
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change cauchyHomMap f g W.of (cauchyMap x y _
      (DirectSum.lof k (Submodule F V.of) _ S (a ⊗ₜ[k] b))) =
        cauchyMap x' y' _ (cauchyHomMap f g V.of
          (DirectSum.lof k (Submodule F V.of) _ S (a ⊗ₜ[k] b)))
    have hf := DFunLike.congr_fun (mapEquiv_naturality f (V := sub S)
      (W := sub (S.map (FGModuleCat.isoToLinearEquiv φ.iso : V.of →ₗ[F] W.of)))
      ((FGModuleCat.isoToLinearEquiv φ.iso).submoduleMap S)) a
    have hg := DFunLike.congr_fun (mapEquiv_naturality g (V := quo S)
      (W := quo (S.map (FGModuleCat.isoToLinearEquiv φ.iso : V.of →ₗ[F] W.of)))
      (Submodule.Quotient.equiv S _ (FGModuleCat.isoToLinearEquiv φ.iso) rfl)) b
    simp only [cauchyMap, cauchyHomMap, DirectSum.toModule_lof,
      LinearMap.comp_apply, TensorProduct.map_tmul]
    simp only [LinearMap.comp_apply] at hf hg
    rw [hf, hg]

@[simp] theorem cauchyHom_id (x y : GLSpecies F k) :
    cauchyHom (𝟙 x) (𝟙 y) = 𝟙 (cauchy x y) := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  change cauchyHomMap (𝟙 x) (𝟙 y) V.of = LinearMap.id
  apply DirectSum.linearMap_ext
  intro S
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change cauchyHomMap (𝟙 x) (𝟙 y) V.of
    (DirectSum.lof k (Submodule F V.of) _ S (a ⊗ₜ[k] b)) = _
  simp [cauchyHomMap]

theorem cauchyHom_comp {x x' x'' y y' y'' : GLSpecies F k}
    (f : x ⟶ x') (f' : x' ⟶ x'') (g : y ⟶ y') (g' : y' ⟶ y'') :
    cauchyHom (f ≫ f') (g ≫ g') = cauchyHom f g ≫ cauchyHom f' g' := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  change cauchyHomMap (f ≫ f') (g ≫ g') V.of =
    (cauchyHomMap f' g' V.of).comp (cauchyHomMap f g V.of)
  apply DirectSum.linearMap_ext
  intro S
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change cauchyHomMap (f ≫ f') (g ≫ g') V.of
    (DirectSum.lof k (Submodule F V.of) _ S (a ⊗ₜ[k] b)) =
      cauchyHomMap f' g' V.of (cauchyHomMap f g V.of
        (DirectSum.lof k (Submodule F V.of) _ S (a ⊗ₜ[k] b)))
  simp [cauchyHomMap]

/-- The unit species `1` of (1.1): `1(0) = k` and `1(V) = 0` for `V ≠ 0`. -/
abbrev unit : GLSpecies F k where
  obj V := ModuleCat.of k ↥(if finrank F V.of = 0 then ⊤ else ⊥ : Submodule k k)
  map φ := ModuleCat.ofHom (LinearEquiv.ofEq _ _ (by
    rw [LinearEquiv.finrank_eq (FGModuleCat.isoToLinearEquiv φ.iso)])).toLinearMap
  map_id _ := by ext v; rfl
  map_comp _ _ := by ext v; rfl

/-- The elementary tensor in the summand indexed by `S`. -/
def pair (x y : GLSpecies F k) (V : FGModuleCat.{0} F) (S : Submodule F V)
    (a : x.ev (sub S)) (b : y.ev (quo S)) : cauchyObj x y V :=
  DirectSum.lof k (Submodule F V) _ S (a ⊗ₜ[k] b)

theorem pair_ext {x y : GLSpecies F k} {V : FGModuleCat.{0} F}
    {M : Type} [AddCommGroup M] [Module k M] {f g : cauchyObj x y V →ₗ[k] M}
    (h : ∀ S a b, f (pair x y V S a b) = g (pair x y V S a b)) : f = g := by
  apply DirectSum.linearMap_ext
  intro S
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  exact h S a b

@[simp] theorem cauchyMap_pair (x y : GLSpecies F k) {V W : FGModuleCat.{0} F}
    (e : V ≃ₗ[F] W) (S : Submodule F V) (a : x.ev (sub S)) (b : y.ev (quo S)) :
    cauchyMap x y e (pair x y V S a b) =
      pair x y W (S.map (e : V →ₗ[F] W))
        (x.mapEquiv (e.submoduleMap S) a)
        (y.mapEquiv (Submodule.Quotient.equiv S _ e rfl) b) := by
  simp [pair, cauchyMap]

@[simp] theorem cauchyHomMap_pair {x x' y y' : GLSpecies F k}
    (f : x ⟶ x') (g : y ⟶ y') (V : FGModuleCat.{0} F)
    (S : Submodule F V) (a : x.ev (sub S)) (b : y.ev (quo S)) :
    cauchyHomMap f g V (pair x y V S a b) =
      pair x' y' V S ((f.app ⟨sub S⟩).hom a) ((g.app ⟨quo S⟩).hom b) := by
  simp [pair, cauchyHomMap]

/-- A unit vector in the value of the unit species on a zero-dimensional space. -/
def unitOne (V : FGModuleCat.{0} F) (h : finrank F V = 0) : (unit (F := F) (k := k)).ev V :=
  ⟨1, by simp [h]⟩

private theorem unit_eq_zero (V : FGModuleCat.{0} F) (h : finrank F V ≠ 0)
    (a : (unit (F := F) (k := k)).ev V) : a = 0 := by
  apply Subtype.ext
  change a.val = (0 : k)
  have ha := a.property
  change a.val ∈ (if finrank F V = 0 then ⊤ else ⊥ : Submodule k k) at ha
  simpa only [ite_eq_right h, Submodule.mem_bot] using ha

/-- The left unit map, supported on the zero subspace. -/
def leftUnitMap (x : GLSpecies F k) (V : FGModuleCat.{0} F) :
    cauchyObj unit x V →ₗ[k] x.ev V :=
  DirectSum.toModule k (Submodule F V) _ fun S =>
    if h : S = ⊥ then
      (TensorProduct.lid k (x.ev V)).toLinearMap ∘ₗ
        TensorProduct.map (if finrank F (sub S) = 0 then ⊤ else ⊥ : Submodule k k).subtype
          (x.mapEquiv (S.quotEquivOfEqBot h))
    else 0

/-- The inverse of the left unit map. -/
def leftUnitInv (x : GLSpecies F k) (V : FGModuleCat.{0} F) :
    x.ev V →ₗ[k] cauchyObj unit x V :=
  (DirectSum.lof k (Submodule F V) _ ⊥) ∘ₗ
    (TensorProduct.mk k ((unit (F := F) (k := k)).ev (sub (⊥ : Submodule F V)))
      (x.ev (quo (⊥ : Submodule F V))) (unitOne _ (by simp))) ∘ₗ
    x.mapEquiv (Submodule.quotEquivOfEqBot (⊥ : Submodule F V) rfl).symm

@[simp] theorem leftUnitMap_pair_bot (x : GLSpecies F k) (V : FGModuleCat.{0} F)
    (a : (unit (F := F) (k := k)).ev (sub (⊥ : Submodule F V)))
    (b : x.ev (quo (⊥ : Submodule F V))) :
    leftUnitMap x V (pair unit x V ⊥ a b) =
      a.val • x.mapEquiv (Submodule.quotEquivOfEqBot (⊥ : Submodule F V) rfl) b := by
  simp only [leftUnitMap, pair, DirectSum.toModule_lof]
  rfl

@[simp] theorem leftUnitMap_pair_ne_bot (x : GLSpecies F k) (V : FGModuleCat.{0} F)
    (S : Submodule F V) (h : S ≠ ⊥) (a : (unit (F := F) (k := k)).ev (sub S))
    (b : x.ev (quo S)) : leftUnitMap x V (pair unit x V S a b) = 0 := by
  simp [leftUnitMap, pair, h]

/-- Objectwise left unitor of the Cauchy product. -/
def leftUnitEquiv (x : GLSpecies F k) (V : FGModuleCat.{0} F) :
    cauchyObj unit x V ≃ₗ[k] x.ev V :=
  LinearEquiv.ofLinearMap (leftUnitMap x V) (leftUnitInv x V) (by
    apply LinearMap.ext
    intro v
    change leftUnitMap x V (pair unit x V ⊥ (unitOne _ (by simp))
      (x.mapEquiv (Submodule.quotEquivOfEqBot (⊥ : Submodule F V) rfl).symm v)) = v
    simp only [leftUnitMap_pair_bot, unitOne, one_smul]
    exact DFunLike.congr_fun (mapEquiv_comp_symm x
      (V := quo (⊥ : Submodule F V)) (W := V) _) v) (by
    apply pair_ext
    intro S a b
    change leftUnitInv x V (leftUnitMap x V (pair unit x V S a b)) = pair unit x V S a b
    by_cases h : S = ⊥
    · subst S
      rw [leftUnitMap_pair_bot]
      change pair unit x V ⊥ (unitOne _ (by simp))
        (x.mapEquiv (Submodule.quotEquivOfEqBot (⊥ : Submodule F V) rfl).symm
          (a.val • x.mapEquiv (Submodule.quotEquivOfEqBot (⊥ : Submodule F V) rfl) b)) = _
      rw [map_smul]
      have hc := DFunLike.congr_fun (mapEquiv_symm_comp x
        (V := quo (⊥ : Submodule F V)) (W := V)
        (Submodule.quotEquivOfEqBot (⊥ : Submodule F V) rfl)) b
      change x.mapEquiv _ (x.mapEquiv _ b) = b at hc
      rw [hc]
      unfold pair
      rw [← TensorProduct.smul_tmul]
      have ha : a.val • unitOne (sub (⊥ : Submodule F V)) (by simp) = a := by
        apply Subtype.ext
        change a.val * 1 = a.val
        exact mul_one _
      rw [ha]
    · have ha := unit_eq_zero (sub S) (Submodule.finrank_eq_zero.not.mpr h) a
      simp [ha, pair])

@[simp] theorem unit_mapEquiv_val {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W)
    (a : (unit (F := F) (k := k)).ev V) :
    ((unit (F := F) (k := k)).mapEquiv e a).val = a.val := rfl

theorem leftUnitMap_pair_of_eq (x : GLSpecies F k) (V : FGModuleCat.{0} F)
    (S : Submodule F V) (h : S = ⊥) (a : (unit (F := F) (k := k)).ev (sub S))
    (b : x.ev (quo S)) :
    leftUnitMap x V (pair unit x V S a b) = a.val • x.mapEquiv (S.quotEquivOfEqBot h) b := by
  subst S
  exact leftUnitMap_pair_bot x V a b

/-- Naturality of the objectwise left unit map under linear isomorphisms. -/
theorem leftUnitMap_naturality (x : GLSpecies F k) {V W : FGModuleCat.{0} F}
    (e : V ≃ₗ[F] W) :
    (leftUnitMap x W).comp (cauchyMap unit x e) = (x.mapEquiv e).comp (leftUnitMap x V) := by
  apply pair_ext
  intro S a b
  change leftUnitMap x W (cauchyMap unit x e (pair unit x V S a b)) =
    x.mapEquiv e (leftUnitMap x V (pair unit x V S a b))
  by_cases h : S = ⊥
  · subst S
    have he : (⊥ : Submodule F V).map (e : V →ₗ[F] W) = ⊥ := Submodule.map_bot _
    rw [cauchyMap_pair, leftUnitMap_pair_of_eq x W _ he, leftUnitMap_pair_bot,
      unit_mapEquiv_val, map_smul]
    have hq : (Submodule.Quotient.equiv (⊥ : Submodule F V) _ e rfl).trans
        (Submodule.quotEquivOfEqBot _ he) =
        (Submodule.quotEquivOfEqBot (⊥ : Submodule F V) rfl).trans e := by
      ext v
      induction v using Submodule.Quotient.induction_on with
      | H v => rfl
    rw [← mapEquiv_trans_apply x (U := quo (⊥ : Submodule F V))
      (V := quo ((⊥ : Submodule F V).map (e : V →ₗ[F] W))) (W := W), hq,
      mapEquiv_trans_apply x (U := quo (⊥ : Submodule F V)) (V := V) (W := W)]
  · have ha := unit_eq_zero (sub S) (Submodule.finrank_eq_zero.not.mpr h) a
    simp [ha, pair]

/-- The left unitor of the Cauchy product, natural in the ambient vector space. -/
def cauchyLeftUnitor (x : GLSpecies F k) : cauchy unit x ≅ x :=
  NatIso.ofComponents (fun V => (leftUnitEquiv x V.of).toModuleIso)
    (fun {V W} φ => by
      apply ModuleCat.hom_ext
      exact leftUnitMap_naturality x (FGModuleCat.isoToLinearEquiv φ.iso))

/-- Naturality of the left unitor with respect to morphisms of species. -/
theorem cauchyLeftUnitor_naturality {x y : GLSpecies F k} (f : x ⟶ y) :
    cauchyHom (𝟙 unit) f ≫ (cauchyLeftUnitor y).hom = (cauchyLeftUnitor x).hom ≫ f := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  change (leftUnitMap y V.of).comp (cauchyHomMap (𝟙 unit) f V.of) =
    (f.app V).hom.comp (leftUnitMap x V.of)
  apply pair_ext
  intro S a b
  change leftUnitMap y V.of (cauchyHomMap (𝟙 unit) f V.of (pair unit x V.of S a b)) =
    (f.app V).hom (leftUnitMap x V.of (pair unit x V.of S a b))
  by_cases h : S = ⊥
  · subst S
    rw [cauchyHomMap_pair, leftUnitMap_pair_bot, leftUnitMap_pair_bot, map_smul]
    have hf := DFunLike.congr_fun (mapEquiv_naturality f
      (V := quo (⊥ : Submodule F V.of)) (W := V.of)
      (Submodule.quotEquivOfEqBot (⊥ : Submodule F V.of) rfl)) b
    change _ = a.val • _
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hf
    rw [hf]
    rfl
  · have ha := unit_eq_zero (sub S) (Submodule.finrank_eq_zero.not.mpr h) a
    simp [ha, pair]

private theorem finrank_quotient_zero_iff (V : FGModuleCat.{0} F) (S : Submodule F V) :
    finrank F (V ⧸ S) = 0 ↔ S = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    have hr := S.finrank_quotient_add_finrank
    omega
  · rintro rfl
    exact finrank_zero_of_subsingleton

/-- The canonical equivalence from the whole subspace to its ambient space. -/
def subTopEquiv {V : FGModuleCat.{0} F} (S : Submodule F V) (h : S = ⊤) : S ≃ₗ[F] V :=
  (LinearEquiv.ofEq S ⊤ h).trans Submodule.topEquiv

/-- The right unit map, supported on the whole subspace. -/
def rightUnitMap (x : GLSpecies F k) (V : FGModuleCat.{0} F) :
    cauchyObj x unit V →ₗ[k] x.ev V :=
  DirectSum.toModule k (Submodule F V) _ fun S =>
    if h : S = ⊤ then
      (TensorProduct.rid k (x.ev V)).toLinearMap ∘ₗ
        TensorProduct.map (x.mapEquiv (subTopEquiv S h))
          (if finrank F (quo S) = 0 then ⊤ else ⊥ : Submodule k k).subtype
    else 0

/-- The inverse of the right unit map. -/
def rightUnitInv (x : GLSpecies F k) (V : FGModuleCat.{0} F) :
    x.ev V →ₗ[k] cauchyObj x unit V :=
  (DirectSum.lof k (Submodule F V) _ ⊤) ∘ₗ
    (TensorProduct.mk k (x.ev (sub (⊤ : Submodule F V)))
      ((unit (F := F) (k := k)).ev (quo (⊤ : Submodule F V)))).flip
        (unitOne _ ((finrank_quotient_zero_iff V ⊤).mpr rfl)) ∘ₗ
    x.mapEquiv (subTopEquiv (⊤ : Submodule F V) rfl).symm

@[simp] theorem rightUnitMap_pair_top (x : GLSpecies F k) (V : FGModuleCat.{0} F)
    (a : x.ev (sub (⊤ : Submodule F V)))
    (b : (unit (F := F) (k := k)).ev (quo (⊤ : Submodule F V))) :
    rightUnitMap x V (pair x unit V ⊤ a b) =
      b.val • x.mapEquiv (subTopEquiv (⊤ : Submodule F V) rfl) a := by
  simp only [rightUnitMap, pair, DirectSum.toModule_lof]
  rfl

/-- Objectwise right unitor of the Cauchy product. -/
def rightUnitEquiv (x : GLSpecies F k) (V : FGModuleCat.{0} F) :
    cauchyObj x unit V ≃ₗ[k] x.ev V :=
  LinearEquiv.ofLinearMap (rightUnitMap x V) (rightUnitInv x V) (by
    apply LinearMap.ext
    intro v
    change rightUnitMap x V (pair x unit V ⊤
      (x.mapEquiv (subTopEquiv (⊤ : Submodule F V) rfl).symm v) (unitOne _ _)) = v
    simp only [rightUnitMap_pair_top, unitOne, one_smul]
    exact DFunLike.congr_fun (mapEquiv_comp_symm x (V := sub (⊤ : Submodule F V))
      (W := V) _) v) (by
    apply pair_ext
    intro S a b
    change rightUnitInv x V (rightUnitMap x V (pair x unit V S a b)) = pair x unit V S a b
    by_cases h : S = ⊤
    · subst S
      rw [rightUnitMap_pair_top]
      change pair x unit V ⊤
        (x.mapEquiv (subTopEquiv (⊤ : Submodule F V) rfl).symm
          (b.val • x.mapEquiv (subTopEquiv (⊤ : Submodule F V) rfl) a)) (unitOne _ _) = _
      rw [map_smul]
      have hc := DFunLike.congr_fun (mapEquiv_symm_comp x
        (V := sub (⊤ : Submodule F V)) (W := V) (subTopEquiv (⊤ : Submodule F V) rfl)) a
      change x.mapEquiv _ (x.mapEquiv _ a) = a at hc
      rw [hc]
      unfold pair
      rw [TensorProduct.smul_tmul]
      have hb : b.val • unitOne (quo (⊤ : Submodule F V)) ((finrank_quotient_zero_iff V ⊤).mpr rfl) = b := by
        apply Subtype.ext
        change b.val * 1 = b.val
        exact mul_one _
      rw [hb]
    · have hb := unit_eq_zero (quo S) ((finrank_quotient_zero_iff V S).not.mpr h) b
      simp [hb, pair])

theorem rightUnitMap_pair_of_eq (x : GLSpecies F k) (V : FGModuleCat.{0} F)
    (S : Submodule F V) (h : S = ⊤) (a : x.ev (sub S))
    (b : (unit (F := F) (k := k)).ev (quo S)) :
    rightUnitMap x V (pair x unit V S a b) = b.val • x.mapEquiv (subTopEquiv S h) a := by
  subst S
  exact rightUnitMap_pair_top x V a b

/-- Naturality of the objectwise right unit map under linear isomorphisms. -/
theorem rightUnitMap_naturality (x : GLSpecies F k) {V W : FGModuleCat.{0} F}
    (e : V ≃ₗ[F] W) :
    (rightUnitMap x W).comp (cauchyMap x unit e) = (x.mapEquiv e).comp (rightUnitMap x V) := by
  apply pair_ext
  intro S a b
  change rightUnitMap x W (cauchyMap x unit e (pair x unit V S a b)) =
    x.mapEquiv e (rightUnitMap x V (pair x unit V S a b))
  by_cases h : S = ⊤
  · subst S
    have he : (⊤ : Submodule F V).map (e : V →ₗ[F] W) = ⊤ := by
      rw [Submodule.map_top, LinearEquiv.range]
    rw [cauchyMap_pair, rightUnitMap_pair_of_eq x W _ he, rightUnitMap_pair_top,
      unit_mapEquiv_val, map_smul]
    have hs : (e.submoduleMap ⊤).trans (subTopEquiv _ he) =
        (subTopEquiv (⊤ : Submodule F V) rfl).trans e := by ext v; rfl
    rw [← mapEquiv_trans_apply x (U := sub (⊤ : Submodule F V))
      (V := sub ((⊤ : Submodule F V).map (e : V →ₗ[F] W))) (W := W), hs,
      mapEquiv_trans_apply x (U := sub (⊤ : Submodule F V)) (V := V) (W := W)]
  · have hb := unit_eq_zero (quo S) ((finrank_quotient_zero_iff V S).not.mpr h) b
    simp [hb, pair]

/-- The right unitor of the Cauchy product, natural in the ambient vector space. -/
def cauchyRightUnitor (x : GLSpecies F k) : cauchy x unit ≅ x :=
  NatIso.ofComponents (fun V => (rightUnitEquiv x V.of).toModuleIso)
    (fun {V W} φ => by
      apply ModuleCat.hom_ext
      exact rightUnitMap_naturality x (FGModuleCat.isoToLinearEquiv φ.iso))

/-- Naturality of the right unitor with respect to morphisms of species. -/
theorem cauchyRightUnitor_naturality {x y : GLSpecies F k} (f : x ⟶ y) :
    cauchyHom f (𝟙 unit) ≫ (cauchyRightUnitor y).hom = (cauchyRightUnitor x).hom ≫ f := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  change (rightUnitMap y V.of).comp (cauchyHomMap f (𝟙 unit) V.of) =
    (f.app V).hom.comp (rightUnitMap x V.of)
  apply pair_ext
  intro S a b
  change rightUnitMap y V.of (cauchyHomMap f (𝟙 unit) V.of (pair x unit V.of S a b)) =
    (f.app V).hom (rightUnitMap x V.of (pair x unit V.of S a b))
  by_cases h : S = ⊤
  · subst S
    rw [cauchyHomMap_pair, rightUnitMap_pair_top, rightUnitMap_pair_top, map_smul]
    have hf := DFunLike.congr_fun (mapEquiv_naturality f
      (V := sub (⊤ : Submodule F V.of)) (W := V.of)
      (subTopEquiv (⊤ : Submodule F V.of) rfl)) a
    change _ = b.val • _
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hf
    rw [hf]
    rfl
  · have hb := unit_eq_zero (quo S) ((finrank_quotient_zero_iff V.of S).not.mpr h) b
    simp [hb, pair]

/-- Change both the indices and the components of a direct sum. -/
def sumCongr {I J : Type} {M : I → Type} {N : J → Type}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
    [∀ j, AddCommMonoid (N j)] [∀ j, Module k (N j)]
    (e : I ≃ J) (f : ∀ i, M i ≃ₗ[k] N (e i)) : (⨁ i, M i) ≃ₗ[k] ⨁ j, N j :=
  (DirectSum.congrLinearEquiv f).trans (DirectSum.lequivCongrLeft k e.symm).symm

@[simp] theorem sumCongr_lof {I J : Type} {M : I → Type} {N : J → Type}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
    [∀ j, AddCommMonoid (N j)] [∀ j, Module k (N j)]
    [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (f : ∀ i, M i ≃ₗ[k] N (e i)) (i : I) (a : M i) :
    sumCongr e f (DirectSum.lof k I M i a) = DirectSum.lof k J N (e i) (f i a) := by
  simp only [sumCongr, LinearEquiv.trans_apply, DirectSum.coe_congrLinearEquiv,
    DirectSum.lmap_lof]
  exact DirectSum.lequivCongrLeft_symm_lof k (M := N) (h := e.symm)

/-- The linear equivalence induced on the value of a species. -/
def mapIso (x : GLSpecies F k) {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) :
    x.ev V ≃ₗ[k] x.ev W :=
  LinearEquiv.ofLinearMap (x.mapEquiv e) (x.mapEquiv e.symm)
    (mapEquiv_comp_symm x e) (mapEquiv_symm_comp x e)

abbrev LeftFlagIndex (V : FGModuleCat.{0} F) := Σ S : Submodule F V, Submodule F S
abbrev RightFlagIndex (V : FGModuleCat.{0} F) := Σ T : Submodule F V, Submodule F (V ⧸ T)

/-- The two descriptions of a two-step flag: a subspace of a subspace, or a
subspace of a quotient. -/
def flagIndexEquiv (V : FGModuleCat.{0} F) : LeftFlagIndex V ≃ RightFlagIndex V :=
  (Equiv.sigmaCongrRight fun S : Submodule F V => S.mapIic.toEquiv).trans
    (({ toFun := fun p => ⟨p.2.val, p.1, p.2.property⟩
        invFun := fun p => ⟨p.2.val, p.1, p.2.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } :
      (Σ S : Submodule F V, Set.Iic S) ≃ (Σ T : Submodule F V, Set.Ici T)).trans
        (Equiv.sigmaCongrRight fun T => T.comapMkQRelIso.toEquiv.symm))

/-- The lower subspace of a subspace flag, viewed inside the ambient space. -/
abbrev flagLower {V : FGModuleCat.{0} F} (S : Submodule F V) (T : Submodule F S) :=
  T.map S.subtype

private theorem flagLower_le {V : FGModuleCat.{0} F} (S : Submodule F V)
    (T : Submodule F S) : flagLower S T ≤ S :=
  (S.mapIic T).property

/-- The middle factor `S/T`, identified with its image in `V/T`. -/
def flagMiddleEquiv {V : FGModuleCat.{0} F} (S : Submodule F V) (T : Submodule F S) :
    (S ⧸ T) ≃ₗ[F] S.map (flagLower S T).mkQ := by
  let f := (flagLower S T).mkQ.comp S.subtype
  have hk : T = f.ker := by
    dsimp [f]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ,
      Submodule.comap_map_eq_of_injective S.subtype_injective]
  have hr : f.range = S.map (flagLower S T).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  exact (Submodule.quotEquivOfEq T f.ker hk).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))

/-- The third-isomorphism map (1.2), in the direction used by the associator. -/
def flagUpperEquiv {V : FGModuleCat.{0} F} (S : Submodule F V) (T : Submodule F S) :
    (V ⧸ S) ≃ₗ[F] ((V ⧸ flagLower S T) ⧸ S.map (flagLower S T).mkQ) :=
  (Submodule.quotientQuotientEquivQuotient (flagLower S T) S (flagLower_le S T)).symm

abbrev LeftFlagValue (x y z : GLSpecies F k) (V : FGModuleCat.{0} F)
    (p : LeftFlagIndex V) := (x.ev (sub (V := sub p.1) p.2) ⊗[k] y.ev (quo (V := sub p.1) p.2)) ⊗[k] z.ev (quo p.1)
abbrev RightFlagValue (x y z : GLSpecies F k) (V : FGModuleCat.{0} F)
    (p : RightFlagIndex V) := x.ev (sub p.1) ⊗[k] (y.ev (sub (V := quo p.1) p.2) ⊗[k] z.ev (quo (V := quo p.1) p.2))

/-- Flatten the two direct sums in a left-associated Cauchy product. -/
def flattenLeft (x y z : GLSpecies F k) (V : FGModuleCat.{0} F) :
    cauchyObj (cauchy x y) z V ≃ₗ[k] ⨁ p : LeftFlagIndex V, LeftFlagValue x y z V p :=
  (DirectSum.congrLinearEquiv fun S : Submodule F V =>
    TensorProduct.directSumLeft k k
      (fun T : Submodule F S => x.ev (sub (V := sub S) T) ⊗[k] y.ev (quo (V := sub S) T)) (z.ev (quo S))).trans
    (DirectSum.sigmaLcurryEquiv k).symm

/-- Flatten the two direct sums in a right-associated Cauchy product. -/
def flattenRight (x y z : GLSpecies F k) (V : FGModuleCat.{0} F) :
    cauchyObj x (cauchy y z) V ≃ₗ[k] ⨁ p : RightFlagIndex V, RightFlagValue x y z V p :=
  (DirectSum.congrLinearEquiv fun T : Submodule F V =>
    TensorProduct.directSumRight k k (x.ev (sub T))
      (fun Q : Submodule F (V ⧸ T) => y.ev (sub (V := quo T) Q) ⊗[k] z.ev (quo (V := quo T) Q))).trans
    (DirectSum.sigmaLcurryEquiv k).symm

/-- On each flag the associator consists of the usual tensor associator and the
three canonical isomorphisms of subquotients. -/
def flagValueEquiv (x y z : GLSpecies F k) (V : FGModuleCat.{0} F)
    (p : LeftFlagIndex V) :
    LeftFlagValue x y z V p ≃ₗ[k] RightFlagValue x y z V (flagIndexEquiv V p) :=
  (TensorProduct.assoc k _ _ _).trans
    (TensorProduct.congr
      (mapIso x (V := sub (V := sub p.1) p.2) (W := sub (flagLower p.1 p.2)) (p.1.equivSubtypeMap p.2))
      (TensorProduct.congr
        (mapIso y (V := quo (V := sub p.1) p.2) (W := sub (V := quo (flagLower p.1 p.2)) (p.1.map (flagLower p.1 p.2).mkQ))
          (flagMiddleEquiv p.1 p.2))
        (mapIso z (V := quo p.1) (W := quo (V := quo (flagLower p.1 p.2)) (p.1.map (flagLower p.1 p.2).mkQ))
          (flagUpperEquiv p.1 p.2))))

/-- Objectwise Cauchy associator, using the correspondence between two-step flags. -/
def assocEquiv (x y z : GLSpecies F k) (V : FGModuleCat.{0} F) :
    cauchyObj (cauchy x y) z V ≃ₗ[k] cauchyObj x (cauchy y z) V :=
  (flattenLeft x y z V).trans
    ((sumCongr (flagIndexEquiv V) (flagValueEquiv x y z V)).trans
      (flattenRight x y z V).symm)

@[simp] theorem sumComponent_lof {I : Type} {M N : I → Type}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module k (N i)] [DecidableEq I]
    (f : ∀ i, M i ≃ₗ[k] N i) (i : I) (a : M i) :
    DirectSum.congrLinearEquiv f (DirectSum.lof k I M i a) =
      DirectSum.lof k I N i (f i a) := DirectSum.lmap_lof _ i a

@[simp] theorem sigmaFlat_lof {I : Type} {J : I → Type} {M : (i : I) → J i → Type}
    [∀ i j, AddCommMonoid (M i j)] [∀ i j, Module k (M i j)]
    [DecidableEq I] [∀ i, DecidableEq (J i)] (i : I) (j : J i) (a : M i j) :
    (DirectSum.sigmaLcurryEquiv k).symm
      (DirectSum.lof k I _ i (DirectSum.lof k (J i) _ j a)) =
      DirectSum.lof k (Sigma J) (fun p => M p.1 p.2) ⟨i, j⟩ a := by
  rw [LinearEquiv.symm_apply_eq]
  symm
  exact DirectSum.sigmaCurry_of ⟨i, j⟩ a

@[simp] theorem flattenLeft_pair (x y z : GLSpecies F k) (V : FGModuleCat.{0} F)
    (S : Submodule F V) (T : Submodule F S)
    (a : x.ev (sub (V := sub S) T)) (b : y.ev (quo (V := sub S) T)) (c : z.ev (quo S)) :
    flattenLeft x y z V (pair (cauchy x y) z V S (pair x y (sub S) T a b) c) =
      DirectSum.lof k (LeftFlagIndex V) (LeftFlagValue x y z V) ⟨S, T⟩ ((a ⊗ₜ[k] b) ⊗ₜ[k] c) := by
  change (DirectSum.sigmaLcurryEquiv k).symm
    ((DirectSum.congrLinearEquiv fun S : Submodule F V =>
      TensorProduct.directSumLeft k k
        (fun T : Submodule F S => x.ev (sub (V := sub S) T) ⊗[k]
          y.ev (quo (V := sub S) T)) (z.ev (quo S)))
      (DirectSum.lof k (Submodule F V) _ S
        (DirectSum.lof k (Submodule F S) _ T (a ⊗ₜ[k] b) ⊗ₜ[k] c))) = _
  rw [sumComponent_lof, TensorProduct.directSumLeft_tmul_lof]
  rw [LinearEquiv.symm_apply_eq]
  exact (DirectSum.sigmaCurry_of (δ := fun S T =>
    (x.ev (sub (V := sub S) T) ⊗[k] y.ev (quo (V := sub S) T)) ⊗[k] z.ev (quo S))
    ⟨S, T⟩ ((a ⊗ₜ[k] b) ⊗ₜ[k] c)).symm

@[simp] theorem flattenRight_pair (x y z : GLSpecies F k) (V : FGModuleCat.{0} F)
    (T : Submodule F V) (Q : Submodule F (V ⧸ T)) (a : x.ev (sub T))
    (b : y.ev (sub (V := quo T) Q)) (c : z.ev (quo (V := quo T) Q)) :
    flattenRight x y z V (pair x (cauchy y z) V T a (pair y z (quo T) Q b c)) =
      DirectSum.lof k (RightFlagIndex V) (RightFlagValue x y z V) ⟨T, Q⟩ (a ⊗ₜ[k] (b ⊗ₜ[k] c)) := by
  simp [flattenRight, pair, cauchy, cauchyObj]

@[simp] theorem flattenRight_symm_pair (x y z : GLSpecies F k) (V : FGModuleCat.{0} F)
    (T : Submodule F V) (Q : Submodule F (V ⧸ T)) (a : x.ev (sub T))
    (b : y.ev (sub (V := quo T) Q)) (c : z.ev (quo (V := quo T) Q)) :
    (flattenRight x y z V).symm
      (DirectSum.lof k (RightFlagIndex V) (RightFlagValue x y z V) ⟨T, Q⟩ (a ⊗ₜ[k] (b ⊗ₜ[k] c))) =
      pair x (cauchy y z) V T a (pair y z (quo T) Q b c) := by
  rw [LinearEquiv.symm_apply_eq, flattenRight_pair]

@[simp] theorem assocEquiv_pair (x y z : GLSpecies F k) (V : FGModuleCat.{0} F)
    (S : Submodule F V) (T : Submodule F S)
    (a : x.ev (sub (V := sub S) T)) (b : y.ev (quo (V := sub S) T)) (c : z.ev (quo S)) :
    assocEquiv x y z V (pair (cauchy x y) z V S (pair x y (sub S) T a b) c) =
      pair x (cauchy y z) V (flagLower S T)
        (x.mapEquiv (S.equivSubtypeMap T) a)
        (pair y z (quo (flagLower S T)) (S.map (flagLower S T).mkQ)
          (y.mapEquiv (flagMiddleEquiv S T) b) (z.mapEquiv (flagUpperEquiv S T) c)) := by
  simp only [assocEquiv, LinearEquiv.trans_apply, flattenLeft_pair, sumCongr_lof]
  change (flattenRight x y z V).symm
    (DirectSum.lof k (RightFlagIndex V) (RightFlagValue x y z V) _
      (flagValueEquiv x y z V ⟨S, T⟩ ((a ⊗ₜ[k] b) ⊗ₜ[k] c))) = _
  simp only [flagValueEquiv, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
    TensorProduct.congr_tmul]
  exact flattenRight_symm_pair x y z V _ _ _ _ _

@[simp] theorem cauchy_mapEquiv (x y : GLSpecies F k) {V W : FGModuleCat.{0} F}
    (e : V ≃ₗ[F] W) : (cauchy x y).mapEquiv e = cauchyMap x y e := rfl

theorem pair_congr {x y : GLSpecies F k} {V : FGModuleCat.{0} F}
    {S T : Submodule F V} (h : S = T) (a : x.ev (sub S)) (b : y.ev (quo S))
    (c : x.ev (sub T)) (d : y.ev (quo T))
    (ha : x.mapEquiv (LinearEquiv.ofEq S T h) a = c)
    (hb : y.mapEquiv (Submodule.quotEquivOfEq S T h) b = d) :
    pair x y V S a b = pair x y V T c d := by
  rw [← ha, ← hb]
  exact (cauchy_lof_ofEq x y h a b).symm

theorem tripleLeft_ext {x y z : GLSpecies F k} {V : FGModuleCat.{0} F}
    {M : Type} [AddCommGroup M] [Module k M]
    {f g : cauchyObj (cauchy x y) z V →ₗ[k] M}
    (h : ∀ (S : Submodule F V) (T : Submodule F S)
      (a : x.ev (sub (V := sub S) T)) (b : y.ev (quo (V := sub S) T)) (c : z.ev (quo S)),
      f (pair (cauchy x y) z V S (pair x y (sub S) T a b) c) =
        g (pair (cauchy x y) z V S (pair x y (sub S) T a b) c)) : f = g := by
  apply pair_ext
  intro S a c
  induction a using DirectSum.induction_on with
  | zero => simp [pair]
  | add a b ha hb => simpa only [pair, TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) ha hb
  | of T t =>
    induction t using TensorProduct.induction_on with
    | zero => simp [pair]
    | add a b ha hb => simpa only [pair, map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) ha hb
    | tmul a b => exact h S T a b c


end GLSpecies
end Species
end MartinPhd

end
end Cauchy
