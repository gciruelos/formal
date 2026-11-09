import MartinPhd.Chapter1Section3Exponential
import MartinPhd.Chapter1Section2Cauchy

/-!
# Chapter 1, Section 1.4 (cohomology of an e-bicomodule)

Contents:
* Chapter1Section4
* Enum
* Leibniz
-/

section Chapter1Section4

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §1.4 La cohomología de un e-bicomódulo -/

section Cobar

variable {F : Type} [Field F] {k : Type} [Field k]

/-- Raw cochains in coordinates (1.11): `α(V, z, F) ∈ k`, linear in `z ∈ x(V)`, with `F`
a flag in `V`. `ē^{⊗n}(V)` has basis `{e_F : F ∈ Fl_n(V)}`, so a morphism
`x → ē^{⊗n}` is a family of such coordinate functions. -/
abbrev RawCochain (x : EBicomod F k) :=
  ∀ V : FGModuleCat.{0} F, x.X.ev V →ₗ[k] (Flag F V → k)

/-- The reduced cobar construction `Cⁿ(x) = Hom_Sp(x, ē^{⊗n})` (1.9): coordinate
families supported on flags of length `n` and natural for linear isomorphisms. -/
def cochains (x : EBicomod F k) (n : ℕ) : Submodule k (RawCochain x) where
  carrier := {α | (∀ (V : FGModuleCat.{0} F) z (G : Flag F V), G.len ≠ n → α V z G = 0) ∧
    (∀ (V W : FGModuleCat.{0} F) (e : V ≃ₗ[F] W) z (G : Flag F V),
      α W (x.X.mapEquiv e z) (G.map e) = α V z G)}
  add_mem' := by
    intro a b ha hb
    exact ⟨fun V z G hG => by simp [ha.1 V z G hG, hb.1 V z G hG],
      fun V W e z G => by simp [ha.2 V W e z G, hb.2 V W e z G]⟩
  zero_mem' := ⟨fun V z G _ => by simp, fun V W e z G => by simp⟩
  smul_mem' := by
    intro r a ha
    exact ⟨fun V z G hG => by simp [ha.1 V z G hG],
      fun V W e z G => by simp [ha.2 V W e z G]⟩

/-- The middle faces `∑_{0<i<n+1} (-1)ⁱ α(V, z, F ∖ Fᵢ)`, as a linear map in `z`. -/
def faceSum {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X] (G : Flag F V)
    (γ : X →ₗ[k] (Flag F V → k)) : X →ₗ[k] k :=
  ∑ A ∈ G.carrier, if h : A ≠ ⊥ ∧ A ≠ ⊤ then
    ((-1 : k) ^ G.index A) • (LinearMap.proj (G.erase A h) ∘ₗ γ) else 0

theorem faceSum_add {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X]
    (G : Flag F V) (γ δ : X →ₗ[k] (Flag F V → k)) :
    faceSum X G (γ + δ) = faceSum X G γ + faceSum X G δ := by
  unfold faceSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
  · rw [dif_pos h, dif_pos h, dif_pos h, LinearMap.comp_add, smul_add]
  · rw [dif_neg h, dif_neg h, dif_neg h]; simp

theorem faceSum_smul {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X]
    (G : Flag F V) (r : k) (γ : X →ₗ[k] (Flag F V → k)) :
    faceSum X G (r • γ) = r • faceSum X G γ := by
  unfold faceSum
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
  · simp only [h, and_self, ne_eq, not_false_eq_true, dif_pos, ← LinearMap.comp_smul, smul_comm r]
  · simp [h]

/-- The differential `d = ∑ (-1)ⁱ ∂ⁱ` of the cobar complex, in coordinates (1.12):
for `F ∈ Fl_{n+1}(V)`,
`dα(V,z,F) = α(V/F₁, z|_{V/F₁}, F|_{V/F₁}) + ∑_{0<i<n+1} (-1)ⁱ α(V, z, F ∖ Fᵢ)
             + (-1)^{n+1} α(Fₙ, z|_{Fₙ}, F|_{Fₙ})`. -/
def dRaw (x : EBicomod F k) (n : ℕ) (α : RawCochain x) : RawCochain x := fun V =>
  LinearMap.pi fun G : Flag F V =>
    if G.len = n + 1 then
      (LinearMap.proj (G.project (G.nth 1)) ∘ₗ α (quo (G.nth 1)) ∘ₗ x.proj V (G.nth 1)) +
      faceSum _ G (α V) +
      ((-1 : k) ^ (n + 1)) • (LinearMap.proj (G.restrict (G.nth n)) ∘ₗ α (sub (G.nth n)) ∘ₗ
          x.res V (G.nth n))
    else 0

/-- Only the middle faces: this is `Hom_Sp(x, −)` applied to the coface maps (1.8)
of `ē^{⊗•}`. -/
def dMidRaw (x : EBicomod F k) (n : ℕ) (α : RawCochain x) : RawCochain x := fun V =>
  LinearMap.pi fun G : Flag F V =>
    if G.len = n + 1 then
      faceSum _ G (α V)
    else 0

/-- The differential `d` as a linear map on raw cochains. -/
def d (x : EBicomod F k) (n : ℕ) : RawCochain x →ₗ[k] RawCochain x where
  toFun := dRaw x n
  map_add' := by
    intro α β
    funext V
    apply LinearMap.ext
    intro z
    funext G
    simp only [dRaw, LinearMap.pi_apply, LinearMap.add_apply, Pi.add_apply, faceSum_add]
    split_ifs
    · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, Pi.add_apply,
        LinearMap.proj_apply, smul_eq_mul]
      ring
    · simp
  map_smul' := by
    intro r α
    funext V
    apply LinearMap.ext
    intro z
    funext G
    simp only [dRaw, LinearMap.pi_apply, LinearMap.smul_apply, Pi.smul_apply, faceSum_smul]
    split_ifs
    · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, Pi.smul_apply,
        LinearMap.proj_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp

theorem term_proj_nat (x : EBicomod F k) {n : ℕ} {α : RawCochain x} (hα : α ∈ cochains x n)
    {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) (z : x.X.ev V) (G : Flag F V)
    (S : Submodule F V) (S' : Submodule F W) (hS : S' = S.map (e : V →ₗ[F] W)) :
    α (quo S') (x.proj W S' (x.X.mapEquiv e z)) ((G.map e).project S') =
      α (quo S) (x.proj V S z) (G.project S) := by
  subst hS
  have h1 := LinearMap.congr_fun (x.proj_natural e S) z
  simp only [LinearMap.comp_apply] at h1
  rw [← h1, Flag.project_map]
  exact hα.2 (quo S) (quo (S.map (e : V →ₗ[F] W))) (Submodule.Quotient.equiv S _ e rfl)
    (x.proj V S z) (G.project S)

theorem term_res_nat (x : EBicomod F k) {n : ℕ} {α : RawCochain x} (hα : α ∈ cochains x n)
    {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) (z : x.X.ev V) (G : Flag F V)
    (S : Submodule F V) (S' : Submodule F W) (hS : S' = S.map (e : V →ₗ[F] W)) :
    α (sub S') (x.res W S' (x.X.mapEquiv e z)) ((G.map e).restrict S') =
      α (sub S) (x.res V S z) (G.restrict S) := by
  subst hS
  have h1 := LinearMap.congr_fun (x.res_natural e S) z
  simp only [LinearMap.comp_apply] at h1
  rw [← h1, Flag.restrict_map]
  exact hα.2 (sub S) (sub (S.map (e : V →ₗ[F] W))) (e.submoduleMap S)
    (x.res V S z) (G.restrict S)

theorem faceSum_nat (x : EBicomod F k) {n : ℕ} {α : RawCochain x} (hα : α ∈ cochains x n)
    {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) (z : x.X.ev V) (G : Flag F V) :
    faceSum _ (G.map e) (α W) (x.X.mapEquiv e z) = faceSum _ G (α V) z := by
  unfold faceSum
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  have hc : (G.map e).carrier = G.carrier.image (Submodule.map (e : V →ₗ[F] W)) := rfl
  rw [hc, Finset.sum_image (fun A _ B _ h =>
    Submodule.map_injective_of_injective e.injective h)]
  refine Finset.sum_congr rfl fun A hA => ?_
  by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
  · have h' := (Submodule.map_ne_bot_top_iff e A).2 h
    rw [dif_pos h', dif_pos h]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Flag.index_map e G hA, Flag.erase_map G e A h h']
    exact congrArg _ (hα.2 V W e z (G.erase A h))
  · have h' : ¬ (A.map (e : V →ₗ[F] W) ≠ ⊥ ∧ A.map (e : V →ₗ[F] W) ≠ ⊤) :=
      fun hh => h ((Submodule.map_ne_bot_top_iff e A).1 hh)
    rw [dif_neg h', dif_neg h]
    simp

theorem d_mem (x : EBicomod F k) {n : ℕ} {α : RawCochain x} (hα : α ∈ cochains x n) :
    d x n α ∈ cochains x (n + 1) := by
  refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
  · show dRaw x n α V z G = 0
    simp [dRaw, hG]
  · show dRaw x n α W (x.X.mapEquiv e z) (G.map e) = dRaw x n α V z G
    by_cases hG : G.len = n + 1
    · have hG' : (G.map e).len = n + 1 := by rw [Flag.len_map]; exact hG
      simp only [dRaw, LinearMap.pi_apply, if_pos hG, if_pos hG', LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      rw [faceSum_nat x hα e z G]
      congr 2
      · exact term_proj_nat x hα e z G (G.nth 1) _ (Flag.nth_map e G 1)
      · exact term_res_nat x hα e z G (G.nth n) _ (Flag.nth_map e G n)
    · have hG' : ¬ (G.map e).len = n + 1 := by rwa [Flag.len_map]
      simp [dRaw, hG, hG']

theorem faceSum_eq {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X] (G : Flag F V)
    (γ : X →ₗ[k] (Flag F V → k)) (z : X) :
    faceSum X G γ z = ∑ p ∈ Finset.range (G.len + 1),
      if 0 < p ∧ p < G.len then ((-1 : k) ^ p) * γ z (G.eraseAt p) else 0 := by
  unfold faceSum
  rw [LinearMap.sum_apply]
  have hc := G.card_eq_len_succ
  conv_lhs => rw [G.carrier_eq_image_nth, hc]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_range] at hp
    obtain ⟨hmem, hidx⟩ := G.nth_mem (i := p) (by omega)
    by_cases h : 0 < p ∧ p < G.len
    · have h' := Flag.nth_ne_bot_top G h
      rw [dif_pos h', if_pos h, hidx]
      simp [Flag.eraseAt, dif_pos h]
    · have h' : ¬ (G.nth p ≠ ⊥ ∧ G.nth p ≠ ⊤) := by
        rintro ⟨h1, h2⟩
        apply h
        refine ⟨?_, ?_⟩
        · rcases Nat.eq_zero_or_pos p with rfl | hp0
          · exact absurd G.nth_zero h1
          · exact hp0
        · by_contra hge
          have : p = G.len := by omega
          subst this
          exact h2 G.nth_len
      rw [dif_neg h', if_neg h]; simp
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have h1 := (G.nth_mem (i := i) (by omega)).2
    have h2 := (G.nth_mem (i := j) (by omega)).2
    rw [← h1, ← h2, hij]

/-- The `p`-th face value of a cochain, `0 ≤ p ≤ len G`. -/
def faceVal (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F) (z : x.X.ev V)
    (G : Flag F V) (p : ℕ) : k :=
  if p = 0 then α (quo (G.nth 1)) (x.proj V (G.nth 1) z) (G.project (G.nth 1))
  else if p = G.len then
    α (sub (G.nth (G.len - 1))) (x.res V (G.nth (G.len - 1)) z) (G.restrict (G.nth (G.len - 1)))
  else α V z (G.eraseAt p)

theorem dRaw_eq (x : EBicomod F k) (n : ℕ) (α : RawCochain x) (V : FGModuleCat.{0} F)
    (z : x.X.ev V) (G : Flag F V) (hG : G.len = n + 1) :
    dRaw x n α V z G = ∑ p ∈ Finset.range (n + 2), ((-1 : k) ^ p) * faceVal x α V z G p := by
  simp only [dRaw, LinearMap.pi_apply, if_pos hG, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul]
  rw [faceSum_eq, hG, Finset.sum_range_succ, Finset.sum_range_succ']
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have h0 : faceVal x α V z G 0 =
      α (quo (G.nth 1)) (x.proj V (G.nth 1) z) (G.project (G.nth 1)) := by simp [faceVal]
  have hl : faceVal x α V z G (n + 1) =
      α (sub (G.nth n)) (x.res V (G.nth n) z) (G.restrict (G.nth n)) := by
    simp only [faceVal]
    rw [if_neg (by omega), if_pos hG.symm, show G.len - 1 = n by omega]
  have hm : ∀ q ∈ Finset.range n, faceVal x α V z G (q + 1) = α V z (G.eraseAt (q + 1)) := by
    intro q hq
    rw [Finset.mem_range] at hq
    simp only [faceVal]
    rw [if_neg (by omega), if_neg (by omega)]
  have e1 : ∑ q ∈ Finset.range n, (if 0 < q + 1 ∧ q + 1 < n + 1 then
        (-1 : k) ^ (q + 1) * α V z (G.eraseAt (q + 1)) else 0) =
      ∑ q ∈ Finset.range n, (-1 : k) ^ (q + 1) * faceVal x α V z G (q + 1) :=
    Finset.sum_congr rfl fun q hq => by
      rw [hm q hq, if_pos ⟨by omega, by rw [Finset.mem_range] at hq; omega⟩]
  rw [e1, h0, hl, if_neg (by omega), if_neg (by omega)]
  simp
  ring

/-- Naturality of a raw cochain under linear isomorphisms. -/
def IsNat (x : EBicomod F k) (α : RawCochain x) : Prop :=
  ∀ (V W : FGModuleCat.{0} F) (e : V ≃ₗ[F] W) z (G : Flag F V),
    α W (x.X.mapEquiv e z) (G.map e) = α V z G

theorem proj_congr (x : EBicomod F k) (α : RawCochain x) {V : FGModuleCat.{0} F}
    (z : x.X.ev V) (G : Flag F V) {S S' : Submodule F V} (h : S = S') :
    α (quo S') (x.proj V S' z) (G.project S') = α (quo S) (x.proj V S z) (G.project S) := by
  subst h; rfl

theorem res_congr (x : EBicomod F k) (α : RawCochain x) {V : FGModuleCat.{0} F}
    (z : x.X.ev V) (G : Flag F V) {S S' : Submodule F V} (h : S = S') :
    α (sub S') (x.res V S' z) (G.restrict S') = α (sub S) (x.res V S z) (G.restrict S) := by
  subst h; rfl

theorem proj_proj_nat (x : EBicomod F k) {α : RawCochain x} (hα : IsNat x α)
    {V : FGModuleCat.{0} F} (z : x.X.ev V) (G : Flag F V) (T S : Submodule F V) (h : T ≤ S)
    (Sb : Submodule F (quo T)) (hSb : Sb = S.map T.mkQ) :
    α (quo Sb) (x.proj (quo T) Sb (x.proj V T z)) ((G.project T).project Sb) =
      α (quo S) (x.proj V S z) (G.project S) := by
  subst hSb
  have h1 := LinearMap.congr_fun (x.proj_proj V T S h) z
  simp only [LinearMap.comp_apply] at h1
  rw [← Flag.project_project G T S h, ← h1]
  exact (hα _ _ _ _ _).symm

theorem proj_res_nat (x : EBicomod F k) {α : RawCochain x} (hα : IsNat x α)
    {V : FGModuleCat.{0} F} (z : x.X.ev V) (G : Flag F V) (T S : Submodule F V) (h : T ≤ S)
    (Tc : Submodule F (sub S)) (hTc : Tc = T.comap S.subtype)
    (Sb : Submodule F (quo T)) (hSb : Sb = S.map T.mkQ) :
    α (quo Tc) (x.proj (sub S) Tc (x.res V S z)) ((G.restrict S).project Tc) =
      α (sub Sb) (x.res (quo T) Sb (x.proj V T z)) ((G.project T).restrict Sb) := by
  subst hTc hSb
  have h1 := LinearMap.congr_fun (x.proj_res V T S h) z
  simp only [LinearMap.comp_apply] at h1
  rw [← Flag.project_restrict G T S h, ← h1]
  exact (hα _ _ _ _ _).symm

theorem res_res_nat (x : EBicomod F k) {α : RawCochain x} (hα : IsNat x α)
    {V : FGModuleCat.{0} F} (z : x.X.ev V) (G : Flag F V) (T S : Submodule F V) (h : T ≤ S)
    (Tc : Submodule F (sub S)) (hTc : Tc = T.comap S.subtype) :
    α (sub Tc) (x.res (sub S) Tc (x.res V S z)) ((G.restrict S).restrict Tc) =
      α (sub T) (x.res V T z) (G.restrict T) := by
  subst hTc
  have h1 := LinearMap.congr_fun (x.res_res V T S h) z
  simp only [LinearMap.comp_apply] at h1
  rw [← Flag.restrict_restrict G T S h, ← h1]
  exact (hα _ _ _ _ _).symm

def face2 (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F) (z : x.X.ev V)
    (G : Flag F V) (j i : ℕ) : k :=
  if j = 0 then faceVal x α (quo (G.nth 1)) (x.proj V (G.nth 1) z) (G.project (G.nth 1)) i
  else if j = G.len then
    faceVal x α (sub (G.nth (G.len - 1))) (x.res V (G.nth (G.len - 1)) z)
      (G.restrict (G.nth (G.len - 1))) i
  else faceVal x α V z (G.eraseAt j) i

theorem faceVal_mid (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F) (z : x.X.ev V)
    (G : Flag F V) {p : ℕ} (h : 0 < p ∧ p < G.len) :
    faceVal x α V z G p = α V z (G.eraseAt p) := by
  simp only [faceVal]
  rw [if_neg (by omega), if_neg (by omega)]

theorem faceVal_zero (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F) (z : x.X.ev V)
    (G : Flag F V) : faceVal x α V z G 0 =
      α (quo (G.nth 1)) (x.proj V (G.nth 1) z) (G.project (G.nth 1)) := by
  simp [faceVal]

theorem faceVal_last (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F) (z : x.X.ev V)
    (G : Flag F V) (h : 0 < G.len) : faceVal x α V z G G.len =
      α (sub (G.nth (G.len - 1))) (x.res V (G.nth (G.len - 1)) z)
        (G.restrict (G.nth (G.len - 1))) := by
  simp only [faceVal]
  rw [if_neg (by omega)]; simp

theorem face2_mid (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F) (z : x.X.ev V)
    (G : Flag F V) {j : ℕ} (h : 0 < j ∧ j < G.len) (i : ℕ) :
    face2 x α V z G j i = faceVal x α V z (G.eraseAt j) i := by
  simp only [face2]
  rw [if_neg (by omega), if_neg (by omega)]

theorem face2_zero (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F) (z : x.X.ev V)
    (G : Flag F V) (i : ℕ) :
    face2 x α V z G 0 i = faceVal x α (quo (G.nth 1)) (x.proj V (G.nth 1) z)
      (G.project (G.nth 1)) i := by
  simp [face2]

theorem face2_last (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F) (z : x.X.ev V)
    (G : Flag F V) (h : 0 < G.len) (i : ℕ) :
    face2 x α V z G G.len i = faceVal x α (sub (G.nth (G.len - 1)))
      (x.res V (G.nth (G.len - 1)) z) (G.restrict (G.nth (G.len - 1))) i := by
  simp only [face2]
  rw [if_neg (by omega)]; simp

theorem caseA (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F) (z : x.X.ev V)
    (G : Flag F V) {i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j < G.len) :
    face2 x α V z G j i = face2 x α V z G i (j - 1) := by
  have hjm : 0 < j ∧ j < G.len := ⟨by omega, hj⟩
  have him : 0 < i ∧ i < G.len := ⟨hi, by omega⟩
  rw [face2_mid x α V z G hjm, face2_mid x α V z G him,
    faceVal_mid x α V z _ (by rw [G.len_eraseAt hjm]; omega),
    faceVal_mid x α V z _ (by rw [G.len_eraseAt him]; omega), G.eraseAt_eraseAt hi hij hj]

theorem faceVal_last' (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F)
    (z : x.X.ev V) (G : Flag F V) (h : 0 < G.len) {p : ℕ} (hp : p = G.len) :
    faceVal x α V z G p =
      α (sub (G.nth (G.len - 1))) (x.res V (G.nth (G.len - 1)) z)
        (G.restrict (G.nth (G.len - 1))) := by
  subst hp; exact faceVal_last x α V z G h

theorem caseB2 (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F) (z : x.X.ev V)
    (G : Flag F V) {j : ℕ} (hj2 : 2 ≤ j) (hj : j < G.len) :
    face2 x α V z G j 0 = face2 x α V z G 0 (j - 1) := by
  have hjm : 0 < j ∧ j < G.len := ⟨by omega, hj⟩
  rw [face2_mid x α V z G hjm, face2_zero, faceVal_zero]
  have hE : (G.eraseAt j).nth 1 = G.nth 1 := by
    rw [G.nth_eraseAt hjm (by omega), if_pos (by omega)]
  rw [proj_congr x α _ (G.eraseAt j) hE.symm, G.project_eraseAt ⟨hj2, hj⟩ _ rfl]
  rw [faceVal_mid x α _ _ _ (by rw [Flag.len_project G (by omega) _ rfl]; omega)]

theorem caseB1 (x : EBicomod F k) (α : RawCochain x) (hα : IsNat x α) (V : FGModuleCat.{0} F)
    (z : x.X.ev V) (G : Flag F V) (hm : 2 ≤ G.len) :
    face2 x α V z G 1 0 = face2 x α V z G 0 0 := by
  have h1m : 0 < 1 ∧ 1 < G.len := ⟨by omega, by omega⟩
  rw [face2_mid x α V z G h1m, face2_zero, faceVal_zero, faceVal_zero]
  have hE : (G.eraseAt 1).nth 1 = G.nth 2 := by
    rw [G.nth_eraseAt h1m (by omega), if_neg (by omega)]
  have hle : G.nth 1 ≤ G.nth 2 := G.nth_mono (by omega) (by have := G.card_eq_len_succ; omega)
  have hEr : G.eraseAt 1 = G.erase (G.nth 1) (G.nth_ne_bot_top h1m) := by
    simp [Flag.eraseAt, h1m]
  rw [proj_congr x α _ (G.eraseAt 1) hE.symm, hEr,
    G.project_erase_of_le _ (G.nth_mem' (by omega)) _ _ hle]
  have hG' : (G.project (G.nth 1)).nth 1 = (G.nth 2).map (G.nth 1).mkQ := by
    rw [G.nth_project (by omega) _ rfl (by omega)]
  rw [proj_congr x α (x.proj V (G.nth 1) z) (G.project (G.nth 1)) hG'.symm]
  exact (proj_proj_nat x hα z G (G.nth 1) (G.nth 2) hle _ rfl).symm

theorem caseC (x : EBicomod F k) (α : RawCochain x) (hα : IsNat x α) (V : FGModuleCat.{0} F)
    (z : x.X.ev V) (G : Flag F V) (hm : 2 ≤ G.len) :
    face2 x α V z G G.len 0 = face2 x α V z G 0 (G.len - 1) := by
  rw [face2_last x α V z G (by omega), face2_zero, faceVal_zero]
  have hle : G.nth 1 ≤ G.nth (G.len - 1) :=
    G.nth_mono (by omega) (by have := G.card_eq_len_succ; omega)
  have hR : (G.restrict (G.nth (G.len - 1))).nth 1 = (G.nth 1).comap (G.nth (G.len - 1)).subtype := by
    rw [G.nth_restrict (by omega) _ rfl (by omega)]
  rw [proj_congr x α (x.res V (G.nth (G.len - 1)) z) (G.restrict (G.nth (G.len - 1)))
    (S := (G.nth 1).comap (G.nth (G.len - 1)).subtype) hR.symm]
  rw [proj_res_nat x hα z G (G.nth 1) (G.nth (G.len - 1)) hle _ rfl _ rfl]
  have hl' : (G.project (G.nth 1)).len = G.len - 1 := G.len_project (by omega) _ rfl
  rw [faceVal_last' x α _ _ _ (by omega) (by omega : G.len - 1 = (G.project (G.nth 1)).len)]
  have hG' : (G.project (G.nth 1)).nth ((G.project (G.nth 1)).len - 1) =
      (G.nth (G.len - 1)).map (G.nth 1).mkQ := by
    rw [G.nth_project (by omega) _ rfl (by omega)]
    congr 2; omega
  rw [res_congr x α (x.proj V (G.nth 1) z) (G.project (G.nth 1))
    (S := (G.nth (G.len - 1)).map (G.nth 1).mkQ) hG'.symm]

theorem caseD (x : EBicomod F k) (α : RawCochain x) (V : FGModuleCat.{0} F)
    (z : x.X.ev V) (G : Flag F V) {i : ℕ} (hi : 1 ≤ i) (hi2 : i + 2 ≤ G.len) :
    face2 x α V z G G.len i = face2 x α V z G i (G.len - 1) := by
  have him : 0 < i ∧ i < G.len := ⟨by omega, by omega⟩
  rw [face2_last x α V z G (by omega), face2_mid x α V z G him]
  have hlr := G.len_restrict (by omega) _ (rfl : G.nth (G.len - 1) = _)
  rw [faceVal_mid x α _ _ _ (by rw [hlr]; omega)]
  have hl1 := G.len_eraseAt him
  rw [faceVal_last' x α _ _ _ (by omega) (by omega : G.len - 1 = (G.eraseAt i).len)]
  have hE : (G.eraseAt i).nth ((G.eraseAt i).len - 1) = G.nth (G.len - 1) := by
    rw [hl1, G.nth_eraseAt him (by omega), if_neg (by omega)]
    congr 1; omega
  rw [res_congr x α z (G.eraseAt i) (S := G.nth (G.len - 1)) hE.symm,
    G.restrict_eraseAt ⟨hi, hi2⟩ _ rfl]

theorem caseE (x : EBicomod F k) (α : RawCochain x) (hα : IsNat x α) (V : FGModuleCat.{0} F)
    (z : x.X.ev V) (G : Flag F V) (hm : 2 ≤ G.len) :
    face2 x α V z G G.len (G.len - 1) = face2 x α V z G (G.len - 1) (G.len - 1) := by
  have him : 0 < G.len - 1 ∧ G.len - 1 < G.len := ⟨by omega, by omega⟩
  rw [face2_last x α V z G (by omega), face2_mid x α V z G him]
  have hlr := G.len_restrict (by omega) _ (rfl : G.nth (G.len - 1) = _)
  rw [faceVal_last' x α _ _ _ (by omega) (by omega : G.len - 1 = (G.restrict (G.nth (G.len - 1))).len)]
  have hl1 := G.len_eraseAt him
  rw [faceVal_last' x α _ _ _ (by omega) (by omega : G.len - 1 = (G.eraseAt (G.len - 1)).len)]
  have hle : G.nth (G.len - 2) ≤ G.nth (G.len - 1) :=
    G.nth_mono (by omega) (by have := G.card_eq_len_succ; omega)
  have hR : (G.restrict (G.nth (G.len - 1))).nth ((G.restrict (G.nth (G.len - 1))).len - 1) =
      (G.nth (G.len - 2)).comap (G.nth (G.len - 1)).subtype := by
    rw [hlr, G.nth_restrict (by omega) _ rfl (by omega)]
    congr 2
  have hE : (G.eraseAt (G.len - 1)).nth ((G.eraseAt (G.len - 1)).len - 1) = G.nth (G.len - 2) := by
    rw [hl1, G.nth_eraseAt him (by omega), if_pos (by omega)]
    congr 1
  rw [res_congr x α (x.res V (G.nth (G.len - 1)) z) (G.restrict (G.nth (G.len - 1)))
    (S := (G.nth (G.len - 2)).comap (G.nth (G.len - 1)).subtype) hR.symm,
    res_res_nat x hα z G _ _ hle _ rfl,
    res_congr x α z (G.eraseAt (G.len - 1)) (S := G.nth (G.len - 2)) hE.symm]
  have hmem : G.nth (G.len - 1) ∈ G.carrier := G.nth_mem' (by omega)
  have hEr : G.eraseAt (G.len - 1) = G.erase (G.nth (G.len - 1))
      (G.nth_ne_bot_top him) := by simp [Flag.eraseAt, him]
  rw [hEr, G.restrict_erase_of_ge _ hmem _ _ hle]

theorem face2_key (x : EBicomod F k) (α : RawCochain x) (hα : IsNat x α) (V : FGModuleCat.{0} F)
    (z : x.X.ev V) (G : Flag F V) (hm : 2 ≤ G.len) {i j : ℕ} (hij : i < j) (hj : j ≤ G.len) :
    face2 x α V z G j i = face2 x α V z G i (j - 1) := by
  by_cases hjl : j = G.len
  · subst hjl
    by_cases hi0 : i = 0
    · subst hi0; exact caseC x α hα V z G hm
    · by_cases hil : i = G.len - 1
      · subst hil; exact caseE x α hα V z G hm
      · exact caseD x α V z G (by omega) (by omega)
  · have hjl' : j < G.len := by omega
    by_cases hi0 : i = 0
    · subst hi0
      by_cases hj1 : j = 1
      · subst hj1; exact caseB1 x α hα V z G hm
      · exact caseB2 x α V z G (by omega) hjl'
    · exact caseA x α V z G (by omega) hij hjl'

theorem faceVal_d (x : EBicomod F k) (n : ℕ) (α : RawCochain x) (V : FGModuleCat.{0} F)
    (z : x.X.ev V) (G : Flag F V) (hG : G.len = n + 2) {j : ℕ} (hj : j ≤ n + 2) :
    faceVal x (d x n α) V z G j =
      ∑ i ∈ Finset.range (n + 2), ((-1 : k) ^ i) * face2 x α V z G j i := by
  by_cases h0 : j = 0
  · subst h0
    rw [faceVal_zero]
    show dRaw x n α _ _ _ = _
    rw [dRaw_eq x n α _ _ _ (by rw [G.len_project (by omega) _ rfl]; omega)]
    simp only [face2_zero]
  · by_cases hl : j = G.len
    · subst hl
      rw [faceVal_last x (d x n α) V z G (by omega)]
      show dRaw x n α _ _ _ = _
      rw [dRaw_eq x n α _ _ _ (by rw [G.len_restrict (by omega) _ rfl]; omega)]
      simp only [face2_last x α V z G (by omega)]
    · have hm : 0 < j ∧ j < G.len := ⟨by omega, by omega⟩
      rw [faceVal_mid x _ V z G hm]
      show dRaw x n α _ _ _ = _
      rw [dRaw_eq x n α _ _ _ (by rw [G.len_eraseAt hm]; omega)]
      simp only [face2_mid x α V z G hm]

theorem d_comp_d_aux (x : EBicomod F k) (n : ℕ) {α : RawCochain x} (hα : IsNat x α)
    (V : FGModuleCat.{0} F) (z : x.X.ev V) (G : Flag F V) :
    d x (n + 1) (d x n α) V z G = 0 := by
  by_cases hG : G.len = n + 2
  · show dRaw x (n + 1) (d x n α) V z G = 0
    rw [dRaw_eq x (n + 1) _ V z G hG]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [faceVal_d x n α V z G hG (by rw [Finset.mem_range] at hj; omega)])]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    refine Finset.sum_involution
      (fun p _ => if p.2 < p.1 then (p.2, p.1 - 1) else (p.2 + 1, p.1)) ?_ ?_ ?_ ?_
    · rintro ⟨j, i⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      by_cases hij : i < j
      · simp only [if_pos hij]
        rw [← face2_key x α hα V z G (by omega) hij (by omega)]
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
      · simp only [if_neg hij]
        rw [face2_key x α hα V z G (by omega) (by omega : j < i + 1) (by omega)]
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
    · rintro ⟨j, i⟩ hp _
      by_cases hij : i < j
      · simp only [if_pos hij, ne_eq, Prod.mk.injEq]; omega
      · simp only [if_neg hij, ne_eq, Prod.mk.injEq]; omega
    · rintro ⟨j, i⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
      by_cases hij : i < j
      · simp only [if_pos hij]; omega
      · simp only [if_neg hij]; omega
    · rintro ⟨j, i⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      by_cases hij : i < j
      · simp only [if_pos hij]
        have : ¬ (j - 1 < i) := by omega
        simp only [if_neg this]
        ext <;> simp <;> omega
      · simp only [if_neg hij]
        have : i + 1 > j := by omega
        simp only [if_pos this]
        ext <;> simp
  · simp [d, dRaw, hG]

theorem d_comp_d (x : EBicomod F k) (n : ℕ) {α : RawCochain x} (hα : α ∈ cochains x n) :
    d x (n + 1) (d x n α) = 0 := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  exact d_comp_d_aux x n hα.2 V z G

/-- `n`-cocycles `Zⁿ(x)`. -/
def cocycles (x : EBicomod F k) (n : ℕ) : Submodule k (RawCochain x) :=
  cochains x n ⊓ LinearMap.ker (d x n)

/-- `n`-coboundaries `Bⁿ(x)`. -/
def coboundaries (x : EBicomod F k) : (n : ℕ) → Submodule k (RawCochain x)
  | 0 => ⊥
  | n + 1 => (cochains x n).map (d x n)

/-- The cohomology `Hⁿ(x)` of an `e`-bicomodule, computed by the reduced cobar complex.
(The thesis defines `H•(x) = Ext•_{e-bicomod}(x, e)`, using Corollary 1.5, and
notes that the cobar complex computes it; see the `TODO` below.) -/
abbrev H (x : EBicomod F k) (n : ℕ) := Subquot (cocycles x n) (coboundaries x n)

/-- The class `[α] ∈ Hⁿ(x)` of a cocycle. -/
def cohClass (x : EBicomod F k) {n : ℕ} (α : RawCochain x) (h : α ∈ cocycles x n) : H x n :=
  Subquot.mk α h

/- TODO: `Hⁿ(x) ≅ Extⁿ(x, e)` in `e`-bicomodules. Needs `Ext` in
`Bicomod (expComon F k)` (abelian, with enough injectives by Corollary 1.5). -/

/-- **Lemma 1.6.** If `x` is a trivial `e`-bicomodule, `C•(x)` is `Hom_Sp(x, ē^{⊗•})`:
the outer cofaces vanish and only the middle ones survive. -/
theorem dRaw_trivial (x : GLSpecies F k) (n : ℕ) (α : RawCochain (EBicomod.trivial x))
    (hα : α ∈ cochains (EBicomod.trivial x) n) :
    dRaw (EBicomod.trivial x) n α = dMidRaw (EBicomod.trivial x) n α := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  simp only [dRaw, dMidRaw, LinearMap.pi_apply]
  by_cases hG : G.len = n + 1
  · rw [if_pos hG, if_pos hG]
    have hcard : G.carrier.card = n + 2 := by rw [G.card_eq_len_succ, hG]
    have h1 : G.nth 1 ≠ ⊥ := by
      have := G.nth_lt_nth (Nat.zero_lt_one) (by omega)
      rw [G.nth_zero] at this
      exact this.ne'
    have hn : G.nth n ≠ ⊤ := by
      have := G.nth_lt_nth (by omega : n < n + 1) (by omega)
      rw [show n + 1 = G.len by omega, G.nth_len] at this
      exact this.ne
    have e1 : (EBicomod.trivial x).proj V (G.nth 1) = 0 := by
      simp only [EBicomod.trivial, dif_neg h1]
      rfl
    have e3 : (EBicomod.trivial x).res V (G.nth n) = 0 := by
      simp only [EBicomod.trivial, dif_neg hn]
      rfl
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, e1, e3,
      map_zero, LinearMap.zero_apply, Pi.zero_apply, LinearMap.proj_apply]
    simp
  · rw [if_neg hG, if_neg hG]

/-- The cup product `f ⌣ g = (f ⊗ g) ∘ Δ` for `f ∈ Cᵐ`, `g ∈ Cⁿ`, in coordinates:
for `F ∈ Fl_{m+n}(V)` only the summand `S = F_m` of `Δ` contributes, giving
`(f ⌣ g)(V, z, F) = (f(F_m, −, F|_{F_m}) ⊗ g(V/F_m, −, F|_{V/F_m}))(Δ_{F_m} z)`. -/
def cupRaw (x : EBicomodCoalg F k) (m n : ℕ) (f g : RawCochain x.toEBicomod) :
    RawCochain x.toEBicomod := fun V =>
  LinearMap.pi fun G : Flag F V =>
    if G.len = m + n then
      LinearMap.mul' k k ∘ₗ
        TensorProduct.map (LinearMap.proj (G.restrict (G.nth m)) ∘ₗ f (sub (G.nth m)))
          (LinearMap.proj (G.project (G.nth m)) ∘ₗ g (quo (G.nth m))) ∘ₗ
        x.comul V (G.nth m)
    else 0

theorem cupRaw_mem (x : EBicomodCoalg F k) {m n : ℕ} {f g : RawCochain x.toEBicomod}
    (hf : f ∈ cochains x.toEBicomod m) (hg : g ∈ cochains x.toEBicomod n) :
    cupRaw x m n f g ∈ cochains x.toEBicomod (m + n) := by
  refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
  · show cupRaw x m n f g V z G = 0
    simp [cupRaw, hG]
  · show cupRaw x m n f g W (x.X.mapEquiv e z) (G.map e) = cupRaw x m n f g V z G
    by_cases hG : G.len = m + n
    · have hG' : (G.map e).len = m + n := by rw [Flag.len_map]; exact hG
      simp only [cupRaw, LinearMap.pi_apply, if_pos hG, if_pos hG', LinearMap.comp_apply]
      have key : ∀ (S' : Submodule F W), S' = (G.nth m).map (e : V →ₗ[F] W) →
          (LinearMap.mul' k k) ((TensorProduct.map
            (LinearMap.proj ((G.map e).restrict S') ∘ₗ f (sub S'))
            (LinearMap.proj ((G.map e).project S') ∘ₗ g (quo S'))) (x.comul W S' (x.X.mapEquiv e z))) =
          (LinearMap.mul' k k) ((TensorProduct.map
            (LinearMap.proj (G.restrict (G.nth m)) ∘ₗ f (sub (G.nth m)))
            (LinearMap.proj (G.project (G.nth m)) ∘ₗ g (quo (G.nth m)))) (x.comul V (G.nth m) z)) := by
        intro S' hS'
        subst hS'
        have h1 := LinearMap.congr_fun (x.comul_natural e (G.nth m)) z
        simp only [LinearMap.comp_apply] at h1
        rw [← h1, ← LinearMap.comp_apply (TensorProduct.map _ _) (TensorProduct.map _ _),
          ← TensorProduct.map_comp]
        have ha : (LinearMap.proj ((G.map e).restrict ((G.nth m).map (e : V →ₗ[F] W))) ∘ₗ
              f (sub ((G.nth m).map (e : V →ₗ[F] W)))) ∘ₗ
            x.X.mapEquiv (e.submoduleMap (G.nth m)) =
            LinearMap.proj (G.restrict (G.nth m)) ∘ₗ f (sub (G.nth m)) := by
          apply LinearMap.ext
          intro u
          change f (sub ((G.nth m).map (e : V →ₗ[F] W)))
              (x.X.mapEquiv (e.submoduleMap (G.nth m)) u)
              ((G.map e).restrict ((G.nth m).map (e : V →ₗ[F] W))) =
            f (sub (G.nth m)) u (G.restrict (G.nth m))
          rw [Flag.restrict_map]
          exact hf.2 (sub (G.nth m)) (sub ((G.nth m).map (e : V →ₗ[F] W))) (e.submoduleMap (G.nth m)) u
            (G.restrict (G.nth m))
        have hb : (LinearMap.proj ((G.map e).project ((G.nth m).map (e : V →ₗ[F] W))) ∘ₗ
              g (quo ((G.nth m).map (e : V →ₗ[F] W)))) ∘ₗ
            x.X.mapEquiv (Submodule.Quotient.equiv (G.nth m) _ e rfl) =
            LinearMap.proj (G.project (G.nth m)) ∘ₗ g (quo (G.nth m)) := by
          apply LinearMap.ext
          intro u
          change g (quo ((G.nth m).map (e : V →ₗ[F] W)))
              (x.X.mapEquiv (Submodule.Quotient.equiv (G.nth m) _ e rfl) u)
              ((G.map e).project ((G.nth m).map (e : V →ₗ[F] W))) =
            g (quo (G.nth m)) u (G.project (G.nth m))
          rw [Flag.project_map]
          exact hg.2 (quo (G.nth m)) (quo ((G.nth m).map (e : V →ₗ[F] W)))
            (Submodule.Quotient.equiv (G.nth m) _ e rfl) u (G.project (G.nth m))
        rw [ha, hb]
      exact key _ (Flag.nth_map e G m)
    · have hG' : ¬ (G.map e).len = m + n := by rwa [Flag.len_map]
      simp [cupRaw, hG, hG']

end Cobar

end MartinPhd

end
end Chapter1Section4

section Enum

/-
Formalization of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Enumerated flags

A flag whose carrier is the image of a strictly increasing sequence `s : ℕ → Submodule K V`
on `{0,…,N}` is *enumerated* by `s`. This reduces flag identities (for `restrict`, `project`,
`erase`) to identities between sequences. Used for the Leibniz rule (`dRaw_cupRaw`).
-/

open scoped BigOperators

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace Flag

/-- `F` is enumerated by the strictly increasing sequence `s` on `{0,…,N}`. -/
def IsEnum (F : Flag K V) (N : ℕ) (s : ℕ → Submodule K V) : Prop :=
  F.carrier = (Finset.range (N + 1)).image s ∧ ∀ i j, i < j → j ≤ N → s i < s j

theorem eq_map_symm {W : Type*} [AddCommGroup W] [Module K W] {e : V ≃ₗ[K] W} {G : Flag K V}
    {H : Flag K W} (h : G.map e = H) : G = H.map e.symm := by
  subst h
  rw [← Flag.map_trans]
  simp [Flag.map_refl]

theorem IsEnum.injOn {F : Flag K V} {N : ℕ} {s : ℕ → Submodule K V} (h : F.IsEnum N s) :
    Set.InjOn s (Finset.range (N + 1) : Set ℕ) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact (h.2 i j h' (by omega)).ne hij
  · exact (h.2 j i h' (by omega)).ne hij.symm

theorem IsEnum.le_of_le {F : Flag K V} {N : ℕ} {s : ℕ → Submodule K V} (h : F.IsEnum N s)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : s i ≤ s j := by
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (h.2 i j hlt hj).le

theorem IsEnum.len {F : Flag K V} {N : ℕ} {s : ℕ → Submodule K V} (h : F.IsEnum N s) :
    F.len = N := by
  unfold Flag.len
  rw [h.1, Finset.card_image_of_injOn h.injOn, Finset.card_range]
  rfl

theorem IsEnum.mem {F : Flag K V} {N : ℕ} {s : ℕ → Submodule K V} (h : F.IsEnum N s)
    {j : ℕ} (hj : j ≤ N) : s j ∈ F.carrier := by
  rw [h.1]
  exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩

theorem IsEnum.index_eq {F : Flag K V} {N : ℕ} {s : ℕ → Submodule K V} (h : F.IsEnum N s)
    {j : ℕ} (hj : j ≤ N) : F.index (s j) = j := by
  unfold Flag.index
  have : F.carrier.filter (· < s j) = (Finset.range j).image s := by
    ext B
    simp only [Finset.mem_filter, h.1, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hlt⟩
      refine ⟨i, ?_, rfl⟩
      by_contra hij
      push_neg at hij
      rcases hij.eq_or_lt with h' | h'
      · subst h'; exact lt_irrefl _ hlt
      · exact absurd (h.2 j i h' (by omega)) (lt_asymm hlt)
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by omega, rfl⟩, h.2 i j hi hj⟩
  rw [this, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact h.injOn (by simp at ha ⊢; omega) (by simp at hb ⊢; omega) hab

theorem IsEnum.nth_eq {F : Flag K V} {N : ℕ} {s : ℕ → Submodule K V} (h : F.IsEnum N s)
    {j : ℕ} (hj : j ≤ N) : F.nth j = s j := by
  have := F.nth_index (h.mem hj)
  rwa [h.index_eq hj] at this

theorem IsEnum.ext {F F' : Flag K V} {N : ℕ} {s s' : ℕ → Submodule K V} (h : F.IsEnum N s)
    (h' : F'.IsEnum N s') (hss : ∀ j, j ≤ N → s j = s' j) : F = F' := by
  apply Flag.ext
  rw [h.1, h'.1]
  exact Finset.image_congr (fun j hj => hss j (by simp at hj; omega))

theorem isEnum_nth (F : Flag K V) : F.IsEnum F.len F.nth := by
  refine ⟨?_, fun i j hij hj => F.nth_lt_nth hij (by rw [F.card_eq_len_succ]; omega)⟩
  rw [F.carrier_eq_image_nth, F.card_eq_len_succ]

theorem IsEnum.restrict {F : Flag K V} {N : ℕ} {s : ℕ → Submodule K V} (h : F.IsEnum N s)
    {p : ℕ} (hp : p ≤ N) :
    (F.restrict (s p)).IsEnum p (fun j => (s j).comap (s p).subtype) := by
  constructor
  · show F.carrier.image _ = _
    rw [h.1, Finset.image_image]
    ext B
    simp only [Finset.mem_image, Finset.mem_range, Function.comp]
    constructor
    · rintro ⟨j, hj, rfl⟩
      by_cases hjp : j ≤ p
      · exact ⟨j, by omega, rfl⟩
      · refine ⟨p, by omega, ?_⟩
        have h1 : s p ≤ s j := (h.2 p j (by omega) (by omega)).le
        rw [Submodule.comap_subtype_eq_top.2 le_rfl, Submodule.comap_subtype_eq_top.2 h1]
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, by omega, rfl⟩
  · intro i j hij hj
    have hle : (s i).comap (s p).subtype ≤ (s j).comap (s p).subtype :=
      Submodule.comap_mono (h.2 i j hij (by omega)).le
    refine lt_of_le_of_ne hle fun heq => ?_
    have := congrArg (Submodule.map (s p).subtype) heq
    rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype,
      inf_eq_right.2 (h.le_of_le (by omega) hp), inf_eq_right.2 (h.le_of_le (by omega) hp)]
        at this
    exact (h.2 i j hij (by omega)).ne this

theorem IsEnum.project {F : Flag K V} {N : ℕ} {s : ℕ → Submodule K V} (h : F.IsEnum N s)
    {p : ℕ} (hp : p ≤ N) :
    (F.project (s p)).IsEnum (N - p) (fun j => (s (p + j)).map (s p).mkQ) := by
  constructor
  · show F.carrier.image _ = _
    rw [h.1, Finset.image_image]
    ext B
    simp only [Finset.mem_image, Finset.mem_range, Function.comp]
    constructor
    · rintro ⟨j, hj, rfl⟩
      by_cases hjp : p ≤ j
      · exact ⟨j - p, by omega, by rw [show p + (j - p) = j by omega]⟩
      · refine ⟨0, by omega, ?_⟩
        have h1 : s j ≤ s p := h.le_of_le (by omega) hp
        have hb : ∀ A : Submodule K V, A ≤ s p → A.map (s p).mkQ = ⊥ := fun A hA =>
          le_bot_iff.1 (Submodule.map_le_iff_le_comap.2 (by
            rw [Submodule.comap_bot, Submodule.ker_mkQ]; exact hA))
        rw [Nat.add_zero, hb _ h1, hb _ le_rfl]
    · rintro ⟨j, hj, rfl⟩
      exact ⟨p + j, by omega, rfl⟩
  · intro i j hij hj
    have hle : (s (p + i)).map (s p).mkQ ≤ (s (p + j)).map (s p).mkQ :=
      Submodule.map_mono (h.2 (p + i) (p + j) (by omega) (by omega)).le
    refine lt_of_le_of_ne hle fun heq => ?_
    have := congrArg (Submodule.comap (s p).mkQ) heq
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ,
      sup_eq_right.2 (h.le_of_le (show p ≤ p + i by omega) (show p + i ≤ N by omega)),
      sup_eq_right.2 (h.le_of_le (show p ≤ p + j by omega) (show p + j ≤ N by omega))] at this
    exact (h.2 (p + i) (p + j) (by omega) (by omega)).ne this

theorem IsEnum.erase {F : Flag K V} {N : ℕ} {s : ℕ → Submodule K V} (h : F.IsEnum N s)
    {i : ℕ} (hi0 : 0 < i) (hiN : i < N) (hA : s i ≠ ⊥ ∧ s i ≠ ⊤) :
    (F.erase (s i) hA).IsEnum (N - 1) (fun j => if j < i then s j else s (j + 1)) := by
  constructor
  · show F.carrier.erase (s i) = _
    ext B
    simp only [Finset.mem_erase, h.1, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hne, j, hj, rfl⟩
      by_cases hji : j < i
      · exact ⟨j, by omega, by simp [hji]⟩
      · have hji' : j ≠ i := fun e => hne (by rw [e])
        exact ⟨j - 1, by omega, by
          rw [if_neg (by omega), show j - 1 + 1 = j by omega]⟩
    · rintro ⟨j, hj, rfl⟩
      by_cases hji : j < i
      · refine ⟨?_, j, by omega, by simp [hji]⟩
        rw [if_pos hji]
        exact (h.2 j i hji (by omega)).ne
      · refine ⟨?_, j + 1, by omega, by simp [hji]⟩
        rw [if_neg hji]
        exact (h.2 i (j + 1) (by omega) (by omega)).ne'
  · intro a b hab hb
    by_cases ha : a < i <;> by_cases hbi : b < i <;> simp only [ha, hbi, if_true, if_false]
    · exact h.2 a b hab (by omega)
    · exact h.2 a (b + 1) (by omega) (by omega)
    · omega
    · exact h.2 (a + 1) (b + 1) (by omega) (by omega)

theorem len_restrict_gen (H : Flag K V) {p : ℕ} (hp : p ≤ H.len) (S : Submodule K V)
    (hS : H.nth p = S) : (H.restrict S).len = p := by
  subst hS
  exact (H.isEnum_nth.restrict hp).len

theorem nth_restrict_gen (H : Flag K V) {p : ℕ} (hp : p ≤ H.len) (S : Submodule K V)
    (hS : H.nth p = S) {q : ℕ} (hq : q ≤ p) :
    (H.restrict S).nth q = (H.nth q).comap S.subtype := by
  subst hS
  rw [(H.isEnum_nth.restrict hp).nth_eq hq]

theorem len_project_gen (H : Flag K V) {p : ℕ} (hp : p ≤ H.len) (T : Submodule K V)
    (hT : H.nth p = T) : (H.project T).len = H.len - p := by
  subst hT
  exact (H.isEnum_nth.project hp).len

theorem nth_project_gen (H : Flag K V) {p : ℕ} (hp : p ≤ H.len) (T : Submodule K V)
    (hT : H.nth p = T) {q : ℕ} (hq : q ≤ H.len - p) :
    (H.project T).nth q = (H.nth (p + q)).map T.mkQ := by
  subst hT
  rw [(H.isEnum_nth.project hp).nth_eq hq]

end Flag


end MartinPhd

end
end Enum

section Leibniz

/-
Formalization of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Leibniz rule for the cup product (§1.4): infrastructure

Index-based face sums and the pairing `cupPair`, used to prove `dRaw_cupRaw`.
-/

open scoped BigOperators TensorProduct

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] {k : Type} [Field k]

/-- `faceSum` as a sum over positions `i` (the `i`-th member is erased, with sign `(-1)ⁱ`). -/
theorem faceSum_eq_range {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X]
    (G : Flag F V) (γ : X →ₗ[k] (Flag F V → k)) :
    faceSum X G γ = ∑ i ∈ Finset.range (G.len + 1),
      if _ : 0 < i ∧ i < G.len then
        ((-1 : k) ^ i) • (LinearMap.proj (G.eraseAt i) ∘ₗ γ) else 0 := by
  unfold faceSum
  rw [G.carrier_eq_image_nth, G.card_eq_len_succ]
  rw [Finset.sum_image (fun a ha b hb hab => by
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    exact G.isEnum_nth.injOn (by simpa using ha) (by simpa using hb) hab)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ G.len := by simp at hi; omega
  by_cases h : 0 < i ∧ i < G.len
  · have hne := G.nth_ne_bot_top h
    rw [dif_pos hne, dif_pos h, G.index_nth hi']
    simp only [Flag.eraseAt, dif_pos h]
  · rw [dif_neg h, dif_neg]
    rintro ⟨h1, h2⟩
    apply h
    refine ⟨Nat.pos_of_ne_zero fun e => h1 (by rw [e, G.nth_zero]), ?_⟩
    by_contra hge
    have : i = G.len := by omega
    exact h2 (by rw [this, G.nth_len])


section FlagIds

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem eraseAt_eq_erase (G : Flag F V) {i : ℕ} (h : 0 < i ∧ i < G.len) :
    G.eraseAt i = G.erase (G.nth i) (G.nth_ne_bot_top h) := by
  simp only [Flag.eraseAt, dif_pos h]

/-- Erasing a low face commutes with restricting to `G_{m+1}`. -/
theorem restrict_eraseAt_low (G : Flag F V) {i m : ℕ} (hi : 0 < i) (him : i ≤ m)
    (hm : m + 1 ≤ G.len) (S : Submodule F V) (hS : G.nth (m + 1) = S) :
    (G.eraseAt i).restrict S = (G.restrict S).eraseAt i := by
  have hiG : 0 < i ∧ i < G.len := ⟨hi, by omega⟩
  have hnm : (G.eraseAt i).nth m = S := by
    rw [G.nth_eraseAt hiG (by have := G.len_eraseAt hiG; omega), if_neg (by omega), hS]
  have hl1 : (G.eraseAt i).len = G.len - 1 := G.len_eraseAt hiG
  have hl2 : ((G.eraseAt i).restrict S).len = m := Flag.len_restrict_gen _ (by omega) S hnm
  have hl3 : (G.restrict S).len = m + 1 := Flag.len_restrict_gen _ hm S hS
  have hiK : 0 < i ∧ i < (G.restrict S).len := ⟨hi, by omega⟩
  apply Flag.ext_nth (by rw [hl2, (G.restrict S).len_eraseAt hiK, hl3]; rfl)
  intro q hq
  rw [hl2] at hq
  rw [Flag.nth_restrict_gen _ (by omega) S hnm hq,
    (G.restrict S).nth_eraseAt hiK (by omega),
    G.nth_eraseAt hiG (by omega)]
  by_cases hqi : q < i
  · rw [if_pos hqi, if_pos hqi, Flag.nth_restrict_gen _ hm S hS (by omega)]
  · rw [if_neg hqi, if_neg hqi, Flag.nth_restrict_gen _ hm S hS (by omega)]

theorem project_eraseAt_low (G : Flag F V) {i m : ℕ} (hi : 0 < i) (him : i ≤ m)
    (hm : m + 1 ≤ G.len) (S : Submodule F V) (hS : G.nth (m + 1) = S) :
    (G.eraseAt i).project S = G.project S := by
  have hiG : 0 < i ∧ i < G.len := ⟨hi, by omega⟩
  rw [eraseAt_eq_erase G hiG]
  exact Flag.project_erase_of_le G _ (G.nth_mem' (by omega)) _ S (by
    rw [← hS]; exact G.nth_mono (by omega) (by have := G.card_eq_len_succ; omega))

theorem restrict_eraseAt_high (G : Flag F V) {i m : ℕ} (him : m < i) (hl : i < G.len)
    (R : Submodule F V) (hR : G.nth m = R) :
    (G.eraseAt i).restrict R = G.restrict R := by
  have hiG : 0 < i ∧ i < G.len := ⟨by omega, hl⟩
  rw [eraseAt_eq_erase G hiG]
  exact Flag.restrict_erase_of_ge G _ (G.nth_mem' (by omega)) _ R (by
    rw [← hR]; exact G.nth_mono (by omega) (by have := G.card_eq_len_succ; omega))

theorem project_eraseAt_high (G : Flag F V) {i m : ℕ} (him : m < i) (hl : i < G.len)
    (R : Submodule F V) (hR : G.nth m = R) :
    (G.eraseAt i).project R = (G.project R).eraseAt (i - m) := by
  have hiG : 0 < i ∧ i < G.len := ⟨by omega, hl⟩
  have hl1 : (G.eraseAt i).len = G.len - 1 := G.len_eraseAt hiG
  have hnm : (G.eraseAt i).nth m = R := by
    rw [G.nth_eraseAt hiG (by omega), if_pos him, hR]
  have hP : (G.project R).len = G.len - m := Flag.len_project_gen _ (by omega) R hR
  have hP' : ((G.eraseAt i).project R).len = G.len - 1 - m := by
    rw [Flag.len_project_gen _ (by omega) R hnm, hl1]
  have hiJ : 0 < i - m ∧ i - m < (G.project R).len := ⟨by omega, by omega⟩
  apply Flag.ext_nth (by rw [hP', (G.project R).len_eraseAt hiJ, hP]; omega)
  intro q hq
  rw [hP'] at hq
  rw [Flag.nth_project_gen _ (by omega) R hnm (by omega),
    (G.project R).nth_eraseAt hiJ (by omega),
    G.nth_eraseAt hiG (by omega)]
  by_cases hqi : q < i - m
  · rw [if_pos hqi, if_pos (by omega), Flag.nth_project_gen _ (by omega) R hR (by omega)]
  · rw [if_neg hqi, if_neg (by omega), Flag.nth_project_gen _ (by omega) R hR (by omega)]
    congr 2

end FlagIds

section Cup

/-- The pairing `(φ, ψ) ↦ mul' ∘ (φ ⊗ ψ) ∘ Δ_S`. -/
def cupPair (x : EBicomodCoalg F k) {V : FGModuleCat.{0} F} (S : Submodule F V)
    (φ : x.X.ev (sub S) →ₗ[k] k) (ψ : x.X.ev (quo S) →ₗ[k] k) : x.X.ev V →ₗ[k] k :=
  LinearMap.mul' k k ∘ₗ TensorProduct.map φ ψ ∘ₗ x.comul V S

theorem cupPair_add_left (x : EBicomodCoalg F k) {V : FGModuleCat.{0} F} (S : Submodule F V)
    (φ φ' : x.X.ev (sub S) →ₗ[k] k) (ψ : x.X.ev (quo S) →ₗ[k] k) :
    cupPair x S (φ + φ') ψ = cupPair x S φ ψ + cupPair x S φ' ψ := by
  unfold cupPair
  rw [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add]

theorem cupPair_add_right (x : EBicomodCoalg F k) {V : FGModuleCat.{0} F} (S : Submodule F V)
    (φ : x.X.ev (sub S) →ₗ[k] k) (ψ ψ' : x.X.ev (quo S) →ₗ[k] k) :
    cupPair x S φ (ψ + ψ') = cupPair x S φ ψ + cupPair x S φ ψ' := by
  unfold cupPair
  rw [TensorProduct.map_add_right, LinearMap.add_comp, LinearMap.comp_add]

theorem cupPair_smul_left (x : EBicomodCoalg F k) {V : FGModuleCat.{0} F} (S : Submodule F V)
    (c : k) (φ : x.X.ev (sub S) →ₗ[k] k) (ψ : x.X.ev (quo S) →ₗ[k] k) :
    cupPair x S (c • φ) ψ = c • cupPair x S φ ψ := by
  unfold cupPair
  rw [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul]

theorem cupPair_smul_right (x : EBicomodCoalg F k) {V : FGModuleCat.{0} F} (S : Submodule F V)
    (c : k) (φ : x.X.ev (sub S) →ₗ[k] k) (ψ : x.X.ev (quo S) →ₗ[k] k) :
    cupPair x S φ (c • ψ) = c • cupPair x S φ ψ := by
  unfold cupPair
  rw [TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul]

theorem cupPair_sum_left (x : EBicomodCoalg F k) {V : FGModuleCat.{0} F} (S : Submodule F V)
    {ι : Type*} (s : Finset ι) (φ : ι → x.X.ev (sub S) →ₗ[k] k) (ψ : x.X.ev (quo S) →ₗ[k] k) :
    cupPair x S (∑ i ∈ s, φ i) ψ = ∑ i ∈ s, cupPair x S (φ i) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    unfold cupPair
    simp [TensorProduct.map_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cupPair_add_left, ih]

theorem cupPair_sum_right (x : EBicomodCoalg F k) {V : FGModuleCat.{0} F} (S : Submodule F V)
    {ι : Type*} (s : Finset ι) (φ : x.X.ev (sub S) →ₗ[k] k) (ψ : ι → x.X.ev (quo S) →ₗ[k] k) :
    cupPair x S φ (∑ i ∈ s, ψ i) = ∑ i ∈ s, cupPair x S φ (ψ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    unfold cupPair
    simp [TensorProduct.map_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cupPair_add_right, ih]

theorem cupPair_zero_left (x : EBicomodCoalg F k) {V : FGModuleCat.{0} F} (S : Submodule F V)
    (ψ : x.X.ev (quo S) →ₗ[k] k) : cupPair x S 0 ψ = 0 := by
  unfold cupPair; simp [TensorProduct.map_zero_left]

theorem cupPair_zero_right (x : EBicomodCoalg F k) {V : FGModuleCat.{0} F} (S : Submodule F V)
    (φ : x.X.ev (sub S) →ₗ[k] k) : cupPair x S φ 0 = 0 := by
  unfold cupPair; simp [TensorProduct.map_zero_right]

/-- Rewriting the functionals along equivalences: `φ = φ' ∘ e₁`, `ψ = ψ' ∘ e₂`. -/
theorem cupPair_transport (x : EBicomodCoalg F k) {V : FGModuleCat.{0} F} (S : Submodule F V)
    {A' B' : Type} [AddCommGroup A'] [Module k A'] [AddCommGroup B'] [Module k B']
    (φ : x.X.ev (sub S) →ₗ[k] k) (ψ : x.X.ev (quo S) →ₗ[k] k)
    (e₁ : x.X.ev (sub S) →ₗ[k] A') (e₂ : x.X.ev (quo S) →ₗ[k] B')
    (φ' : A' →ₗ[k] k) (ψ' : B' →ₗ[k] k) (h₁ : φ = φ' ∘ₗ e₁) (h₂ : ψ = ψ' ∘ₗ e₂) (z : x.X.ev V) :
    cupPair x S φ ψ z =
      LinearMap.mul' k k (TensorProduct.map φ' ψ' (TensorProduct.map e₁ e₂ (x.comul V S z))) := by
  subst h₁ h₂
  unfold cupPair
  simp only [LinearMap.comp_apply]
  rw [← LinearMap.comp_apply (TensorProduct.map φ' ψ'), ← TensorProduct.map_comp]

/-- The `S`-term of the cup product at the flag `G`. -/
def cupTerm (x : EBicomodCoalg F k) (f g : RawCochain x.toEBicomod) {V : FGModuleCat.{0} F}
    (G : Flag F V) (S : Submodule F V) : x.X.ev V →ₗ[k] k :=
  cupPair x S (LinearMap.proj (G.restrict S) ∘ₗ f (sub S))
    (LinearMap.proj (G.project S) ∘ₗ g (quo S))

theorem cupRaw_apply (x : EBicomodCoalg F k) (m n : ℕ) (f g : RawCochain x.toEBicomod)
    {V : FGModuleCat.{0} F} (z : x.X.ev V) (H : Flag F V) (hH : H.len = m + n) :
    cupRaw x m n f g V z H = cupTerm x f g H (H.nth m) z := by
  simp only [cupRaw, LinearMap.pi_apply, if_pos hH]
  rfl

/-- `d` evaluated at a flag, as a map in `z`. -/
theorem dRaw_proj (x : EBicomod F k) (n : ℕ) (α : RawCochain x) (V : FGModuleCat.{0} F)
    (G : Flag F V) (hG : G.len = n + 1) :
    LinearMap.proj G ∘ₗ dRaw x n α V =
      (LinearMap.proj (G.project (G.nth 1)) ∘ₗ α (quo (G.nth 1)) ∘ₗ x.proj V (G.nth 1)) +
      faceSum _ G (α V) +
      ((-1 : k) ^ (n + 1)) • (LinearMap.proj (G.restrict (G.nth n)) ∘ₗ α (sub (G.nth n)) ∘ₗ
          x.res V (G.nth n)) := by
  apply LinearMap.ext
  intro z
  simp only [dRaw, LinearMap.pi_apply, if_pos hG, LinearMap.comp_apply, LinearMap.proj_apply]

/-- M1: the first outer face. -/
theorem term_first (x : EBicomodCoalg F k) {m n : ℕ} {f g : RawCochain x.toEBicomod}
    (hf : f ∈ cochains x.toEBicomod m) (hg : g ∈ cochains x.toEBicomod n)
    {V : FGModuleCat.{0} F} (G : Flag F V) (T S : Submodule F V) (hTS : T ≤ S)
    (S1 : Submodule F (quo T)) (hS1 : S1 = S.map T.mkQ)
    (T' : Submodule F (sub S)) (hT' : T' = T.comap S.subtype) (z : x.X.ev V) :
    cupTerm x f g (G.project T) S1 (x.proj V T z) =
      cupPair x S
        (LinearMap.proj ((G.restrict S).project T') ∘ₗ f (quo T') ∘ₗ x.proj (sub S) T')
        (LinearMap.proj (G.project S) ∘ₗ g (quo S)) z := by
  subst hS1 hT'
  unfold cupTerm cupPair
  have hax := LinearMap.congr_fun (x.comul_proj V T S hTS) z
  simp only [LinearMap.comp_apply] at hax ⊢
  rw [← hax, TensorProduct.map_map, TensorProduct.map_map]
  have hφ : ∀ w : x.X.ev (sub S),
      f (sub (V := quo T) (S.map T.mkQ)) (x.X.mapEquiv (V := quo (V := sub S) (T.comap S.subtype))
          (W := sub (V := quo T) (S.map T.mkQ)) (subQuotIso T S)
          (x.proj (sub S) (T.comap S.subtype) w)) ((G.project T).restrict (S.map T.mkQ)) =
      f (quo (V := sub S) (T.comap S.subtype)) (x.proj (sub S) (T.comap S.subtype) w)
        ((G.restrict S).project (T.comap S.subtype)) := by
    intro w
    rw [← Flag.project_restrict G T S hTS]
    exact hf.2 (quo (V := sub S) (T.comap S.subtype)) (sub (V := quo T) (S.map T.mkQ))
      (subQuotIso T S) _ _
  have hψ : ∀ u : x.X.ev (quo S),
      g (quo (V := quo T) (S.map T.mkQ)) (x.X.mapEquiv (V := quo S) (W := quo (V := quo T) (S.map T.mkQ))
          (T.quotientQuotientEquivQuotient S hTS).symm u) ((G.project T).project (S.map T.mkQ)) =
      g (quo S) u (G.project S) := by
    intro u
    rw [Flag.eq_map_symm (Flag.project_project G T S hTS)]
    exact hg.2 (quo S) (quo (V := quo T) (S.map T.mkQ))
      (T.quotientQuotientEquivQuotient S hTS).symm _ _
  congr 2
  apply congrArg₂ TensorProduct.map
  · apply LinearMap.ext
    intro w
    exact hφ w
  · apply LinearMap.ext
    intro u
    exact hψ u

/-- M2: a low face of the cup product. -/
theorem term_low (x : EBicomodCoalg F k) {m n : ℕ} (f g : RawCochain x.toEBicomod)
    {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = m + n + 1) {i : ℕ} (hi : 0 < i)
    (him : i ≤ m) (S : Submodule F V) (hS : G.nth (m + 1) = S) (z : x.X.ev V) :
    cupRaw x m n f g V z (G.eraseAt i) =
      cupPair x S (LinearMap.proj ((G.restrict S).eraseAt i) ∘ₗ f (sub S))
        (LinearMap.proj (G.project S) ∘ₗ g (quo S)) z := by
  have hiG : 0 < i ∧ i < G.len := ⟨hi, by omega⟩
  have hl1 : (G.eraseAt i).len = m + n := by rw [G.len_eraseAt hiG]; omega
  have hnm : (G.eraseAt i).nth m = S := by
    rw [G.nth_eraseAt hiG (by omega), if_neg (by omega), hS]
  rw [cupRaw_apply x m n f g z _ hl1, hnm]
  unfold cupTerm
  rw [restrict_eraseAt_low G hi him (by omega) S hS, project_eraseAt_low G hi him (by omega) S hS]

/-- M3: a high face of the cup product. -/
theorem term_high (x : EBicomodCoalg F k) {m n : ℕ} (f g : RawCochain x.toEBicomod)
    {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = m + n + 1) {i : ℕ} (him : m < i)
    (hin : i ≤ m + n) (R : Submodule F V) (hR : G.nth m = R) (z : x.X.ev V) :
    cupRaw x m n f g V z (G.eraseAt i) =
      cupPair x R (LinearMap.proj (G.restrict R) ∘ₗ f (sub R))
        (LinearMap.proj ((G.project R).eraseAt (i - m)) ∘ₗ g (quo R)) z := by
  have hiG : 0 < i ∧ i < G.len := ⟨by omega, by omega⟩
  have hl1 : (G.eraseAt i).len = m + n := by rw [G.len_eraseAt hiG]; omega
  have hnm : (G.eraseAt i).nth m = R := by
    rw [G.nth_eraseAt hiG (by omega), if_pos him, hR]
  rw [cupRaw_apply x m n f g z _ hl1, hnm]
  unfold cupTerm
  rw [restrict_eraseAt_high G him hiG.2 R hR, project_eraseAt_high G him hiG.2 R hR]

/-- M4: the last outer face. -/
theorem term_last (x : EBicomodCoalg F k) {m n : ℕ} {f g : RawCochain x.toEBicomod}
    (hf : f ∈ cochains x.toEBicomod m) (hg : g ∈ cochains x.toEBicomod n)
    {V : FGModuleCat.{0} F} (G : Flag F V) (R U : Submodule F V) (hRU : R ≤ U)
    (R' : Submodule F (sub U)) (hR' : R' = R.comap U.subtype)
    (U1 : Submodule F (quo R)) (hU1 : U1 = U.map R.mkQ) (z : x.X.ev V) :
    cupTerm x f g (G.restrict U) R' (x.res V U z) =
      cupPair x R (LinearMap.proj (G.restrict R) ∘ₗ f (sub R))
        (LinearMap.proj ((G.project R).restrict U1) ∘ₗ
          g (sub (V := quo R) U1) ∘ₗ x.res (quo R) U1) z := by
  subst hR' hU1
  unfold cupTerm cupPair
  have hax := LinearMap.congr_fun (x.comul_res V R U hRU) z
  simp only [LinearMap.comp_apply] at hax ⊢
  have hφ : ∀ w : x.X.ev (sub (V := sub U) (R.comap U.subtype)),
      f (sub (V := sub U) (R.comap U.subtype)) w ((G.restrict U).restrict (R.comap U.subtype)) =
      f (sub R) (x.X.mapEquiv (V := sub (V := sub U) (R.comap U.subtype)) (W := sub R)
        (Submodule.comapSubtypeEquivOfLe hRU) w) (G.restrict R) := by
    intro w
    rw [← Flag.restrict_restrict G R U hRU]
    exact (hf.2 (sub (V := sub U) (R.comap U.subtype)) (sub R)
      (Submodule.comapSubtypeEquivOfLe hRU) w _).symm
  have hψ : ∀ u : x.X.ev (quo (V := sub U) (R.comap U.subtype)),
      g (quo (V := sub U) (R.comap U.subtype)) u ((G.restrict U).project (R.comap U.subtype)) =
      g (sub (V := quo R) (U.map R.mkQ)) (x.X.mapEquiv (V := quo (V := sub U) (R.comap U.subtype))
        (W := sub (V := quo R) (U.map R.mkQ)) (subQuotIso R U) u)
        ((G.project R).restrict (U.map R.mkQ)) := by
    intro u
    rw [← Flag.project_restrict G R U hRU]
    exact (hg.2 (quo (V := sub U) (R.comap U.subtype)) (sub (V := quo R) (U.map R.mkQ))
      (subQuotIso R U) u _).symm
  have key : TensorProduct.map
      (LinearMap.proj ((G.restrict U).restrict (R.comap U.subtype)) ∘ₗ
        f (sub (V := sub U) (R.comap U.subtype)))
      (LinearMap.proj ((G.restrict U).project (R.comap U.subtype)) ∘ₗ
        g (quo (V := sub U) (R.comap U.subtype))) =
      TensorProduct.map (LinearMap.proj (G.restrict R) ∘ₗ f (sub R))
        (LinearMap.proj ((G.project R).restrict (U.map R.mkQ)) ∘ₗ
          g (sub (V := quo R) (U.map R.mkQ))) ∘ₗ
      TensorProduct.map (x.X.mapEquiv (V := sub (V := sub U) (R.comap U.subtype)) (W := sub R)
          (Submodule.comapSubtypeEquivOfLe hRU))
        (x.X.mapEquiv (V := quo (V := sub U) (R.comap U.subtype))
          (W := sub (V := quo R) (U.map R.mkQ)) (subQuotIso R U)) := by
    rw [← TensorProduct.map_comp]
    congr 1
    · apply LinearMap.ext; intro w; exact hφ w
    · apply LinearMap.ext; intro u; exact hψ u
  rw [key, LinearMap.comp_apply, hax, TensorProduct.map_map]
  rfl

/-- M5: the middle cancellation, via `comul_res_proj`. -/
theorem term_mid (x : EBicomodCoalg F k) {m n : ℕ} {f g : RawCochain x.toEBicomod}
    (hf : f ∈ cochains x.toEBicomod m) (hg : g ∈ cochains x.toEBicomod n)
    {V : FGModuleCat.{0} F} (G : Flag F V) (R S : Submodule F V) (hRS : R ≤ S)
    (R' : Submodule F (sub S)) (hR' : R' = R.comap S.subtype)
    (S1 : Submodule F (quo R)) (hS1 : S1 = S.map R.mkQ) (z : x.X.ev V) :
    cupPair x S
      (LinearMap.proj ((G.restrict S).restrict R') ∘ₗ
        f (sub (V := sub S) R') ∘ₗ x.res (sub S) R')
      (LinearMap.proj (G.project S) ∘ₗ g (quo S)) z =
    cupPair x R (LinearMap.proj (G.restrict R) ∘ₗ f (sub R))
      (LinearMap.proj ((G.project R).project S1) ∘ₗ
        g (quo (V := quo R) S1) ∘ₗ x.proj (quo R) S1) z := by
  subst hR' hS1
  unfold cupPair
  have hax := LinearMap.congr_fun (x.comul_res_proj V R S hRS) z
  simp only [LinearMap.comp_apply] at hax ⊢
  have hφ : ∀ w : x.X.ev (sub (V := sub S) (R.comap S.subtype)),
      f (sub (V := sub S) (R.comap S.subtype)) w ((G.restrict S).restrict (R.comap S.subtype)) =
      f (sub R) (x.X.mapEquiv (V := sub (V := sub S) (R.comap S.subtype)) (W := sub R)
        (Submodule.comapSubtypeEquivOfLe hRS) w) (G.restrict R) := by
    intro w
    rw [← Flag.restrict_restrict G R S hRS]
    exact (hf.2 (sub (V := sub S) (R.comap S.subtype)) (sub R)
      (Submodule.comapSubtypeEquivOfLe hRS) w _).symm
  have hψ : ∀ v : x.X.ev (quo (V := quo R) (S.map R.mkQ)),
      g (quo S) (x.X.mapEquiv (V := quo (V := quo R) (S.map R.mkQ)) (W := quo S)
          (Submodule.quotientQuotientEquivQuotient R S hRS) v) (G.project S) =
      g (quo (V := quo R) (S.map R.mkQ)) v ((G.project R).project (S.map R.mkQ)) := by
    intro v
    rw [← Flag.project_project G R S hRS]
    exact hg.2 (quo (V := quo R) (S.map R.mkQ)) (quo S)
      (Submodule.quotientQuotientEquivQuotient R S hRS) v _
  have key1 : TensorProduct.map
      (LinearMap.proj ((G.restrict S).restrict (R.comap S.subtype)) ∘ₗ
        f (sub (V := sub S) (R.comap S.subtype)) ∘ₗ x.res (sub S) (R.comap S.subtype))
      (LinearMap.proj (G.project S) ∘ₗ g (quo S)) =
      TensorProduct.map (LinearMap.proj (G.restrict R) ∘ₗ f (sub R))
        (LinearMap.proj (G.project S) ∘ₗ g (quo S)) ∘ₗ
      TensorProduct.map (x.X.mapEquiv (V := sub (V := sub S) (R.comap S.subtype)) (W := sub R)
          (Submodule.comapSubtypeEquivOfLe hRS)) LinearMap.id ∘ₗ
      TensorProduct.map (x.res (sub S) (R.comap S.subtype)) LinearMap.id := by
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
    congr 1
    apply LinearMap.ext; intro w; simp only [LinearMap.comp_apply, LinearMap.proj_apply]; exact hφ _
  have key2 : TensorProduct.map (LinearMap.proj (G.restrict R) ∘ₗ f (sub R))
        (LinearMap.proj (G.project S) ∘ₗ g (quo S)) ∘ₗ
      TensorProduct.map LinearMap.id (x.X.mapEquiv (V := quo (V := quo R) (S.map R.mkQ))
          (W := quo S) (Submodule.quotientQuotientEquivQuotient R S hRS)) =
      TensorProduct.map (LinearMap.proj (G.restrict R) ∘ₗ f (sub R))
        (LinearMap.proj ((G.project R).project (S.map R.mkQ)) ∘ₗ
          g (quo (V := quo R) (S.map R.mkQ))) := by
    rw [← TensorProduct.map_comp]
    congr 1
    apply LinearMap.ext; intro v; simp only [LinearMap.comp_apply, LinearMap.proj_apply]; exact hψ v
  rw [key1, LinearMap.comp_apply, LinearMap.comp_apply, hax]
  have := LinearMap.congr_fun key2
    (TensorProduct.map LinearMap.id (x.proj (quo R) (S.map R.mkQ)) (x.comul V R z))
  simp only [LinearMap.comp_apply] at this
  rw [this]
  simp only [TensorProduct.map_map]
  rfl

end Cup


theorem sum_mid {M : Type*} [AddCommMonoid M] (L : ℕ) (φ : ℕ → M) :
    ∑ i ∈ Finset.range (L + 1), (if 0 < i ∧ i < L then φ i else 0) =
      ∑ j ∈ Finset.range (L - 1), φ (j + 1) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  obtain ⟨a, rfl⟩ : ∃ a, L = a + 1 := ⟨L - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel]
  have h1 : ¬ (0 < 0 ∧ 0 < a + 1) := by omega
  have h2 : ¬ (0 < a + 1 ∧ a + 1 < a + 1) := by omega
  rw [if_neg h1, if_neg h2, add_zero, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [if_pos]
  simp at hi
  omega


theorem faceSum_eq_sum {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X]
    (G : Flag F V) (γ : X →ₗ[k] (Flag F V → k)) :
    faceSum X G γ = ∑ j ∈ Finset.range (G.len - 1),
      ((-1 : k) ^ (j + 1)) • (LinearMap.proj (G.eraseAt (j + 1)) ∘ₗ γ) := by
  rw [faceSum_eq_range]
  have : ∀ i, (if h : 0 < i ∧ i < G.len then
        ((-1 : k) ^ i) • (LinearMap.proj (G.eraseAt i) ∘ₗ γ) else 0) =
      if 0 < i ∧ i < G.len then ((-1 : k) ^ i) • (LinearMap.proj (G.eraseAt i) ∘ₗ γ) else 0 := by
    intro i; exact dite_eq_ite
  simp only [this]
  exact sum_mid (G.len) (fun i => ((-1 : k) ^ i) • (LinearMap.proj (G.eraseAt i) ∘ₗ γ))

theorem faceSum_apply_range {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X]
    (G : Flag F V) (γ : X →ₗ[k] (Flag F V → k)) (z : X) :
    faceSum X G γ z = ∑ j ∈ Finset.range (G.len - 1), (-1 : k) ^ (j + 1) * γ z (G.eraseAt (j + 1)) := by
  rw [faceSum_eq_sum, LinearMap.sum_apply]
  simp

theorem expand_left (x : EBicomodCoalg F k) {m : ℕ} (f g : RawCochain x.toEBicomod)
    {V : FGModuleCat.{0} F} (G : Flag F V) (S : Submodule F V)
    (hK : (G.restrict S).len = m + 1) (z : x.X.ev V) :
    cupTerm x (dRaw x.toEBicomod m f) g G S z =
      cupPair x S
        (LinearMap.proj ((G.restrict S).project ((G.restrict S).nth 1)) ∘ₗ
          f (quo (V := sub S) ((G.restrict S).nth 1)) ∘ₗ x.proj (sub S) ((G.restrict S).nth 1))
        (LinearMap.proj (G.project S) ∘ₗ g (quo S)) z +
      ∑ j ∈ Finset.range m, (-1 : k) ^ (j + 1) * cupPair x S
        (LinearMap.proj ((G.restrict S).eraseAt (j + 1)) ∘ₗ f (sub S))
        (LinearMap.proj (G.project S) ∘ₗ g (quo S)) z +
      (-1 : k) ^ (m + 1) * cupPair x S
        (LinearMap.proj ((G.restrict S).restrict ((G.restrict S).nth m)) ∘ₗ
          f (sub (V := sub S) ((G.restrict S).nth m)) ∘ₗ x.res (sub S) ((G.restrict S).nth m))
        (LinearMap.proj (G.project S) ∘ₗ g (quo S)) z := by
  unfold cupTerm
  rw [dRaw_proj x.toEBicomod m f (sub S) _ hK, faceSum_eq_sum, hK, Nat.add_sub_cancel,
    cupPair_add_left, cupPair_add_left, cupPair_smul_left, cupPair_sum_left]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    cupPair_smul_left]

theorem expand_right (x : EBicomodCoalg F k) {n : ℕ} (f g : RawCochain x.toEBicomod)
    {V : FGModuleCat.{0} F} (G : Flag F V) (R : Submodule F V)
    (hJ : (G.project R).len = n + 1) (z : x.X.ev V) :
    cupTerm x f (dRaw x.toEBicomod n g) G R z =
      cupPair x R (LinearMap.proj (G.restrict R) ∘ₗ f (sub R))
        (LinearMap.proj ((G.project R).project ((G.project R).nth 1)) ∘ₗ
          g (quo (V := quo R) ((G.project R).nth 1)) ∘ₗ x.proj (quo R) ((G.project R).nth 1)) z +
      ∑ j ∈ Finset.range n, (-1 : k) ^ (j + 1) * cupPair x R
        (LinearMap.proj (G.restrict R) ∘ₗ f (sub R))
        (LinearMap.proj ((G.project R).eraseAt (j + 1)) ∘ₗ g (quo R)) z +
      (-1 : k) ^ (n + 1) * cupPair x R (LinearMap.proj (G.restrict R) ∘ₗ f (sub R))
        (LinearMap.proj ((G.project R).restrict ((G.project R).nth n)) ∘ₗ
          g (sub (V := quo R) ((G.project R).nth n)) ∘ₗ x.res (quo R) ((G.project R).nth n)) z := by
  unfold cupTerm
  rw [dRaw_proj x.toEBicomod n g (quo R) _ hJ, faceSum_eq_sum, hJ, Nat.add_sub_cancel,
    cupPair_add_right, cupPair_add_right, cupPair_smul_right, cupPair_sum_right]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    cupPair_smul_right]

set_option maxHeartbeats 800000 in
theorem dRaw_cupRaw_pos (x : EBicomodCoalg F k) {m n : ℕ} {f g : RawCochain x.toEBicomod}
    (hf : f ∈ cochains x.toEBicomod m) (hg : g ∈ cochains x.toEBicomod n)
    (V : FGModuleCat.{0} F) (z : x.X.ev V) (G : Flag F V) (hG : G.len = m + n + 1) :
    dRaw x.toEBicomod (m + n) (cupRaw x m n f g) V z G =
      cupRaw x (m + 1) n (dRaw x.toEBicomod m f) g V z G +
        (-1 : k) ^ m * cupRaw x m (n + 1) f (dRaw x.toEBicomod n g) V z G := by
  have hcard := G.card_eq_len_succ
  have hRS : G.nth m ≤ G.nth (m + 1) := (G.nth_lt_nth (Nat.lt_succ_self m) (by omega)).le
  have hTS : G.nth 1 ≤ G.nth (m + 1) := G.nth_mono (by omega) (by omega)
  have hRU : G.nth m ≤ G.nth (m + n) := G.nth_mono (by omega) (by omega)
  -- the left-hand side
  have hL := LinearMap.congr_fun (dRaw_proj x.toEBicomod (m + n) (cupRaw x m n f g) V G hG) z
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul] at hL
  rw [show dRaw x.toEBicomod (m + n) (cupRaw x m n f g) V z G = _ from hL]
  -- lengths and members of the derived flags
  have hKlen : (G.restrict (G.nth (m + 1))).len = m + 1 :=
    Flag.len_restrict_gen G (p := m + 1) (by omega) _ rfl
  have hK1 : (G.restrict (G.nth (m + 1))).nth 1 = (G.nth 1).comap (G.nth (m + 1)).subtype :=
    Flag.nth_restrict_gen G (p := m + 1) (by omega) _ rfl (q := 1) (by omega)
  have hKm : (G.restrict (G.nth (m + 1))).nth m = (G.nth m).comap (G.nth (m + 1)).subtype :=
    Flag.nth_restrict_gen G (p := m + 1) (by omega) _ rfl (q := m) (by omega)
  have hJlen : (G.project (G.nth m)).len = n + 1 := by
    rw [Flag.len_project_gen G (p := m) (by omega) _ rfl]; omega
  have hJ1 : (G.project (G.nth m)).nth 1 = (G.nth (m + 1)).map (G.nth m).mkQ := by
    rw [Flag.nth_project_gen G (p := m) (by omega) _ rfl (q := 1) (by omega)]
  have hJn : (G.project (G.nth m)).nth n = (G.nth (m + n)).map (G.nth m).mkQ := by
    rw [Flag.nth_project_gen G (p := m) (by omega) _ rfl (q := n) (by omega)]
  have hH1len : (G.project (G.nth 1)).len = m + n := by
    rw [Flag.len_project_gen G (p := 1) (by omega) _ rfl]; omega
  have hH1m : (G.project (G.nth 1)).nth m = (G.nth (m + 1)).map (G.nth 1).mkQ := by
    rw [Flag.nth_project_gen G (p := 1) (by omega) _ rfl (q := m) (by omega), add_comm]
  have hH2len : (G.restrict (G.nth (m + n))).len = m + n :=
    Flag.len_restrict_gen G (p := m + n) (by omega) _ rfl
  have hH2m : (G.restrict (G.nth (m + n))).nth m = (G.nth m).comap (G.nth (m + n)).subtype :=
    Flag.nth_restrict_gen G (p := m + n) (by omega) _ rfl (q := m) (by omega)
  -- the first outer face
  have hA := term_first x hf hg G (G.nth 1) (G.nth (m + 1)) hTS _ hH1m _ hK1 z
  rw [← cupRaw_apply x m n f g _ _ hH1len] at hA
  -- the last outer face
  have hC := term_last x hf hg G (G.nth m) (G.nth (m + n)) hRU _ hH2m _ hJn z
  rw [← cupRaw_apply x m n f g _ _ hH2len] at hC
  -- the middle faces
  have hB := faceSum_apply_range _ G (cupRaw x m n f g V) z
  rw [hG, show m + n + 1 - 1 = m + n by omega, Finset.sum_range_add] at hB
  have hBlow : ∀ j ∈ Finset.range m, (-1 : k) ^ (j + 1) * cupRaw x m n f g V z (G.eraseAt (j + 1)) =
      (-1 : k) ^ (j + 1) * cupPair x (G.nth (m + 1))
        (LinearMap.proj ((G.restrict (G.nth (m + 1))).eraseAt (j + 1)) ∘ₗ f (sub (G.nth (m + 1))))
        (LinearMap.proj (G.project (G.nth (m + 1))) ∘ₗ g (quo (G.nth (m + 1)))) z := by
    intro j hj
    rw [term_low x f g G hG (i := j + 1) (by omega) (by simp at hj; omega) _ rfl z]
  have hBhigh : ∀ j ∈ Finset.range n,
      (-1 : k) ^ (m + j + 1) * cupRaw x m n f g V z (G.eraseAt (m + j + 1)) =
      (-1 : k) ^ m * ((-1 : k) ^ (j + 1) * cupPair x (G.nth m)
        (LinearMap.proj (G.restrict (G.nth m)) ∘ₗ f (sub (G.nth m)))
        (LinearMap.proj ((G.project (G.nth m)).eraseAt (j + 1)) ∘ₗ g (quo (G.nth m))) z) := by
    intro j hj
    rw [term_high x f g G hG (i := m + j + 1) (by omega) (by simp at hj; omega) _ rfl z,
      show m + j + 1 - m = j + 1 by omega, pow_add, pow_add]
    ring
  rw [Finset.sum_congr rfl hBlow, Finset.sum_congr rfl hBhigh, ← Finset.mul_sum] at hB
  have hR1 := expand_left x f g G (G.nth (m + 1)) hKlen z
  have hR2 := expand_right x f g G (G.nth m) hJlen z
  have hM := term_mid x hf hg G (G.nth m) (G.nth (m + 1)) hRS _ hKm _ hJ1 z
  rw [cupRaw_apply x (m + 1) n _ g z G (by omega), cupRaw_apply x m (n + 1) f _ z G (by omega),
    hR1, hR2, hM, hA, hC, hB]
  ring


/-- The cup product is compatible with the differential (Leibniz rule), so `H•(x)` is an
algebra; it is graded-commutative by [SA04].

**Gap (missing hypothesis, §1.4).** The Leibniz rule requires that `x` is a coalgebra in
`e`-bicomodules, i.e. that comultiplication commutes with `res` and `proj`. The thesis states
this without proof. We add the needed compatibilities as the axioms `comul_proj`, `comul_res`
and `comul_res_proj` of `EBicomodCoalg` (§1.3); they hold for `flagCoalg` and
`completeFlagCoalg`. -/
theorem dRaw_cupRaw (x : EBicomodCoalg F k) (m n : ℕ) (f g : RawCochain x.toEBicomod)
    (hf : f ∈ cochains x.toEBicomod m) (hg : g ∈ cochains x.toEBicomod n) :
    dRaw x.toEBicomod (m + n) (cupRaw x m n f g) =
      cupRaw x (m + 1) n (dRaw x.toEBicomod m f) g +
        ((-1 : k) ^ m) • cupRaw x m (n + 1) f (dRaw x.toEBicomod n g) := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  by_cases hG : G.len = m + n + 1
  · exact dRaw_cupRaw_pos x hf hg V z G hG
  · have h1 : ¬ G.len = m + n + 1 := hG
    have h2 : ¬ G.len = m + 1 + n := by omega
    have h3 : ¬ G.len = m + (n + 1) := by omega
    simp [dRaw, cupRaw, h1, h2, h3]

end MartinPhd

end
end Leibniz
