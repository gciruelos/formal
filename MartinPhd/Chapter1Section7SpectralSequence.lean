import Mathlib
import MartinPhd.Chapter1Section6FlagVarieties

/-!
# Chapter 1, Section 1.7 (a spectral sequence: E1 page)

Contents:
* Chapter1Section7
* E1
* Faces
* Lift
* Hom
* Lemma 1.25: the `E₁` page for relatively projective species
-/

section Chapter1Section7

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §1.7 Una sucesión espectral -/

section SpectralSequence

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

/-- The decreasing filtration `F^p Cⁿ(x) = {α : α(V) = 0 whenever dim V < p}`
(`p ∈ ℤ`; it is everything for `p ≤ 0`). -/
def filt (x : EBicomod F k) (p : ℤ) (n : ℕ) : Submodule k (RawCochain x) :=
  cochains x n ⊓ ⨅ (V : FGModuleCat.{0} F) (_ : (finrank F V : ℤ) < p),
    LinearMap.ker (LinearMap.proj (R := k) (φ := fun V : FGModuleCat.{0} F =>
      x.X.ev V →ₗ[k] (Flag F V → k)) V)

theorem mem_filt_iff (x : EBicomod F k) (p : ℤ) (n : ℕ) (α : RawCochain x) :
    α ∈ filt x p n ↔ α ∈ cochains x n ∧ ∀ V : FGModuleCat.{0} F, (finrank F V : ℤ) < p → α V = 0 := by
  unfold filt
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]

theorem dMidRaw_mem (x : EBicomod F k) {n : ℕ} {α : RawCochain x} (hα : α ∈ cochains x n) :
    dMidRaw x n α ∈ cochains x (n + 1) := by
  refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
  · show dMidRaw x n α V z G = 0
    simp [dMidRaw, hG]
  · show dMidRaw x n α W (x.X.mapEquiv e z) (G.map e) = dMidRaw x n α V z G
    by_cases hG : G.len = n + 1
    · have hG' : (G.map e).len = n + 1 := by rw [Flag.len_map]; exact hG
      simp only [dMidRaw, LinearMap.pi_apply, if_pos hG, if_pos hG']
      exact faceSum_nat x hα e z G
    · have hG' : ¬ (G.map e).len = n + 1 := by rwa [Flag.len_map]
      simp [dMidRaw, hG, hG']

/-- Dimension bounds for the outer faces of a flag of length `n + 1`. -/
theorem outer_face_dims {V : FGModuleCat.{0} F} (G : Flag F V) {n : ℕ} (hG : G.len = n + 1) :
    finrank F (V ⧸ G.nth 1) < finrank F V ∧ finrank F (G.nth n) < finrank F V := by
  have hcard : G.carrier.card = n + 2 := by rw [G.card_eq_len_succ, hG]
  have h1 : G.nth 1 ≠ ⊥ := by
    have := G.nth_lt_nth (Nat.zero_lt_one) (by omega)
    rw [G.nth_zero] at this
    exact this.ne'
  have hn : G.nth n ≠ ⊤ := by
    have := G.nth_lt_nth (by omega : n < n + 1) (by omega)
    rw [show n + 1 = G.len by omega, G.nth_len] at this
    exact this.ne
  refine ⟨?_, Submodule.finrank_lt hn⟩
  have hq := (G.nth 1).finrank_quotient_add_finrank
  have hpos : 0 < finrank F (G.nth 1) := by
    have := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 h1)
    simpa using this
  omega

/-- `d` preserves the filtration, and the outer cofaces `∂⁰, ∂ⁿ⁺¹` raise it by one. -/
theorem d_filt (x : EBicomod F k) (p : ℤ) (n : ℕ) {α : RawCochain x} (hα : α ∈ filt x p n) :
    d x n α ∈ filt x p (n + 1) ∧ d x n α - dMidRaw x n α ∈ filt x (p + 1) (n + 1) := by
  obtain ⟨hαc, hαV⟩ := (mem_filt_iff x p n α).1 hα
  constructor
  · rw [mem_filt_iff]
    refine ⟨d_mem x hαc, fun V hV => ?_⟩
    apply LinearMap.ext
    intro z
    funext G
    show dRaw x n α V z G = 0
    simp only [dRaw, LinearMap.pi_apply]
    by_cases hG : G.len = n + 1
    · rw [if_pos hG]
      obtain ⟨h1, h2⟩ := outer_face_dims G hG
      have hq : α (quo (G.nth 1)) = 0 := hαV _ (by
        have : finrank F (V ⧸ G.nth 1) ≤ finrank F V := h1.le
        exact lt_of_le_of_lt (by exact_mod_cast this) hV)
      have hs : α (sub (G.nth n)) = 0 := hαV _ (by
        exact lt_of_le_of_lt (by exact_mod_cast h2.le) hV)
      have hv : α V = 0 := hαV V hV
      simp [hq, hs, hv, faceSum]
    · rw [if_neg hG]; rfl
  · rw [mem_filt_iff]
    refine ⟨(Submodule.sub_mem _ (d_mem x hαc) (dMidRaw_mem x hαc)), fun V hV => ?_⟩
    apply LinearMap.ext
    intro z
    funext G
    show dRaw x n α V z G - dMidRaw x n α V z G = 0
    simp only [dRaw, dMidRaw, LinearMap.pi_apply]
    by_cases hG : G.len = n + 1
    · rw [if_pos hG, if_pos hG]
      obtain ⟨h1, h2⟩ := outer_face_dims G hG
      have hq : α (quo (G.nth 1)) = 0 := hαV _ (by
        have : finrank F (V ⧸ G.nth 1) + 1 ≤ finrank F V := h1
        have hV' : (finrank F V : ℤ) < p + 1 := hV
        have : (finrank F (V ⧸ G.nth 1) : ℤ) + 1 ≤ finrank F V := by exact_mod_cast this
        show (finrank F (V ⧸ G.nth 1) : ℤ) < p
        omega)
      have hs : α (sub (G.nth n)) = 0 := hαV _ (by
        have : finrank F (G.nth n) + 1 ≤ finrank F V := h2
        have hV' : (finrank F V : ℤ) < p + 1 := hV
        have : (finrank F (G.nth n) : ℤ) + 1 ≤ finrank F V := by exact_mod_cast this
        show (finrank F (G.nth n) : ℤ) < p
        omega)
      simp [hq, hs]
    · rw [if_neg hG, if_neg hG]; simp

/-- `Z_s^{p}(n) = F^p Cⁿ ∩ d⁻¹(F^{p+s} Cⁿ⁺¹)`. -/
def Zpage (x : EBicomod F k) (s p : ℤ) (n : ℕ) : Submodule k (RawCochain x) :=
  filt x p n ⊓ (filt x (p + s) (n + 1)).comap (d x n)

/-- `B_r^{p}(n) = d(Z_{r-1}^{p-r+1}(n-1)) + Z_{r-1}^{p+1}(n)`. -/
def Bpage (x : EBicomod F k) (r : ℕ) (p : ℤ) : ℕ → Submodule k (RawCochain x)
  | 0 => Zpage x ((r : ℤ) - 1) (p + 1) 0
  | n + 1 => (Zpage x ((r : ℤ) - 1) (p - r + 1) n).map (d x n) ⊔ Zpage x ((r : ℤ) - 1) (p + 1) (n + 1)

/-- The page `E_r^{p,q}(x) = Z_r^p / B_r^p` of the spectral sequence of the filtered cobar
complex, in total degree `n = p + q`. So `E₀^{p,q} = F^p C^{p+q} / F^{p+1} C^{p+q}`. The
sequence lives in the fourth quadrant: `E₀^{p,q} = 0` unless `-p ≤ q ≤ 0`. -/
abbrev E (x : EBicomod F k) (r : ℕ) (p : ℤ) (n : ℕ) := Subquot (Zpage x r p n) (Bpage x r p n)

/-- The differential `d_r : E_r^{p,q} → E_r^{p+r, q-r+1}`, induced by `d`. -/
theorem Zpage_le_cochains (x : EBicomod F k) (s p : ℤ) (n : ℕ) {α : RawCochain x}
    (hα : α ∈ Zpage x s p n) : α ∈ cochains x n :=
  ((mem_filt_iff x p n α).1 hα.1).1

theorem dPage_hA (x : EBicomod F k) (r : ℕ) (p : ℤ) (n : ℕ) :
    Zpage x r p n ≤ (Zpage x r (p + r) (n + 1)).comap (d x n) := by
  intro α hα
  refine ⟨hα.2, ?_⟩
  show d x (n + 1) (d x n α) ∈ filt x _ (n + 1 + 1)
  rw [d_comp_d x n (Zpage_le_cochains x _ _ _ hα)]
  exact Submodule.zero_mem _

theorem dPage_hB (x : EBicomod F k) (r : ℕ) (p : ℤ) (n : ℕ) :
    Bpage x r p n ⊓ Zpage x r p n ≤ (Bpage x r (p + r) (n + 1)).comap (d x n) := by
  have hI : p + (r : ℤ) - r + 1 = p + 1 := by ring
  rintro α ⟨hB, -⟩
  show d x n α ∈ Bpage x r (p + r) (n + 1)
  simp only [Bpage]
  rw [hI]
  cases n with
  | zero =>
    simp only [Bpage] at hB
    exact Submodule.mem_sup_left ⟨α, hB, rfl⟩
  | succ n =>
    simp only [Bpage] at hB
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hB
    obtain ⟨β, hβ, rfl⟩ := ha
    rw [map_add, d_comp_d x n (Zpage_le_cochains x _ _ _ hβ), zero_add]
    exact Submodule.mem_sup_left ⟨c, hc, rfl⟩

def dPage (x : EBicomod F k) (r : ℕ) (p : ℤ) (n : ℕ) : E x r p n →ₗ[k] E x r (p + r) (n + 1) :=
  Subquot.map (d x n) (dPage_hA x r p n) (dPage_hB x r p n)

/-- The induced filtration `F^p Hⁿ(x)`: classes with a representative in `F^p Cⁿ(x)`. -/
def filtH (x : EBicomod F k) (p : ℤ) (n : ℕ) : Submodule k (H x n) :=
  ((filt x p n).comap (cocycles x n).subtype).map (Submodule.mkQ _)

/-- `α ↦ α ∘ π_p : Cⁿ(x_p) → F^p Cⁿ(x)` (with `x_p` the trivial bicomodule). -/
def precompTrunc (x : EBicomod F k) (p : ℕ) :
    RawCochain (EBicomod.trivial (x.X.trunc p)) →ₗ[k] RawCochain x where
  toFun α V := α V ∘ₗ ((x.X.truncπ p).app ⟨V⟩).hom
  map_add' := by intro α β; funext V; exact LinearMap.add_comp _ _ _
  map_smul' := by intro r α; funext V; exact LinearMap.smul_comp _ _ _

theorem precompTrunc_mem (x : EBicomod F k) (p n : ℕ) {α : RawCochain (EBicomod.trivial (x.X.trunc p))}
    (hα : α ∈ cochains _ n) : precompTrunc x p α ∈ Zpage x 0 p n := by
  have hπ0 : ∀ (V : FGModuleCat.{0} F), finrank F V ≠ p → ((x.X.truncπ p).app ⟨V⟩).hom = 0 := by
    intro V hV
    show (ModuleCat.ofHom (if h : finrank F V = p then _ else 0)).hom = 0
    rw [dif_neg hV]; rfl
  have hvan : ∀ (W : FGModuleCat.{0} F), (finrank F W : ℤ) < p → precompTrunc x p α W = 0 := by
    intro W hW
    apply LinearMap.ext
    intro v
    show α W (((x.X.truncπ p).app ⟨W⟩).hom v) = 0
    rw [LinearMap.congr_fun (hπ0 W (by omega)) v]
    exact map_zero (α W)
  have hc : precompTrunc x p α ∈ cochains x n := by
    refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
    · exact hα.1 V _ G hG
    · have h1 := LinearMap.congr_fun (GLSpecies.mapEquiv_naturality (x.X.truncπ p) e) z
      simp only [LinearMap.comp_apply] at h1
      show α W (((x.X.truncπ p).app ⟨W⟩).hom (x.X.mapEquiv e z)) (G.map e) =
        α V (((x.X.truncπ p).app ⟨V⟩).hom z) G
      rw [h1]
      exact hα.2 V W e _ G
  have hd : d x n (precompTrunc x p α) ∈ filt x (p + (0 : ℕ)) (n + 1) := by
    rw [mem_filt_iff]
    refine ⟨d_mem x hc, fun V hV => ?_⟩
    have hV' : (finrank F V : ℤ) < p := by simpa using hV
    have hq : ∀ (U : FGModuleCat.{0} F), finrank F U < finrank F V →
        precompTrunc x p α U = 0 := fun U hU => hvan U (by omega)
    apply LinearMap.ext
    intro z
    funext G
    show dRaw x n _ V z G = 0
    simp only [dRaw, LinearMap.pi_apply]
    by_cases hG : G.len = n + 1
    · rw [if_pos hG]
      obtain ⟨h1, h2⟩ := outer_face_dims G hG
      have e1 := hq (quo (G.nth 1)) h1
      have e2 := hq (sub (G.nth n)) h2
      have e3 : faceSum _ G (precompTrunc x p α V) = 0 := by
        rw [hvan V hV']; unfold faceSum; simp
      simp [e1, e2, e3]
    · rw [if_neg hG]; rfl
  exact ⟨(mem_filt_iff x p n _).2 ⟨hc, hvan⟩, by simpa using hd⟩

theorem dTriv_eq (y : GLSpecies F k) (n : ℕ) (α : RawCochain (EBicomod.trivial y)) :
    d (EBicomod.trivial y) n α = dMidRaw (EBicomod.trivial y) n α := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  show dRaw _ n α V z G = dMidRaw _ n α V z G
  simp only [dRaw, dMidRaw, LinearMap.pi_apply]
  by_cases hG : G.len = n + 1
  · rw [if_pos hG, if_pos hG]
    have h1 : G.nth 1 ≠ ⊥ := G.ne_bot_of_pos (by omega) (by omega)
    have h2 : G.nth n ≠ ⊤ := G.ne_top_of_lt (by omega)
    have e1 : (EBicomod.trivial y).proj V (G.nth 1) = 0 := by
      simp only [EBicomod.trivial, dif_neg h1]; rfl
    have e2 : (EBicomod.trivial y).res V (G.nth n) = 0 := by
      simp only [EBicomod.trivial, dif_neg h2]; rfl
    simp [e1, e2]
  · rw [if_neg hG, if_neg hG]

theorem faceSum_comp {V : FGModuleCat.{0} F} {X Y : Type} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (G : Flag F V) (γ : Y →ₗ[k] (Flag F V → k)) (φ : X →ₗ[k] Y) :
    faceSum X G (γ ∘ₗ φ) = faceSum Y G γ ∘ₗ φ := by
  unfold faceSum
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
  · simp only [dif_pos h, LinearMap.smul_apply, LinearMap.comp_apply]
  · simp [dif_neg h]

theorem precompTrunc_dMid (x : EBicomod F k) (p n : ℕ)
    (α : RawCochain (EBicomod.trivial (x.X.trunc p))) :
    precompTrunc x p (dMidRaw (EBicomod.trivial (x.X.trunc p)) n α) =
      dMidRaw x n (precompTrunc x p α) := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  have key : ∀ w : (EBicomod.trivial (x.X.trunc p)).X.ev V, dMidRaw _ n α V w G =
      if G.len = n + 1 then faceSum _ G (α V) w else 0 := fun w => by
    by_cases hG : G.len = n + 1 <;> simp [dMidRaw, hG]
  have key2 : dMidRaw x n (precompTrunc x p α) V z G =
      if G.len = n + 1 then faceSum _ G (precompTrunc x p α V) z else 0 := by
    by_cases hG : G.len = n + 1 <;> simp [dMidRaw, hG]
  refine (key (((x.X.truncπ p).app ⟨V⟩).hom z)).trans (Eq.trans ?_ key2.symm)
  split_ifs
  · exact (LinearMap.congr_fun (faceSum_comp G (α V) ((x.X.truncπ p).app ⟨V⟩).hom) z).symm
  · rfl

theorem filt_anti (x : EBicomod F k) {p q : ℤ} (h : p ≤ q) (n : ℕ) :
    filt x q n ≤ filt x p n := by
  intro α hα
  rw [mem_filt_iff] at hα ⊢
  exact ⟨hα.1, fun V hV => hα.2 V (lt_of_lt_of_le hV h)⟩

theorem Bpage_zero_le_filt (x : EBicomod F k) (p : ℕ) (n : ℕ) :
    Bpage x 0 p n ≤ filt x ((p : ℤ) + 1) n := by
  cases n with
  | zero => exact inf_le_left
  | succ n =>
    refine sup_le ?_ inf_le_left
    rintro _ ⟨β, hβ, rfl⟩
    have h1 : β ∈ filt x ((p : ℤ) + 1) n := by
      have := hβ.1
      simpa using this
    exact (d_filt x _ n h1).1

theorem filt_le_Bpage_zero (x : EBicomod F k) (p : ℕ) (n : ℕ) :
    filt x ((p : ℤ) + 1) n ≤ Bpage x 0 p n := by
  have hZ : filt x ((p : ℤ) + 1) n ≤ Zpage x (((0 : ℕ) : ℤ) - 1) ((p : ℤ) + 1) n := by
    intro α hα
    refine ⟨hα, ?_⟩
    show d x n α ∈ filt x _ (n + 1)
    exact filt_anti x (by simp) _ (d_filt x _ n hα).1
  cases n with
  | zero => exact hZ
  | succ n => exact le_sup_of_le_right hZ

theorem truncπ_apply_of_eq (x : GLSpecies F k) (p : ℕ) (V : FGModuleCat.{0} F)
    (h : finrank F V = p) (w : x.ev V) :
    (((x.truncπ p).app ⟨V⟩).hom w).val = w := by
  simp [GLSpecies.truncπ, h]
  rfl

theorem truncπ_surj (x : GLSpecies F k) (p : ℕ) (V : FGModuleCat.{0} F) :
    Function.Surjective ((x.truncπ p).app ⟨V⟩).hom := by
  intro z
  by_cases h : finrank F V = p
  · exact ⟨z.val, Subtype.ext (truncπ_apply_of_eq x p V h z.val)⟩
  · refine ⟨0, ?_⟩
    have hz : z.val ∈ (⊥ : Submodule k (x.obj ⟨V⟩)) := by
      have := z.2
      simpa [h] using this
    have hz0 : z = 0 := Subtype.ext ((Submodule.mem_bot k).1 hz)
    rw [hz0]
    exact map_zero _

/-- **Lemma 1.24.** `f^p : C•(x_p)[p] → E₀^{p,•}(x)`, `f^p(α) = α ∘ π_p + F^{p+1}`, is an
isomorphism of complexes. Its domain only depends on the species underlying `x`. -/
theorem lemma_1_24 (x : EBicomod F k) (p n : ℕ) :
    ∃ f : cochains (EBicomod.trivial (x.X.trunc p)) n ≃ₗ[k] E x 0 p n,
      (∀ α : cochains (EBicomod.trivial (x.X.trunc p)) n,
        f α = Subquot.mk (precompTrunc x p α.1) (precompTrunc_mem x p n α.2)) ∧
      (∀ α : cochains (EBicomod.trivial (x.X.trunc p)) n,
        Subquot.mk (precompTrunc x p (d _ n α.1)) (precompTrunc_mem x p (n + 1) (d_mem _ α.2)) =
          (Subquot.map (A' := Zpage x 0 p (n + 1)) (B' := Bpage x 0 p (n + 1)) (d x n)
            (by simpa using dPage_hA x 0 (p : ℤ) n) (by simpa using dPage_hB x 0 (p : ℤ) n)
            (f α) : E x 0 p (n + 1))) := by
  have hpc : ∀ α, α ∈ cochains (EBicomod.trivial (x.X.trunc p)) n →
      precompTrunc x p α ∈ cochains x n :=
    fun α hα => Zpage_le_cochains x _ _ _ (precompTrunc_mem x p n hα)
  let ψ : cochains (EBicomod.trivial (x.X.trunc p)) n →ₗ[k] Zpage x 0 p n :=
    ((precompTrunc x p).comp (Submodule.subtype _)).codRestrict (Zpage x 0 p n)
      (fun α => precompTrunc_mem x p n α.2)
  let f0 : cochains (EBicomod.trivial (x.X.trunc p)) n →ₗ[k] E x 0 p n :=
    (Submodule.mkQ _).comp ψ
  have hf0 : ∀ α, f0 α = Subquot.mk (precompTrunc x p α.1) (precompTrunc_mem x p n α.2) :=
    fun α => rfl
  have hinj : Function.Injective f0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro α hα
    have h1 : precompTrunc x p α.1 ∈ Bpage x 0 p n := by
      have := (Submodule.Quotient.mk_eq_zero _).1 hα
      exact this
    have h2 := (mem_filt_iff x _ n _).1 (Bpage_zero_le_filt x p n h1)
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro z
    funext G
    obtain ⟨w, rfl⟩ := truncπ_surj (x.X) p V z
    by_cases hV : (finrank F V : ℤ) < p + 1
    · have := congrArg (fun f => f w G) (h2.2 V hV)
      exact this
    · have hne : finrank F V ≠ p := by omega
      have hz : ((x.X.truncπ p).app ⟨V⟩).hom w = 0 := by
        have : ((x.X.truncπ p).app ⟨V⟩).hom = 0 := by
          show (ModuleCat.ofHom (if h : finrank F V = p then _ else 0)).hom = 0
          rw [dif_neg hne]; rfl
        rw [this]; rfl
      rw [hz]
      exact congrFun (map_zero (α.1 V)) G
  have hsurj : Function.Surjective f0 := by
    intro c
    obtain ⟨⟨β, hβ⟩, rfl⟩ := Submodule.mkQ_surjective _ c
    have hβc : β ∈ cochains x n := Zpage_le_cochains x _ _ _ hβ
    have hβV : ∀ V : FGModuleCat.{0} F, (finrank F V : ℤ) < p → β V = 0 :=
      fun V hV => ((mem_filt_iff x _ n _).1 hβ.1).2 V hV
    let α : RawCochain (EBicomod.trivial (x.X.trunc p)) := fun V =>
      β V ∘ₗ Submodule.subtype _
    have hαc : α ∈ cochains (EBicomod.trivial (x.X.trunc p)) n := by
      refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
      · exact hβc.1 V _ G hG
      · exact hβc.2 V W e z.val G
    refine ⟨⟨α, hαc⟩, ?_⟩
    show (Submodule.mkQ _) (ψ ⟨α, hαc⟩) = Submodule.mkQ _ ⟨β, hβ⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show precompTrunc x p α - β ∈ Bpage x 0 p n
    apply filt_le_Bpage_zero
    rw [mem_filt_iff]
    refine ⟨Submodule.sub_mem _ (hpc α hαc) hβc, fun V hV => ?_⟩
    apply LinearMap.ext
    intro w
    funext G
    show β V ((((x.X.truncπ p).app ⟨V⟩).hom w).val) G - β V w G = 0
    by_cases hlt : (finrank F V : ℤ) < p
    · rw [hβV V hlt]
      have : ((x.X.truncπ p).app ⟨V⟩).hom = 0 := by
        show (ModuleCat.ofHom (if h : finrank F V = p then _ else 0)).hom = 0
        rw [dif_neg (by omega)]; rfl
      rw [this]
      simp
    · have heq : finrank F V = p := by omega
      rw [truncπ_apply_of_eq x.X p V heq w]
      simp
  refine ⟨LinearEquiv.ofBijective f0 ⟨hinj, hsurj⟩, fun α => rfl, fun α => ?_⟩
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  show precompTrunc x p (d _ n α.1) - d x n (precompTrunc x p α.1) ∈ Bpage x 0 p (n + 1)
  have hpre : precompTrunc x p α.1 ∈ filt x (p : ℤ) n := ((precompTrunc_mem x p n α.2).1)
  have h1 := (d_filt x _ n hpre).2
  have e : precompTrunc x p (d (EBicomod.trivial (x.X.trunc p)) n α.1) =
      dMidRaw x n (precompTrunc x p α.1) := by
    rw [dTriv_eq, precompTrunc_dMid]
  rw [e, ← neg_sub]
  exact filt_le_Bpage_zero x p (n + 1) (Submodule.neg_mem _ h1)

theorem Flag.map_le_map_iff {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (G H : Flag K V) :
    G.map e ≤ H.map e ↔ G ≤ H := by
  show (G.map e).carrier ⊆ (H.map e).carrier ↔ G.carrier ⊆ H.carrier
  exact Finset.image_subset_image_iff (Submodule.map_injective_of_injective e.injective)

theorem Flag.directlyRefines_map {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (G H : Flag K V) :
    (G.map e).DirectlyRefines (H.map e) ↔ G.DirectlyRefines H := by
  unfold Flag.DirectlyRefines
  rw [Flag.map_le_map_iff, Flag.len_map, Flag.len_map]

theorem Flag.newMember_mem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (G H : Flag K V) (h : G.DirectlyRefines H) : G.newMember H ∈ H.carrier := by
  have hcard : (H.carrier \ G.carrier).card = 1 := by
    have h1 := Finset.card_sdiff_of_subset h.1
    have h2 := G.card_eq_len_succ
    have h3 := H.card_eq_len_succ
    have h4 := h.2
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
  have hne : (H.carrier \ G.carrier).Nonempty := by rw [ha]; exact ⟨a, Finset.mem_singleton_self a⟩
  unfold Flag.newMember
  rw [dif_pos hne]
  exact (Finset.mem_sdiff.1 hne.choose_spec).1

theorem Flag.newMember_map {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (G H : Flag K V) (h : G.DirectlyRefines H) :
    (G.map e).newMember (H.map e) = (G.newMember H).map (e : V →ₗ[K] W) := by
  have hinj := Submodule.map_injective_of_injective (f := (e : V →ₗ[K] W)) e.injective
  have hcard : (H.carrier \ G.carrier).card = 1 := by
    have h1 := Finset.card_sdiff_of_subset h.1
    have h2 := G.card_eq_len_succ
    have h3 := H.card_eq_len_succ
    have h4 := h.2
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
  have hne : (H.carrier \ G.carrier).Nonempty := by rw [ha]; exact ⟨a, Finset.mem_singleton_self a⟩
  have uniq : ∀ x ∈ H.carrier \ G.carrier, x = a := fun x hx => by
    rw [ha] at hx; exact Finset.mem_singleton.1 hx
  have hdiff : ((H.map e).carrier \ (G.map e).carrier) = {a.map (e : V →ₗ[K] W)} := by
    show (H.carrier.image _ \ G.carrier.image _) = _
    rw [← Finset.image_sdiff _ _ hinj, ha, Finset.image_singleton]
  have hne' : ((H.map e).carrier \ (G.map e).carrier).Nonempty := by
    rw [hdiff]; exact ⟨_, Finset.mem_singleton_self _⟩
  unfold Flag.newMember
  rw [dif_pos hne', dif_pos hne]
  have h1 : hne.choose = a := uniq _ hne.choose_spec
  have uniq' : ∀ x ∈ (H.map e).carrier \ (G.map e).carrier, x = a.map (e : V →ₗ[K] W) :=
    fun x hx => by rw [hdiff] at hx; exact Finset.mem_singleton.1 hx
  rw [uniq' _ hne'.choose_spec, h1]

/-- The permutation action of `GL(Fⁿ)` commutes with the differential of `Σₙ`. -/
theorem sigmaD_flagRep (n : ℕ) (g : GLn F n) :
    (sigmaD F k n) ∘ₗ (flagRep F k n g) = (flagRep F k n g) ∘ₗ (sigmaD F k n) := by
  apply Finsupp.lhom_ext
  intro G b
  have hb : Finsupp.single G b = b • Finsupp.single G (1 : k) := by simp
  rw [hb]
  simp only [LinearMap.comp_apply, map_smul]
  congr 1
  have h1 : flagRep F k n g (Finsupp.single G (1 : k)) = Finsupp.single (g • G) (1 : k) := by
    simp [flagRep]
  rw [h1]
  simp only [sigmaD, Finsupp.linearCombination_single, one_smul, map_sum, map_smul]
  refine (Finset.sum_equiv (MulAction.toPerm g) (fun H => ?_) (fun H hH => ?_)).symm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulAction.toPerm_apply]
    exact (Flag.directlyRefines_map g G H).symm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH
    have hnm := Flag.newMember_map g G H hH
    have hi : (g • H).index ((g • G).newMember (g • H)) = H.index (G.newMember H) := by
      show (H.map g).index ((G.map g).newMember (H.map g)) = _
      rw [hnm]
      exact Flag.index_map g H (Flag.newMember_mem G H hH)
    simp only [MulAction.toPerm_apply]
    rw [hi]
    simp [flagRep]

theorem flagRep_mem_cycles (n q : ℕ) (g : GLn F n) {v : FlagModule F k n}
    (hv : v ∈ flagDeg F k n q ⊓ LinearMap.ker (sigmaD F k n)) :
    flagRep F k n g v ∈ flagDeg F k n q ⊓ LinearMap.ker (sigmaD F k n) := by
  refine ⟨flagRep_mem_flagDeg F k n q g hv.1, ?_⟩
  have := LinearMap.congr_fun (sigmaD_flagRep (F := F) (k := k) n g) v
  simp only [LinearMap.comp_apply] at this
  rw [LinearMap.mem_ker.1 hv.2, map_zero] at this
  exact LinearMap.mem_ker.2 this

theorem flagRep_mem_sigmaB (n q : ℕ) (g : GLn F n) {v : FlagModule F k n}
    (hv : v ∈ sigmaB F k n q) : flagRep F k n g v ∈ sigmaB F k n q := by
  cases q with
  | zero =>
    simp only [sigmaB, Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  | succ q =>
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    refine Submodule.mem_map.2 ⟨flagRep F k n g w, flagRep_mem_flagDeg F k n q g hw, ?_⟩
    exact LinearMap.congr_fun (sigmaD_flagRep (F := F) (k := k) n g) w

/-- The `GL(Fⁿ)`-module structure on `H^q(Σₙ^•)`. -/
def hsigmaRep (F : Type) [Field F] [Fintype F] (k : Type) [Field k] (n q : ℕ) :
    Representation k (GLn F n) (HSigma F k n q) where
  toFun g := Subquot.map (flagRep F k n g) (fun v hv => flagRep_mem_cycles (F := F) (k := k) n q g hv)
    (fun v hv => flagRep_mem_sigmaB (F := F) (k := k) n q g hv.1)
  map_one' := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H a =>
      simp only [Subquot.map, Submodule.mapQ_apply, map_one, Module.End.one_apply]
      rfl
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H a =>
      simp only [Subquot.map, Submodule.mapQ_apply, map_mul, Module.End.mul_apply]
      rfl

/-- `Hom_G(M, N)` for representations of a group `G`. -/
def equivariantHom {G M N : Type*} [Group G] [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] (ρ : Representation k G M) (σ : Representation k G N) :
    Submodule k (M →ₗ[k] N) where
  carrier := {f | ∀ g, f ∘ₗ ρ g = σ g ∘ₗ f}
  add_mem' := by
    intro f f' hf hf' g
    simp only [LinearMap.add_comp, LinearMap.comp_add, hf g, hf' g]
  zero_mem' := by intro g; simp
  smul_mem' := by
    intro r f hf g
    simp only [LinearMap.smul_comp, LinearMap.comp_smul, hf g]

end SpectralSequence

end MartinPhd

end
end Chapter1Section7

section E1

open scoped BigOperators TensorProduct
open CategoryTheory Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

/-! ## Natural families of dimension `p` (for Lemma 1.25)

A cochain supported in dimension exactly `p` is determined by its value on `Fᵖ`, which is a
`GL(Fᵖ)`-equivariant family; conversely every equivariant family extends. -/

section NatFam

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

/-- Equivariance of a family `f : x(Fᵖ) → (Fl(Fᵖ) → k)` under `GL(Fᵖ)`. -/
def IsNatFam (x : GLSpecies F k) (p : ℕ)
    (f : x.ev (stdSpace F p) →ₗ[k] (Flag F (stdSpace F p) → k)) : Prop :=
  ∀ (g : (stdSpace F p) ≃ₗ[F] (stdSpace F p)) (w : x.ev (stdSpace F p))
    (K : Flag F (stdSpace F p)), f (x.mapEquiv g w) (K.map g) = f w K

/-- The extension of a family on `Fᵖ` to all `V` (zero unless `dim V = p`). -/
def extFamily (x : GLSpecies F k) (p : ℕ)
    (f : x.ev (stdSpace F p) →ₗ[k] (Flag F (stdSpace F p) → k)) (V : FGModuleCat.{0} F) :
    x.ev V →ₗ[k] (Flag F V → k) :=
  if h : finrank F V = p then
    LinearMap.pi fun G : Flag F V =>
      (LinearMap.proj (G.map (LinearEquiv.ofFinrankEq V (stdSpace F p) (by simpa using h)))) ∘ₗ f ∘ₗ
        x.mapEquiv (LinearEquiv.ofFinrankEq V (stdSpace F p) (by simpa using h))
  else 0

theorem extFamily_apply (x : GLSpecies F k) (p : ℕ)
    {f : x.ev (stdSpace F p) →ₗ[k] (Flag F (stdSpace F p) → k)} (hf : IsNatFam x p f)
    (V : FGModuleCat.{0} F) (e : V ≃ₗ[F] stdSpace F p) (z : x.ev V) (G : Flag F V) :
    extFamily x p f V z G = f (x.mapEquiv e z) (G.map e) := by
  have h : finrank F V = p := by simpa using e.finrank_eq
  unfold extFamily
  rw [dif_pos h]
  set e0 : V ≃ₗ[F] stdSpace F p := LinearEquiv.ofFinrankEq V (stdSpace F p) (by simpa using h)
  have h1 := hf (e0.symm.trans e) (x.mapEquiv e0 z) (G.map e0)
  have e2 : x.mapEquiv (e0.symm.trans e) (x.mapEquiv e0 z) = x.mapEquiv e z := by
    rw [GLSpecies.mapEquiv_trans_apply]
    congr 1
    exact LinearMap.congr_fun (GLSpecies.mapEquiv_symm_comp x e0) z
  have e3 : (G.map e0).map (e0.symm.trans e) = G.map e := by
    rw [← Flag.map_trans]
    congr 1
    ext v
    simp
  rw [e2, e3] at h1
  exact h1.symm

theorem extFamily_of_not (x : GLSpecies F k) (p : ℕ)
    (f : x.ev (stdSpace F p) →ₗ[k] (Flag F (stdSpace F p) → k)) (V : FGModuleCat.{0} F)
    (h : finrank F V ≠ p) : extFamily x p f V = 0 := by
  unfold extFamily; rw [dif_neg h]

theorem extFamily_stdSpace (x : GLSpecies F k) (p : ℕ)
    {f : x.ev (stdSpace F p) →ₗ[k] (Flag F (stdSpace F p) → k)} (hf : IsNatFam x p f) :
    extFamily x p f (stdSpace F p) = f := by
  apply LinearMap.ext; intro z; funext G
  rw [extFamily_apply x p hf (stdSpace F p) (LinearEquiv.refl F _) z G]
  have h := hf (LinearEquiv.refl F _) z G
  simpa using h

theorem extFamily_mem_cochains (x : EBicomod F k) (p n : ℕ)
    {f : x.X.ev (stdSpace F p) →ₗ[k] (Flag F (stdSpace F p) → k)} (hf : IsNatFam x.X p f)
    (hdeg : ∀ w K, K.len ≠ n → f w K = 0) : extFamily x.X p f ∈ cochains x n := by
  refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
  · by_cases h : finrank F V = p
    · let e0 : V ≃ₗ[F] stdSpace F p := LinearEquiv.ofFinrankEq V (stdSpace F p) (by simpa using h)
      rw [extFamily_apply x.X p hf V e0 z G]
      exact hdeg _ _ (by rw [Flag.len_map]; exact hG)
    · rw [extFamily_of_not x.X p f V h]; rfl
  · by_cases h : finrank F V = p
    · have hW : finrank F W = p := by rw [← LinearEquiv.finrank_eq e]; exact h
      let e0 : W ≃ₗ[F] stdSpace F p := LinearEquiv.ofFinrankEq W (stdSpace F p) (by simpa using hW)
      rw [extFamily_apply x.X p hf W e0 _ _, extFamily_apply x.X p hf V (e.trans e0) z G]
      rw [GLSpecies.mapEquiv_trans_apply, Flag.map_trans]
    · have hW : finrank F W ≠ p := by rw [← LinearEquiv.finrank_eq e]; exact h
      rw [extFamily_of_not x.X p f V h, extFamily_of_not x.X p f W hW]; rfl

theorem extFamily_mem_filt (x : EBicomod F k) (p n : ℕ)
    {f : x.X.ev (stdSpace F p) →ₗ[k] (Flag F (stdSpace F p) → k)} (hf : IsNatFam x.X p f)
    (hdeg : ∀ w K, K.len ≠ n → f w K = 0) : extFamily x.X p f ∈ filt x (p : ℤ) n := by
  refine (mem_filt_iff x _ _ _).2 ⟨extFamily_mem_cochains x p n hf hdeg, fun V hV => ?_⟩
  rw [extFamily_of_not x.X p f V (by omega)]

theorem isNatFam_of_mem_cochains (x : EBicomod F k) (p n : ℕ) {α : RawCochain x}
    (hα : α ∈ cochains x n) : IsNatFam x.X p (α (stdSpace F p)) :=
  fun g w K => hα.2 (stdSpace F p) (stdSpace F p) g w K

theorem mem_filt_succ_of_stdSpace (x : EBicomod F k) (p n : ℕ) {α : RawCochain x}
    (hα : α ∈ filt x (p : ℤ) n) (h0 : α (stdSpace F p) = 0) : α ∈ filt x ((p : ℤ) + 1) n := by
  obtain ⟨hαc, hαV⟩ := (mem_filt_iff x _ _ _).1 hα
  refine (mem_filt_iff x _ _ _).2 ⟨hαc, fun V hV => ?_⟩
  by_cases hlt : (finrank F V : ℤ) < p
  · exact hαV V hlt
  · have hVp : finrank F V = p := by omega
    let e : V ≃ₗ[F] stdSpace F p := LinearEquiv.ofFinrankEq V (stdSpace F p) (by simpa using hVp)
    apply LinearMap.ext; intro z; funext G
    have := hαc.2 V (stdSpace F p) e z G
    rw [h0] at this
    simpa using this.symm

end NatFam

end MartinPhd

end
end E1

section Faces

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

theorem dRaw_eq_faceSum_of_filt {F : Type} [Field F] [Fintype F] {k : Type} [Field k]
    (x : EBicomod F k) (p : ℤ) (n : ℕ) {α : RawCochain x} (hα : α ∈ filt x p n)
    (V : FGModuleCat.{0} F) (hV : (finrank F V : ℤ) = p) (z : x.X.ev V) (G : Flag F V)
    (hG : G.len = n + 1) :
    dRaw x n α V z G = faceSum _ G (α V) z := by
  obtain ⟨h1, h2⟩ := outer_face_dims G hG
  obtain ⟨-, hαV⟩ := (mem_filt_iff x p n α).1 hα
  have hq : α (quo (G.nth 1)) = 0 := hαV _ (by
    have : (finrank F (V ⧸ G.nth 1) : ℤ) < finrank F V := by exact_mod_cast h1
    change (finrank F (V ⧸ G.nth 1) : ℤ) < p
    omega)
  have hs : α (sub (G.nth n)) = 0 := hαV _ (by
    have : (finrank F (G.nth n) : ℤ) < finrank F V := by exact_mod_cast h2
    change (finrank F (G.nth n) : ℤ) < p
    omega)
  simp only [dRaw, LinearMap.pi_apply, if_pos hG]
  simp [hq, hs]

theorem sigmaD_xi_apply {F : Type} [Field F] [Fintype F] {k : Type} [Field k] (n : ℕ)
    (φ : Flag F (Fin n → F) → k) (G : Flag F (Fin n → F)) :
    sigmaD F k n ((Finsupp.linearEquivFunOnFinite k k (Flag F (Fin n → F))).symm φ) G =
      ∑ A ∈ G.carrier, if h : A ≠ ⊥ ∧ A ≠ ⊤ then ((-1 : k) ^ G.index A) * φ (G.erase A h) else 0 := by
  let ξ := (Finsupp.linearEquivFunOnFinite k k (Flag F (Fin n → F))).symm
  have hprop := (prop_1_8 F k n).2.1 φ
  have hstep1 : sigmaD F k n (ξ φ) G = flagPairing F k n (ξ φ) (chainBoundary F k n (Finsupp.single G 1)) := by
    have hcoe := congr_fun (congrArg DFunLike.coe hprop.symm) G
    exact hcoe
  rw [hstep1]
  change flagBil F k n (ξ φ) (chainBoundary F k n (Finsupp.single G 1)) = _
  rw [chainBoundary_single, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
  · rw [dif_pos h, dif_pos h, map_smul, smul_eq_mul]
    change ((-1 : k) ^ G.index A) * flagPairing F k n (ξ φ) (Finsupp.single (G.erase A h) 1) = _
    rw [flagPairing_single]
    rfl
  · rw [dif_neg h, dif_neg h, map_zero]

end MartinPhd

end
end Faces

section Lift

open Module
noncomputable section
namespace MartinPhd

/-! ## Equivariant lifting through projective modules (for Lemma 1.25) -/

section Lift

variable {k : Type} [Field k] {G : Type} [Group G]

/-- An equivariant linear map is `k[G]`-linear on the associated modules. -/
def toKGHom {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {ρ : Representation k G M} {σ : Representation k G N} (f : M →ₗ[k] N)
    (hf : ∀ g, f ∘ₗ ρ g = σ g ∘ₗ f) : ρ.asModule →ₗ[MonoidAlgebra k G] σ.asModule where
  toFun x := σ.asModuleEquiv.symm (f (ρ.asModuleEquiv x))
  map_add' x y := by simp
  map_smul' r x := by
    have key : ∀ r : MonoidAlgebra k G, ∀ v : M, f (ρ.asAlgebraHom r v) = σ.asAlgebraHom r (f v) := by
      intro r
      induction r using MonoidAlgebra.induction_linear with
      | zero => intro v; simp
      | add a b ha hb => intro v; simp [map_add, LinearMap.add_apply, ha, hb]
      | single g c =>
        intro v
        have h1 := LinearMap.congr_fun (hf g) v
        simp only [LinearMap.comp_apply] at h1
        simp [Representation.asAlgebraHom_single, h1]
    show σ.asModuleEquiv.symm (f (ρ.asModuleEquiv (r • x))) = r • σ.asModuleEquiv.symm
      (f (ρ.asModuleEquiv x))
    rw [Representation.asModuleEquiv_map_smul, key]
    rfl

theorem equiv_lift {M N N' : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup N'] [Module k N'] (ρ : Representation k G M) (σ : Representation k G N)
    (τ : Representation k G N') (hP : Module.Projective (MonoidAlgebra k G) ρ.asModule)
    (π : N →ₗ[k] N') (hπ : ∀ g, π ∘ₗ σ g = τ g ∘ₗ π) (hsurj : Function.Surjective π)
    (f : M →ₗ[k] N') (hf : ∀ g, f ∘ₗ ρ g = τ g ∘ₗ f) :
    ∃ h : M →ₗ[k] N, (∀ g, h ∘ₗ ρ g = σ g ∘ₗ h) ∧ π ∘ₗ h = f := by
  let π' := toKGHom π hπ
  let f' := toKGHom f hf
  have hs : Function.Surjective π' := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (τ.asModuleEquiv y)
    exact ⟨σ.asModuleEquiv.symm x, by
      show τ.asModuleEquiv.symm (π (σ.asModuleEquiv (σ.asModuleEquiv.symm x))) = y
      rw [LinearEquiv.apply_symm_apply, hx, LinearEquiv.symm_apply_apply]⟩
  obtain ⟨h', hh'⟩ := Module.projective_lifting_property π' f' hs
  let h : M →ₗ[k] N := σ.asModuleEquiv.toLinearMap ∘ₗ (h'.restrictScalars k) ∘ₗ
    ρ.asModuleEquiv.symm.toLinearMap
  refine ⟨h, fun g => ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    have := h'.map_smul (MonoidAlgebra.of k G g) (ρ.asModuleEquiv.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars, h]
    rw [Representation.asModuleEquiv_symm_map_rho, this]
    simp [Representation.asAlgebraHom_of]
    rfl
  · apply LinearMap.ext
    intro x
    have := LinearMap.congr_fun hh' (ρ.asModuleEquiv.symm x)
    have h2 : (π' (h' (ρ.asModuleEquiv.symm x))) = f' (ρ.asModuleEquiv.symm x) := this
    simp only [π', f', toKGHom, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply] at h2
    have h3 := congrArg τ.asModuleEquiv h2
    simp only [LinearEquiv.apply_symm_apply] at h3
    simpa [h] using h3

end Lift

end MartinPhd

end
end Lift

section Hom

open Module
noncomputable section
namespace MartinPhd

variable {k : Type} [Field k] {G : Type} [Group G]

/-- equivariant maps, as a submodule (same as `equivariantHom` in Chapter1Section7, restated here to stay Mathlib-only) -/
def eqHom {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (ρ : Representation k G M) (σ : Representation k G N) : Submodule k (M →ₗ[k] N) where
  carrier := {f | ∀ g, f ∘ₗ ρ g = σ g ∘ₗ f}
  add_mem' := by
    intro f f' hf hf' g
    simp only [LinearMap.add_comp, LinearMap.comp_add, hf g, hf' g]
  zero_mem' := by intro g; simp
  smul_mem' := by
    intro r f hf g
    simp only [LinearMap.smul_comp, LinearMap.comp_smul, hf g]

/-- postcomposition with an equivariant map, on equivariant maps -/
def eqHomComp {M N N' : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup N'] [Module k N'] {ρ : Representation k G M} {σ : Representation k G N}
    {σ' : Representation k G N'} (u : N →ₗ[k] N') (hu : ∀ g, u ∘ₗ σ g = σ' g ∘ₗ u) :
    eqHom ρ σ →ₗ[k] eqHom ρ σ' where
  toFun f := ⟨u ∘ₗ f.1, fun g => by
    calc
      (u ∘ₗ f.1) ∘ₗ ρ g = u ∘ₗ (f.1 ∘ₗ ρ g) := by rw [LinearMap.comp_assoc]
      _ = u ∘ₗ (σ g ∘ₗ f.1) := by rw [f.2 g]
      _ = (u ∘ₗ σ g) ∘ₗ f.1 := by rw [← LinearMap.comp_assoc]
      _ = (σ' g ∘ₗ u) ∘ₗ f.1 := by rw [hu g]
      _ = σ' g ∘ₗ (u ∘ₗ f.1) := by rw [LinearMap.comp_assoc]⟩
  map_add' f g := Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' r f := Subtype.ext (LinearMap.comp_smul _ _ _)

@[simp]
lemma eqHomComp_apply_coe {M N N' : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup N'] [Module k N'] {ρ : Representation k G M} {σ : Representation k G N}
    {σ' : Representation k G N'} (u : N →ₗ[k] N') (hu : ∀ g, u ∘ₗ σ g = σ' g ∘ₗ u)
    (f : eqHom ρ σ) :
    ((eqHomComp (ρ := ρ) u hu f : eqHom ρ σ') : M →ₗ[k] N') = u ∘ₗ (f : M →ₗ[k] N) := rfl

lemma range_stable {N' Z : Type} [AddCommGroup N'] [Module k N'] [AddCommGroup Z] [Module k Z]
    (σ' : Representation k G N') (σ : Representation k G Z)
    (d : N' →ₗ[k] Z) (hd : ∀ g, d ∘ₗ σ' g = σ g ∘ₗ d) (g : G) (x : LinearMap.range d) :
    σ g x.1 ∈ LinearMap.range d := by
  obtain ⟨y, hy⟩ := x.2
  use σ' g y
  rw [← hy]
  have h := LinearMap.congr_fun (hd g) y
  simp only [LinearMap.comp_apply] at h
  exact h

/-- Subrepresentation on `LinearMap.range d` when `d` is equivariant. -/
def repRange {N' Z : Type} [AddCommGroup N'] [Module k N'] [AddCommGroup Z] [Module k Z]
    (σ' : Representation k G N') (σ : Representation k G Z)
    (d : N' →ₗ[k] Z) (hd : ∀ g, d ∘ₗ σ' g = σ g ∘ₗ d) :
    Representation k G (LinearMap.range d) where
  toFun g := (σ g).restrict (fun x hx => range_stable σ' σ d hd g ⟨x, hx⟩)
  map_one' := by
    ext ⟨x, hx⟩
    simp
  map_mul' g h := by
    ext ⟨x, hx⟩
    simp

theorem hom_cohomology {M N' Z H : Type} [AddCommGroup M] [Module k M] [AddCommGroup N'] [Module k N']
    [AddCommGroup Z] [Module k Z] [AddCommGroup H] [Module k H]
    (ρ : Representation k G M) (σ' : Representation k G N') (σ : Representation k G Z)
    (τ : Representation k G H) (hP : Module.Projective (MonoidAlgebra k G) ρ.asModule)
    (d : N' →ₗ[k] Z) (hd : ∀ g, d ∘ₗ σ' g = σ g ∘ₗ d)
    (π : Z →ₗ[k] H) (hπ : ∀ g, π ∘ₗ σ g = τ g ∘ₗ π)
    (hsurj : Function.Surjective π) (hker : LinearMap.ker π = LinearMap.range d) :
    Function.Surjective (eqHomComp (ρ := ρ) π hπ : eqHom ρ σ →ₗ[k] eqHom ρ τ) ∧
    LinearMap.ker (eqHomComp (ρ := ρ) π hπ) = LinearMap.range (eqHomComp (ρ := ρ) d hd) := by
  constructor
  · -- Surjective
    intro ⟨f, hf⟩
    obtain ⟨h, hh, hcomp⟩ := equiv_lift ρ σ τ hP π hπ hsurj f hf
    exact ⟨⟨h, hh⟩, Subtype.ext hcomp⟩
  · -- ker = range
    apply le_antisymm
    · intro ⟨f, hf⟩ hfker
      simp only [LinearMap.mem_ker] at hfker
      have hfker_val : π ∘ₗ f = 0 := by
        have := congrArg Subtype.val hfker
        exact this
      have hrange : ∀ m, f m ∈ LinearMap.range d := by
        intro m
        have hm : f m ∈ LinearMap.ker π := by
          rw [LinearMap.mem_ker]
          exact LinearMap.congr_fun hfker_val m
        rwa [hker] at hm
      let f_corest : M →ₗ[k] LinearMap.range d :=
        LinearMap.codRestrict (LinearMap.range d) f hrange
      have hf_corest_eq : ∀ g, f_corest ∘ₗ ρ g = (repRange σ' σ d hd) g ∘ₗ f_corest := by
        intro g
        ext m : 1
        apply Subtype.ext
        change (f (ρ g m) : Z) = σ g (f m)
        exact LinearMap.congr_fun (hf g) m
      have hd_rangeRestrict_eq : ∀ g, d.rangeRestrict ∘ₗ σ' g =
          (repRange σ' σ d hd) g ∘ₗ d.rangeRestrict := by
        intro g
        ext y : 1
        apply Subtype.ext
        change (d (σ' g y) : Z) = σ g (d y)
        exact LinearMap.congr_fun (hd g) y
      obtain ⟨g', hg', hcomp'⟩ := equiv_lift ρ σ' (repRange σ' σ d hd) hP
        d.rangeRestrict hd_rangeRestrict_eq (LinearMap.surjective_rangeRestrict d)
        f_corest hf_corest_eq
      rw [LinearMap.mem_range]
      refine ⟨⟨g', hg'⟩, ?_⟩
      apply Subtype.ext
      simp only [eqHomComp_apply_coe]
      apply LinearMap.ext
      intro m
      have := LinearMap.congr_fun hcomp' m
      have h_val := congrArg Subtype.val this
      exact h_val
    · intro x hx
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      simp only [eqHomComp_apply_coe, ZeroMemClass.coe_zero]
      have hpid : π ∘ₗ d = 0 := by
        apply LinearMap.ext
        intro z
        have hz : d z ∈ LinearMap.range d := LinearMap.mem_range_self d z
        rw [← hker] at hz
        exact hz
      calc
        π ∘ₗ (d ∘ₗ (y : M →ₗ[k] N')) = (π ∘ₗ d) ∘ₗ (y : M →ₗ[k] N') := by rw [LinearMap.comp_assoc]
        _ = 0 ∘ₗ (y : M →ₗ[k] N') := by rw [hpid]
        _ = 0 := LinearMap.zero_comp _

end MartinPhd

end
end Hom

section E1Map

/-!
## Lemma 1.25: the `E₁` page for relatively projective species

The coordinates of a cochain on `Fᵖ` give a map `Tlin α : x(Fᵖ) → k[Fl(Fᵖ)]`; for `α ∈ Zpage x 1 p n`
this lands in cocycles of `Σₚ^•` and is `GL(Fᵖ)`-equivariant, defining `E₁ → Hom_G(x(Fᵖ), Hⁿ(Σₚ))`.
-/

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

/-- `ξ : (Flag → k) ≃ k[Flag]`. -/
abbrev xi (F : Type) [Field F] [Fintype F] (k : Type) [Field k] (p : ℕ) :
    (Flag F (Fin p → F) → k) ≃ₗ[k] FlagModule F k p :=
  (Finsupp.linearEquivFunOnFinite k k (Flag F (Fin p → F))).symm

/-- Coordinates of a cochain on the standard space, as a map into `k[Fl(Fᵖ)]`. -/
def Tlin (x : EBicomod F k) (p : ℕ) : RawCochain x →ₗ[k]
    (x.X.ev (stdSpace F p) →ₗ[k] FlagModule F k p) where
  toFun α := (xi F k p).toLinearMap ∘ₗ α (stdSpace F p)
  map_add' α β := by ext z; simp
  map_smul' c α := by ext z; simp

theorem Tlin_apply (x : EBicomod F k) (p : ℕ) (α : RawCochain x) (z : x.X.ev (stdSpace F p))
    (G : Flag F (Fin p → F)) : Tlin x p α z G = α (stdSpace F p) z G := rfl

theorem Tlin_injective (x : EBicomod F k) (p : ℕ) {α : RawCochain x}
    (h : Tlin x p α = 0) : α (stdSpace F p) = 0 := by
  apply LinearMap.ext; intro z; funext G
  have := congrArg (fun f => f z G) h
  simpa [Tlin_apply] using this

theorem Tlin_eq_zero (x : EBicomod F k) (p : ℕ) {α : RawCochain x}
    (h : α (stdSpace F p) = 0) : Tlin x p α = 0 := by
  apply LinearMap.ext; intro z; ext G
  simp [Tlin_apply, h]

theorem Tlin_mem_flagDeg (x : EBicomod F k) (p n : ℕ) {α : RawCochain x} (hα : α ∈ cochains x n)
    (z : x.X.ev (stdSpace F p)) : Tlin x p α z ∈ flagDeg F k p n := by
  rw [mem_flagDeg_iff]
  intro G hG
  exact hα.1 (stdSpace F p) z G hG

theorem Tlin_equivariant (x : EBicomod F k) (p n : ℕ) {α : RawCochain x} (hα : α ∈ cochains x n)
    (g : GLn F p) : Tlin x p α ∘ₗ x.X.rep p g = flagRep F k p g ∘ₗ Tlin x p α := by
  apply LinearMap.ext; intro z
  ext G'
  obtain ⟨G, rfl⟩ : ∃ G, G' = g • G := ⟨g⁻¹ • G', by simp⟩
  simp only [LinearMap.comp_apply]
  have h1 : flagRep F k p g (Tlin x p α z) (g • G) = Tlin x p α z G := by
    show Finsupp.mapDomain (g • ·) (Tlin x p α z) (g • G) = _
    exact Finsupp.mapDomain_apply_of_injective (MulAction.injective g) _ _
  rw [h1, Tlin_apply, Tlin_apply]
  exact hα.2 (stdSpace F p) (stdSpace F p) g z G


theorem sigmaD_sigmaD (p : ℕ) (φ : FlagModule F k p) :
    sigmaD F k p (sigmaD F k p φ) = 0 := by
  refine pairing_nondeg F k Set.univ (by simp) fun c _ => ?_
  rw [pairing_sigmaD, pairing_sigmaD, chainBoundary_eq, ST.bd_bd]
  simp [flagPairing_eq]

theorem sigmaD_Tlin (x : EBicomod F k) (p n : ℕ) {α : RawCochain x} (hα : α ∈ filt x (p : ℤ) n)
    (z : x.X.ev (stdSpace F p)) :
    sigmaD F k p (Tlin x p α z) = Tlin x p (d x n α) z := by
  have hc := ((mem_filt_iff x _ _ _).1 hα).1
  ext G
  have e1 : sigmaD F k p (Tlin x p α z) G = ∑ A ∈ G.carrier,
      if h : A ≠ ⊥ ∧ A ≠ ⊤ then ((-1 : k) ^ G.index A) * α (stdSpace F p) z (G.erase A h)
      else 0 := sigmaD_xi_apply (F := F) (k := k) p (α (stdSpace F p) z) G
  rw [e1, Tlin_apply]
  show _ = dRaw x n α (stdSpace F p) z G
  by_cases hG : G.len = n + 1
  · rw [dRaw_eq_faceSum_of_filt x p n hα (stdSpace F p) (by simp) z G hG]
    simp only [faceSum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
    · simp [dif_pos h]
    · simp [dif_neg h]
  · have : dRaw x n α (stdSpace F p) z G = 0 := by simp [dRaw, hG]
    rw [this]
    refine Finset.sum_eq_zero fun A hA => ?_
    by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
    · rw [dif_pos h, hc.1 (stdSpace F p) z _ ?_, mul_zero]
      have := ST.len_erase G h hA
      omega
    · rw [dif_neg h]

theorem Tlin_d_filt_succ (x : EBicomod F k) (p n : ℕ) {α : RawCochain x}
    (hα : α ∈ filt x ((p : ℤ) + 1) n) : Tlin x p α = 0 :=
  Tlin_eq_zero x p (((mem_filt_iff x _ _ _).1 hα).2 (stdSpace F p) (by simp))


theorem mem_Zpage_one (x : EBicomod F k) (p : ℤ) (n : ℕ) (α : RawCochain x) :
    α ∈ Zpage x ((1 : ℕ) : ℤ) p n ↔ α ∈ filt x p n ∧ d x n α ∈ filt x (p + 1) (n + 1) := by
  simp [Zpage]

theorem mem_Zpage_zero (x : EBicomod F k) (p : ℤ) (n : ℕ) (α : RawCochain x) :
    α ∈ Zpage x (((1 : ℕ) : ℤ) - 1) p n ↔ α ∈ filt x p n ∧ d x n α ∈ filt x p (n + 1) := by
  simp [Zpage]

theorem mem_Zpage_zero' (x : EBicomod F k) (p : ℤ) (n : ℕ) (α : RawCochain x) :
    α ∈ Zpage x 0 p n ↔ α ∈ filt x p n ∧ d x n α ∈ filt x p (n + 1) := by
  simp [Zpage]

theorem mem_Bpage_zero (x : EBicomod F k) (p : ℤ) (α : RawCochain x) :
    α ∈ Bpage x 1 p 0 ↔ α ∈ filt x (p + 1) 0 ∧ d x 0 α ∈ filt x (p + 1) 1 := by
  simp [Bpage, mem_Zpage_zero']

theorem mem_Bpage_succ (x : EBicomod F k) (p : ℤ) (m : ℕ) (α : RawCochain x) :
    α ∈ Bpage x 1 p (m + 1) ↔ ∃ β ∈ filt x p m, d x m β ∈ filt x p (m + 1) ∧
      ∃ c, (c ∈ filt x (p + 1) (m + 1) ∧ d x (m + 1) c ∈ filt x (p + 1) (m + 2)) ∧ α = d x m β + c := by
  simp only [Bpage, Submodule.mem_sup, Submodule.mem_map, Nat.cast_one, sub_self, sub_add_cancel,
    mem_Zpage_zero']
  constructor
  · rintro ⟨_, ⟨β, hβ, rfl⟩, c, hc, rfl⟩
    exact ⟨β, hβ.1, hβ.2, c, by simpa using hc, rfl⟩
  · rintro ⟨β, hβ, hdβ, c, hc, rfl⟩
    exact ⟨_, ⟨β, ⟨hβ, hdβ⟩, rfl⟩, c, by simpa using hc, rfl⟩


section Theta

/-- Subrepresentation on a stable submodule. -/
def subRep {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module k V]
    (σ : Representation k G V) (W : Submodule k V) (h : ∀ g, ∀ v ∈ W, σ g v ∈ W) :
    Representation k G W where
  toFun g := (σ g).restrict (h g)
  map_one' := by ext ⟨v, hv⟩; simp
  map_mul' g h' := by ext ⟨v, hv⟩; simp

variable (F k) in
/-- cocycles `Zⁿ(Σₚ^•)` inside `k[Fl(Fᵖ)]`. -/
abbrev Alg (p n : ℕ) : Submodule k (FlagModule F k p) :=
  flagDeg F k p n ⊓ LinearMap.ker (sigmaD F k p)

variable (F k) in
def repDeg (p m : ℕ) : Representation k (GLn F p) (flagDeg F k p m) :=
  subRep (flagRep F k p) _ (fun g _ hv => flagRep_mem_flagDeg F k p m g hv)

variable (F k) in
def repAlg (p n : ℕ) : Representation k (GLn F p) (Alg F k p n) :=
  subRep (flagRep F k p) _ (fun g _ hv => flagRep_mem_cycles (F := F) (k := k) p n g hv)

variable (F k) in
/-- `sigmaD : k[Fl_m] → Zᵐ⁺¹`. -/
def dSig (p m : ℕ) : flagDeg F k p m →ₗ[k] Alg F k p (m + 1) :=
  LinearMap.codRestrict _ ((sigmaD F k p) ∘ₗ (flagDeg F k p m).subtype) (fun v =>
    ⟨sigmaD_mem_flagDeg F k v.2, LinearMap.mem_ker.2 (sigmaD_sigmaD p _)⟩)

variable (F k) in
/-- the quotient map `Zⁿ → Hⁿ(Σₚ)`. -/
def piSig (p n : ℕ) : Alg F k p n →ₗ[k] HSigma F k p n := Submodule.mkQ _

theorem dSig_equiv (p m : ℕ) (g : GLn F p) :
    dSig F k p m ∘ₗ repDeg F k p m g = repAlg F k p (m + 1) g ∘ₗ dSig F k p m := by
  ext ⟨v, hv⟩ : 2
  exact LinearMap.congr_fun (sigmaD_flagRep (F := F) (k := k) p g) v

theorem piSig_equiv (p n : ℕ) (g : GLn F p) :
    piSig F k p n ∘ₗ repAlg F k p n g = hsigmaRep F k p n g ∘ₗ piSig F k p n := by
  ext ⟨v, hv⟩ : 2
  rfl

theorem piSig_ker (p m : ℕ) :
    LinearMap.ker (piSig F k p (m + 1)) = LinearMap.range (dSig F k p m) := by
  ext ⟨v, hv⟩
  constructor
  · intro h
    have h' : v ∈ sigmaB F k p (m + 1) := by
      simpa [piSig, LinearMap.mem_ker] using h
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 h'
    exact ⟨⟨w, hw⟩, rfl⟩
  · rintro ⟨⟨w, hw⟩, h⟩
    have : sigmaD F k p w = v := congrArg Subtype.val h
    rw [LinearMap.mem_ker]
    simp only [piSig, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply]
    exact Submodule.mem_map.2 ⟨w, hw, this⟩

theorem mem_ker_piSig (p n : ℕ) (v : Alg F k p n) :
    v ∈ LinearMap.ker (piSig F k p n) ↔ v.1 ∈ sigmaB F k p n := by
  rw [LinearMap.mem_ker]
  simp only [piSig, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply]

theorem piSig_surj (p n : ℕ) : Function.Surjective (piSig F k p n) :=
  Submodule.mkQ_surjective _

end Theta

section Main

variable (x : EBicomod F k) (p n : ℕ)

theorem Tlin_mem_Alg {a : RawCochain x} (ha : a ∈ Zpage x ((1 : ℕ) : ℤ) (p : ℤ) n)
    (z : x.X.ev (stdSpace F p)) : Tlin x p a z ∈ Alg F k p n := by
  obtain ⟨h1, h2⟩ := (mem_Zpage_one x p n a).1 ha
  refine ⟨Tlin_mem_flagDeg x p n ((mem_filt_iff x _ _ _).1 h1).1 z, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, sigmaD_Tlin x p n h1 z]
  exact LinearMap.congr_fun (Tlin_d_filt_succ x p (n + 1) h2) z

/-- `α ↦ (z ↦ ξ(α(Fᵖ)(z)) ∈ Zⁿ(Σₚ))`. -/
def lam (a : Zpage x ((1 : ℕ) : ℤ) (p : ℤ) n) : x.X.ev (stdSpace F p) →ₗ[k] Alg F k p n :=
  LinearMap.codRestrict _ (Tlin x p a.1) (Tlin_mem_Alg x p n a.2)

theorem lam_equiv (a : Zpage x ((1 : ℕ) : ℤ) (p : ℤ) n) (g : GLn F p) :
    lam x p n a ∘ₗ x.X.rep p g = repAlg F k p n g ∘ₗ lam x p n a := by
  apply LinearMap.ext; intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (Tlin_equivariant x p n (Zpage_le_cochains x _ _ _ a.2) g) z

/-- The map `Z₁^{p,n} → Hom_G(x(Fᵖ), Hⁿ(Σₚ))`. -/
def Theta : Zpage x ((1 : ℕ) : ℤ) (p : ℤ) n →ₗ[k]
    equivariantHom (x.X.rep p) (hsigmaRep F k p n) where
  toFun a := ⟨piSig F k p n ∘ₗ lam x p n a, fun g => by
    rw [LinearMap.comp_assoc, lam_equiv, ← LinearMap.comp_assoc, piSig_equiv, LinearMap.comp_assoc]⟩
  map_add' a b := by
    apply Subtype.ext; apply LinearMap.ext; intro z
    show piSig F k p n (lam x p n (a + b) z) = piSig F k p n (lam x p n a z) + piSig F k p n (lam x p n b z)
    rw [← map_add]; congr 1; apply Subtype.ext; simp [lam]
  map_smul' c a := by
    apply Subtype.ext; apply LinearMap.ext; intro z
    have h : lam x p n (c • a) z = c • lam x p n a z := by apply Subtype.ext; simp [lam]
    exact (congrArg (piSig F k p n) h).trans (map_smul _ _ _)

theorem Theta_apply (a : Zpage x ((1 : ℕ) : ℤ) (p : ℤ) n) (z : x.X.ev (stdSpace F p)) :
    (Theta x p n a : x.X.ev (stdSpace F p) →ₗ[k] HSigma F k p n) z =
      piSig F k p n (lam x p n a z) := rfl

theorem Theta_eq_zero_iff (a : Zpage x ((1 : ℕ) : ℤ) (p : ℤ) n) :
    Theta x p n a = 0 ↔ ∀ z, Tlin x p a.1 z ∈ sigmaB F k p n := by
  constructor
  · intro h z
    have h1 : lam x p n a z ∈ LinearMap.ker (piSig F k p n) := by
      rw [LinearMap.mem_ker]
      exact LinearMap.congr_fun (congrArg Subtype.val h) z
    exact (mem_ker_piSig p n _).1 h1
  · intro h
    apply Subtype.ext; apply LinearMap.ext; intro z
    have h1 : lam x p n a z ∈ LinearMap.ker (piSig F k p n) := (mem_ker_piSig p n _).2 (h z)
    exact (LinearMap.mem_ker.1 h1)

/-- Extension of an equivariant family `u : x(Fᵖ) → k[Fl_n(Fᵖ)]` to a cochain. -/
def extCochain (u : x.X.ev (stdSpace F p) →ₗ[k] FlagModule F k p) : RawCochain x :=
  extFamily x.X p ((xi F k p).symm.toLinearMap ∘ₗ u)

theorem extCochain_props (n : ℕ) (u : x.X.ev (stdSpace F p) →ₗ[k] FlagModule F k p)
    (hu : ∀ g, u ∘ₗ x.X.rep p g = flagRep F k p g ∘ₗ u) (hdeg : ∀ z, u z ∈ flagDeg F k p n) :
    extCochain x p u ∈ filt x (p : ℤ) n ∧ Tlin x p (extCochain x p u) = u := by
  have hnat : IsNatFam x.X p ((xi F k p).symm.toLinearMap ∘ₗ u) := by
    intro g w K
    have h1 := LinearMap.congr_fun (hu g) w
    simp only [LinearMap.comp_apply] at h1
    show (xi F k p).symm (u (x.X.mapEquiv g w)) (K.map g) = (xi F k p).symm (u w) K
    have h2 : u (x.X.mapEquiv g w) = flagRep F k p g (u w) := h1
    rw [h2]
    show Finsupp.mapDomain (g • ·) (u w) (g • K) = _
    exact Finsupp.mapDomain_apply_of_injective (MulAction.injective g) _ _
  have hd : ∀ w K, K.len ≠ n → ((xi F k p).symm.toLinearMap ∘ₗ u) w K = 0 := by
    intro w K hK
    exact (mem_flagDeg_iff F k).1 (hdeg w) K hK
  refine ⟨extFamily_mem_filt x p n hnat hd, ?_⟩
  apply LinearMap.ext; intro z
  show xi F k p (extFamily x.X p ((xi F k p).symm.toLinearMap ∘ₗ u) (stdSpace F p) z) = u z
  rw [extFamily_stdSpace x.X p hnat]
  simp

theorem Theta_eq_zero_of_Bpage (a : Zpage x ((1 : ℕ) : ℤ) (p : ℤ) n)
    (ha : a.1 ∈ Bpage x 1 (p : ℤ) n) : Theta x p n a = 0 := by
  rw [Theta_eq_zero_iff]
  intro z
  cases n with
  | zero =>
    have := ((mem_Bpage_zero x p a.1).1 ha).1
    rw [Tlin_d_filt_succ x p 0 this]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨β, hβ, -, c, hc, hac⟩ := (mem_Bpage_succ x p m a.1).1 ha
    rw [hac, map_add, LinearMap.add_apply, Tlin_d_filt_succ x p (m + 1) hc.1, LinearMap.zero_apply, add_zero,
      ← sigmaD_Tlin x p m hβ z]
    exact Submodule.mem_map.2 ⟨_, Tlin_mem_flagDeg x p m ((mem_filt_iff x _ _ _).1 hβ).1 z, rfl⟩

theorem Bpage_of_Theta_eq_zero (hx : x.X.IsRelativelyProjective)
    (a : Zpage x ((1 : ℕ) : ℤ) (p : ℤ) n) (h : Theta x p n a = 0) : a.1 ∈ Bpage x 1 (p : ℤ) n := by
  have hz := (Theta_eq_zero_iff x p n a).1 h
  obtain ⟨h1, h2⟩ := (mem_Zpage_one x p n a.1).1 a.2
  cases n with
  | zero =>
    have h0 : Tlin x p a.1 = 0 := by
      apply LinearMap.ext; intro z
      have := hz z
      simpa [sigmaB] using this
    have := mem_filt_succ_of_stdSpace x p 0 h1 (Tlin_injective x p h0)
    exact (mem_Bpage_zero x p a.1).2 ⟨this, h2⟩
  | succ m =>
    have hπe : ∀ g, piSig F k p (m + 1) ∘ₗ repAlg F k p (m + 1) g =
        hsigmaRep F k p (m + 1) g ∘ₗ piSig F k p (m + 1) := piSig_equiv p (m + 1)
    have hde : ∀ g, dSig F k p m ∘ₗ repDeg F k p m g = repAlg F k p (m + 1) g ∘ₗ dSig F k p m :=
      dSig_equiv p m
    have hs : Function.Surjective (piSig F k p (m + 1)) := piSig_surj p (m + 1)
    have hkr : LinearMap.ker (piSig F k p (m + 1)) = LinearMap.range (dSig F k p m) := piSig_ker p m
    have hker := (hom_cohomology (N' := flagDeg F k p m) (Z := Alg F k p (m + 1))
      (H := HSigma F k p (m + 1)) (x.X.rep p) (repDeg F k p m) (repAlg F k p (m + 1))
      (hsigmaRep F k p (m + 1)) (hx p) (dSig F k p m) hde (piSig F k p (m + 1)) hπe hs hkr).2
    let f : eqHom (M := x.X.ev (stdSpace F p)) (N := Alg F k p (m + 1)) (x.X.rep p) (repAlg F k p (m + 1)) := ⟨lam x p (m + 1) a, lam_equiv x p (m + 1) a⟩
    have hf : f ∈ LinearMap.ker (eqHomComp (M := x.X.ev (stdSpace F p)) (N := Alg F k p (m + 1)) (N' := HSigma F k p (m + 1)) (ρ := x.X.rep p) (σ := repAlg F k p (m + 1)) (σ' := hsigmaRep F k p (m + 1)) (piSig F k p (m + 1)) hπe) := by
      rw [LinearMap.mem_ker]
      apply Subtype.ext; apply LinearMap.ext; intro z
      exact LinearMap.mem_ker.1 ((mem_ker_piSig p (m + 1) _).2 (hz z))
    rw [hker] at hf
    obtain ⟨β, hβ⟩ := hf
    have hβz : ∀ z, Tlin x p a.1 z = sigmaD F k p (β.1 z).1 := by
      intro z
      have := LinearMap.congr_fun (congrArg Subtype.val hβ) z
      exact congrArg Subtype.val this.symm
    have hβeq : ∀ g, (flagDeg F k p m).subtype ∘ₗ β.1 ∘ₗ x.X.rep p g =
        flagRep F k p g ∘ₗ ((flagDeg F k p m).subtype ∘ₗ β.1) := by
      intro g
      apply LinearMap.ext; intro z
      have := LinearMap.congr_fun (β.2 g) z
      exact congrArg Subtype.val this
    obtain ⟨hbf, hbT⟩ := extCochain_props x p m ((flagDeg F k p m).subtype ∘ₗ β.1) hβeq
      (fun z => (β.1 z).2)
    set bh := extCochain x p ((flagDeg F k p m).subtype ∘ₗ β.1) with hbh
    have hβc := ((mem_filt_iff x _ _ _).1 hbf).1
    obtain ⟨hdf1, -⟩ := d_filt x p m hbf
    have ha' : a.1 - d x m bh ∈ filt x (p : ℤ) (m + 1) := Submodule.sub_mem _ h1 hdf1
    have hT : Tlin x p (a.1 - d x m bh) = 0 := by
      apply LinearMap.ext; intro z
      rw [map_sub, LinearMap.sub_apply, ← sigmaD_Tlin x p m hbf z, hβz z, hbT]
      simp
    have h3 := mem_filt_succ_of_stdSpace x p (m + 1) ha' (Tlin_injective x p hT)
    refine (mem_Bpage_succ x p m a.1).2 ⟨bh, hbf, hdf1, a.1 - d x m bh, ⟨h3, ?_⟩, by abel⟩
    rw [map_sub, d_comp_d x m hβc, sub_zero]
    exact h2

theorem Theta_surj (hx : x.X.IsRelativelyProjective) : Function.Surjective (Theta x p n) := by
  rintro ⟨f, hf⟩
  have hπe : ∀ g, piSig F k p n ∘ₗ repAlg F k p n g = hsigmaRep F k p n g ∘ₗ piSig F k p n :=
    piSig_equiv p n
  have hs : Function.Surjective (piSig F k p n) := piSig_surj p n
  obtain ⟨f', hf', hπ⟩ := equiv_lift (N := Alg F k p n) (N' := HSigma F k p n) (x.X.rep p) (repAlg F k p n) (hsigmaRep F k p n) (hx p)
    (piSig F k p n) hπe hs f hf
  have hu : ∀ g, (Alg F k p n).subtype ∘ₗ f' ∘ₗ x.X.rep p g =
      flagRep F k p g ∘ₗ ((Alg F k p n).subtype ∘ₗ f') := by
    intro g
    apply LinearMap.ext; intro z
    have := LinearMap.congr_fun (hf' g) z
    exact congrArg Subtype.val this
  obtain ⟨hbf, hbT⟩ := extCochain_props x p n ((Alg F k p n).subtype ∘ₗ f') hu
    (fun z => (f' z).2.1)
  set α := extCochain x p ((Alg F k p n).subtype ∘ₗ f') with hα
  obtain ⟨hdf1, -⟩ := d_filt x p n hbf
  have hT : Tlin x p (d x n α) = 0 := by
    apply LinearMap.ext; intro z
    rw [← sigmaD_Tlin x p n hbf z, hbT]
    exact LinearMap.mem_ker.1 (f' z).2.2
  have hdα := mem_filt_succ_of_stdSpace x p (n + 1) hdf1 (Tlin_injective x p hT)
  refine ⟨⟨α, (mem_Zpage_one x p n α).2 ⟨hbf, hdα⟩⟩, ?_⟩
  apply Subtype.ext; apply LinearMap.ext; intro z
  have hl : lam x p n ⟨α, (mem_Zpage_one x p n α).2 ⟨hbf, hdα⟩⟩ z = f' z := by
    apply Subtype.ext
    exact LinearMap.congr_fun hbT z
  show piSig F k p n (lam x p n _ z) = f z
  rw [hl]
  exact LinearMap.congr_fun hπ z

end Main

/-- **Lemma 1.25.** If `x` is relatively projective as a species,
`E₁^{p,q}(x) ≅ Hom_{GL(Fᵖ)}(x_p(Fᵖ), H^q(Σ_p^•[p]))`; in particular `E₁^{p,q}(x) = 0`
unless `q = 0` (i.e. `n = p`). -/
theorem lemma_1_25 (x : EBicomod F k) (hx : x.X.IsRelativelyProjective) (p n : ℕ) :
    Nonempty (E x 1 p n ≃ₗ[k] equivariantHom (x.X.rep p) (hsigmaRep F k p n)) ∧
    (n ≠ p → Subsingleton (E x 1 p n)) :=
  by
  have hex : Nonempty (E x 1 p n ≃ₗ[k] equivariantHom (x.X.rep p) (hsigmaRep F k p n)) := by
    let L : E x 1 p n →ₗ[k] equivariantHom (x.X.rep p) (hsigmaRep F k p n) :=
      Submodule.liftQ _ (Theta x p n) (fun a ha => by
        exact LinearMap.mem_ker.2 (Theta_eq_zero_of_Bpage x p n a ha))
    have hinj : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot]
      refine Submodule.ker_liftQ_eq_bot _ _ _ (fun a ha => ?_)
      exact Bpage_of_Theta_eq_zero x p n hx a (LinearMap.mem_ker.1 ha)
    have hsurj : Function.Surjective L := by
      intro f
      obtain ⟨a, ha⟩ := Theta_surj x p n hx f
      exact ⟨Submodule.Quotient.mk a, by simpa [L] using ha⟩
    exact ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩⟩
  refine ⟨hex, fun hn => ?_⟩
  obtain ⟨e⟩ := hex
  have : Subsingleton (HSigma F k p n) := (cor_1_9 F k p).1 n hn
  have : Subsingleton (equivariantHom (x.X.rep p) (hsigmaRep F k p n)) :=
    ⟨fun f g => Subtype.ext (LinearMap.ext fun z => Subsingleton.elim _ _)⟩
  exact e.injective.subsingleton


end MartinPhd

end
end E1Map
