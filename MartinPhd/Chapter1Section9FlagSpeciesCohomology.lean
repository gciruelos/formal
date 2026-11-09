import MartinPhd.Chapter1Section6Steinberg
import MartinPhd.Chapter1Section7Convergence
import MartinPhd.Chapter1Section8FlagSpeciesShuffle

/-!
# Chapter 1, end of Section 1.7 (assembly of the exponential case, which needs Section 1.6) and Section 1.9 (cohomology of flag species: base)

Contents:
* `HΣ_n^n` has no nonzero invariant vectors for `n ≥ 2`
* Assembly of `H•(e)` (Corollary 1.27, second half)
* Sch
* Base
-/

section HSigmaInv

/-!
## `HΣ_n^n` has no nonzero invariant vectors for `n ≥ 2`

`HΣ_n^n ≅ Stₙ^*` equivariantly (Corollary 1.9); an invariant functional on the simple module
`Stₙ` (of dimension `|F|^{C(n,2)} ≥ 2`) vanishes.
-/

open Module
noncomputable section
namespace MartinPhd

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

theorem hsigma_invariant_eq_zero [CharZero k] (n : ℕ) (hn : 2 ≤ n) (w : HSigma F k n n)
    (hw : ∀ g, hsigmaRep F k n n g w = w) : w = 0 := by
  obtain ⟨e, he⟩ := cor_1_9_equivariant (F := F) (k := k) n
  set φ : Module.Dual k (steinberg F k n) := e w with hφdef
  have hφ : ∀ g c, φ (stAct F k g c) = φ c := fun g c => by
    have := he g w c
    rw [hw g] at this
    exact this
  let W : Submodule k (FlagModule F k n) :=
    (LinearMap.ker φ).map (steinberg F k n).subtype
  have hWle : W ≤ steinberg F k n := by
    rintro _ ⟨c, -, rfl⟩; exact c.2
  have hWinv : ∀ g, W.map (flagRep F k n g) ≤ W := by
    rintro g _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨stAct F k g c, ?_, rfl⟩
    have hc' : φ c = 0 := hc
    show φ (stAct F k g c) = 0
    rw [hφ, hc']
  rcases steinberg_simple n W hWle hWinv with h | h
  · -- φ is injective
    exfalso
    have hker : LinearMap.ker φ = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      have : (c : FlagModule F k n) ∈ W := ⟨c, hc, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact (Submodule.mem_bot k).2 (Subtype.ext this)
    have hinj : Function.Injective φ := LinearMap.ker_eq_bot.1 hker
    have hdim := (solomon_tits (F := F) (k := k) n (by omega)).2.1
    have hpos : 0 < finrank k (steinberg F k n) := by
      rw [hdim]; exact pow_pos Fintype.card_pos _
    haveI : Module.Finite k (steinberg F k n) := Module.finite_of_finrank_pos hpos
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_self, hdim] at hle
    have h2 : 2 ≤ Fintype.card F := by
      have : 1 < Fintype.card F := Fintype.one_lt_card
      omega
    have hc : 1 ≤ n.choose 2 := by
      rw [Nat.choose_two_right]
      have : 2 ≤ n * (n - 1) := by
        calc 2 = 2 * 1 := rfl
          _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
      omega
    have : 2 ≤ Fintype.card F ^ n.choose 2 :=
      calc 2 ≤ Fintype.card F := h2
        _ = Fintype.card F ^ 1 := (pow_one _).symm
        _ ≤ Fintype.card F ^ n.choose 2 := Nat.pow_le_pow_right (by omega) hc
    omega
  · -- φ = 0
    have hall : ∀ c : steinberg F k n, φ c = 0 := by
      intro c
      have : (c : FlagModule F k n) ∈ W := by rw [h]; exact c.2
      obtain ⟨c', hc', hcc'⟩ := this
      have : c' = c := Subtype.ext hcc'
      rw [← this]
      exact LinearMap.mem_ker.1 hc'
    have : e w = 0 := LinearMap.ext hall
    exact e.injective (this.trans (map_zero e).symm)

end MartinPhd

end
end HSigmaInv

section ExpAssembly

/-!
## Assembly of `H•(e)` (Corollary 1.27, second half)

* `n ≥ 2`: `E₁^{n,n}(e) = Hom_{GL}(1, HΣ_n^n)` vanishes (no invariants), so `Hⁿ(e) = 0`
  (Lemma 1.25 and Corollary 1.26 via `H_subsingleton_of_E1`);
* `n = 0, 1`: direct cochain computations.
-/

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section
namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

theorem exp_E1_subsingleton [CharZero k] (n : ℕ)
    (hinv : ∀ w : HSigma F k n n, (∀ g, hsigmaRep F k n n g w = w) → w = 0) :
    Subsingleton (E (EBicomod.exp (F := F) (k := k)) 1 (n : ℤ) n) := by
  obtain ⟨e⟩ := (lemma_1_25 (EBicomod.exp (F := F) (k := k))
    (GLSpecies.isRelativelyProjective_of_charZero _) n n).1
  haveI : Subsingleton (equivariantHom ((EBicomod.exp (F := F) (k := k)).X.rep n)
      (hsigmaRep F k n n)) := by
    refine ⟨fun f g => ?_⟩
    have key : ∀ f : equivariantHom ((EBicomod.exp (F := F) (k := k)).X.rep n)
        (hsigmaRep F k n n), f = 0 := by
      intro f
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      refine hinv _ fun g => ?_
      have := LinearMap.congr_fun (f.2 g) v
      exact this.symm
    rw [key f, key g]
  exact e.injective.subsingleton

/-- In degree 1 the coboundaries of `e` vanish (degree-0 cochains are cocycles). -/
theorem coboundaries_exp_one :
    coboundaries (EBicomod.exp (F := F) (k := k)) 1 = ⊥ := by
  show (cochains (EBicomod.exp (F := F) (k := k)) 0).map (d (EBicomod.exp) 0) = ⊥
  rw [eq_bot_iff]
  rintro _ ⟨α, hα, rfl⟩
  have : α ∈ cocycles (EBicomod.exp (F := F) (k := k)) 0 := by
    rw [cocycles_exp_zero]; exact hα
  rw [Submodule.mem_bot]
  exact LinearMap.mem_ker.1 this.2

/-- `H¹(e) ≃ Z¹(e)`. -/
def H_exp_one_equiv_cocycles :
    H (EBicomod.exp (F := F) (k := k)) 1 ≃ₗ[k] cocycles (EBicomod.exp (F := F) (k := k)) 1 := by
  have hp : (coboundaries (EBicomod.exp (F := F) (k := k)) 1).comap
      (cocycles (EBicomod.exp (F := F) (k := k)) 1).subtype = ⊥ := by
    rw [coboundaries_exp_one, Submodule.comap_bot, Submodule.ker_subtype]
  exact Submodule.quotEquivOfEqBot _ hp

/-- Evaluation of a raw cochain of `e` at the unit vector of `V` and the flag `G`. -/
def evAt (V : FGModuleCat.{0} F) (G : Flag F V) :
    cocycles (EBicomod.exp (F := F) (k := k)) 1 →ₗ[k] k where
  toFun α := α.1 V (expUnit V) G
  map_add' α β := rfl
  map_smul' c α := rfl

/-- If evaluation at a fixed `(V₁, G₁)` is injective on degree-1 cocycles and there is a
nonzero cocycle, then `Z¹(e)` is one-dimensional. -/
theorem finrank_cocycles_exp_one_of (V₁ : FGModuleCat.{0} F) (G₁ : Flag F V₁)
    (hinj : ∀ α ∈ cocycles (EBicomod.exp (F := F) (k := k)) 1,
      α V₁ (expUnit V₁) G₁ = 0 → α = 0)
    (α₀ : RawCochain (EBicomod.exp (F := F) (k := k)))
    (hα₀ : α₀ ∈ cocycles (EBicomod.exp (F := F) (k := k)) 1) (hne : α₀ ≠ 0) :
    finrank k (cocycles (EBicomod.exp (F := F) (k := k)) 1) = 1 := by
  have hinj' : Function.Injective (evAt (F := F) (k := k) V₁ G₁) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro α hα
    exact Subtype.ext (hinj α.1 α.2 hα)
  haveI : Module.Finite k (cocycles (EBicomod.exp (F := F) (k := k)) 1) :=
    Module.Finite.of_injective _ hinj'
  have hle : finrank k (cocycles (EBicomod.exp (F := F) (k := k)) 1) ≤ finrank k k :=
    LinearMap.finrank_le_finrank_of_injective hinj'
  have hpos : 0 < finrank k (cocycles (EBicomod.exp (F := F) (k := k)) 1) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨α₀, hα₀⟩, fun h => hne (congrArg Subtype.val h)⟩
  rw [Module.finrank_self] at hle
  omega

/-- A degree-1 cocycle of `e` vanishing at a one-dimensional space is zero. -/
theorem exp_cocycle_eq_zero (V₁ : FGModuleCat.{0} F) (hV₁ : finrank F V₁ = 1) (G₁ : Flag F V₁)
    (hG₁ : G₁.len = 1) (α : RawCochain (EBicomod.exp (F := F) (k := k)))
    (hα : α ∈ cocycles (EBicomod.exp (F := F) (k := k)) 1)
    (h : α V₁ (expUnit V₁) G₁ = 0) : α = 0 := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  by_cases hG : G.len = 1
  · have := exp_cocycle_vanishes hα V₁ hV₁ G₁ hG₁ h (finrank F V) V rfl G hG
    show α V z G = 0
    rw [ExpD.rawCochain_exp_apply α V (show k from z) G]
    show (show k from z) * α V 1 G = 0
    rw [this, mul_zero]
  · exact hα.1.1 V z G hG

/-- The second half of Corollary 1.27: `H•(e)` has dimension `1` in degrees `0` and `1`
and vanishes above (characteristic `0`). It follows from Lemma 1.25 and the convergence
Corollary 1.26: `E₁^{p,p}(e) = Hom_{GL(Fᵖ)}(1, Stₚ^*)` is `k` for `p ≤ 1` and `0` for `p ≥ 2`. -/
theorem finrank_H_exp [CharZero k] (n : ℕ) :
    finrank k (H (EBicomod.exp (F := F) (k := k)) n) = (if n ≤ 1 then 1 else 0) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact finrank_H_exp_zero
    · let V₁ : FGModuleCat.{0} F := FGModuleCat.of F F
      have hne : (⊥ : Submodule F V₁) ≠ ⊤ := bot_ne_top
      have hG₁ : (Flag.trivial : Flag F V₁).len = 1 :=
        len_eq_one_of_pair _ (fun B hB => by
          simp only [Flag.trivial, Finset.mem_insert, Finset.mem_singleton] at hB; exact hB) hne
      have hV₁ : finrank F V₁ = 1 := Module.finrank_self F
      have hcoc : finrank k (cocycles (EBicomod.exp (F := F) (k := k)) 1) = 1 :=
        finrank_cocycles_exp_one_of V₁ Flag.trivial
          (fun α hα h => exp_cocycle_eq_zero V₁ hV₁ Flag.trivial hG₁ α hα h)
          expDimCochain expDimCochain_cocycle expDimCochain_ne_zero
      rw [(H_exp_one_equiv_cocycles (F := F) (k := k)).finrank_eq, hcoc]
      rfl
  · have hinv : ∀ w : HSigma F k n n, (∀ g, hsigmaRep F k n n g w = w) → w = 0 :=
      fun w hw => hsigma_invariant_eq_zero n hn w hw
    haveI := H_subsingleton_of_E1 (EBicomod.exp (F := F) (k := k))
      (GLSpecies.isRelativelyProjective_of_charZero _) n (exp_E1_subsingleton n hinv)
    rw [Module.finrank_zero_of_subsingleton, if_neg (by omega)]
/-- **Corollary 1.27.** In characteristic `0`, `H•(1) ≅ k`, concentrated in degree `0`, and
`H•(e)` is `k` in each of the degrees `0` and `1`.

**Gap (error).** The thesis claims `H•(e) ≅ k` concentrated in degree `0`, arguing that the
Steinberg module `Stₚ` is trivial only for `p = 0`. But `St₁` is the trivial one-dimensional
module (`dim Stₚ = |F|^{C(p,2)}`), so `E₁^{1,1}(e) ≅ k`, and it survives since `E₁^{0,0}(e)`
is the only other nonzero term. Directly: degree-1 cochains of `e` are the families
`(α_d)_{d ≥ 1}` (natural in `V`, so depending only on `dim V`), the differential is
`dα_{a,d} = α_{d-a} - α_d + α_a`, and the cocycles `α_d = d·α₁` are not coboundaries, since
`d` vanishes on degree-0 cochains. So `H¹(e) ≅ k`. We formalize the corrected statement. -/
theorem cor_1_27 [CharZero k] (n : ℕ) :
    finrank k (H (EBicomod.unit (F := F) (k := k)) n) = (if n = 0 then 1 else 0) ∧
    finrank k (H (EBicomod.exp (F := F) (k := k)) n) = (if n ≤ 1 then 1 else 0) :=
  ⟨finrank_H_unit n, finrank_H_exp n⟩



end MartinPhd

end
end ExpAssembly

section Sch

open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

/-! ## Step sums over flags, and their behaviour under monotone images (for Lemma 1.29) -/

section StepSum

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- `∑_{i < len H} g(Hᵢ, H_{i+1})`. -/
def Flag.stepSum {M : Type*} [AddCommMonoid M] (H : Flag K V)
    (g : Submodule K V → Submodule K V → M) : M :=
  ∑ i ∈ Finset.range H.len, g (H.nth i) (H.nth (i + 1))

theorem tele_sum {M : Type*} [AddCommMonoid M] (r : ℕ → ℕ) (f : ℕ → M) (N : ℕ) (h0 : r 0 = 0)
    (hstep : ∀ i < N, r (i + 1) = r i ∨ r (i + 1) = r i + 1) :
    ∑ i ∈ Finset.range N, (if r (i + 1) = r i + 1 then f (r i) else 0) =
      ∑ j ∈ Finset.range (r N), f j := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih (fun i hi => hstep i (by omega))]
    rcases hstep N (by omega) with h | h
    · have : ¬ r (N + 1) = r N + 1 := by omega
      rw [ite_eq_right this, h]; simp
    · rw [ite_eq_left h, h, Finset.sum_range_succ]

theorem Flag.index_mono (H : Flag K V) {A B : Submodule K V} (hA : A ∈ H.carrier)
    (hB : B ∈ H.carrier) (h : A ≤ B) : H.index A ≤ H.index B := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · exact (H.index_lt_index hA hB hlt).le

theorem Flag.stepSum_image {M : Type*} [AddCommMonoid M] (H : Flag K V) (K' : Flag K W)
    (φ : Submodule K V → Submodule K W) (hφ : Monotone φ) (hbot : φ ⊥ = ⊥) (htop : φ ⊤ = ⊤)
    (hcar : K'.carrier = H.carrier.image φ) (g : Submodule K W → Submodule K W → M)
    (hg : ∀ P, g P P = 0) :
    K'.stepSum g = H.stepSum (fun P Q => g (φ P) (φ Q)) := by
  have hmem : ∀ i, i ≤ H.len → φ (H.nth i) ∈ K'.carrier := fun i hi => by
    rw [hcar]
    exact Finset.mem_image.2 ⟨H.nth i, H.nth_mem' hi, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℕ, ∀ i, r i = K'.index (φ (H.nth i)) := ⟨_, fun _ => rfl⟩
  have hnth : ∀ i, i ≤ H.len → K'.nth (r i) = φ (H.nth i) := fun i hi => by
    rw [hr]; exact K'.nth_index (hmem i hi)
  have hrmono : ∀ i j, i ≤ j → j ≤ H.len → r i ≤ r j := fun i j hij hj => by
    rw [hr, hr]
    exact K'.index_mono (hmem i (by omega)) (hmem j hj)
      (hφ (H.nth_mono hij (by have := H.card_eq_len_succ; omega)))
  have hr0 : r 0 = 0 := by
    rw [hr, H.nth_zero, hbot]
    have : K'.nth 0 = ⊥ := K'.nth_zero
    rw [← this]; exact K'.index_nth (by omega)
  have hrN : r H.len = K'.len := by
    rw [hr, H.nth_len, htop]
    have : K'.nth K'.len = ⊤ := K'.nth_len
    rw [← this]; exact K'.index_nth le_rfl
  have hstep : ∀ i < H.len, r (i + 1) = r i ∨ r (i + 1) = r i + 1 := by
    intro i hi
    have h1 := hrmono i (i + 1) (by omega) (by omega)
    by_contra hcon
    push Not at hcon
    have hm : r i + 1 < K'.carrier.card := by
      have : r (i + 1) < K'.carrier.card := by
        rw [hr]; exact K'.index_lt_card (hmem (i + 1) (by omega))
      omega
    obtain ⟨C, hC, hCi⟩ := K'.exists_index_eq hm
    rw [hcar] at hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.1 hC
    have hDj : D = H.nth (H.index D) := (H.nth_index hD).symm
    have hjl : H.index D ≤ H.len := by
      have := H.index_lt_card hD; have := H.card_eq_len_succ; omega
    rcases le_or_gt (H.index D) i with hj | hj
    · have := hrmono _ _ hj (by omega)
      have e1 : r (H.index D) = K'.index (φ D) := by rw [hr, ← hDj]
      omega
    · have := hrmono (i + 1) (H.index D) hj hjl
      have e1 : r (H.index D) = K'.index (φ D) := by rw [hr, ← hDj]
      omega
  have hdeg : ∀ i < H.len, r (i + 1) = r i → g (φ (H.nth i)) (φ (H.nth (i + 1))) = 0 := by
    intro i hi h
    have hinj := K'.index_injOn (hmem i (by omega)) (hmem (i + 1) hi)
      (by rw [← hr, ← hr]; exact h.symm)
    rw [← hinj]; exact hg _
  unfold Flag.stepSum
  have hL : ∑ j ∈ Finset.range K'.len, g (K'.nth j) (K'.nth (j + 1)) =
      ∑ i ∈ Finset.range H.len, (if r (i + 1) = r i + 1 then
        g (K'.nth (r i)) (K'.nth (r i + 1)) else 0) := by
    rw [tele_sum r (fun j => g (K'.nth j) (K'.nth (j + 1))) H.len hr0 hstep, hrN]
  rw [hL]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  by_cases h : r (i + 1) = r i + 1
  · rw [ite_eq_left h, hnth i (by omega), ← h, hnth (i + 1) hi']
  · rw [ite_eq_right h]
    have : r (i + 1) = r i := (hstep i hi').resolve_right h
    exact (hdeg i hi' this).symm

end StepSum

section SchIdentity

variable {K : Type*} [Field K] {k : Type} [Field k]

/-- The summand of `schVal`. -/
def schG {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U] (k : Type) [Field k]
    (S P Q : Submodule K U) : k :=
  ((finrank K ↥(S ⊓ Q) - finrank K ↥(S ⊓ P) : ℕ) : k) *
    ((finrank K ↥P - finrank K ↥(S ⊓ P) : ℕ) : k)

theorem sch_arith (k : Type) [Field k] (xp xq yP p q : ℕ) (h1 : xp ≤ xq) (h2 : p ≤ q)
    (h3 : xp ≤ yP) :
    ((xq - xp : ℕ) : k) * ((yP - xp : ℕ) : k) -
      (((xq + q) - (xp + p) : ℕ) : k) * (((yP + p) - (xp + p) : ℕ) : k) +
      ((q - p : ℕ) : k) * (((yP + p) - p : ℕ) : k) - ((q - p : ℕ) : k) * (((xp + p) - p : ℕ) : k)
      = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h2
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le h3
  have e1 : xp + s - xp = s := by omega
  have e2 : xp + w - xp = w := by omega
  have e3 : xp + s + (p + t) - (xp + p) = s + t := by omega
  have e4 : xp + w + p - (xp + p) = w := by omega
  have e5 : p + t - p = t := by omega
  have e6 : xp + w + p - p = xp + w := by omega
  have e7 : xp + p - p = xp := by omega
  rw [e1, e2, e3, e4, e5, e6, e7]
  push_cast
  ring

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem sch_identity (A B P Q : Submodule K V) (hAB : A ≤ B) (hPQ : P ≤ Q) :
    schG k (B.map A.mkQ) (P.map A.mkQ) (Q.map A.mkQ) - schG k B P Q + schG k A P Q -
      schG k (A.comap B.subtype) (P.comap B.subtype) (Q.comap B.subtype) = 0 := by
  -- dimension facts
  have hx : ∀ X : Submodule K V, finrank K ↥(B.map A.mkQ ⊓ X.map A.mkQ) +
      finrank K ↥(A ⊓ X) = finrank K ↥(B ⊓ X) := by
    intro X
    have e : B.map A.mkQ ⊓ X.map A.mkQ = ((X ⊔ A) ⊓ B).map A.mkQ := by
      ext y
      simp only [Submodule.mem_inf, Submodule.mem_map]
      constructor
      · rintro ⟨⟨b, hb, rfl⟩, ⟨x, hx, hxb⟩⟩
        refine ⟨b, ⟨?_, hb⟩, rfl⟩
        have hba : b - x ∈ A := by
          rw [← Submodule.ker_mkQ A, LinearMap.mem_ker, map_sub, hxb, sub_self]
        exact Submodule.mem_sup.2 ⟨x, hx, b - x, hba, by abel⟩
      · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
        obtain ⟨x, hx, a, ha, rfl⟩ := Submodule.mem_sup.1 hz1
        refine ⟨⟨_, hz2, rfl⟩, ⟨x, hx, ?_⟩⟩
        have h0 : A.mkQ a = 0 := by rw [← LinearMap.mem_ker, Submodule.ker_mkQ]; exact ha
        rw [map_add, h0, add_zero]
    have h1 := finrank_map_mkQ_add ((X ⊔ A) ⊓ B) A
    have h2 : ((X ⊔ A) ⊓ B) ⊓ A = A := by
      rw [inf_eq_right]; exact le_inf le_sup_right hAB
    have h3 : (X ⊔ A) ⊓ B = A ⊔ (X ⊓ B) := by
      rw [sup_comm X A]; exact sup_inf_assoc_of_le X hAB
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq A (X ⊓ B)
    have h5 : A ⊓ (X ⊓ B) = A ⊓ X := by
      ext x; simp only [Submodule.mem_inf]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hAB h.1⟩⟩
    have h6 : finrank K ↥((X ⊔ A) ⊓ B) = finrank K ↥(A ⊔ (X ⊓ B)) := by rw [h3]
    rw [e]
    rw [h2] at h1
    rw [h5] at h4
    rw [inf_comm B X]
    omega
  have hy : ∀ X : Submodule K V, finrank K ↥(X.map A.mkQ) + finrank K ↥(A ⊓ X) = finrank K ↥X :=
    fun X => by rw [inf_comm]; exact finrank_map_mkQ_add X A
  have hz : ∀ X : Submodule K V, finrank K ↥(A.comap B.subtype ⊓ X.comap B.subtype) =
      finrank K ↥(A ⊓ X) := by
    intro X
    rw [← Submodule.comap_inf, finrank_comap_subtype, ← inf_assoc, inf_eq_right.2 hAB]
  have hw : ∀ X : Submodule K V, finrank K ↥(X.comap B.subtype) = finrank K ↥(B ⊓ X) :=
    fun X => finrank_comap_subtype B X
  have h1 : finrank K ↥(B.map A.mkQ ⊓ P.map A.mkQ) ≤ finrank K ↥(B.map A.mkQ ⊓ Q.map A.mkQ) :=
    Submodule.finrank_mono (inf_le_inf_left _ (Submodule.map_mono hPQ))
  have h2 : finrank K ↥(A ⊓ P) ≤ finrank K ↥(A ⊓ Q) :=
    Submodule.finrank_mono (inf_le_inf_left _ hPQ)
  have h3 : finrank K ↥(B.map A.mkQ ⊓ P.map A.mkQ) ≤ finrank K ↥(P.map A.mkQ) :=
    Submodule.finrank_mono inf_le_right
  unfold schG
  rw [hz, hz, hw]
  rw [← hx P, ← hx Q, ← hy P]
  exact sch_arith k _ _ _ _ _ h1 h2 h3

end SchIdentity

end MartinPhd

end
end Sch

section Base

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §1.9 La cohomología de las especies de banderas -/

section FlagCohomology

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

/-- The **dimension 1-cochain** `dim : Σ → ē`, `dim(V, F, (0, V)) = dim V`. -/
def dimCochain : RawCochain (flagBicomod F k) := fun V =>
  Finsupp.linearCombination k fun _ : Flag F V => fun G : Flag F V =>
    if G.len = 1 then (finrank F V : k) else 0

/-- The linear Schubert statistic (1.19):
`sch(V, F, (0,S,V)) = ∑_{i=1}^{l} dim((S ∩ Fᵢ)/(S ∩ F_{i-1})) · dim(F_{i-1}/(S ∩ F_{i-1}))`,
the analogue of `sch(I, H, S) = #{(i,j) : i ∈ S, j ∉ S, j ≺_H i}` (1.18). -/
def schVal {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (H : Flag F V)
    (S : Submodule F V) : k :=
  ∑ i ∈ Finset.range H.len,
    ((finrank F ↥(S ⊓ H.nth (i + 1)) - finrank F ↥(S ⊓ H.nth i) : ℕ) : k) *
      ((finrank F ↥(H.nth i) - finrank F ↥(S ⊓ H.nth i) : ℕ) : k)

/-- The **Schubert 2-cochain** `sch : Σ → ē^{⊗2}`. -/
def schCochain : RawCochain (flagBicomod F k) := fun V =>
  Finsupp.linearCombination k fun H : Flag F V => fun G : Flag F V =>
    if G.len = 2 then schVal H (G.nth 1) else 0

theorem lin_const_apply {V : Type} [AddCommGroup V] [Module F V] (c : Flag F V → k)
    (z : Flag F V →₀ k) (G : Flag F V) :
    (Finsupp.linearCombination k (fun _ : Flag F V => c)) z G = (z.sum fun _ a => a) * c G := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum]
  simp [Finset.sum_mul, Finsupp.sum]

theorem dimCochain_apply (V : FGModuleCat.{0} F) (z : (flagBicomod F k).X.ev V) (G : Flag F V) :
    dimCochain (F := F) (k := k) V z G =
      (z.sum fun _ a => a) * (if G.len = 1 then (finrank F V : k) else 0) :=
  lin_const_apply (fun G : Flag F V => if G.len = 1 then (finrank F V : k) else 0) z G

theorem sum_lmapDomain {α β : Type*} (f : α → β) (z : α →₀ k) :
    ((Finsupp.lmapDomain k k f z).sum fun _ a => a) = z.sum fun _ a => a := by
  rw [Finsupp.lmapDomain_apply]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem dimCochain_mem_cochains : dimCochain (F := F) (k := k) ∈ cochains (flagBicomod F k) 1 := by
  refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
  · rw [dimCochain_apply, if_neg hG, mul_zero]
  · rw [dimCochain_apply, dimCochain_apply, Flag.len_map]
    have hz : (Finsupp.sum (show Flag F W →₀ k from (flagBicomod F k).X.mapEquiv e z)
        (fun _ a => a)) = Finsupp.sum (show Flag F V →₀ k from z) (fun _ a => a) :=
      sum_lmapDomain _ z
    erw [hz]
    have : finrank F W = finrank F V := (LinearEquiv.finrank_eq e).symm
    rw [this]

theorem nth_one_proper {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = 2) :
    G.nth 1 ≠ ⊥ ∧ G.nth 1 ≠ ⊤ := Flag.nth_ne_bot_top G ⟨by omega, by omega⟩

theorem faceSum_len2 {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X]
    (G : Flag F V) (hG : G.len = 2) (γ : X →ₗ[k] (Flag F V → k)) (z : X) :
    faceSum X G γ z = -γ z (G.erase (G.nth 1) (nth_one_proper G hG)) := by
  unfold faceSum
  rw [LinearMap.sum_apply, Finset.sum_eq_single (G.nth 1)]
  · rw [dif_pos (nth_one_proper G hG), Flag.index_nth G (by omega)]
    simp
  · intro A hA hne
    by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
    · exfalso
      apply hne
      have hi := G.nth_index hA
      have hlt : G.index A < 3 := by
        have := G.index_lt_card hA
        have := G.card_eq_len_succ
        omega
      have h0 : G.index A ≠ 0 := fun h0 => h.1 (by rw [← hi, h0, G.nth_zero])
      have h2 : G.index A ≠ 2 := fun h2 => h.2 (by rw [← hi, h2, ← hG, G.nth_len])
      have : G.index A = 1 := by omega
      rw [← hi, this]
    · rw [dif_neg h]; rfl
  · intro hn
    exact absurd (Flag.nth_mem' G (by omega)) hn

theorem dimCochain_cocycle : dimCochain (F := F) (k := k) ∈ cocycles (flagBicomod F k) 1 := by
  refine ⟨dimCochain_mem_cochains, LinearMap.mem_ker.2 ?_⟩
  funext V
  apply LinearMap.ext
  intro z
  funext G
  show dRaw (flagBicomod F k) 1 dimCochain V z G = 0
  have e1 : dRaw (flagBicomod F k) 1 dimCochain V z G =
      (if G.len = 1 + 1 then
        (LinearMap.proj (G.project (G.nth 1)) ∘ₗ dimCochain (quo (G.nth 1)) ∘ₗ
          (flagBicomod F k).proj V (G.nth 1)) +
          faceSum _ G (dimCochain (F := F) (k := k) V) +
        ((-1 : k) ^ (1 + 1)) • (LinearMap.proj (G.restrict (G.nth 1)) ∘ₗ
          dimCochain (sub (G.nth 1)) ∘ₗ (flagBicomod F k).res V (G.nth 1))
      else 0) z := rfl
  rw [e1]
  by_cases hG : G.len = 1 + 1
  · rw [if_pos hG]
    have hG2 : G.len = 2 := hG
    erw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply]
    rw [faceSum_len2 _ G hG2]
    set S := G.nth 1 with hS
    set ε : k := Finsupp.sum (show Flag F V →₀ k from z) (fun _ a => a) with hε
    have hl1 : (G.project S).len = 1 := by
      rw [Flag.len_project G (by omega) S hS.symm]; omega
    have hl3 : (G.restrict S).len = 1 := by
      rw [Flag.len_restrict G (by omega) S (by rw [hS]; congr 1; omega)]; omega
    have hlf : (G.erase S (nth_one_proper G hG2)).len = 1 := by
      have h1 := (G.erase S (nth_one_proper G hG2)).card_eq_len_succ
      have h2 := G.card_eq_len_succ
      have h3 : (G.erase S (nth_one_proper G hG2)).carrier.card + 1 = G.carrier.card :=
        Finset.card_erase_add_one (Flag.nth_mem' G (by omega))
      omega
    have t1 : dimCochain (F := F) (k := k) (quo S)
        ((flagBicomod F k).proj V S z) (G.project S) = ε * (finrank F (V ⧸ S) : k) := by
      rw [dimCochain_apply, if_pos hl1]
      have : Finsupp.sum (show Flag F (quo S) →₀ k from (flagBicomod F k).proj V S z)
          (fun _ a => a) = ε := sum_lmapDomain _ z
      erw [this]
    have t3 : dimCochain (F := F) (k := k) (sub S)
        ((flagBicomod F k).res V S z) (G.restrict S) = ε * (finrank F S : k) := by
      rw [dimCochain_apply, if_pos hl3]
      have : Finsupp.sum (show Flag F (sub S) →₀ k from (flagBicomod F k).res V S z)
          (fun _ a => a) = ε := sum_lmapDomain _ z
      erw [this]
    have tf : dimCochain (F := F) (k := k) V z (G.erase S (nth_one_proper G hG2)) =
        ε * (finrank F V : k) := by
      rw [dimCochain_apply, if_pos hlf]
    have hdim : (finrank F (V ⧸ S) : k) + finrank F S = finrank F V := by
      have := congrArg (Nat.cast : ℕ → k) S.finrank_quotient_add_finrank
      push_cast at this
      exact this
    change dimCochain (quo S) ((flagBicomod F k).proj V S z) (G.project S) +
        -dimCochain V z (G.erase S (nth_one_proper G hG2)) +
        (-1 : k) ^ (1 + 1) * dimCochain (sub S) ((flagBicomod F k).res V S z) (G.restrict S) = 0
    rw [t1, t3, tf]
    linear_combination ε * hdim
  · rw [if_neg hG]; rfl

theorem flag_subsingleton {W : Type} [AddCommGroup W] [Module F W] [Subsingleton W] :
    Subsingleton (Flag F W) := by
  haveI : Subsingleton (Submodule F W) := ⟨fun A B => by
    rw [Submodule.eq_bot_of_subsingleton (p := A), Submodule.eq_bot_of_subsingleton (p := B)]⟩
  exact ⟨fun G H => Flag.ext (by
    ext A; simp [Subsingleton.elim A ⊥, G.bot_mem, H.bot_mem])⟩

theorem mapDomain_subsingleton {α β : Type*} [Subsingleton β] (f : α → β) (z : α →₀ k) (H : β) :
    Finsupp.mapDomain f z = Finsupp.single H (z.sum fun _ a => a) := by
  rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.sum]
  have h : ∀ a, (Finsupp.single (f a) (z a) : β →₀ k) = Finsupp.single H (z a) := fun a => by
    rw [Subsingleton.elim (f a) H]
  simp only [h]
  exact (map_sum (Finsupp.singleAddHom H) (fun a => z a) z.support).symm

theorem key_zero {β : RawCochain (flagBicomod F k)} (hβ : β ∈ cochains (flagBicomod F k) 0)
    (V : FGModuleCat.{0} F) (z : (flagBicomod F k).X.ev V) (G : Flag F V) :
    β (quo (⊤ : Submodule F V)) ((flagBicomod F k).proj V ⊤ z) (G.project ⊤) =
      β (sub (⊥ : Submodule F V)) ((flagBicomod F k).res V ⊥ z) (G.restrict ⊥) := by
  haveI h1 : Subsingleton (V ⧸ (⊤ : Submodule F V)) := ⟨fun a b => by
    induction a using Submodule.Quotient.induction_on with | H a => ?_
    induction b using Submodule.Quotient.induction_on with | H b => ?_
    exact (Submodule.Quotient.eq _).2 trivial⟩
  haveI h2 : Subsingleton (↥(⊥ : Submodule F V)) := inferInstance
  haveI : Subsingleton (Flag F (V ⧸ (⊤ : Submodule F V))) := flag_subsingleton
  haveI : Subsingleton (Flag F (↥(⊥ : Submodule F V))) := flag_subsingleton
  let e : (quo (⊤ : Submodule F V)) ≃ₗ[F] (sub (⊥ : Submodule F V)) :=
    LinearEquiv.ofSubsingleton _ _
  have hnat := hβ.2 (quo ⊤) (sub ⊥) e ((flagBicomod F k).proj V ⊤ z) (G.project ⊤)
  rw [← hnat]
  have hflag : (G.project ⊤).map e = G.restrict ⊥ := Subsingleton.elim _ _
  have hz : (flagBicomod F k).X.mapEquiv e ((flagBicomod F k).proj V ⊤ z) =
      (flagBicomod F k).res V ⊥ z := by
    change Finsupp.mapDomain (Flag.map e) (Finsupp.mapDomain (fun G : Flag F V => G.project ⊤)
        (z : Flag F V →₀ k)) = Finsupp.mapDomain (fun G : Flag F V => G.restrict ⊥) (z : Flag F V →₀ k)
    set z' : Flag F V →₀ k := z with hz'
    rw [mapDomain_subsingleton (Flag.map e) _ (G.restrict ⊥),
      mapDomain_subsingleton (fun G : Flag F V => G.restrict ⊥) z' (G.restrict ⊥),
      mapDomain_subsingleton (fun G : Flag F V => G.project ⊤) z' (G.project ⊤),
      Finsupp.sum_single_index rfl]
  rw [hz, hflag]

theorem faceSum_len1 {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X]
    (G : Flag F V) (hG : G.len = 1) (γ : X →ₗ[k] (Flag F V → k)) : faceSum X G γ = 0 := by
  unfold faceSum
  refine Finset.sum_eq_zero fun A hA => ?_
  have hi := G.nth_index hA
  have hlt : G.index A < 2 := by
    have := G.index_lt_card hA
    have := G.card_eq_len_succ
    omega
  have : ¬ (A ≠ ⊥ ∧ A ≠ ⊤) := by
    rintro ⟨h0, h2⟩
    have : G.index A = 0 ∨ G.index A = 1 := by omega
    rcases this with h | h
    · exact h0 (by rw [← hi, h, G.nth_zero])
    · exact h2 (by rw [← hi, h, ← hG, G.nth_len])
  rw [dif_neg this]

theorem dRaw_zero_len1 {β : RawCochain (flagBicomod F k)} (hβ : β ∈ cochains (flagBicomod F k) 0)
    (V : FGModuleCat.{0} F) (z : (flagBicomod F k).X.ev V) (G : Flag F V) (hG : G.len = 1) :
    dRaw (flagBicomod F k) 0 β V z G = 0 := by
  have e1 : dRaw (flagBicomod F k) 0 β V z G =
      (if G.len = 0 + 1 then
        (LinearMap.proj (G.project (G.nth 1)) ∘ₗ β (quo (G.nth 1)) ∘ₗ
          (flagBicomod F k).proj V (G.nth 1)) +
          faceSum _ G (β V) +
        ((-1 : k) ^ (0 + 1)) • (LinearMap.proj (G.restrict (G.nth 0)) ∘ₗ
          β (sub (G.nth 0)) ∘ₗ (flagBicomod F k).res V (G.nth 0))
      else 0) z := rfl
  rw [e1, if_pos (by omega)]
  erw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [faceSum_len1 _ G hG]
  have hS : G.nth 1 = ⊤ := by rw [← hG, G.nth_len]
  have hT : G.nth 0 = ⊥ := G.nth_zero
  have key : ∀ S T : Submodule F V, S = ⊤ → T = ⊥ →
      β (quo S) ((flagBicomod F k).proj V S z) (G.project S) +
        (-1 : k) ^ (0 + 1) * β (sub T) ((flagBicomod F k).res V T z) (G.restrict T) = 0 := by
    intro S T hS hT
    subst hS hT
    rw [key_zero hβ]; ring
  have := key _ _ hS hT
  erw [LinearMap.zero_apply, add_zero]
  exact this

/-- **Lemma 1.28.** `dim` is a 1-cocycle that is not a coboundary. -/
theorem lemma_1_28 :
    dimCochain (F := F) (k := k) ∈ cocycles (flagBicomod F k) 1 ∧
    dimCochain (F := F) (k := k) ∉ coboundaries (flagBicomod F k) 1 := by
  refine ⟨dimCochain_cocycle, ?_⟩
  rintro ⟨β, hβ, hd⟩
  obtain ⟨V, hV⟩ : ∃ V : FGModuleCat.{0} F, finrank F V = 1 :=
    ⟨FGModuleCat.of F F, by simp [FGModuleCat.of]⟩
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hne : (⊥ : Submodule F V) ≠ ⊤ := bot_ne_top
  let G : Flag F V :=
    { carrier := {⊥, ⊤}
      isChain := by
        intro a ha b hb _
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
      bot_mem := by simp
      top_mem := by simp }
  have hG : G.len = 1 := by
    show ({⊥, ⊤} : Finset (Submodule F V)).card - 1 = 1
    rw [Finset.card_pair hne]
  let z : (flagBicomod F k).X.ev V := Finsupp.single G 1
  have h1 : dRaw (flagBicomod F k) 0 β V z G = 0 := dRaw_zero_len1 hβ V z G hG
  have h2 : dimCochain (F := F) (k := k) V z G = 1 := by
    rw [dimCochain_apply, if_pos hG]
    have : Finsupp.sum (show Flag F V →₀ k from z) (fun _ a => a) = 1 := by
      show Finsupp.sum (Finsupp.single G (1 : k)) (fun _ a => a) = 1
      rw [Finsupp.sum_single_index rfl]
    erw [this]
    rw [hV]; simp
  have h3 : d (flagBicomod F k) 0 β V z G = dimCochain (F := F) (k := k) V z G := by
    rw [hd]
  have h4 : d (flagBicomod F k) 0 β V z G = 0 := h1
  rw [h4, h2] at h3
  exact zero_ne_one h3

theorem schVal_eq_stepSum {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : Flag F V) (S : Submodule F V) : schVal (k := k) H S = H.stepSum (schG k S) := rfl

theorem schCochain_single (V : FGModuleCat.{0} F) (H K : Flag F V) :
    schCochain (F := F) (k := k) V (Finsupp.single H (1 : k)) K =
      if K.len = 2 then schVal H (K.nth 1) else 0 := by
  have h : schCochain (F := F) (k := k) V (Finsupp.single H (1 : k)) K =
      (Finsupp.linearCombination k (fun H : Flag F V => fun G : Flag F V =>
        if G.len = 2 then schVal (k := k) H (G.nth 1) else 0)) (Finsupp.single H (1 : k)) K := rfl
  rw [h, Finsupp.linearCombination_single, one_smul]

theorem proj_single (V : FGModuleCat.{0} F) (S : Submodule F V) (H : Flag F V) :
    ((flagBicomod F k).proj V S (Finsupp.single H (1 : k) : (flagBicomod F k).X.ev V) :
        (flagBicomod F k).X.ev (quo S)) = Finsupp.single (H.project S) 1 := by
  show Finsupp.lmapDomain k k _ (Finsupp.single H (1 : k)) = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem res_single (V : FGModuleCat.{0} F) (S : Submodule F V) (H : Flag F V) :
    ((flagBicomod F k).res V S (Finsupp.single H (1 : k) : (flagBicomod F k).X.ev V) :
        (flagBicomod F k).X.ev (sub S)) = Finsupp.single (H.restrict S) 1 := by
  show Finsupp.lmapDomain k k _ (Finsupp.single H (1 : k)) = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem faceSum_len3 {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X]
    (G : Flag F V) (hG : G.len = 3) (γ : X →ₗ[k] (Flag F V → k)) (z : X) :
    faceSum X G γ z = -γ z (G.eraseAt 1) + γ z (G.eraseAt 2) := by
  have hp1 : 0 < 1 ∧ 1 < G.len := ⟨by omega, by omega⟩
  have hp2 : 0 < 2 ∧ 2 < G.len := ⟨by omega, by omega⟩
  unfold faceSum
  rw [LinearMap.sum_apply]
  have hmem1 := Flag.nth_mem' G (p := 1) (by omega)
  have hmem2 := Flag.nth_mem' G (p := 2) (by omega)
  have hne : G.nth 1 ≠ G.nth 2 :=
    (G.nth_lt_nth (by omega) (by have := G.card_eq_len_succ; omega)).ne
  have hpr1 := Flag.nth_ne_bot_top G hp1
  have hpr2 := Flag.nth_ne_bot_top G hp2
  rw [Finset.sum_eq_add_of_mem (G.nth 1) (G.nth 2) hmem1 hmem2 hne]
  · rw [dif_pos hpr1, dif_pos hpr2, Flag.index_nth G (by omega), Flag.index_nth G (by omega)]
    have e1 : G.erase (G.nth 1) hpr1 = G.eraseAt 1 := by
      unfold Flag.eraseAt; rw [dif_pos hp1]
    have e2 : G.erase (G.nth 2) hpr2 = G.eraseAt 2 := by
      unfold Flag.eraseAt; rw [dif_pos hp2]
    rw [e1, e2]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
    norm_num
  · intro A hA hA'
    by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
    · exfalso
      have hi := G.nth_index hA
      have hlt : G.index A < 4 := by
        have := G.index_lt_card hA; have := G.card_eq_len_succ; omega
      have h0 : G.index A ≠ 0 := fun h0 => h.1 (by rw [← hi, h0, G.nth_zero])
      have h3 : G.index A ≠ 3 := fun h3 => h.2 (by rw [← hi, h3, ← hG, G.nth_len])
      have : G.index A = 1 ∨ G.index A = 2 := by omega
      rcases this with h1 | h2
      · exact hA'.1 (by rw [← hi, h1])
      · exact hA'.2 (by rw [← hi, h2])
    · rw [dif_neg h]; rfl

theorem dsch_single (V : FGModuleCat.{0} F) (H G : Flag F V) :
    dRaw (flagBicomod F k) 2 schCochain V (Finsupp.single H (1 : k)) G = 0 := by
  have e1 : dRaw (flagBicomod F k) 2 schCochain V (Finsupp.single H (1 : k)) G =
      (if G.len = 2 + 1 then
        (LinearMap.proj (G.project (G.nth 1)) ∘ₗ schCochain (quo (G.nth 1)) ∘ₗ
          (flagBicomod F k).proj V (G.nth 1)) +
          faceSum _ G (schCochain (F := F) (k := k) V) +
        ((-1 : k) ^ (2 + 1)) • (LinearMap.proj (G.restrict (G.nth 2)) ∘ₗ
          schCochain (sub (G.nth 2)) ∘ₗ (flagBicomod F k).res V (G.nth 2))
      else 0) (Finsupp.single H (1 : k)) := rfl
  rw [e1]
  by_cases hG : G.len = 2 + 1
  · rw [if_pos hG]
    have hG3 : G.len = 3 := hG
    erw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply]
    erw [faceSum_len3 _ G hG3]
    set A := G.nth 1 with hA
    set B := G.nth 2 with hB
    have hAB : A ≤ B := G.nth_mono (by omega) (by have := G.card_eq_len_succ; omega)
    have hp1 : 0 < 1 ∧ 1 < G.len := ⟨by omega, by omega⟩
    have hp2 : 0 < 2 ∧ 2 < G.len := ⟨by omega, by omega⟩
    -- the four pieces
    have l0 : (G.project A).len = 2 := by
      rw [Flag.len_project G (by omega) A hA.symm]; omega
    have n0 : (G.project A).nth 1 = B.map A.mkQ := by
      rw [Flag.nth_project G (by omega) A hA.symm (by omega)]
    have l3 : (G.restrict B).len = 2 := by
      rw [Flag.len_restrict G (by omega) B (by rw [hB]; congr 1; omega)]; omega
    have n3 : (G.restrict B).nth 1 = A.comap B.subtype := by
      rw [Flag.nth_restrict G (by omega) B (by rw [hB]; congr 1; omega) (by omega)]
    have l1 : (G.eraseAt 1).len = 2 := by rw [Flag.len_eraseAt G hp1]; omega
    have n1 : (G.eraseAt 1).nth 1 = B := by
      rw [Flag.nth_eraseAt G hp1 (by omega)]; simp [hB]
    have l2 : (G.eraseAt 2).len = 2 := by rw [Flag.len_eraseAt G hp2]; omega
    have n2 : (G.eraseAt 2).nth 1 = A := by
      rw [Flag.nth_eraseAt G hp2 (by omega)]; simp [hA]
    have t0 : schCochain (F := F) (k := k) (quo A) ((flagBicomod F k).proj V A
        (Finsupp.single H (1 : k))) (G.project A) = schVal (H.project A) (B.map A.mkQ) := by
      rw [proj_single, schCochain_single, if_pos l0, n0]
    have t3 : schCochain (F := F) (k := k) (sub B) ((flagBicomod F k).res V B
        (Finsupp.single H (1 : k))) (G.restrict B) = schVal (H.restrict B) (A.comap B.subtype) := by
      rw [res_single, schCochain_single, if_pos l3, n3]
    have t1 : schCochain (F := F) (k := k) V (Finsupp.single H (1 : k)) (G.eraseAt 1) =
        schVal H B := by rw [schCochain_single, if_pos l1, n1]
    have t2 : schCochain (F := F) (k := k) V (Finsupp.single H (1 : k)) (G.eraseAt 2) =
        schVal H A := by rw [schCochain_single, if_pos l2, n2]
    have hP : schVal (H.project A) (B.map A.mkQ) =
        H.stepSum (fun P Q => schG k (B.map A.mkQ) (P.map A.mkQ) (Q.map A.mkQ)) := by
      rw [schVal_eq_stepSum]
      exact Flag.stepSum_image H (H.project A) (Submodule.map A.mkQ)
        (fun _ _ h => Submodule.map_mono h) (Submodule.map_bot _)
        (by rw [Submodule.map_top, Submodule.range_mkQ]) rfl _ (fun P => by simp [schG])
    have hR : schVal (H.restrict B) (A.comap B.subtype) =
        H.stepSum (fun P Q => schG k (A.comap B.subtype) (P.comap B.subtype) (Q.comap B.subtype)) := by
      rw [schVal_eq_stepSum]
      exact Flag.stepSum_image H (H.restrict B) (Submodule.comap B.subtype)
        (fun _ _ h => Submodule.comap_mono h) (by simp) (Submodule.comap_top _) rfl _
        (fun P => by simp [schG])
    have key : H.stepSum (fun P Q => schG k (B.map A.mkQ) (P.map A.mkQ) (Q.map A.mkQ)) -
        schVal H B + schVal H A -
        H.stepSum (fun P Q => schG k (A.comap B.subtype) (P.comap B.subtype)
          (Q.comap B.subtype)) = 0 := by
      rw [schVal_eq_stepSum, schVal_eq_stepSum]
      unfold Flag.stepSum
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      exact sch_identity A B _ _ hAB
        (H.nth_mono (by omega) (by have := H.card_eq_len_succ; omega))
    change schCochain (quo A) ((flagBicomod F k).proj V A (Finsupp.single H (1 : k)))
        (G.project A) + (-schCochain V (Finsupp.single H (1 : k)) (G.eraseAt 1) +
        schCochain V (Finsupp.single H (1 : k)) (G.eraseAt 2)) +
        (-1 : k) ^ (2 + 1) • schCochain (sub B) ((flagBicomod F k).res V B
          (Finsupp.single H (1 : k))) (G.restrict B) = 0
    rw [smul_eq_mul, t0, t1, t2, t3, hP, hR]
    linear_combination key
  · rw [if_neg hG]; rfl

theorem dsch_zero (V : FGModuleCat.{0} F) (z : (flagBicomod F k).X.ev V) (G : Flag F V) :
    dRaw (flagBicomod F k) 2 schCochain V z G = 0 := by
  let f : (Flag F V →₀ k) →ₗ[k] (Flag F V → k) := dRaw (flagBicomod F k) 2 schCochain V
  have hf : f = 0 := by
    refine Finsupp.lhom_ext fun H b => ?_
    have : (Finsupp.single H b : Flag F V →₀ k) = b • Finsupp.single H 1 := by simp
    rw [this, map_smul]
    funext G
    have := dsch_single (k := k) V H G
    change f (Finsupp.single H 1) G = 0 at this
    simp [this]
  exact congrFun (LinearMap.congr_fun hf z) G

theorem schVal_map {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (e : V ≃ₗ[F] W) (H : Flag F V)
    (S : Submodule F V) :
    schVal (k := k) (H.map e) (S.map (e : V →ₗ[F] W)) = schVal H S := by
  unfold schVal
  rw [Flag.len_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [Flag.nth_map, Flag.nth_map]
  have hinf : ∀ X : Submodule F V, (S.map (e : V →ₗ[F] W)) ⊓ X.map (e : V →ₗ[F] W) =
      (S ⊓ X).map (e : V →ₗ[F] W) := fun X => (Submodule.map_inf _ e.injective).symm
  have hfin : ∀ X : Submodule F V, finrank F ↥(X.map (e : V →ₗ[F] W)) = finrank F ↥X :=
    fun X => LinearEquiv.finrank_map_eq e X
  rw [hinf, hinf]
  simp only [hfin]

/-- `schCochain` on a bare finitely supported function. -/
def schBare (V : FGModuleCat.{0} F) : (Flag F V →₀ k) →ₗ[k] (Flag F V → k) :=
  Finsupp.linearCombination k fun H : Flag F V => fun G : Flag F V =>
    if G.len = 2 then schVal (k := k) H (G.nth 1) else 0

theorem schBare_single (V : FGModuleCat.{0} F) (H K : Flag F V) (a : k) :
    schBare V (Finsupp.single H a) K = a * (if K.len = 2 then schVal (k := k) H (K.nth 1) else 0) := by
  unfold schBare
  rw [Finsupp.linearCombination_single]
  simp

theorem schBare_natural {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) (z : Flag F V →₀ k)
    (G : Flag F V) :
    schBare W (Finsupp.lmapDomain k k (Flag.map e) z) (G.map e) = schBare V z G := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    rw [hf, hg]
  | single H a =>
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, schBare_single, schBare_single,
      Flag.len_map]
    by_cases hG : G.len = 2
    · simp only [hG, if_true]
      rw [Flag.nth_map, schVal_map]
    · simp [hG]

theorem schBare_eq_zero (V : FGModuleCat.{0} F) (z : Flag F V →₀ k) (G : Flag F V)
    (hG : G.len ≠ 2) : schBare V z G = 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
    rw [hf, hg, add_zero]
  | single H a => rw [schBare_single, if_neg hG, mul_zero]

theorem schCochain_mem_cochains : schCochain (F := F) (k := k) ∈ cochains (flagBicomod F k) 2 :=
  ⟨fun V z G hG => schBare_eq_zero V (z : Flag F V →₀ k) G hG,
   fun V W e z G => schBare_natural e (z : Flag F V →₀ k) G⟩

theorem flag_eq_triv_of_len1 {V : Type} [AddCommGroup V] [Module F V] (G H : Flag F V)
    (hG : G.len = 1) (hH : H.len = 1) : G = H := by
  apply Flag.ext
  rw [G.carrier_eq_image_nth, H.carrier_eq_image_nth, G.card_eq_len_succ, H.card_eq_len_succ,
    hG, hH]
  ext A
  simp only [Finset.mem_image, Finset.mem_range]
  have g0 := G.nth_zero; have g1 : G.nth 1 = ⊤ := by rw [← hG, G.nth_len]
  have h0 := H.nth_zero; have h1 : H.nth 1 = ⊤ := by rw [← hH, H.nth_len]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact ⟨0, by omega, by rw [g0, h0]⟩
    · exact ⟨1, by omega, by rw [g1, h1]⟩
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact ⟨0, by omega, by rw [g0, h0]⟩
    · exact ⟨1, by omega, by rw [g1, h1]⟩

theorem flag_subsingleton_of_finrank_one {W : Type} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (hW : finrank F W = 1) (G H : Flag F W) : G = H := by
  have hmem : ∀ K : Flag F W, ∀ A ∈ K.carrier, A = ⊥ ∨ A = ⊤ := by
    intro K A _
    have h := Submodule.finrank_le A
    rw [hW] at h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
    · left; exact Submodule.finrank_eq_zero.1 h0
    · right; exact Submodule.eq_top_of_finrank_eq (h1.trans hW.symm)
  apply Flag.ext
  ext A
  constructor
  · intro hA
    rcases hmem G A hA with rfl | rfl
    · exact H.bot_mem
    · exact H.top_mem
  · intro hA
    rcases hmem H A hA with rfl | rfl
    · exact G.bot_mem
    · exact G.top_mem

theorem beta_const {β : RawCochain (flagBicomod F k)} (hβ : β ∈ cochains (flagBicomod F k) 1)
    (W W' : FGModuleCat.{0} F) (hW : finrank F W = 1) (hW' : finrank F W' = 1)
    (K₁ K₀ : Flag F W) (K K0 : Flag F W') :
    β W (Finsupp.single K₁ (1 : k)) K₀ = β W' (Finsupp.single K 1) K0 := by
  let e : W ≃ₗ[F] W' := LinearEquiv.ofFinrankEq W W' (hW.trans hW'.symm)
  have hnat := hβ.2 W W' e (Finsupp.single K₁ (1 : k)) K₀
  have hz : (flagBicomod F k).X.mapEquiv e (Finsupp.single K₁ (1 : k)) =
      (Finsupp.single K (1 : k) : (flagBicomod F k).X.ev W') := by
    show Finsupp.lmapDomain k k (Flag.map e) (Finsupp.single K₁ 1) = _
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      flag_subsingleton_of_finrank_one hW' (K₁.map e) K]
  rw [hz, flag_subsingleton_of_finrank_one hW' (K₀.map e) K0] at hnat
  exact hnat.symm

theorem dRaw1_formula {β : RawCochain (flagBicomod F k)} (V : FGModuleCat.{0} F) (H G : Flag F V)
    (hG : G.len = 2) :
    dRaw (flagBicomod F k) 1 β V (Finsupp.single H (1 : k)) G =
      β (quo (G.nth 1)) (Finsupp.single (H.project (G.nth 1)) (1 : k)) (G.project (G.nth 1)) -
        β V (Finsupp.single H (1 : k)) (G.eraseAt 1) +
        β (sub (G.nth 1)) (Finsupp.single (H.restrict (G.nth 1)) (1 : k)) (G.restrict (G.nth 1)) := by
  have e1 : dRaw (flagBicomod F k) 1 β V (Finsupp.single H (1 : k)) G =
      (if G.len = 1 + 1 then
        (LinearMap.proj (G.project (G.nth 1)) ∘ₗ β (quo (G.nth 1)) ∘ₗ
          (flagBicomod F k).proj V (G.nth 1)) +
          faceSum _ G (β V) +
        ((-1 : k) ^ (1 + 1)) • (LinearMap.proj (G.restrict (G.nth 1)) ∘ₗ
          β (sub (G.nth 1)) ∘ₗ (flagBicomod F k).res V (G.nth 1))
      else 0) (Finsupp.single H (1 : k)) := rfl
  rw [e1, if_pos (by omega)]
  erw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply]
  erw [faceSum_len2 _ G hG]
  have hp : 0 < 1 ∧ 1 < G.len := ⟨by omega, by omega⟩
  have e2 : G.erase (G.nth 1) (nth_one_proper G hG) = G.eraseAt 1 := by
    unfold Flag.eraseAt; rw [dif_pos hp]
  rw [e2]
  have h1 := proj_single (k := k) V (G.nth 1) H
  have h2 := res_single (k := k) V (G.nth 1) H
  change β (quo (G.nth 1)) ((flagBicomod F k).proj V (G.nth 1) (Finsupp.single H (1 : k)))
      (G.project (G.nth 1)) + -β V (Finsupp.single H (1 : k)) (G.eraseAt 1) +
      (-1 : k) ^ (1 + 1) * β (sub (G.nth 1)) ((flagBicomod F k).res V (G.nth 1)
        (Finsupp.single H (1 : k))) (G.restrict (G.nth 1)) = _
  rw [h1, h2]
  ring

/-- The geometric description `sch(V, F, (0,S,V)) = inv(d(F, F ∗ S))` for complete `F`
and `0 < S < V`, generalizing [AM10, §10.13].

**Gap (unproved, §1.9).** The thesis states this but does not prove it ("No probaremos aquí
la equivalencia"). -/
theorem schVal_eq_inv_jh {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (n : ℕ) (hn : finrank F V = n) (H : Flag F V) (hH : H.IsComplete) (S : Submodule F V)
    (hS : S ≠ ⊥ ∧ S ≠ ⊤) :
    schVal (k := k) H S = (inv (jh n H (H.convSub S)) : k) := by
  obtain ⟨b, X, hHb, hSb, hconv⟩ := exists_basis_convSub hn H hH S
  have hlen : H.len = n := hH.trans hn
  have hj : jh n H (H.convSub S) = shuffle X := by rw [hconv, hHb, jh_jhFlag]
  subst hHb
  rw [hj, ← sch_nat X]
  push_cast
  unfold schVal
  rw [hlen]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.1 hi
  have h1 : (jhFlag b).nth (i + 1) = b.flag ⟨i + 1, by omega⟩ := jhFlag_nth b ⟨i + 1, by omega⟩
  have h0 : (jhFlag b).nth i = b.flag ⟨i, by omega⟩ := jhFlag_nth b ⟨i, by omega⟩
  rw [h1, h0, hSb, finrank_inf_flag, finrank_inf_flag, finrank_flag']

theorem schVal_basis_line (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (b : Module.Basis (Fin 2) F V) (x : Fin 2) :
    schVal (k := k) (jhFlag b) (Submodule.span F (b '' (({x} : Finset (Fin 2)) : Set (Fin 2)))) =
      (inv (shuffle ({x} : Finset (Fin 2))) : k) := by
  have hn : finrank F V = 2 := by rw [Module.finrank_eq_card_basis b]; simp
  have hH : (jhFlag b).IsComplete := by
    unfold Flag.IsComplete Flag.len; simp [jhFlag_card, hn]
  have hS : Submodule.span F (b '' (({x} : Finset (Fin 2)) : Set (Fin 2))) ≠ ⊥ ∧
      Submodule.span F (b '' (({x} : Finset (Fin 2)) : Set (Fin 2))) ≠ ⊤ := by
    have h1 := finrank_span_basis_image b ({x} : Finset (Fin 2))
    constructor <;> intro h <;> rw [h] at h1 <;> simp [hn] at h1
  rw [schVal_eq_inv_jh 2 hn (jhFlag b) hH _ hS, convSub_jhFlag b hn, jh_jhFlag]

theorem sch_not_coboundary :
    schCochain (F := F) (k := k) ∉ coboundaries (flagBicomod F k) 2 := by
  rintro ⟨β, hβ, hd⟩
  obtain ⟨V, ⟨b⟩⟩ : ∃ V : FGModuleCat.{0} F, Nonempty (Module.Basis (Fin 2) F V) :=
    ⟨FGModuleCat.of F (Fin 2 → F), ⟨Pi.basisFun F (Fin 2)⟩⟩
  have hn : finrank F V = 2 := by rw [Module.finrank_eq_card_basis b]; simp
  set H := jhFlag b with hH
  -- the two flags `(0 < ⟨e_x⟩ < V)`
  have hG : ∀ x : Fin 2, ∃ G : Flag F V, G.len = 2 ∧
      G.nth 1 = Submodule.span F (b '' (({x} : Finset (Fin 2)) : Set (Fin 2))) ∧
      G = jhFlag (b.reindex (shuffle ({x} : Finset (Fin 2))).symm) := by
    intro x
    refine ⟨jhFlag (b.reindex (shuffle ({x} : Finset (Fin 2))).symm), ?_, ?_, rfl⟩
    · have := jhFlag_card (b.reindex (shuffle ({x} : Finset (Fin 2))).symm)
      have h2 := (jhFlag (b.reindex (shuffle ({x} : Finset (Fin 2))).symm)).card_eq_len_succ
      omega
    · rw [show (1 : ℕ) = (⟨1, by omega⟩ : Fin 3).val from rfl, jhFlag_nth, reindex_flag_eq]
      congr 2
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_singleton, Set.mem_singleton_iff]
      constructor
      · rintro ⟨l, hl, rfl⟩
        have h0 : l = 0 := Fin.ext (by simpa using hl)
        subst h0
        have := (shuffle_mem_iff ({x} : Finset (Fin 2)) 0).2 (by simp)
        simpa using this
      · rintro rfl
        refine ⟨0, by simp, ?_⟩
        have := (shuffle_mem_iff ({y} : Finset (Fin 2)) 0).2 (by simp)
        simpa using this
  choose G hGlen hGnth hGeq using hG
  have hline : ∀ x : Fin 2, finrank F ↥(Submodule.span F (b '' (({x} : Finset (Fin 2)) : Set (Fin 2)))) = 1 := by
    intro x; rw [finrank_span_basis_image]; simp
  have hquo : ∀ x : Fin 2, finrank F ↥(quo ((G x).nth 1)) = 1 := by
    intro x
    show finrank F (V ⧸ (G x).nth 1) = 1
    have := Submodule.finrank_quotient_add_finrank ((G x).nth 1)
    rw [hGnth x] at this ⊢
    have := hline x
    omega
  have hsub : ∀ x : Fin 2, finrank F ↥(sub ((G x).nth 1)) = 1 := by
    intro x
    show finrank F ↥((G x).nth 1) = 1
    rw [hGnth x, hline x]
  have hdG : ∀ x : Fin 2, dRaw (flagBicomod F k) 1 β V (Finsupp.single H (1 : k)) (G x) =
      (inv (shuffle ({x} : Finset (Fin 2))) : k) := by
    intro x
    have h1 : dRaw (flagBicomod F k) 1 β V (Finsupp.single H (1 : k)) (G x) =
        schCochain (F := F) (k := k) V (Finsupp.single H (1 : k)) (G x) := by
      have := congrArg (fun f => f V (Finsupp.single H (1 : k)) (G x)) hd
      exact this
    rw [h1, schCochain_single, if_pos (hGlen x), hGnth x, hH, schVal_basis_line]
  have hE : ∀ x : Fin 2, ((G x).eraseAt 1).len = 1 := by
    intro x
    rw [Flag.len_eraseAt _ ⟨by omega, by rw [hGlen x]; omega⟩, hGlen x]
  have hmain : dRaw (flagBicomod F k) 1 β V (Finsupp.single H (1 : k)) (G 0) =
      dRaw (flagBicomod F k) 1 β V (Finsupp.single H (1 : k)) (G 1) := by
    rw [dRaw1_formula V H (G 0) (hGlen 0), dRaw1_formula V H (G 1) (hGlen 1)]
    have e1 := beta_const (k := k) hβ (quo ((G 0).nth 1)) (quo ((G 1).nth 1)) (hquo 0) (hquo 1)
      (H.project ((G 0).nth 1))
      ((G 0).project ((G 0).nth 1)) (H.project ((G 1).nth 1)) ((G 1).project ((G 1).nth 1))
    have e3 := beta_const (k := k) hβ (sub ((G 0).nth 1)) (sub ((G 1).nth 1)) (hsub 0) (hsub 1)
      (H.restrict ((G 0).nth 1)) ((G 0).restrict ((G 0).nth 1)) (H.restrict ((G 1).nth 1))
      ((G 1).restrict ((G 1).nth 1))
    rw [e1, e3, flag_eq_triv_of_len1 ((G 0).eraseAt 1) ((G 1).eraseAt 1) (hE 0) (hE 1)]
  rw [hdG, hdG] at hmain
  have h0 : inv (shuffle ({0} : Finset (Fin 2))) = 0 := by
    rw [inv_shuffle_eq]; simp
  have h1 : inv (shuffle ({1} : Finset (Fin 2))) = 1 := by
    have : (({1} : Finset (Fin 2))ᶜ.filter (· < (1 : Fin 2))) = {0} := by
      ext y; fin_cases y <;> simp
    rw [inv_shuffle_eq, Finset.sum_singleton, this, Finset.card_singleton]
  rw [h0, h1] at hmain
  simp at hmain

/-- **Lemma 1.29.** `sch` is a 2-cocycle that is not a coboundary (the cocycle identity is
the Zassenhaus lemma; non-triviality is checked on two complete flags in `F²`). -/
theorem lemma_1_29 :
    schCochain (F := F) (k := k) ∈ cocycles (flagBicomod F k) 2 ∧
    schCochain (F := F) (k := k) ∉ coboundaries (flagBicomod F k) 2 := by
  refine ⟨⟨schCochain_mem_cochains, LinearMap.mem_ker.2 ?_⟩, sch_not_coboundary⟩
  funext V
  apply LinearMap.ext
  intro z
  funext G
  exact dsch_zero V z G

/-- **Lemma 1.30.** If `X` is a transitive `G`-set and `M_X = k[X]`, evaluation at
`x ∈ X` gives `Hom_G(M_X, N) ≅ N^{Stab x}`. -/
theorem lemma_1_30 {G X N : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommGroup N] [Module k N] (ρ : Representation k G N) (x : X) :
    Set.BijOn (fun f : MonoidAlgebra k X →ₗ[k] N => f (MonoidAlgebra.single x 1))
      (equivariantHom (Representation.ofMulAction k G X) ρ : Set (MonoidAlgebra k X →ₗ[k] N))
      {v | ∀ g ∈ MulAction.stabilizer G x, ρ g v = v} := by
  have hext : ∀ f f' : MonoidAlgebra k X →ₗ[k] N,
      (∀ y, f (MonoidAlgebra.single y 1) = f' (MonoidAlgebra.single y 1)) → f = f' := by
    intro f f' h
    apply MonoidAlgebra.lhom_ext'
    intro y
    apply LinearMap.ext_ring
    simpa using h y
  have hs : ∀ (g : G) (y : X), Representation.ofMulAction k G X g (MonoidAlgebra.single y (1 : k)) =
      MonoidAlgebra.single (g • y) 1 := fun g y => Representation.ofMulAction_single g y 1
  have hcomm : ∀ f : MonoidAlgebra k X →ₗ[k] N,
      f ∈ (equivariantHom (Representation.ofMulAction k G X) ρ : Set (MonoidAlgebra k X →ₗ[k] N)) →
      ∀ (g : G) (y : X), f (MonoidAlgebra.single (g • y) (1 : k)) =
        ρ g (f (MonoidAlgebra.single y 1)) := by
    intro f hf g y
    have := LinearMap.congr_fun (hf g) (MonoidAlgebra.single y 1)
    simp only [LinearMap.comp_apply, hs] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro f hf g hg
    have := hcomm f hf g x
    rw [MulAction.mem_stabilizer_iff.1 hg] at this
    exact this.symm
  · intro f hf f' hf' h
    refine hext f f' fun y => ?_
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
    rw [hcomm f hf g x, hcomm f' hf' g x]
    exact congrArg _ h
  · intro v hv
    choose c hc using fun y : X => MulAction.exists_smul_eq G x y
    let f : MonoidAlgebra k X →ₗ[k] N :=
      (Finsupp.linearCombination k fun y : X => ρ (c y) v) ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
    have hf : ∀ y, f (MonoidAlgebra.single y 1) = ρ (c y) v := fun y => by
      simp [f]
    refine ⟨f, ?_, ?_⟩
    · intro g
      refine hext _ _ fun y => ?_
      show f (Representation.ofMulAction k G X g (MonoidAlgebra.single y 1)) = ρ g (f (MonoidAlgebra.single y 1))
      rw [hs, hf, hf]
      have hst : (c (g • y))⁻¹ * g * c y ∈ MulAction.stabilizer G x := by
        rw [MulAction.mem_stabilizer_iff]
        rw [mul_smul, mul_smul, hc y, inv_smul_eq_iff, hc (g • y)]
      have h1 := hv _ hst
      calc ρ (c (g • y)) v = ρ (c (g • y)) (ρ ((c (g • y))⁻¹ * g * c y) v) := by rw [h1]
        _ = ρ g (ρ (c y) v) := by
          rw [← Module.End.mul_apply, ← map_mul]
          simp [mul_assoc]
    · show f (MonoidAlgebra.single x 1) = v
      rw [hf]
      exact hv (c x) (by rw [MulAction.mem_stabilizer_iff]; exact hc x)

set_option synthInstance.maxHeartbeats 100000 in
/-- `H^p(Σ_p^•)^B`, the `B`-invariants of the top cohomology. -/
def hsigmaFixed (p : ℕ) (Hs : Subgroup (GLn F p)) : Submodule k (HSigma F k p p) where
  carrier := {v | ∀ h ∈ Hs, hsigmaRep F k p p h v = v}
  add_mem' := by
    intro a b ha hb h hh
    rw [map_add, ha h hh, hb h hh]
  zero_mem' := by intro h _; exact map_zero _
  smul_mem' := by
    intro r a ha h hh
    rw [map_smul, ha h hh]

/-- `δ_{σ,p} = ∑_{d(F⁰, F) = σ} e_F`, the indicator of the Schubert cell `BσB` in
`Fl⁺(Fᵖ)` (a top cochain of `Σ_p`, identified with a functional via Proposition 1.8). -/
def deltaElt {p : ℕ} (σ : Equiv.Perm (Fin p)) : FlagModule F k p :=
  ∑ G ∈ Finset.univ.filter (fun G : Flag F (Fin p → F) =>
      G.IsComplete ∧ jh p (stdFlag F p) G = σ), Finsupp.single G 1

theorem deltaElt_apply {p : ℕ} (σ : Equiv.Perm (Fin p)) (G : Flag F (Fin p → F)) :
    deltaElt (k := k) σ G = if G.IsComplete ∧ jh p (stdFlag F p) G = σ then 1 else 0 := by
  classical
  simp [deltaElt, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', eq_comm]

/-- Equation (1.22): pairing a Schubert-cell indicator with the standard apartment cycle. -/
theorem deltaElt_pair_eps {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    flagPairing F k p (deltaElt σ) (epsSteinberg F k p) = (-1 : k) ^ inv σ := by
  change flagBil F k p (deltaElt σ) (epsSteinberg F k p) = _
  simp only [epsSteinberg, map_sum, map_smul]
  have he (τ : Equiv.Perm (Fin p)) :
      flagBil F k p (deltaElt σ) (Finsupp.single (permToGL F τ • stdFlag F p) 1) =
        if τ = σ then 1 else 0 := by
    change flagPairing F k p _ _ = _
    rw [flagPairing_single, deltaElt_apply, jh_perm_smul]
    have hc : (permToGL F τ • stdFlag F p).IsComplete := by
      change ((stdFlag F p).map (permToGL F τ)).IsComplete
      simpa only [Flag.IsComplete, Flag.len_map] using (show (stdFlag F p).IsComplete from by
        rw [Flag.IsComplete, stdFlag_eq_flagOf, ST.len_flagOf, Module.finrank_fin_fun])
    simp [hc]
  simp only [he, smul_eq_mul]
  simp

theorem deltaElt_mem {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    deltaElt (k := k) σ ∈ flagDeg F k p p ⊓ LinearMap.ker (sigmaD F k p) := by
  have hdeg : deltaElt (k := k) σ ∈ flagDeg F k p p := by
    unfold deltaElt
    refine Submodule.sum_mem _ fun G hG => ?_
    have hc := (Finset.mem_filter.1 hG).2.1
    exact Finsupp.single_mem_supported k (1 : k) (show G.len = p from by
      have := hc; unfold Flag.IsComplete at this; rw [this, Module.finrank_fin_fun])
  refine ⟨hdeg, LinearMap.mem_ker.2 ?_⟩
  ext G
  have h1 := (mem_flagDeg_iff F k).1 (sigmaD_mem_flagDeg F k hdeg) G
  by_cases hG : G.len = p + 1
  · exact absurd hG (by
      have := ST.len_le_finrank (F := F) G
      rw [Module.finrank_fin_fun] at this
      omega)
  · simpa using h1 hG

/-- The class `[δ_{σ,p}] ∈ H^p(Σ_p^•)`. -/
def deltaClass {p : ℕ} (σ : Equiv.Perm (Fin p)) : HSigma F k p p :=
  Subquot.mk _ (deltaElt_mem σ)

/-- The cochain `α_k : Σ → ē^{⊗k}`, `α_k(V)(F) = e_F` if `F` is complete and
`dim V = k`, and `0` otherwise. Its class in `E₁^{k,0}(Σ)` is `[δ_{id,k}]`. -/
def alphaCochain (m : ℕ) : RawCochain (flagBicomod F k) := fun V =>
  Finsupp.linearCombination k fun H : Flag F V => fun G : Flag F V =>
    if finrank F V = m ∧ H.IsComplete ∧ G = H then 1 else 0

theorem alpha_lin_apply {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (m : ℕ)
    (z : Flag F V →₀ k) (G : Flag F V) :
    (Finsupp.linearCombination k fun H : Flag F V => fun G : Flag F V =>
        if finrank F V = m ∧ H.IsComplete ∧ G = H then (1 : k) else 0) z G =
      z G * (if finrank F V = m ∧ G.IsComplete then 1 else 0) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
  rw [Finset.sum_eq_single G]
  · by_cases hc : finrank F V = m ∧ G.IsComplete
    · simp [hc]
    · have : ¬ (finrank F V = m ∧ G.IsComplete ∧ G = G) := fun h => hc ⟨h.1, h.2.1⟩
      simp [this, hc]
  · intro H _ hne
    simp [Finsupp.smul_apply, Ne.symm hne]
  · intro hG
    simp [Finsupp.notMem_support_iff.1 hG]

theorem alphaCochain_apply (m : ℕ) (V : FGModuleCat.{0} F) (z : (flagBicomod F k).X.ev V)
    (G : Flag F V) :
    alphaCochain (F := F) (k := k) m V z G =
      (show Flag F V →₀ k from z) G * (if finrank F V = m ∧ G.IsComplete then 1 else 0) :=
  alpha_lin_apply m z G

theorem flag_map_injective {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] (e : V ≃ₗ[F] W) : Function.Injective (Flag.map e) := by
  intro G H h
  have := congrArg (Flag.map e.symm) h
  rwa [← Flag.map_trans, ← Flag.map_trans, LinearEquiv.self_trans_symm, Flag.map_refl,
    Flag.map_refl] at this

theorem lmapDomain_flag_apply {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] (e : V ≃ₗ[F] W) (z : Flag F V →₀ k) (G : Flag F V) :
    (Finsupp.lmapDomain k k (Flag.map e) z) (G.map e) = z G := by
  rw [Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply_of_injective (flag_map_injective e) _ _

theorem alphaCochain_mem_cochains (m : ℕ) :
    alphaCochain (F := F) (k := k) m ∈ cochains (flagBicomod F k) m := by
  refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
  · rw [alphaCochain_apply, if_neg, mul_zero]
    rintro ⟨_, hc⟩
    exact hG (by rw [hc]; assumption)
  · rw [alphaCochain_apply, alphaCochain_apply]
    have hz : (show Flag F W →₀ k from (flagBicomod F k).X.mapEquiv e z) (G.map e) =
        (show Flag F V →₀ k from z) G := lmapDomain_flag_apply e z G
    erw [hz]
    have h1 : finrank F W = finrank F V := (LinearEquiv.finrank_eq e).symm
    have h2 : (G.map e).IsComplete ↔ G.IsComplete := by
      unfold Flag.IsComplete; rw [Flag.len_map, h1]
    simp only [h1, h2]

theorem alphaCochain_mem (m : ℕ) :
    alphaCochain (F := F) (k := k) m ∈ Zpage (flagBicomod F k) 1 m m := by
  have hc := alphaCochain_mem_cochains (F := F) (k := k) m
  refine ⟨(mem_filt_iff _ _ _ _).2 ⟨hc, fun V hV => ?_⟩, ?_⟩
  · apply LinearMap.ext; intro z; funext G
    rw [alphaCochain_apply, if_neg, mul_zero]; rfl
    rintro ⟨h, _⟩
    have : (finrank F V : ℤ) = m := by exact_mod_cast h
    omega
  · refine (mem_filt_iff _ _ _ _).2 ⟨d_mem _ hc, fun V hV => ?_⟩
    apply LinearMap.ext; intro z; funext G
    show dRaw (flagBicomod F k) m (alphaCochain m) V z G = 0
    have : ¬ G.len = m + 1 := by
      intro hG
      have := ST.len_le_finrank (F := F) G
      have hV' : (finrank F V : ℤ) < m + 1 := by simpa using hV
      omega
    have e1 : dRaw (flagBicomod F k) m (alphaCochain m) V z G = (if G.len = m + 1 then
        (LinearMap.proj (G.project (G.nth 1)) ∘ₗ alphaCochain m (quo (G.nth 1)) ∘ₗ
          (flagBicomod F k).proj V (G.nth 1)) +
          faceSum _ G (alphaCochain (F := F) (k := k) m V) +
        ((-1 : k) ^ (m + 1)) • (LinearMap.proj (G.restrict (G.nth m)) ∘ₗ
          alphaCochain m (sub (G.nth m)) ∘ₗ (flagBicomod F k).res V (G.nth m))
      else 0) z := rfl
    rw [e1, if_neg this]; rfl


end FlagCohomology

end MartinPhd

end
end Base
