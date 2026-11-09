import MartinPhd.Chapter1Section7SpectralSequence

/-!
# Chapter 1, Section 1.7 (convergence, unit and exponential cases)

Contents:
* Convergence of the spectral sequence for relatively projective bicomodules (Corollary 1.26)
* UnitPositive
* UnitZero
* UnitCoh
* ExpD
* ExpZero
* The dimension cocycle of the exponential bicomodule
* Injectivity of evaluation on degree-1 cocycles of the exponential bicomodule
-/

section Conv

/-!
## Convergence of the spectral sequence for relatively projective bicomodules (Corollary 1.26)

By Lemma 1.25, `E₁^{p,n}` vanishes for `n ≠ p`. This means that for `n ≠ p`, a cochain
`α ∈ F^p Cⁿ` with `dα ∈ F^{p+1}` is `dβ + γ` with `β ∈ F^p`, `γ ∈ F^{p+1}`. Iterating, and
using that `F^q` vanishes on spaces of dimension `< q` (so the corrections converge pointwise),
gives the collapse and the identification with the associated graded of `H•`.
-/

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section
namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

section Conv

variable (x : EBicomod F k)

theorem filt_eq_cochains (q : ℤ) (n : ℕ) (hq : q ≤ n) : filt x q n = cochains x n := by
  apply le_antisymm inf_le_left
  intro α hα
  refine (mem_filt_iff x q n α).2 ⟨hα, fun V hV => ?_⟩
  apply LinearMap.ext
  intro z
  funext G
  have hlen : G.len ≤ finrank F V := by
    have := ST.len_le_finrank (F := F) G
    exact this
  exact hα.1 V z G (by omega)

/-- `Z_0^p = F^p` (as `d` preserves the filtration). -/
theorem Zpage_zero (p : ℤ) (n : ℕ) : Zpage x 0 p n = filt x p n := by
  apply le_antisymm inf_le_left
  intro α hα
  refine ⟨hα, ?_⟩
  have := (d_filt x p n hα).1
  simpa using this

theorem star_succ_of_sub (m p' : ℕ) (hsub : Subsingleton (E x 1 (p' : ℤ) (m + 1)))
    {α : RawCochain x} (hα : α ∈ filt x (p' : ℤ) (m + 1))
    (hd : d x (m + 1) α ∈ filt x ((p' : ℤ) + 1) (m + 1 + 1)) :
    ∃ β ∈ filt x (p' : ℤ) m, ∃ γ ∈ filt x ((p' : ℤ) + 1) (m + 1), α = d x m β + γ := by
  have hZ : α ∈ Zpage x ((1 : ℕ) : ℤ) (p' : ℤ) (m + 1) := ⟨hα, by simpa using hd⟩
  have h0 : (Subquot.mk α hZ : E x 1 (p' : ℤ) (m + 1)) = 0 := Subsingleton.elim _ _
  have hB : α ∈ Bpage x 1 (p' : ℤ) (m + 1) := by
    have := (Submodule.Quotient.mk_eq_zero _).1 h0
    exact this
  simp only [Bpage] at hB
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1 hB
  obtain ⟨β, hβ, rfl⟩ := ha
  have e1 : ((1 : ℕ) : ℤ) - 1 = 0 := by simp
  have e2 : (p' : ℤ) - ((1 : ℕ) : ℤ) + 1 = p' := by simp
  rw [e1, e2, Zpage_zero] at hβ
  rw [e1, Zpage_zero] at hc
  exact ⟨β, hβ, c, hc, hac.symm⟩

theorem star_zero_of_sub (p' : ℕ) (hsub : Subsingleton (E x 1 (p' : ℤ) 0))
    {α : RawCochain x} (hα : α ∈ filt x (p' : ℤ) 0)
    (hd : d x 0 α ∈ filt x ((p' : ℤ) + 1) 1) : α ∈ filt x ((p' : ℤ) + 1) 0 := by
  have hZ : α ∈ Zpage x ((1 : ℕ) : ℤ) (p' : ℤ) 0 := ⟨hα, by simpa using hd⟩
  have h0 : (Subquot.mk α hZ : E x 1 (p' : ℤ) 0) = 0 := Subsingleton.elim _ _
  have hB : α ∈ Bpage x 1 (p' : ℤ) 0 := by
    have := (Submodule.Quotient.mk_eq_zero _).1 h0
    exact this
  simp only [Bpage] at hB
  have e1 : ((1 : ℕ) : ℤ) - 1 = 0 := by simp
  rw [e1, Zpage_zero] at hB
  exact hB

theorem star_succ (hx : x.X.IsRelativelyProjective) (m p' : ℕ) (hne : m + 1 ≠ p')
    {α : RawCochain x} (hα : α ∈ filt x (p' : ℤ) (m + 1))
    (hd : d x (m + 1) α ∈ filt x ((p' : ℤ) + 1) (m + 1 + 1)) :
    ∃ β ∈ filt x (p' : ℤ) m, ∃ γ ∈ filt x ((p' : ℤ) + 1) (m + 1), α = d x m β + γ :=
  star_succ_of_sub x m p' ((lemma_1_25 x hx p' (m + 1)).2 hne) hα hd

theorem star_zero (hx : x.X.IsRelativelyProjective) (p' : ℕ) (hne : 0 ≠ p')
    {α : RawCochain x} (hα : α ∈ filt x (p' : ℤ) 0)
    (hd : d x 0 α ∈ filt x ((p' : ℤ) + 1) 1) : α ∈ filt x ((p' : ℤ) + 1) 0 :=
  star_zero_of_sub x p' ((lemma_1_25 x hx p' 0).2 hne) hα hd

/-- Locality of the differential: `dα(V, ·)` only involves `α` on spaces of dimension
`≤ dim V`. -/
theorem dRaw_local (n : ℕ) (α α' : RawCochain x) (V : FGModuleCat.{0} F)
    (h : ∀ W : FGModuleCat.{0} F, finrank F W ≤ finrank F V → α W = α' W) :
    dRaw x n α V = dRaw x n α' V := by
  apply LinearMap.ext
  intro z
  funext G
  simp only [dRaw, LinearMap.pi_apply]
  by_cases hG : G.len = n + 1
  · rw [if_pos hG, if_pos hG]
    have hq : α (quo (G.nth 1)) = α' (quo (G.nth 1)) :=
      h _ ((G.nth 1).finrank_quotient_le)
    have hs : α (sub (G.nth n)) = α' (sub (G.nth n)) := h _ (Submodule.finrank_le _)
    have hv : α V = α' V := h V le_rfl
    simp [hq, hs, hv]
  · rw [if_neg hG, if_neg hG]

/-- The pointwise-finite sum of a family of cochains `β i ∈ F^{L+i}`. -/
def sumFam (β : ℕ → RawCochain x) : RawCochain x := fun V =>
  ∑ i ∈ Finset.range (finrank F V + 1), β i V

theorem sumFam_eq_range {β : ℕ → RawCochain x} (L : ℕ)
    (hv : ∀ (i : ℕ) (W : FGModuleCat.{0} F), (finrank F W : ℤ) < ((L + i : ℕ) : ℤ) → β i W = 0)
    (V : FGModuleCat.{0} F) (N : ℕ) (hN : finrank F V + 1 ≤ N) :
    sumFam x β V = ∑ i ∈ Finset.range N, β i V := by
  unfold sumFam
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hi'
    simp only [Finset.mem_range] at hi hi'
    exact hv i V (by omega)

theorem sumFam_mem_cochains {β : ℕ → RawCochain x} {m : ℕ} (h : ∀ i, β i ∈ cochains x m) :
    sumFam x β ∈ cochains x m := by
  refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
  · show (∑ i ∈ Finset.range (finrank F V + 1), β i V) z G = 0
    rw [LinearMap.sum_apply, Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => (h i).1 V z G hG
  · have hfin : finrank F W = finrank F V := (LinearEquiv.finrank_eq e).symm
    show (∑ i ∈ Finset.range (finrank F W + 1), β i W) (x.X.mapEquiv e z) (G.map e) =
      (∑ i ∈ Finset.range (finrank F V + 1), β i V) z G
    rw [hfin, LinearMap.sum_apply, Finset.sum_apply, LinearMap.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (h i).2 V W e z G

theorem sumFam_mem_filt {β : ℕ → RawCochain x} {m : ℕ} (L : ℕ)
    (h : ∀ i, β i ∈ filt x ((L + i : ℕ) : ℤ) m) : sumFam x β ∈ filt x (L : ℤ) m := by
  refine (mem_filt_iff x _ m _).2 ⟨sumFam_mem_cochains x fun i => ((mem_filt_iff x _ m _).1 (h i)).1,
    fun V hV => ?_⟩
  apply LinearMap.ext
  intro z
  funext G
  show (∑ i ∈ Finset.range (finrank F V + 1), β i V) z G = 0
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := ((mem_filt_iff x _ m _).1 (h i)).2 V (by push_cast; omega)
  rw [this]; rfl

theorem d_sumFam {β : ℕ → RawCochain x} (L : ℕ)
    (hv : ∀ (i : ℕ) (W : FGModuleCat.{0} F), (finrank F W : ℤ) < ((L + i : ℕ) : ℤ) → β i W = 0)
    (m : ℕ) (V : FGModuleCat.{0} F) (N : ℕ) (hN : finrank F V + 1 ≤ N) :
    d x m (sumFam x β) V = ∑ i ∈ Finset.range N, d x m (β i) V := by
  have h1 : dRaw x m (sumFam x β) V = dRaw x m (∑ i ∈ Finset.range N, β i) V := by
    apply dRaw_local
    intro W hW
    rw [sumFam_eq_range x L hv W N (by omega)]
    funext
    simp [Finset.sum_apply]
  have h2 : d x m (∑ i ∈ Finset.range N, β i) = ∑ i ∈ Finset.range N, d x m (β i) := map_sum _ _ _
  show dRaw x m (sumFam x β) V = _
  rw [h1]
  show d x m (∑ i ∈ Finset.range N, β i) V = _
  rw [h2, Finset.sum_apply]

/-- Closed cochains of degree `p + 1` in `F^ℓ`. -/
def ClosedLevel (p ℓ : ℕ) : Type 1 :=
  {δ : RawCochain x // δ ∈ filt x (ℓ : ℤ) (p + 1) ∧ d x (p + 1) δ = 0}

theorem closed_step (hx : x.X.IsRelativelyProjective) (p ℓ : ℕ) (δ : ClosedLevel x p ℓ) :
    ∃ (β : RawCochain x) (δ' : ClosedLevel x p (ℓ + 1)),
      p + 2 ≤ ℓ → (β ∈ filt x (ℓ : ℤ) p ∧ δ.1 = d x p β + δ'.1) := by
  by_cases hℓ : p + 2 ≤ ℓ
  · have hne : p + 1 ≠ ℓ := by omega
    have hd : d x (p + 1) δ.1 ∈ filt x ((ℓ : ℤ) + 1) (p + 1 + 1) := by
      rw [δ.2.2]; exact Submodule.zero_mem _
    obtain ⟨β, hβ, γ, hγ, hδ⟩ := star_succ x hx p ℓ hne δ.2.1 hd
    have hβc : β ∈ cochains x p := ((mem_filt_iff x _ p β).1 hβ).1
    have hγd : d x (p + 1) γ = 0 := by
      have h1 : d x (p + 1) δ.1 = d x (p + 1) (d x p β) + d x (p + 1) γ := by
        rw [hδ, map_add]
      rw [δ.2.2, d_comp_d x p hβc, zero_add] at h1
      exact h1.symm
    refine ⟨β, ⟨γ, by simpa using hγ, hγd⟩, fun _ => ⟨hβ, hδ⟩⟩
  · exact ⟨0, ⟨0, Submodule.zero_mem _, map_zero _⟩, fun h => absurd h hℓ⟩

theorem exists_primitive_closed (hx : x.X.IsRelativelyProjective) (p r : ℕ) (hr : 2 ≤ r)
    (δ0 : ClosedLevel x p (p + r)) :
    ∃ β ∈ filt x ((p + r : ℕ) : ℤ) p, δ0.1 = d x p β := by
  choose B D hBD using closed_step x hx p
  let chain : ∀ i : ℕ, ClosedLevel x p (p + r + i) :=
    fun i => Nat.rec δ0 (fun i s => D (p + r + i) s) i
  let β : ℕ → RawCochain x := fun i => B (p + r + i) (chain i)
  have hβ : ∀ i, β i ∈ filt x ((p + r + i : ℕ) : ℤ) p := fun i =>
    (hBD (p + r + i) (chain i) (by omega)).1
  have hrec : ∀ i, (chain i).1 = d x p (β i) + (chain (i + 1)).1 := fun i =>
    (hBD (p + r + i) (chain i) (by omega)).2
  have hsum : ∀ N, (chain 0).1 = ∑ i ∈ Finset.range N, d x p (β i) + (chain N).1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      calc (chain 0).1 = ∑ i ∈ Finset.range N, d x p (β i) + (chain N).1 := ih
        _ = ∑ i ∈ Finset.range N, d x p (β i) + (d x p (β N) + (chain (N + 1)).1) := by
          rw [← hrec N]
        _ = ∑ i ∈ Finset.range (N + 1), d x p (β i) + (chain (N + 1)).1 := by
          have key : ∀ c : RawCochain x, ∑ i ∈ Finset.range N, d x p (β i) + (d x p (β N) + c) =
              ∑ i ∈ Finset.range (N + 1), d x p (β i) + c := fun c => by
            rw [Finset.sum_range_succ, add_assoc]
          exact key _
  have hvanβ : ∀ (i : ℕ) (W : FGModuleCat.{0} F),
      (finrank F W : ℤ) < ((p + r + i : ℕ) : ℤ) → β i W = 0 := fun i W hW =>
    ((mem_filt_iff x _ p _).1 (hβ i)).2 W hW
  refine ⟨sumFam x β, sumFam_mem_filt x (p + r) hβ, ?_⟩
  funext V
  have hN := hsum (finrank F V + 1)
  have hz : (chain (finrank F V + 1)).1 V = 0 :=
    ((mem_filt_iff x _ (p + 1) _).1 (chain (finrank F V + 1)).2.1).2 V (by push_cast; omega)
  have h0 : (chain 0).1 = δ0.1 := rfl
  have := congrArg (fun f : RawCochain x => f V) hN
  simp only [h0, Pi.add_apply, Finset.sum_apply, hz, add_zero] at this
  rw [this]
  exact (d_sumFam x (p + r) hvanβ p V (finrank F V + 1) le_rfl).symm

theorem exists_primitive (hx : x.X.IsRelativelyProjective) (p r : ℕ) (hr : 2 ≤ r)
    {α : RawCochain x} (hα : α ∈ filt x (p : ℤ) p)
    (hd : d x p α ∈ filt x ((p + r : ℕ) : ℤ) (p + 1)) :
    ∃ β ∈ filt x ((p + r : ℕ) : ℤ) p, d x p α = d x p β :=
  exists_primitive_closed x hx p r hr ⟨d x p α, hd, d_comp_d x p ((mem_filt_iff x _ p α).1 hα).1⟩

theorem filt_mono {p q : ℤ} (h : p ≤ q) (n : ℕ) : filt x q n ≤ filt x p n := by
  intro α hα
  obtain ⟨hc, hv⟩ := (mem_filt_iff x q n α).1 hα
  exact (mem_filt_iff x p n α).2 ⟨hc, fun V hV => hv V (by omega)⟩

theorem subquot_subsingleton_of_le {M : Type*} [AddCommGroup M] [Module k M]
    {A B : Submodule k M} (h : A ≤ B) : Subsingleton (Subquot A B) := by
  refine ⟨fun a b => ?_⟩
  induction a using Submodule.Quotient.induction_on with | _ a => ?_
  induction b using Submodule.Quotient.induction_on with | _ b => ?_
  have ha : (Submodule.Quotient.mk a : Subquot A B) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (h a.2)
  have hb : (Submodule.Quotient.mk b : Subquot A B) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (h b.2)
  rw [ha, hb]

theorem Zpage_inf_Bpage_one_le (p : ℤ) (n r : ℕ) (hr : 1 ≤ r) :
    Zpage x (r : ℤ) p n ⊓ Bpage x 1 p n ≤ Bpage x r p n := by
  rintro α ⟨⟨hαf, hαd⟩, hB1⟩
  have e1 : ((1 : ℕ) : ℤ) - 1 = 0 := by simp
  cases n with
  | zero =>
    simp only [Bpage] at hB1 ⊢
    rw [e1, Zpage_zero] at hB1
    refine ⟨hB1, ?_⟩
    show d x 0 α ∈ filt x (p + 1 + ((r : ℤ) - 1)) 1
    exact filt_mono x (by omega) _ hαd
  | succ m =>
    simp only [Bpage] at hB1 ⊢
    obtain ⟨a, ha, γ, hγ, hsum⟩ := Submodule.mem_sup.1 hB1
    obtain ⟨β, hβ, rfl⟩ := ha
    have e2 : p - ((1 : ℕ) : ℤ) + 1 = p := by simp
    rw [e1, e2, Zpage_zero] at hβ
    rw [e1, Zpage_zero] at hγ
    have hβc : β ∈ cochains x m := ((mem_filt_iff x _ m β).1 hβ).1
    have hdγ : d x (m + 1) γ = d x (m + 1) α := by
      rw [← hsum, map_add, d_comp_d x m hβc, zero_add]
    rw [← hsum]
    refine Submodule.add_mem_sup ⟨β, ⟨?_, ?_⟩, rfl⟩ ⟨?_, ?_⟩
    · exact filt_mono x (by omega) _ hβ
    · show d x m β ∈ filt x (p - r + 1 + ((r : ℤ) - 1)) (m + 1)
      have : d x m β = α - γ := by rw [← hsum]; abel
      rw [this]
      have e : p - r + 1 + ((r : ℤ) - 1) = p := by ring
      rw [e]
      exact Submodule.sub_mem _ hαf (filt_mono x (by omega) _ hγ)
    · exact hγ
    · show d x (m + 1) γ ∈ filt x (p + 1 + ((r : ℤ) - 1)) (m + 1 + 1)
      rw [hdγ]
      have e : p + 1 + ((r : ℤ) - 1) = p + r := by ring
      rw [e]; exact hαd

theorem Zpage_le_Bpage_of_sub (p : ℤ) (n r : ℕ) (hr : 1 ≤ r) (hsub : Subsingleton (E x 1 p n)) :
    Zpage x (r : ℤ) p n ≤ Bpage x r p n := by
  intro α hα
  have hZ1 : α ∈ Zpage x ((1 : ℕ) : ℤ) p n := ⟨hα.1, filt_mono x (by push_cast; omega) _ hα.2⟩
  have h0 : (Subquot.mk α hZ1 : E x 1 p n) = 0 := Subsingleton.elim _ _
  have hB : α ∈ Bpage x 1 p n := by
    have := (Submodule.Quotient.mk_eq_zero _).1 h0
    exact this
  exact Zpage_inf_Bpage_one_le x p n r hr ⟨hα, hB⟩

theorem Zpage_le_Bpage_of_ne (hx : x.X.IsRelativelyProjective) (p n r : ℕ) (hr : 1 ≤ r)
    (hne : n ≠ p) : Zpage x (r : ℤ) (p : ℤ) n ≤ Bpage x r (p : ℤ) n :=
  Zpage_le_Bpage_of_sub x (p : ℤ) n r hr ((lemma_1_25 x hx p n).2 hne)

theorem cocycle_mem (n : ℕ) {α : RawCochain x} (hc : α ∈ cochains x n) (hd : d x n α = 0) :
    α ∈ cocycles x n := ⟨hc, LinearMap.mem_ker.2 hd⟩

theorem filtH_le_of_ne (hx : x.X.IsRelativelyProjective) (p n : ℕ) (hne : n ≠ p) :
    filtH x (p : ℤ) n ≤ filtH x ((p : ℤ) + 1) n := by
  intro h hh
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hh
  have hcf : c.1 ∈ filt x (p : ℤ) n := hc
  have hcd : d x n c.1 = 0 := LinearMap.mem_ker.1 c.2.2
  cases n with
  | zero =>
    have h1 : c.1 ∈ filt x ((p : ℤ) + 1) 0 :=
      star_zero x hx p hne hcf (by rw [hcd]; exact Submodule.zero_mem _)
    exact Submodule.mem_map.2 ⟨c, h1, rfl⟩
  | succ m =>
    have hd' : d x (m + 1) c.1 ∈ filt x ((p : ℤ) + 1) (m + 1 + 1) := by
      rw [hcd]; exact Submodule.zero_mem _
    obtain ⟨β, hβ, γ, hγ, hαeq⟩ := star_succ x hx m p hne hcf hd'
    have hβc : β ∈ cochains x m := ((mem_filt_iff x _ m β).1 hβ).1
    have hγc : γ ∈ cochains x (m + 1) := ((mem_filt_iff x _ (m + 1) γ).1 hγ).1
    have hγd : d x (m + 1) γ = 0 := by
      have : d x (m + 1) c.1 = d x (m + 1) (d x m β) + d x (m + 1) γ := by rw [hαeq, map_add]
      rw [hcd, d_comp_d x m hβc, zero_add] at this
      exact this.symm
    refine Submodule.mem_map.2 ⟨⟨γ, cocycle_mem x _ hγc hγd⟩, hγ, ?_⟩
    apply (Submodule.Quotient.eq _).2
    show γ - c.1 ∈ coboundaries x (m + 1)
    have : γ - c.1 = -(d x m β) := by rw [hαeq]; abel
    rw [this]
    exact Submodule.neg_mem _ ⟨β, hβc, rfl⟩

/-- The cocycles lying in `F^p C^p`. -/
def Cp (p : ℕ) : Submodule k (RawCochain x) := filt x (p : ℤ) p ⊓ LinearMap.ker (d x p)

theorem Cp_le_cocycles (p : ℕ) : Cp x p ≤ cocycles x p := fun α hα =>
  ⟨((mem_filt_iff x _ p α).1 hα.1).1, hα.2⟩

theorem Cp_le_Zpage (p r : ℕ) : Cp x p ≤ Zpage x (r : ℤ) (p : ℤ) p := fun α hα => by
  refine ⟨hα.1, ?_⟩
  show d x p α ∈ filt x ((p : ℤ) + r) (p + 1)
  rw [LinearMap.mem_ker.1 hα.2]; exact Submodule.zero_mem _

/-- `Cp → E_r^{p,p}`. -/
def fE (p r : ℕ) : Cp x p →ₗ[k] E x r (p : ℤ) p :=
  (Submodule.mkQ _) ∘ₗ Submodule.inclusion (Cp_le_Zpage x p r)

theorem Cp_mem_filtH (p : ℕ) (α : Cp x p) :
    (Submodule.Quotient.mk (⟨α.1, Cp_le_cocycles x p α.2⟩ : cocycles x p) : H x p) ∈
      filtH x (p : ℤ) p :=
  Submodule.mem_map.2 ⟨⟨α.1, Cp_le_cocycles x p α.2⟩, α.2.1, rfl⟩

/-- `Cp → F^pH^p / F^{p+1}H^p`. -/
def gH (p : ℕ) : Cp x p →ₗ[k] Subquot (filtH x (p : ℤ) p) (filtH x ((p : ℤ) + 1) p) :=
  (Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (filtH x (p : ℤ) p)
    ((Submodule.mkQ _) ∘ₗ Submodule.inclusion (Cp_le_cocycles x p)) (Cp_mem_filtH x p)

theorem fE_eq_zero_iff (p r : ℕ) (α : Cp x p) : fE x p r α = 0 ↔ α.1 ∈ Bpage x r (p : ℤ) p := by
  show Submodule.Quotient.mk (Submodule.inclusion (Cp_le_Zpage x p r) α) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem gH_eq_zero_iff (p : ℕ) (α : Cp x p) :
    gH x p α = 0 ↔
      (Submodule.Quotient.mk (⟨α.1, Cp_le_cocycles x p α.2⟩ : cocycles x p) : H x p) ∈
        filtH x ((p : ℤ) + 1) p := by
  show Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem Bpage_iff_filtH (p r : ℕ) (hr : 2 ≤ r) (α : Cp x p) :
    α.1 ∈ Bpage x r (p : ℤ) p ↔
      (Submodule.Quotient.mk (⟨α.1, Cp_le_cocycles x p α.2⟩ : cocycles x p) : H x p) ∈
        filtH x ((p : ℤ) + 1) p := by
  have hαd : d x p α.1 = 0 := LinearMap.mem_ker.1 α.2.2
  have hαf : α.1 ∈ filt x (p : ℤ) p := α.2.1
  have hαc : α.1 ∈ cochains x p := ((mem_filt_iff x _ p _).1 hαf).1
  constructor
  · intro hB
    cases p with
    | zero =>
      simp only [Bpage] at hB
      exact Submodule.mem_map.2 ⟨⟨α.1, Cp_le_cocycles x 0 α.2⟩, hB.1, rfl⟩
    | succ m =>
      simp only [Bpage] at hB
      obtain ⟨a, ha, γ, hγ, hsum⟩ := Submodule.mem_sup.1 hB
      obtain ⟨β, hβ, rfl⟩ := ha
      have hβc : β ∈ cochains x m := ((mem_filt_iff x _ m β).1 hβ.1).1
      have hγf : γ ∈ filt x ((m + 1 : ℕ) + 1 : ℤ) (m + 1) := hγ.1
      have hγc : γ ∈ cochains x (m + 1) := ((mem_filt_iff x _ _ γ).1 hγf).1
      have hγd : d x (m + 1) γ = 0 := by
        have : d x (m + 1) α.1 = d x (m + 1) (d x m β) + d x (m + 1) γ := by
          rw [← hsum, map_add]
        rw [hαd, d_comp_d x m hβc, zero_add] at this
        exact this.symm
      refine Submodule.mem_map.2 ⟨⟨γ, cocycle_mem x _ hγc hγd⟩, by simpa using hγf, ?_⟩
      apply (Submodule.Quotient.eq _).2
      show γ - α.1 ∈ coboundaries x (m + 1)
      have : γ - α.1 = -(d x m β) := by rw [← hsum]; abel
      rw [this]
      exact Submodule.neg_mem _ ⟨β, hβc, rfl⟩
  · intro hH
    obtain ⟨c, hc, hceq⟩ := Submodule.mem_map.1 hH
    have hcf : c.1 ∈ filt x ((p : ℤ) + 1) p := hc
    have hcd : d x p c.1 = 0 := LinearMap.mem_ker.1 c.2.2
    have hdiff : c.1 - α.1 ∈ coboundaries x p := by
      have := (Submodule.Quotient.eq _).1 hceq
      exact this
    cases p with
    | zero =>
      have h0 : c.1 - α.1 = 0 := by simpa [coboundaries] using hdiff
      have : α.1 = c.1 := by rw [sub_eq_zero] at h0; exact h0.symm
      simp only [Bpage]
      refine ⟨by rw [this]; simpa using hcf, ?_⟩
      show d x 0 α.1 ∈ filt x _ 1
      rw [hαd]; exact Submodule.zero_mem _
    | succ m =>
      obtain ⟨η, hη, hηeq⟩ := hdiff
      simp only [Bpage]
      have hαeq : α.1 = d x m (-η) + c.1 := by
        rw [map_neg, hηeq]; abel
      rw [hαeq]
      refine Submodule.add_mem_sup ⟨-η, ⟨?_, ?_⟩, rfl⟩ ⟨hcf, ?_⟩
      · rw [filt_eq_cochains x _ m (by push_cast; omega)]
        exact Submodule.neg_mem _ hη
      · show d x m (-η) ∈ filt x (((m + 1 : ℕ) : ℤ) - r + 1 + ((r : ℤ) - 1)) (m + 1)
        have e : (((m + 1 : ℕ) : ℤ) - r + 1 + ((r : ℤ) - 1)) = ((m + 1 : ℕ) : ℤ) := by ring
        rw [e]
        have : d x m (-η) = α.1 - c.1 := by rw [hαeq]; abel
        rw [this]
        exact Submodule.sub_mem _ hαf (filt_mono x (by omega) _ hcf)
      · show d x (m + 1) c.1 ∈ filt x _ (m + 1 + 1)
        rw [hcd]; exact Submodule.zero_mem _

theorem Zpage_le_Bpage_right (r : ℕ) (p : ℤ) (n : ℕ) :
    Zpage x ((r : ℤ) - 1) (p + 1) n ≤ Bpage x r p n := by
  cases n with
  | zero => exact le_rfl
  | succ m => exact le_sup_right

theorem fE_surjective (hx : x.X.IsRelativelyProjective) (p r : ℕ) (hr : 2 ≤ r) :
    Function.Surjective (fE x p r) := by
  intro e
  induction e using Submodule.Quotient.induction_on with | _ z => ?_
  have hz1 : z.1 ∈ filt x (p : ℤ) p := z.2.1
  have hzd : d x p z.1 ∈ filt x ((p + r : ℕ) : ℤ) (p + 1) := by
    have := z.2.2
    simpa using this
  obtain ⟨β, hβ, hdβ⟩ := exists_primitive x hx p r hr hz1 hzd
  have hβp : β ∈ filt x (p : ℤ) p := filt_mono x (by push_cast; omega) _ hβ
  have hmem : z.1 - β ∈ Cp x p := by
    refine ⟨Submodule.sub_mem _ hz1 hβp, ?_⟩
    show d x p (z.1 - β) = 0
    rw [map_sub, hdβ, sub_self]
  refine ⟨⟨z.1 - β, hmem⟩, ?_⟩
  apply (Submodule.Quotient.eq _).2
  show (z.1 - β) - z.1 ∈ Bpage x r (p : ℤ) p
  have : (z.1 - β) - z.1 = -β := by abel
  rw [this]
  refine Zpage_le_Bpage_right x r (p : ℤ) p ⟨?_, ?_⟩
  · exact Submodule.neg_mem _ (filt_mono x (by push_cast; omega) _ hβ)
  · show d x p (-β) ∈ filt x (((p : ℤ) + 1) + ((r : ℤ) - 1)) (p + 1)
    rw [map_neg, ← hdβ]
    have e : ((p : ℤ) + 1) + ((r : ℤ) - 1) = ((p + r : ℕ) : ℤ) := by push_cast; ring
    rw [e]
    exact Submodule.neg_mem _ hzd

theorem gH_surjective (p : ℕ) : Function.Surjective (gH x p) := by
  intro e
  induction e using Submodule.Quotient.induction_on with | _ h => ?_
  obtain ⟨c, hc, hceq⟩ := Submodule.mem_map.1 h.2
  have hmem : c.1 ∈ Cp x p := ⟨hc, c.2.2⟩
  refine ⟨⟨c.1, hmem⟩, ?_⟩
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk h
  congr 1
  exact Subtype.ext hceq

/-- **Corollary 1.26.** If `x` is relatively projective, `E(x)` collapses at `E₂` and
converges to `H•(x)`: `E_r^{p,q} ≅ F^p H^{p+q} / F^{p+1} H^{p+q}` for `r ≥ 2`. If `x` is
moreover a coalgebra in `e`-bicomodules the convergence is multiplicative (not stated
here: it needs the products on the pages).

The thesis follows [Tam17, §IV.3] and the complete convergence theorem [Wei94, 5.5.10]. We
give a direct argument: by Lemma 1.25 the first page vanishes off the diagonal `n = p`, so
a cochain `δ ∈ F^ℓ` that is closed (`ℓ > p + 1`) is `dβ + δ'` with `δ' ∈ F^{ℓ+1}` closed;
iterating, and summing the corrections (a finite sum at each `V`, since `F^q` vanishes on
spaces of dimension `< q`), every `α ∈ Z_r^p` is a cocycle modulo `F^{p+r}`. -/
theorem cor_1_26 (hx : x.X.IsRelativelyProjective) (p n r : ℕ) (hr : 2 ≤ r) :
    Nonempty (E x r (p : ℤ) n ≃ₗ[k] Subquot (filtH x (p : ℤ) n) (filtH x ((p : ℤ) + 1) n)) := by
  rcases eq_or_ne n p with rfl | hne
  · have hker : LinearMap.ker (fE x n r) = LinearMap.ker (gH x n) := by
      ext α
      rw [LinearMap.mem_ker, LinearMap.mem_ker, fE_eq_zero_iff, gH_eq_zero_iff,
        Bpage_iff_filtH x n r hr]
    exact ⟨(LinearMap.quotKerEquivOfSurjective _ (fE_surjective x hx n r hr)).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans
        (LinearMap.quotKerEquivOfSurjective _ (gH_surjective x n)))⟩
  · haveI : Subsingleton (E x r (p : ℤ) n) :=
      subquot_subsingleton_of_le (Zpage_le_Bpage_of_ne x hx p n r (by omega) hne)
    haveI : Subsingleton (Subquot (filtH x (p : ℤ) n) (filtH x ((p : ℤ) + 1) n)) :=
      subquot_subsingleton_of_le (filtH_le_of_ne x hx p n hne)
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩

theorem filt_one_zero : filt x 1 0 = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  obtain ⟨hc, hv⟩ := (mem_filt_iff x 1 0 α).1 hα
  rw [Submodule.mem_bot]
  funext V
  apply LinearMap.ext
  intro z
  funext G
  by_cases hV : (finrank F V : ℤ) < 1
  · rw [hv V hV]; rfl
  · apply hc.1 V z G
    intro hlen
    have hcard : G.carrier.card = 1 := by
      have := G.card_eq_len_succ
      omega
    have hbt : (⊥ : Submodule F V) = ⊤ :=
      Finset.card_le_one.1 hcard.le _ G.bot_mem _ G.top_mem
    apply hV
    have : finrank F V = 0 := by
      have h1 : finrank F (⊤ : Submodule F V) = finrank F V := finrank_top F V
      rw [← hbt, finrank_bot] at h1
      exact h1.symm
    omega

theorem filtH_succ_eq_bot (hx : x.X.IsRelativelyProjective) (n : ℕ) :
    filtH x ((n : ℤ) + 1) n = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hh
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hcd : d x n c.1 = 0 := LinearMap.mem_ker.1 c.2.2
  cases n with
  | zero =>
    have : c.1 ∈ filt x 1 0 := by simpa using (hc : c.1 ∈ filt x (((0 : ℕ) : ℤ) + 1) 0)
    rw [filt_one_zero, Submodule.mem_bot] at this
    show c ∈ (coboundaries x 0).comap (cocycles x 0).subtype
    show c.1 ∈ coboundaries x 0
    rw [this]; exact Submodule.zero_mem _
  | succ m =>
    have hcf : c.1 ∈ filt x ((m + 2 : ℕ) : ℤ) (m + 1) := by
      have : (((m + 1 : ℕ) : ℤ) + 1) = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [← this]; exact hc
    obtain ⟨β, hβ, hβeq⟩ := exists_primitive_closed x hx m 2 le_rfl ⟨c.1, hcf, hcd⟩
    show c.1 ∈ coboundaries x (m + 1)
    exact ⟨β, ((mem_filt_iff x _ m β).1 hβ).1, hβeq.symm⟩

theorem mem_filtH_self (n : ℕ) (h : H x n) : h ∈ filtH x (n : ℤ) n := by
  induction h using Submodule.Quotient.induction_on with | _ c => ?_
  refine Submodule.mem_map.2 ⟨c, ?_, rfl⟩
  show c.1 ∈ filt x (n : ℤ) n
  rw [filt_eq_cochains x _ n le_rfl]
  exact c.2.1

/-- If the diagonal term `E₁^{n,n}` vanishes, so does `Hⁿ`. -/
theorem H_subsingleton_of_E1 (hx : x.X.IsRelativelyProjective) (n : ℕ)
    (hE1 : Subsingleton (E x 1 (n : ℤ) n)) : Subsingleton (H x n) := by
  obtain ⟨e⟩ := cor_1_26 x hx n n 2 le_rfl
  haveI : Subsingleton (E x 2 (n : ℤ) n) :=
    subquot_subsingleton_of_le (Zpage_le_Bpage_of_sub x (n : ℤ) n 2 (by norm_num) hE1)
  haveI : Subsingleton (Subquot (filtH x (n : ℤ) n) (filtH x ((n : ℤ) + 1) n)) :=
    e.symm.injective.subsingleton
  refine ⟨fun a b => ?_⟩
  have key : ∀ h : H x n, h = 0 := by
    intro h
    have hmem := mem_filtH_self x n h
    have h0 : (Submodule.Quotient.mk (⟨h, hmem⟩ : filtH x (n : ℤ) n) :
        Subquot (filtH x (n : ℤ) n) (filtH x ((n : ℤ) + 1) n)) = 0 := Subsingleton.elim _ _
    have := (Submodule.Quotient.mk_eq_zero _).1 h0
    have h1 : h ∈ filtH x ((n : ℤ) + 1) n := this
    rw [filtH_succ_eq_bot x hx n, Submodule.mem_bot] at h1
    exact h1
  rw [key a, key b]

end Conv

end MartinPhd

end
end Conv

section UnitPositive

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] {k : Type} [Field k]

/-- The unit species evaluates to zero on vector spaces of positive dimension. -/
theorem unit_eq_zero (V : FGModuleCat.{0} F) (h : finrank F V ≠ 0)
    (a : (EBicomod.unit (F := F) (k := k)).X.ev V) : a = 0 := by
  apply Subtype.ext
  change a.val = (0 : k)
  have ha := a.property
  change a.val ∈ (if finrank F V = 0 then ⊤ else ⊥ : Submodule k k) at ha
  simpa only [ite_eq_right h, Submodule.mem_bot] using ha

/-- Any flag of a 0-dimensional vector space has length 0. -/
theorem flag_len_eq_zero_of_finrank_zero {V : FGModuleCat.{0} F} (hV : finrank F V = 0)
    (G : Flag F V) : G.len = 0 := by
  have : Subsingleton V := finrank_zero_iff.mp hV
  have hbot_top : (⊥ : Submodule F V) = ⊤ := Subsingleton.elim ⊥ ⊤
  have hcar : G.carrier = {⊥} := by
    ext A
    simp only [Finset.mem_singleton]
    constructor
    · intro _
      exact Subsingleton.elim A ⊥
    · rintro rfl
      exact G.bot_mem
  have hcard : G.carrier.card = 1 := by
    rw [hcar, Finset.card_singleton]
  unfold Flag.len
  omega

/-- The cochains of degree `n > 0` of the unit bicomodule vanish. -/
theorem cochains_unit_pos (n : ℕ) (hn : 0 < n) :
    cochains (EBicomod.unit (F := F) (k := k)) n = ⊥ := by
  refine Submodule.ext fun α => ⟨fun hα => ?_, fun hα => ?_⟩
  · rw [Submodule.mem_bot]
    funext V
    apply LinearMap.ext
    intro z
    funext G
    by_cases hV : finrank F V = 0
    · have hG : G.len = 0 := flag_len_eq_zero_of_finrank_zero hV G
      have hlen : G.len ≠ n := by omega
      exact hα.1 V z G hlen
    · have hz : z = 0 := unit_eq_zero V hV z
      rw [hz, map_zero]
      rfl
  · rw [Submodule.mem_bot] at hα
    rw [hα]
    exact Submodule.zero_mem _

/-- The cocycles of degree `n > 0` of the unit bicomodule vanish. -/
theorem cocycles_unit_pos (n : ℕ) (hn : 0 < n) :
    cocycles (EBicomod.unit (F := F) (k := k)) n = ⊥ := by
  rw [cocycles, cochains_unit_pos n hn, bot_inf_eq]

/-- The cohomology `Hⁿ(1)` of the unit bicomodule is a subsingleton for `n > 0`. -/
theorem H_unit_pos_subsingleton (n : ℕ) (hn : 0 < n) :
    Subsingleton (H (EBicomod.unit (F := F) (k := k)) n) := by
  have hc := cocycles_unit_pos (F := F) (k := k) n hn
  constructor
  intro x y
  refine Quotient.inductionOn' x fun ⟨a, ha⟩ => ?_
  refine Quotient.inductionOn' y fun ⟨b, hb⟩ => ?_
  rw [hc, Submodule.mem_bot] at ha hb
  subst ha hb
  rfl

/-- The cohomology `Hⁿ(1)` has dimension 0 for `n > 0`. -/
theorem finrank_H_unit_pos (n : ℕ) (hn : 0 < n) :
    Module.finrank k (H (EBicomod.unit (F := F) (k := k)) n) = 0 := by
  have := H_unit_pos_subsingleton (F := F) (k := k) n hn
  exact finrank_zero_of_subsingleton

end MartinPhd
end
end UnitPositive

section UnitZero

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-!
# Degree 0 cochains of the unit bicomodule

In this file we establish the canonical linear equivalence between the degree-0 cochains
of the unit bicomodule `EBicomod.unit` and the base field `k` (Corollary 1.27):
`unitZeroEquiv : cochains (EBicomod.unit (F := F) (k := k)) 0 ≃ₗ[k] k`.

As a corollary, we deduce:
`finrank_cochains_unit_zero : Module.finrank k (cochains (EBicomod.unit (F := F) (k := k)) 0) = 1`.
-/

variable {F : Type} [Field F] {k : Type} [Field k]

theorem finrank_stdSpace_zero : finrank F (stdSpace F 0) = 0 := by simp

/-- A fixed 0-dimensional space. -/
abbrev V0 : FGModuleCat.{0} F := stdSpace F 0

/-- The unique flag of `V0`. -/
abbrev G0 : Flag F (V0 (F := F)) := Flag.trivial

/-- A unit vector in `(EBicomod.unit).X.ev V0`. -/
def z0 : (EBicomod.unit (F := F) (k := k)).X.ev (V0 (F := F)) :=
  GLSpecies.unitOne (V0 (F := F)) (finrank_stdSpace_zero (F := F))

/-- On spaces of non-zero dimension, the unit bicomodule evaluation is zero. -/
theorem unit_ev_eq_zero {V : FGModuleCat.{0} F} (h : finrank F V ≠ 0)
    (z : (EBicomod.unit (F := F) (k := k)).X.ev V) : z = 0 := by
  apply Subtype.ext
  change z.val = (0 : k)
  have hz := z.property
  change z.val ∈ (if finrank F V = 0 then ⊤ else ⊥ : Submodule k k) at hz
  simpa only [ite_eq_right h, Submodule.mem_bot] using hz

/-- On a space of dimension 0, any element of `unit.ev V` is a scalar multiple of `unitOne`. -/
theorem unit_eq_smul_unitOne {V : FGModuleCat.{0} F} (h : finrank F V = 0)
    (z : (EBicomod.unit (F := F) (k := k)).X.ev V) :
    z = z.val • GLSpecies.unitOne V h := by
  apply Subtype.ext
  change z.val = z.val * 1
  exact (mul_one _).symm

/-- Transport along a linear equivalence preserves the underlying scalar in `unit.ev`. -/
theorem unit_mapEquiv_val {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W)
    (z : (EBicomod.unit (F := F) (k := k)).X.ev V) :
    ((EBicomod.unit (F := F) (k := k)).X.mapEquiv e z).val = z.val := by
  rfl

/-- Transport along a linear equivalence maps `unitOne` to `unitOne`. -/
theorem unit_mapEquiv_unitOne {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W)
    (hV : finrank F V = 0) (hW : finrank F W = 0) :
    (EBicomod.unit (F := F) (k := k)).X.mapEquiv e (GLSpecies.unitOne V hV) = GLSpecies.unitOne W hW := by
  apply Subtype.ext
  rfl

/-- The flag on a 0-dimensional space is unique. -/
theorem flag_eq_of_finrank_zero {V : FGModuleCat.{0} F} (hV : finrank F V = 0)
    (G G' : Flag F V) : G = G' := by
  have : Subsingleton V := finrank_zero_iff.1 hV
  have hsub : ∀ W : Submodule F V, W = ⊥ := fun W => Submodule.eq_bot_of_subsingleton
  have hcar (H : Flag F V) : H.carrier = {⊥} := by
    ext W; rw [hsub W]; simp [H.bot_mem]
  exact Flag.ext (by rw [hcar G, hcar G'])

/-- Forward map on degree-0 cochains: evaluate at `(V0, z0, G0)`. -/
def unitZeroToLinearMap : cochains (EBicomod.unit (F := F) (k := k)) 0 →ₗ[k] k where
  toFun α := α.1 (V0 (F := F)) (z0 (F := F) (k := k)) (G0 (F := F))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Inverse map on raw cochains: given `c : k`, construct a raw cochain. -/
def unitZeroRaw (c : k) : RawCochain (EBicomod.unit (F := F) (k := k)) := fun V =>
  LinearMap.pi fun G : Flag F V =>
    if G.len = 0 then c • Submodule.subtype _ else 0

theorem unitZeroRaw_apply (c : k) (V : FGModuleCat.{0} F)
    (z : (EBicomod.unit (F := F) (k := k)).X.ev V) (G : Flag F V) :
    unitZeroRaw c V z G = if G.len = 0 then c * z.val else 0 := by
  dsimp [unitZeroRaw]
  split_ifs <;> rfl

theorem unitZeroRaw_mem (c : k) :
    unitZeroRaw (F := F) c ∈ cochains (EBicomod.unit (F := F) (k := k)) 0 := by
  refine ⟨fun V z G hG => by simp [unitZeroRaw_apply, hG], fun V W e z G => ?_⟩
  rw [unitZeroRaw_apply, unitZeroRaw_apply]
  rw [Flag.len_map, unit_mapEquiv_val]

/-- Inverse map as a linear map from `k` to degree-0 cochains. -/
def unitZeroInvLinearMap : k →ₗ[k] cochains (EBicomod.unit (F := F) (k := k)) 0 where
  toFun c := ⟨unitZeroRaw c, unitZeroRaw_mem c⟩
  map_add' c1 c2 := by
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro z
    funext G
    by_cases hG : G.len = 0 <;> simp [unitZeroRaw_apply, hG, add_mul]
  map_smul' r c := by
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro z
    funext G
    by_cases hG : G.len = 0 <;> simp [unitZeroRaw_apply, hG, mul_assoc]

theorem unitZeroToLinearMap_inv (c : k) :
    unitZeroToLinearMap (F := F) (unitZeroInvLinearMap (F := F) c) = c := by
  have hlen : (G0 (F := F)).len = 0 :=
    flag_len_eq_zero_of_finrank_zero (finrank_stdSpace_zero (F := F)) G0
  have hz : (z0 (F := F) (k := k)).val = 1 := rfl
  change unitZeroRaw c (V0 (F := F)) (z0 (F := F) (k := k)) (G0 (F := F)) = c
  rw [unitZeroRaw_apply, hlen]
  simp [hz]

theorem unitZeroInv_toLinearMap (α : cochains (EBicomod.unit (F := F) (k := k)) 0) :
    unitZeroInvLinearMap (F := F) (unitZeroToLinearMap (F := F) α) = α := by
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro z
  funext G
  by_cases hV : finrank F V = 0
  · have hlen : G.len = 0 := flag_len_eq_zero_of_finrank_zero hV G
    let e : V ≃ₗ[F] V0 (F := F) :=
      LinearEquiv.ofFinrankEq V (V0 (F := F)) (by rw [hV, finrank_stdSpace_zero])
    have hnat := α.2.2 V (V0 (F := F)) e (GLSpecies.unitOne V hV) G
    rw [unit_mapEquiv_unitOne e hV (finrank_stdSpace_zero (F := F))] at hnat
    have hG0 : G.map e = G0 := flag_eq_of_finrank_zero (finrank_stdSpace_zero (F := F)) (G.map e) G0
    rw [hG0] at hnat
    have hz_smul : z = z.val • GLSpecies.unitOne V hV := unit_eq_smul_unitOne hV z
    have hsmul : (α.1 V) z = z.val • (α.1 V) (GLSpecies.unitOne V hV) := by
      conv_lhs => rw [hz_smul]
      exact (α.1 V).map_smul z.val (GLSpecies.unitOne V hV)
    have hsmulG : (α.1 V) z G = z.val * (α.1 V) (GLSpecies.unitOne V hV) G := by
      rw [hsmul, Pi.smul_apply, smul_eq_mul]
    change unitZeroRaw (unitZeroToLinearMap α) V z G = (α.1 V) z G
    rw [unitZeroRaw_apply, hlen, hsmulG, ← hnat]
    simp [unitZeroToLinearMap, z0, mul_comm]
  · have hz : z = 0 := unit_ev_eq_zero hV z
    change unitZeroRaw (unitZeroToLinearMap α) V z G = (α.1 V) z G
    rw [hz, map_zero, map_zero]

/-- Linear equivalence between degree-0 cochains of the unit bicomodule and `k`. -/
def unitZeroEquiv : cochains (EBicomod.unit (F := F) (k := k)) 0 ≃ₗ[k] k :=
  LinearEquiv.ofLinearMap (unitZeroToLinearMap (F := F)) (unitZeroInvLinearMap (F := F))
    (LinearMap.ext (unitZeroToLinearMap_inv (F := F)))
    (LinearMap.ext (unitZeroInv_toLinearMap (F := F)))

@[simp] theorem unitZeroEquiv_apply (α : cochains (EBicomod.unit (F := F) (k := k)) 0) :
    unitZeroEquiv α = α.1 (V0 (F := F)) (z0 (F := F) (k := k)) (G0 (F := F)) := rfl

/-- Evaluation of degree-0 cochain on `unitOne` on any zero-dimensional space equals `unitZeroEquiv α`. -/
theorem unitZero_apply_of_finrank_zero (α : cochains (EBicomod.unit (F := F) (k := k)) 0)
    (V : FGModuleCat.{0} F) (hV : finrank F V = 0) (G : Flag F V) :
    α.1 V (GLSpecies.unitOne V hV) G = unitZeroEquiv α := by
  let e : V ≃ₗ[F] V0 (F := F) :=
    LinearEquiv.ofFinrankEq V (V0 (F := F)) (by rw [hV, finrank_stdSpace_zero])
  have hnat := α.2.2 V (V0 (F := F)) e (GLSpecies.unitOne V hV) G
  rw [unit_mapEquiv_unitOne e hV (finrank_stdSpace_zero (F := F))] at hnat
  have hG0 : G.map e = G0 := flag_eq_of_finrank_zero (finrank_stdSpace_zero (F := F)) (G.map e) G0
  rw [hG0] at hnat
  exact hnat.symm

/-- Evaluation of degree-0 cochain on any element on any zero-dimensional space. -/
theorem unitZero_apply_of_finrank_zero' (α : cochains (EBicomod.unit (F := F) (k := k)) 0)
    (V : FGModuleCat.{0} F) (hV : finrank F V = 0)
    (z : (EBicomod.unit (F := F) (k := k)).X.ev V) (G : Flag F V) :
    α.1 V z G = z.val * unitZeroEquiv α := by
  have hz_smul : z = z.val • GLSpecies.unitOne V hV := unit_eq_smul_unitOne hV z
  have hsmul : (α.1 V) z = z.val • (α.1 V) (GLSpecies.unitOne V hV) := by
    conv_lhs => rw [hz_smul]
    exact (α.1 V).map_smul z.val (GLSpecies.unitOne V hV)
  rw [hsmul, Pi.smul_apply, smul_eq_mul, unitZero_apply_of_finrank_zero]

/-- Evaluation of degree-0 cochain on any space of dimension ≠ 0 is zero. -/
theorem unitZero_apply_of_finrank_ne_zero (α : cochains (EBicomod.unit (F := F) (k := k)) 0)
    (V : FGModuleCat.{0} F) (hV : finrank F V ≠ 0)
    (z : (EBicomod.unit (F := F) (k := k)).X.ev V) (G : Flag F V) :
    α.1 V z G = 0 := by
  have hz : z = 0 := unit_ev_eq_zero hV z
  rw [hz, map_zero, Pi.zero_apply]

@[simp] theorem unitZeroEquiv_symm_apply (c : k) (V : FGModuleCat.{0} F)
    (z : (EBicomod.unit (F := F) (k := k)).X.ev V) (G : Flag F V) :
    ((unitZeroEquiv (F := F) (k := k)).symm c).1 V z G = if G.len = 0 then c * z.val else 0 := by
  change unitZeroRaw c V z G = _
  rw [unitZeroRaw_apply]

/-- The dimension of the degree-0 cochains of the unit bicomodule is 1. -/
theorem finrank_cochains_unit_zero :
    Module.finrank k (cochains (EBicomod.unit (F := F) (k := k)) 0) = 1 := by
  rw [LinearEquiv.finrank_eq (unitZeroEquiv (F := F) (k := k)), finrank_self]

end MartinPhd

end
end UnitZero

section UnitCoh

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] {k : Type} [Field k]

/-- In degree 0, the coboundaries of the unit bicomodule vanish by definition. -/
theorem coboundaries_unit_zero :
    coboundaries (EBicomod.unit (F := F) (k := k)) 0 = ⊥ := rfl

/-- In degree 0, every cochain of the unit bicomodule is a cocycle because degree-1 cochains vanish. -/
theorem cocycles_unit_zero :
    cocycles (EBicomod.unit (F := F) (k := k)) 0 = cochains (EBicomod.unit (F := F) (k := k)) 0 := by
  apply le_antisymm inf_le_left
  rw [le_inf_iff]
  refine ⟨le_rfl, fun α hα => ?_⟩
  rw [LinearMap.mem_ker]
  have hd : d (EBicomod.unit) 0 α ∈ cochains (EBicomod.unit) 1 := d_mem (EBicomod.unit) hα
  rw [cochains_unit_pos 1 (by omega)] at hd
  rw [Submodule.mem_bot] at hd
  exact hd

/-- The space of degree-0 cocycles of the unit bicomodule has dimension 1. -/
theorem finrank_cocycles_unit_zero :
    Module.finrank k (cocycles (EBicomod.unit (F := F) (k := k)) 0) = 1 := by
  have h := (LinearEquiv.ofEq _ _ (cocycles_unit_zero (F := F) (k := k))).finrank_eq
  rw [h, finrank_cochains_unit_zero]

/-- The canonical linear equivalence between `H⁰(1)` and degree-0 cocycles. -/
def H_unit_zero_equiv_cocycles :
    H (EBicomod.unit (F := F) (k := k)) 0 ≃ₗ[k]
      cocycles (EBicomod.unit (F := F) (k := k)) 0 := by
  have hp : (coboundaries (EBicomod.unit (F := F) (k := k)) 0).comap
      (cocycles (EBicomod.unit (F := F) (k := k)) 0).subtype = ⊥ := by
    rw [coboundaries_unit_zero, Submodule.comap_bot, Submodule.ker_subtype]
  exact Submodule.quotEquivOfEqBot _ hp

/-- The degree-0 cohomology `H⁰(1)` has dimension 1. -/
theorem finrank_H_unit_zero :
    Module.finrank k (H (EBicomod.unit (F := F) (k := k)) 0) = 1 := by
  exact (H_unit_zero_equiv_cocycles (F := F) (k := k)).finrank_eq.trans
    (finrank_cocycles_unit_zero (F := F) (k := k))

/-- **Corollary 1.27 (unit part).** The cohomology `Hⁿ(1)` of the unit bicomodule
has dimension 1 for `n = 0` and 0 for `n > 0`. -/
theorem finrank_H_unit (n : ℕ) :
    Module.finrank k (H (EBicomod.unit (F := F) (k := k)) n) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn
    exact finrank_H_unit_zero
  · exact finrank_H_unit_pos n (Nat.pos_of_ne_zero hn)

end MartinPhd

end
end UnitCoh

section ExpD

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd
namespace ExpD

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] {k : Type} [Field k]

instance (W : FGModuleCat.{0} F) : OfNat ((EBicomod.exp (F := F) (k := k)).X.ev W) (nat_lit 1) := ⟨(1 : k)⟩

theorem rawCochain_exp_apply (α : RawCochain (EBicomod.exp (F := F) (k := k)))
    (W : FGModuleCat.{0} F) (z : k) (H : Flag F W) :
    α W (z : (EBicomod.exp (F := F) (k := k)).X.ev W) H = z * α W 1 H := by
  have hz : (z : (EBicomod.exp (F := F) (k := k)).X.ev W) = z • (1 : (EBicomod.exp (F := F) (k := k)).X.ev W) := by
    change z = z * (1 : k)
    rw [mul_one]
  rw [hz, LinearMap.map_smul]
  rw [Pi.smul_apply, smul_eq_mul]
  congr 1

theorem expD_nth_one_proper {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = 2) :
    G.nth 1 ≠ ⊥ ∧ G.nth 1 ≠ ⊤ := by
  constructor
  · intro h0
    have hlt := G.nth_lt_nth (i := 0) (j := 1) (by omega) (by rw [G.card_eq_len_succ, hG]; omega)
    rw [Flag.nth_zero, h0] at hlt
    exact lt_irrefl _ hlt
  · intro h2
    have hlt := G.nth_lt_nth (i := 1) (j := 2) (by omega) (by rw [G.card_eq_len_succ, hG]; omega)
    rw [show (2 : ℕ) = G.len from hG.symm, Flag.nth_len, h2] at hlt
    exact lt_irrefl _ hlt

theorem faceSum_len2 {V : FGModuleCat.{0} F} (X : Type) [AddCommGroup X] [Module k X]
    (G : Flag F V) (hG : G.len = 2) (γ : X →ₗ[k] (Flag F V → k)) (z : X) :
    faceSum X G γ z = -γ z (G.erase (G.nth 1) (expD_nth_one_proper G hG)) := by
  unfold faceSum
  rw [LinearMap.sum_apply, Finset.sum_eq_single (G.nth 1)]
  · rw [dite_eq_left (expD_nth_one_proper G hG), Flag.index_nth G (by omega)]
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
    · rw [dite_eq_right h]; rfl
  · intro hn
    exact absurd (Flag.nth_mem' G (by omega)) hn

/-- The differential of degree-1 cochains of `EBicomod.exp` on flags of length 2. -/
theorem d_exp_one_apply (α : RawCochain (EBicomod.exp (F := F) (k := k)))
    (V : FGModuleCat.{0} F) (G : Flag F V) (hG : G.len = 2) (z : k) :
    d (EBicomod.exp) 1 α V z G =
      z * (α (quo (G.nth 1)) 1 (G.project (G.nth 1)) -
           α V 1 (G.erase (G.nth 1) (expD_nth_one_proper G hG)) +
           α (sub (G.nth 1)) 1 (G.restrict (G.nth 1))) := by
  have e1 : d (EBicomod.exp) 1 α V z G =
      (if G.len = 1 + 1 then
        (LinearMap.proj (G.project (G.nth 1)) ∘ₗ α (quo (G.nth 1)) ∘ₗ
          (EBicomod.exp).proj V (G.nth 1)) +
          faceSum _ G (α V) +
        ((-1 : k) ^ (1 + 1)) • (LinearMap.proj (G.restrict (G.nth 1)) ∘ₗ
          α (sub (G.nth 1)) ∘ₗ (EBicomod.exp).res V (G.nth 1))
      else 0) z := rfl
  rw [e1]
  have hG2 : G.len = 1 + 1 := by omega
  split_ifs
  erw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [faceSum_len2 _ G hG (α V) z]
  change α (quo (G.nth 1)) z (G.project (G.nth 1)) +
      -α V z (G.erase (G.nth 1) (expD_nth_one_proper G hG)) +
      ((-1 : k) ^ (1 + 1)) • α (sub (G.nth 1)) z (G.restrict (G.nth 1)) = _
  rw [rawCochain_exp_apply α (quo (G.nth 1)) z (G.project (G.nth 1))]
  rw [rawCochain_exp_apply α V z (G.erase (G.nth 1) (expD_nth_one_proper G hG))]
  rw [rawCochain_exp_apply α (sub (G.nth 1)) z (G.restrict (G.nth 1))]
  simp only [smul_eq_mul]
  ring

end ExpD
end MartinPhd

end
end ExpD

section ExpZero

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] {k : Type} [Field k]

theorem finrank_zero_of_flag_len_zero {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = 0) :
    finrank F V = 0 := by
  have hcard : G.carrier.card = 1 := by rw [G.card_eq_len_succ, hG]
  have hbot_eq_top : (⊥ : Submodule F V) = ⊤ :=
    Finset.card_le_one_iff.mp (le_of_eq hcard) G.bot_mem G.top_mem
  have : Subsingleton V := ⟨fun x y => by
    have hx : x ∈ (⊥ : Submodule F V) := by rw [hbot_eq_top]; exact Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule F V) := by rw [hbot_eq_top]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at hx hy
    rw [hx, hy]⟩
  exact finrank_zero_iff.2 this

theorem finrank_quo_top (V : FGModuleCat.{0} F) :
    finrank F (quo (⊤ : Submodule F V)) = 0 := by
  have : Subsingleton (V ⧸ (⊤ : Submodule F V)) := ⟨fun x y => by
    obtain ⟨vx, rfl⟩ := Submodule.Quotient.mk_surjective ⊤ x
    obtain ⟨vy, rfl⟩ := Submodule.Quotient.mk_surjective ⊤ y
    exact (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top⟩
  exact finrank_zero_iff.2 this

/-- The linear map identifying `exp.ev V` with `k`. -/
def expVal (V : FGModuleCat.{0} F) :
    (EBicomod.exp (F := F) (k := k)).X.ev V →ₗ[k] k where
  toFun z := (show k from z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The unit vector in `exp.ev V`. -/
def expUnit (V : FGModuleCat.{0} F) : (EBicomod.exp (F := F) (k := k)).X.ev V := (1 : k)

/-- The unit vector in `exp.ev V0`. -/
def expZ0 : (EBicomod.exp (F := F) (k := k)).X.ev (V0 (F := F)) := expUnit (V0 (F := F))

theorem expVal_expUnit (V : FGModuleCat.{0} F) : expVal V (expUnit (F := F) (k := k) V) = 1 := rfl

theorem expVal_expZ0 : expVal (V0 (F := F)) (expZ0 (F := F) (k := k)) = 1 := rfl

theorem exp_eq_smul (V : FGModuleCat.{0} F)
    (z : (EBicomod.exp (F := F) (k := k)).X.ev V) :
    z = expVal V z • expUnit V := by
  change (show k from z) = (show k from z) * 1
  exact (mul_one _).symm

theorem expVal_mapEquiv {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W)
    (z : (EBicomod.exp (F := F) (k := k)).X.ev V) :
    expVal W ((EBicomod.exp (F := F) (k := k)).X.mapEquiv e z) = expVal V z := rfl

/-- Forward map on degree-0 cochains: evaluate at `(V0, expZ0, G0)`. -/
def expZeroToLinearMap : cochains (EBicomod.exp (F := F) (k := k)) 0 →ₗ[k] k where
  toFun α := α.1 (V0 (F := F)) (expZ0 (F := F) (k := k)) (G0 (F := F))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Inverse map on raw cochains: given `c : k`, construct a raw cochain. -/
def expZeroRaw (c : k) : RawCochain (EBicomod.exp (F := F) (k := k)) := fun V =>
  LinearMap.pi fun G : Flag F V =>
    if G.len = 0 then c • expVal V else 0

theorem expZeroRaw_apply (c : k) (V : FGModuleCat.{0} F)
    (z : (EBicomod.exp (F := F) (k := k)).X.ev V) (G : Flag F V) :
    expZeroRaw c V z G = if G.len = 0 then c * expVal V z else 0 := by
  dsimp [expZeroRaw]
  split_ifs with h
  · simp [smul_eq_mul]
  · rfl

theorem expZeroRaw_mem (c : k) :
    expZeroRaw (F := F) c ∈ cochains (EBicomod.exp (F := F) (k := k)) 0 := by
  refine ⟨fun V z G hG => by simp [expZeroRaw_apply, hG], fun V W e z G => ?_⟩
  rw [expZeroRaw_apply, expZeroRaw_apply]
  rw [Flag.len_map, expVal_mapEquiv]

/-- Inverse map as a linear map from `k` to degree-0 cochains. -/
def expZeroInvLinearMap : k →ₗ[k] cochains (EBicomod.exp (F := F) (k := k)) 0 where
  toFun c := ⟨expZeroRaw c, expZeroRaw_mem c⟩
  map_add' c1 c2 := by
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro z
    funext G
    by_cases hG : G.len = 0 <;> simp [expZeroRaw_apply, hG, add_mul]
  map_smul' r c := by
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro z
    funext G
    by_cases hG : G.len = 0 <;> simp [expZeroRaw_apply, hG, mul_assoc]

theorem expZeroToLinearMap_inv (c : k) :
    expZeroToLinearMap (F := F) (expZeroInvLinearMap (F := F) c) = c := by
  have hlen : (G0 (F := F)).len = 0 :=
    flag_len_eq_zero_of_finrank_zero (finrank_stdSpace_zero (F := F)) G0
  change expZeroRaw c (V0 (F := F)) (expZ0 (F := F) (k := k)) (G0 (F := F)) = c
  rw [expZeroRaw_apply]
  simp [hlen, expVal_expZ0]

theorem expZeroInv_toLinearMap (α : cochains (EBicomod.exp (F := F) (k := k)) 0) :
    expZeroInvLinearMap (F := F) (expZeroToLinearMap (F := F) α) = α := by
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro z
  funext G
  by_cases hG : G.len = 0
  · have hV : finrank F V = 0 := finrank_zero_of_flag_len_zero G hG
    let e : V ≃ₗ[F] V0 (F := F) :=
      LinearEquiv.ofFinrankEq V (V0 (F := F)) (by rw [hV, finrank_stdSpace_zero])
    have hnat : (α.1 (V0 (F := F))) (expUnit (V0 (F := F))) (G.map e) = (α.1 V) (expUnit V) G :=
      α.2.2 V (V0 (F := F)) e (expUnit V) G
    have hG0 : G.map e = G0 := flag_eq_of_finrank_zero (finrank_stdSpace_zero (F := F)) (G.map e) G0
    rw [hG0] at hnat
    have hz_smul : (α.1 V) z = expVal V z • (α.1 V) (expUnit V) := by
      have hz : z = expVal V z • expUnit V := exp_eq_smul V z
      conv_lhs => rw [hz]
      exact (α.1 V).map_smul (expVal V z) (expUnit V)
    have hsmulG : (α.1 V) z G = expVal V z * (α.1 V) (expUnit V) G := by
      rw [hz_smul, Pi.smul_apply, smul_eq_mul]
    change expZeroRaw (expZeroToLinearMap α) V z G = (α.1 V) z G
    rw [expZeroRaw_apply]
    simp [hG, hsmulG, ← hnat, expZeroToLinearMap, expZ0, mul_comm]
  · change expZeroRaw (expZeroToLinearMap α) V z G = (α.1 V) z G
    rw [expZeroRaw_apply]
    simp [hG, α.2.1 V z G hG]

/-- Linear equivalence between degree-0 cochains of the exponential bicomodule and `k`. -/
def expZeroEquiv : cochains (EBicomod.exp (F := F) (k := k)) 0 ≃ₗ[k] k :=
  LinearEquiv.ofLinearMap (expZeroToLinearMap (F := F)) (expZeroInvLinearMap (F := F))
    (LinearMap.ext (expZeroToLinearMap_inv (F := F)))
    (LinearMap.ext (expZeroInv_toLinearMap (F := F)))

@[simp] theorem expZeroEquiv_apply (α : cochains (EBicomod.exp (F := F) (k := k)) 0) :
    expZeroEquiv α = α.1 (V0 (F := F)) (expZ0 (F := F) (k := k)) (G0 (F := F)) := rfl

/-- The dimension of the degree-0 cochains of the exponential bicomodule is 1. -/
theorem finrank_cochains_exp_zero :
    Module.finrank k (cochains (EBicomod.exp (F := F) (k := k)) 0) = 1 := by
  rw [LinearEquiv.finrank_eq (expZeroEquiv (F := F) (k := k)), finrank_self]

/-- Evaluation of degree-0 cochain on `expUnit` on any zero-dimensional space equals `expZeroEquiv α`. -/
theorem expZero_apply_of_finrank_zero_unit (α : cochains (EBicomod.exp (F := F) (k := k)) 0)
    (V : FGModuleCat.{0} F) (hV : finrank F V = 0) (G : Flag F V) :
    α.1 V (expUnit V) G = expZeroEquiv α := by
  let e : V ≃ₗ[F] V0 (F := F) :=
    LinearEquiv.ofFinrankEq V (V0 (F := F)) (by rw [hV, finrank_stdSpace_zero])
  have hnat : (α.1 (V0 (F := F))) (expUnit (V0 (F := F))) (G.map e) = (α.1 V) (expUnit V) G :=
    α.2.2 V (V0 (F := F)) e (expUnit V) G
  have hG0 : G.map e = G0 := flag_eq_of_finrank_zero (finrank_stdSpace_zero (F := F)) (G.map e) G0
  rw [hG0] at hnat
  exact hnat.symm

/-- Evaluation of degree-0 cochain on any element on any zero-dimensional space. -/
theorem expZero_apply_of_finrank_zero (α : cochains (EBicomod.exp (F := F) (k := k)) 0)
    (V : FGModuleCat.{0} F) (hV : finrank F V = 0)
    (z : (EBicomod.exp (F := F) (k := k)).X.ev V) (G : Flag F V) :
    α.1 V z G = expVal V z * expZeroEquiv α := by
  have hz_smul : (α.1 V) z = expVal V z • (α.1 V) (expUnit V) := by
    have hz : z = expVal V z • expUnit V := exp_eq_smul V z
    conv_lhs => rw [hz]
    exact (α.1 V).map_smul (expVal V z) (expUnit V)
  rw [hz_smul, Pi.smul_apply, smul_eq_mul, expZero_apply_of_finrank_zero_unit α V hV G]

theorem exp_proj (V : FGModuleCat.{0} F) (S : Submodule F V) :
    (EBicomod.exp (F := F) (k := k)).proj V S = LinearMap.id := rfl

theorem exp_res (V : FGModuleCat.{0} F) (S : Submodule F V) :
    (EBicomod.exp (F := F) (k := k)).res V S = LinearMap.id := rfl

theorem flag_carrier_eq_pair_of_len_one {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = 1) :
    ∀ A ∈ G.carrier, A = ⊥ ∨ A = ⊤ := by
  intro A hA
  have hcard : G.carrier.card = 2 := by rw [G.card_eq_len_succ, hG]
  by_contra h
  have hbot : A ≠ ⊥ := fun heq => h (Or.inl heq)
  have htop : A ≠ ⊤ := fun heq => h (Or.inr heq)
  have hbot_ne_top : (⊥ : Submodule F V) ≠ ⊤ := by
    intro hbot_top
    have : Subsingleton V := ⟨fun x y => by
      have hx : x ∈ (⊥ : Submodule F V) := by rw [hbot_top]; exact Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule F V) := by rw [hbot_top]; exact Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy
      rw [hx, hy]⟩
    have heq : G.carrier = {⊥} := by
      ext W; rw [Subsingleton.elim W ⊥]; simp [G.bot_mem]
    have h1 : G.carrier.card = 1 := by rw [heq, Finset.card_singleton]
    omega
  have h3 : {⊥, ⊤, A} ⊆ G.carrier := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact G.bot_mem
    · exact G.top_mem
    · exact hA
  have htop_bot : (⊤ : Submodule F V) ∉ ({A} : Finset (Submodule F V)) := by
    simp [htop.symm]
  have hbot_topA : (⊥ : Submodule F V) ∉ ({⊤, A} : Finset (Submodule F V)) := by
    simp [hbot.symm, hbot_ne_top]
  have hcard3 : ({⊥, ⊤, A} : Finset (Submodule F V)).card = 3 := by
    rw [Finset.card_insert_of_notMem hbot_topA, Finset.card_insert_of_notMem htop_bot,
      Finset.card_singleton]
  have : 3 ≤ G.carrier.card := hcard3.symm.trans_le (Finset.card_le_card h3)
  omega

theorem faceSum_eq_zero_of_len_one {V : FGModuleCat.{0} F} {X : Type} [AddCommGroup X] [Module k X]
    (G : Flag F V) (hG : G.len = 1) (γ : X →ₗ[k] (Flag F V → k)) :
    faceSum X G γ = 0 := by
  unfold faceSum
  apply Finset.sum_eq_zero
  intro A hA
  have hpair := flag_carrier_eq_pair_of_len_one G hG A hA
  have hnot : ¬ (A ≠ ⊥ ∧ A ≠ ⊤) := by
    rcases hpair with rfl | rfl
    · intro h; exact h.1 rfl
    · intro h; exact h.2 rfl
  simp [hnot]

/-- The differential vanishes on degree-0 cochains of the exponential bicomodule. -/
theorem d_exp_zero (α : RawCochain (EBicomod.exp (F := F) (k := k)))
    (hα : α ∈ cochains (EBicomod.exp (F := F) (k := k)) 0) :
    d (EBicomod.exp (F := F) (k := k)) 0 α = 0 := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  change dRaw (EBicomod.exp) 0 α V z G = 0
  dsimp [dRaw]
  split_ifs with hG
  · have hG1 : G.nth 1 = ⊤ := by
      have : G.len = 1 := hG
      rw [← this, Flag.nth_len]
    have hG0 : G.nth 0 = ⊥ := Flag.nth_zero G
    have hq : finrank F (quo (⊤ : Submodule F V)) = 0 := finrank_quo_top V
    have hs : finrank F (sub (⊥ : Submodule F V)) = 0 := finrank_bot F V
    have hface : faceSum (EBicomod.exp.X.ev V) G (α V) = 0 :=
      faceSum_eq_zero_of_len_one G hG (α V)
    rw [hG1, hG0]
    change α (quo ⊤) z (G.project ⊤) + faceSum _ G (α V) z +
      (-1 : k) ^ 1 • (α (sub ⊥) z (G.restrict ⊥)) = 0
    rw [hface]
    have ht1 : α (quo ⊤) z (G.project ⊤) = expVal V z * expZeroEquiv ⟨α, hα⟩ :=
      expZero_apply_of_finrank_zero ⟨α, hα⟩ (quo ⊤) hq z (G.project ⊤)
    have ht3 : α (sub ⊥) z (G.restrict ⊥) = expVal V z * expZeroEquiv ⟨α, hα⟩ :=
      expZero_apply_of_finrank_zero ⟨α, hα⟩ (sub ⊥) hs z (G.restrict ⊥)
    rw [ht1, ht3]
    simp
  · rfl

/-- In degree 0, the coboundaries of the exponential bicomodule vanish by definition. -/
theorem coboundaries_exp_zero :
    coboundaries (EBicomod.exp (F := F) (k := k)) 0 = ⊥ := rfl

/-- In degree 0, every cochain of the exponential bicomodule is a cocycle. -/
theorem cocycles_exp_zero :
    cocycles (EBicomod.exp (F := F) (k := k)) 0 = cochains (EBicomod.exp (F := F) (k := k)) 0 := by
  apply le_antisymm inf_le_left
  rw [le_inf_iff]
  refine ⟨le_rfl, fun α hα => ?_⟩
  rw [LinearMap.mem_ker]
  exact d_exp_zero α hα

/-- The space of degree-0 cocycles of the exponential bicomodule has dimension 1. -/
theorem finrank_cocycles_exp_zero :
    Module.finrank k (cocycles (EBicomod.exp (F := F) (k := k)) 0) = 1 := by
  have h := (LinearEquiv.ofEq _ _ (cocycles_exp_zero (F := F) (k := k))).finrank_eq
  rw [h, finrank_cochains_exp_zero]

/-- The canonical linear equivalence between `H⁰(e)` and degree-0 cocycles. -/
def H_exp_zero_equiv_cocycles :
    H (EBicomod.exp (F := F) (k := k)) 0 ≃ₗ[k]
      cocycles (EBicomod.exp (F := F) (k := k)) 0 := by
  have hp : (coboundaries (EBicomod.exp (F := F) (k := k)) 0).comap
      (cocycles (EBicomod.exp (F := F) (k := k)) 0).subtype = ⊥ := by
    rw [coboundaries_exp_zero, Submodule.comap_bot, Submodule.ker_subtype]
  exact Submodule.quotEquivOfEqBot _ hp

/-- The degree-0 cohomology `H⁰(e)` has dimension 1. -/
theorem finrank_H_exp_zero :
    Module.finrank k (H (EBicomod.exp (F := F) (k := k)) 0) = 1 := by
  exact (H_exp_zero_equiv_cocycles (F := F) (k := k)).finrank_eq.trans
    (finrank_cocycles_exp_zero (F := F) (k := k))

end MartinPhd

end
end ExpZero

section ExpDim

/-!
## The dimension cocycle of the exponential bicomodule

`α(V, z, G) = dim V · z` on flags of length one is a nonzero degree-1 cocycle of `e`
(the cobar differential gives `dα(V,z,G) = z(dim V/A - dim V + dim A) = 0`).
-/

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section
namespace MartinPhd
open MartinPhd.ExpD

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] {k : Type} [Field k]

/-- The raw cochain `(V, z, G) ↦ dim V · z` on flags of length one. -/
def expDimCochain : RawCochain (EBicomod.exp (F := F) (k := k)) := fun V =>
  LinearMap.pi fun G : Flag F V => if G.len = 1 then (finrank F V : k) • expVal V else 0

theorem expDimCochain_apply (V : FGModuleCat.{0} F) (z : (EBicomod.exp (F := F) (k := k)).X.ev V)
    (G : Flag F V) :
    expDimCochain V z G = if G.len = 1 then (finrank F V : k) * expVal V z else 0 := by
  unfold expDimCochain
  by_cases h : G.len = 1 <;> simp [h]

theorem expDimCochain_mem : expDimCochain (F := F) (k := k) ∈ cochains (EBicomod.exp (F := F) (k := k)) 1 := by
  refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
  · rw [expDimCochain_apply, if_neg hG]
  · rw [expDimCochain_apply, expDimCochain_apply, Flag.len_map, expVal_mapEquiv,
      (LinearEquiv.finrank_eq e).symm]

/-- A flag all of whose members are `⊥` or `⊤` (in a nontrivial space) has length one. -/
theorem len_eq_one_of_pair {V : Type} [AddCommGroup V] [Module F V] (H : Flag F V)
    (h : ∀ B ∈ H.carrier, B = ⊥ ∨ B = ⊤) (hne : (⊥ : Submodule F V) ≠ ⊤) : H.len = 1 := by
  have hc : H.carrier = {⊥, ⊤} := by
    ext B
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact h B
    · rintro (rfl | rfl)
      · exact H.bot_mem
      · exact H.top_mem
  have := H.card_eq_len_succ
  rw [hc, Finset.card_insert_of_notMem (by simpa using hne)] at this
  simp at this
  omega

theorem mem_len_two {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = 2) :
    ∀ B ∈ G.carrier, B = ⊥ ∨ B = G.nth 1 ∨ B = ⊤ := by
  intro B hB
  have hi := G.nth_index hB
  have hlt : G.index B < 3 := by
    have := G.index_lt_card hB
    have := G.card_eq_len_succ
    omega
  by_cases h0 : G.index B = 0
  · left; rw [← hi, h0, G.nth_zero]
  by_cases h2 : G.index B = 2
  · right; right; rw [← hi, h2, ← hG, G.nth_len]
  · right; left
    have : G.index B = 1 := by omega
    rw [← hi, this]

theorem bot_ne_top_of_len_two {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = 2) :
    (⊥ : Submodule F V) ≠ ⊤ := by
  intro h
  apply (expD_nth_one_proper G hG).1
  apply le_bot_iff.1
  rw [h]
  exact le_top

theorem project_len {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = 2) :
    (G.project (G.nth 1)).len = 1 := by
  have hp := expD_nth_one_proper G hG
  have hne : (⊥ : Submodule F (V ⧸ G.nth 1)) ≠ ⊤ := by
    intro h
    obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hp.2)
    apply hv
    have hmem : Submodule.Quotient.mk v ∈ (⊤ : Submodule F (V ⧸ G.nth 1)) := Submodule.mem_top
    rw [← h, Submodule.mem_bot] at hmem
    exact (Submodule.Quotient.mk_eq_zero _).1 hmem
  refine len_eq_one_of_pair _ (fun B hB => ?_) hne
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hB
  rcases mem_len_two G hG C hC with rfl | rfl | rfl
  · left; exact Submodule.map_bot _
  · left; exact Submodule.mkQ_map_self _
  · right; rw [Submodule.map_top, Submodule.range_mkQ]

theorem restrict_len {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = 2) :
    (G.restrict (G.nth 1)).len = 1 := by
  have hp := expD_nth_one_proper G hG
  have hnt : Nontrivial (G.nth 1) := Submodule.nontrivial_iff_ne_bot.2 hp.1
  refine len_eq_one_of_pair _ (fun B hB => ?_) (bot_ne_top (α := Submodule F (G.nth 1)))
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hB
  rcases mem_len_two G hG C hC with rfl | rfl | rfl
  · left; exact Submodule.ker_subtype _
  · right; exact Submodule.comap_subtype_self _
  · right; exact Submodule.comap_top _

theorem erase_len {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = 2) :
    (G.erase (G.nth 1) (expD_nth_one_proper G hG)).len = 1 := by
  refine len_eq_one_of_pair _ (fun B hB => ?_) (bot_ne_top_of_len_two G hG)
  have hB' : B ∈ G.carrier.erase (G.nth 1) := hB
  rw [Finset.mem_erase] at hB'
  rcases mem_len_two G hG B hB'.2 with h | h | h
  · left; exact h
  · exact absurd h hB'.1
  · right; exact h

theorem d_dimCochain : d (EBicomod.exp (F := F) (k := k)) 1 expDimCochain = 0 := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  by_cases hG : G.len = 2
  · rw [d_exp_one_apply _ V G hG (show k from z)]
    have hq := Submodule.finrank_quotient_add_finrank (G.nth 1)
    rw [expDimCochain_apply, expDimCochain_apply, expDimCochain_apply, if_pos (project_len G hG),
      if_pos (erase_len G hG), if_pos (restrict_len G hG)]
    show (show k from z) * ((finrank F (V ⧸ G.nth 1) : k) * 1 - (finrank F V : k) * 1 +
      (finrank F (G.nth 1) : k) * 1) = 0
    have : (finrank F (V ⧸ G.nth 1) : k) * 1 - (finrank F V : k) * 1 +
        (finrank F (G.nth 1) : k) * 1 = 0 := by
      rw [← hq]; push_cast; ring
    rw [this, mul_zero]
  · show dRaw _ 1 expDimCochain V z G = 0
    simp only [dRaw, LinearMap.pi_apply]
    rw [if_neg (by omega)]
    rfl

theorem expDimCochain_cocycle : expDimCochain (F := F) (k := k) ∈ cocycles (EBicomod.exp (F := F) (k := k)) 1 :=
  ⟨expDimCochain_mem, LinearMap.mem_ker.2 d_dimCochain⟩

theorem expDimCochain_ne_zero : (expDimCochain (F := F) (k := k)) ≠ 0 := by
  intro h
  let V₁ : FGModuleCat.{0} F := FGModuleCat.of F F
  have hne : (⊥ : Submodule F V₁) ≠ ⊤ := bot_ne_top
  have hlen : (Flag.trivial : Flag F V₁).len = 1 :=
    len_eq_one_of_pair _ (fun B hB => by
      simp only [Flag.trivial, Finset.mem_insert, Finset.mem_singleton] at hB; exact hB) hne
  have := congrArg (fun f : RawCochain (EBicomod.exp (F := F) (k := k)) =>
    f V₁ (expUnit V₁) (Flag.trivial : Flag F V₁)) h
  simp only [expDimCochain_apply, hlen, if_true] at this
  have hfr : finrank F V₁ = 1 := Module.finrank_self F
  rw [hfr] at this
  simp [expVal_expUnit] at this

end MartinPhd

end
end ExpDim

section ExpInj

/-!
## Injectivity of evaluation on degree-1 cocycles of the exponential bicomodule

A degree-1 cocycle `α` of `e` is determined by `a(V) = α(V, 1, trivial flag)`, which depends only
on `dim V` and satisfies `a(V/A) - a(V) + a(A) = 0`; hence `a(V) = dim V · a(V₁)`.
-/

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section
namespace MartinPhd
open MartinPhd.ExpD

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] {k : Type} [Field k]

theorem carrier_eq_of_len_one {V : FGModuleCat.{0} F} (G : Flag F V) (hG : G.len = 1) :
    G.carrier = {⊥, ⊤} := by
  ext B
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact flag_carrier_eq_pair_of_len_one G hG B
  · rintro (rfl | rfl)
    · exact G.bot_mem
    · exact G.top_mem

theorem flag_eq_of_len_one {V : FGModuleCat.{0} F} (G G' : Flag F V) (hG : G.len = 1)
    (hG' : G'.len = 1) : G = G' :=
  Flag.ext ((carrier_eq_of_len_one G hG).trans (carrier_eq_of_len_one G' hG').symm)

variable {α : RawCochain (EBicomod.exp (F := F) (k := k))}

theorem val_eq_of_finrank_eq (hα : α ∈ cochains (EBicomod.exp (F := F) (k := k)) 1)
    (V W : FGModuleCat.{0} F) (h : finrank F V = finrank F W) (G : Flag F V) (hG : G.len = 1)
    (G' : Flag F W) (hG' : G'.len = 1) : α V (expUnit V) G = α W (expUnit W) G' := by
  have e : V ≃ₗ[F] W := LinearEquiv.ofFinrankEq V W h
  have h1 := hα.2 V W e (expUnit V) G
  have hlen : (G.map e).len = 1 := by rw [Flag.len_map]; exact hG
  rw [flag_eq_of_len_one _ G' hlen hG'] at h1
  exact h1.symm

theorem exists_len_two_flag (V : FGModuleCat.{0} F) (h : 2 ≤ finrank F V) :
    ∃ G : Flag F V, G.len = 2 := by
  have hpos : 0 < finrank F V := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  set A : Submodule F V := Submodule.span F {v} with hA
  have hAbot : A ≠ ⊥ := by
    intro h0
    apply hv
    have : v ∈ A := Submodule.subset_span rfl
    rw [h0, Submodule.mem_bot] at this
    exact this
  have hfin : finrank F A = 1 := finrank_span_singleton hv
  have hAtop : A ≠ ⊤ := by
    intro ht
    have : finrank F A = finrank F V := by rw [ht]; exact finrank_top F V
    omega
  have hbt : (⊥ : Submodule F V) ≠ ⊤ := fun h0 => hAbot (by
    apply le_bot_iff.1; rw [h0]; exact le_top)
  refine ⟨Flag.ofSubspace A, ?_⟩
  have hc := (Flag.ofSubspace A).card_eq_len_succ
  have hcard : (Flag.ofSubspace A).carrier.card = 3 := by
    show ({⊥, A, ⊤} : Finset (Submodule F V)).card = 3
    rw [Finset.card_insert_of_notMem (by simp [hAbot.symm, hbt]),
      Finset.card_insert_of_notMem (by simp [hAtop]), Finset.card_singleton]
  omega

theorem exp_cocycle_vanishes [Fintype F] (hα : α ∈ cocycles (EBicomod.exp (F := F) (k := k)) 1)
    (V₁ : FGModuleCat.{0} F) (hV₁ : finrank F V₁ = 1) (G₁ : Flag F V₁) (hG₁ : G₁.len = 1)
    (h : α V₁ 1 G₁ = 0) :
    ∀ (m : ℕ) (V : FGModuleCat.{0} F), finrank F V = m → ∀ G : Flag F V, G.len = 1 →
      α V 1 G = 0 := by
  intro m
  induction m using Nat.strong_induction_on with | _ m ih => ?_
  intro V hV G hG
  have hd1 : 1 ≤ m := by
    have := ST.len_le_finrank (F := F) G
    omega
  by_cases hd : m = 1
  · exact (val_eq_of_finrank_eq hα.1 V V₁ (by omega) G hG G₁ hG₁).trans h
  · have hd2 : 2 ≤ m := by omega
    obtain ⟨G2, hG2⟩ := exists_len_two_flag V (by omega)
    have hp := expD_nth_one_proper G2 hG2
    set B := G2.nth 1 with hB
    have hker : d (EBicomod.exp (F := F) (k := k)) 1 α = 0 := LinearMap.mem_ker.1 hα.2
    have h0 : d (EBicomod.exp (F := F) (k := k)) 1 α V (1 : k) G2 = 0 := by
      have := congrArg (fun f : RawCochain (EBicomod.exp (F := F) (k := k)) => f V (1 : k) G2) hker
      exact this
    rw [d_exp_one_apply α V G2 hG2 (1 : k)] at h0
    have hBpos : 1 ≤ finrank F B := by
      by_contra hc
      apply hp.1
      exact Submodule.finrank_eq_zero.1 (by omega)
    have hBlt : finrank F B < m := by
      rw [← hV]; exact Submodule.finrank_lt hp.2
    have hq := Submodule.finrank_quotient_add_finrank B
    have hI1 : α (quo B) 1 (G2.project B) = 0 :=
      ih (finrank F (V ⧸ B)) (by rw [← hV] at hBlt ⊢; omega) (quo B) rfl _ (project_len G2 hG2)
    have hI3 : α (sub B) 1 (G2.restrict B) = 0 :=
      ih (finrank F B) hBlt (sub B) rfl _ (restrict_len G2 hG2)
    rw [hI1, hI3, one_mul] at h0
    have h2 : α V 1 (G2.erase B (expD_nth_one_proper G2 hG2)) = 0 := by
      have : (0 : k) - α V 1 (G2.erase B (expD_nth_one_proper G2 hG2)) + 0 = 0 := h0
      have h' : α V 1 (G2.erase B (expD_nth_one_proper G2 hG2)) = 0 := by
        have := this; simp at this; exact this
      exact h'
    rw [flag_eq_of_len_one G (G2.erase B (expD_nth_one_proper G2 hG2)) hG (erase_len G2 hG2)]
    exact h2

end MartinPhd

end
end ExpInj
