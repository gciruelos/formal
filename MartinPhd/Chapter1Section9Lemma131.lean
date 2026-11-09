import MartinPhd.Chapter1Section9FlagSpeciesCohomology
import MartinPhd.Chapter1Section6Steinberg
import MartinPhd.Chapter1Section5SubspacesFlagVarieties
import MartinPhd.Chapter1Section7SpectralSequence
import MartinPhd.Chapter1Section6Bruhat
import MartinPhd.Chapter1Section7Convergence

/-!
# Chapter 1, Section 1.9 (Lemma 1.31 and cup products)

Contents:
* Lemma131Dim
* Lemma131Map
* Lemma131
* Chapter1Section9
* CupAlpha
* CupDetect
-/

section Lemma131Dim

/-! Fixed-space dimensions for the first-page computation in Lemma 1.31. -/
open Module
noncomputable section
namespace MartinPhd
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Top flag cohomology and the Steinberg dual have the same fixed spaces. -/
theorem hsigmaFixed_equiv_dual_invariants (n : ℕ) (H : Subgroup (GLn F n)) :
    Nonempty (hsigmaFixed (F := F) (k := k) n H ≃ₗ[k]
      Representation.invariants ((stRep (F := F) (k := k) n H).dual)) := by
  classical
  obtain ⟨e, he⟩ := cor_1_9_equivariant (F := F) (k := k) n
  have hact (g : H) (x : HSigma F k n n) (c : steinberg F k n) :
      ((stRep (F := F) (k := k) n H).dual g (e x)) c =
        e (hsigmaRep F k n n g.1 x) c := by
    change e x (stAct F k (g.1⁻¹) c) = _
    have h := he g.1 x (stAct F k (g.1⁻¹) c)
    have hi : stAct F k g.1 (stAct F k (g.1⁻¹) c) = c := by
      change (stAct F k g.1 ∘ₗ stAct F k (g.1⁻¹)) c = c
      rw [← stAct_mul, mul_inv_cancel, stAct_one]
      rfl
    rw [hi] at h
    exact h.symm
  refine ⟨{
    toFun := fun x => ⟨e x.1, by
      intro g
      apply LinearMap.ext
      intro c
      rw [hact, x.2 g.1 g.2]⟩
    invFun := fun y => ⟨e.symm y.1, by
      intro g hg
      apply e.injective
      apply LinearMap.ext
      intro c
      rw [← hact ⟨g, hg⟩ (e.symm y.1) c]
      have h := congrArg (fun f : Module.Dual k (steinberg F k n) => f c) (y.2 ⟨g, hg⟩)
      simpa using h⟩
    left_inv := fun x => by apply Subtype.ext; simp
    right_inv := fun y => by apply Subtype.ext; simp
    map_add' := fun x y => by apply Subtype.ext; simp
    map_smul' := fun a x => by apply Subtype.ext; simp }⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Top cohomology and Steinberg have equal fixed-space dimensions. -/
theorem finrank_hsigmaFixed [CharZero k] (n : ℕ) (H : Subgroup (GLn F n)) :
    finrank k (hsigmaFixed (F := F) (k := k) n H) = finrank k (stFixed F k H) := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨e⟩ := hsigmaFixed_equiv_dual_invariants (F := F) (k := k) n H
  have hd := Representation.finrank_invariants_dual (stRep (F := F) (k := k) n H)
  have hf := congrArg (fun S : Submodule k (steinberg F k n) => finrank k S)
    (stFixed_eq_invariants (F := F) (k := k) n H)
  exact (LinearEquiv.finrank_eq e).trans (hd.trans hf.symm)

/-- The top-cohomology Borel-fixed space is one-dimensional. -/
theorem finrank_hsigmaFixed_borel [CharZero k] (n : ℕ) :
    finrank k (hsigmaFixed (F := F) (k := k) n (borel F n)) = 1 := by
  rw [finrank_hsigmaFixed, finrank_stFixed_borel]

/-- Proper supergroups of the Borel have no invariants in top flag cohomology. -/
theorem hsigmaFixed_eq_bot_of_borel_lt [CharZero k] (n : ℕ) (H : Subgroup (GLn F n))
    (hH : borel F n < H) : hsigmaFixed (F := F) (k := k) n H = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [finrank_hsigmaFixed, (lemma_1_23 (F := F) (k := k) n).2 H hH, finrank_bot]
end MartinPhd

end
end Lemma131Dim

section Lemma131Map

/-! Evaluation of diagonal E₁ classes at the standard complete flag. -/
open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the equivariant cohomology-valued map on the standard flag. -/
def e1StdEval (p : ℕ) : E (flagBicomod F k) 1 p p →ₗ[k] HSigma F k p p :=
  Submodule.liftQ _
    ({ toFun := fun z => (Theta (flagBicomod F k) p p z).1 (Finsupp.single (stdFlag F p) 1)
       map_add' := by
         intro z w
         rw [map_add]
         change ((Theta (flagBicomod F k) p p z).1 + (Theta (flagBicomod F k) p p w).1) _ = _
         rw [LinearMap.add_apply]
       map_smul' := by
         intro c z
         rw [map_smul]
         change (c • (Theta (flagBicomod F k) p p z).1) _ = _
         rw [LinearMap.smul_apply]
         rfl } :
      Zpage (flagBicomod F k) 1 p p →ₗ[k] HSigma F k p p)
    (by
      intro z hz
      rw [LinearMap.mem_ker]
      have h := Theta_eq_zero_of_Bpage (flagBicomod F k) p p z hz
      change (Theta (flagBicomod F k) p p z).1 _ = 0
      rw [h]
      rfl)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation always takes values fixed by the standard Borel. -/
theorem e1StdEval_mem_fixed (p : ℕ) (z : E (flagBicomod F k) 1 p p) :
    e1StdEval (F := F) (k := k) p z ∈ hsigmaFixed p (borel F p) := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    intro g hg
    change hsigmaRep F k p p g ((Theta (flagBicomod F k) p p z).1
      (Finsupp.single (stdFlag F p) 1)) = _
    have h := LinearMap.congr_fun ((Theta (flagBicomod F k) p p z).2 g)
      (Finsupp.single (stdFlag F p) 1)
    change (Theta (flagBicomod F k) p p z).1
      (((flagBicomod F k).X.rep p g) (Finsupp.single (stdFlag F p) 1)) =
      hsigmaRep F k p p g ((Theta (flagBicomod F k) p p z).1
        (Finsupp.single (stdFlag F p) 1)) at h
    change hsigmaRep F k p p g ((Theta (flagBicomod F k) p p z).1
      (Finsupp.single (stdFlag F p) 1)) = (Theta (flagBicomod F k) p p z).1
      (Finsupp.single (stdFlag F p) 1)
    rw [← h]
    congr 1
    change (Finsupp.lmapDomain k k (Flag.map g)) (Finsupp.single (stdFlag F p) 1) = _
    simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    change Finsupp.single (g • stdFlag F p) 1 = _
    rw [show g • stdFlag F p = stdFlag F p from hg]

/-- A complete flag has trivial relative position from the standard flag precisely when it is standard. -/
theorem jh_std_eq_one_iff (p : ℕ) (G : Flag F (Fin p → F)) (hG : G.IsComplete) :
    jh p (stdFlag F p) G = 1 ↔ G = stdFlag F p := by
  have hself : jh p (stdFlag F p) (stdFlag F p) = 1 := by
    have h := jh_perm_smul (F := F) p (1 : Equiv.Perm (Fin p))
    have hp : permToGL F (1 : Equiv.Perm (Fin p)) = 1 := by ext v i; rfl
    simpa [hp] using h
  constructor
  · intro h
    obtain ⟨g, hg, hgG⟩ := (bruhat_pair_orbit p _ _ _ _
      (bruhat_std_complete p) hG (bruhat_std_complete p) (bruhat_std_complete p)).2
      (h.trans hself.symm)
    exact (MulAction.injective g) (hgG.trans hg.symm)
  · rintro rfl
    exact hself

/-- The identity Schubert cell contains only the standard flag. -/
theorem deltaElt_one_eq_single (p : ℕ) :
    deltaElt (F := F) (k := k) (1 : Equiv.Perm (Fin p)) =
      Finsupp.single (stdFlag F p) 1 := by
  ext G
  rw [deltaElt_apply]
  by_cases hG : G.IsComplete
  · simp only [hG, true_and, jh_std_eq_one_iff p G hG, Finsupp.single_apply]
    simp [eq_comm]
  · have hne : G ≠ stdFlag F p := fun h => hG (h ▸ bruhat_std_complete p)
    simp [hG, Finsupp.single_apply, hne, Ne.symm hne]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The standard diagonal cocycle evaluates to the identity Schubert class. -/
theorem e1StdEval_alpha (p : ℕ) :
    e1StdEval (F := F) (k := k) p (Subquot.mk _ (alphaCochain_mem p)) =
      deltaClass (1 : Equiv.Perm (Fin p)) := by
  change piSig F k p p (lam (flagBicomod F k) p p
    ⟨alphaCochain p, alphaCochain_mem p⟩ (Finsupp.single (stdFlag F p) 1)) = _
  change Subquot.mk (Tlin (flagBicomod F k) p (alphaCochain p)
    (Finsupp.single (stdFlag F p) 1)) _ = Subquot.mk (deltaElt (1 : Equiv.Perm (Fin p))) _
  congr 1
  rw [deltaElt_one_eq_single]
  ext G
  rw [Tlin_apply, alphaCochain_apply]
  by_cases h : G = stdFlag F p
  · subst G
    simp [bruhat_std_complete, Module.finrank_fin_fun]
  · simp [Finsupp.single_apply, h, Ne.symm h]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- An equivariant map vanishes if it vanishes on the standard flag and on every incomplete flag. -/
theorem equivariantHom_eq_zero_of_std_and_incomplete (p : ℕ)
    (f : equivariantHom ((flagBicomod F k).X.rep p) (hsigmaRep F k p p))
    (hstd : f.1 (Finsupp.single (stdFlag F p) 1) = 0)
    (hincomplete : ∀ G : Flag F (Fin p → F), ¬ G.IsComplete → f.1 (Finsupp.single G 1) = 0) :
    f = 0 := by
  apply Subtype.ext
  apply Finsupp.lhom_ext
  intro G c
  have hc : Finsupp.single G c = c • Finsupp.single G (1 : k) := by simp
  rw [hc, map_smul]
  erw [LinearMap.zero_apply]
  have hg : f.1 (Finsupp.single G 1) = 0 := by
    by_cases hG : G.IsComplete
    · obtain ⟨g, rfl⟩ := exists_smul_stdFlag G hG
      have he := LinearMap.congr_fun (f.2 g) (Finsupp.single (stdFlag F p) 1)
      change f.1 (((flagBicomod F k).X.rep p g) (Finsupp.single (stdFlag F p) 1)) =
        hsigmaRep F k p p g (f.1 (Finsupp.single (stdFlag F p) 1)) at he
      have hs : ((flagBicomod F k).X.rep p g) (Finsupp.single (stdFlag F p) 1) =
          Finsupp.single (g • stdFlag F p) 1 := by
        change Finsupp.lmapDomain k k (Flag.map g) (Finsupp.single (stdFlag F p) 1) = _
        simp [Finsupp.lmapDomain_apply]; rfl
      rw [hs, hstd, map_zero] at he
      exact he
    · exact hincomplete G hG
  exact (congrArg (c • ·) hg).trans (smul_zero c)

end MartinPhd

end
end Lemma131Map

section Lemma131

/-! # Lemma 1.31

`E₁^{p,0}(Σ) ≅ H^p(Σ_p^•)^B`, via evaluation at the standard flag. -/
open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem rep_single (p : ℕ) (g : GLn F p) (G : Flag F (Fin p → F)) :
    ((flagBicomod F k).X.rep p g) (Finsupp.single G 1) = Finsupp.single (g • G) 1 := by
  change Finsupp.lmapDomain k k (Flag.map g) (Finsupp.single G 1) = _
  simp [Finsupp.lmapDomain_apply]; rfl

theorem smul_isComplete_iff {p : ℕ} (g : GLn F p) (G : Flag F (Fin p → F)) :
    (g • G).IsComplete ↔ G.IsComplete := by
  change (G.map g).IsComplete ↔ _
  simp only [Flag.IsComplete, Flag.len_map]

/-- Equivariant maps out of the flag module vanish on incomplete flags (Lemmas 1.13, 1.23). -/
theorem equivariantHom_incomplete [CharZero k] (p : ℕ)
    (f : equivariantHom ((flagBicomod F k).X.rep p) (hsigmaRep F k p p))
    (G : Flag F (Fin p → F)) (hG : ¬ G.IsComplete) : f.1 (Finsupp.single G 1) = 0 := by
  have hn : finrank F (Fin p → F) = p := Module.finrank_fin_fun F
  set c := G.toComposition hn with hc
  obtain ⟨g, hg⟩ := exists_smul_stdFlagOfType c G (Flag.toComposition_isOfType hn G)
  have hle : borel F p ≤ parabolic F c := stdFlag_stabilizer_le F c
  have hlt : borel F p < parabolic F c := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : stdFlag F p = stdFlagOfType F c := (Flag.eq_iff_stabilizer_eq _ _).2 heq
    apply hG
    rw [← hg, ← h1, smul_isComplete_iff]
    exact stdFlag_isComplete p
  set v := f.1 (Finsupp.single G 1) with hv
  have hw : hsigmaRep F k p p g⁻¹ v ∈ hsigmaFixed p (parabolic F c) := by
    intro s hs
    have hs' : (g * s * g⁻¹) • G = G := by
      have : s • stdFlagOfType F c = stdFlagOfType F c := hs
      rw [← hg, ← mul_smul, show g * s * g⁻¹ * g = g * s by group, mul_smul, this]
    have he := LinearMap.congr_fun (f.2 (g * s * g⁻¹)) (Finsupp.single G 1)
    change f.1 (((flagBicomod F k).X.rep p (g * s * g⁻¹)) (Finsupp.single G 1)) =
      hsigmaRep F k p p (g * s * g⁻¹) (f.1 (Finsupp.single G 1)) at he
    rw [rep_single, hs'] at he
    have h2 : hsigmaRep F k p p s (hsigmaRep F k p p g⁻¹ v) =
        hsigmaRep F k p p g⁻¹ (hsigmaRep F k p p (g * s * g⁻¹) v) := by
      have := LinearMap.congr_fun (map_mul (hsigmaRep F k p p) g⁻¹ (g * s * g⁻¹)) v
      rw [show g⁻¹ * (g * s * g⁻¹) = s * g⁻¹ by group, map_mul] at this
      exact this
    rw [h2, ← he]
  have h0 : hsigmaRep F k p p g⁻¹ v = 0 := by
    have := hsigmaFixed_eq_bot_of_borel_lt (F := F) (k := k) p _ hlt
    rw [this] at hw
    exact (Submodule.mem_bot k).1 hw
  have : v = hsigmaRep F k p p g (hsigmaRep F k p p g⁻¹ v) := by
    have h := LinearMap.congr_fun (map_mul (hsigmaRep F k p p) g g⁻¹) v
    rw [mul_inv_cancel, map_one] at h
    exact h
  rw [this, h0, map_zero]

theorem hsigmaRep_eq_of_smul_eq {p : ℕ} {v : HSigma F k p p} (hv : v ∈ hsigmaFixed p (borel F p))
    (g₁ g₂ : GLn F p) (h : g₁ • stdFlag F p = g₂ • stdFlag F p) :
    hsigmaRep F k p p g₁ v = hsigmaRep F k p p g₂ v := by
  have hb : g₂⁻¹ * g₁ ∈ borel F p := by
    show (g₂⁻¹ * g₁) • stdFlag F p = stdFlag F p
    rw [mul_smul, h, inv_smul_smul]
  have h1 := hv _ hb
  have h2 := LinearMap.congr_fun (map_mul (hsigmaRep F k p p) g₂ (g₂⁻¹ * g₁)) v
  rw [show g₂ * (g₂⁻¹ * g₁) = g₁ by group] at h2
  rw [h2]
  change hsigmaRep F k p p g₂ (hsigmaRep F k p p (g₂⁻¹ * g₁) v) = _
  rw [h1]

/-- The candidate equivariant extension of a Borel-fixed vector: `G = g • std ↦ g • v` on
complete flags, `0` on incomplete ones. -/
def extendFixed (p : ℕ) (v : HSigma F k p p) :
    (Flag F (Fin p → F) →₀ k) →ₗ[k] HSigma F k p p :=
  Finsupp.linearCombination k fun G =>
    if hG : G.IsComplete then
      hsigmaRep F k p p (Classical.choose (exists_smul_stdFlag G hG)) v else 0

theorem exists_equivariant_of_fixed (p : ℕ) (v : HSigma F k p p)
    (hv : v ∈ hsigmaFixed p (borel F p)) :
    ∃ f : equivariantHom ((flagBicomod F k).X.rep p) (hsigmaRep F k p p),
      f.1 (Finsupp.single (stdFlag F p) 1) = v := by
  have hφ : ∀ G hG, (Classical.choose (exists_smul_stdFlag G hG)) • stdFlag F p = G :=
    fun G hG => Classical.choose_spec (exists_smul_stdFlag G hG)
  refine ⟨⟨extendFixed (F := F) (k := k) p v, fun g => ?_⟩, ?_⟩
  · refine Finsupp.lhom_ext' fun G => LinearMap.ext_ring ?_
    show extendFixed p v (((flagBicomod F k).X.rep p g) (Finsupp.single G 1)) =
      hsigmaRep F k p p g (extendFixed p v (Finsupp.single G 1))
    rw [rep_single]
    simp only [extendFixed, Finsupp.linearCombination_single, one_smul]
    by_cases hG : G.IsComplete
    · have hgG : (g • G).IsComplete := (smul_isComplete_iff g G).2 hG
      rw [dif_pos hG, dif_pos hgG]
      have h1 := hφ G hG
      have h2 := hφ (g • G) hgG
      have : Classical.choose (exists_smul_stdFlag (g • G) hgG) • stdFlag F p =
          (g * Classical.choose (exists_smul_stdFlag G hG)) • stdFlag F p := by
        rw [h2, mul_smul, h1]
      rw [hsigmaRep_eq_of_smul_eq hv _ _ this, map_mul]; rfl
    · have hgG : ¬ (g • G).IsComplete := fun h => hG ((smul_isComplete_iff g G).1 h)
      rw [dif_neg hG, dif_neg hgG, map_zero]
  · show extendFixed p v (Finsupp.single (stdFlag F p) 1) = v
    simp only [extendFixed, Finsupp.linearCombination_single, one_smul]
    rw [dif_pos (stdFlag_isComplete p)]
    exact hv _ (hφ _ (stdFlag_isComplete p))

theorem e1StdEval_injective [CharZero k] (p : ℕ) :
    Function.Injective (e1StdEval (F := F) (k := k) p) := by
  have hx := GLSpecies.isRelativelyProjective_of_charZero (F := F) (k := k) (flagBicomod F k).X
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | _ a =>
    have hz' : (Theta (flagBicomod F k) p p a).1 (Finsupp.single (stdFlag F p) 1) = 0 := hz
    have hT : Theta (flagBicomod F k) p p a = 0 :=
      equivariantHom_eq_zero_of_std_and_incomplete p _ hz'
        (fun G hG => equivariantHom_incomplete p _ G hG)
    have := Bpage_of_Theta_eq_zero (flagBicomod F k) p p hx a hT
    exact (Submodule.Quotient.mk_eq_zero _).2 this

theorem e1StdEval_range [CharZero k] (p : ℕ) :
    LinearMap.range (e1StdEval (F := F) (k := k) p) = hsigmaFixed p (borel F p) := by
  have hx := GLSpecies.isRelativelyProjective_of_charZero (F := F) (k := k) (flagBicomod F k).X
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩; exact e1StdEval_mem_fixed p z
  · intro v hv
    obtain ⟨f, hf⟩ := exists_equivariant_of_fixed p v hv
    obtain ⟨a, ha⟩ := Theta_surj (flagBicomod F k) p p hx f
    refine ⟨Submodule.Quotient.mk a, ?_⟩
    change (Theta (flagBicomod F k) p p a).1 (Finsupp.single (stdFlag F p) 1) = v
    rw [ha]; exact hf

/-- **Lemma 1.31.** `E₁^{p,0}(Σ) ≅ H^p(Σ_p^•)^B` (composing Lemmas 1.25 and 1.30 with
Lemmas 1.22 and 1.23); in particular it is one-dimensional. The identification sends the
class of `α_p` to `[δ_{id,p}]`. -/
theorem lemma_1_31 [CharZero k] (p : ℕ) :
    ∃ Φ : E (flagBicomod F k) 1 p p →ₗ[k] HSigma F k p p,
      Function.Injective Φ ∧ LinearMap.range Φ = hsigmaFixed p (borel F p) ∧
      Φ (Subquot.mk _ (alphaCochain_mem p)) = deltaClass (1 : Equiv.Perm (Fin p)) ∧
      finrank k (E (flagBicomod F k) 1 p p) = 1 :=
  by
  refine ⟨e1StdEval p, e1StdEval_injective p, e1StdEval_range p, e1StdEval_alpha p, ?_⟩
  rw [← LinearMap.finrank_range_of_inj (e1StdEval_injective (F := F) (k := k) p),
    e1StdEval_range, finrank_hsigmaFixed_borel]

end MartinPhd

end
end Lemma131

section Chapter1Section9

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §1.9 La cohomología de las especies de banderas -/

section FlagCohomology

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]
/-- The indicator of a Schubert cell is invariant under the standard Borel. -/
theorem deltaElt_borel_invariant {p : ℕ} (σ : Equiv.Perm (Fin p))
    (g : GLn F p) (hg : g ∈ borel F p) :
    flagRep F k p g (deltaElt σ) = deltaElt σ := by
  have hfix : g • stdFlag F p = stdFlag F p := hg
  have hpred (G : Flag F (Fin p → F)) :
      (g • G).IsComplete ∧ jh p (stdFlag F p) (g • G) = σ ↔
        G.IsComplete ∧ jh p (stdFlag F p) G = σ := by
    have hj := jh_smul p (stdFlag F p) G g
    rw [hfix] at hj
    change (G.map g).IsComplete ∧ _ ↔ G.IsComplete ∧ _
    simp only [Flag.IsComplete, Flag.len_map, hj]
  unfold deltaElt
  rw [map_sum]
  refine Finset.sum_equiv (MulAction.toPerm g) (fun G => ?_) (fun G hG => ?_)
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      MulAction.toPerm_apply] using (hpred G).symm
  · simp [flagRep]

/-- The Schubert-cell class belongs to the Borel-fixed subspace. -/
theorem deltaClass_mem_hsigmaFixed {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    deltaClass (F := F) (k := k) σ ∈ hsigmaFixed p (borel F p) := by
  intro g hg
  change Subquot.mk (flagRep F k p g (deltaElt σ)) _ = Subquot.mk (deltaElt σ) _
  congr 1
  exact deltaElt_borel_invariant σ g hg

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Lemma 1.32.** `E₁^{p,0}(Σ)` is spanned by `[δ_{σ,p}]` for any `σ ∈ S_p`, and
`[δ_{σ,p}] = (-1)^{inv σ} [δ_{id,p}]`. -/
theorem lemma_1_32 [CharZero k] (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    deltaClass (F := F) (k := k) σ = ((-1 : k) ^ inv σ) • deltaClass (F := F) (1 : Equiv.Perm (Fin p)) ∧
    deltaClass (F := F) (k := k) σ ∈ hsigmaFixed p (borel F p) ∧
    Submodule.span k {deltaClass (F := F) (k := k) σ} = hsigmaFixed p (borel F p) := by
  classical
  obtain ⟨Φ, hΦ, hrange, _, hdim⟩ := lemma_1_31 (F := F) (k := k) p
  have hd : finrank k (hsigmaFixed (F := F) (k := k) p (borel F p)) = 1 := by
    rw [← hrange, LinearMap.finrank_range_of_inj hΦ, hdim]
  obtain ⟨e, he⟩ := (cor_1_9 F k p).2
  let ε : steinberg F k p := ⟨epsSteinberg F k p, by
    rw [steinberg_eq, epsSteinberg_eq]; exact ST.eps_mem_St k _⟩
  have hev (τ : Equiv.Perm (Fin p)) :
      e (deltaClass (F := F) (k := k) τ) ε = (-1 : k) ^ inv τ := by
    rw [deltaClass, he]
    exact deltaElt_pair_eps τ
  have hne (τ : Equiv.Perm (Fin p)) : deltaClass (F := F) (k := k) τ ≠ 0 := by
    intro h
    have hv := hev τ
    rw [h, map_zero, LinearMap.zero_apply] at hv
    exact (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hv.symm
  let v : hsigmaFixed (F := F) (k := k) p (borel F p) :=
    ⟨deltaClass (1 : Equiv.Perm (Fin p)), deltaClass_mem_hsigmaFixed _⟩
  let w : hsigmaFixed (F := F) (k := k) p (borel F p) :=
    ⟨deltaClass σ, deltaClass_mem_hsigmaFixed _⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd
    (show v ≠ 0 from fun h => hne 1 (congrArg Subtype.val h)) w
  have hcv : c • deltaClass (F := F) (k := k) (1 : Equiv.Perm (Fin p)) = deltaClass σ :=
    congrArg Subtype.val hc
  have hscalar : c = (-1 : k) ^ inv σ := by
    have hv := congrArg (fun x => e x ε) hcv
    rw [map_smul, LinearMap.smul_apply, hev, hev] at hv
    have hi : inv (1 : Equiv.Perm (Fin p)) = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro x _ hx
      simp only [Equiv.Perm.one_apply] at hx
      exact (not_lt_of_ge (le_of_lt hx.1)) hx.2
    simpa only [hi, pow_zero, smul_eq_mul, mul_one] using hv
  refine ⟨by rw [← hcv, hscalar], deltaClass_mem_hsigmaFixed σ, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.span_le.mpr (by simpa using deltaClass_mem_hsigmaFixed (F := F) (k := k) σ)
  · rw [finrank_span_singleton (hne σ), hd]

/-- **Lemma 1.33.** A complete flag `F` in `Fⁿ` lies in the Schubert cell of a
`j`-shuffle iff `F = F⁰ ∗ S` for some `j`-dimensional `S ≤ Fⁿ`. -/
theorem lemma_1_33 (n j : ℕ) (G : Flag F (Fin n → F)) (hG : G.IsComplete) :
    (∃ X : Finset (Fin n), X.card = j ∧ jh n (stdFlag F n) G = shuffle X) ↔
      ∃ S : Submodule F (Fin n → F), finrank F S = j ∧ G = (stdFlag F n).convSub S := by
  have hn : finrank F (Fin n → F) = n := Module.finrank_fin_fun F
  have hstd : stdFlag F n = jhFlag (Pi.basisFun F (Fin n)) :=
    (stdFlag_eq_flagOf F n).trans (Flag.ext rfl)
  have hF : (stdFlag F n).IsComplete := by
    rw [hstd]; unfold Flag.IsComplete Flag.len; rw [jhFlag_card, hn]; rfl
  obtain ⟨b, σ, hFb, hGb⟩ := jh_exists_common_permutation n hn _ _ hF hG
  have hjh : jh n (stdFlag F n) G = σ := by rw [hFb, hGb, jh_jhFlag]
  constructor
  · rintro ⟨X, hX, hXσ⟩
    refine ⟨Submodule.span F (b '' (X : Set (Fin n))), ?_, ?_⟩
    · rw [finrank_span_basis_image, hX]
    · rw [hFb, convSub_jhFlag b hn X, hGb, ← hjh, hXσ]
  · rintro ⟨S, hS, hGS⟩
    have hSmem : S ∈ G.carrier := by
      rw [hGS, Flag.convSub_carrier]
      refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨⊤, (stdFlag F n).top_mem, ?_⟩)
      simp
    rw [hGb] at hSmem
    obtain ⟨m, _, hm⟩ := Finset.mem_image.1 hSmem
    rw [reindex_flag_eq] at hm
    set X : Finset (Fin n) := Finset.univ.filter fun x => ∃ l : Fin n, l.val < m.val ∧ σ l = x
      with hX
    have hXS : S = Submodule.span F (b '' (X : Set (Fin n))) := by
      rw [← hm]; congr 2; ext x; simp only [hX, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq, Set.mem_image]
    refine ⟨X, ?_, ?_⟩
    · rw [← finrank_span_basis_image b X, ← hXS, hS]
    · have : G = jhFlag (b.reindex (shuffle X).symm) := by
        rw [hGS, hXS, hFb]; exact convSub_jhFlag b hn X
      rw [this, hFb, jh_jhFlag]

/-- The unit 0-cochain (the counit of `Σ`). -/
def oneCochain : RawCochain (flagBicomod F k) := fun V =>
  Finsupp.linearCombination k fun _ : Flag F V => fun G : Flag F V =>
    if G.len = 0 then 1 else 0

/-- Cup powers `sch^{⌣m}`. -/
def schPow : ℕ → RawCochain (flagBicomod F k)
  | 0 => oneCochain
  | m + 1 => cupRaw (flagCoalg F k) 2 (2 * m) schCochain (schPow m)

/-- Restriction of cochains along the inclusion `L → Σ`. -/
def restrictCochain : RawCochain (flagBicomod F k) →ₗ[k] RawCochain (completeFlagBicomod F k) where
  toFun α V := α V ∘ₗ ((completeFlagInclusion F k).app ⟨V⟩).hom
  map_add' α β := by
    funext V
    exact LinearMap.add_comp ((completeFlagInclusion F k).app ⟨V⟩).hom (β V) (α V)
  map_smul' a α := by
    funext V
    exact LinearMap.smul_comp a (α V) ((completeFlagInclusion F k).app ⟨V⟩).hom

theorem restrictCochain_apply (α : RawCochain (flagBicomod F k)) (V : FGModuleCat.{0} F)
    (z : (completeFlagBicomod F k).X.ev V) (G : Flag F V) :
    restrictCochain α V z G = α V (z.1 : (flagBicomod F k).X.ev V) G := rfl

theorem restrictCochain_d (n : ℕ) (α : RawCochain (flagBicomod F k)) :
    restrictCochain (d (flagBicomod F k) n α) = d (completeFlagBicomod F k) n (restrictCochain α) := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  show dRaw (flagBicomod F k) n α V z.1 G = dRaw (completeFlagBicomod F k) n (restrictCochain α) V z G
  have e1 : dRaw (flagBicomod F k) n α V z.1 G =
      (if G.len = n + 1 then
        (LinearMap.proj (G.project (G.nth 1)) ∘ₗ α (quo (G.nth 1)) ∘ₗ (flagBicomod F k).proj V (G.nth 1)) +
          faceSum _ G (α V) +
        ((-1 : k) ^ (n + 1)) • (LinearMap.proj (G.restrict (G.nth n)) ∘ₗ α (sub (G.nth n)) ∘ₗ
          (flagBicomod F k).res V (G.nth n))
      else 0) z.1 := rfl
  have e2 : dRaw (completeFlagBicomod F k) n (restrictCochain α) V z G =
      (if G.len = n + 1 then
        (LinearMap.proj (G.project (G.nth 1)) ∘ₗ restrictCochain α (quo (G.nth 1)) ∘ₗ
          (completeFlagBicomod F k).proj V (G.nth 1)) +
          faceSum _ G (restrictCochain α V) +
        ((-1 : k) ^ (n + 1)) • (LinearMap.proj (G.restrict (G.nth n)) ∘ₗ
          restrictCochain α (sub (G.nth n)) ∘ₗ (completeFlagBicomod F k).res V (G.nth n))
      else 0) z := rfl
  rw [e1, e2]
  by_cases hG : G.len = n + 1
  · rw [if_pos hG, if_pos hG]
    erw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.add_apply, LinearMap.smul_apply]
    congr 2
    unfold faceSum
    erw [LinearMap.sum_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases h : A ≠ ⊥ ∧ A ≠ ⊤
    · simp only [dif_pos h]; rfl
    · simp only [dif_neg h]; rfl
  · rw [if_neg hG, if_neg hG]
    rfl

theorem restrictCochain_mem_cochains (n : ℕ) {α : RawCochain (flagBicomod F k)}
    (hα : α ∈ cochains (flagBicomod F k) n) : restrictCochain α ∈ cochains (completeFlagBicomod F k) n :=
  ⟨fun V z G hG => hα.1 V z.1 G hG, fun V W e z G => hα.2 V W e z.1 G⟩

theorem restrictCochain_cocycles (n : ℕ) :
    cocycles (flagBicomod F k) n ≤ (cocycles (completeFlagBicomod F k) n).comap restrictCochain := by
  intro α hα
  refine ⟨restrictCochain_mem_cochains n hα.1, ?_⟩
  have h0 : d (flagBicomod F k) n α = 0 := hα.2
  have := restrictCochain_d n α
  rw [h0, map_zero] at this
  exact this.symm

theorem restrictCochain_coboundaries (n : ℕ) :
    coboundaries (flagBicomod F k) n ⊓ cocycles (flagBicomod F k) n ≤
      (coboundaries (completeFlagBicomod F k) n).comap restrictCochain := by
  intro α hα
  cases n with
  | zero =>
    have : α = 0 := by simpa [coboundaries] using hα.1
    rw [this]; exact zero_mem _
  | succ m =>
    obtain ⟨β, hβ, rfl⟩ := hα.1
    exact ⟨restrictCochain β, restrictCochain_mem_cochains m hβ, (restrictCochain_d m β).symm⟩

set_option maxHeartbeats 1600000 in
theorem comul_incl_lin (V : FGModuleCat.{0} F) (S : Submodule F V) :
    (TensorProduct.map (((completeFlagInclusion F k).app ⟨sub S⟩).hom)
        (((completeFlagInclusion F k).app ⟨quo S⟩).hom) ∘ₗ (completeFlagCoalg F k).comul V S) =
      (flagCoalg F k).comul V S ∘ₗ ((completeFlagInclusion F k).app ⟨V⟩).hom := by
  let e := (Finsupp.supportedEquivFinsupp (M := k) (R := k) {G : Flag F V | G.IsComplete})
  have h : (TensorProduct.map (((completeFlagInclusion F k).app ⟨sub S⟩).hom)
        (((completeFlagInclusion F k).app ⟨quo S⟩).hom) ∘ₗ (completeFlagCoalg F k).comul V S) ∘ₗ
        e.symm.toLinearMap =
      ((flagCoalg F k).comul V S ∘ₗ ((completeFlagInclusion F k).app ⟨V⟩).hom) ∘ₗ
        e.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro H c
    have h1 : (completeFlagCoalg F k).comul V S (e.symm (Finsupp.single H c)) =
        c • ((⟨Finsupp.single (H.1.restrict S) (1 : k),
            Finsupp.single_mem_supported k 1 (Flag.isComplete_restrict H.1 S H.2)⟩ :
          Finsupp.supported k k {G : Flag F (sub S) | G.IsComplete}) ⊗ₜ[k]
        (⟨Finsupp.single (H.1.project S) (1 : k),
            Finsupp.single_mem_supported k 1 (Flag.isComplete_project H.1 S H.2)⟩ :
          Finsupp.supported k k {G : Flag F (quo S) | G.IsComplete})) := by
      show (Finsupp.linearCombination k _) (e (e.symm (Finsupp.single H c))) = _
      rw [LinearEquiv.apply_symm_apply]
      erw [Finsupp.linearCombination_single]
      rfl
    have h2 : (((completeFlagInclusion F k).app ⟨V⟩).hom) (e.symm (Finsupp.single H c)) =
        Finsupp.single H.1 c := by
      show ((e.symm (Finsupp.single H c) : Finsupp.supported k k _) : Flag F V →₀ k) = _
      rw [Finsupp.supportedEquivFinsupp_symm_apply_coe]
      exact Finsupp.extendDomain_single H c
    have h3 : TensorProduct.map
        (Submodule.subtype (Finsupp.supported k k {G : Flag F (sub S) | G.IsComplete}))
        (Submodule.subtype (Finsupp.supported k k {G : Flag F (quo S) | G.IsComplete}))
        (c • ((⟨Finsupp.single (H.1.restrict S) (1 : k),
            Finsupp.single_mem_supported k 1 (Flag.isComplete_restrict H.1 S H.2)⟩ :
          Finsupp.supported k k {G : Flag F (sub S) | G.IsComplete}) ⊗ₜ[k]
        (⟨Finsupp.single (H.1.project S) (1 : k),
            Finsupp.single_mem_supported k 1 (Flag.isComplete_project H.1 S H.2)⟩ :
          Finsupp.supported k k {G : Flag F (quo S) | G.IsComplete}))) =
        c • ((Finsupp.single (H.1.restrict S) (1 : k)) ⊗ₜ[k]
          (Finsupp.single (H.1.project S) (1 : k))) := by
      rw [map_smul, TensorProduct.map_tmul]; rfl
    have h4 : (Finsupp.linearCombination k (fun H : Flag F V =>
          (Finsupp.single (H.restrict S) (1 : k)) ⊗ₜ[k] (Finsupp.single (H.project S) (1 : k))) :
          (Flag F V →₀ k) →ₗ[k] (Flag F (sub S) →₀ k) ⊗[k] (Flag F (quo S) →₀ k))
          (Finsupp.single H.1 c) =
        c • ((Finsupp.single (H.1.restrict S) (1 : k)) ⊗ₜ[k]
          (Finsupp.single (H.1.project S) (1 : k))) := by
      rw [Finsupp.linearCombination_single]
    show TensorProduct.map _ _ ((completeFlagCoalg F k).comul V S (e.symm (Finsupp.single H c))) =
      (flagCoalg F k).comul V S (((completeFlagInclusion F k).app ⟨V⟩).hom
        (e.symm (Finsupp.single H c)))
    rw [h1, h2]
    exact h3.trans h4.symm
  exact (LinearMap.cancel_right e.symm.surjective).1 h

theorem comul_incl (V : FGModuleCat.{0} F) (S : Submodule F V)
    (z : (completeFlagBicomod F k).X.ev V) :
    TensorProduct.map (((completeFlagInclusion F k).app ⟨sub S⟩).hom)
        (((completeFlagInclusion F k).app ⟨quo S⟩).hom)
        ((completeFlagCoalg F k).comul V S z) =
      (flagCoalg F k).comul V S (((completeFlagInclusion F k).app ⟨V⟩).hom z) :=
  LinearMap.congr_fun (comul_incl_lin V S) z

/-- Restriction is multiplicative (`L` is a sub-coalgebra of `Σ`). -/
theorem cup_aux {M₁ M₂ N₁ N₂ P Q : Type} [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂]
    [Module k M₂] [AddCommGroup N₁] [Module k N₁] [AddCommGroup N₂] [Module k N₂]
    [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
    (A : M₁ →ₗ[k] k) (B : M₂ →ₗ[k] k) (ι₁ : N₁ →ₗ[k] M₁) (ι₂ : N₂ →ₗ[k] M₂) (ι : P →ₗ[k] Q)
    (cL : P →ₗ[k] TensorProduct k N₁ N₂) (cS : Q →ₗ[k] TensorProduct k M₁ M₂)
    (h : TensorProduct.map ι₁ ι₂ ∘ₗ cL = cS ∘ₗ ι) (z : P) :
    (LinearMap.mul' k k ∘ₗ TensorProduct.map A B ∘ₗ cS) (ι z) =
      (LinearMap.mul' k k ∘ₗ TensorProduct.map (A ∘ₗ ι₁) (B ∘ₗ ι₂) ∘ₗ cL) z := by
  have := LinearMap.congr_fun h z
  simp only [LinearMap.comp_apply] at this ⊢
  rw [← this, ← LinearMap.comp_apply (TensorProduct.map A B), ← TensorProduct.map_comp]

theorem restrictCochain_cup (m n : ℕ) (f g : RawCochain (flagBicomod F k)) :
    restrictCochain (cupRaw (flagCoalg F k) m n f g) =
      cupRaw (completeFlagCoalg F k) m n (restrictCochain f) (restrictCochain g) := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  show cupRaw (flagCoalg F k) m n f g V (((completeFlagInclusion F k).app ⟨V⟩).hom z) G =
    cupRaw (completeFlagCoalg F k) m n (restrictCochain f) (restrictCochain g) V z G
  unfold cupRaw
  erw [LinearMap.pi_apply, LinearMap.pi_apply]
  by_cases hG : G.len = m + n
  · rw [if_pos hG, if_pos hG]
    exact cup_aux _ _ _ _ _ _ _ (comul_incl_lin (k := k) V (G.nth m)) z
  · rw [if_neg hG, if_neg hG]; rfl

end FlagCohomology

end MartinPhd

end
end Chapter1Section9

section CupAlpha

open scoped BigOperators TensorProduct
open CategoryTheory Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

/-- Cup products of the diagonal cochains, evaluated on a basis flag. -/
theorem cup_alpha_single (m n : ℕ) (V : FGModuleCat.{0} F) (H G : Flag F V) :
    cupRaw (flagCoalg F k) m n (alphaCochain m) (alphaCochain n)
      V (Finsupp.single H 1) G =
      if G.len = m + n then
        (if finrank F (G.nth m) = m ∧ (H.restrict (G.nth m)).IsComplete ∧
          G.restrict (G.nth m) = H.restrict (G.nth m) then (1 : k) else 0) *
        (if finrank F (V ⧸ G.nth m) = n ∧ (H.project (G.nth m)).IsComplete ∧
          G.project (G.nth m) = H.project (G.nth m) then (1 : k) else 0)
      else 0 := by
  change (if G.len = m + n then
    LinearMap.mul' k k ∘ₗ
      TensorProduct.map (LinearMap.proj (G.restrict (G.nth m)) ∘ₗ alphaCochain m (sub (G.nth m)))
        (LinearMap.proj (G.project (G.nth m)) ∘ₗ alphaCochain n (quo (G.nth m))) ∘ₗ
      (flagCoalg F k).comul V (G.nth m)
    else 0) (Finsupp.single H 1) = _
  by_cases h : G.len = m + n
  · rw [if_pos h, if_pos h]
    change (LinearMap.mul' k k) (TensorProduct.map
      (LinearMap.proj (G.restrict (G.nth m)) ∘ₗ alphaCochain m (sub (G.nth m)))
      (LinearMap.proj (G.project (G.nth m)) ∘ₗ alphaCochain n (quo (G.nth m)))
      ((flagCoalg F k).comul V (G.nth m) (Finsupp.single H 1))) = _
    have hd : (flagCoalg F k).comul V (G.nth m) (Finsupp.single H 1) =
        (Finsupp.single (H.restrict (G.nth m)) (1 : k)) ⊗ₜ[k]
          (Finsupp.single (H.project (G.nth m)) (1 : k)) := by
      change (Finsupp.linearCombination k fun H : Flag F V =>
        (Finsupp.single (H.restrict (G.nth m)) (1 : k)) ⊗ₜ[k]
          (Finsupp.single (H.project (G.nth m)) (1 : k))) (Finsupp.single H 1) = _
      rw [Finsupp.linearCombination_single, one_smul]
    rw [hd]
    change (LinearMap.mul' k k) (TensorProduct.map
      (LinearMap.proj (G.restrict (G.nth m)) ∘ₗ
        Finsupp.linearCombination k (fun J : Flag F (G.nth m) => fun K : Flag F (G.nth m) =>
          if finrank F (G.nth m) = m ∧ J.IsComplete ∧ K = J then (1 : k) else 0))
      (LinearMap.proj (G.project (G.nth m)) ∘ₗ
        Finsupp.linearCombination k (fun J : Flag F (V ⧸ G.nth m) => fun K : Flag F (V ⧸ G.nth m) =>
          if finrank F (V ⧸ G.nth m) = n ∧ J.IsComplete ∧ K = J then (1 : k) else 0))
      ((Finsupp.single (H.restrict (G.nth m)) (1 : k)) ⊗ₜ[k]
        (Finsupp.single (H.project (G.nth m)) (1 : k)))) = _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply,
      Finsupp.linearCombination_single, one_smul]
  · rw [if_neg h, if_neg h]
    rfl

/-- In top degree, the cup value is the indicator that the two induced flags agree. -/
theorem cup_alpha_single_complete (m n : ℕ) (V : FGModuleCat.{0} F)
    (hV : finrank F V = m + n) (H G : Flag F V)
    (hH : H.IsComplete) (hG : G.IsComplete) :
    cupRaw (flagCoalg F k) m n (alphaCochain m) (alphaCochain n)
      V (Finsupp.single H 1) G =
      if G.restrict (G.nth m) = H.restrict (G.nth m) ∧
        G.project (G.nth m) = H.project (G.nth m) then (1 : k) else 0 := by
  have hlen : G.len = m + n := hG.trans hV
  have hm : finrank F (G.nth m) = m := G.finrank_nth_of_isComplete hG (by omega)
  have hn : finrank F (V ⧸ G.nth m) = n := by
    have h := (G.nth m).finrank_quotient_add_finrank
    rw [hm, hV] at h
    omega
  rw [cup_alpha_single, if_pos hlen]
  have hc1 := Flag.isComplete_restrict H (G.nth m) hH
  have hc2 := Flag.isComplete_project H (G.nth m) hH
  simp only [hm, hn, hc1, hc2, true_and]
  split_ifs <;> simp_all

/-- Convolution at a member of a flag leaves it unchanged. -/
theorem Flag.convSub_eq_self_of_mem {V : Type*} [AddCommGroup V] [Module F V]
    (G : Flag F V) {S : Submodule F V} (hS : S ∈ G.carrier) : G.convSub S = G := by
  apply Flag.ext
  rw [Flag.convSub_carrier]
  ext A
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨B, hB, rfl⟩ | ⟨B, hB, rfl⟩)
    · rcases G.isChain.total hS hB with h | h
      · simpa [inf_eq_left.mpr h] using hS
      · simpa [inf_eq_right.mpr h] using hB
    · rcases G.isChain.total hS hB with h | h
      · simpa [sup_eq_right.mpr h] using hB
      · simpa [sup_eq_left.mpr h] using hS
  · intro hA
    rcases G.isChain.total hS hA with h | h
    · exact Or.inr ⟨A, hA, sup_eq_right.mpr h⟩
    · exact Or.inl ⟨A, hA, inf_eq_right.mpr h⟩


/-- Restriction of convolution recovers the restricted flag. -/
theorem Flag.restrict_convSub {V : Type*} [AddCommGroup V] [Module F V]
    (H : Flag F V) (S : Submodule F V) : (H.convSub S).restrict S = H.restrict S := by
  apply Flag.ext
  change ((H.convSub S).carrier.image (Submodule.comap S.subtype)) =
    H.carrier.image (Submodule.comap S.subtype)
  rw [Flag.convSub_carrier, Finset.image_union, Finset.image_image, Finset.image_image]
  have h1 (B : Submodule F V) : (S ⊓ B).comap S.subtype = B.comap S.subtype := by
    ext x
    simp [Submodule.mem_comap]
  have h2 (B : Submodule F V) : (S ⊔ B).comap S.subtype = ⊤ := by
    apply top_unique
    intro x _
    exact Submodule.mem_sup_left x.property
  simp only [Function.comp_def, h1, h2]
  apply Finset.union_eq_left.mpr
  intro A hA
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
  exact Finset.mem_image.mpr ⟨⊤, H.top_mem, by simp⟩


/-- Projection of convolution recovers the projected flag. -/
theorem Flag.project_convSub {V : Type*} [AddCommGroup V] [Module F V]
    (H : Flag F V) (S : Submodule F V) : (H.convSub S).project S = H.project S := by
  apply Flag.ext
  change ((H.convSub S).carrier.image (Submodule.map S.mkQ)) =
    H.carrier.image (Submodule.map S.mkQ)
  rw [Flag.convSub_carrier, Finset.image_union, Finset.image_image, Finset.image_image]
  have h0 : S.map S.mkQ = ⊥ := by
    apply bot_unique
    rintro x ⟨y, hy, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero S).mpr hy
  have h1 (B : Submodule F V) : (S ⊓ B).map S.mkQ = ⊥ := by
    apply bot_unique
    calc (S ⊓ B).map S.mkQ ≤ S.map S.mkQ := Submodule.map_mono inf_le_left
      _ = ⊥ := h0
  have h2 (B : Submodule F V) : (S ⊔ B).map S.mkQ = B.map S.mkQ := by
    rw [Submodule.map_sup, h0, bot_sup_eq]
  simp only [Function.comp_def, h1, h2]
  apply Finset.union_eq_right.mpr
  intro A hA
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
  exact Finset.mem_image.mpr ⟨⊥, H.bot_mem, by simp⟩

/-- At a member of `G`, convolution equality is equivalent to the two induced flags agreeing. -/
theorem Flag.eq_convSub_iff {V : Type*} [AddCommGroup V] [Module F V]
    (H G : Flag F V) {S : Submodule F V} (hS : S ∈ G.carrier) :
    G = H.convSub S ↔ G.restrict S = H.restrict S ∧ G.project S = H.project S := by
  constructor
  · intro h
    rw [h, Flag.restrict_convSub, Flag.project_convSub]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hr, hp⟩
    calc G = G.convSub S := (G.convSub_eq_self_of_mem hS).symm
      _ = H.convSub S := by unfold Flag.convSub; rw [hr, hp]


/-- For complete flags, the cup product is the indicator of convolution. -/
theorem cup_alpha_single_convSub (m n : ℕ) (V : FGModuleCat.{0} F)
    (hV : finrank F V = m + n) (H G : Flag F V)
    (hH : H.IsComplete) (hG : G.IsComplete) :
    cupRaw (flagCoalg F k) m n (alphaCochain m) (alphaCochain n)
      V (Finsupp.single H 1) G =
      if G = H.convSub (G.nth m) then (1 : k) else 0 := by
  have hm : m < G.carrier.card := by
    rw [G.card_eq_len_succ, hG, hV]
    omega
  rw [cup_alpha_single_complete m n V hV H G hH hG]
  simp only [← Flag.eq_convSub_iff H G (G.nth_mem hm).1]


/-- A complete flag passing through a subspace places it at its dimension. -/
theorem Flag.nth_finrank_of_mem {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (G : Flag F V) (hG : G.IsComplete)
    {S : Submodule F V} (hS : S ∈ G.carrier) : G.nth (finrank F S) = S := by
  have hi : G.index S ≤ G.len := by
    have := G.index_lt_card hS
    rw [G.card_eq_len_succ] at this
    omega
  have h := G.finrank_nth_of_isComplete hG hi
  rw [G.nth_index hS] at h
  rw [h, G.nth_index hS]

/-- The convolution test can equivalently quantify over subspaces of the first degree. -/
theorem eq_convSub_nth_iff {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (m : ℕ) (H G : Flag F V) (hG : G.IsComplete)
    (hm : m ≤ G.len) :
    G = H.convSub (G.nth m) ↔
      ∃ S : Submodule F V, finrank F S = m ∧ G = H.convSub S := by
  constructor
  · intro h
    exact ⟨G.nth m, G.finrank_nth_of_isComplete hG hm, h⟩
  · rintro ⟨S, hS, he⟩
    have hmem : S ∈ G.carrier := by
      rw [he, Flag.convSub_carrier]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⊤, H.top_mem, by simp⟩)
    have hn : G.nth m = S := by rw [← hS]; exact G.nth_finrank_of_mem hG hmem
    rwa [hn]

/-- On apartment flags the cup coefficient tests whether the permutation is a shuffle. -/
theorem cup_alpha_perm (m n : ℕ) (τ : Equiv.Perm (Fin (m + n))) :
    cupRaw (flagCoalg F k) m n (alphaCochain m) (alphaCochain n)
      (stdSpace F (m + n)) (Finsupp.single (stdFlag F (m + n)) 1)
      (permToGL F τ • stdFlag F (m + n)) =
      if ∃ X : Finset (Fin (m + n)), X.card = m ∧ τ = shuffle X then (1 : k) else 0 := by
  have hH : (stdFlag F (m + n)).IsComplete := by
    rw [Flag.IsComplete, stdFlag_eq_flagOf, ST.len_flagOf, Module.finrank_fin_fun]
  have hG : (permToGL F τ • stdFlag F (m + n)).IsComplete := by
    change ((stdFlag F (m + n)).map (permToGL F τ)).IsComplete
    simpa only [Flag.IsComplete, Flag.len_map] using hH
  rw [cup_alpha_single_convSub m n _ (Module.finrank_fin_fun F) _ _ hH hG]
  have hm : m ≤ (permToGL F τ • stdFlag F (m + n)).len := by
    change m ≤ ((stdFlag F (m + n)).map (permToGL F τ)).len
    rw [Flag.len_map, hH, Module.finrank_fin_fun]
    omega
  rw [eq_convSub_nth_iff m _ _ hG hm, ← lemma_1_33 (m + n) m _ hG, jh_perm_smul]
  simp


/-- The cup product's evaluation on the standard apartment is the signed shuffle sum. -/
theorem cup_alpha_pair_eps (m n : ℕ) :
    flagPairing F k (m + n)
      ((Finsupp.linearEquivFunOnFinite k k (Flag F (Fin (m + n) → F))).symm
        (cupRaw (flagCoalg F k) m n (alphaCochain m) (alphaCochain n)
          (stdSpace F (m + n)) (Finsupp.single (stdFlag F (m + n)) 1))) (epsSteinberg F k (m + n)) =
      ∑ X ∈ Finset.univ.filter (fun X : Finset (Fin (m + n)) => X.card = m),
        (-1 : k) ^ inv (shuffle X) := by
  classical
  let A : Finset (Finset (Fin (m + n))) := Finset.univ.filter fun X => X.card = m
  let B : Finset (Equiv.Perm (Fin (m + n))) := Finset.univ.filter fun τ =>
    ∃ X : Finset (Fin (m + n)), X.card = m ∧ τ = shuffle X
  have hsum : (∑ X ∈ A, (-1 : k) ^ inv (shuffle X)) =
      ∑ τ ∈ B, (-1 : k) ^ inv τ := by
    apply Finset.sum_bij (fun X _ => shuffle X)
    · intro X hX
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, X, (Finset.mem_filter.mp hX).2, rfl⟩
    · intro X hX Y hY hXY
      have hx := (Finset.mem_filter.mp hX).2
      have hy := (Finset.mem_filter.mp hY).2
      apply Finset.ext
      intro u
      have h1 := shuffle_mem_iff X ((shuffle X).symm u)
      have h2 := shuffle_mem_iff Y ((shuffle X).symm u)
      rw [← hXY] at h2
      rw [hx] at h1
      rw [hy] at h2
      simpa only [Equiv.apply_symm_apply] using h1.trans h2.symm
    · intro τ hτ
      obtain ⟨X, hX, hτX⟩ := (Finset.mem_filter.mp hτ).2
      exact ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩, hτX.symm⟩
    · intro X hX
      rfl
  rw [hsum]
  change flagBil F k (m + n) _ (epsSteinberg F k (m + n)) = _
  simp only [epsSteinberg, map_sum, map_smul]
  have he (τ : Equiv.Perm (Fin (m + n))) :
      flagBil F k (m + n)
        ((Finsupp.linearEquivFunOnFinite k k (Flag F (Fin (m + n) → F))).symm
        (cupRaw (flagCoalg F k) m n (alphaCochain m) (alphaCochain n)
          (stdSpace F (m + n)) (Finsupp.single (stdFlag F (m + n)) 1)))
        (Finsupp.single (permToGL F τ • stdFlag F (m + n)) 1) =
      if ∃ X : Finset (Fin (m + n)), X.card = m ∧ τ = shuffle X then (1 : k) else 0 := by
    change flagPairing F k (m + n) _ _ = _
    rw [flagPairing_single]
    change cupRaw (flagCoalg F k) m n (alphaCochain m) (alphaCochain n)
      (stdSpace F (m + n)) (Finsupp.single (stdFlag F (m + n)) 1)
      (permToGL F τ • stdFlag F (m + n)) = _
    exact cup_alpha_perm m n τ
  simp only [he, smul_eq_mul]
  simp [B, Finset.sum_filter, mul_ite]


end MartinPhd

end
end CupAlpha

section CupDetect

open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

private theorem subquot_mk_eq_zero_iff {M : Type*} [AddCommGroup M] [Module k M]
    {A B : Submodule k M} {a : M} (ha : a ∈ A) :
    (Subquot.mk a ha : Subquot A B) = 0 ↔ a ∈ B := by
  exact Submodule.Quotient.mk_eq_zero _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- The diagonal representative evaluates to one on the standard apartment. -/
theorem alpha_apartment_pairing (p : ℕ) :
    flagPairing F k p (Tlin (flagBicomod F k) p (alphaCochain p)
      (Finsupp.single (stdFlag F p) 1)) (epsSteinberg F k p) = 1 := by
  change flagBil F k p (Tlin (flagBicomod F k) p (alphaCochain p)
    (Finsupp.single (stdFlag F p) 1)) (epsSteinberg F k p) = 1
  simp only [epsSteinberg, map_sum, map_smul]
  have heval (τ : Equiv.Perm (Fin p)) :
      flagBil F k p (Tlin (flagBicomod F k) p (alphaCochain p)
        (Finsupp.single (stdFlag F p) 1))
        (Finsupp.single (permToGL F τ • stdFlag F p) 1) =
          if τ = 1 then 1 else 0 := by
    change flagPairing F k p _ _ = _
    rw [flagPairing_single]
    change alphaCochain p (stdSpace F p) (Finsupp.single (stdFlag F p) 1)
      (permToGL F τ • stdFlag F p) = _
    change (Finsupp.linearCombination k (fun H : Flag F (Fin p → F) =>
      fun G : Flag F (Fin p → F) =>
        if finrank F (Fin p → F) = p ∧ H.IsComplete ∧ G = H then (1 : k) else 0))
      (Finsupp.single (stdFlag F p) 1) (permToGL F τ • stdFlag F p) = _
    rw [Finsupp.linearCombination_single, one_smul]
    have hs : (stdFlag F p).IsComplete := by
      rw [Flag.IsComplete, stdFlag_eq_flagOf, ST.len_flagOf, Module.finrank_fin_fun]
    have hc : (permToGL F τ • stdFlag F p).IsComplete := by
      change ((stdFlag F p).map (permToGL F τ)).IsComplete
      rw [Flag.IsComplete, Flag.len_map, stdFlag_eq_flagOf, ST.len_flagOf,
        Module.finrank_fin_fun]
    have hp1 : permToGL F (1 : Equiv.Perm (Fin p)) = 1 := by
      ext v i
      rfl
    have heq : permToGL F τ • stdFlag F p = stdFlag F p ↔ τ = 1 := by
      constructor
      · intro h
        have hj := jh_perm_smul (F := F) p τ
        rw [h] at hj
        have hj1 := jh_perm_smul (F := F) p (1 : Equiv.Perm (Fin p))
        rw [hp1, one_smul] at hj1
        exact hj.symm.trans hj1
      · rintro rfl; rw [hp1, one_smul]
    simp [Module.finrank_fin_fun, hs, hc, heq]
  simp only [heval, smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hi : inv (1 : Equiv.Perm (Fin p)) = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro z _ hz
    simp only [Equiv.Perm.one_apply] at hz
    exact (not_lt_of_ge (le_of_lt hz.1)) hz.2
  rw [hi, pow_zero]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Evaluation on the standard apartment detects classes on the diagonal first page. -/
theorem diagonal_mem_Bpage_iff [CharZero k] (p : ℕ) (a : RawCochain (flagBicomod F k))
    (ha : a ∈ Zpage (flagBicomod F k) 1 p p) :
    a ∈ Bpage (flagBicomod F k) 1 p p ↔
      flagPairing F k p (Tlin (flagBicomod F k) p a
        (Finsupp.single (stdFlag F p) 1)) (epsSteinberg F k p) = 0 := by
  let x := flagBicomod F k
  obtain ⟨e, he⟩ := (cor_1_9 F k p).2
  let ε : steinberg F k p := ⟨epsSteinberg F k p, by
    rw [steinberg_eq, epsSteinberg_eq]; exact ST.eps_mem_St k _⟩
  let f : Zpage x 1 p p →ₗ[k] k :=
    { toFun := fun z => e ((Theta x p p z).1 (Finsupp.single (stdFlag F p) 1)) ε
      map_add' := by
        intro z w
        rw [map_add]
        change e ((Theta x p p z).1 _ + (Theta x p p w).1 _) ε = _
        rw [map_add, LinearMap.add_apply]
      map_smul' := by
        intro c z
        rw [map_smul]
        change e (c • (Theta x p p z).1 _) ε = _
        rw [map_smul, LinearMap.smul_apply]
        rfl }
  have hf (z : Zpage x 1 p p) : f z = flagPairing F k p
      (Tlin x p z.1 (Finsupp.single (stdFlag F p) 1)) (epsSteinberg F k p) := by
    exact he _ _ ε
  have hkill : (Bpage x 1 p p).comap (Zpage x 1 p p).subtype ≤ LinearMap.ker f := by
    intro z hz
    change f z = 0
    have hh := Theta_eq_zero_of_Bpage x p p z hz
    change e ((Theta x p p z).1 _) ε = 0
    rw [hh]; change e 0 ε = 0; rw [map_zero]; rfl
  let L : E x 1 p p →ₗ[k] k := Submodule.liftQ _ f hkill
  have hL (z : RawCochain x) (hz : z ∈ Zpage x 1 p p) :
      L (Subquot.mk z hz) = flagPairing F k p
        (Tlin x p z (Finsupp.single (stdFlag F p) 1)) (epsSteinberg F k p) := hf ⟨z, hz⟩
  have hα : L (Subquot.mk _ (alphaCochain_mem (F := F) (k := k) p)) = 1 := by
    rw [hL]
    exact alpha_apartment_pairing p
  have hd : finrank k (E x 1 p p) = 1 := (lemma_1_31 (F := F) (k := k) p).choose_spec.2.2.2
  have hinj : Function.Injective L := by
    have hn : (Subquot.mk _ (alphaCochain_mem (F := F) (k := k) p) : E x 1 p p) ≠ 0 := by
      intro h
      rw [h, map_zero] at hα
      exact zero_ne_one hα
    intro u v huv
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd hn (u - v)
    have hz : L (u - v) = 0 := by rw [map_sub, huv, sub_self]
    rw [← hc, map_smul, hα, smul_eq_mul, mul_one] at hz
    rw [hz, zero_smul] at hc
    exact sub_eq_zero.mp hc.symm
  rw [← hL a ha]
  constructor
  · intro h
    have hz : (Subquot.mk a ha : E x 1 p p) = 0 := (subquot_mk_eq_zero_iff ha).2 h
    rw [hz, map_zero]
  · intro h
    have hz : (Subquot.mk a ha : E x 1 p p) = 0 := hinj (h.trans (map_zero L).symm)
    exact (subquot_mk_eq_zero_iff ha).1 hz
end MartinPhd

end
end CupDetect
