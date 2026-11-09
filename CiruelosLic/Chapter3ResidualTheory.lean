import Mathlib
import CiruelosLic.Chapter2Section4Properties

/-!
# Chapter 3: residual theory of λ^dist

Contents:
* Chapter 3: Residual theory of λ^dist — Definitions
* Chapter 3: Residual theory of λ^dist — Appendix
* Chapter 3: Residual theory of λ^dist
-/

namespace CiruelosLic

/-! ## Chapter 3: Residual theory of λ^dist — Definitions

Steps of λ^dist are addressed by their *name*: the label of the contracted λ. In a correct term
λ-labels are pairwise distinct, so a step is determined by its source and its name. -/

section Ch3Defs

open DTerm

namespace DTerm

/-- `t` is a λ decorated with `ℓ`. -/
def isLamWith : DTerm → Label → Bool
  | lam m _, ℓ => m == ℓ
  | _, _ => false

/-- `t` contains a redex whose λ is decorated with `ℓ`. -/
def hasRedex : DTerm → Label → Bool
  | var _ _, _ => false
  | lam _ t, ℓ => hasRedex t ℓ
  | app t ss, ℓ => isLamWith t ℓ || hasRedex t ℓ || ss.any (hasRedex · ℓ)

/-- Contract the redex named `ℓ` (if any). -/
def contract : DTerm → Label → DTerm
  | var n τ, _ => var n τ
  | lam m t, ℓ => lam m (contract t ℓ)
  | app t ss, ℓ =>
    match t with
    | lam m b => if m = ℓ then b.subst 0 ss else app (lam m (contract b ℓ)) (ss.map (contract · ℓ))
    | t => app (contract t ℓ) (ss.map (contract · ℓ))

theorem hasRedex_iff_step {t : DTerm} {ℓ : Label} :
    t.hasRedex ℓ = true ↔ ∃ u, DStep t ℓ u := by
  constructor
  · intro h
    induction t using DTerm.ind with
    | var => simp [hasRedex] at h
    | lam m t ih =>
      obtain ⟨u, hu⟩ := ih (by simpa only [hasRedex] using h)
      exact ⟨_, .lam m hu⟩
    | app t ss ih ihs =>
      simp only [hasRedex, Bool.or_eq_true, List.any_eq_true] at h
      rcases h with (h | h) | ⟨s, hs, h⟩
      · cases t with
        | var => simp [isLamWith] at h
        | app => simp [isLamWith] at h
        | lam m b =>
          have he : m = ℓ := by simpa [isLamWith] using h
          subst m
          exact ⟨_, .beta ℓ b ss⟩
      · obtain ⟨u, hu⟩ := ih h
        exact ⟨_, .appL ss hu⟩
      · obtain ⟨v, hv⟩ := ihs s hs h
        obtain ⟨us, vs, rfl⟩ := List.mem_iff_append.mp hs
        exact ⟨_, .appR t us vs hv⟩
  · rintro ⟨u, h⟩
    induction h with
    | beta => simp [hasRedex, isLamWith]
    | lam _ _ ih => simpa only [hasRedex] using ih
    | appL _ _ ih => simp [hasRedex, ih]
    | appR _ _ _ _ ih => simp [hasRedex, ih]

theorem contract_absent {t : DTerm} {ℓ : Label} (ha : ℓ ∉ t.lamLabels) :
    t.contract ℓ = t := by
  induction t using DTerm.ind with
  | var => simp only [contract]
  | lam m b ih =>
    simp only [lamLabels, List.mem_cons, not_or] at ha
    simp only [contract, ih ha.2]
  | app t ss ih ihs =>
    simp only [lamLabels, List.mem_append, not_or] at ha
    have he : ss.map (contract · ℓ) = ss := by
      simpa using List.map_congr_left (fun s hs =>
        ihs s hs (fun hm => ha.2 (List.mem_flatMap.mpr ⟨s, hs, hm⟩)))
    have ht := ih ha.1
    cases t with
    | var => simp only [contract, he]
    | app => simp only [contract, ht, he]
    | lam m b =>
      have hne : m ≠ ℓ := fun hh => ha.1 (by simp [lamLabels, hh])
      simp only [contract] at ht
      simp only [contract, ite_eq_right hne, ht, he]

end DTerm

/-- A source lambda cannot have the label of a step strictly inside its body. -/
theorem DStep.label_ne_outer {b u : DTerm} {m ℓ : Label}
    (h : DStep (.lam m b) ℓ u) (hc : Correct (.lam m b)) : m ≠ ℓ := by
  cases h with
  | lam _ h =>
    intro he
    have hn := hc.uniquely_labeled
    rw [DTerm.lamLabels] at hn
    have hn' := List.nodup_cons.mp hn
    exact hn'.1 (he ▸ h.label_mem)

/-- The named contraction function computes any step of a correct term. -/
theorem DStep.eq_contract {t u : DTerm} {ℓ : Label} (h : DStep t ℓ u)
    (hc : Correct t) : t.contract ℓ = u := by
  induction h with
  | beta => simp [contract]
  | lam m h ih => simp only [contract, ih (hc.sub (.lam m (.refl _)))]
  | @appL t t' ℓ ss h ih =>
    have hn := hc.uniquely_labeled
    rw [DTerm.lamLabels] at hn
    have hn := List.nodup_append.mp hn
    have he : ss.map (contract · ℓ) = ss := by
      simpa using List.map_congr_left (fun s hs =>
        DTerm.contract_absent (fun hm => hn.2.2 ℓ h.label_mem ℓ
          (List.mem_flatMap.mpr ⟨s, hs, hm⟩) rfl))
    have ht := ih (hc.sub (.fn ss (.refl _)))
    cases t with
    | var => cases h
    | app => simp only [contract, ht, he]
    | lam m b =>
      simp only [contract] at ht
      simp only [contract, ite_eq_right (h.label_ne_outer (hc.sub (.fn ss (.refl _)))), ht, he]
  | @appR s s' ℓ t us vs h ih =>
    have hn := hc.uniquely_labeled
    rw [DTerm.lamLabels] at hn
    have hn := List.nodup_append.mp hn
    have hm : ℓ ∈ (us ++ s :: vs).flatMap DTerm.lamLabels :=
      List.mem_flatMap (f := DTerm.lamLabels).mpr ⟨s, by simp, h.label_mem⟩
    have ht : ℓ ∉ t.lamLabels := fun hh => hn.2.2 ℓ hh ℓ hm rfl
    have hn' := List.nodup_append.mp (by
      simpa only [List.flatMap_append, List.flatMap_cons] using hn.2.1)
    have hn'' := List.nodup_append.mp hn'.2.1
    have hu : us.map (contract · ℓ) = us := by
      simpa using List.map_congr_left (fun a ha =>
        DTerm.contract_absent (fun hh => hn'.2.2 ℓ
          (List.mem_flatMap.mpr ⟨a, ha, hh⟩) ℓ (by simp [h.label_mem]) rfl))
    have hv : vs.map (contract · ℓ) = vs := by
      simpa using List.map_congr_left (fun a ha =>
        DTerm.contract_absent (fun hh => hn''.2.2 ℓ h.label_mem ℓ
          (List.mem_flatMap.mpr ⟨a, ha, hh⟩) rfl))
    have hs := ih (hc.sub (.arg t (by simp) (.refl s)))
    have he : (us ++ s :: vs).map (contract · ℓ) = us ++ s' :: vs := by
      simp only [List.map_append, List.map_cons, hu, hv, hs]
    have ht' := DTerm.contract_absent ht
    cases t with
    | var => simp only [contract, he]
    | app => simp only [contract, ht', he]
    | lam m b =>
      have hne : m ≠ ℓ := fun hh => ht (by simp [DTerm.lamLabels, hh])
      simp only [contract] at ht'
      simp only [contract, ite_eq_right hne, ht', he]

namespace DTerm

end DTerm

/-- In a correct term, `hasRedex t ℓ` holds iff there is a step `t →ℓ u`, and then `u` is
`contract t ℓ`. -/
theorem dStep_iff_hasRedex {t u : DTerm} {ℓ : Label} (ht : Correct t) :
    DStep t ℓ u ↔ t.hasRedex ℓ = true ∧ u = t.contract ℓ := by
  constructor
  · intro h
    exact ⟨DTerm.hasRedex_iff_step.mpr ⟨u, h⟩, (h.eq_contract ht).symm⟩
  · rintro ⟨h, rfl⟩
    obtain ⟨v, hv⟩ := DTerm.hasRedex_iff_step.mp h
    exact (hv.eq_contract ht).symm ▸ hv

theorem contract_of_not_hasRedex {t : DTerm} {ℓ : Label} (h : t.hasRedex ℓ = false) :
    t.contract ℓ = t := by
  induction t using DTerm.ind with
  | var n τ => simp [contract]
  | lam m t ih => simp only [hasRedex] at h; simp [contract, ih h]
  | app t ss ih ihs =>
    simp only [hasRedex, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hss : ss.map (contract · ℓ) = ss := by
      conv_rhs => rw [← List.map_id ss]
      exact List.map_congr_left fun s hs => ihs s hs (h3 s hs)
    cases t with
    | lam m b =>
      have hm : m ≠ ℓ := by simpa [isLamWith] using h1
      have hb : b.contract ℓ = b := by simpa [contract] using ih h2
      simp [contract, hm, hb, hss]
    | var n τ => simp [contract, hss]
    | app u us => rw [contract, ih h2, hss]; simp

theorem correct_contract {t : DTerm} (ht : Correct t) (ℓ : Label) : Correct (t.contract ℓ) := by
  cases h : t.hasRedex ℓ
  · rwa [contract_of_not_hasRedex h]
  · exact correct_of_dStep ht ((dStep_iff_hasRedex ht).2 ⟨h, rfl⟩)

/-- λ^dist as an axiomatic rewrite system over correct terms.
**Residuals** (Definition "Residuals in the distributive λ-calculus"):
`R/S = {R' | src(R') = tgt(S) ∧ name(R') = name(R)}`. -/
abbrev distRS : ResidualSystem where
  Obj := CTerm
  Adr := Label
  isStep t ℓ := t.1.hasRedex ℓ = true
  contract t ℓ := ⟨t.1.contract ℓ, correct_contract t.2 ℓ⟩
  res t m ℓ := if (t.1.contract m).hasRedex ℓ then {ℓ} else ∅
  dev _ M := M.sort (· ≤ ·)

namespace distRS

/-! ## Names -/

/-- The set of names of a derivation. -/
def names (σ : List Label) : Finset Label := σ.toFinset

/-- `R ∈ σ`: some residual of `R` is contracted along `σ`. -/
def Belongs (t : CTerm) (ℓ : Label) (σ : List Label) : Prop :=
  ∃ σ₁ ℓ' σ₂, σ = σ₁ ++ ℓ' :: σ₂ ∧ ℓ' ∈ distRS.resSetDeriv t {ℓ} σ₁

/-! ## Creation and stability -/

/-- `R` (named `m`) *creates* the step `S` (named `n`, out of the target of `R`): `S` is not a
residual of any step coinitial with `R`. -/
def Creates (t : CTerm) (m n : Label) : Prop :=
  distRS.isStep t m ∧ distRS.isStep (distRS.contract t m) n ∧
    ∀ a, distRS.isStep t a → n ∉ distRS.res t m a

/-- The three ways in which a step `R` (named `ℓ`) of `t` can create a step named `ℓ'`. -/
inductive CreationCase : DTerm → Label → Label → Prop
  /-- **Case I.** `C⟨(λ^ℓ x.x^τ)[λ^ℓ' y.t] s̄⟩ → C⟨(λ^ℓ' y.t) s̄⟩ → ⋯` -/
  | I (C : DCtx) (ℓ ℓ' : Label) (τ : Ty) (b : DTerm) (ss : List DTerm) :
      CreationCase (C.plug (.app (.app (.lam ℓ (.var 0 τ)) [.lam ℓ' b]) ss)) ℓ ℓ'
  /-- **Case II.** `C⟨(λ^ℓ x.λ^ℓ' y.t) s̄ ū⟩ → C⟨(λ^ℓ' y.t') ū⟩ → ⋯` -/
  | II (C : DCtx) (ℓ ℓ' : Label) (b : DTerm) (ss us : List DTerm) :
      CreationCase (C.plug (.app (.app (.lam ℓ (.lam ℓ' b)) ss) us)) ℓ ℓ'
  /-- **Case III.** `C₁⟨(λ^ℓ x.C₂⟨x^τ ū⟩)[s̄₁, λ^ℓ' y.t, s̄₂]⟩ → C₁⟨C₂'⟨(λ^ℓ' y.t) ū'⟩⟩ → ⋯`,
  where the argument `λ^ℓ' y.t` is the one of type `τ`. -/
  | III (C₁ C₂ : DCtx) (ℓ ℓ' : Label) (τ : Ty) (us ss₁ ss₂ : List DTerm) (b : DTerm) :
      (DTerm.lam ℓ' b).ty = τ →
      CreationCase
        (C₁.plug (.app (.lam ℓ (C₂.plug (.app (.var C₂.depth τ) us))) (ss₁ ++ .lam ℓ' b :: ss₂)))
        ℓ ℓ'

/-! ## Meets -/

open Classical in
/-- The meet of derivations: repeatedly contract a step *common* to `σ` and `τ`
(the least such name, to make the choice deterministic). `fuel` bounds the recursion; `|σ|`
suffices since projections are decreasing. -/
noncomputable def meetAux : ℕ → CTerm → List Label → List Label → List Label
  | 0, _, _, _ => []
  | fuel + 1, t, σ, τ =>
    if h : ∃ a, distRS.isStep t a ∧ distRS.Prefix t [a] σ ∧ distRS.Prefix t [a] τ then
      let a := Nat.find h
      a :: meetAux fuel (distRS.contract t a) (distRS.proj t σ [a]) (distRS.proj t τ [a])
    else []

/-- `σ ⊓ τ`. -/
noncomputable def meet (t : CTerm) (σ τ : List Label) : List Label := meetAux σ.length t σ τ

end distRS

end Ch3Defs

/-! ## Chapter 3: Residual theory of λ^dist — Appendix

Auxiliary proofs for Chapter 3, following `04-01`..`04-04` and appendices `08-08`, `08-10`:
* Orthogonality from strong permutation and lambda conservation.
* Names of residuals and projections, belonging, and the prefix order.
* Validity and greatest-lower-bound specification of the fuelled meet construction.
* The three syntactic creation cases and uniqueness of the creator of each lambda.
* Basic/full stability and the intersection formula for meet names. -/

section Ch3Appendix

namespace distRS

@[simp] theorem tgt_nil_core (t : CTerm) : distRS.tgt t [] = t := rfl
@[simp] theorem tgt_cons_core (t : CTerm) (a : Label) (σ : List Label) :
    distRS.tgt t (a :: σ) = distRS.tgt (distRS.contract t a) σ := rfl

/-- A step named `a` in the residual system is the corresponding syntactic step. -/
theorem step_contract {t : CTerm} {a : Label} (ha : distRS.isStep t a) :
    DStep t.1 a (distRS.contract t a).1 := (dStep_iff_hasRedex t.2).mpr ⟨ha, rfl⟩

theorem step_label_mem {t : CTerm} {a : Label} (ha : distRS.isStep t a) :
    a ∈ t.1.lamLabels := (step_contract ha).label_mem

theorem erased_label {t : CTerm} {a : Label} (ha : distRS.isStep t a) :
    a ∉ (distRS.contract t a).1.lamLabels := by
  have hn : (a ::ₘ ((distRS.contract t a).1.lamLabels : Multiset Label)).Nodup :=
    ((step_contract ha).lamLabels t.2).symm ▸ t.2.uniquely_labeled
  exact (Multiset.nodup_cons.mp hn).1

theorem step_after {t : CTerm} {a b : Label} (ha : distRS.isStep t a)
    (hb : distRS.isStep t b) (hne : a ≠ b) : distRS.isStep (distRS.contract t b) a := by
  obtain ⟨u, _, h⟩ := strong_permutation t.2 (step_contract ha) (step_contract hb) (.inl hne)
  exact (dStep_iff_hasRedex (distRS.contract t b).2).mp h |>.1

/-- Residuals of distinct steps retain their name; the contracted label is erased. -/
theorem res_formula {t : CTerm} {a b : Label} (ha : distRS.isStep t a)
    (hb : distRS.isStep t b) : distRS.res t b a = if a = b then ∅ else {a} := by
  by_cases he : a = b
  · subst a
    have hn : ¬ distRS.isStep (distRS.contract t b) b := fun h => erased_label hb (step_label_mem h)
    simp only [distRS]
    have hf : (t.1.contract b).hasRedex b = false := Bool.eq_false_iff.mpr hn
    simp [hf]
  · have hh := step_after ha hb he
    change (if (t.1.contract b).hasRedex a then {a} else ∅) = if a = b then ∅ else {a}
    rw [ite_eq_right he, show (t.1.contract b).hasRedex a = true from hh]
    rfl

/-- A finite coinitial set loses just the contracted member. -/
theorem resSet_erase {t : CTerm} {M : Finset Label} {a : Label}
    (hM : ∀ b ∈ M, distRS.isStep t b) (ha : distRS.isStep t a) :
    distRS.resSet t M a = M.erase a := by
  ext b
  simp only [ResidualSystem.resSet, Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨c, hc, hb⟩
    change b ∈ distRS.res t a c at hb
    rw [res_formula (hM c hc) ha] at hb
    split_ifs at hb with he
    · simp at hb
    · have : b = c := Finset.mem_singleton.mp hb
      subst b
      exact ⟨he, hc⟩
  · rintro ⟨hne, hb⟩
    refine ⟨b, hb, ?_⟩
    change b ∈ distRS.res t a b
    rw [res_formula (hM b hb) ha, ite_eq_right hne]
    exact Finset.mem_singleton_self _

theorem resSet_steps {t : CTerm} {M : Finset Label} {a : Label}
    (hM : ∀ b ∈ M, distRS.isStep t b) (ha : distRS.isStep t a) :
    ∀ b ∈ M.erase a, distRS.isStep (distRS.contract t a) b := by
  intro b hb
  exact step_after (hM b (Finset.mem_erase.mp hb).2) ha (Finset.mem_erase.mp hb).1

/-- Residuals of initially available steps are obtained by deleting executed names. -/
theorem residual_names {t : CTerm} {M : Finset Label} {σ : List Label}
    (hM : ∀ b ∈ M, distRS.isStep t b) (hσ : distRS.Valid t σ) :
    distRS.resSetDeriv t M σ = M \ names σ ∧
      ∀ b ∈ M \ names σ, distRS.isStep (distRS.tgt t σ) b := by
  induction σ generalizing t M with
  | nil =>
    rw [tgt_nil_core]
    simpa only [ResidualSystem.resSetDeriv, names, List.toFinset_nil, Finset.sdiff_empty, eq_self, true_and] using hM
  | cons a σ ih =>
    obtain ⟨ha, hσ⟩ := hσ
    have hh := ih (resSet_steps hM ha) hσ
    rw [ResidualSystem.resSetDeriv, resSet_erase hM ha]
    have he : M.erase a \ names σ = M \ names (a :: σ) := by
      ext b; simp [names]; tauto
    exact ⟨hh.1.trans he, he ▸ hh.2⟩

/-- A valid trace consumes one lambda per step. -/
theorem valid_size {t : CTerm} {σ : List Label} (hσ : distRS.Valid t σ) :
    (distRS.tgt t σ).1.size + σ.length = t.1.size := by
  induction σ generalizing t with
  | nil => rfl
  | cons a σ ih =>
    have h := size_dStep t.2 (step_contract hσ.1)
    have hh := ih hσ.2
    rw [tgt_cons_core, List.length_cons]
    omega

theorem valid_labels {t : CTerm} {σ : List Label} (hσ : distRS.Valid t σ) :
    (σ : Multiset Label) + ((distRS.tgt t σ).1.lamLabels : Multiset Label) =
      (t.1.lamLabels : Multiset Label) := by
  induction σ generalizing t with
  | nil => rw [tgt_nil_core]; simp only [Multiset.coe_nil, zero_add]
  | cons a σ ih =>
    have hh := ih hσ.2
    have he := (step_contract hσ.1).lamLabels t.2
    rw [tgt_cons_core, ← Multiset.cons_coe, Multiset.cons_add, hh, he]

/-- Enumerating a coinitial set without repetitions is its complete development. -/
theorem list_development {t : CTerm} {σ : List Label} (hn : σ.Nodup)
    (hs : ∀ a ∈ σ, distRS.isStep t a) :
    distRS.IsCompleteDevelopment t σ.toFinset σ := by
  induction σ generalizing t with
  | nil => simp [ResidualSystem.IsCompleteDevelopment, ResidualSystem.IsDevelopment,
      ResidualSystem.resSetDeriv]
  | cons a σ ih =>
    have ha := hs a (by simp)
    have hn' := List.nodup_cons.mp hn
    have he : (a :: σ).toFinset.erase a = σ.toFinset := by
      ext b; simp [hn'.1]
    have hh := ih hn'.2 (fun b hb => step_after (hs b (by simp [hb])) ha (by
      intro h; subst b; exact hn'.1 hb))
    refine ⟨⟨ha, by simp, ?_⟩, ?_⟩
    · rw [resSet_erase (by simpa using hs) ha, he]
      exact hh.1
    · rw [ResidualSystem.resSetDeriv, resSet_erase (by simpa using hs) ha, he]
      exact hh.2

/-- The explicit orthogonality obligations, from strong permutation and lambda counting. -/
theorem orthogonal_core : distRS.Orthogonal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t a b ha hb c hc
    change c ∈ (if (t.1.contract b).hasRedex a then {a} else ∅) at hc
    split_ifs at hc with h
    · have he := Finset.mem_singleton.mp hc
      subst c
      exact h
    · simp at hc
  · intro t a ha
    exact (res_formula ha ha).trans (ite_eq_left rfl)
  · intro t M hM
    rintro ⟨f, hf⟩
    have hv := ResidualSystem.isDevelopment_valid (hf (t.1.size + 1))
    have hh := valid_size hv
    simp only [List.length_ofFn] at hh
    omega
  · intro t a b ha hb
    by_cases he : a = b
    · subst b
      refine ⟨[], [], ?_, ?_, rfl, ?_⟩
      · rw [(res_formula ha ha).trans (ite_eq_left rfl)]
        exact ⟨trivial, rfl⟩
      · rw [(res_formula ha ha).trans (ite_eq_left rfl)]
        exact ⟨trivial, rfl⟩
      · intro c hc; rfl
    · have hab := step_after ha hb he
      have hba := step_after hb ha (Ne.symm he)
      obtain ⟨u, hua, hub⟩ := strong_permutation t.2 (step_contract ha) (step_contract hb) (.inl he)
      have hsquare : distRS.contract (distRS.contract t b) a =
          distRS.contract (distRS.contract t a) b := by
        apply Subtype.ext
        exact ((dStep_iff_hasRedex (distRS.contract t b).2).mp hub).2.symm.trans
          ((dStep_iff_hasRedex (distRS.contract t a).2).mp hua).2
      refine ⟨[a], [b], ?_, ?_, hsquare, ?_⟩
      · rw [res_formula ha hb, ite_eq_right he]
        simpa using list_development (by simp : [a].Nodup) (by simpa using hab)
      · rw [res_formula hb ha, ite_eq_right (Ne.symm he)]
        simpa using list_development (by simp : [b].Nodup) (by simpa using hba)
      · intro c hc
        have hv₁ : distRS.Valid t [a, b] := ⟨ha, hba, trivial⟩
        have hv₂ : distRS.Valid t [b, a] := ⟨hb, hab, trivial⟩
        rw [(residual_names (M := {c}) (fun b hb => (Finset.mem_singleton.mp hb) ▸ hc) hv₁).1,
          (residual_names (M := {c}) (fun b hb => (Finset.mem_singleton.mp hb) ▸ hc) hv₂).1]
        simp [names, Finset.pair_comm]
  · intro t M hM
    have hh := list_development (Finset.sort_nodup M (· ≤ ·))
      (by simpa only [Finset.mem_sort] using hM)
    simpa using hh

variable {t : CTerm}

/-- The λs of the target of `σ` are disjoint from the names of `σ`; hence names along a
derivation never repeat. -/
theorem nodup_of_valid {σ : List Label} (hσ : distRS.Valid t σ) : σ.Nodup := by
  have he := valid_labels hσ
  have hn : ((σ : Multiset Label) +
      ((distRS.tgt t σ).1.lamLabels : Multiset Label)).Nodup := he.symm ▸ t.2.uniquely_labeled
  exact Multiset.coe_nodup.mp (Multiset.nodup_of_le (le_add_right le_rfl) hn)

@[simp] theorem names_dev (t : CTerm) (M : Finset Label) :
    names (distRS.dev t M) = M := by
  exact Finset.sort_toFinset _ _

theorem names_cons (a : Label) (σ : List Label) : names (a :: σ) = insert a (names σ) := by
  simp [names]

theorem names_append_core (σ τ : List Label) : names (σ ++ τ) = names σ ∪ names τ := by
  simp [names]

/-- Multistep projection deletes precisely the names of its coinitial set. -/
theorem names_projM {t : CTerm} {σ : List Label} {M : Finset Label}
    (hσ : distRS.Valid t σ) (hM : ∀ a ∈ M, distRS.isStep t a) :
    names (distRS.projM t σ M) = names σ \ M := by
  induction σ generalizing t M with
  | nil => simp [ResidualSystem.projM, names]
  | cons a σ ih =>
    have ha := hσ.1
    have hσ' := hσ.2
    have hn := (List.nodup_cons.mp (nodup_of_valid hσ)).1
    have hv := ResidualSystem.dev_valid (R := distRS) orthogonal_core hM
    have hdnames : names (distRS.dev t M) = M := names_dev t M
    rw [ResidualSystem.projM, names_append_core, names_dev,
      (residual_names (M := {a}) (fun b hb => (Finset.mem_singleton.mp hb) ▸ ha) hv).1,
      hdnames, resSet_erase hM ha, ih hσ' (resSet_steps hM ha), names_cons]
    ext b
    have hn' : a ∉ names σ := by simpa [names] using hn
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton,
      Finset.mem_erase, Finset.mem_insert]
    by_cases he : b = a
    · subst b; simp [hn']
    · tauto

/-- Derivation projection deletes precisely the names of its denominator. -/
theorem names_proj_core {t : CTerm} {σ τ : List Label}
    (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    names (distRS.proj t σ τ) = names σ \ names τ := by
  induction σ generalizing t τ with
  | nil => simp [ResidualSystem.proj, names]
  | cons a σ ih =>
    have ha := hσ.1
    have haM : ∀ b ∈ ({a} : Finset Label), distRS.isStep t b :=
      fun b hb => (Finset.mem_singleton.mp hb) ▸ ha
    have hv := ResidualSystem.projM_valid orthogonal_core hτ haM
    rw [ResidualSystem.dev_singleton orthogonal_core ha, tgt_cons_core, tgt_nil_core] at hv
    have hn : a ∉ names σ := by
      simpa [names] using (List.nodup_cons.mp (nodup_of_valid hσ)).1
    rw [ResidualSystem.proj, names_append_core, names_dev,
      (residual_names haM hτ).1,
      ih hσ.2 hv, names_projM hτ haM, names_cons]
    ext b
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
    by_cases he : b = a
    · subst b; simp [hn]
    · tauto

theorem prefix_names {t : CTerm} {σ τ : List Label}
    (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    distRS.Prefix t σ τ ↔ names σ ⊆ names τ := by
  have he : names (distRS.proj t σ τ) = ∅ ↔ distRS.proj t σ τ = [] := by simp [names]
  rw [ResidualSystem.Prefix, ← he, names_proj_core hσ hτ, Finset.sdiff_eq_empty_iff_subset]

theorem development_subset {t : CTerm} {M : Finset Label} {σ : List Label}
    (hM : ∀ a ∈ M, distRS.isStep t a) (hσ : distRS.IsDevelopment t M σ) :
    names σ ⊆ M := by
  induction σ generalizing t M with
  | nil => simp [names]
  | cons a σ ih =>
    obtain ⟨ha, ham, hσ⟩ := hσ
    rw [resSet_erase hM ha] at hσ
    have hh := ih (resSet_steps hM ha) hσ
    rw [names_cons]
    exact Finset.insert_subset ham (hh.trans (Finset.erase_subset _ _))

theorem belongs_names {t : CTerm} {a : Label} {σ : List Label}
    (ha : distRS.isStep t a) (hσ : distRS.Valid t σ) : Belongs t a σ ↔ a ∈ names σ := by
  constructor
  · rintro ⟨σ₁, b, σ₂, rfl, hb⟩
    have hv := (ResidualSystem.valid_append _ _ _ _).mp hσ |>.1
    rw [(residual_names (M := {a}) (fun c hc => (Finset.mem_singleton.mp hc) ▸ ha) hv).1] at hb
    have he := Finset.mem_singleton.mp (Finset.mem_sdiff.mp hb).1
    subst b
    simp [names]
  · intro hm
    obtain ⟨σ₁, σ₂, rfl⟩ := List.mem_iff_append.mp (show a ∈ σ from by simpa [names] using hm)
    have hv := (ResidualSystem.valid_append _ _ _ _).mp hσ |>.1
    have hn := List.nodup_append.mp (nodup_of_valid hσ)
    have hnot : a ∉ names σ₁ := by
      intro h
      exact hn.2.2 a (by simpa [names] using h) a (by simp) rfl
    refine ⟨σ₁, a, σ₂, rfl, ?_⟩
    rw [(residual_names (M := {a}) (fun c hc => (Finset.mem_singleton.mp hc) ▸ ha) hv).1]
    simp [hnot]

/-- **Projections are decreasing** (`08-10-lattices-and-derivation-spaces.tex`). -/
theorem length_proj_lt {σ : List Label} {ℓ : Label} (hσ : distRS.Valid t σ)
    (hℓ : distRS.isStep t ℓ) (h : ℓ ∈ names σ) :
    (distRS.proj t σ [ℓ]).length < σ.length := by
  have hv := ResidualSystem.proj_valid orthogonal_core hσ (ResidualSystem.valid_singleton hℓ)
  have hn := names_proj_core hσ (ResidualSystem.valid_singleton hℓ)
  have hc := Finset.card_erase_lt_of_mem h
  have hlenσ := List.toFinset_card_of_nodup (nodup_of_valid hσ)
  have hlenp := List.toFinset_card_of_nodup (nodup_of_valid hv)
  rw [show names [ℓ] = {ℓ} by rfl, Finset.sdiff_singleton_eq_erase] at hn
  change (names (distRS.proj t σ [ℓ])).card = _ at hlenp
  rw [hn] at hlenp
  change (names σ).card = _ at hlenσ
  omega

/-- The fuelled construction is a greatest valid lower bound once its fuel bounds
`σ.length`. This is the induction on length in `04-04-lattices.tex`. -/
theorem meetAux_spec (fuel : ℕ) {t : CTerm} {σ τ : List Label}
    (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) (hlen : σ.length ≤ fuel) :
    names (meetAux fuel t σ τ) ⊆ names σ ∩ names τ ∧
      ∀ ρ, distRS.Valid t ρ → names ρ ⊆ names σ ∩ names τ →
        names ρ ⊆ names (meetAux fuel t σ τ) := by
  induction fuel generalizing t σ τ with
  | zero =>
    have he : σ = [] := List.length_eq_zero_iff.mp (by omega)
    subst σ
    simp [meetAux, names]
  | succ fuel ih =>
    unfold meetAux
    split_ifs with h
    · let a := Nat.find h
      have hh : distRS.isStep t a ∧ distRS.Prefix t [a] σ ∧ distRS.Prefix t [a] τ := Nat.find_spec h
      have ha := hh.1
      have hva := ResidualSystem.valid_singleton ha
      have ham : a ∈ names σ ∩ names τ := by
        exact Finset.mem_inter.mpr ⟨(prefix_names hva hσ).mp hh.2.1 (by simp [names]),
          (prefix_names hva hτ).mp hh.2.2 (by simp [names])⟩
      have hvs := ResidualSystem.proj_valid orthogonal_core hσ hva
      have hvt := ResidualSystem.proj_valid orthogonal_core hτ hva
      rw [tgt_cons_core, tgt_nil_core] at hvs hvt
      have hbnd : (distRS.proj t σ [a]).length ≤ fuel := by
        have := length_proj_lt hσ ha (Finset.mem_inter.mp ham).1
        omega
      have hi := ih hvs hvt hbnd
      change names (a :: meetAux fuel (distRS.contract t a)
        (distRS.proj t σ [a]) (distRS.proj t τ [a])) ⊆ _ ∧ _
      rw [names_cons]
      refine ⟨?_, ?_⟩
      · apply Finset.insert_subset ham
        intro b hb
        have hb' := hi.1 hb
        rw [names_proj_core hσ hva, names_proj_core hτ hva] at hb'
        exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hb').1).1,
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb').2).1⟩
      · intro ρ hρ hsub b hb
        by_cases he : b = a
        · exact Finset.mem_insert.mpr (.inl he)
        · have hvr := ResidualSystem.proj_valid orthogonal_core hρ hva
          rw [tgt_cons_core, tgt_nil_core] at hvr
          have hsub' : names (distRS.proj t ρ [a]) ⊆
              names (distRS.proj t σ [a]) ∩ names (distRS.proj t τ [a]) := by
            rw [names_proj_core hρ hva, names_proj_core hσ hva, names_proj_core hτ hva]
            intro c hc
            have hc' := hsub (Finset.mem_sdiff.mp hc).1
            exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hc').1,
              (Finset.mem_sdiff.mp hc).2⟩, Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hc').2,
              (Finset.mem_sdiff.mp hc).2⟩⟩
          apply Finset.mem_insert.mpr ∘ Or.inr
          apply hi.2 _ hvr hsub'
          rw [names_proj_core hρ hva]
          exact Finset.mem_sdiff.mpr ⟨hb, by simpa [names] using he⟩
    · constructor
      · simp [names]
      · intro ρ hρ hsub
        cases ρ with
        | nil => simp [names]
        | cons b ρ =>
          have hb := hsub (show b ∈ names (b :: ρ) by simp [names])
          have hvb := ResidualSystem.valid_singleton hρ.1
          exact False.elim (h ⟨b, hρ.1,
            (prefix_names hvb hσ).mpr (by simpa [names] using (Finset.mem_inter.mp hb).1),
            (prefix_names hvb hτ).mpr (by simpa [names] using (Finset.mem_inter.mp hb).2)⟩)

/-- Residuals never change a label, including for sets containing unavailable labels. -/
theorem residual_subset (t : CTerm) (M : Finset Label) (σ : List Label) :
    distRS.resSetDeriv t M σ ⊆ M := by
  induction σ generalizing t M with
  | nil => exact fun _ h => h
  | cons a σ ih =>
    apply Finset.Subset.trans (ih _ _)
    intro b hb
    obtain ⟨c, hc, hb⟩ := Finset.mem_biUnion.mp hb
    change b ∈ (if (t.1.contract a).hasRedex c then {c} else ∅) at hb
    split_ifs at hb
    · exact (Finset.mem_singleton.mp hb) ▸ hc
    · simp at hb

theorem creates_iff {t : CTerm} {m n : Label} : Creates t m n ↔
    distRS.isStep t m ∧ distRS.isStep (distRS.contract t m) n ∧ ¬ distRS.isStep t n := by
  constructor
  · rintro ⟨hm, hn, h⟩
    refine ⟨hm, hn, fun hn₀ => h n hn₀ ?_⟩
    change n ∈ (if (t.1.contract m).hasRedex n then {n} else ∅)
    rw [show (t.1.contract m).hasRedex n = true from hn]
    simp
  · rintro ⟨hm, hn, hnot⟩
    refine ⟨hm, hn, ?_⟩
    intro a ha hmem
    change n ∈ (if (t.1.contract m).hasRedex a then {a} else ∅) at hmem
    split_ifs at hmem
    · exact hnot ((Finset.mem_singleton.mp hmem) ▸ ha)
    · simp at hmem

theorem step_persists {t : CTerm} {n : Label} {σ : List Label}
    (hn : distRS.isStep t n) (hσ : distRS.Valid t σ) (hnot : n ∉ names σ) :
    distRS.isStep (distRS.tgt t σ) n :=
  (residual_names (M := {n}) (fun a ha => (Finset.mem_singleton.mp ha) ▸ hn) hσ).2 n
    (by simp [hnot])

theorem step_not_names {t : CTerm} {n : Label} {σ : List Label}
    (hσ : distRS.Valid t σ) (hn : distRS.isStep (distRS.tgt t σ) n) : n ∉ names σ := by
  have hv := (ResidualSystem.valid_append distRS t σ [n]).mpr
    ⟨hσ, ResidualSystem.valid_singleton hn⟩
  have hh := List.nodup_append.mp (nodup_of_valid hv)
  intro hm
  exact hh.2.2 n (by simpa [names] using hm) n (by simp) rfl

/-- A creator remains necessary while only different names are contracted. -/
theorem creator_necessary
    (stable : ∀ {t : CTerm} {m k n : Label}, m ≠ k → distRS.isStep t k →
      Creates t m n → Creates (distRS.contract t k) m n)
    {t : CTerm} {m n : Label} {σ : List Label} (h : Creates t m n)
    (hσ : distRS.Valid t σ) (hnot : m ∉ names σ) :
    ¬ distRS.isStep (distRS.tgt t σ) n := by
  induction σ generalizing t with
  | nil => rw [tgt_nil_core]; exact (creates_iff.mp h).2.2
  | cons k σ ih =>
    have hk : m ≠ k := fun he => hnot (by simp [names, he])
    rw [tgt_cons_core]
    exact ih (stable hk hσ.1 h) hσ.2 (fun hm => hnot (by rw [names_cons]; exact Finset.mem_insert_of_mem hm))

/-- Disjoint computations cannot independently enable the same previously unavailable
step. This is the double induction in `04-03-creation-and-stability.tex`. -/
theorem disjoint_available
    (stable : ∀ {t : CTerm} {m k n : Label}, m ≠ k → distRS.isStep t k →
      Creates t m n → Creates (distRS.contract t k) m n)
    {t : CTerm} {σ τ : List Label} {n : Label}
    (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ)
    (hd : Disjoint (names σ) (names τ))
    (hnσ : distRS.isStep (distRS.tgt t σ) n)
    (hnτ : distRS.isStep (distRS.tgt t τ) n) : distRS.isStep t n := by
  induction σ generalizing t τ with
  | nil => rw [tgt_nil_core] at hnσ; exact hnσ
  | cons a σ ih =>
    by_cases hn : distRS.isStep t n
    · exact hn
    · have ha := hσ.1
      have hva := ResidualSystem.valid_singleton ha
      have haτ : a ∉ names τ := fun hm =>
        Finset.disjoint_left.mp hd (by simp [names]) hm
      by_cases hna : distRS.isStep (distRS.contract t a) n
      · exact False.elim (creator_necessary stable (creates_iff.mpr ⟨ha, hna, hn⟩) hτ haτ hnτ)
      · have hvp := ResidualSystem.proj_valid orthogonal_core hτ hva
        rw [tgt_cons_core, tgt_nil_core] at hvp
        have hne : n ≠ a := fun he => step_not_names hσ hnσ (by simp [names, he])
        have hnpj : n ∉ names (distRS.proj t [a] τ) := by
          rw [names_proj_core hva hτ]
          simp [names, hne]
        have hnp := step_persists hnτ
          (ResidualSystem.proj_valid orthogonal_core hva hτ) hnpj
        have hsquare := ResidualSystem.tgt_join_comm orthogonal_core hva hτ
        unfold ResidualSystem.join at hsquare
        rw [ResidualSystem.tgt_append, ResidualSystem.tgt_append, tgt_cons_core, tgt_nil_core] at hsquare
        rw [← hsquare] at hnp
        have hd' : Disjoint (names σ) (names (distRS.proj t τ [a])) := by
          rw [names_proj_core hτ hva]
          apply Finset.disjoint_left.mpr
          intro b hb hp
          exact Finset.disjoint_left.mp hd (by rw [names_cons]; exact Finset.mem_insert_of_mem hb) (Finset.mem_sdiff.mp hp).1
        exact False.elim (hna (ih hσ.2 hvp hd' hnσ hnp))

/-- Executing a created step requires executing its creator first. -/
theorem creator_in_trace
    (stable : ∀ {t : CTerm} {m k n : Label}, m ≠ k → distRS.isStep t k →
      Creates t m n → Creates (distRS.contract t k) m n)
    {t : CTerm} {m n : Label} {σ : List Label} (h : Creates t m n)
    (hσ : distRS.Valid t σ) (hn : n ∈ names σ) : m ∈ names σ := by
  by_contra hm
  obtain ⟨ρ, τ, he⟩ := List.mem_iff_append.mp (show n ∈ σ from by simpa [names] using hn)
  subst σ
  obtain ⟨hρ, htail⟩ := (ResidualSystem.valid_append distRS t ρ (n :: τ)).mp hσ
  have hnot : m ∉ names ρ := fun hmem => hm (by rw [names_append_core]; exact Finset.mem_union_left _ hmem)
  exact creator_necessary stable h hρ hnot htail.1

/-- If computations share a name, they share an initially available step
(`08-10-lattices-and-derivation-spaces.tex`, properties of disjoint derivations). -/
theorem common_source
    (stable : ∀ {t : CTerm} {m k n : Label}, m ≠ k → distRS.isStep t k →
      Creates t m n → Creates (distRS.contract t k) m n)
    {t : CTerm} {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ)
    (hcommon : (names σ ∩ names τ).Nonempty) :
    ∃ a, distRS.isStep t a ∧ a ∈ names σ ∩ names τ := by
  induction σ generalizing t τ with
  | nil => simp [names] at hcommon
  | cons a σ ih =>
    by_cases ham : a ∈ names τ
    · exact ⟨a, hσ.1, Finset.mem_inter.mpr ⟨by rw [names_cons]; exact Finset.mem_insert_self _ _, ham⟩⟩
    · have hva := ResidualSystem.valid_singleton hσ.1
      have hvp := ResidualSystem.proj_valid orthogonal_core hτ hva
      rw [tgt_cons_core, tgt_nil_core] at hvp
      have hpnames : names (distRS.proj t τ [a]) = names τ := by
        rw [names_proj_core hτ hva]
        rw [show names [a] = {a} by rfl, Finset.sdiff_singleton_eq_erase]
        exact Finset.erase_eq_of_notMem ham
      have hc' : (names σ ∩ names (distRS.proj t τ [a])).Nonempty := by
        rw [hpnames]
        obtain ⟨b, hb⟩ := hcommon
        rw [names_cons] at hb
        have he : b ≠ a := fun he => ham (he ▸ (Finset.mem_inter.mp hb).2)
        exact ⟨b, Finset.mem_inter.mpr ⟨(Finset.mem_insert.mp (Finset.mem_inter.mp hb).1).resolve_left he,
          (Finset.mem_inter.mp hb).2⟩⟩
      obtain ⟨b, hb, hbm⟩ := ih hσ.2 hvp hc'
      rw [hpnames] at hbm
      have hbt : distRS.isStep t b := by
        by_contra hn
        exact ham (creator_in_trace stable (creates_iff.mpr ⟨hσ.1, hb, hn⟩) hτ
          (Finset.mem_inter.mp hbm).2)
      have hbσ : b ∈ names (a :: σ) := by
        rw [names_cons]
        exact Finset.mem_insert_of_mem (Finset.mem_inter.mp hbm).1
      exact ⟨b, hbt, Finset.mem_inter.mpr ⟨hbσ, (Finset.mem_inter.mp hbm).2⟩⟩

theorem meetAux_names
    (stable : ∀ {t : CTerm} {m k n : Label}, m ≠ k → distRS.isStep t k →
      Creates t m n → Creates (distRS.contract t k) m n)
    (fuel : ℕ) {t : CTerm} {σ τ : List Label} (hσ : distRS.Valid t σ)
    (hτ : distRS.Valid t τ) (hlen : σ.length ≤ fuel) :
    names (meetAux fuel t σ τ) = names σ ∩ names τ := by
  induction fuel generalizing t σ τ with
  | zero =>
    have he : σ = [] := List.length_eq_zero_iff.mp (by omega)
    subst σ; simp [meetAux, names]
  | succ fuel ih =>
    unfold meetAux
    split_ifs with h
    · let a := Nat.find h
      have hh : distRS.isStep t a ∧ distRS.Prefix t [a] σ ∧ distRS.Prefix t [a] τ := Nat.find_spec h
      have hva := ResidualSystem.valid_singleton hh.1
      have ham : a ∈ names σ ∩ names τ := Finset.mem_inter.mpr
        ⟨(prefix_names hva hσ).mp hh.2.1 (by simp [names]),
          (prefix_names hva hτ).mp hh.2.2 (by simp [names])⟩
      have hvs := ResidualSystem.proj_valid orthogonal_core hσ hva
      have hvt := ResidualSystem.proj_valid orthogonal_core hτ hva
      rw [tgt_cons_core, tgt_nil_core] at hvs hvt
      have hbnd : (distRS.proj t σ [a]).length ≤ fuel := by
        have := length_proj_lt hσ hh.1 (Finset.mem_inter.mp ham).1
        omega
      change names (a :: meetAux fuel (distRS.contract t a) _ _) = _
      rw [names_cons, ih hvs hvt hbnd, names_proj_core hσ hva, names_proj_core hτ hva]
      ext b
      by_cases he : b = a
      · subst b; simp [ham]
      · simp [names, he]
    · have he : names σ ∩ names τ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
        obtain ⟨a, ha, ham⟩ := common_source stable hσ hτ ⟨b, hb⟩
        have hva := ResidualSystem.valid_singleton ha
        exact h ⟨a, ha,
          (prefix_names hva hσ).mpr (by simpa [names] using (Finset.mem_inter.mp ham).1),
          (prefix_names hva hτ).mpr (by simpa [names] using (Finset.mem_inter.mp ham).2)⟩
      simpa [names] using he.symm

end distRS

namespace DTerm

theorem isLamWith_shift (t : DTerm) (d c : ℕ) (n : Label) :
    (t.shift d c).isLamWith n = t.isLamWith n := by
  cases t with
  | var => simp only [shift]; split <;> simp only [isLamWith]
  | lam => simp only [shift, isLamWith]
  | app => simp only [shift, isLamWith]

theorem hasRedex_shift (t : DTerm) (d c : ℕ) (n : Label) :
    (t.shift d c).hasRedex n = t.hasRedex n := by
  induction t using DTerm.ind generalizing c with
  | var => simp only [shift]; split <;> simp only [hasRedex]
  | lam m t ih => simp only [shift, hasRedex, ih]
  | app t ss ih ihs =>
    simp only [shift, hasRedex, isLamWith_shift, ih, List.any_map]
    congr 1
    induction ss with
    | nil => rfl
    | cons s ss ihss =>
      simp only [List.any_cons, Function.comp_apply, ihs s (by simp)]
      rw [ihss (fun s hs => ihs s (by simp [hs]))]

end DTerm

/-- An application headed by the substituted variable whose matching resource is a lambda. -/
def CreationSite (t : DTerm) (k : ℕ) (n : Label) (ss : List DTerm) : Prop :=
  ∃ (C : DCtx) (τ : Ty) (us : List DTerm) (b : DTerm), t = C.plug (.app (.var (k + C.depth) τ) us) ∧
    .lam n b ∈ ss ∧ (DTerm.lam n b).ty = τ

theorem PSubst.lam_head {t u : DTerm} {k : ℕ} {ss : List DTerm} {n : Label}
    (hp : PSubst t k ss u) (hu : u.isLamWith n = true) :
    (∃ b, t = .lam n b) ∨
      (∃ τ b, t = .var k τ ∧ ss = [.lam n b] ∧ (DTerm.lam n b).ty = τ) := by
  cases hp with
  | @var_eq s Γ τ k ht =>
    rw [DTerm.isLamWith_shift] at hu
    cases s with
    | var => simp [DTerm.isLamWith] at hu
    | app => simp [DTerm.isLamWith] at hu
    | lam m b =>
      have he : m = n := by simpa [DTerm.isLamWith] using hu
      subst m
      exact .inr ⟨τ, b, rfl, rfl, (hasType_ty ht).symm⟩
  | var_lt => simp [DTerm.isLamWith] at hu
  | var_gt => simp [DTerm.isLamWith] at hu
  | lam m h =>
    have he : m = n := by simpa [DTerm.isLamWith] using hu
    subst m
    exact .inl ⟨_, rfl⟩
  | app => simp [DTerm.isLamWith] at hu

/-- A new redex internal to substitution must come from putting a lambda resource
in function position (creation case III, `08-08-creation.tex`). -/
theorem PSubst.creation_site {t u : DTerm} {k : ℕ} {ss : List DTerm} {n : Label}
    (hp : PSubst t k ss u) (ht : t.hasRedex n = false)
    (hs : ∀ s ∈ ss, s.hasRedex n = false) (hu : u.hasRedex n = true) :
    CreationSite t k n ss := by
  induction hp using PSubst.rec
    (motive_2 := fun ts k ss us _ => (∀ t ∈ ts, t.hasRedex n = false) →
      (∀ s ∈ ss, s.hasRedex n = false) →
      (∃ u ∈ us, u.hasRedex n = true) → ∃ t ∈ ts, CreationSite t k n ss) with
  | var_eq k ht =>
    rw [DTerm.hasRedex_shift, hs _ (by simp)] at hu
    contradiction
  | var_lt => simp [DTerm.hasRedex] at hu
  | var_gt => simp [DTerm.hasRedex] at hu
  | @lam t u k ss m hp ih =>
    obtain ⟨C, τ, us, b, he, hm, hty⟩ := ih (by simpa only [DTerm.hasRedex] using ht) hs (by simpa only [DTerm.hasRedex] using hu)
    refine ⟨.lam m C, τ, us, b, ?_, hm, hty⟩
    simpa only [DCtx.plug, DCtx.depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (DTerm.lam m) he
  | @app t u ts us ss ss₀ ss₁ k hp hps hperm ih ihs =>
    have ht' := ht
    simp only [DTerm.hasRedex, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at ht'
    have hs₀ : ∀ s ∈ ss₀, s.hasRedex n = false :=
      fun s hm => hs s (hperm.subset (List.mem_append_left _ hm))
    have hs₁ : ∀ s ∈ ss₁, s.hasRedex n = false :=
      fun s hm => hs s (hperm.subset (List.mem_append_right _ hm))
    simp only [DTerm.hasRedex, Bool.or_eq_true, List.any_eq_true] at hu
    rcases hu with (hu | hu) | hu
    · rcases hp.lam_head hu with ⟨b, rfl⟩ | ⟨τ, b, rfl, rfl, hty⟩
      · simp [DTerm.isLamWith] at ht'
      · exact ⟨.hole, τ, ts, b, by simp [DCtx.plug, DCtx.depth],
          hperm.subset (by simp), hty⟩
    · obtain ⟨C, τ, vs, b, he, hm, hty⟩ := ih ht'.1.2 hs₀ hu
      have he' : DTerm.app t ts = (DCtx.appL C ts).plug
          (.app (.var (k + (DCtx.appL C ts).depth) τ) vs) := by
        simpa only [DCtx.plug, DCtx.depth] using congrArg (fun t => DTerm.app t ts) he
      exact ⟨.appL C ts, τ, vs, b, he', hperm.subset (List.mem_append_left _ hm), hty⟩
    · obtain ⟨s, hm, C, τ, vs, b, he, hb, hty⟩ := ihs ht'.2 hs₁ hu
      obtain ⟨ts₁, ts₂, he'⟩ := List.mem_iff_append.mp hm
      subst ts
      refine ⟨.appR t ts₁ C ts₂, τ, vs, b, ?_,
        hperm.subset (List.mem_append_right _ hb), hty⟩
      simp only [DCtx.plug, DCtx.depth, ← he]
  | nil => rename_i ht hs hu; simp at hu
  | @cons t u ts us ss₀ ss₁ k hp hps ih ihs =>
    rename_i ht hs hu
    have hs₀ : ∀ s ∈ ss₀, s.hasRedex n = false := fun s hm => hs s (by simp [hm])
    have hs₁ : ∀ s ∈ ss₁, s.hasRedex n = false := fun s hm => hs s (by simp [hm])
    obtain ⟨v, hv, hu⟩ := hu
    rcases List.mem_cons.mp hv with rfl | hv
    · obtain ⟨C, τ, vs, b, he, hm, hty⟩ := ih (ht t (by simp)) hs₀ hu
      exact ⟨t, by simp, C, τ, vs, b, he, List.mem_append_left _ hm, hty⟩
    · obtain ⟨s, hm, C, τ, vs, b, he, hb, hty⟩ := ihs
        (fun s hm => ht s (by simp [hm])) hs₁ ⟨v, hv, hu⟩
      exact ⟨s, by simp [hm], C, τ, vs, b, he, List.mem_append_right _ hb, hty⟩

open distRS

theorem distRS.CreationCase.lam {t : DTerm} {m n : Label} (h : CreationCase t m n) (a : Label) :
    CreationCase (.lam a t) m n := by
  cases h with
  | I C m n τ b ss => exact .I (.lam a C) m n τ b ss
  | II C m n b ss us => exact .II (.lam a C) m n b ss us
  | III C D m n τ us ss₁ ss₂ b he => exact .III (.lam a C) D m n τ us ss₁ ss₂ b he

theorem distRS.CreationCase.appL {t : DTerm} {m n : Label} (h : CreationCase t m n) (ss : List DTerm) :
    CreationCase (.app t ss) m n := by
  cases h with
  | I C m n τ b us => exact .I (.appL C ss) m n τ b us
  | II C m n b us vs => exact .II (.appL C ss) m n b us vs
  | III C D m n τ us ss₁ ss₂ b he => exact .III (.appL C ss) D m n τ us ss₁ ss₂ b he

theorem distRS.CreationCase.appR {s : DTerm} {m n : Label} (h : CreationCase s m n)
    (t : DTerm) (us vs : List DTerm) : CreationCase (.app t (us ++ s :: vs)) m n := by
  cases h with
  | I C m n τ b ss => exact .I (.appR t us C vs) m n τ b ss
  | II C m n b ss ts => exact .II (.appR t us C vs) m n b ss ts
  | III C D m n τ ts ss₁ ss₂ b he => exact .III (.appR t us C vs) D m n τ ts ss₁ ss₂ b he

/-- The three syntactic creation cases, by induction on the contracting context
(`08-08-creation.tex`). -/
theorem DStep.creation_case {t u : DTerm} {m n : Label} (h : DStep t m u)
    (hc : Correct t) (ht : t.hasRedex n = false) (hu : u.hasRedex n = true) :
    CreationCase t m n := by
  induction h with
  | beta m b ss =>
    have hp := hc.beta_partition
    have ht' := ht
    simp only [DTerm.hasRedex, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at ht'
    obtain ⟨C, τ, us, b', he, hm, hty⟩ := hp.creation_site ht'.1.2 ht'.2 hu
    obtain ⟨ss₁, ss₂, rfl⟩ := List.mem_iff_append.mp hm
    subst b
    simpa only [DCtx.plug, Nat.zero_add] using
      CreationCase.III .hole C m n τ us ss₁ ss₂ b' hty
  | lam a h ih =>
    apply CreationCase.lam (ih (hc.sub (.lam a (.refl _))) _ _) a
    · simpa only [DTerm.hasRedex] using ht
    · simpa only [DTerm.hasRedex] using hu
  | @appL t t' m ss h ih =>
    have ht' := ht
    simp only [DTerm.hasRedex, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at ht'
    simp only [DTerm.hasRedex, Bool.or_eq_true, List.any_eq_true] at hu
    rcases hu with (hu | hu) | ⟨s, hs, hu⟩
    · cases h with
      | beta m b ts =>
        have hp := (hc.sub (.fn ss (.refl _))).beta_partition
        rcases hp.lam_head hu with ⟨b', rfl⟩ | ⟨τ, b', rfl, rfl, hty⟩
        · exact CreationCase.II .hole m n b' ts ss
        · exact CreationCase.I .hole m n τ b' ss
      | lam a h =>
        have he : a = n := by simpa [DTerm.isLamWith] using hu
        simp [DTerm.isLamWith, he] at ht'
      | appL => simp [DTerm.isLamWith] at hu
      | appR => simp [DTerm.isLamWith] at hu
    · exact (ih (hc.sub (.fn ss (.refl _))) ht'.1.2 hu).appL ss
    · rw [ht'.2 s hs] at hu; contradiction
  | @appR s s' m t us vs h ih =>
    have ht' := ht
    simp only [DTerm.hasRedex, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at ht'
    simp only [DTerm.hasRedex, Bool.or_eq_true, List.any_eq_true] at hu
    have hnew : s'.hasRedex n = true := by
      rcases hu with (hu | hu) | ⟨v, hv, hu⟩
      · rw [ht'.1.1] at hu; contradiction
      · rw [ht'.1.2] at hu; contradiction
      · rcases List.mem_append.mp hv with hv | hv
        · rw [ht'.2 v (by simp [hv])] at hu; contradiction
        · rcases List.mem_cons.mp hv with rfl | hv
          · exact hu
          · rw [ht'.2 v (by simp [hv])] at hu; contradiction
    exact (ih (hc.sub (.arg t (by simp) (.refl s))) (ht'.2 s (by simp)) hnew).appR t us vs

/-- The immediate syntactic owner of a lambda that can be exposed by creation. -/
inductive LambdaOwner : DTerm → Label → Label → Prop
  | body (m n : Label) (b : DTerm) : LambdaOwner (.lam m (.lam n b)) m n
  | argument (m n : Label) (b c : DTerm) {ss : List DTerm} :
      .lam n c ∈ ss → LambdaOwner (.app (.lam m b) ss) m n
  | lam {t : DTerm} {m n : Label} (a : Label) : LambdaOwner t m n → LambdaOwner (.lam a t) m n
  | fn {t : DTerm} {m n : Label} (ss : List DTerm) : LambdaOwner t m n → LambdaOwner (.app t ss) m n
  | arg {s : DTerm} {m n : Label} (t : DTerm) {ss : List DTerm} :
      s ∈ ss → LambdaOwner s m n → LambdaOwner (.app t ss) m n

theorem LambdaOwner.label_mem {t : DTerm} {m n : Label} (h : LambdaOwner t m n) :
    n ∈ t.lamLabels := by
  induction h with
  | body => simp [DTerm.lamLabels]
  | argument m n b c hm =>
    simp only [DTerm.lamLabels, List.mem_append, List.mem_flatMap]
    exact .inr ⟨_, hm, by simp [DTerm.lamLabels]⟩
  | lam _ _ ih => simp [DTerm.lamLabels, ih]
  | fn _ _ ih => simp [DTerm.lamLabels, ih]
  | arg t hm _ ih =>
    simp only [DTerm.lamLabels, List.mem_append, List.mem_flatMap]
    exact .inr ⟨_, hm, ih⟩

theorem LambdaOwner.not_root {b : DTerm} {m n : Label} (hc : Correct (.lam n b)) :
    ¬ LambdaOwner (.lam n b) m n := by
  intro h
  have hn := hc.uniquely_labeled
  rw [DTerm.lamLabels] at hn
  cases h with
  | body => exact (List.nodup_cons.mp hn).1 (by simp [DTerm.lamLabels])
  | lam _ h => exact (List.nodup_cons.mp hn).1 h.label_mem

/-- A unique lambda label can occur in only one child of an application. -/
theorem unique_label_child {ss : List DTerm} {s r : DTerm} {n : Label}
    (hn : (ss.flatMap DTerm.lamLabels).Nodup) (hs : s ∈ ss) (hr : r ∈ ss)
    (hns : n ∈ s.lamLabels) (hnr : n ∈ r.lamLabels) : s = r := by
  induction ss with
  | nil => simp at hs
  | cons a ss ih =>
    rw [List.flatMap_cons] at hn
    have hh := List.nodup_append.mp hn
    rcases List.mem_cons.mp hs with rfl | hsTail <;> rcases List.mem_cons.mp hr with rfl | hrTail
    · rfl
    · exact False.elim (hh.2.2 n hns n (List.mem_flatMap.mpr ⟨r, hrTail, hnr⟩) rfl)
    · exact False.elim (hh.2.2 n hnr n (List.mem_flatMap.mpr ⟨s, hsTail, hns⟩) rfl)
    · exact ih hh.2.1 hsTail hrTail

theorem Correct.fn_arg_labels {t s : DTerm} {ss : List DTerm} {n : Label}
    (hc : Correct (.app t ss)) (ht : n ∈ t.lamLabels) (hs : s ∈ ss)
    (hn : n ∈ s.lamLabels) : False := by
  have hh := hc.uniquely_labeled
  rw [DTerm.lamLabels] at hh
  exact (List.nodup_append.mp hh).2.2 n ht n (List.mem_flatMap.mpr ⟨s, hs, hn⟩) rfl

theorem LambdaOwner.unique {t : DTerm} {m k n : Label} (hc : Correct t)
    (h₁ : LambdaOwner t m n) (h₂ : LambdaOwner t k n) : m = k := by
  induction h₁ generalizing k with
  | body m n b =>
    cases h₂ with
    | body => rfl
    | lam _ h => exact False.elim (LambdaOwner.not_root (hc.sub (.lam m (.refl _))) h)
  | @argument m n b c ss hm =>
    cases h₂ with
    | argument => rfl
    | fn _ h => exact False.elim (hc.fn_arg_labels h.label_mem hm (by simp [DTerm.lamLabels]))
    | arg _ hs h =>
      have hh := hc.uniquely_labeled
      rw [DTerm.lamLabels] at hh
      have he := unique_label_child (List.nodup_append.mp hh).2.1 hs hm h.label_mem
        (by simp [DTerm.lamLabels])
      subst he
      exact False.elim (LambdaOwner.not_root (hc.sub (.arg _ hm (.refl _))) h)
  | @lam t m n a h ih =>
    cases h₂ with
    | body => exact False.elim (LambdaOwner.not_root (hc.sub (.lam a (.refl _))) h)
    | lam _ h₂ => exact ih (hc.sub (.lam a (.refl _))) h₂
  | @fn t m n ss h ih =>
    cases h₂ with
    | argument _ _ _ _ hm =>
      exact False.elim (hc.fn_arg_labels h.label_mem hm (by simp [DTerm.lamLabels]))
    | fn _ h₂ => exact ih (hc.sub (.fn ss (.refl t))) h₂
    | arg _ hs h₂ => exact False.elim (hc.fn_arg_labels h.label_mem hs h₂.label_mem)
  | @arg s m n t ss hs h ih =>
    cases h₂ with
    | argument a n b c hm =>
      have hh := hc.uniquely_labeled
      rw [DTerm.lamLabels] at hh
      have he := unique_label_child (List.nodup_append.mp hh).2.1 hs hm h.label_mem
        (by simp [DTerm.lamLabels])
      subst he
      exact False.elim (LambdaOwner.not_root (hc.sub (.arg _ hm (.refl _))) h)
    | fn _ h₂ => exact False.elim (hc.fn_arg_labels h₂.label_mem hs h.label_mem)
    | arg _ hr h₂ =>
      have hh := hc.uniquely_labeled
      rw [DTerm.lamLabels] at hh
      have he := unique_label_child (List.nodup_append.mp hh).2.1 hs hr h.label_mem h₂.label_mem
      subst he
      exact ih (hc.sub (.arg t hs (.refl s))) h₂

theorem LambdaOwner.plug {t : DTerm} {m n : Label} (h : LambdaOwner t m n) (C : DCtx) :
    LambdaOwner (C.plug t) m n := by
  induction C with
  | hole => exact h
  | lam a C ih => exact .lam a ih
  | appL C ss ih => exact .fn ss ih
  | appR f us C vs ih => exact .arg f (by simp) ih

theorem distRS.CreationCase.owner {t : DTerm} {m n : Label} (h : CreationCase t m n) :
    LambdaOwner t m n := by
  cases h with
  | I C m n τ b ss => exact (LambdaOwner.fn ss (.argument m n _ b (by simp))).plug C
  | II C m n b ss us => exact (LambdaOwner.fn us (.fn ss (.body m n b))).plug C
  | III C D m n τ us ss₁ ss₂ b he => exact (LambdaOwner.argument m n _ b (by simp)).plug C

namespace distRS

theorem creation_core {t : CTerm} {m n : Label} (h : Creates t m n) : CreationCase t.1 m n :=
  (step_contract h.1).creation_case t.2 (Bool.eq_false_iff.mpr (creates_iff.mp h).2.2) h.2.1

theorem basic_stability_core {t : CTerm} {m k n : Label} (hmk : m ≠ k)
    (hk : distRS.isStep t k) (h : Creates t m n) : Creates (distRS.contract t k) m n := by
  have hh := creates_iff.mp h
  have hmk' := step_after hh.1 hk hmk
  have hkm := step_after hk hh.1 (Ne.symm hmk)
  have hnk : n ≠ k := fun he => hh.2.2 (he.symm ▸ hk)
  have hnfinal := step_after hh.2.1 hkm hnk
  obtain ⟨u, hu, hv⟩ := strong_permutation t.2 (step_contract hh.1) (step_contract hk) (.inl hmk)
  have hsquare : distRS.contract (distRS.contract t m) k = distRS.contract (distRS.contract t k) m := by
    apply Subtype.ext
    exact ((dStep_iff_hasRedex (distRS.contract t m).2).mp hu).2.symm.trans
      ((dStep_iff_hasRedex (distRS.contract t k).2).mp hv).2
  rw [hsquare] at hnfinal
  apply creates_iff.mpr ⟨hmk', hnfinal, ?_⟩
  intro hn
  have hkcreates := creates_iff.mpr ⟨hk, hn, hh.2.2⟩
  exact hmk (LambdaOwner.unique t.2 (creation_core h).owner (creation_core hkcreates).owner)

end distRS

namespace distRS

theorem meet_valid {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    distRS.Valid t (meet t σ τ) := by
  suffices hv : ∀ fuel t σ τ, distRS.Valid t σ → distRS.Valid t τ →
      distRS.Valid t (meetAux fuel t σ τ) from hv _ _ _ _ hσ hτ
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel ih =>
    intro t σ τ hσ hτ
    unfold meetAux
    split_ifs with h
    · have hh := Nat.find_spec h
      exact ⟨hh.1, ih _ _ _
        (ResidualSystem.proj_valid orthogonal_core hσ (ResidualSystem.valid_singleton hh.1))
        (ResidualSystem.proj_valid orthogonal_core hτ (ResidualSystem.valid_singleton hh.1))⟩
    · trivial

end distRS

end Ch3Appendix

/-! ## Chapter 3: Residual theory of λ^dist

Main-text results of Chapter 3:
* Residuals, finite developments, and orthogonality of `distRS` (`card_res`,
  `length_of_completeDevelopment`, `orthogonal`).
* Names, belonging, permanence, and prefixes as subsets (`permanence`,
  `characterization_of_belonging`, `names_append_disjoint`, `length_eq_card_names`,
  `names_proj`, `prefix_iff_subset`, `permEq_iff_names`).
* Creation and stability (`creation`, `basic_stability`, `full_stability`).
* Meets (`meet_isGLB`, `names_join`, `names_meet`), the `DistribLattice` structure on
  `DSpace distRS t`, and the ring-of-sets representation `namesHom`. -/

section Ch3Main

namespace distRS

variable {t : CTerm}

/-- **Cardinality of the set of residuals**: `#(R/S) = 0` if `R = S`, and `1` otherwise. -/
theorem card_res {ℓ m : Label} (hℓ : distRS.isStep t ℓ) (hm : distRS.isStep t m) :
    (distRS.res t m ℓ).card = if ℓ = m then 0 else 1 := by
  rw [res_formula hℓ hm]
  split_ifs <;> simp

theorem res_eq {ℓ m : Label} (hℓ : distRS.isStep t ℓ) (hm : distRS.isStep t m) :
    distRS.res t m ℓ = if ℓ = m then ∅ else {ℓ} := by
  have := card_res hℓ hm
  dsimp only [distRS] at this ⊢
  split_ifs at this ⊢ <;> simp_all

/-- **Finite developments**: every complete development of `M` has length `#M`. -/
theorem length_of_completeDevelopment {M : Finset Label} {σ : List Label}
    (hM : ∀ ℓ ∈ M, distRS.isStep t ℓ) (h : distRS.IsCompleteDevelopment t M σ) :
    σ.length = M.card := by
  have hv := ResidualSystem.isDevelopment_valid h.1
  have he : M = names σ := Finset.Subset.antisymm
    (Finset.sdiff_eq_empty_iff_subset.mp ((residual_names hM hv).1.symm.trans h.2))
    (development_subset hM h.1)
  rw [he]
  exact (List.toFinset_card_of_nodup (nodup_of_valid hv)).symm

/-- **λ^dist is an orthogonal axiomatic rewrite system** in the sense of Melliès
(Autoerasure and Finite Residuals from `card_res`, Finite Developments from
`length_of_completeDevelopment`, Semantic Orthogonality from `strong_permutation`). -/
theorem orthogonal : distRS.Orthogonal := by
  exact orthogonal_core

instance : Fact distRS.Orthogonal := ⟨orthogonal⟩

/-! ## Names -/

/-- **Permanence**: if `R ∉ σ` then `R/σ` is a singleton (with the same name). -/
theorem permanence {ℓ : Label} {σ : List Label} (hℓ : distRS.isStep t ℓ) (hσ : distRS.Valid t σ)
    (h : ¬ Belongs t ℓ σ) : distRS.resSetDeriv t {ℓ} σ = {ℓ} := by
  have hn : ℓ ∉ names σ := fun hmem => h ((belongs_names hℓ hσ).mpr hmem)
  rw [(residual_names (M := {ℓ}) (fun a ha => (Finset.mem_singleton.mp ha) ▸ hℓ) hσ).1]
  simp [hn]

/-- **Characterization of belonging**: for coinitial `R` and `σ`,
`R ∈ σ ⟺ R ⊑ σ ⟺ name(R) ∈ names(σ)`. -/
theorem characterization_of_belonging {ℓ : Label} {σ : List Label} (hℓ : distRS.isStep t ℓ)
    (hσ : distRS.Valid t σ) :
    [Belongs t ℓ σ, distRS.Prefix t [ℓ] σ, ℓ ∈ names σ].TFAE := by
  have h₁ := belongs_names hℓ hσ
  have h₂ : distRS.Prefix t [ℓ] σ ↔ ℓ ∈ names σ := by
    rw [prefix_names (ResidualSystem.valid_singleton hℓ) hσ]
    simp [names]
  tfae_have 1 ↔ 3 := h₁
  tfae_have 2 ↔ 3 := h₂
  tfae_finish

theorem names_append (σ τ : List Label) : names (σ ++ τ) = names σ ∪ names τ := by
  simp [names, List.toFinset_append]

/-- `names(στ) = names(σ) ⊎ names(τ)`. -/
theorem names_append_disjoint {σ τ : List Label} (h : distRS.Valid t (σ ++ τ)) :
    Disjoint (names σ) (names τ) := by
  have := (List.nodup_append.1 (nodup_of_valid h))
  rw [names, names, List.disjoint_toFinset_iff_disjoint]
  intro a ha hb
  exact this.2.2 a ha a hb rfl

/-- **The length of a derivation equals the number of distinct names along it.** -/
theorem length_eq_card_names {σ : List Label} (hσ : distRS.Valid t σ) :
    σ.length = (names σ).card :=
  (List.toFinset_card_of_nodup (nodup_of_valid hσ)).symm

/-- **Names after a projection**: `names(σ/τ) = names(σ) ∖ names(τ)`. -/
theorem names_proj {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    names (distRS.proj t σ τ) = names σ \ names τ := by
  exact names_proj_core hσ hτ

/-- **Prefixes as subsets**: `σ ⊑ τ ⟺ names(σ) ⊆ names(τ)`. -/
theorem prefix_iff_subset {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    distRS.Prefix t σ τ ↔ names σ ⊆ names τ := by
  exact prefix_names hσ hτ

/-- **Permutation equivalence in terms of names**: `σ ≡ τ ⟺ names(σ) = names(τ)`. -/
theorem permEq_iff_names {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    distRS.PermEq t σ τ ↔ names σ = names τ := by
  rw [ResidualSystem.PermEq, prefix_iff_subset hσ hτ, prefix_iff_subset hτ hσ,
    Finset.Subset.antisymm_iff]

/-! ## Creation and stability -/

/-- **Creation**: there are exactly three creation cases in λ^dist. -/
theorem creation {m n : Label} (h : Creates t m n) : CreationCase t.1 m n := by
  exact creation_core h

/-- **Stability**: if `R ≠ S` are coinitial and `R` creates `T`, then `R/S` creates
`T/(S/R)`. (With names: the step named `m` still creates `n` after the step named `k`.) -/
theorem basic_stability {m k n : Label} (hmk : m ≠ k) (hk : distRS.isStep t k)
    (h : Creates t m n) : Creates (distRS.contract t k) m n := by
  exact basic_stability_core hmk hk h

/-- **Full stability**: if `ρ₁` (after `σ`) and `ρ₂` (after `τ`) have a common residual `ρ₃`
after `σ ⊔ τ`, with `names σ ∩ names τ = ∅`, then they have a common ancestor `ρ₀`. -/
theorem full_stability {σ τ : List Label} {n₁ n₂ n₃ : Label} (hσ : distRS.Valid t σ)
    (hτ : distRS.Valid t τ) (hdisj : Disjoint (names σ) (names τ))
    (h₁ : distRS.isStep (distRS.tgt t σ) n₁) (h₂ : distRS.isStep (distRS.tgt t τ) n₂)
    (h₁₃ : distRS.resSetDeriv (distRS.tgt t σ) {n₁} (distRS.proj t τ σ) = {n₃})
    (h₂₃ : distRS.resSetDeriv (distRS.tgt t τ) {n₂} (distRS.proj t σ τ) = {n₃}) :
    ∃ n₀, distRS.isStep t n₀ ∧ distRS.resSetDeriv t {n₀} σ = {n₁} ∧
      distRS.resSetDeriv t {n₀} τ = {n₂} := by
  have he₁ : n₃ = n₁ := Finset.mem_singleton.mp
    (residual_subset _ _ _ (h₁₃.symm ▸ Finset.mem_singleton_self n₃))
  have he₂ : n₃ = n₂ := Finset.mem_singleton.mp
    (residual_subset _ _ _ (h₂₃.symm ▸ Finset.mem_singleton_self n₃))
  subst n₁
  subst n₂
  have hn := disjoint_available basic_stability hσ hτ hdisj h₁ h₂
  refine ⟨n₃, hn, ?_, ?_⟩
  · rw [(residual_names (M := {n₃}) (fun a ha => (Finset.mem_singleton.mp ha) ▸ hn) hσ).1]
    simp [step_not_names hσ h₁]
  · rw [(residual_names (M := {n₃}) (fun a ha => (Finset.mem_singleton.mp ha) ▸ hn) hτ).1]
    simp [step_not_names hτ h₂]

/-! ## Meets -/

/-- **Meet of derivations**: `σ ⊓ τ` is a greatest lower bound for the prefix order. -/
theorem meet_isGLB {t : CTerm} {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    distRS.Prefix t (meet t σ τ) σ ∧ distRS.Prefix t (meet t σ τ) τ ∧
      ∀ ρ, distRS.Valid t ρ → distRS.Prefix t ρ σ → distRS.Prefix t ρ τ →
        distRS.Prefix t ρ (meet t σ τ) := by
  have hh := meetAux_spec σ.length hσ hτ le_rfl
  have hv := meet_valid hσ hτ
  refine ⟨(prefix_names hv hσ).mpr (fun a ha => (Finset.mem_inter.mp (hh.1 ha)).1),
    (prefix_names hv hτ).mpr (fun a ha => (Finset.mem_inter.mp (hh.1 ha)).2), ?_⟩
  intro ρ hρ hρσ hρτ
  apply (prefix_names hρ hv).mpr
  exact hh.2 ρ hρ (fun a ha => Finset.mem_inter.mpr
    ⟨(prefix_names hρ hσ).mp hρσ ha, (prefix_names hρ hτ).mp hρτ ha⟩)

/-- **Names of join and meet** (1): `names(σ ⊔ τ) = names(σ) ∪ names(τ)`. -/
theorem names_join {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    names (distRS.join t σ τ) = names σ ∪ names τ := by
  rw [ResidualSystem.join, names_append, names_proj hτ hσ, Finset.union_sdiff_self_eq_union]

/-- **Names of join and meet** (2): `names(σ ⊓ τ) = names(σ) ∩ names(τ)`. -/
theorem names_meet {σ τ : List Label} (hσ : distRS.Valid t σ) (hτ : distRS.Valid t τ) :
    names (meet t σ τ) = names σ ∩ names τ := by
  exact meetAux_names basic_stability σ.length hσ hτ le_rfl

/-! ## The derivation space of a correct term is a distributive lattice -/

/-- `names` on permutation-equivalence classes. -/
def namesQ : distRS.DSpace t → Finset Label :=
  Quotient.lift (fun σ : distRS.DerivFrom t => names σ.1) fun σ τ h =>
    (permEq_iff_names σ.2 τ.2).1 h

@[simp] theorem namesQ_mk (σ : distRS.DerivFrom t) :
    namesQ (ResidualSystem.DSpace.mk σ) = names σ.1 := rfl

theorem namesQ_injective : Function.Injective (namesQ (t := t)) := by
  refine ResidualSystem.DSpace.ind fun σ => ResidualSystem.DSpace.ind fun τ => ?_
  intro h
  exact ResidualSystem.DSpace.mk_eq_mk.2 ((permEq_iff_names σ.2 τ.2).2 h)

/-- The meet as a derivation. -/
noncomputable def DerivFrom.meet (σ τ : distRS.DerivFrom t) : distRS.DerivFrom t :=
  ⟨CiruelosLic.distRS.meet t σ.1 τ.1, meet_valid σ.2 τ.2⟩

noncomputable instance : Min (distRS.DSpace t) where
  min := Quotient.map₂ DerivFrom.meet fun σ σ' hσ τ τ' hτ => by
    change distRS.PermEq t (meet t σ.1 τ.1) (meet t σ'.1 τ'.1)
    rw [permEq_iff_names (meet_valid σ.2 τ.2) (meet_valid σ'.2 τ'.2), names_meet σ.2 τ.2,
      names_meet σ'.2 τ'.2, (permEq_iff_names σ.2 σ'.2).1 hσ, (permEq_iff_names τ.2 τ'.2).1 hτ]

theorem namesQ_le_iff {x y : distRS.DSpace t} : namesQ x ⊆ namesQ y ↔ x ≤ y := by
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  exact (prefix_iff_subset σ.2 τ.2).symm

theorem namesQ_sup (x y : distRS.DSpace t) : namesQ (x ⊔ y) = namesQ x ∪ namesQ y := by
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  exact names_join σ.2 τ.2

theorem namesQ_inf (x y : distRS.DSpace t) : namesQ (x ⊓ y) = namesQ x ∩ namesQ y := by
  induction x using ResidualSystem.DSpace.ind with | h σ => ?_
  induction y using ResidualSystem.DSpace.ind with | h τ => ?_
  exact names_meet σ.2 τ.2

/-- **Theorem (derivations modulo `≡` form a distributive lattice).** For a correct term `t`,
`𝔻^dist(t)` is a distributive lattice, with `[σ] ∧ [τ] = [σ ⊓ τ]` and `[σ] ∨ [τ] = [σ ⊔ τ]`. -/
noncomputable instance instDistribLattice : DistribLattice (distRS.DSpace t) :=
  Function.Injective.distribLattice namesQ namesQ_injective
    (fun {_ _} => namesQ_le_iff)
    (fun {x y} => by
      rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
      exact and_congr namesQ_le_iff (not_congr namesQ_le_iff))
    namesQ_sup namesQ_inf

/-- **Theorem (the lattice of derivations is representable as a ring of sets).**
`names : 𝔻^dist(t) → 𝒫(ℒ)` is a monomorphism of lattices. -/
def namesHom : LatticeHom (distRS.DSpace t) (Finset Label) where
  toFun := namesQ
  map_sup' := namesQ_sup
  map_inf' := namesQ_inf

theorem namesHom_injective : Function.Injective (namesHom (t := t)) := namesQ_injective

theorem namesHom_mono : Monotone (namesHom (t := t)) := fun _ _ h => namesQ_le_iff.2 h

end distRS

/-- The derivation space `𝔻^dist(t)` of a correct term. -/
abbrev DSpaceDist (t : CTerm) : Type := distRS.DSpace t

end Ch3Main

end CiruelosLic
