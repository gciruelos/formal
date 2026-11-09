import MartinPhd.Chapter1Section6FlagVarieties
import MartinPhd.Chapter1Section8FlagSpeciesShuffle
import MartinPhd.Chapter1Section5SubspacesFlagVarieties
import MartinPhd.Chapter1Section6Bruhat

/-!
# Chapter 1, Section 1.6 (Steinberg module: self-duality, transvections, Lemma 1.13); placed after Section 1.8 because it uses the shuffle lemmas

Contents:
* `GL(Fⁿ)` acts transitively on flags of a given type
* Burnside count of `B`-fixed flags of a given type
* Simplicity of the Steinberg module (characteristic `0`)
* Self-duality of the Steinberg module (Lemma 1.22)
* Equivariance of the Corollary 1.9 isomorphism
* Inclusions and dimensions of `St^P` for parabolic subgroups
* Transvections in `GL(Fⁿ)`
* `St^P = 0` for parabolics `P ⊋ B` (Lemma 1.23, second half)
* Lower Transvections in Parabolic Subgroups
* Lemma 1.23 (assembly)
* Interval Transvections in Parabolic Subgroups
* Lemma 1.13, surjectivity (every `P ⊇ B` is a standard parabolic)
-/

section Trans

/-!
## `GL(Fⁿ)` acts transitively on flags of a given type
-/

open Module
noncomputable section
namespace MartinPhd

variable {F : Type} [Field F] [Fintype F]

theorem exists_smul_stdFlagOfType {n : ℕ} (c : Composition n) (G : Flag F (Fin n → F))
    (hG : G.IsOfType c) : ∃ g : GLn F n, g • stdFlagOfType F c = G := by
  have hstd : (stdFlagOfType F c).typeList = G.typeList := by
    rw [hG]; exact stdFlagOfType_isOfType F c
  obtain ⟨hlen, hdim⟩ := Flag.dims_eq_of_typeList_eq hstd
  obtain ⟨b, hb⟩ := exists_adapted_basis F n (Fin n → F) (Module.finrank_fin_fun F) G.carrier
    G.isChain
  set g : GLn F n := b.equivFun.symm with hg
  have hgsingle : ∀ j : Fin n, g (Pi.single j (1 : F)) = b j := by
    intro j
    rw [hg, LinearEquiv.symm_apply_eq]
    ext l
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  have hmap : ∀ m (hm : m < n + 1),
      Submodule.map (g : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n m) = b.flag ⟨m, hm⟩ := by
    intro m hm
    unfold stdSpan Module.Basis.flag
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨⟨j, hj⟩, rfl⟩, rfl⟩
      exact ⟨j, by simpa [Fin.lt_def] using hj, (hgsingle j).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, ⟨⟨j, by simpa [Fin.lt_def] using hj⟩, rfl⟩, hgsingle j⟩
  refine ⟨g, Flag.ext ?_⟩
  show (stdFlagOfType F c |>.map g).carrier = G.carrier
  rw [Flag.carrier_eq_image_nth (Flag.map g _), Flag.carrier_eq_image_nth G,
    Flag.card_eq_len_succ, Flag.card_eq_len_succ, Flag.len_map, hlen]
  refine Finset.image_congr fun i hi => ?_
  have hi' : i < G.len + 1 := Finset.mem_range.1 hi
  rw [Flag.nth_map]
  have hmem := (Flag.nth_mem (stdFlagOfType F c) (i := i) (by rw [Flag.card_eq_len_succ]; omega)).1
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hmem
  have hmemG := (Flag.nth_mem G (i := i) (by rw [Flag.card_eq_len_succ]; omega)).1
  obtain ⟨kk, hk⟩ := hb _ hmemG
  have hd := hdim i (by omega)
  have h1 : finrank F (stdFlagOfType F c |>.nth i) = j.val := by
    rw [← hj]; exact finrank_stdSpan F n (by have := j.2; omega)
  have h2 : finrank F (G.nth i) = kk.val := by rw [← hk]; exact finrank_flag' b kk
  have hjk : kk = j := Fin.ext (by omega)
  rw [← hj, hmap j.val j.2, ← hk, hjk]

end MartinPhd

end
end Trans

section StDim

/-!
## Burnside count of `B`-fixed flags of a given type
-/

open Module
noncomputable section
namespace MartinPhd

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

theorem isOfType_smul {n : ℕ} {c : Composition n} (g : GLn F n) {G : Flag F (Fin n → F)}
    (hG : G.IsOfType c) : (g • G).IsOfType c := by
  unfold Flag.IsOfType at *
  rw [← hG]
  exact Flag.typeList_map g G

/-- The count of fixed points of `b` on flags of type `c` equals that on `G/P_c`. -/
theorem card_fixed_flags_eq {n : ℕ} (c : Composition n) (b : GLn F n) :
    Nat.card {G : Flag F (Fin n → F) // G.IsOfType c ∧ b • G = G} =
      Nat.card {q : GLn F n ⧸ parabolic F c // b • q = q} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun q => ⟨MulAction.ofQuotientStabilizer (GLn F n) (stdFlagOfType F c) q.1, ?_, ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q.1
    rw [← hg]
    show (MulAction.ofQuotientStabilizer (GLn F n) (stdFlagOfType F c) (QuotientGroup.mk g)).IsOfType c
    rw [MulAction.ofQuotientStabilizer_mk]
    exact isOfType_smul g (stdFlagOfType_isOfType F c)
  · have := q.2
    have h2 := MulAction.ofQuotientStabilizer_smul (G := GLn F n) (x := stdFlagOfType F c) b q.1
    exact h2.symm.trans (congrArg (MulAction.ofQuotientStabilizer (GLn F n) (stdFlagOfType F c)) this)
  · intro q q' h
    apply Subtype.ext
    exact MulAction.injective_ofQuotientStabilizer (GLn F n) (stdFlagOfType F c)
      (congrArg Subtype.val h)
  · rintro ⟨G, hG, hb⟩
    obtain ⟨g, hg⟩ := exists_smul_stdFlagOfType c G hG
    have hq : MulAction.ofQuotientStabilizer (GLn F n) (stdFlagOfType F c)
        (QuotientGroup.mk g : GLn F n ⧸ parabolic F c) = G := by
      exact (MulAction.ofQuotientStabilizer_mk (G := GLn F n) (x := stdFlagOfType F c) g).trans hg
    refine ⟨⟨QuotientGroup.mk g, ?_⟩, Subtype.ext hq⟩
    apply MulAction.injective_ofQuotientStabilizer (GLn F n) (stdFlagOfType F c)
    exact (MulAction.ofQuotientStabilizer_smul (G := GLn F n) (x := stdFlagOfType F c) b _).trans
      ((congrArg (b • ·) hq).trans (hb.trans hq.symm))

theorem sum_card_fixed_flags {n : ℕ} (c : Composition n) [Fintype (borel F n)] :
    ∑ b : borel F n, Nat.card {G : Flag F (Fin n → F) // G.IsOfType c ∧ b.1 • G = G} =
      Nat.multinomial Finset.univ c.blocksFun * Nat.card (borel F n) := by
  classical
  haveI : Finite (GLn F n ⧸ parabolic F c) := inferInstance
  haveI : Fintype (GLn F n ⧸ parabolic F c) := Fintype.ofFinite _
  haveI : ∀ b : borel F n, Fintype (MulAction.fixedBy (GLn F n ⧸ parabolic F c) b) :=
    fun _ => Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient (borel F n) (GLn F n ⧸ parabolic F c)) :=
    Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (borel F n)
    (GLn F n ⧸ parabolic F c)
  have h18 := lemma_1_18 (F := F) c
  rw [Nat.card_eq_fintype_card] at h18 ⊢
  rw [← h18, ← hB]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [card_fixed_flags_eq c b.1, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.refl _)

theorem finrank_stFixed_borel [CharZero k] (n : ℕ) : finrank k (stFixed F k (borel F n)) = 1 := by
  classical
  haveI : Finite (borel F n) := inferInstance
  haveI : Fintype (borel F n) := Fintype.ofFinite _
  have hpos : (Nat.card (borel F n) : k) ≠ 0 := by
    have : 0 < Nat.card (borel F n) := Nat.card_pos
    exact_mod_cast this.ne'
  have h1 := finrank_stFixed (F := F) (k := k) n (borel F n)
  simp only [steinberg_character] at h1
  have h2 : ∑ b : borel F n, ∑ c : Composition n, (-1 : k) ^ (n - c.length) *
      (Nat.card {G : Flag F (Fin n → F) // G.IsOfType c ∧ b.1 • G = G} : k) =
      (Nat.card (borel F n) : k) * ∑ c : Composition n, (-1 : k) ^ (n - c.length) *
        (Nat.multinomial Finset.univ c.blocksFun : k) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.mul_sum, ← Nat.cast_sum, sum_card_fixed_flags c]
    push_cast; ring
  have h3 : ∑ c : Composition n, (-1 : k) ^ (n - c.length) *
      (Nat.multinomial Finset.univ c.blocksFun : k) = 1 := by
    have := congrArg (Int.cast : ℤ → k) (lemma_1_21_one n)
    simpa using this
  rw [h2, h3] at h1
  have : (finrank k (stFixed F k (borel F n)) : k) = 1 := by
    rw [h1]; field_simp
  exact_mod_cast this

end MartinPhd

end
end StDim

section StSimple

/-!
## Simplicity of the Steinberg module (characteristic `0`)

The thesis cites [Hum87]. Proof here: every nonzero `G`-submodule `S` of `Stₙ` contains a nonzero
`B`-fixed vector (average a translate of an element of `S` that is nonzero on the standard flag);
since `dim St^B = 1`, two nonzero submodules of `Stₙ` would intersect, contradicting a complement
(Maschke).
-/

open Module
noncomputable section
namespace MartinPhd

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

theorem stdFlag_isComplete (n : ℕ) : (stdFlag F n).IsComplete := by
  have hn : finrank F (Fin n → F) = n := Module.finrank_fin_fun F
  have hstd : stdFlag F n = jhFlag (Pi.basisFun F (Fin n)) :=
    (stdFlag_eq_flagOf F n).trans (Flag.ext rfl)
  rw [hstd]; unfold Flag.IsComplete Flag.len; rw [jhFlag_card, hn]; rfl

theorem exists_smul_stdFlag {n : ℕ} (G₀ : Flag F (Fin n → F)) (h : G₀.IsComplete) :
    ∃ g : GLn F n, g • stdFlag F n = G₀ := by
  obtain ⟨b, σ, hF, hG⟩ := jh_exists_common_permutation n (Module.finrank_fin_fun F) _ _
    (stdFlag_isComplete n) h
  refine ⟨b.equiv (b.reindex σ.symm) (Equiv.refl _), ?_⟩
  rw [hF, bruhat_smul_jhFlag, hG]
  congr 1
  apply Basis.eq_of_apply_eq
  intro i
  simp

theorem flagRep_apply_smul {n : ℕ} (h : GLn F n) (w : FlagModule F k n) (G : Flag F (Fin n → F)) :
    flagRep F k n h w (h • G) = w G :=
  Finsupp.mapDomain_apply_of_injective (MulAction.injective h) w G

theorem exists_borel_fixed [CharZero k] {n : ℕ} (S : Submodule k (steinberg F k n))
    (hS : ∀ (g : GLn F n) (w : steinberg F k n), w ∈ S → stAct F k g w ∈ S)
    (u : steinberg F k n) (huS : u ∈ S) (hu : u ≠ 0) :
    ∃ v ∈ S, v ≠ 0 ∧ ∀ b ∈ borel F n, stAct F k b v = v := by
  classical
  haveI : Fintype (borel F n) := Fintype.ofFinite _
  -- a complete flag in the support of `u`
  have hsupp : ∃ G₀ : Flag F (Fin n → F), (u : FlagModule F k n) G₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu (Subtype.ext (Finsupp.ext hcon))
  obtain ⟨G₀, hG₀⟩ := hsupp
  have hlen : G₀.len = n := by
    by_contra hne
    exact hG₀ (((mem_flagDeg_iff F k).1 u.2.1) G₀ hne)
  have hcomp : G₀.IsComplete := by
    unfold Flag.IsComplete; rw [hlen, Module.finrank_fin_fun]
  obtain ⟨g, hg⟩ := exists_smul_stdFlag G₀ hcomp
  set u' : steinberg F k n := stAct F k g⁻¹ u with hu'
  have hu'S : u' ∈ S := hS _ _ huS
  have hu'std : (u' : FlagModule F k n) (stdFlag F n) ≠ 0 := by
    have : (u' : FlagModule F k n) (stdFlag F n) = (u : FlagModule F k n) G₀ := by
      show flagRep F k n g⁻¹ (u : FlagModule F k n) (stdFlag F n) = _
      have h1 : stdFlag F n = g⁻¹ • G₀ := by rw [← hg]; simp
      rw [h1, flagRep_apply_smul]
    rw [this]; exact hG₀
  refine ⟨∑ b : borel F n, stAct F k b.1 u', Submodule.sum_mem _ fun b _ => hS _ _ hu'S, ?_, ?_⟩
  · intro hv
    have h1 := congrArg (fun w : steinberg F k n => (w : FlagModule F k n) (stdFlag F n)) hv
    simp only [Submodule.coe_sum, Finsupp.finsetSum_apply, ZeroMemClass.coe_zero,
      Finsupp.coe_zero, Pi.zero_apply] at h1
    have h2 : ∀ b : borel F n, (stAct F k b.1 u' : FlagModule F k n) (stdFlag F n) =
        (u' : FlagModule F k n) (stdFlag F n) := by
      intro b
      have hb : b.1 • stdFlag F n = stdFlag F n := b.2
      show flagRep F k n b.1 (u' : FlagModule F k n) (stdFlag F n) = _
      conv_lhs => rw [← hb]
      exact flagRep_apply_smul _ _ _
    simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have hne : (Fintype.card (borel F n) : k) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := borel F n)).ne'
    exact hu'std ((mul_eq_zero.1 h1).resolve_left hne)
  · intro b' hb'
    rw [map_sum]
    have hmul : ∀ b : borel F n, stAct F k b' (stAct F k b.1 u') = stAct F k (b' * b.1) u' :=
      fun b => (LinearMap.congr_fun (stAct_mul n b' b.1) u').symm
    simp only [hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨b', hb'⟩ : borel F n)) _ _ (fun b => rfl)

/-- `GL(Fⁿ)` acting on `Stₙ`. -/
def stRepFull (n : ℕ) : Representation k (GLn F n) (steinberg F k n) where
  toFun g := stAct F k g
  map_one' := stAct_one n
  map_mul' g h := stAct_mul n g h

/-- `Stₙ` is the unique simple `GL(Fⁿ)`-module of dimension `ℓ^{C(n,2)}`; we record
simplicity (in characteristic `0`).

**Note.** The thesis states this claim without proof, citing [Hum87]
(§1.5, p. 14: "Referimos al lector a [Hum87] para un resumen de sus muchas otras propiedades;
al final de la Sección 1.6 explicitaremos los detalles que necesitamos sobre su teoría de
representaciones"). We prove it from `dim St^B = 1` (Lemma 1.23) and Maschke's theorem: see the
module docstring. -/
theorem steinberg_simple [CharZero k] (n : ℕ) (W : Submodule k (FlagModule F k n))
    (hW : W ≤ steinberg F k n) (hinv : ∀ g, W.map (flagRep F k n g) ≤ W) :
    W = ⊥ ∨ W = steinberg F k n := by
  classical
  haveI : Finite (GLn F n) := inferInstance
  haveI : NeZero (Nat.card (GLn F n) : k) := ⟨by
    have : 0 < Nat.card (GLn F n) := Nat.card_pos
    exact_mod_cast this.ne'⟩
  let S₁ : Subrepresentation (stRepFull (F := F) (k := k) n) :=
    ⟨W.comap (steinberg F k n).subtype, fun g v hv =>
      hinv g (Submodule.mem_map_of_mem hv)⟩
  haveI hss : Representation.IsSemisimpleRepresentation (k := k) (G := GLn F n) (V := steinberg F k n) (stRepFull (F := F) (k := k) n) := by
    rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    infer_instance
  obtain ⟨S₂, hcompl⟩ := exists_isCompl S₁
  have hinf : S₁.toSubmodule ⊓ S₂.toSubmodule = ⊥ := by
    have := congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
    rwa [Subrepresentation.toSubmodule_inf] at this
  have hsup : S₁.toSubmodule ⊔ S₂.toSubmodule = ⊤ := by
    have := congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
    rwa [Subrepresentation.toSubmodule_sup] at this
  have hfix := finrank_stFixed_borel (F := F) (k := k) n
  by_cases h1 : S₁.toSubmodule = ⊥
  · left
    apply le_antisymm _ bot_le
    intro x hx
    have hxs : (⟨x, hW hx⟩ : steinberg F k n) ∈ S₁.toSubmodule := hx
    rw [h1] at hxs
    have := Submodule.mem_bot k |>.1 hxs
    simpa using congrArg Subtype.val this
  by_cases h2 : S₂.toSubmodule = ⊥
  · right
    apply le_antisymm hW
    intro x hx
    have : (⟨x, hx⟩ : steinberg F k n) ∈ S₁.toSubmodule ⊔ S₂.toSubmodule := by rw [hsup]; trivial
    rw [h2, sup_bot_eq] at this
    exact this
  exfalso
  obtain ⟨u₁, hu₁, hu₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
  obtain ⟨u₂, hu₂, hu₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h2
  obtain ⟨v₁, hv₁S, hv₁0, hv₁fix⟩ := exists_borel_fixed S₁.toSubmodule
    (fun g w hw => S₁.apply_mem_toSubmodule g hw) u₁ hu₁ hu₁0
  obtain ⟨v₂, hv₂S, hv₂0, hv₂fix⟩ := exists_borel_fixed S₂.toSubmodule
    (fun g w hw => S₂.apply_mem_toSubmodule g hw) u₂ hu₂ hu₂0
  let T : Submodule k (FlagModule F k n) :=
    (stFixed F k (borel F n)).map (steinberg F k n).subtype
  have hT : finrank k T = 1 := by
    rw [← hfix]
    exact (Submodule.equivMapOfInjective _ (steinberg F k n).injective_subtype _).symm.finrank_eq
  let w₁ : T := ⟨(v₁ : FlagModule F k n), ⟨v₁, hv₁fix, rfl⟩⟩
  let w₂ : T := ⟨(v₂ : FlagModule F k n), ⟨v₂, hv₂fix, rfl⟩⟩
  have hw₁ : w₁ ≠ 0 := fun h => hv₁0 (Subtype.ext (by
    have := congrArg (fun t : T => (t : FlagModule F k n)) h
    simpa [w₁] using this))
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' w₁ hw₁).1 hT w₂
  have hc' : c • v₁ = v₂ := Subtype.ext (by
    have := congrArg (fun t : T => (t : FlagModule F k n)) hc
    simpa [w₁, w₂] using this)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hv₂0 (by rw [← hc']; simp)
  have hv₁S₂ : v₁ ∈ S₂.toSubmodule := by
    have : v₁ = c⁻¹ • v₂ := by rw [← hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]; exact S₂.toSubmodule.smul_mem _ hv₂S
  have : v₁ ∈ S₁.toSubmodule ⊓ S₂.toSubmodule := ⟨hv₁S, hv₁S₂⟩
  rw [hinf] at this
  exact hv₁0 ((Submodule.mem_bot k).1 this)

end MartinPhd

end
end StSimple

section StSelfDual

/-!
## Self-duality of the Steinberg module (Lemma 1.22)

Proof (characteristic `0`): by `steinberg_character` the character of `Stₙ` is invariant under
`g ↦ g⁻¹` (it only counts fixed flags), hence `dim Hom_G(St, St*) = dim Hom_G(St, St) ≥ 1`
(character inner products); a nonzero equivariant map `St → St*` is injective because `St` is
simple (`steinberg_simple`), hence bijective by dimension.
-/

open Module
noncomputable section
namespace MartinPhd

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

theorem stChar_inv [CharZero k] (n : ℕ) (g : GLn F n) :
    LinearMap.trace k _ (stAct F k g⁻¹) = LinearMap.trace k _ (stAct F k g) := by
  rw [steinberg_character, steinberg_character]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  refine Nat.card_congr (Equiv.subtypeEquivRight fun G => ?_)
  rw [inv_smul_eq_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩

set_option maxHeartbeats 2000000 in
/-- **Lemma 1.22.** In characteristic `0`, `Stₙ ≅ Stₙ^*` as `GL(Fⁿ)`-modules, i.e.
`Stₙ` carries a nondegenerate invariant bilinear form.

Proof: `Stₙ` is simple (`steinberg_simple`) and its character is invariant under `g ↦ g⁻¹`
(`steinberg_character` only counts fixed flags), so `selfDual_of_simple_char` applies. -/
theorem lemma_1_22 [CharZero k] (n : ℕ) :
    ∃ e : steinberg F k n ≃ₗ[k] Module.Dual k (steinberg F k n),
      ∀ (g : GLn F n) (v w : steinberg F k n), e (stAct F k g v) (stAct F k g w) = e v w := by
  haveI : Nontrivial (steinberg F k n) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have := finrank_stFixed_borel (F := F) (k := k) n
    have h0 : finrank k (stFixed F k (borel F n)) = 0 := by
      haveI : Subsingleton (stFixed F k (borel F n)) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      exact Module.finrank_zero_of_subsingleton
    omega
  have hsimple : ∀ W : Submodule k (steinberg F k n),
      (∀ g, W.map ((stRepFull (F := F) (k := k) n) g) ≤ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    rcases steinberg_simple n (W.map (steinberg F k n).subtype) (by
        rintro _ ⟨w, -, rfl⟩; exact w.2) (fun g => by
        rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨stAct F k g w, hW g (Submodule.mem_map_of_mem hw), rfl⟩) with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      have : (w : FlagModule F k n) ∈ W.map (steinberg F k n).subtype := ⟨w, hw, rfl⟩
      rw [h] at this
      exact (Submodule.mem_bot k).2 (Subtype.ext ((Submodule.mem_bot k).1 this))
    · right
      rw [eq_top_iff]
      intro w _
      have : (w : FlagModule F k n) ∈ W.map (steinberg F k n).subtype := by rw [h]; exact w.2
      obtain ⟨w', hw', hww'⟩ := this
      have : w' = w := Subtype.ext hww'
      rw [← this]; exact hw'
  have hchar : ∀ g : GLn F n,
      Representation.character (k := k) (G := GLn F n) (V := steinberg F k n)
        (stRepFull (F := F) (k := k) n) g⁻¹ =
      Representation.character (k := k) (G := GLn F n) (V := steinberg F k n)
        (stRepFull (F := F) (k := k) n) g := fun g => stChar_inv n g
  haveI : Finite (GLn F n) := inferInstance
  obtain ⟨φ⟩ := selfDual_of_simple_char (G := GLn F n) (k := k) (V := steinberg F k n)
    (stRepFull (F := F) (k := k) n) hsimple hchar
  exact (exists_invariant_form_iff (k := k) (G := GLn F n) (V := steinberg F k n)
    (stRepFull (F := F) (k := k) n)).2 ⟨φ⟩

end MartinPhd

end
end StSelfDual

section DualEquiv

/-!
## Equivariance of the Corollary 1.9 isomorphism

The linear isomorphism `e : Hⁿ(Σₙ) ≅ Stₙ^*` of Corollary 1.9 descends from the evaluation
pairing `flagPairing` between flags. Since `flagPairing` is invariant under the diagonal action
of `GL(Fⁿ)` (`flagPairing_flagRep`), the isomorphism `e` is equivariant:
`e (g • x) (g • c) = e x c`.
-/

open scoped BigOperators
open Module

noncomputable section

namespace MartinPhd

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

/-- The evaluation pairing `flagPairing` is invariant under the diagonal `GL(Fⁿ)` action. -/
theorem flagPairing_flagRep {n : ℕ} (g : GLn F n) (φ c : FlagModule F k n) :
    flagPairing F k n (flagRep F k n g φ) (flagRep F k n g c) = flagPairing F k n φ c := by
  rw [flagPairing_eq, flagPairing_eq]
  rw [← Equiv.sum_comp (MulAction.toPerm g)]
  simp only [MulAction.toPerm_apply, flagRep_apply_smul]

/-- Equivariance of any linear isomorphism `Hⁿ(Σₙ) ≅ Stₙ^*` descending from the flag pairing. -/
theorem flagPairing_hsigma_equivariant {n : ℕ}
    {e : HSigma F k n n ≃ₗ[k] Module.Dual k (steinberg F k n)}
    (he : ∀ (φ : FlagModule F k n) (hφ : φ ∈ flagDeg F k n n ⊓ LinearMap.ker (sigmaD F k n))
      (c : steinberg F k n), e (Subquot.mk φ hφ) c = flagPairing F k n φ c)
    (g : GLn F n) (x : HSigma F k n n) (c : steinberg F k n) :
    e (hsigmaRep F k n n g x) (stAct F k g c) = e x c := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    obtain ⟨φ, hφ⟩ := a
    change e (hsigmaRep F k n n g (Subquot.mk φ hφ)) (stAct F k g c) = e (Subquot.mk φ hφ) c
    have h1 : hsigmaRep F k n n g (Subquot.mk φ hφ) =
        Subquot.mk (flagRep F k n g φ) (flagRep_mem_cycles n n g hφ) := rfl
    rw [h1, he, he]
    have hc : (stAct F k g c : FlagModule F k n) = flagRep F k n g (c : FlagModule F k n) := rfl
    show flagPairing F k n (flagRep F k n g φ) (stAct F k g c) = flagPairing F k n φ c
    rw [hc, flagPairing_flagRep]

/-- **Corollary 1.9 (equivariance).** The isomorphism `Hⁿ(Σₙ) ≅ Stₙ^*` given by
Corollary 1.9 is equivariant under `GL(Fⁿ)`: for all `g ∈ GL(Fⁿ)`, `x ∈ Hⁿ(Σₙ)`, and
`c ∈ Stₙ`, `e (g • x) (g • c) = e x c`. -/
theorem cor_1_9_equivariant (n : ℕ) :
    ∃ e : HSigma F k n n ≃ₗ[k] Module.Dual k (steinberg F k n),
      ∀ (g : GLn F n) (x : HSigma F k n n) (c : steinberg F k n),
        e (hsigmaRep F k n n g x) (stAct F k g c) = e x c := by
  obtain ⟨-, e, he⟩ := cor_1_9 F k n
  exact ⟨e, flagPairing_hsigma_equivariant he⟩

/-- **Corollary 1.9 (equivariance with pairing characterization).** -/
theorem cor_1_9_equivariant_pairing (n : ℕ) :
    ∃ e : HSigma F k n n ≃ₗ[k] Module.Dual k (steinberg F k n),
      (∀ (φ : FlagModule F k n) (hφ : φ ∈ flagDeg F k n n ⊓ LinearMap.ker (sigmaD F k n))
        (c : steinberg F k n), e (Subquot.mk φ hφ) c = flagPairing F k n φ c) ∧
      ∀ (g : GLn F n) (x : HSigma F k n n) (c : steinberg F k n),
        e (hsigmaRep F k n n g x) (stAct F k g c) = e x c := by
  obtain ⟨-, e, he⟩ := cor_1_9 F k n
  exact ⟨e, he, flagPairing_hsigma_equivariant he⟩

/-- Alias for `cor_1_9_equivariant`. -/
theorem cor_1_9_dualEquiv (n : ℕ) :
    ∃ e : HSigma F k n n ≃ₗ[k] Module.Dual k (steinberg F k n),
      ∀ (g : GLn F n) (x : HSigma F k n n) (c : steinberg F k n),
        e (hsigmaRep F k n n g x) (stAct F k g c) = e x c :=
  cor_1_9_equivariant n

end MartinPhd

end
end DualEquiv

section StFixedLe

/-!
## Inclusions and dimensions of `St^P` for parabolic subgroups

Properties of the fixed subspace `stFixed F k H` of the Steinberg module:
1. `stFixed_anti`: `H ≤ K → St^K ≤ St^H`.
2. `finrank_stFixed_parabolic_le`: for any parabolic `P`, `dim St^P ≤ 1`.
3. `stFixed_eq_bot_or_borel`: for any parabolic `P`, `St^P = ⊥ ∨ St^P = St^B`.
-/

open Module
noncomputable section
namespace MartinPhd

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

theorem stFixed_anti {n : ℕ} {H K : Subgroup (GLn F n)} (h : H ≤ K) :
    stFixed F k K ≤ stFixed F k H := by
  intro v hv g hg
  exact hv g (h hg)

theorem finrank_stFixed_parabolic_le [CharZero k] {n : ℕ} {P : Subgroup (GLn F n)}
    (hP : IsParabolic F P) : finrank k (stFixed F k P) ≤ 1 := by
  let T_P : Submodule k (FlagModule F k n) :=
    (stFixed F k P).map (steinberg F k n).subtype
  let T_B : Submodule k (FlagModule F k n) :=
    (stFixed F k (borel F n)).map (steinberg F k n).subtype
  have hTP : finrank k (stFixed F k P) = finrank k T_P :=
    (Submodule.equivMapOfInjective _ (steinberg F k n).injective_subtype _).finrank_eq
  have hTB : finrank k T_B = 1 := by
    rw [← finrank_stFixed_borel (F := F) (k := k) n]
    exact (Submodule.equivMapOfInjective _ (steinberg F k n).injective_subtype _).symm.finrank_eq
  have hle : T_P ≤ T_B := Submodule.map_mono (stFixed_anti hP)
  have : FiniteDimensional k T_B := FiniteDimensional.of_finrank_eq_succ hTB
  have hmono : finrank k T_P ≤ finrank k T_B := Submodule.finrank_mono hle
  omega

theorem stFixed_eq_bot_or_borel [CharZero k] {n : ℕ} {P : Subgroup (GLn F n)}
    (hP : IsParabolic F P) :
    stFixed F k P = ⊥ ∨ stFixed F k P = stFixed F k (borel F n) := by
  have hle : stFixed F k P ≤ stFixed F k (borel F n) := stFixed_anti hP
  by_cases h : stFixed F k P = ⊥
  · left; exact h
  · right
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    let T : Submodule k (FlagModule F k n) :=
      (stFixed F k (borel F n)).map (steinberg F k n).subtype
    have hT : finrank k T = 1 := by
      rw [← finrank_stFixed_borel (F := F) (k := k) n]
      exact (Submodule.equivMapOfInjective _ (steinberg F k n).injective_subtype _).symm.finrank_eq
    let w₁ : T := ⟨(u : FlagModule F k n), ⟨u, hle hu, rfl⟩⟩
    have hw₁ : w₁ ≠ 0 := fun hw => hu0 (Subtype.ext (by
      have := congrArg (fun t : T => (t : FlagModule F k n)) hw
      simpa [w₁] using this))
    apply le_antisymm hle
    intro v hv
    let w₂ : T := ⟨(v : FlagModule F k n), ⟨v, hv, rfl⟩⟩
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' w₁ hw₁).1 hT w₂
    have hc' : c • u = v := Subtype.ext (by
      have := congrArg (fun t : T => (t : FlagModule F k n)) hc
      simpa [w₁, w₂] using this)
    rw [← hc']
    exact Submodule.smul_mem _ _ hu

end MartinPhd

end
end StFixedLe

section Transvection

/-!
## Transvections in `GL(Fⁿ)`

`tvec i j h s = I + s E_{ij}` as a linear automorphism of `Fⁿ`: it sends `e_j ↦ e_j + s e_i`
and fixes every other standard basis vector. For `i < j` it lies in the Borel subgroup.
-/

open Module
noncomputable section
namespace MartinPhd

variable {F : Type} [Field F] {n : ℕ}

/-- The linear map `v ↦ v + s v_j e_i`. -/
def tvecMap (i j : Fin n) (s : F) : (Fin n → F) →ₗ[F] (Fin n → F) :=
  LinearMap.id + (LinearMap.proj j : (Fin n → F) →ₗ[F] F).smulRight (s • Pi.single i (1 : F))

theorem tvecMap_apply (i j : Fin n) (s : F) (v : Fin n → F) :
    tvecMap i j s v = v + (v j) • (s • Pi.single i (1 : F)) := by
  simp [tvecMap]

theorem tvecMap_add (i j : Fin n) (h : i ≠ j) (s t : F) :
    tvecMap i j s ∘ₗ tvecMap i j t = tvecMap i j (s + t) := by
  refine LinearMap.ext fun v => funext fun m => ?_
  by_cases hm : m = i
  · subst hm
    simp [tvecMap_apply, h, add_mul, mul_add]
    ring
  · simp [tvecMap_apply, hm, h, Pi.single_apply]

theorem tvecMap_zero (i j : Fin n) : tvecMap i j (0 : F) = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun m => ?_
  simp [tvecMap_apply]

/-- The transvection `I + s E_{ij}` (`i ≠ j`). -/
def tvec (i j : Fin n) (h : i ≠ j) (s : F) : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
  LinearEquiv.ofLinear (tvecMap i j s) (tvecMap i j (-s))
    (by rw [tvecMap_add i j h, add_neg_cancel, tvecMap_zero])
    (by rw [tvecMap_add i j h, neg_add_cancel, tvecMap_zero])

theorem tvec_apply (i j : Fin n) (h : i ≠ j) (s : F) (v : Fin n → F) :
    tvec i j h s v = v + (v j) • (s • Pi.single i (1 : F)) := tvecMap_apply i j s v

theorem tvec_single_self (i j : Fin n) (h : i ≠ j) (s : F) :
    tvec i j h s (Pi.single j 1) = Pi.single j 1 + s • Pi.single i (1 : F) := by
  rw [tvec_apply]; simp

theorem tvec_single_of_ne (i j : Fin n) (h : i ≠ j) (s : F) (m : Fin n) (hm : m ≠ j) :
    tvec i j h s (Pi.single m 1) = Pi.single m 1 := by
  rw [tvec_apply]; simp [Pi.single_apply, hm]

theorem tvec_zero (i j : Fin n) (h : i ≠ j) : tvec i j h (0 : F) = 1 := by
  refine LinearEquiv.ext fun v => funext fun m => ?_
  simp [tvec_apply]

theorem tvec_mul (i j : Fin n) (h : i ≠ j) (s t : F) :
    tvec i j h s * tvec i j h t = tvec i j h (s + t) := by
  refine LinearEquiv.ext fun v => funext fun m => ?_
  have := LinearMap.congr_fun (tvecMap_add i j h s t) v
  exact congrArg (fun w => w m) this

end MartinPhd

end
end Transvection

section StParZero

/-!
## `St^P = 0` for parabolics `P ⊋ B` (Lemma 1.23, second half)

Strategy (a variant of the thesis argument, with the Bruhat-cell signs replaced by the
cycle condition): a `B`-fixed vector `w` of `Stₙ` with `w(F⁰) ≠ 0` exists (average of a
vector over `B`). If `P ⊋ B` fixed `w`, then `w` is constant on `P F⁰`; for a suitable codimension-one
flag `H ⊂ F⁰` all refinements of `H` lie in `P F⁰`, so the cycle condition `∂w = 0` at `H`
gives `± N w(F⁰) = 0`, with `N ≥ 1` the number of refinements. Contradiction in characteristic `0`.
-/

open Module
noncomputable section
namespace MartinPhd

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

attribute [local instance] Classical.propDecidable

/-- A `B`-fixed vector of `Stₙ` not vanishing at the standard flag. -/
theorem exists_borel_fixed_std [CharZero k] {n : ℕ} (hn : 1 ≤ n) :
    ∃ v : steinberg F k n, (∀ b ∈ borel F n, stAct F k b v = v) ∧
      (v : FlagModule F k n) (stdFlag F n) ≠ 0 := by
  classical
  haveI : Fintype (borel F n) := Fintype.ofFinite _
  have hfin : 0 < finrank k (steinberg F k n) := by
    rw [(solomon_tits (F := F) (k := k) n hn).2.1]
    exact pow_pos Fintype.card_pos _
  obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hfin
  have hsupp : ∃ G₀ : Flag F (Fin n → F), (u : FlagModule F k n) G₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu (Subtype.ext (Finsupp.ext hcon))
  obtain ⟨G₀, hG₀⟩ := hsupp
  have hlen : G₀.len = n := by
    by_contra hne
    exact hG₀ (((mem_flagDeg_iff F k).1 u.2.1) G₀ hne)
  have hcomp : G₀.IsComplete := by
    unfold Flag.IsComplete; rw [hlen, Module.finrank_fin_fun]
  obtain ⟨g, hg⟩ := exists_smul_stdFlag G₀ hcomp
  set u' : steinberg F k n := stAct F k g⁻¹ u with hu'
  have hu'std : (u' : FlagModule F k n) (stdFlag F n) ≠ 0 := by
    have : (u' : FlagModule F k n) (stdFlag F n) = (u : FlagModule F k n) G₀ := by
      show flagRep F k n g⁻¹ (u : FlagModule F k n) (stdFlag F n) = _
      have h1 : stdFlag F n = g⁻¹ • G₀ := by rw [← hg]; simp
      rw [h1, flagRep_apply_smul]
    rw [this]; exact hG₀
  refine ⟨∑ b : borel F n, stAct F k b.1 u', ?_, ?_⟩
  · intro b' hb'
    rw [map_sum]
    have hmul : ∀ b : borel F n, stAct F k b' (stAct F k b.1 u') = stAct F k (b' * b.1) u' :=
      fun b => (LinearMap.congr_fun (stAct_mul n b' b.1) u').symm
    simp only [hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨b', hb'⟩ : borel F n)) _ _ (fun b => rfl)
  · intro h1
    simp only [Submodule.coe_sum, Finsupp.finsetSum_apply] at h1
    have h2 : ∀ b : borel F n, (stAct F k b.1 u' : FlagModule F k n) (stdFlag F n) =
        (u' : FlagModule F k n) (stdFlag F n) := by
      intro b
      have hb : b.1 • stdFlag F n = stdFlag F n := b.2
      show flagRep F k n b.1 (u' : FlagModule F k n) (stdFlag F n) = _
      conv_lhs => rw [← hb]
      exact flagRep_apply_smul _ _ _
    simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have hne : (Fintype.card (borel F n) : k) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := borel F n)).ne'
    exact hu'std ((mul_eq_zero.1 h1).resolve_left hne)

section Classif

variable {n a : ℕ}

/-- `g` fixes every standard basis vector but `e_a, e_{a+1}`, and preserves `⟨e_a, e_{a+1}⟩`
(well, maps those into `V_{a+2}`). -/
def NearId (ha : a + 1 < n) (g : GLn F n) : Prop :=
  (∀ m : Fin n, m.val ≠ a → m.val ≠ a + 1 → g (Pi.single m 1) = Pi.single m 1) ∧
  g (Pi.single (⟨a, by omega⟩ : Fin n) 1) ∈ stdSpan F n (a + 2) ∧
  g (Pi.single (⟨a + 1, ha⟩ : Fin n) 1) ∈ stdSpan F n (a + 2)

theorem map_stdSpan_le_of_basis (g : GLn F n) (j : ℕ) {X : Submodule F (Fin n → F)}
    (h : ∀ m : Fin n, m.val < j → g (Pi.single m 1) ∈ X) :
    Submodule.map (g : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n j) ≤ X := by
  rw [Submodule.map_le_iff_le_comap, stdSpan, Submodule.span_le]
  rintro _ ⟨⟨m, hm⟩, rfl⟩
  exact h m hm

theorem NearId.map_stdSpan {ha : a + 1 < n} {g : GLn F n} (hg : NearId ha g) {j : ℕ}
    (hj : j ≠ a + 1) (hjn : j ≤ n) :
    Submodule.map (g : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n j) = stdSpan F n j := by
  have hle : Submodule.map (g : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n j) ≤
      stdSpan F n j := by
    refine map_stdSpan_le_of_basis g j fun m hm => ?_
    by_cases hma : m.val = a
    · have : (⟨a, by omega⟩ : Fin n) = m := Fin.ext hma.symm
      rw [← this]
      exact stdSpan_mono F n (by omega) (hg.2.1)
    by_cases hma' : m.val = a + 1
    · have : (⟨a + 1, ha⟩ : Fin n) = m := Fin.ext hma'.symm
      rw [← this]
      exact stdSpan_mono F n (by omega) (hg.2.2)
    · rw [hg.1 m hma hma']
      exact (partial_single_mem_stdSpan F m).2 hm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [LinearEquiv.finrank_map_eq]

end Classif

section Elements

variable {n a : ℕ}

theorem ne_a (ha : a + 1 < n) : (⟨a + 1, ha⟩ : Fin n) ≠ ⟨a, by omega⟩ := by
  simp [Fin.ext_iff]

/-- `t_s = I + s E_{a+1,a}`. -/
def tA (ha : a + 1 < n) (s : F) : GLn F n := tvec ⟨a + 1, ha⟩ ⟨a, by omega⟩ (ne_a ha) s

/-- `u_s = I + s E_{a,a+1}`. -/
def uA (ha : a + 1 < n) (s : F) : GLn F n := tvec ⟨a, by omega⟩ ⟨a + 1, ha⟩ (ne_a ha).symm s

/-- The swap-like element `u₁ t₋₁ u₁`. -/
def mA (ha : a + 1 < n) : GLn F n := uA ha 1 * tA ha (-1) * uA ha 1

theorem single_mem_stdSpan_iff (m : Fin n) (j : ℕ) :
    (Pi.single m (1 : F) : Fin n → F) ∈ stdSpan F n j ↔ m.val < j :=
  partial_single_mem_stdSpan F m

theorem tA_nearId (ha : a + 1 < n) (s : F) : NearId ha (tA ha s) := by
  refine ⟨fun m hm hm' => ?_, ?_, ?_⟩
  · unfold tA
    refine tvec_single_of_ne _ _ _ _ _ ?_
    simpa [Fin.ext_iff] using hm
  · unfold tA
    rw [tvec_single_self]
    refine add_mem ((single_mem_stdSpan_iff _ _).2 (by simp)) (Submodule.smul_mem _ _
      ((single_mem_stdSpan_iff _ _).2 (by simp)))
  · unfold tA
    rw [tvec_single_of_ne _ _ _ _ _ (ne_a ha)]
    exact (single_mem_stdSpan_iff _ _).2 (by simp)

theorem uA_a (ha : a + 1 < n) (s : F) :
    uA ha s (Pi.single ⟨a, by omega⟩ 1) = Pi.single ⟨a, by omega⟩ (1 : F) :=
  tvec_single_of_ne _ _ _ _ _ (by simp [Fin.ext_iff])

theorem uA_a1 (ha : a + 1 < n) (s : F) :
    uA ha s (Pi.single ⟨a + 1, ha⟩ 1) =
      Pi.single ⟨a + 1, ha⟩ (1 : F) + s • Pi.single ⟨a, by omega⟩ (1 : F) :=
  tvec_single_self _ _ _ _

theorem tA_a (ha : a + 1 < n) (s : F) :
    tA ha s (Pi.single ⟨a, by omega⟩ 1) =
      Pi.single ⟨a, by omega⟩ (1 : F) + s • Pi.single ⟨a + 1, ha⟩ (1 : F) :=
  tvec_single_self _ _ _ _

theorem tA_a1 (ha : a + 1 < n) (s : F) :
    tA ha s (Pi.single ⟨a + 1, ha⟩ 1) = Pi.single ⟨a + 1, ha⟩ (1 : F) :=
  tvec_single_of_ne _ _ _ _ _ (ne_a ha)

theorem mA_single_a (ha : a + 1 < n) :
    mA ha (Pi.single ⟨a, by omega⟩ 1) = -(Pi.single ⟨a + 1, ha⟩ (1 : F)) := by
  unfold mA
  simp only [LinearEquiv.mul_apply]
  rw [uA_a, tA_a, map_add, map_smul, uA_a, uA_a1]
  simp

theorem mA_single_a1 (ha : a + 1 < n) :
    mA ha (Pi.single ⟨a + 1, ha⟩ 1) = (Pi.single ⟨a, by omega⟩ (1 : F)) := by
  unfold mA
  simp only [LinearEquiv.mul_apply]
  rw [uA_a1]
  simp only [map_add, map_smul, tA_a1, tA_a, uA_a1, uA_a, one_smul]
  module

theorem mA_nearId (ha : a + 1 < n) : NearId (F := F) ha (mA ha) := by
  refine ⟨fun m hm hm' => ?_, ?_, ?_⟩
  · unfold mA uA tA
    simp only [LinearEquiv.mul_apply]
    have h1 : m ≠ ⟨a, by omega⟩ := by simpa [Fin.ext_iff] using hm
    have h2 : m ≠ ⟨a + 1, ha⟩ := by simpa [Fin.ext_iff] using hm'
    rw [tvec_single_of_ne _ _ _ _ _ h2, tvec_single_of_ne _ _ _ _ _ h1,
      tvec_single_of_ne _ _ _ _ _ h2]
  · rw [mA_single_a]
    exact Submodule.neg_mem _ ((single_mem_stdSpan_iff _ _).2 (by simp))
  · rw [mA_single_a1]
    exact (single_mem_stdSpan_iff _ _).2 (by simp)

end Elements


section Classify

variable {n a : ℕ}

theorem sub_mem_stdSpan_a (ha : a + 1 < n) (y : Fin n → F) (hy : y ∈ stdSpan F n (a + 2)) :
    y - y ⟨a, by omega⟩ • (Pi.single ⟨a, by omega⟩ (1 : F) : Fin n → F) -
      y ⟨a + 1, ha⟩ • (Pi.single ⟨a + 1, ha⟩ (1 : F) : Fin n → F) ∈ stdSpan F n a := by
  rw [partial_mem_stdSpan] at hy ⊢
  intro j hj
  have hy' := hy j
  by_cases h0 : j.val = a
  · have : j = ⟨a, by omega⟩ := Fin.ext h0
    rw [this]
    simp [Pi.single_apply, Fin.ext_iff]
  by_cases h1 : j.val = a + 1
  · have : j = ⟨a + 1, ha⟩ := Fin.ext h1
    rw [this]
    simp [Pi.single_apply, Fin.ext_iff]
  · have : y j = 0 := hy' (by omega)
    have e0 : j ≠ ⟨a, by omega⟩ := fun h => h0 (by simp [h])
    have e1 : j ≠ ⟨a + 1, ha⟩ := fun h => h1 (by simp [h])
    simp [Pi.single_apply, this, e0, e1]

/-- Classification of the refinements: every `X` with `V_a ≤ X ≤ V_{a+2}` of dimension `a+1`
is the image of `V_{a+1}` under `t_s` or `m`. -/
theorem exists_nearId_map (ha : a + 1 < n) {X : Submodule F (Fin n → F)}
    (h1 : stdSpan F n a ≤ X) (h2 : X ≤ stdSpan F n (a + 2)) (h3 : finrank F X = a + 1) :
    (∃ s : F, Submodule.map (tA ha s : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n (a + 1)) = X) ∨
      Submodule.map (mA (F := F) ha : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n (a + 1)) = X := by
  have hfa : finrank F (stdSpan F n a) = a := finrank_stdSpan F n (by omega)
  have hfa1 : finrank F (stdSpan F n (a + 1)) = a + 1 := finrank_stdSpan F n (by omega)
  obtain ⟨v, hvX, hvA⟩ : ∃ v ∈ X, v ∉ stdSpan F n a := by
    by_contra hcon
    push_neg at hcon
    have := Submodule.finrank_mono (show X ≤ stdSpan F n a from hcon)
    omega
  have hv2 := (partial_mem_stdSpan F v).1 (h2 hvX)
  rw [partial_mem_stdSpan] at hvA
  push_neg at hvA
  obtain ⟨j, hj, hvj⟩ := hvA
  have hjn : j.val = a ∨ j.val = a + 1 := by
    by_contra hcon
    push_neg at hcon
    exact hvj (hv2 j (by omega))
  have hvi : v ⟨a, by omega⟩ ≠ 0 ∨ v ⟨a + 1, ha⟩ ≠ 0 := by
    rcases hjn with h | h
    · left; have : j = ⟨a, by omega⟩ := Fin.ext h
      rwa [← this]
    · right; have : j = ⟨a + 1, ha⟩ := Fin.ext h
      rwa [← this]
  by_cases hα : v ⟨a, by omega⟩ = 0
  · -- the swap-like case
    right
    have hβ : v ⟨a + 1, ha⟩ ≠ 0 := hvi.resolve_left (not_not.2 hα)
    set β := v ⟨a + 1, ha⟩
    have hy : β⁻¹ • v ∈ X := X.smul_mem _ hvX
    have hyz := sub_mem_stdSpan_a ha (β⁻¹ • v) ((stdSpan F n (a + 2)).smul_mem _ (h2 hvX))
    have hz := h1 hyz
    have he1 : (Pi.single ⟨a + 1, ha⟩ (1 : F) : Fin n → F) ∈ X := by
      have : (Pi.single ⟨a + 1, ha⟩ (1 : F) : Fin n → F) =
          β⁻¹ • v - ((β⁻¹ • v) - (β⁻¹ • v) ⟨a, by omega⟩ • (Pi.single ⟨a, by omega⟩ (1 : F) : Fin n → F)
            - (β⁻¹ • v) ⟨a + 1, ha⟩ • (Pi.single ⟨a + 1, ha⟩ (1 : F) : Fin n → F)) := by
        have hb : β⁻¹ * v ⟨a + 1, ha⟩ = 1 := inv_mul_cancel₀ hβ
        simp [hα, hb]
      rw [this]
      exact X.sub_mem hy hz
    have hle : Submodule.map (mA (F := F) ha : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n (a + 1)) ≤ X := by
      refine map_stdSpan_le_of_basis _ _ fun m hm => ?_
      by_cases hma : m.val = a
      · have : m = ⟨a, by omega⟩ := Fin.ext hma
        rw [this, mA_single_a]
        exact X.neg_mem he1
      · rw [(mA_nearId ha).1 m hma (by omega)]
        exact h1 ((single_mem_stdSpan_iff _ _).2 (by omega))
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearEquiv.finrank_map_eq, hfa1, h3]
  · left
    set α := v ⟨a, by omega⟩
    refine ⟨v ⟨a + 1, ha⟩ / α, ?_⟩
    have hy : α⁻¹ • v ∈ X := X.smul_mem _ hvX
    have hyz := sub_mem_stdSpan_a ha (α⁻¹ • v) ((stdSpan F n (a + 2)).smul_mem _ (h2 hvX))
    have hz := h1 hyz
    have he : (Pi.single ⟨a, by omega⟩ (1 : F) : Fin n → F) + (v ⟨a + 1, ha⟩ / α) •
        (Pi.single ⟨a + 1, ha⟩ (1 : F) : Fin n → F) ∈ X := by
      have : (Pi.single ⟨a, by omega⟩ (1 : F) : Fin n → F) + (v ⟨a + 1, ha⟩ / α) •
          (Pi.single ⟨a + 1, ha⟩ (1 : F) : Fin n → F) =
          α⁻¹ • v - ((α⁻¹ • v) - (α⁻¹ • v) ⟨a, by omega⟩ • (Pi.single ⟨a, by omega⟩ (1 : F) : Fin n → F)
            - (α⁻¹ • v) ⟨a + 1, ha⟩ • (Pi.single ⟨a + 1, ha⟩ (1 : F) : Fin n → F)) := by
        have hb : α⁻¹ * v ⟨a, by omega⟩ = 1 := inv_mul_cancel₀ hα
        simp [hb, div_eq_inv_mul]
        abel
      rw [this]
      exact X.sub_mem hy hz
    have hle : Submodule.map (tA ha (v ⟨a + 1, ha⟩ / α) : (Fin n → F) →ₗ[F] (Fin n → F))
        (stdSpan F n (a + 1)) ≤ X := by
      refine map_stdSpan_le_of_basis _ _ fun m hm => ?_
      by_cases hma : m.val = a
      · have : m = ⟨a, by omega⟩ := Fin.ext hma
        rw [this, tA_a]
        exact he
      · rw [(tA_nearId ha _).1 m hma (by omega)]
        exact h1 ((single_mem_stdSpan_iff _ _).2 (by omega))
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearEquiv.finrank_map_eq, hfa1, h3]

end Classify


section Std

variable {n : ℕ}

theorem mem_stdFlag_iff (A : Submodule F (Fin n → F)) :
    A ∈ (stdFlag F n).carrier ↔ ∃ j ≤ n, A = stdSpan F n j := by
  simp only [stdFlag, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

theorem stdSpan_mem_stdFlag {j : ℕ} (hj : j ≤ n) : stdSpan F n j ∈ (stdFlag F n).carrier :=
  (mem_stdFlag_iff _).2 ⟨j, hj, rfl⟩

theorem card_stdFlag : (stdFlag F n).carrier.card = n + 1 := by
  have h : (stdFlag F n).len = n := by
    have := bruhat_std_complete (F := F) n
    unfold Flag.IsComplete at this
    rwa [Module.finrank_fin_fun] at this
  have := (stdFlag F n).card_eq_len_succ
  omega

theorem index_stdFlag {i : ℕ} (hi : i ≤ n) : (stdFlag F n).index (stdSpan F n i) = i := by
  unfold Flag.index
  have : (stdFlag F n).carrier.filter (· < stdSpan F n i) =
      (Finset.range i).image (stdSpan F n) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, mem_stdFlag_iff]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hlt⟩
      exact ⟨j, (stdSpan_lt_iff F n hj hi).1 hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by omega, rfl⟩, (stdSpan_lt_iff F n (by omega) hi).2 hj⟩
  rw [this, Finset.card_image_of_injOn, Finset.card_range]
  intro x hx y hy hxy
  exact stdSpan_inj F n (by simp at hx; omega) (by simp at hy; omega) hxy

end Std


section Pigeon

theorem exists_finrank_mem {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Finset (Submodule F V)) (hS : IsChain (· ≤ ·) (S : Set (Submodule F V)))
    (hcard : S.card = finrank F V + 1) (d : ℕ) (hd : d ≤ finrank F V) :
    ∃ A ∈ S, finrank F A = d := by
  have hinj : Set.InjOn (fun A : Submodule F V => finrank F A) (S : Set (Submodule F V)) := by
    intro A hA B hB hAB
    by_cases hne : A = B
    · exact hne
    rcases hS hA hB hne with h | h
    · exact Submodule.eq_of_le_of_finrank_eq h hAB
    · exact (Submodule.eq_of_le_of_finrank_eq h hAB.symm).symm
  have hsub : S.image (fun A : Submodule F V => finrank F A) ⊆ Finset.range (finrank F V + 1) := by
    intro x hx
    obtain ⟨A, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Submodule.finrank_le A))
  have hcard' : (S.image (fun A : Submodule F V => finrank F A)).card = finrank F V + 1 := by
    rw [Finset.card_image_of_injOn hinj, hcard]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard']; simp)
  have hd' : d ∈ S.image (fun A : Submodule F V => finrank F A) := by
    rw [heq]; exact Finset.mem_range.2 (Nat.lt_succ_of_le hd)
  obtain ⟨A, hA, hAd⟩ := Finset.mem_image.1 hd'
  exact ⟨A, hA, hAd⟩

end Pigeon


section Refinement

variable {n a : ℕ}

theorem stdSpan_ne_zero_top (ha : a + 1 < n) :
    stdSpan F n (a + 1) ≠ ⊥ ∧ stdSpan F n (a + 1) ≠ ⊤ := by
  constructor
  · intro h
    rw [← stdSpan_zero F n] at h
    have := stdSpan_inj F n (by omega) (by omega) h
    omega
  · intro h
    rw [← stdSpan_top F n] at h
    have := stdSpan_inj F n (by omega) (by omega) h
    omega

/-- The codimension-one flag `H = F⁰ ∖ V_{a+1}`. -/
def holeFlag (ha : a + 1 < n) : Flag F (Fin n → F) :=
  (stdFlag F n).erase (stdSpan F n (a + 1)) (stdSpan_ne_zero_top ha)

theorem holeFlag_carrier (ha : a + 1 < n) :
    (holeFlag (F := F) ha).carrier = (stdFlag F n).carrier.erase (stdSpan F n (a + 1)) := rfl

theorem mem_holeFlag_iff (ha : a + 1 < n) (B : Submodule F (Fin n → F)) :
    B ∈ (holeFlag (F := F) ha).carrier ↔ ∃ j ≤ n, j ≠ a + 1 ∧ B = stdSpan F n j := by
  rw [holeFlag_carrier, Finset.mem_erase, mem_stdFlag_iff]
  constructor
  · rintro ⟨hne, j, hj, rfl⟩
    exact ⟨j, hj, fun h => hne (by rw [h]), rfl⟩
  · rintro ⟨j, hj, hj1, rfl⟩
    refine ⟨fun h => hj1 ?_, j, hj, rfl⟩
    exact stdSpan_inj F n hj (by omega) h

theorem stdFlag_directlyRefines_hole (ha : a + 1 < n) :
    (holeFlag (F := F) ha).DirectlyRefines (stdFlag F n) := by
  refine ⟨Finset.erase_subset _ _, ?_⟩
  have h1 := (holeFlag (F := F) ha).card_eq_len_succ
  have h2 := (stdFlag F n).card_eq_len_succ
  rw [holeFlag_carrier, Finset.card_erase_of_mem (stdSpan_mem_stdFlag (by omega)),
    card_stdFlag] at h1
  rw [card_stdFlag] at h2
  omega

/-- Every direct refinement of `H` is `p F⁰` for some `p ∈ P`, with new member at index `a+1`. -/
theorem refinement_eq_smul (ha : a + 1 < n) {P : Subgroup (GLn F n)}
    (ht : ∀ s, tA ha s ∈ P) (hm : mA ha ∈ P) {G : Flag F (Fin n → F)}
    (hDR : (holeFlag (F := F) ha).DirectlyRefines G) :
    ∃ p ∈ P, G = p • stdFlag F n ∧
      G.index ((holeFlag (F := F) ha).newMember G) = a + 1 := by
  obtain ⟨hA, hGe, hAG⟩ := Flag.dr_erase _ G hDR
  set A := (holeFlag (F := F) ha).newMember G with hAdef
  have hHc : (holeFlag (F := F) ha).carrier = G.carrier.erase A := by
    rw [← hGe]; rfl
  have hcar : G.carrier = insert A (holeFlag (F := F) ha).carrier := by
    rw [hHc, Finset.insert_erase hAG]
  have hAH : A ∉ (holeFlag (F := F) ha).carrier := by
    rw [hHc]; exact Finset.notMem_erase _ _
  have hcardH : (holeFlag (F := F) ha).carrier.card = n := by
    rw [holeFlag_carrier, Finset.card_erase_of_mem (stdSpan_mem_stdFlag (by omega)),
      card_stdFlag]; rfl
  have hcardG : G.carrier.card = finrank F (Fin n → F) + 1 := by
    rw [hcar, Finset.card_insert_of_notMem hAH, hcardH, Module.finrank_fin_fun]
  obtain ⟨B, hBG, hBd⟩ := exists_finrank_mem G.carrier G.isChain hcardG (a + 1)
    (by rw [Module.finrank_fin_fun]; omega)
  have hBA : B = A := by
    rw [hcar, Finset.mem_insert] at hBG
    rcases hBG with h | h
    · exact h
    · obtain ⟨j, hj, hj1, rfl⟩ := (mem_holeFlag_iff ha B).1 h
      rw [finrank_stdSpan F n hj] at hBd
      exact absurd hBd hj1
  have hfA : finrank F A = a + 1 := hBA ▸ hBd
  have hAG' : A ∈ G.carrier := hAG
  have hVa : stdSpan F n a ∈ G.carrier := by
    rw [hcar]
    exact Finset.mem_insert_of_mem ((mem_holeFlag_iff ha _).2 ⟨a, by omega, by omega, rfl⟩)
  have hVa2 : stdSpan F n (a + 2) ∈ G.carrier := by
    rw [hcar]
    exact Finset.mem_insert_of_mem ((mem_holeFlag_iff ha _).2 ⟨a + 2, by omega, by omega, rfl⟩)
  have hle1 : stdSpan F n a ≤ A := by
    by_cases heq : stdSpan F n a = A
    · exact heq.le
    rcases G.isChain hVa hAG' heq with h | h
    · exact h
    · have := Submodule.finrank_mono h
      rw [hfA, finrank_stdSpan F n (by omega)] at this
      omega
  have hle2 : A ≤ stdSpan F n (a + 2) := by
    by_cases heq : A = stdSpan F n (a + 2)
    · exact heq.le
    rcases G.isChain hAG' hVa2 heq with h | h
    · exact h
    · have := Submodule.finrank_mono h
      rw [hfA, finrank_stdSpan F n (by omega)] at this
      omega
  have hp : ∃ p : GLn F n, p ∈ P ∧ NearId ha p ∧
      Submodule.map (p : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n (a + 1)) = A := by
    rcases exists_nearId_map ha hle1 hle2 hfA with ⟨s, hs⟩ | hs
    · exact ⟨tA ha s, ht s, tA_nearId ha s, hs⟩
    · exact ⟨mA ha, hm, mA_nearId ha, hs⟩
  obtain ⟨p, hpP, hpN, hpA⟩ := hp
  have hG : G = p • stdFlag F n := by
    apply Flag.ext
    ext B
    show B ∈ G.carrier ↔ B ∈ (stdFlag F n).carrier.image (Submodule.map (p : (Fin n → F) →ₗ[F] (Fin n → F)))
    rw [hcar, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (rfl | hB)
      · exact ⟨stdSpan F n (a + 1), stdSpan_mem_stdFlag (by omega), hpA⟩
      · obtain ⟨j, hj, hj1, rfl⟩ := (mem_holeFlag_iff ha B).1 hB
        exact ⟨stdSpan F n j, stdSpan_mem_stdFlag hj, hpN.map_stdSpan hj1 hj⟩
    · rintro ⟨C, hC, rfl⟩
      obtain ⟨j, hj, rfl⟩ := (mem_stdFlag_iff C).1 hC
      by_cases hj1 : j = a + 1
      · subst hj1; left; exact hpA
      · right
        rw [hpN.map_stdSpan hj1 hj]
        exact (mem_holeFlag_iff ha _).2 ⟨j, hj, hj1, rfl⟩
  refine ⟨p, hpP, hG, ?_⟩
  have hidx : (p • stdFlag F n).index
      (Submodule.map (p : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n (a + 1))) = a + 1 := by
    have := Flag.index_map (p : (Fin n → F) ≃ₗ[F] (Fin n → F)) (stdFlag F n)
      (stdSpan_mem_stdFlag (n := n) (F := F) (j := a + 1) (by omega))
    rw [index_stdFlag (by omega)] at this
    exact this
  show G.index A = a + 1
  rw [← hpA, hG]
  exact hidx

end Refinement


section Key

variable {n a : ℕ}

/-- If `P` contains `t_s` for all `s` and `m`, a `P`-fixed vector of `Stₙ` vanishes at `F⁰`. -/
theorem fixed_vanishes_std [CharZero k] (ha : a + 1 < n) {P : Subgroup (GLn F n)}
    (ht : ∀ s, tA ha s ∈ P) (hm : mA ha ∈ P) (w : steinberg F k n)
    (hw : ∀ p ∈ P, stAct F k p w = w) : (w : FlagModule F k n) (stdFlag F n) = 0 := by
  have hconst : ∀ p ∈ P, (w : FlagModule F k n) (p • stdFlag F n) = (w : FlagModule F k n)
      (stdFlag F n) := by
    intro p hp
    have h1 : flagRep F k n p (w : FlagModule F k n) = (w : FlagModule F k n) :=
      congrArg Subtype.val (hw p hp)
    calc (w : FlagModule F k n) (p • stdFlag F n)
        = flagRep F k n p (w : FlagModule F k n) (p • stdFlag F n) := by rw [h1]
      _ = _ := flagRep_apply_smul p _ _
  have hbd : chainBoundary F k n (w : FlagModule F k n) = 0 := LinearMap.mem_ker.1 w.2.2
  have h0 := congrArg (fun f : FlagModule F k n => f (holeFlag (F := F) ha)) hbd
  simp only [bd_apply, Finsupp.coe_zero, Pi.zero_apply] at h0
  have hterm : ∀ G : Flag F (Fin n → F), (w : FlagModule F k n) G *
      sigmaCoef F k (holeFlag (F := F) ha) G =
      if (holeFlag (F := F) ha).DirectlyRefines G then
        (-1 : k) ^ (a + 1) * (w : FlagModule F k n) (stdFlag F n) else 0 := by
    intro G
    unfold sigmaCoef
    by_cases h : (holeFlag (F := F) ha).DirectlyRefines G
    · rw [if_pos h, if_pos h]
      obtain ⟨p, hp, hG, hi⟩ := refinement_eq_smul ha ht hm h
      have : (w : FlagModule F k n) G = (w : FlagModule F k n) (stdFlag F n) := by
        rw [hG]; exact hconst p hp
      rw [this, hi, mul_comm]
    · simp [h]
  simp only [hterm] at h0
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at h0
  have hpos : 0 < (Finset.univ.filter fun G : Flag F (Fin n → F) =>
      (holeFlag (F := F) ha).DirectlyRefines G).card :=
    Finset.card_pos.2 ⟨stdFlag F n, by simpa using stdFlag_directlyRefines_hole ha⟩
  have hc : ((Finset.univ.filter fun G : Flag F (Fin n → F) =>
      (holeFlag (F := F) ha).DirectlyRefines G).card : k) ≠ 0 := by exact_mod_cast hpos.ne'
  have hs : (-1 : k) ^ (a + 1) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h hc
  · exact (mul_eq_zero.1 h).resolve_left hs

end Key


end MartinPhd

end
end StParZero

section TransvectionP

/-!
## Lower Transvections in Parabolic Subgroups

Lemma 1.23 in the thesis of F. D. Martin: A subgroup `P ≤ GL(n, F)` containing the Borel
subgroup `B` and an element `g ∉ B` contains all adjacent lower transvections
`I + s E_{a+1, a}` for some index `a`.
-/

open Module
noncomputable section
namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F]

theorem mem_borel_of_maps_stdSpan {n : ℕ} (g : GLn F n)
    (h : ∀ d ≤ n, ∀ x ∈ stdSpan F n d, g x ∈ stdSpan F n d) :
    g ∈ borel F n := by
  have hf (d : ℕ) (hd : d ≤ n) : (stdSpan F n d).map g.toLinearMap = stdSpan F n d := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      exact h d hd x hx
    · exact LinearEquiv.finrank_map_eq _ _
  change (stdFlag F n).map g = stdFlag F n
  apply Flag.ext
  have hm : ∀ A ∈ (stdFlag F n).carrier, A.map g.toLinearMap = A := by
    intro A hA
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hA
    exact hf d (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))
  exact (Finset.image_congr (g := id) hm).trans Finset.image_id

theorem tvec_mem_borel {n : ℕ} (i j : Fin n) (h : i < j) (s : F) :
    tvec i j h.ne s ∈ borel F n := by
  apply mem_borel_of_maps_stdSpan
  intro d hd x hx
  rw [partial_mem_stdSpan] at hx ⊢
  intro m hm
  rw [tvec_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hx m hm, zero_add]
  by_cases hmi : m = i
  · subst hmi
    have hj : d ≤ j.val := by omega
    simp [hx j hj]
  · simp [hmi]

theorem tvec_inv {n : ℕ} (i j : Fin n) (h : i ≠ j) (s : F) :
    (tvec i j h s)⁻¹ = tvec i j h (-s) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tvec_mul, add_neg_cancel, tvec_zero]

theorem tvec_commutator {n : ℕ} (i j k : Fin n)
    (h1 : i ≠ k) (h2 : k ≠ j) (h3 : i ≠ j) (x y : F) :
    tvec i k h1 x * tvec k j h2 y * (tvec i k h1 x)⁻¹ * (tvec k j h2 y)⁻¹ =
      tvec i j h3 (x * y) := by
  rw [tvec_inv, tvec_inv]
  refine LinearEquiv.ext fun v => funext fun m => ?_
  simp only [LinearEquiv.mul_apply, tvec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne m i with rfl | hmi
  · simp [h1.symm, h3.symm, h2.symm]
    ring
  · rcases eq_or_ne m k with rfl | hmk
    · simp [hmi, h2.symm, h3.symm]
    · simp [hmi, hmk]

theorem permToGL_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → F) (m : Fin n) :
    permToGL F σ v m = v (σ.symm m) := rfl

theorem permToGL_symm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → F) (m : Fin n) :
    (permToGL F σ)⁻¹ v m = v (σ m) := rfl

theorem permToGL_one {n : ℕ} : permToGL F (1 : Equiv.Perm (Fin n)) = 1 := by
  refine LinearEquiv.ext fun v => funext fun m => ?_
  simp [permToGL_apply]
  rfl

theorem permToGL_conj_tvec {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n)
    (h : i ≠ j) (s : F) :
    permToGL F σ * tvec i j h s * (permToGL F σ)⁻¹ =
      tvec (σ i) (σ j) (σ.injective.ne h) s := by
  refine LinearEquiv.ext fun v => funext fun m => ?_
  simp only [LinearEquiv.mul_apply, permToGL_apply, permToGL_symm_apply,
    tvec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Equiv.apply_symm_apply]
  by_cases hm : m = σ i
  · subst hm
    simp
  · simp [hm, show σ.symm m ≠ i by intro he; exact hm (by rw [← he, Equiv.apply_symm_apply])]

def diagMap {n : ℕ} (c : Fin n) (u : F) : (Fin n → F) →ₗ[F] (Fin n → F) where
  toFun v k := if k = c then u * v k else v k
  map_add' v w := by
    ext k
    by_cases hk : k = c <;> simp [hk, mul_add]
  map_smul' a v := by
    ext k
    by_cases hk : k = c <;> simp [hk, mul_left_comm]

theorem diagMap_mul {n : ℕ} (c : Fin n) (u u' : F) :
    diagMap c u ∘ₗ diagMap c u' = diagMap (n := n) c (u * u') := by
  ext v k
  by_cases hk : k = c <;> simp [diagMap, hk, mul_assoc]

theorem diagMap_one {n : ℕ} (c : Fin n) : diagMap c (1 : F) = LinearMap.id := by
  ext v k
  by_cases hk : k = c <;> simp [diagMap, hk]

def diagScale {n : ℕ} (c : Fin n) (u : F) (hu : u ≠ 0) : GLn F n :=
  LinearEquiv.ofLinearMap (diagMap c u) (diagMap c u⁻¹)
    (by rw [diagMap_mul, mul_inv_cancel₀ hu, diagMap_one])
    (by rw [diagMap_mul, inv_mul_cancel₀ hu, diagMap_one])

theorem diagScale_apply {n : ℕ} (c : Fin n) (u : F) (hu : u ≠ 0) (v : Fin n → F) (k : Fin n) :
    diagScale c u hu v k = if k = c then u * v k else v k := rfl

theorem diagScale_symm_apply {n : ℕ} (c : Fin n) (u : F) (hu : u ≠ 0) (v : Fin n → F) (k : Fin n) :
    (diagScale c u hu)⁻¹ v k = if k = c then u⁻¹ * v k else v k := rfl

theorem diagScale_mem_borel {n : ℕ} (c : Fin n) (u : F) (hu : u ≠ 0) :
    diagScale c u hu ∈ borel F n := by
  apply mem_borel_of_maps_stdSpan
  intro d hd x hx
  rw [partial_mem_stdSpan] at hx ⊢
  intro m hm
  rw [diagScale_apply]
  rcases eq_or_ne m c with rfl | hmc
  · simp [hx m hm]
  · simp [hmc, hx m hm]

theorem diagScale_conj_tvec {n : ℕ} (b c : Fin n) (h : b ≠ c) (u : F) (hu : u ≠ 0) :
    diagScale b u hu * tvec b c h 1 * (diagScale b u hu)⁻¹ = tvec b c h u := by
  refine LinearEquiv.ext fun v => funext fun m => ?_
  simp only [LinearEquiv.mul_apply, diagScale_apply, diagScale_symm_apply,
    tvec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne m b with rfl | hmb
  · simp only [ite_true, ite_false, h.symm]
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    ring
  · simp [hmb]

theorem tvec_all_scalars_of_one {n : ℕ} {P : Subgroup (GLn F n)}
    (hP : borel F n ≤ P) (b c : Fin n) (h : b ≠ c)
    (h1 : tvec b c h 1 ∈ P) (u : F) :
    tvec b c h u ∈ P := by
  by_cases hu : u = 0
  · subst hu
    rw [tvec_zero]
    exact P.one_mem
  · rw [← diagScale_conj_tvec b c h u hu]
    have hd : diagScale b u hu ∈ P := hP (diagScale_mem_borel b u hu)
    exact P.mul_mem (P.mul_mem hd h1) (P.inv_mem hd)

theorem tvec_descent_aux {n : ℕ} {P : Subgroup (GLn F n)} (hP : borel F n ≤ P) :
    ∀ (k : ℕ) (b c : Fin n) (hc : c < b), b.val - c.val = k →
      tvec b c hc.ne' 1 ∈ P →
      ∃ (a : ℕ) (ha : a + 1 < n), ∀ x : F,
        tvec ⟨a + 1, ha⟩ ⟨a, by omega⟩ (by simp [Fin.ext_iff]) x ∈ P := by
  intro k
  induction' k using Nat.strong_induction_on with k ih
  intro b c hc hk h1
  by_cases hstep : b.val = c.val + 1
  · refine ⟨c.val, by omega, ?_⟩
    intro x
    have heq : tvec ⟨c.val + 1, by omega⟩ ⟨c.val, by omega⟩ (by simp [Fin.ext_iff]) x =
        tvec b c hc.ne' x := by
      refine LinearEquiv.ext fun v => funext fun m => ?_
      simp only [tvec_apply]
      have hb : b = ⟨c.val + 1, by omega⟩ := Fin.ext (by omega)
      have hc' : c = ⟨c.val, by omega⟩ := Fin.ext rfl
      rw [← hb, ← hc']
    rw [heq]
    exact tvec_all_scalars_of_one hP b c hc.ne' h1 x
  · have hgt : b.val ≥ c.val + 2 := by omega
    let b' : Fin n := ⟨b.val - 1, by omega⟩
    have hb'b : b' < b := by
      show b'.val < b.val
      dsimp [b']; omega
    have hcb' : c < b' := by
      show c.val < b'.val
      dsimp [b']; omega
    have hbb'_mem : tvec b' b hb'b.ne 1 ∈ P :=
      hP (tvec_mem_borel b' b hb'b 1)
    have hcom := tvec_commutator b' c b hb'b.ne hc.ne' hcb'.ne' (1 : F) (1 : F)
    rw [mul_one] at hcom
    have hcom_mem : tvec b' c hcb'.ne' 1 ∈ P := by
      rw [← hcom]
      exact P.mul_mem (P.mul_mem (P.mul_mem hbb'_mem h1) (P.inv_mem hbb'_mem)) (P.inv_mem h1)
    have hk' : b'.val - c.val < k := by
      dsimp [b']; omega
    exact ih (b'.val - c.val) hk' b' c hcb' rfl hcom_mem

theorem tvec_descent {n : ℕ} {P : Subgroup (GLn F n)} (hP : borel F n ≤ P)
    (b c : Fin n) (hc : c < b) (h1 : tvec b c hc.ne' 1 ∈ P) :
    ∃ (a : ℕ) (ha : a + 1 < n), ∀ x : F,
      tvec ⟨a + 1, ha⟩ ⟨a, by omega⟩ (by simp [Fin.ext_iff]) x ∈ P :=
  tvec_descent_aux hP (b.val - c.val) b c hc rfl h1

theorem exists_inversion_of_ne_one {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
    ∃ (i j : Fin n), i < j ∧ σ j < σ i := by
  by_contra h
  have hle (a b : Fin n) (hab : a < b) : σ a ≤ σ b := by
    by_contra hlt
    exact h ⟨a, b, hab, not_le.mp hlt⟩
  have hmono : StrictMono σ := fun a b hab =>
    lt_of_le_of_ne (hle a b hab) (σ.injective.ne hab.ne)
  have hid : (σ : Fin n → Fin n) = id := hmono.eq_id
  have h1 : σ = 1 := Equiv.ext (fun x => congr_fun hid x)
  exact hσ h1

theorem exists_adjacent_tvec [Fintype F] {n : ℕ} {P : Subgroup (GLn F n)}
    (hP : borel F n ≤ P) (g : GLn F n) (hgP : g ∈ P) (hgB : g ∉ borel F n) :
    ∃ (a : ℕ) (ha : a + 1 < n), ∀ s : F,
      tvec ⟨a + 1, ha⟩ ⟨a, by omega⟩ (by simp [Fin.ext_iff]) s ∈ P := by
  let σ := jh n (stdFlag F n) (g • stdFlag F n)
  have hσP : permToGL F σ ∈ P := (subgroup_mem_iff_bruhat_perm F P hP g).1 hgP
  have hσ_ne : σ ≠ 1 := by
    intro h1
    have hg_dc : g ∈ bruhatDC (permToGL F σ) := by
      rw [bruhatDC_mem_iff, jh_std_perm]
    rw [h1, permToGL_one] at hg_dc
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg_dc
    have hmem : b₁ * 1 * b₂ ∈ borel F n := by
      rw [mul_one]
      exact (borel F n).mul_mem hb₁ hb₂
    exact hgB hmem
  obtain ⟨i, j, hij, hσji⟩ := exists_inversion_of_ne_one σ hσ_ne
  have hi_P : tvec i j hij.ne 1 ∈ P := hP (tvec_mem_borel i j hij 1)
  have h_conj_mem : tvec (σ i) (σ j) (σ.injective.ne hij.ne) 1 ∈ P := by
    rw [← permToGL_conj_tvec σ i j hij.ne 1]
    exact P.mul_mem (P.mul_mem hσP hi_P) (P.inv_mem hσP)
  exact tvec_descent hP (σ i) (σ j) hσji h_conj_mem

end MartinPhd

end
end TransvectionP

section StParGlue

/-!
## Lemma 1.23 (assembly)

`dim St^B = 1` (`finrank_stFixed_borel`) and `St^P = 0` for every subgroup `P ⊋ B`
(from `fixed_vanishes_std`).
-/

open Module
noncomputable section
namespace MartinPhd

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

theorem stFixed_eq_bot_of_gt [CharZero k] {n : ℕ} {P : Subgroup (GLn F n)}
    (hP : borel F n < P) : stFixed F k P = ⊥ := by
  obtain ⟨g, hgP, hgB⟩ := SetLike.exists_of_lt hP
  obtain ⟨a, ha, hts⟩ := exists_adjacent_tvec hP.le g hgP hgB
  have ht : ∀ s, tA ha s ∈ P := hts
  have hu : uA (F := F) ha 1 ∈ P :=
    hP.le (tvec_mem_borel _ _ (by simp [Fin.lt_def]) _)
  have hm : mA (F := F) ha ∈ P := P.mul_mem (P.mul_mem hu (ht (-1))) hu
  rcases stFixed_eq_bot_or_borel (k := k) hP.le with h | h
  · exact h
  · exfalso
    obtain ⟨v, hv, hv0⟩ := exists_borel_fixed_std (F := F) (k := k) (n := n) (by omega)
    have hvP : v ∈ stFixed F k P := by rw [h]; exact hv
    exact hv0 (fixed_vanishes_std ha ht hm v hvP)

/-- **Lemma 1.23.** `dim St^B = 1`, and `St^P = 0` for every parabolic `P ⊋ B`. -/
theorem lemma_1_23 [CharZero k] (n : ℕ) :
    finrank k (stFixed F k (borel F n)) = 1 ∧
    ∀ P : Subgroup (GLn F n), borel F n < P → stFixed F k P = ⊥ :=
  ⟨finrank_stFixed_borel n, fun _ hP => stFixed_eq_bot_of_gt hP⟩

end MartinPhd

end
end StParGlue

section TransvectionI

/-!
## Interval Transvections in Parabolic Subgroups

Lemma 1.23 helper in the thesis of F. D. Martin: A subgroup `P ≤ GL(n, F)` containing the Borel
subgroup `B` and a lower transvection `tvec b c 1 ∈ P` contains all transvections
`tvec b' c' x` in the interval `c ≤ c' < b' ≤ b`.
-/

open Module
noncomputable section
namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F]

omit [Fintype F]

lemma tvec_lower_top {n : ℕ} {P : Subgroup (GLn F n)} (hP : borel F n ≤ P)
    (c : Fin n) :
    ∀ (k : ℕ) (b : Fin n) (hcb : c < b), tvec b c hcb.ne' 1 ∈ P →
      ∀ (b' : Fin n) (hcb' : c < b'), b' ≤ b → b.val - b'.val = k →
      tvec b' c hcb'.ne' 1 ∈ P := by
  intro k
  induction' k with k ih
  · intro b hcb h1 b' hcb' hb'b hk
    have heq : b' = b := by
      ext
      omega
    subst heq
    exact h1
  · intro b hcb h1 b' hcb' hb'b hk
    have hgt : b.val ≥ c.val + 2 := by omega
    let b1 : Fin n := ⟨b.val - 1, by omega⟩
    have hb1b : b1 < b := by
      show b1.val < b.val
      dsimp [b1]; omega
    have hcb1 : c < b1 := by
      show c.val < b1.val
      dsimp [b1]; omega
    have hb1b_mem : tvec b1 b hb1b.ne 1 ∈ P :=
      hP (tvec_mem_borel b1 b hb1b 1)
    have hcom := tvec_commutator b1 c b hb1b.ne hcb.ne' hcb1.ne' (1 : F) (1 : F)
    rw [mul_one] at hcom
    have hcom_mem : tvec b1 c hcb1.ne' 1 ∈ P := by
      rw [← hcom]
      exact P.mul_mem (P.mul_mem (P.mul_mem hb1b_mem h1) (P.inv_mem hb1b_mem)) (P.inv_mem h1)
    have hb'b1 : b' ≤ b1 := by
      show b'.val ≤ b1.val
      dsimp [b1]; omega
    have hk1 : b1.val - b'.val = k := by
      dsimp [b1]; omega
    exact ih b1 hcb1 hcom_mem b' hcb' hb'b1 hk1

lemma tvec_raise_bottom {n : ℕ} {P : Subgroup (GLn F n)} (hP : borel F n ≤ P)
    (b' : Fin n) :
    ∀ (k : ℕ) (c : Fin n) (hcb' : c < b'), tvec b' c hcb'.ne' 1 ∈ P →
      ∀ (c' : Fin n) (hc'b' : c' < b'), c ≤ c' → c'.val - c.val = k →
      tvec b' c' hc'b'.ne' 1 ∈ P := by
  intro k
  induction' k with k ih
  · intro c hcb' h1 c' hc'b' hcc' hk
    have heq : c' = c := by
      ext
      omega
    subst heq
    exact h1
  · intro c hcb' h1 c' hc'b' hcc' hk
    have hgt : c.val + 1 < b'.val := by omega
    let c1 : Fin n := ⟨c.val + 1, by omega⟩
    have hcc1 : c < c1 := by
      show c.val < c1.val
      dsimp [c1]; omega
    have hc1b' : c1 < b' := by
      show c1.val < b'.val
      dsimp [c1]; omega
    have hcc1_mem : tvec c c1 hcc1.ne 1 ∈ P :=
      hP (tvec_mem_borel c c1 hcc1 1)
    have hcom := tvec_commutator b' c1 c hcb'.ne' hcc1.ne hc1b'.ne' (1 : F) (1 : F)
    rw [mul_one] at hcom
    have hcom_mem : tvec b' c1 hc1b'.ne' 1 ∈ P := by
      rw [← hcom]
      exact P.mul_mem (P.mul_mem (P.mul_mem h1 hcc1_mem) (P.inv_mem h1)) (P.inv_mem hcc1_mem)
    have hc1c' : c1 ≤ c' := by
      show c1.val ≤ c'.val
      dsimp [c1]; omega
    have hk1 : c'.val - c1.val = k := by
      dsimp [c1]; omega
    exact ih c1 hc1b' hcom_mem c' hc'b' hc1c' hk1

theorem tvec_interval {n : ℕ} {P : Subgroup (GLn F n)} (hP : borel F n ≤ P)
    (b c : Fin n) (hcb : c < b) (h1 : tvec b c hcb.ne' 1 ∈ P)
    (b' c' : Fin n) (hc : c ≤ c') (hcb' : c' < b') (hb : b' ≤ b) (x : F) :
    tvec b' c' hcb'.ne' x ∈ P := by
  have hcb'0 : c < b' := lt_of_le_of_lt hc hcb'
  have h_top : tvec b' c hcb'0.ne' 1 ∈ P :=
    tvec_lower_top hP c (b.val - b'.val) b hcb h1 b' hcb'0 hb rfl
  have h_bot : tvec b' c' hcb'.ne' 1 ∈ P :=
    tvec_raise_bottom hP b' (c'.val - c.val) c hcb'0 h_top c' hcb' hc rfl
  exact tvec_all_scalars_of_one hP b' c' hcb'.ne' h_bot x

theorem tvec_adjacent_of_interval {n : ℕ} {P : Subgroup (GLn F n)} (hP : borel F n ≤ P)
    (b c : Fin n) (hcb : c < b) (h1 : tvec b c hcb.ne' 1 ∈ P) (a : ℕ) (ha : a + 1 < n)
    (hca : c.val ≤ a) (hab : a + 1 ≤ b.val) (x : F) :
    tvec ⟨a + 1, ha⟩ ⟨a, by omega⟩ (by simp [Fin.ext_iff]) x ∈ P := by
  have hc' : c ≤ ⟨a, by omega⟩ := by
    show c.val ≤ a
    exact hca
  have hcb' : (⟨a, by omega⟩ : Fin n) < ⟨a + 1, ha⟩ := by
    show a < a + 1
    omega
  have hb' : (⟨a + 1, ha⟩ : Fin n) ≤ b := by
    show a + 1 ≤ b.val
    exact hab
  exact tvec_interval hP b c hcb h1 ⟨a + 1, ha⟩ ⟨a, by omega⟩ hc' hcb' hb' x

end MartinPhd

end
end TransvectionI

section Lemma113

/-!
## Lemma 1.13, surjectivity (every `P ⊇ B` is a standard parabolic)

Following the thesis (after [Igu, Thm 16.5]): let `c` be the finest composition whose standard
flag `P` stabilizes. Then `P ⊆ Stab F^{0,c}`. Conversely, if `a, a+1` are in one block of `c`,
`P` does not preserve `V_{a+1}`; the Bruhat permutation of an element moving `V_{a+1}` has an
inversion crossing `a+1`, which produces (by the commutator argument for transvections) all
`I + sE_{a+1,a}` in `P`, hence the transposition `(a a+1)`. The Young subgroup is generated by such
transpositions, and `Stab F^{0,c} = ⋃_{σ ∈ Y_c} BσB` (Lemma 1.16).
-/

open Module
noncomputable section
namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F]

theorem borel_map_stdSpan {n : ℕ} {b : GLn F n} (hb : b ∈ borel F n) {m : ℕ} (hm : m ≤ n) :
    Submodule.map (b : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n m) = stdSpan F n m :=
  Flag.fix_of_smul_eq hb (stdSpan_mem_stdFlag hm)

theorem map_mul_stdSpan {n : ℕ} {g h : GLn F n} {m : ℕ}
    (hg : Submodule.map (g : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n m) = stdSpan F n m)
    (hh : Submodule.map (h : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n m) = stdSpan F n m) :
    Submodule.map ((g * h : GLn F n) : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n m) =
      stdSpan F n m := by
  have : ((g * h : GLn F n) : (Fin n → F) →ₗ[F] (Fin n → F)) =
      (g : (Fin n → F) →ₗ[F] (Fin n → F)) ∘ₗ (h : (Fin n → F) →ₗ[F] (Fin n → F)) := rfl
  rw [this, Submodule.map_comp, hh, hg]

theorem permToGL_map_stdSpan {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : m ≤ n)
    (h : ∀ i : Fin n, i.val < m → (σ i).val < m) :
    Submodule.map (permToGL F σ : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n m) =
      stdSpan F n m := by
  have hle : Submodule.map (permToGL F σ : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n m) ≤
      stdSpan F n m := by
    refine map_stdSpan_le_of_basis _ _ fun i hi => ?_
    show permToGL F σ (Pi.single i 1) ∈ _
    rw [permToGL_single]
    exact (single_mem_stdSpan_iff _ _).2 (h i hi)
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq _ _)

/-- If an element of `P ⊇ B` moves `V_m`, some permutation matrix in `P` sends a point
below `m` to a point `≥ m`. -/
theorem exists_perm_cross {n : ℕ} {P : Subgroup (GLn F n)} (hP : borel F n ≤ P)
    {g : GLn F n} (hg : g ∈ P) {m : ℕ} (hm : m ≤ n)
    (hmove : Submodule.map (g : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n m) ≠
      stdSpan F n m) :
    ∃ σ : Equiv.Perm (Fin n), permToGL F σ ∈ P ∧ ∃ i : Fin n, i.val < m ∧ m ≤ (σ i).val := by
  set σ := jh n (stdFlag F n) (g • stdFlag F n) with hσ
  have hσP : permToGL F σ ∈ P := (subgroup_mem_iff_bruhat_perm F P hP g).1 hg
  refine ⟨σ, hσP, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hpres := permToGL_map_stdSpan (F := F) σ hm (fun i hi => hcon i hi)
  have hg_dc : g ∈ bruhatDC (permToGL F σ) := by
    rw [bruhatDC_mem_iff, jh_std_perm]
  obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hg_dc
  apply hmove
  rw [he]
  exact map_mul_stdSpan (map_mul_stdSpan (borel_map_stdSpan hb₁ hm) hpres)
    (borel_map_stdSpan hb₂ hm)

theorem diagScale_single {n : ℕ} (c i : Fin n) (u : F) (hu : u ≠ 0) :
    diagScale c u hu (Pi.single i 1) = if i = c then u • (Pi.single i (1 : F) : Fin n → F)
      else Pi.single i 1 := by
  funext k
  rw [diagScale_apply]
  by_cases hk : k = c <;> by_cases hi : i = c <;> by_cases hki : k = i <;>
    simp [hk, hi, hki, Pi.single_apply] <;> subst_vars <;> simp_all

/-- The permutation matrix of the adjacent transposition is `m · diag(-1)`. -/
theorem permToGL_swap_eq {n a : ℕ} (ha : a + 1 < n) :
    permToGL F (Equiv.swap (⟨a, by omega⟩ : Fin n) ⟨a + 1, ha⟩) =
      mA ha * diagScale (⟨a, by omega⟩ : Fin n) (-1) (neg_ne_zero.2 one_ne_zero) := by
  apply LinearEquiv.toLinearMap_injective
  refine (Pi.basisFun F (Fin n)).ext fun i => ?_
  simp only [Pi.basisFun_apply]
  show permToGL F _ (Pi.single i 1) = mA ha (diagScale _ (-1) _ (Pi.single i 1))
  rw [permToGL_single, diagScale_single]
  by_cases h0 : i.val = a
  · have : i = ⟨a, by omega⟩ := Fin.ext h0
    rw [this]
    simp only [if_true, map_smul, mA_single_a, Equiv.swap_apply_left]
    simp
  by_cases h1 : i.val = a + 1
  · have : i = ⟨a + 1, ha⟩ := Fin.ext h1
    rw [this]
    have hne : (⟨a + 1, ha⟩ : Fin n) ≠ ⟨a, by omega⟩ := ne_a ha
    simp [hne, mA_single_a1]
  · have e0 : i ≠ ⟨a, by omega⟩ := fun h => h0 (by simp [h])
    have e1 : i ≠ ⟨a + 1, ha⟩ := fun h => h1 (by simp [h])
    rw [Equiv.swap_apply_of_ne_of_ne e0 e1, if_neg e0]
    exact ((mA_nearId ha).1 i h0 h1).symm

/-- If an element of `P ⊇ B` moves `V_{a+1}` then the adjacent transposition `(a a+1)` lies in
`P` (as a permutation matrix). -/
theorem swap_mem_of_move {n a : ℕ} (ha : a + 1 < n) {P : Subgroup (GLn F n)}
    (hP : borel F n ≤ P) {g : GLn F n} (hg : g ∈ P)
    (hmove : Submodule.map (g : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n (a + 1)) ≠
      stdSpan F n (a + 1)) :
    permToGL F (Equiv.swap (⟨a, by omega⟩ : Fin n) ⟨a + 1, ha⟩) ∈ P := by
  obtain ⟨σ, hσP, i, hi, hσi⟩ := exists_perm_cross hP hg (by omega) hmove
  obtain ⟨i', j', hij, hσ, hj1, hi1⟩ := perm_cross σ (a + 1) ⟨i, hi, hσi⟩
  have h1 : tvec i' j' hij.ne 1 ∈ P := hP (tvec_mem_borel i' j' hij 1)
  have h2 : tvec (σ i') (σ j') (σ.injective.ne hij.ne) 1 ∈ P := by
    rw [← permToGL_conj_tvec σ i' j' hij.ne]
    exact P.mul_mem (P.mul_mem hσP h1) (P.inv_mem hσP)
  have ht : ∀ x : F, tvec ⟨a + 1, ha⟩ ⟨a, by omega⟩ (ne_a ha) x ∈ P := fun x =>
    tvec_adjacent_of_interval hP (σ i') (σ j') hσ h2 a ha (by omega) (by omega) x
  have hm : mA (F := F) ha ∈ P := by
    have hu : uA (F := F) ha 1 ∈ P := hP (tvec_mem_borel _ _ (by simp [Fin.lt_def]) _)
    exact P.mul_mem (P.mul_mem hu (ht (-1))) hu
  rw [permToGL_swap_eq]
  exact P.mul_mem hm (hP (diagScale_mem_borel _ _ _))

/-- The finest composition whose standard flag is stabilized by `P`. -/
theorem exists_finest_boundaries {n : ℕ} (P : Subgroup (GLn F n)) :
    ∃ c : Composition n, (∀ i : Fin (n + 1), i ∈ c.boundaries ↔
        ∀ g ∈ P, Submodule.map (g : (Fin n → F) →ₗ[F] (Fin n → F)) (stdSpan F n i.val) =
          stdSpan F n i.val) ∧ P ≤ parabolic F c := by
  let C : CompositionAsSet n :=
    { boundaries := Finset.univ.filter fun i =>
        ∀ g ∈ P, (stdSpan F n i.val).map g.toLinearMap = stdSpan F n i.val
      zero_mem := by simp [stdSpan_zero]
      getLast_mem := by simp [stdSpan_top] }
  let c := (compositionEquiv n).symm C
  have hc : c.boundaries = C.boundaries :=
    congrArg CompositionAsSet.boundaries ((compositionEquiv n).apply_symm_apply C)
  refine ⟨c, fun i => ?_, fun g hg => ?_⟩
  · rw [hc]
    simp [C]
  · show g ∈ MulAction.stabilizer (GLn F n) (stdFlagOfType F c)
    rw [mem_stdFlagOfType_stabilizer_iff]
    intro i hi
    rw [hc] at hi
    exact (Finset.mem_filter.1 hi).2 g hg

theorem succ_not_mem_boundaries {n a : ℕ} (c : Composition n) (ha : a + 1 < n)
    (h : c.index ⟨a, by omega⟩ = c.index ⟨a + 1, ha⟩) :
    (⟨a + 1, by omega⟩ : Fin (n + 1)) ∉ c.boundaries := by
  intro hmem
  obtain ⟨j, -, hj⟩ := Finset.mem_map.1 hmem
  have hj' : c.sizeUpTo j = a + 1 := by
    have := congrArg Fin.val hj
    simpa [Composition.boundary] using this
  have h1 := c.sizeUpTo_index_le ⟨a, by omega⟩
  have h2 := c.lt_sizeUpTo_index_succ ⟨a + 1, ha⟩
  rw [h] at h1
  simp only at h1 h2
  have h2' : a + 1 < c.sizeUpTo ((c.index ⟨a + 1, ha⟩ : ℕ) + 1) := h2
  clear h2
  have hji : (c.index ⟨a + 1, ha⟩ : ℕ) < j := by
    by_contra hcon
    push_neg at hcon
    have := c.monotone_sizeUpTo hcon
    omega
  have hjl : (j : ℕ) < (c.index ⟨a + 1, ha⟩ : ℕ) + 1 := by
    by_contra hcon
    push_neg at hcon
    have := c.monotone_sizeUpTo hcon
    omega
  omega

/-- **Lemma 1.13, surjectivity.** Every subgroup `P ⊇ B` is a standard parabolic. -/
theorem exists_parabolic_eq {n : ℕ} {P : Subgroup (GLn F n)} (hP : borel F n ≤ P) :
    ∃ c : Composition n, P = parabolic F c := by
  obtain ⟨c, hbd, hle⟩ := exists_finest_boundaries (F := F) P
  refine ⟨c, le_antisymm hle ?_⟩
  -- the Weyl subgroup of `P` contains the Young subgroup
  have hW : youngSubgroup c ≤ parabolicWeylSubgroup F P := by
    refine youngSubgroup_le_of_adjacent c _ fun a ha hidx => ?_
    have hnb := succ_not_mem_boundaries c ha hidx
    rw [hbd] at hnb
    push_neg at hnb
    obtain ⟨g, hg, hmove⟩ := hnb
    exact swap_mem_of_move ha hP hg hmove
  intro g hg
  have hcells := lemma_1_16 (F := F) c
  have hg' : g ∈ (parabolic F c : Set (GLn F n)) := hg
  rw [hcells] at hg'
  simp only [Set.mem_iUnion] at hg'
  obtain ⟨σ, hσ, b₁, hb₁, b₂, hb₂, rfl⟩ := hg'
  exact P.mul_mem (P.mul_mem (hP hb₁) (hW hσ)) (hP hb₂)


/-- **Lemma 1.13.** `c ↦ Stab F^{0,c}` is an order-reversing bijection between
compositions of `n` and parabolic subgroups of `GL(Fⁿ)`.

**Gap (proof gap).** The printed elementary-matrix commutator identities need
pairwise distinct indices. In particular, the asserted case `j = d` involves
`E_{dd}^λ`, which is singular for `λ = -1`. We argue instead with the Bruhat permutation of an
element moving `V_{a+1}`, which yields a lower transvection `I + E_{ba}` (`b > a`) in `P`, and
the commutators `[I + E_{ba}, I + E_{a,a+1}]`, `[I + E_{b-1,b}, I + E_{ba}]` (distinct indices),
which give all adjacent `I + sE_{a+1,a}`. -/
theorem lemma_1_13 (n : ℕ) :
    (∀ c : Composition n, IsParabolic F (parabolic F c)) ∧
    Function.Injective (parabolic F (n := n)) ∧
    (∀ P : Subgroup (GLn F n), IsParabolic F P → ∃ c, P = parabolic F c) ∧
    (∀ c c' : Composition n, Composition.Refines c c' ↔ parabolic F c' ≤ parabolic F c) :=
  ⟨fun c => stdFlag_stabilizer_le F c, stdFlagOfType_stabilizer_injective F n,
    fun _ hP => exists_parabolic_eq hP,
    fun c c' => (stdFlagOfType_stabilizer_le_iff F c c').symm⟩

end MartinPhd

end
end Lemma113
