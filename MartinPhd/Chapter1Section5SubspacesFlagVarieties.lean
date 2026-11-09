import Mathlib
import MartinPhd.Chapter1Section4Cohomology
import MartinPhd.PreliminariesSolomonTits

/-!
# Chapter 1, Section 1.5 (poset of subspaces) and the start of Section 1.6 (flag varieties, J_h)

Contents:
* Chapter1Section5
* Char
* DualInv
* FormDual
* Jh
-/

section Chapter1Section5

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §1.5 El poset de subespacios de un F-espacio vectorial -/

section SubspacePoset

variable (F : Type) [Field F] [Fintype F] (k : Type) [Field k]

/-- The permutation module `k[Fl(Fⁿ)]`. -/
abbrev FlagModule (n : ℕ) := Flag F (Fin n → F) →₀ k

/-- The span of flags of length `m`, `k[Fl_m(Fⁿ)]`. -/
def flagDeg (n m : ℕ) : Submodule k (FlagModule F k n) :=
  Finsupp.supported k k {G | G.len = m}

/-- `GL(Fⁿ)` acts on `k[Fl(Fⁿ)]` by permuting flags. -/
def flagRep (n : ℕ) : Representation k (GLn F n) (FlagModule F k n) where
  toFun g := Finsupp.lmapDomain k k (g • ·)
  map_one' := by
    apply Finsupp.lhom_ext
    intro G b
    simp
  map_mul' := by
    intro g h
    apply Finsupp.lhom_ext
    intro G b
    simp [mul_smul]

/-- The `j`-simplices of the order complex `Δₙ` of the poset `Pₙ` of proper nonzero
subspaces of `Fⁿ` (strict chains of `j+1` such subspaces) correspond to flags of length
`j+2` via `φ_j(F₁ < ⋯ < F_{j+1}) = (0, F₁, …, F_{j+1}, Fⁿ)`. -/
theorem simplices_equiv_flags (n j : ℕ) :
    Nonempty ({s : Finset (Submodule F (Fin n → F)) // s.card = j + 1 ∧
        (∀ S ∈ s, S ≠ ⊥ ∧ S ≠ ⊤) ∧ IsChain (· ≤ ·) (s : Set (Submodule F (Fin n → F)))} ≃
      {G : Flag F (Fin n → F) // G.len = j + 2}) :=
by
  classical
  let forward : {s : Finset (Submodule F (Fin n → F)) // s.card = j + 1 ∧
      (∀ S ∈ s, S ≠ ⊥ ∧ S ≠ ⊤) ∧ IsChain (· ≤ ·) (s : Set (Submodule F (Fin n → F)))} →
      {G : Flag F (Fin n → F) // G.len = j + 2} := fun s => by
    have hb : (⊥ : Submodule F (Fin n → F)) ∉ s.val := fun h => (s.property.2.1 _ h).1 rfl
    have ht : (⊤ : Submodule F (Fin n → F)) ∉ s.val := fun h => (s.property.2.1 _ h).2 rfl
    have hbt : (⊥ : Submodule F (Fin n → F)) ≠ ⊤ := by
      obtain ⟨A, hA⟩ := Finset.card_pos.mp (show 0 < s.val.card by rw [s.property.1]; omega)
      intro h
      exact (s.property.2.1 _ hA).1 (le_antisymm (h ▸ le_top) bot_le)
    refine ⟨⟨insert ⊥ (insert ⊤ s.val), ?_, by simp, by simp⟩, ?_⟩
    · intro A hA B hB hne
      simp only [Finset.mem_coe, Finset.mem_insert] at hA hB
      rcases hA with rfl | rfl | hA <;> rcases hB with rfl | rfl | hB
      all_goals first | exact Or.inl bot_le | exact Or.inr bot_le |
        exact Or.inl le_top | exact Or.inr le_top | exact s.property.2.2 hA hB hne
    · simp [Flag.len, Finset.card_insert_of_notMem, hb, ht, hbt, s.property.1]
  refine ⟨Equiv.ofBijective forward ⟨?_, ?_⟩⟩
  · intro s t h
    have hc : insert ⊥ (insert ⊤ s.val) = insert ⊥ (insert ⊤ t.val) :=
      congrArg (fun G => G.val.carrier) h
    apply Subtype.ext
    ext A
    have hs := s.property.2.1 A
    have ht := t.property.2.1 A
    constructor
    · intro hA
      have := hc ▸ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hA))
      simpa only [Finset.mem_insert, (hs hA).1, (hs hA).2, false_or] using this
    · intro hA
      have := hc.symm ▸ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hA))
      simpa only [Finset.mem_insert, (ht hA).1, (ht hA).2, false_or] using this
  · intro G
    have hbt : (⊥ : Submodule F (Fin n → F)) ≠ ⊤ := by
      intro h
      have hc : G.val.carrier = {⊥} := by
        ext A
        have : A = ⊥ := le_antisymm (h ▸ le_top) bot_le
        simp [this, G.val.bot_mem]
      have := G.property
      simp [Flag.len, hc] at this
    let s := (G.val.carrier.erase ⊥).erase ⊤
    have hs : s.card = j + 1 := by
      have hc := G.val.card_eq_len_succ
      have ht : ⊤ ∈ G.val.carrier.erase ⊥ := Finset.mem_erase.mpr ⟨hbt.symm, G.val.top_mem⟩
      dsimp [s]
      rw [Finset.card_erase_of_mem ht, Finset.card_erase_of_mem G.val.bot_mem]
      rw [G.property] at hc
      omega
    refine ⟨⟨s, hs, ?_, ?_⟩, ?_⟩
    · intro A hA
      simp only [s, Finset.mem_erase] at hA
      exact ⟨hA.2.1, hA.1⟩
    · exact G.val.isChain.mono (by intro A hA; exact (Finset.mem_erase.mp (Finset.mem_erase.mp hA).2).2)
    · apply Subtype.ext
      apply Flag.ext
      change insert ⊥ (insert ⊤ s) = G.val.carrier
      ext A
      simp only [s, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | rfl | ⟨_, _, hA⟩)
        · exact G.val.bot_mem
        · exact G.val.top_mem
        · exact hA
      · intro hA
        by_cases hb : A = ⊥
        · exact Or.inl hb
        by_cases ht : A = ⊤
        · exact Or.inr (Or.inl ht)
        exact Or.inr (Or.inr ⟨ht, hb, hA⟩)

/-- The boundary of the augmented chain complex `C•(Δₙ)`, `C_j(Δₙ) = k[Fl_{j+2}(Fⁿ)]`:
`∂ e_G = ∑_{0<i<len G} (-1)ⁱ e_{G ∖ Gᵢ}`. (We sign faces by their position in the flag,
which is minus the usual simplicial sign; homology is unchanged, and this is the sign
that makes Proposition 1.8 an isomorphism of complexes on the nose.) -/
def chainBoundary (n : ℕ) : FlagModule F k n →ₗ[k] FlagModule F k n :=
  Finsupp.linearCombination k fun G =>
    ∑ A ∈ G.carrier, if h : A ≠ ⊥ ∧ A ≠ ⊤ then
      ((-1 : k) ^ G.index A) • Finsupp.single (G.erase A h) (1 : k) else 0

/-- Reduced simplicial homology `H̃_{m-2}(Δₙ)`, indexed by the flag length `m`. -/
abbrev redHomology (n m : ℕ) :=
  Subquot (flagDeg F k n m ⊓ LinearMap.ker (chainBoundary F k n))
    ((flagDeg F k n (m + 1)).map (chainBoundary F k n))

/-- The **Steinberg module** `Stₙ = H̃_{n-2}(Δₙ)`. Top-dimensional homology has no
boundaries, so it is the space of top cycles inside `k[Fl⁺(Fⁿ)]`. -/
def steinberg (n : ℕ) : Submodule k (FlagModule F k n) :=
  flagDeg F k n n ⊓ LinearMap.ker (chainBoundary F k n)

/-- The permutation matrix of `σ ∈ Sₙ` as an element of `GL(Fⁿ)`: `eᵢ ↦ e_{σ(i)}`. -/
def permToGL {n : ℕ} (σ : Equiv.Perm (Fin n)) : GLn F n :=
  LinearEquiv.funCongrLeft F F σ.symm

theorem permToGL_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permToGL F (σ * τ) = permToGL F σ * permToGL F τ := by
  ext v i
  simp [permToGL, LinearEquiv.funCongrLeft_apply]
  rfl

theorem permToGL_single {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permToGL F σ (Pi.single i 1) = Pi.single (σ i) 1 := by
  ext j
  simp [permToGL, LinearEquiv.funCongrLeft_apply, Pi.single_apply, Equiv.symm_apply_eq]

/-- `εₙ = ∑_{σ ∈ Sₙ} (-1)^{inv σ} σ · F⁰`. -/
def epsSteinberg (n : ℕ) : FlagModule F k n :=
  ∑ σ : Equiv.Perm (Fin n), ((-1 : k) ^ inv σ) • Finsupp.single (permToGL F σ • stdFlag F n) 1

/-- **Theorem 1.7 (Solomon–Tits).** For `n ≥ 1`, the reduced homology of `Δₙ` is
concentrated in degree `n − 2`, of dimension `ℓ^{C(n,2)}`, and is generated as a
`GL(Fⁿ)`-module by `εₙ`. (The homotopy-type statement, a wedge of `ℓ^{C(n,2)}` spheres
of dimension `n − 2`, is not formalized: Mathlib has no order complexes of posets.) -/
theorem chainBoundary_eq (n : ℕ) : chainBoundary F k n = ST.bd k := rfl

theorem steinberg_eq (n : ℕ) : steinberg F k n = ST.St F k (Fin n → F) n := rfl

theorem stdFlag_eq_flagOf (n : ℕ) : stdFlag F n = ST.flagOf (Pi.basisFun F (Fin n)) := by
  apply Flag.ext
  rw [ST.flagOf_carrier]
  simp only [stdFlag]
  ext W
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
  have key : ∀ i : Fin (n + 1), stdSpan F n i.val = (Pi.basisFun F (Fin n)).flag i := by
    intro i
    unfold stdSpan Module.Basis.flag
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, Pi.basisFun_apply,
      Fin.lt_def, Fin.coe_castSucc, Subtype.exists]
    exact ⟨fun ⟨a, h, e⟩ => ⟨a, h, e⟩, fun ⟨a, h, e⟩ => ⟨a, h, e⟩⟩
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, (key ⟨i, hi⟩).symm⟩
  · rintro ⟨i, rfl⟩; exact ⟨i.val, i.2, key i⟩

theorem permToGL_smul_stdFlag (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permToGL F σ • stdFlag F n = ST.flagOf ((Pi.basisFun F (Fin n)).reindex σ.symm) := by
  rw [stdFlag_eq_flagOf, ST.smul_flagOf]
  congr 1
  apply Module.Basis.eq_of_apply_eq
  intro i
  rw [Module.Basis.map_apply, ST.reindex_apply', Pi.basisFun_apply, Pi.basisFun_apply]
  exact permToGL_single F σ i

theorem epsSteinberg_eq (n : ℕ) :
    epsSteinberg F k n = ST.eps k (Pi.basisFun F (Fin n)) := by
  unfold epsSteinberg ST.eps
  simp only [permToGL_smul_stdFlag]

theorem solomon_tits (n : ℕ) (hn : 1 ≤ n) :
    (∀ m, m ≠ n → Subsingleton (redHomology F k n m)) ∧
    finrank k (steinberg F k n) = Fintype.card F ^ n.choose 2 ∧
    epsSteinberg F k n ∈ steinberg F k n ∧
    Submodule.span k (Set.range fun g : GLn F n => flagRep F k n g (epsSteinberg F k n)) =
      steinberg F k n := by
  obtain ⟨hex, hdim, hgen⟩ := ST.claim k n (Fin n → F) (Module.finrank_fin_fun F)
  refine ⟨fun m hm => ?_, hdim, ?_, ?_⟩
  · refine ⟨fun a b => ?_⟩
    induction a using Submodule.Quotient.induction_on with | H a => ?_
    induction b using Submodule.Quotient.induction_on with | H b => ?_
    rw [Submodule.Quotient.eq]
    obtain ⟨y, hyd, hy⟩ := hex m hm (a - b).1 (a - b).2.1 (a - b).2.2
    exact ⟨y, hyd, hy⟩
  · rw [epsSteinberg_eq]; exact ST.eps_mem_St k _
  · rw [steinberg_eq, hgen, epsSteinberg_eq]
    congr 1
    ext x
    simp only [Set.mem_range]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(Pi.basisFun F (Fin n)).map g, (ST.lmapDomain_smul_eps k _ g).symm⟩
    · rintro ⟨b, rfl⟩
      refine ⟨(Pi.basisFun F (Fin n)).equiv b (Equiv.refl _), ?_⟩
      show Finsupp.lmapDomain k k _ _ = _
      rw [ST.lmapDomain_smul_eps]
      congr 1
      apply Module.Basis.eq_of_apply_eq
      intro i
      rw [Module.Basis.map_apply, Module.Basis.equiv_apply]
      rfl

/-- The member of `G` missing from `F` when `G` refines `F` directly. -/
def Flag.newMember {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F G : Flag K V) : Submodule K V :=
  if h : (G.carrier \ F.carrier).Nonempty then h.choose else ⊤

/-- The complex `Σₙ^•` attached to the semicosimplicial `GL(Fⁿ)`-module `e^{⊗•}(Fⁿ)`
(1.8): `Σₙ^m = k[Fl_m(Fⁿ)]` and `d e_F = ∑ᵢ (-1)ⁱ ∑ e_G` over the `G` obtained by
splitting the `i`-th step of `F` (the new member sits at position `i`). -/
def sigmaD (n : ℕ) : FlagModule F k n →ₗ[k] FlagModule F k n :=
  Finsupp.linearCombination k fun G₀ =>
    ∑ G ∈ Finset.univ.filter (fun G => G₀.DirectlyRefines G),
      ((-1 : k) ^ G.index (G₀.newMember G)) • Finsupp.single G (1 : k)

/-- Coboundaries of `Σₙ^•` in degree `q`. -/
def sigmaB (n : ℕ) : ℕ → Submodule k (FlagModule F k n)
  | 0 => ⊥
  | q + 1 => (flagDeg F k n q).map (sigmaD F k n)

/-- `H^q(Σₙ^•)`. -/
abbrev HSigma (n q : ℕ) :=
  Subquot (flagDeg F k n q ⊓ LinearMap.ker (sigmaD F k n)) (sigmaB F k n q)

/-- The evaluation pairing `⟨φ, c⟩ = ∑_F φ(F) c(F)` between cochains of `Σₙ` (as
functions on flags, via Proposition 1.8) and chains of `Δₙ`. -/
def flagPairing (n : ℕ) (φ c : FlagModule F k n) : k := φ.sum fun G a => a * c G

theorem flagPairing_eq (n : ℕ) (φ c : FlagModule F k n) :
    flagPairing F k n φ c = ∑ G, φ G * c G := by
  unfold flagPairing
  rw [Finsupp.sum_fintype _ _ (by simp)]

theorem flagPairing_single (n : ℕ) (φ : FlagModule F k n) (G : Flag F (Fin n → F)) :
    flagPairing F k n φ (Finsupp.single G 1) = φ G := by
  rw [flagPairing_eq]
  simp [Finsupp.single_apply]

/-- The bilinear form `flagPairing`. -/
def flagBil (n : ℕ) : FlagModule F k n →ₗ[k] FlagModule F k n →ₗ[k] k :=
  LinearMap.mk₂ k (flagPairing F k n)
    (fun a b c => by simp [flagPairing_eq, add_mul, Finset.sum_add_distrib])
    (fun a b c => by simp [flagPairing_eq, Finset.mul_sum, mul_assoc])
    (fun a b c => by simp [flagPairing_eq, mul_add, Finset.sum_add_distrib])
    (fun a b c => by simp [flagPairing_eq, Finset.mul_sum, mul_left_comm])

/-- The coefficient of `e_G` in `d e_{G₀}`. -/
def sigmaCoef {n : ℕ} (G₀ G : Flag F (Fin n → F)) : k :=
  if G₀.DirectlyRefines G then (-1 : k) ^ G.index (G₀.newMember G) else 0

theorem Flag.dr_sdiff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (G₀ G : Flag K V) (h : G₀.DirectlyRefines G) :
    ∃ A, G.carrier \ G₀.carrier = {A} ∧ G₀.newMember G = A := by
  have hcard : (G.carrier \ G₀.carrier).card = 1 := by
    have h1 := Finset.card_sdiff_of_subset h.1
    have h2 := G₀.card_eq_len_succ
    have h3 := G.card_eq_len_succ
    have h4 := h.2
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
  refine ⟨a, ha, ?_⟩
  have hne : (G.carrier \ G₀.carrier).Nonempty := by rw [ha]; exact ⟨a, Finset.mem_singleton_self a⟩
  unfold Flag.newMember
  rw [dif_pos hne]
  have hc : hne.choose ∈ ({a} : Finset _) := by rw [← ha]; exact hne.choose_spec
  exact Finset.mem_singleton.1 hc

theorem Flag.erase_dr {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (G : Flag K V) (A : Submodule K V) (h : A ≠ ⊥ ∧ A ≠ ⊤) (hA : A ∈ G.carrier) :
    (G.erase A h).DirectlyRefines G ∧ (G.erase A h).newMember G = A := by
  have hsd : G.carrier \ (G.erase A h).carrier = {A} := by
    ext x
    simp only [Flag.erase, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hx'⟩
      by_contra hxA
      exact hx' ⟨hxA, hx⟩
    · rintro rfl
      exact ⟨hA, fun h => h.1 rfl⟩
  have hdr : (G.erase A h).DirectlyRefines G := by
    refine ⟨Finset.erase_subset _ _, ?_⟩
    have h1 := (G.erase A h).card_eq_len_succ
    have h2 := G.card_eq_len_succ
    have h3 : (G.erase A h).carrier.card + 1 = G.carrier.card := Finset.card_erase_add_one hA
    omega
  refine ⟨hdr, ?_⟩
  obtain ⟨B, hB, hn⟩ := Flag.dr_sdiff _ _ hdr
  rw [hn]
  rw [hsd] at hB
  exact (Finset.singleton_inj.1 hB).symm

theorem Flag.dr_erase {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (G₀ G : Flag K V) (h : G₀.DirectlyRefines G) :
    ∃ hA : G₀.newMember G ≠ ⊥ ∧ G₀.newMember G ≠ ⊤,
      G.erase (G₀.newMember G) hA = G₀ ∧ G₀.newMember G ∈ G.carrier := by
  obtain ⟨A, hsd, hn⟩ := Flag.dr_sdiff G₀ G h
  have hAmem : A ∈ G.carrier \ G₀.carrier := by rw [hsd]; simp
  rw [Finset.mem_sdiff] at hAmem
  have hA : A ≠ ⊥ ∧ A ≠ ⊤ :=
    ⟨fun e => hAmem.2 (e ▸ G₀.bot_mem), fun e => hAmem.2 (e ▸ G₀.top_mem)⟩
  rw [hn]
  refine ⟨hA, ?_, hAmem.1⟩
  apply Flag.ext
  show G.carrier.erase A = G₀.carrier
  ext x
  rw [Finset.mem_erase]
  constructor
  · rintro ⟨hx, hxG⟩
    by_contra hx0
    have : x ∈ G.carrier \ G₀.carrier := Finset.mem_sdiff.2 ⟨hxG, hx0⟩
    rw [hsd] at this
    exact hx (Finset.mem_singleton.1 this)
  · intro hx
    refine ⟨?_, h.1 hx⟩
    rintro rfl
    exact hAmem.2 hx

theorem sigmaCoef_ne_zero {n : ℕ} {G₀ G : Flag F (Fin n → F)} (h : sigmaCoef F k G₀ G ≠ 0) :
    G.len = G₀.len + 1 := by
  unfold sigmaCoef at h
  split_ifs at h with hd
  · exact hd.2
  · exact absurd rfl h

theorem sigmaD_single (n : ℕ) (G₀ G : Flag F (Fin n → F)) :
    sigmaD F k n (Finsupp.single G₀ 1) G = sigmaCoef F k G₀ G := by
  unfold sigmaD
  rw [Finsupp.linearCombination_single, one_smul, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' ]
  unfold sigmaCoef
  by_cases hd : G₀.DirectlyRefines G <;> simp [hd]

theorem bd_single (n : ℕ) (G₀ G : Flag F (Fin n → F)) :
    chainBoundary F k n (Finsupp.single G 1) G₀ = sigmaCoef F k G₀ G := by
  unfold chainBoundary
  rw [Finsupp.linearCombination_single, one_smul, Finsupp.finsetSum_apply]
  by_cases hd : G₀.DirectlyRefines G
  · obtain ⟨hA, he, hm⟩ := Flag.dr_erase G₀ G hd
    rw [Finset.sum_eq_single (G₀.newMember G)]
    · rw [dif_pos hA, Finsupp.smul_apply, he, Finsupp.single_eq_same]
      simp [sigmaCoef, hd]
    · intro A hAG hne
      by_cases hp : A ≠ ⊥ ∧ A ≠ ⊤
      · rw [dif_pos hp, Finsupp.smul_apply, Finsupp.single_apply]
        have : G.erase A hp ≠ G₀ := by
          intro heq
          have h1 := (Flag.erase_dr G A hp hAG).2
          rw [heq] at h1
          exact hne h1.symm
        simp [this]
      · rw [dif_neg hp]; rfl
    · intro hn; exact absurd hm hn
  · rw [Finset.sum_eq_zero]
    · simp [sigmaCoef, hd]
    · intro A hAG
      by_cases hp : A ≠ ⊥ ∧ A ≠ ⊤
      · rw [dif_pos hp, Finsupp.smul_apply, Finsupp.single_apply]
        have : G.erase A hp ≠ G₀ := by
          intro heq
          exact hd (heq ▸ (Flag.erase_dr G A hp hAG).1)
        simp [this]
      · rw [dif_neg hp]; rfl

theorem sigmaD_apply (n : ℕ) (φ : FlagModule F k n) (G : Flag F (Fin n → F)) :
    sigmaD F k n φ G = ∑ G₀, φ G₀ * sigmaCoef F k G₀ G := by
  induction φ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [add_mul, Finset.sum_add_distrib, hf, hg]
  | single G₁ a =>
    have : (Finsupp.single G₁ a : FlagModule F k n) = a • Finsupp.single G₁ 1 := by
      simp
    rw [this, map_smul, Finsupp.smul_apply, sigmaD_single]
    simp [Finsupp.single_apply]

theorem bd_apply (n : ℕ) (c : FlagModule F k n) (G₀ : Flag F (Fin n → F)) :
    chainBoundary F k n c G₀ = ∑ G, c G * sigmaCoef F k G₀ G := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [add_mul, Finset.sum_add_distrib, hf, hg]
  | single G₁ a =>
    have : (Finsupp.single G₁ a : FlagModule F k n) = a • Finsupp.single G₁ 1 := by
      simp
    rw [this, map_smul, Finsupp.smul_apply, bd_single]
    simp [Finsupp.single_apply]

/-- `d` is the adjoint of `∂` for the evaluation pairing. -/
theorem pairing_sigmaD (n : ℕ) (φ c : FlagModule F k n) :
    flagPairing F k n (sigmaD F k n φ) c = flagPairing F k n φ (chainBoundary F k n c) := by
  simp only [flagPairing_eq, sigmaD_apply, bd_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Proposition 1.8.** `ξ : Hom_k(C•(Δₙ), k) ≅ Σₙ^{•+2}`, `δ_F ↦ e_F`, is a
`GL(Fⁿ)`-equivariant isomorphism of complexes. Here `ξ` is the identification of
functions on flags with finitely supported ones; we state that it intertwines the
transpose of `∂` with `d`, and that it is equivariant. -/
theorem prop_1_8 (n : ℕ) :
    let ξ := (Finsupp.linearEquivFunOnFinite k k (Flag F (Fin n → F))).symm
    (∀ G, ξ (Pi.single G 1) = Finsupp.single G 1) ∧
    (∀ φ : Flag F (Fin n → F) → k,
      ξ (fun G => flagPairing F k n (ξ φ) (chainBoundary F k n (Finsupp.single G 1))) =
        sigmaD F k n (ξ φ)) ∧
    (∀ (g : GLn F n) (φ : Flag F (Fin n → F) → k),
      ξ (fun G => φ (g⁻¹ • G)) = flagRep F k n g (ξ φ)) := by
  intro ξ
  refine ⟨fun G => ?_, fun φ => ?_, fun g φ => ?_⟩
  · ext H
    simp [ξ, Finsupp.single_apply, Pi.single_apply]
  · ext G
    have : ξ (fun G => flagPairing F k n (ξ φ) (chainBoundary F k n (Finsupp.single G 1))) G =
        flagPairing F k n (ξ φ) (chainBoundary F k n (Finsupp.single G 1)) := rfl
    rw [this, ← pairing_sigmaD, flagPairing_single]
  · ext G
    have h1 : ξ (fun G => φ (g⁻¹ • G)) G = φ (g⁻¹ • G) := rfl
    rw [h1]
    show _ = Finsupp.mapDomain (g • ·) (ξ φ) G
    have := Finsupp.mapDomain_equiv_apply (f := (MulAction.toPerm g : Flag F (Fin n → F) ≃ _)) (ξ φ) G
    simp only [MulAction.toPerm_apply, MulAction.toPerm_symm_apply] at this
    exact (this.trans rfl).symm

theorem mem_flagDeg_iff {n m : ℕ} {φ : FlagModule F k n} :
    φ ∈ flagDeg F k n m ↔ ∀ G, G.len ≠ m → φ G = 0 := by
  unfold flagDeg
  rw [Finsupp.mem_supported']
  exact Iff.rfl

theorem sigmaD_mem_flagDeg {n q : ℕ} {φ : FlagModule F k n} (hφ : φ ∈ flagDeg F k n q) :
    sigmaD F k n φ ∈ flagDeg F k n (q + 1) := by
  rw [mem_flagDeg_iff] at hφ ⊢
  intro G hG
  rw [sigmaD_apply]
  refine Finset.sum_eq_zero fun G₀ _ => ?_
  by_cases h0 : sigmaCoef F k G₀ G = 0
  · rw [h0, mul_zero]
  · have := sigmaCoef_ne_zero F k h0
    rw [hφ G₀ (by omega), zero_mul]

theorem bd_mem_flagDeg {n p : ℕ} {c : FlagModule F k n} (hc : c ∈ flagDeg F k n (p + 1)) :
    chainBoundary F k n c ∈ flagDeg F k n p := by
  rw [mem_flagDeg_iff] at hc ⊢
  intro G₀ hG
  rw [bd_apply]
  refine Finset.sum_eq_zero fun G _ => ?_
  by_cases h0 : sigmaCoef F k G₀ G = 0
  · rw [h0, mul_zero]
  · have := sigmaCoef_ne_zero F k h0
    rw [hc G (by omega), zero_mul]

theorem bd_zero_of_deg_zero {n : ℕ} {c : FlagModule F k n} (hc : c ∈ flagDeg F k n 0) :
    chainBoundary F k n c = 0 := by
  rw [mem_flagDeg_iff] at hc
  ext G₀
  rw [bd_apply]
  refine (Finset.sum_eq_zero fun G _ => ?_).trans (Finsupp.zero_apply).symm
  by_cases h0 : sigmaCoef F k G₀ G = 0
  · rw [h0, mul_zero]
  · have := sigmaCoef_ne_zero F k h0
    rw [hc G (by omega), zero_mul]

/-- The pairing is nondegenerate on each `k[S]`. -/
theorem pairing_nondeg {n : ℕ} (S : Set (Flag F (Fin n → F))) {φ : FlagModule F k n}
    (hφ : φ ∈ Finsupp.supported k k S)
    (h : ∀ c ∈ Finsupp.supported k k S, flagPairing F k n φ c = 0) : φ = 0 := by
  ext G
  by_cases hG : G ∈ S
  · have := h _ (Finsupp.single_mem_supported k (1 : k) hG)
    rw [flagPairing_single] at this
    simpa using this
  · exact (Finsupp.mem_supported' _ _ |>.1 hφ) G hG

/-- The pairing identifies `k[S]` with its own dual. -/
def pairPhi {n : ℕ} (S : Set (Flag F (Fin n → F))) :
    Finsupp.supported k k S →ₗ[k] Module.Dual k (Finsupp.supported k k S) :=
  (flagBil F k n).compl₁₂ (Finsupp.supported k k S).subtype (Finsupp.supported k k S).subtype

theorem pairPhi_apply {n : ℕ} (S : Set (Flag F (Fin n → F))) (φ c : Finsupp.supported k k S) :
    pairPhi F k S φ c = flagPairing F k n φ.1 c.1 := rfl

theorem pairPhi_surjective {n : ℕ} (S : Set (Flag F (Fin n → F))) :
    Function.Surjective (pairPhi F k S) := by
  have hinj : Function.Injective (pairPhi F k S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    refine pairing_nondeg F k S φ.2 fun c hc => ?_
    have := LinearMap.congr_fun hφ ⟨c, hc⟩
    simpa [pairPhi_apply] using this
  have hfin : Module.finrank k (Module.Dual k (Finsupp.supported k k S)) =
      Module.finrank k (Finsupp.supported k k S) := Subspace.dual_finrank_eq
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin.symm).1 hinj

/-- Cocycles in `Σ` are orthogonal to all `∂`-images, and conversely. -/
theorem sigmaD_eq_zero_of_orth {n q : ℕ} {φ : FlagModule F k n} (hφ : φ ∈ flagDeg F k n q)
    (h : ∀ c ∈ flagDeg F k n (q + 1), flagPairing F k n φ (chainBoundary F k n c) = 0) :
    sigmaD F k n φ = 0 := by
  refine pairing_nondeg F k _ (sigmaD_mem_flagDeg F k hφ) fun c hc => ?_
  rw [pairing_sigmaD]; exact h c hc

/-- A class orthogonal to all cycles is a coboundary. -/
theorem mem_sigmaB_of_orth {n q : ℕ} {φ : FlagModule F k n} (hφ : φ ∈ flagDeg F k n q)
    (h : ∀ c ∈ flagDeg F k n q, chainBoundary F k n c = 0 → flagPairing F k n φ c = 0) :
    φ ∈ sigmaB F k n q := by
  cases q with
  | zero =>
    have : φ = 0 := pairing_nondeg F k _ hφ fun c hc => h c hc (bd_zero_of_deg_zero F k hc)
    rw [this]; exact zero_mem _
  | succ p =>
    let T : flagDeg F k n (p + 1) →ₗ[k] flagDeg F k n p :=
      (chainBoundary F k n).restrict (fun c hc => bd_mem_flagDeg F k hc)
    let f : Module.Dual k (flagDeg F k n (p + 1)) := pairPhi F k _ ⟨φ, hφ⟩
    have hf : f ∈ (LinearMap.ker T).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro c hc
      have hT : chainBoundary F k n c.1 = 0 := by
        have := congrArg Subtype.val (LinearMap.mem_ker.1 hc)
        simpa [T] using this
      exact h c.1 c.2 hT
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hf
    obtain ⟨g, hg⟩ := hf
    obtain ⟨ψ, hψ⟩ := pairPhi_surjective F k _ g
    have hdψ : sigmaD F k n ψ.1 ∈ flagDeg F k n (p + 1) := sigmaD_mem_flagDeg F k ψ.2
    have heq : φ = sigmaD F k n ψ.1 := by
      have : φ - sigmaD F k n ψ.1 = 0 := by
        refine pairing_nondeg F k _ (Submodule.sub_mem _ hφ hdψ) fun c hc => ?_
        have h1 := LinearMap.congr_fun hg ⟨c, hc⟩
        rw [LinearMap.dualMap_apply, ← hψ] at h1
        have h2 : flagPairing F k n φ c = flagPairing F k n ψ.1 (chainBoundary F k n c) := by
          exact h1.symm
        rw [← pairing_sigmaD] at h2
        simp only [flagPairing_eq] at h2 ⊢
        simp only [Finsupp.coe_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        rw [h2, sub_self]
      exact sub_eq_zero.1 this
    rw [heq]
    exact ⟨ψ.1, ψ.2, rfl⟩

/-- **Corollary 1.9.** `H^q(Σₙ^•) ≅ Stₙ^*` for `q = n` and `0` otherwise, as
`GL(Fⁿ)`-modules; the evaluation pairing `Hⁿ(Σₙ) ⊗ Stₙ → k` is nondegenerate. We state
this as: the pairing descends to a linear isomorphism `Hⁿ(Σₙ) ≅ Stₙ^*` (which is then
automatically equivariant, the pairing being invariant). -/
theorem cor_1_9 (n : ℕ) :
    (∀ q, q ≠ n → Subsingleton (HSigma F k n q)) ∧
    ∃ e : HSigma F k n n ≃ₗ[k] Module.Dual k (steinberg F k n),
      ∀ (φ : FlagModule F k n) (hφ : φ ∈ flagDeg F k n n ⊓ LinearMap.ker (sigmaD F k n))
        (c : steinberg F k n), e (Subquot.mk φ hφ) c = flagPairing F k n φ c := by
  obtain ⟨hex, -, -⟩ := ST.claim k n (Fin n → F) (Module.finrank_fin_fun F)
  refine ⟨fun q hq => ?_, ?_⟩
  · refine ⟨fun a b => ?_⟩
    induction a using Submodule.Quotient.induction_on with | H a => ?_
    induction b using Submodule.Quotient.induction_on with | H b => ?_
    rw [Submodule.Quotient.eq]
    have hx := (a - b).2
    refine mem_sigmaB_of_orth F k hx.1 fun c hc hbc => ?_
    obtain ⟨y, hy, rfl⟩ := hex q hq c hc hbc
    have hx0 : sigmaD F k n (a - b).1 = 0 := LinearMap.mem_ker.1 hx.2
    rw [← chainBoundary_eq F k n, ← pairing_sigmaD]
    change flagPairing F k n (sigmaD F k n (a - b).1) y = 0
    rw [hx0]
    simp [flagPairing_eq]
  · -- every cochain of degree `n` is a cocycle
    have hz : ∀ φ ∈ flagDeg F k n n, sigmaD F k n φ = 0 := by
      intro φ hφ
      ext G
      have h1 := (mem_flagDeg_iff F k).1 (sigmaD_mem_flagDeg F k hφ) G
      by_cases hG : G.len = n + 1
      · exact absurd hG (by
          have := ST.len_le_finrank (F := F) G
          rw [Module.finrank_fin_fun] at this
          omega)
      · simpa using h1 hG
    let Z := flagDeg F k n n ⊓ LinearMap.ker (sigmaD F k n)
    let ι : steinberg F k n →ₗ[k] flagDeg F k n n := Submodule.inclusion inf_le_left
    let Ψ : Z →ₗ[k] Module.Dual k (steinberg F k n) :=
      (flagBil F k n).compl₁₂ Z.subtype (steinberg F k n).subtype
    have hsurj : Function.Surjective Ψ := by
      intro f
      obtain ⟨f', hf'⟩ := LinearMap.dualMap_surjective_of_injective
        (Submodule.inclusion_injective (inf_le_left : steinberg F k n ≤ flagDeg F k n n)) f
      obtain ⟨φ, hφ⟩ := pairPhi_surjective F k _ f'
      refine ⟨⟨φ.1, Submodule.mem_inf.2 ⟨φ.2, LinearMap.mem_ker.2 (hz _ φ.2)⟩⟩, ?_⟩
      ext c
      exact (LinearMap.congr_fun hφ ⟨c.1, c.2.1⟩).trans (LinearMap.congr_fun hf' c)
    have hker : LinearMap.ker Ψ = (sigmaB F k n n).comap Z.subtype := by
      ext ⟨φ, hφ⟩
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · intro h
        refine mem_sigmaB_of_orth F k hφ.1 fun c hc hbc => ?_
        have := LinearMap.congr_fun h ⟨c, Submodule.mem_inf.2 ⟨hc, LinearMap.mem_ker.2 hbc⟩⟩
        exact this
      · intro h
        ext c
        cases n with
        | zero =>
          have : φ = 0 := by simpa [sigmaB] using h
          simp [Ψ, this, flagPairing_eq]
        | succ p =>
          obtain ⟨ψ, hψ, rfl⟩ := h
          have hc := LinearMap.mem_ker.1 c.2.2
          simp only [Ψ, LinearMap.compl₁₂_apply, Submodule.subtype_apply, LinearMap.zero_apply]
          change flagPairing F k _ (sigmaD F k _ ψ) c.1 = 0
          rw [pairing_sigmaD, hc]
          simp [flagPairing_eq]
    refine ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
      (LinearMap.quotKerEquivOfSurjective Ψ hsurj), fun φ hφ c => ?_⟩
    rfl

end SubspacePoset

end MartinPhd

end
end Chapter1Section5

section Char

open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

/-! ## Flags of a given length split by their type (for the character formula 1.16) -/

section TypeSplit

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem Flag.finrank_nth_mono (F : Flag K V) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.len) :
    finrank K (F.nth i) ≤ finrank K (F.nth j) :=
  Submodule.finrank_mono (F.nth_mono hij (by have := F.card_eq_len_succ; omega))

theorem Flag.typeList_sum_aux (F : Flag K V) (N : ℕ) (hN : N ≤ F.len) :
    ((List.range N).map fun i => finrank K (F.nth (i + 1)) - finrank K (F.nth i)).sum =
      finrank K (F.nth N) := by
  induction N with
  | zero => simpa using ((Submodule.finrank_eq_zero (S := F.nth 0)).2 F.nth_zero).symm
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
    have := F.finrank_nth_mono (i := N) (j := N + 1) (by omega) hN
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    omega

theorem Flag.typeList_sum (F : Flag K V) : F.typeList.sum = finrank K V := by
  unfold Flag.typeList
  rw [F.typeList_sum_aux F.len le_rfl, F.nth_len]
  simp

theorem Flag.typeList_pos (F : Flag K V) : ∀ x ∈ F.typeList, 0 < x := by
  intro x hx
  unfold Flag.typeList at hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hi' := List.mem_range.1 hi
  have hlt : F.nth i < F.nth (i + 1) :=
    F.nth_lt_nth (by omega) (by have := F.card_eq_len_succ; omega)
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

/-- The type of a flag of `V` (`dim V = n`) as a composition of `n`. -/
def Flag.toComposition {n : ℕ} (hn : finrank K V = n) (F : Flag K V) : Composition n where
  blocks := F.typeList
  blocks_pos := fun hi => F.typeList_pos _ hi
  blocks_sum := by rw [F.typeList_sum, hn]

theorem Flag.toComposition_isOfType {n : ℕ} (hn : finrank K V = n) (F : Flag K V) :
    F.IsOfType (F.toComposition hn) := rfl

theorem Flag.toComposition_length {n : ℕ} (hn : finrank K V = n) (F : Flag K V) :
    (F.toComposition hn).length = F.len := by
  show F.typeList.length = F.len
  exact F.typeList_length

theorem card_len_eq_sum_types [Finite K] {n : ℕ} (hn : finrank K V = n) (P : Flag K V → Prop)
    (m : ℕ) :
    Nat.card {G : Flag K V // G.len = m ∧ P G} =
      ∑ c ∈ (Finset.univ : Finset (Composition n)).filter (fun c => c.length = m),
        Nat.card {G : Flag K V // G.IsOfType c ∧ P G} := by
  classical
  haveI : Fintype (Flag K V) := Fintype.ofFinite _
  have hc : ∀ (Q : Flag K V → Prop), Nat.card {G : Flag K V // Q G} =
      (Finset.univ.filter Q).card := fun Q => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  simp_rw [hc]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun G : Flag K V => G.toComposition hn)
    (t := (Finset.univ : Finset (Composition n)).filter (fun c => c.length = m))]
  · refine Finset.sum_congr rfl fun c hcm => ?_
    congr 1
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcm ⊢
    constructor
    · rintro ⟨⟨hl, hP⟩, rfl⟩
      exact ⟨G.toComposition_isOfType hn, hP⟩
    · rintro ⟨hty, hP⟩
      have hcomp : G.toComposition hn = c := Composition.ext hty
      refine ⟨⟨?_, hP⟩, hcomp⟩
      rw [← G.toComposition_length hn, hcomp]; exact hcm
  · intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter,
      Set.mem_setOf_eq] at hG ⊢
    rw [G.toComposition_length hn]; exact hG.1

end TypeSplit

end MartinPhd

end
end Char

section DualInv

open Representation Module

namespace Representation

section DualComp

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

@[simp]
theorem dual_comp {H : Type*} [Group H] (f : H →* G) :
    Representation.dual (ρ.comp f) = (ρ.dual).comp f := by
  ext h
  simp [Representation.dual_apply]

end DualComp

section FinrankInvariants

variable {k G V : Type*} [Field k] [CharZero k] [Group G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (ρ : Representation k G V)

/-- The dimension of the invariant subspace of the dual representation equals
that of the original representation, for a finite group over a field of characteristic 0. -/
theorem finrank_invariants_dual [Fintype G] :
    finrank k (invariants ρ.dual) = finrank k (invariants ρ) := by
  have : Invertible (Nat.card G : k) := invertibleOfNonzero (NeZero.ne (Nat.card G : k))
  have h_sum : (∑ g : G, ρ.dual.character g) = ∑ g : G, ρ.character g := by
    simp_rw [char_dual]
    exact Equiv.sum_comp (Equiv.inv G) ρ.character
  have h_cast : (finrank k (invariants ρ.dual) : k) = (finrank k (invariants ρ) : k) := by
    rw [← card_inv_mul_sum_char_eq_finrank ρ.dual, ← card_inv_mul_sum_char_eq_finrank ρ, h_sum]
  exact Nat.cast_injective h_cast

/-- The dimension of the invariant subspace of the dual representation equals
that of the original representation, for a finite group over a field of characteristic 0. -/
theorem finrank_invariants_dual_of_finite [Finite G] :
    finrank k (invariants ρ.dual) = finrank k (invariants ρ) := by
  have : Fintype G := Fintype.ofFinite G
  exact finrank_invariants_dual ρ

/-- Invariant dimension equality for dual representations restricted to a finite subgroup. -/
theorem finrank_invariants_subgroup_dual (H : Subgroup G) [Fintype H] :
    finrank k (invariants (ρ.dual.comp H.subtype)) = finrank k (invariants (ρ.comp H.subtype)) := by
  have h := finrank_invariants_dual (ρ.comp H.subtype)
  rw [dual_comp] at h
  exact h

/-- Invariant dimension equality for dual representations restricted to a finite subgroup. -/
theorem finrank_invariants_subgroup_dual_of_finite (H : Subgroup G) [Finite H] :
    finrank k (invariants (ρ.dual.comp H.subtype)) = finrank k (invariants (ρ.comp H.subtype)) := by
  have : Fintype H := Fintype.ofFinite H
  exact finrank_invariants_subgroup_dual ρ H

end FinrankInvariants

end Representation

namespace MartinPhd

export Representation (finrank_invariants_dual finrank_invariants_dual_of_finite
  finrank_invariants_subgroup_dual finrank_invariants_subgroup_dual_of_finite dual_comp)

end MartinPhd

end DualInv

section FormDual

/-! # Invariant nondegenerate bilinear forms vs self-duality

Let `G` be a group, `k` a field, and `ρ : Representation k G V`.
A nondegenerate bilinear form on `V` can be identified with a linear equivalence
`e : V ≃ₗ[k] Module.Dual k V`. The form is `G`-invariant if `e (ρ g v) (ρ g w) = e v w`
for all `g, v, w`.

This file proves that such an invariant nondegenerate bilinear form exists if and only if
`ρ` is self-dual, i.e., isomorphic to its dual representation `ρ.dual`.
-/

namespace MartinPhd

open Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- Given a nondegenerate invariant bilinear form on `V` (viewed as a linear equivalence
`e : V ≃ₗ[k] Module.Dual k V` such that `e (ρ g v) (ρ g w) = e v w`), construct an equivalence
of representations between `ρ` and `ρ.dual`. -/
def equivOfInvariantForm (e : V ≃ₗ[k] Module.Dual k V)
    (he : ∀ (g : G) (v w : V), e (ρ g v) (ρ g w) = e v w) : ρ.Equiv ρ.dual :=
  Representation.Equiv.mk e fun g => by
    ext v w
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      dual_apply, Module.Dual.transpose_apply]
    rw [← he g⁻¹ (ρ g v) w, inv_self_apply]

/-- A representation equivalence between `ρ` and its dual `ρ.dual` yields an invariant
bilinear form. -/
theorem invariant_form_of_equiv (φ : ρ.Equiv ρ.dual) (g : G) (v w : V) :
    φ.toLinearEquiv (ρ g v) (ρ g w) = φ.toLinearEquiv v w := by
  have h1 : φ (ρ g v) = (ρ.dual g) (φ v) := LinearMap.congr_fun (φ.isIntertwining' g) v
  change (φ (ρ g v)) (ρ g w) = (φ v) w
  rw [h1]
  simp only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_self_apply]

/-- Invariant nondegenerate bilinear forms vs self-duality: a representation `ρ` carries an
invariant nondegenerate bilinear form if and only if `ρ` is isomorphic to `ρ.dual`. -/
theorem exists_invariant_form_iff :
    (∃ e : V ≃ₗ[k] Module.Dual k V, ∀ (g : G) (v w : V), e (ρ g v) (ρ g w) = e v w) ↔
      Nonempty (ρ.Equiv ρ.dual) := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨equivOfInvariantForm ρ e he⟩
  · rintro ⟨φ⟩
    exact ⟨φ.toLinearEquiv, invariant_form_of_equiv ρ φ⟩

end MartinPhd

end FormDual

section Jh

/-! Linear algebra for the Jordan–Hölder permutation of two flags. -/

open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

/-- The Jordan–Hölder (Weyl distance) function: `d(F,G)(i)` is the least `j` with
`(Fᵢ ∩ Gⱼ)/(F_{i-1} ∩ Gⱼ) ≠ 0` (thesis indices from `1`; here `i, j : Fin n`). -/
def jhFun {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (n : ℕ) (F G : Flag K V) (i : Fin n) : Fin n :=
  let s := Finset.univ.filter fun j : Fin n =>
    finrank K ↥(F.nth i.val ⊓ G.nth (j.val + 1)) < finrank K ↥(F.nth (i.val + 1) ⊓ G.nth (j.val + 1))
  if h : s.Nonempty then s.min' h else i

/-- The **Jordan–Hölder permutation** `d(F, G) ∈ Sₙ` of two complete flags
([AB08, §4.3], [Abe91, §II]).

`jhFun n F G` sends the step `i` of `F` to the step of `G` where it first appears. The
permutation `σ = d(F, G)` of Proposition 1.10 goes the other way: the `j`-th vector of a
basis adapted to `G` is the `σ(j)`-th vector of a basis adapted to `F`, so `σ` is the
inverse of `jhFun`. (With `σ = jhFun` itself, Proposition 1.10, `d(F, σF) = σ` and
`F⁰ ∗ S ↔ shuffle` would all hold only up to inversion; we checked this on the 3-cycle
`F = (e₁,e₂,e₃)`, `G = (e₂,e₃,e₁)`.) -/
def jh {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (n : ℕ) (F G : Flag K V) : Equiv.Perm (Fin n) :=
  if h : Function.Bijective (jhFun n F G) then (Equiv.ofBijective _ h).symm else 1


section LinearAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Transport of the first-appearance function under a linear automorphism. -/
theorem jhFun_smul (n : ℕ) (F G : Flag K V) (g : V ≃ₗ[K] V) :
    jhFun n (g • F) (g • G) = jhFun n F G := by
  have hr (a b : ℕ) :
      finrank K ↥((g • F).nth a ⊓ (g • G).nth b) =
        finrank K ↥(F.nth a ⊓ G.nth b) := by
    change finrank K ↥((F.map g).nth a ⊓ (G.map g).nth b) = _
    rw [Flag.nth_map, Flag.nth_map, ← Submodule.map_inf _ g.injective,
      LinearEquiv.finrank_map_eq]
  funext i
  simp only [jhFun, hr]

/-- The Weyl permutation is invariant under simultaneous transport. -/
theorem jh_smul (n : ℕ) (F G : Flag K V) (g : V ≃ₗ[K] V) :
    jh n (g • F) (g • G) = jh n F G := by
  simp only [jh, jhFun_smul]

omit [FiniteDimensional K V] in
/-- Intersection of two subspaces spanned by subsets of one basis. -/
theorem jh_span_inf {ι : Type*} (b : Basis ι K V) (s t : Set ι) :
    Submodule.span K (b '' s) ⊓ Submodule.span K (b '' t) =
      Submodule.span K (b '' (s ∩ t)) := by
  ext x
  simp only [Submodule.mem_inf, b.mem_span_image, Set.subset_inter_iff]

omit [FiniteDimensional K V] in
/-- Inclusion of coordinate subspaces reflects inclusion of their index sets. -/
theorem jh_span_le {ι : Type*} (b : Basis ι K V) (s t : Set ι) :
    Submodule.span K (b '' s) ≤ Submodule.span K (b '' t) ↔ s ⊆ t := by
  constructor
  · intro h i hi
    exact b.self_mem_span_image.mp (h (Submodule.subset_span ⟨i, hi, rfl⟩))
  · intro h
    exact Submodule.span_mono (Set.image_mono h)

/-- Strict rank growth for nested coordinate subspaces. -/
theorem jh_rank_span_lt {ι : Type*} (b : Basis ι K V) (s t : Set ι) (hst : s ⊆ t) :
    finrank K (Submodule.span K (b '' s)) < finrank K (Submodule.span K (b '' t)) ↔
      ¬ t ⊆ s := by
  have hle := (jh_span_le b s t).2 hst
  constructor
  · intro h hts
    have he := le_antisymm hle ((jh_span_le b t s).2 hts)
    rw [he] at h
    exact (lt_irrefl _ h)
  · intro h
    exact Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne hle (fun he => h ((jh_span_le b t s).1 he.ge)))

/-- The complete flag of an ordered basis (universe-polymorphic version). -/
def jhFlag {n : ℕ} (b : Basis (Fin n) K V) : Flag K V where
  carrier := Finset.univ.image b.flag
  isChain := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact b.isChain_range_flag
  bot_mem := Finset.mem_image.2 ⟨0, Finset.mem_univ _, b.flag_zero⟩
  top_mem := Finset.mem_image.2 ⟨Fin.last n, Finset.mem_univ _, b.flag_last⟩

omit [FiniteDimensional K V] in
theorem jhFlag_index {n : ℕ} (b : Basis (Fin n) K V) (i : Fin (n + 1)) :
    (jhFlag b).index (b.flag i) = i.val := by
  unfold Flag.index jhFlag
  have he : (Finset.univ.image b.flag).filter (· < b.flag i) =
      (Finset.univ.filter (· < i)).image b.flag := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, rfl⟩, h⟩
      exact ⟨j, b.flag_strictMono.lt_iff_lt.1 h, rfl⟩
    · rintro ⟨j, h, rfl⟩
      exact ⟨⟨j, rfl⟩, b.flag_strictMono h⟩
  rw [he, Finset.card_image_of_injective _ b.flag_strictMono.injective,
    Finset.filter_gt_eq_Iio, Fin.card_Iio]

omit [FiniteDimensional K V] in
theorem jhFlag_nth {n : ℕ} (b : Basis (Fin n) K V) (i : Fin (n + 1)) :
    (jhFlag b).nth i.val = b.flag i := by
  rw [← jhFlag_index b i]
  exact Flag.nth_index _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)

omit [FiniteDimensional K V] in
theorem jhFlag_adapted {n : ℕ} (b : Basis (Fin n) K V) : Flag.IsAdapted b (jhFlag b) := by
  rintro A hA
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hA
  by_cases h : i.val < n
  · right
    refine ⟨⟨i.val, h⟩, ?_⟩
    rfl
  · left
    have he : i = Fin.last n := Fin.ext (by have := i.isLt; simp; omega)
    rw [he, b.flag_last]

/-- A complete flag adapted to a basis is precisely that basis's full flag. -/
theorem jhFlag_eq_of_adapted {n : ℕ} (b : Basis (Fin n) K V) (F : Flag K V)
    (hF : F.IsComplete) (hn : finrank K V = n) (hb : Flag.IsAdapted b F) : F = jhFlag b := by
  apply Flag.ext
  apply Finset.eq_of_subset_of_card_le
  · intro A hA
    rcases hb A hA with rfl | ⟨i, rfl⟩
    · exact Finset.mem_image.2 ⟨Fin.last n, Finset.mem_univ _, b.flag_last⟩
    · exact Finset.mem_image.2 ⟨i.castSucc, Finset.mem_univ _, rfl⟩
  · change (Finset.univ.image b.flag).card ≤ F.carrier.card
    rw [Finset.card_image_of_injective _ b.flag_strictMono.injective,
      Finset.card_univ, Fintype.card_fin, Flag.card_eq_len_succ, hF, hn]

omit [FiniteDimensional K V] in
theorem jhFlag_reindex_span {n : ℕ} (b : Basis (Fin n) K V)
    (σ : Equiv.Perm (Fin n)) (j : Fin (n + 1)) :
    (b.reindex σ.symm).flag j =
      Submodule.span K (b '' {i | (σ.symm i).val < j.val}) := by
  unfold Basis.flag
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨σ i, by simpa [Fin.lt_def] using hi, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨σ.symm i, hi, by simp⟩

/-- For coordinate flags, the rank jump at row `i` occurs precisely after its
column `σ⁻¹(i)` has entered the second flag. -/
theorem jhFlag_rank_jump {n : ℕ} (b : Basis (Fin n) K V)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    finrank K ↥((jhFlag b).nth i.val ⊓ (jhFlag (b.reindex σ.symm)).nth (j.val + 1)) <
      finrank K ↥((jhFlag b).nth (i.val + 1) ⊓ (jhFlag (b.reindex σ.symm)).nth (j.val + 1)) ↔
      σ.symm i ≤ j := by
  have h0 := jhFlag_nth b i.castSucc
  have h1 := jhFlag_nth b i.succ
  have h2 := jhFlag_nth (b.reindex σ.symm) j.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h0 h1 h2
  rw [h0, h1, h2, jhFlag_reindex_span]
  change finrank K ↥(Submodule.span K (b '' {x | x.val < i.val}) ⊓
      Submodule.span K (b '' {x | (σ.symm x).val < j.val + 1})) <
    finrank K ↥(Submodule.span K (b '' {x | x.val < i.val + 1}) ⊓
      Submodule.span K (b '' {x | (σ.symm x).val < j.val + 1})) ↔ _
  rw [jh_span_inf, jh_span_inf]
  rw [jh_rank_span_lt b _ _ (by
    intro x hx
    exact ⟨Nat.lt_succ_of_lt hx.1, hx.2⟩)]
  change (¬ ∀ x : Fin n, (x.val < i.val + 1 ∧ (σ.symm x).val < j.val + 1) →
    (x.val < i.val ∧ (σ.symm x).val < j.val + 1)) ↔ _
  push Not
  constructor
  · rintro ⟨x, hx, hn⟩
    have he : x = i := Fin.ext (by omega)
    subst x
    change (σ.symm i).val ≤ j.val
    omega
  · intro h
    refine ⟨i, ⟨by omega, ?_⟩, by omega⟩
    change (σ.symm i).val ≤ j.val at h
    omega

/-- Coordinate flags give the inverse of the reindexing permutation as the
first-appearance function. -/
theorem jhFun_jhFlag {n : ℕ} (b : Basis (Fin n) K V) (σ : Equiv.Perm (Fin n)) :
    jhFun n (jhFlag b) (jhFlag (b.reindex σ.symm)) = σ.symm := by
  funext i
  have hm : σ.symm i ∈ Finset.univ.filter (fun j : Fin n =>
      finrank K ↥((jhFlag b).nth i.val ⊓ (jhFlag (b.reindex σ.symm)).nth (j.val + 1)) <
        finrank K ↥((jhFlag b).nth (i.val + 1) ⊓ (jhFlag (b.reindex σ.symm)).nth (j.val + 1))) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, jhFlag_rank_jump, le_refl]
  rw [jhFun, dite_eq_left ⟨_, hm⟩]
  apply (Finset.min'_eq_iff _ _ _).2
  exact ⟨hm, fun j hj => (jhFlag_rank_jump b σ i j).1 (Finset.mem_filter.1 hj).2⟩

theorem jh_jhFlag {n : ℕ} (b : Basis (Fin n) K V) (σ : Equiv.Perm (Fin n)) :
    jh n (jhFlag b) (jhFlag (b.reindex σ.symm)) = σ := by
  rw [jh, jhFun_jhFlag, dite_eq_left σ.symm.bijective]
  apply Equiv.ext
  intro i
  exact σ.symm_apply_eq.mp ((Equiv.ofBijective _ σ.symm.bijective).apply_symm_apply i)

/-- Splitting off a line from two chains. The first chain is ordered by the basis;
the second consists of coordinate subspaces for that same basis. This is the
linear-algebra construction underlying the adapted-basis assertion of Proposition 1.10. -/
theorem jh_common_basis (K : Type*) [Field K] :
    ∀ (d : ℕ) (V : Type _) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    finrank K V = d →
    ∀ C D : Finset (Submodule K V), IsChain (· ≤ ·) (C : Set (Submodule K V)) →
      IsChain (· ≤ ·) (D : Set (Submodule K V)) → ⊤ ∈ C → ⊥ ∈ D →
    ∃ b : Basis (Fin d) K V,
      (∀ A ∈ C, ∃ k, b.flag k = A) ∧
      (∀ A ∈ D, ∃ s : Set (Fin d), A = Submodule.span K (b '' s)) := by
  intro d
  induction d with
  | zero =>
    intro V _ _ _ hd C D hC hD htop hbot
    have : Subsingleton V := Module.finrank_zero_iff.1 hd
    refine ⟨Basis.empty V, (fun A _ => ⟨0, Subsingleton.elim _ _⟩), ?_⟩
    intro A _
    exact ⟨∅, Subsingleton.elim _ _⟩
  | succ d ih =>
    intro V _ _ _ hd C D hC hD htop hbot
    have htop0 : (⊤ : Submodule K V) ≠ ⊥ := by
      intro h
      have : finrank K V = 0 := by
        simpa using congrArg (fun S : Submodule K V => finrank K S) h
      omega
    obtain ⟨A₀, hA₀, hmin⟩ := Finset.exists_min_image (C.filter (· ≠ ⊥))
      (fun A => finrank K A) ⟨⊤, Finset.mem_filter.2 ⟨htop, htop0⟩⟩
    obtain ⟨hA₀C, hA₀0⟩ := Finset.mem_filter.1 hA₀
    have hle : ∀ A ∈ C, A ≠ ⊥ → A₀ ≤ A := by
      intro A hA hA0
      by_cases he : A = A₀
      · exact he ▸ le_rfl
      rcases hC hA₀C hA (Ne.symm he) with h | h
      · exact h
      · exact (Submodule.eq_of_le_of_finrank_eq h
          (le_antisymm (Submodule.finrank_mono h)
            (hmin A (Finset.mem_filter.2 ⟨hA, hA0⟩)))).ge
    obtain ⟨v, hvA, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA₀0
    obtain ⟨B, hBD, hmax⟩ := Finset.exists_max_image (D.filter (fun A => v ∉ A))
      (fun A => finrank K A) ⟨⊥, Finset.mem_filter.2 ⟨hbot, by simpa using hv0⟩⟩
    obtain ⟨hBD, hvB⟩ := Finset.mem_filter.1 hBD
    have hBle : ∀ A ∈ D, v ∉ A → A ≤ B := by
      intro A hA hv
      by_cases he : A = B
      · exact he ▸ le_rfl
      rcases hD hA hBD he with h | h
      · exact h
      · exact (Submodule.eq_of_le_of_finrank_eq h
          (le_antisymm (Submodule.finrank_mono h)
            (hmax A (Finset.mem_filter.2 ⟨hA, hv⟩)))).ge
    have hdis : Disjoint B (Submodule.span K {v}) := by
      rw [disjoint_iff_inf_le]
      rintro x ⟨hxB, hxv⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hxv
      by_cases ha : a = 0
      · simp [ha]
      · exact (hvB ((Submodule.smul_mem_iff _ ha).1 hxB)).elim
    obtain ⟨H, hBH, hH'⟩ := hdis.exists_isCompl
    have hH := hH'.symm
    have hdim : finrank K H = d := by
      have hh := Submodule.finrank_add_eq_of_isCompl hH
      rw [finrank_span_singleton hv0] at hh
      omega
    have chain (E : Finset (Submodule K V)) (hE : IsChain (· ≤ ·) (E : Set (Submodule K V))) :
        IsChain (· ≤ ·) ((E.image (Submodule.comap H.subtype) : Finset (Submodule K H)) :
          Set (Submodule K H)) := by
      rw [Finset.coe_image]
      exact hE.image_of_map_rel (· ≤ ·) (· ≤ ·) _ (fun _ _ h => Submodule.comap_mono h)
    obtain ⟨bH, hbC, hbD⟩ := ih H hdim
      (C.image (Submodule.comap H.subtype)) (D.image (Submodule.comap H.subtype))
      (chain C hC) (chain D hD)
      (by simpa using Finset.mem_image_of_mem (Submodule.comap H.subtype) htop)
      (by simpa using Finset.mem_image_of_mem (Submodule.comap H.subtype) hbot)
    have hli : ∀ a : K, ∀ x ∈ H, a • v + x = 0 → a = 0 := by
      intro a x hx hax
      have hav : a • v ∈ Submodule.span K {v} :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
      have havH : a • v ∈ H := by
        rw [eq_neg_of_add_eq_zero_left hax]
        exact H.neg_mem hx
      have hz : a • v = 0 := hH.disjoint.le_bot ⟨hav, havH⟩
      exact (smul_eq_zero.1 hz).resolve_right hv0
    have hsp : ∀ z : V, ∃ a : K, z + a • v ∈ H := by
      intro z
      have hz : z ∈ Submodule.span K {v} ⊔ H := by rw [hH.sup_eq_top]; trivial
      obtain ⟨l, hl, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hl
      exact ⟨-a, by simpa using hw⟩
    let b := Basis.mkFinCons v bH hli hsp
    refine ⟨b, ?_, ?_⟩
    · intro A hA
      by_cases hA0 : A = ⊥
      · exact ⟨0, by rw [Basis.flag_zero, hA0]⟩
      obtain ⟨k, hk⟩ := hbC _ (Finset.mem_image_of_mem _ hA)
      have hvle : Submodule.span K {v} ≤ A :=
        Submodule.span_singleton_le_iff_mem _ _ |>.2 (hle A hA hA0 hvA)
      refine ⟨k.succ, ?_⟩
      rw [flag_cons_eq, hk, Submodule.map_comap_subtype, ← sup_inf_assoc_of_le _ hvle,
        hH.sup_eq_top, top_inf_eq]
    · intro A hA
      obtain ⟨s, hs⟩ := hbD _ (Finset.mem_image_of_mem _ hA)
      have he : Submodule.span K (b '' (Fin.succ '' s)) = H ⊓ A := by
        rw [← Submodule.map_comap_subtype, hs, Submodule.map_span]
        congr 1
        simp only [Set.image_image, b, Basis.coe_mkFinCons, Fin.cons_succ,
          Function.comp_apply, Submodule.coe_subtype]
      by_cases hv : v ∈ A
      · refine ⟨insert 0 (Fin.succ '' s), ?_⟩
        rw [Set.image_insert_eq, Submodule.span_insert, he]
        simp only [b, Basis.coe_mkFinCons, Fin.cons_zero]
        rw [← sup_inf_assoc_of_le _ (Submodule.span_singleton_le_iff_mem _ _ |>.2 hv),
          hH.sup_eq_top, top_inf_eq]
      · exact ⟨Fin.succ '' s, by rw [he, inf_eq_right.2 ((hBle A hA hv).trans hBH)]⟩

theorem jhFlag_eq_of_spans {n : ℕ} (b : Basis (Fin n) K V) (F : Flag K V)
    (hF : F.IsComplete) (hn : finrank K V = n)
    (hb : ∀ A ∈ F.carrier, ∃ k, b.flag k = A) : F = jhFlag b := by
  apply Flag.ext
  apply Finset.eq_of_subset_of_card_le
  · intro A hA
    obtain ⟨k, hk⟩ := hb A hA
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩
  · change (Finset.univ.image b.flag).card ≤ F.carrier.card
    rw [Finset.card_image_of_injective _ b.flag_strictMono.injective,
      Finset.card_univ, Fintype.card_fin, Flag.card_eq_len_succ, hF, hn]

/-- The `i`-th member of a complete flag has dimension `i`. -/
theorem jh_finrank_nth {n : ℕ} (F : Flag K V) (hF : F.IsComplete)
    (hn : finrank K V = n) (i : Fin (n + 1)) : finrank K (F.nth i.val) = i.val := by
  obtain ⟨b, hb⟩ := exists_adapted_basis K n V hn F.carrier F.isChain
  rw [jhFlag_eq_of_spans b F hF hn hb, jhFlag_nth, finrank_flag]

/-- Two complete flags admit a common basis, with the second flag obtained by
permuting its vectors. -/
theorem jh_exists_common_permutation (n : ℕ) (hn : finrank K V = n)
    (F G : Flag K V) (hF : F.IsComplete) (hG : G.IsComplete) :
    ∃ (b : Basis (Fin n) K V) (σ : Equiv.Perm (Fin n)),
      F = jhFlag b ∧ G = jhFlag (b.reindex σ.symm) := by
  obtain ⟨b, hbF, hbG⟩ := jh_common_basis K n V hn F.carrier G.carrier
    F.isChain G.isChain F.top_mem G.bot_mem
  have hFeq := jhFlag_eq_of_spans b F hF hn hbF
  have hlen : G.len = n := hG.trans hn
  have hm (i : Fin n) : ∃ a : Fin n, b a ∈ G.nth (i.val + 1) ∧ b a ∉ G.nth i.val := by
    have hlt : G.nth i.val < G.nth (i.val + 1) :=
      G.nth_lt_nth (by omega) (by rw [Flag.card_eq_len_succ, hlen]; omega)
    obtain ⟨s, hs⟩ := hbG _ ((G.nth_mem (i := i.val + 1) (by rw [Flag.card_eq_len_succ, hlen]; omega)).1)
    by_contra h
    push Not at h
    have hle : G.nth (i.val + 1) ≤ G.nth i.val := by
      rw [hs]
      apply Submodule.span_le.2
      rintro _ ⟨a, ha, rfl⟩
      exact h a (by rw [hs]; exact Submodule.subset_span ⟨a, ha, rfl⟩)
    exact hlt.not_ge hle
  choose f hf using hm
  have hordered (i j : Fin n) (h : i < j) : f i ≠ f j := by
    intro he
    have hle : G.nth (i.val + 1) ≤ G.nth j.val :=
      G.nth_mono (by change i.val < j.val at h; omega)
        (by rw [Flag.card_eq_len_succ, hlen]; omega)
    exact (hf j).2 (he ▸ hle (hf i).1)
  have hfi : Function.Injective f := by
    intro i j he
    rcases lt_trichotomy i j with h | h | h
    · exact (hordered i j h he).elim
    · exact h
    · exact (hordered j i h he.symm).elim
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f
    ⟨hfi, (Finite.injective_iff_surjective).1 hfi⟩
  have hc (i : Fin (n + 1)) : (b.reindex σ.symm).flag i = G.nth i.val := by
    have hle : (b.reindex σ.symm).flag i ≤ G.nth i.val := by
      apply ((b.reindex σ.symm).flag_le_iff).2
      intro j hj
      have hj' : j.val < i.val := hj
      have hji : G.nth (j.val + 1) ≤ G.nth i.val :=
        G.nth_mono (by omega) (by rw [Flag.card_eq_len_succ, hlen]; omega)
      have he : (b.reindex σ.symm) j = b (f j) := by
        simp only [Basis.reindex_apply, Equiv.symm_symm]
        rfl
      rw [he]
      exact hji (hf j).1
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_flag, jh_finrank_nth G hG hn]
  refine ⟨b, σ, hFeq, ?_⟩
  apply Flag.ext
  apply Finset.eq_of_subset_of_card_le
  · intro A hA
    have hi : G.index A < n + 1 := by
      have := G.index_lt_card hA
      rwa [Flag.card_eq_len_succ, hlen] at this
    refine Finset.mem_image.2 ⟨⟨G.index A, hi⟩, Finset.mem_univ _, ?_⟩
    rw [hc, G.nth_index hA]
  · change (Finset.univ.image (b.reindex σ.symm).flag).card ≤ G.carrier.card
    rw [Finset.card_image_of_injective _ (b.reindex σ.symm).flag_strictMono.injective,
      Finset.card_univ, Fintype.card_fin, Flag.card_eq_len_succ, hlen]

/-- The three assertions used in Proposition 1.10. -/
theorem jh_characterization (n : ℕ) (hn : finrank K V = n)
    (F G : Flag K V) (hF : F.IsComplete) (hG : G.IsComplete) :
    (∀ g : V ≃ₗ[K] V, jh n (g • F) (g • G) = jh n F G) ∧
    (∃ b : Basis (Fin n) K V, Flag.IsAdapted b F ∧ Flag.IsAdapted (b.reindex (jh n F G).symm) G) ∧
    (∀ σ : Equiv.Perm (Fin n),
      (∃ b : Basis (Fin n) K V, Flag.IsAdapted b F ∧ Flag.IsAdapted (b.reindex σ.symm) G) → σ = jh n F G) := by
  refine ⟨jh_smul n F G, ?_, ?_⟩
  · obtain ⟨b, σ, rfl, rfl⟩ := jh_exists_common_permutation n hn F G hF hG
    rw [jh_jhFlag]
    exact ⟨b, jhFlag_adapted b, jhFlag_adapted _⟩
  · rintro σ ⟨b, hbF, hbG⟩
    rw [jhFlag_eq_of_adapted b F hF hn hbF,
      jhFlag_eq_of_adapted (b.reindex σ.symm) G hG hn hbG, jh_jhFlag]

end LinearAlgebra
/-- The standard-flag consequence of the coordinate calculation. -/
theorem jh_std_perm (F : Type) [Field F] [Fintype F] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    jh n (stdFlag F n) (permToGL F σ • stdFlag F n) = σ := by
  rw [permToGL_smul_stdFlag, stdFlag_eq_flagOf]
  exact jh_jhFlag (Pi.basisFun F (Fin n)) σ

end MartinPhd

end
end Jh
