import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Chapter 2 (the coalgebra L: Sections 2.1–2.8)

Contents:
* ArrAux
* WordAux
* Species
* Cobar
* Arrangements
* Salvetti
* Topology
* E1
* H1
-/

section ArrAux

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Helper lemmas for hyperplane arrangements (§2.3)
-/

open scoped BigOperators

noncomputable section

namespace MartinPhd

lemma sign_add_smul_eq_sign_of_lt (u v : ℝ) (hu : u ≠ 0) {ε : ℝ} (hεpos : 0 < ε)
    (hε : ε < |u| / (|v| + 1)) : SignType.sign (u + ε * v) = SignType.sign u := by
  have hvpos : 0 < |v| + 1 := by positivity
  have hmul : ε * (|v| + 1) < |u| := by
    rwa [lt_div_iff₀ hvpos] at hε
  have hle : ε * |v| ≤ ε * (|v| + 1) := by
    nlinarith [abs_nonneg v]
  have hbound : |ε * v| < |u| := by
    rw [abs_mul, abs_of_pos hεpos]
    exact hle.trans_lt hmul
  rcases lt_trichotomy u 0 with hu_neg | rfl | hu_pos
  · rw [sign_neg hu_neg]
    have : u + ε * v < 0 := by
      have : ε * v ≤ |ε * v| := le_abs_self (ε * v)
      rw [abs_of_neg hu_neg] at hbound
      linarith
    exact sign_neg this
  · exact False.elim (hu rfl)
  · rw [sign_pos hu_pos]
    have : 0 < u + ε * v := by
      have : -|ε * v| ≤ ε * v := neg_abs_le (ε * v)
      rw [abs_of_pos hu_pos] at hbound
      linarith
    exact sign_pos this

lemma sign_add_smul_eq_sign_of_zero (v : ℝ) {ε : ℝ} (hεpos : 0 < ε) :
    SignType.sign (0 + ε * v) = SignType.sign v := by
  rw [zero_add, sign_mul, sign_pos hεpos, one_mul]

lemma sign_add_smul_eq_tits (u v : ℝ) {ε : ℝ} (hεpos : 0 < ε)
    (hε : ε < if u = 0 then 1 else |u| / (|v| + 1)) :
    SignType.sign (u + ε * v) = if SignType.sign u ≠ 0 then SignType.sign u else SignType.sign v := by
  by_cases hu : u = 0
  · simp only [hu, ite_true] at hε
    rw [hu, zero_add, sign_mul, sign_pos hεpos, one_mul, sign_zero]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  · simp only [hu, ite_false] at hε
    have hne : SignType.sign u ≠ 0 := by rwa [ne_eq, sign_eq_zero_iff]
    simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
    exact sign_add_smul_eq_sign_of_lt u v hu hεpos hε

end MartinPhd

end
end ArrAux

section WordAux

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.
-/

namespace MartinPhd

namespace LinOrd

lemma length_filter_le_of_imp (l : List ℕ) {p q : ℕ → Bool} (h : ∀ z, p z → q z) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons, List.filter_cons]
    split_ifs with hp hq
    · simp only [List.length_cons]
      exact Nat.succ_le_succ ih
    · exfalso
      have : q a := h a hp
      exact hq this
    · simp only [List.length_cons]
      exact Nat.le_succ_of_le ih
    · exact ih

lemma length_filter_lt_length {w : List ℕ} (hnd : w.Nodup) {x : ℕ} (hx : x ∈ w) :
    (w.filter (· < x)).length < w.length := by
  induction w with
  | nil => cases hx
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
    cases List.mem_cons.mp hx with
    | inl hxa =>
      subst hxa
      rw [List.filter_cons]
      have : ¬ (x < x) := lt_irrefl x
      simp only [decide_eq_true_eq, this, ↓reduceIte, List.length_cons]
      have : (l.filter (· < x)).length ≤ l.length := List.length_filter_le _ _
      linarith
    | inr hxl =>
      rw [List.filter_cons]
      split_ifs with hax
      · simp only [List.length_cons]
        have := ih hl hxl
        linarith
      · simp only [List.length_cons]
        have : (l.filter (· < x)).length ≤ l.length := List.length_filter_le _ _
        linarith

lemma length_filter_lt_length_filter {w : List ℕ} (hnd : w.Nodup) {x y : ℕ}
    (hx : x ∈ w) (hxy : x < y) :
    (w.filter (· < x)).length < (w.filter (· < y)).length := by
  induction w with
  | nil => cases hx
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
    cases List.mem_cons.mp hx with
    | inl hxa =>
      subst hxa
      rw [List.filter_cons, List.filter_cons]
      have h1 : ¬ (x < x) := lt_irrefl x
      simp only [decide_eq_true_eq, h1, hxy, ↓reduceIte, List.length_cons]
      have hle : (l.filter (· < x)).length ≤ (l.filter (· < y)).length :=
        length_filter_le_of_imp l fun z hz =>
          decide_eq_true (lt_trans (of_decide_eq_true hz) hxy)
      linarith
    | inr hxl =>
      rw [List.filter_cons, List.filter_cons]
      have ih' := ih hl hxl
      split_ifs with hax hay
      · simp only [List.length_cons]
        linarith
      · exfalso
        exact hay (decide_eq_true (lt_trans (of_decide_eq_true hax) hxy))
      · simp only [List.length_cons]
        linarith
      · exact ih'

theorem std_perm_range' {w : List ℕ} (hnd : w.Nodup) (_hne : w ≠ []) :
    (w.map fun x => (w.filter (· < x)).length + 1).Perm (List.range' 1 w.length) := by
  let f := fun x => (w.filter (· < x)).length + 1
  have hnodup : (w.map f).Nodup := by
    apply List.Nodup.map_on (fun x hx y hy hfeq => ?_) hnd
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have := length_filter_lt_length_filter hnd hx hlt
      have : f x < f y := by dsimp [f]; linarith
      exact ne_of_lt this hfeq
    · have := length_filter_lt_length_filter hnd hy hgt
      have : f y < f x := by dsimp [f]; linarith
      exact ne_of_gt this hfeq
  have hsub : w.map f ⊆ List.range' 1 w.length := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨x, hx, rfl⟩
    have hlt := length_filter_lt_length hnd hx
    rw [List.mem_range'_1]
    dsimp [f]
    constructor
    · linarith
    · linarith
  have hsp := List.subperm_of_subset hnodup hsub
  have hlen : (List.range' 1 w.length).length ≤ (w.map f).length := by
    simp [List.length_range']
  exact hsp.perm_of_length_le hlen

end LinOrd

end MartinPhd

end WordAux

section Species

/-
Outline of

  Fernando Daniel Martin, *Aspectos homológicos de la teoría de especies*,
  PhD thesis, Universidad de Buenos Aires, 2024 (advisor: M. Suárez-Álvarez).

# Chapter 2 — La cohomología de la especie de órdenes lineales (§2.1–2.2)

Outline pass: definitions and statements with the thesis numbering; proofs are `sorry`.

## Modelling choices

* A (combinatorial) **species** is a functor `Core FintypeCat ⥤ ModuleCat k`. The thesis asks for
  finite-dimensional values; as in Chapter 1 we drop that.
* The Cauchy product, its monoidal structure, and the coalgebra structures on `L` and `e` are
  recorded with their defining formulas; the functoriality proofs and the monoidal
  coherence are deferred (`sorry`) in this outline.
-/

open scoped TensorProduct BigOperators
open CategoryTheory MonoidalCategory

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

namespace Sp

variable (k : Type) [Field k]

/-- The category of combinatorial species: functors from the groupoid of finite sets and
bijections to `k`-vector spaces. -/
def Species : Type 1 := Core FintypeCat.{0} ⥤ ModuleCat.{0} k

instance : Category.{1} (Species k) :=
  inferInstanceAs (Category (Core FintypeCat.{0} ⥤ ModuleCat.{0} k))

variable {k}

/-- The value `x(A)` of a species on a finite set. -/
def Species.ev (x : Species k) (A : FintypeCat.{0}) : ModuleCat.{0} k :=
  (show Core FintypeCat.{0} ⥤ ModuleCat.{0} k from x).obj ⟨A⟩

/-- The action `x(f) : x(A) → x(B)` of a bijection `f : A ≃ B`. -/
def Species.mapBij (x : Species k) {A B : FintypeCat.{0}} (f : A ≃ B) : x.ev A →ₗ[k] x.ev B :=
  ((show Core FintypeCat.{0} ⥤ ModuleCat.{0} k from x).map (X := ⟨A⟩) (Y := ⟨B⟩)
    ⟨(FintypeCat.equivEquivIso f)⟩).hom

/-- Value of the **Cauchy product** `(x ⊗ y)(A) = ⨁_{B ⊆ A} x(B) ⊗ y(A \ B)`. -/
abbrev Species.cauchyObj (x y : Species k) (A : FintypeCat.{0}) : Type :=
  DirectSum (Set A.obj) fun B => x.ev (@FintypeCat.of ↥B (by
      haveI : Finite A.obj := A.property; infer_instance)) ⊗[k]
    y.ev (@FintypeCat.of ↥Bᶜ (by haveI : Finite A.obj := A.property; infer_instance))

/-- The Cauchy product of species, acting on a bijection `f` by
`∑_C x(f|_C) ⊗ y(f|_{A∖C})`. (Functoriality deferred.) -/
def cauchy (x y : Species k) : Species k := sorry

/-- The unit `1`: `k` on the empty set and `0` elsewhere. -/
def one : Species k := sorry

/-- The Cauchy product makes `Sp` a monoidal category, **symmetric** unlike the `GL` case
(coherence deferred). -/
axiom instMonoidalCategorySpecies (k : Type) [Field k] : MonoidalCategory (Species k)
attribute [instance] instMonoidalCategorySpecies

instance : SymmetricCategory (Species k) := sorry

/-- A species is **concentrated in cardinal `n`** if it vanishes on all other cardinals. -/
def IsConcentrated (x : Species k) (n : ℕ) : Prop :=
  ∀ A : FintypeCat.{0}, Nat.card A.obj ≠ n → Subsingleton (x.ev A)

/-- **Lemma 2.1.** If `x` is concentrated in cardinal `n` and `y` is arbitrary,
`Hom_Sp(x, y) ∋ f ↦ f([n]) ∈ Hom_{S_n}(x([n]), y([n]))` is a natural isomorphism. -/
theorem lemma_2_1 (x y : Species k) (n : ℕ) (hx : IsConcentrated x n) :
    Nonempty ((x ⟶ y) ≃ {f : x.ev (FintypeCat.of (Fin n)) →ₗ[k] y.ev (FintypeCat.of (Fin n)) //
      ∀ σ : Equiv.Perm (Fin n), f ∘ₗ Species.mapBij x σ = Species.mapBij y σ ∘ₗ f}) := sorry

/-! ## §2.2 The coalgebra `L` of linear orders -/

/-- The species `L` of **linear orders**: `L(A)` is free on the set of total orders on `A`;
a bijection transports orders. -/
def L : Species k :=
  { obj := fun A => ModuleCat.of k (LinearOrder A.of →₀ k)
    map := fun f => sorry
    map_id := sorry
    map_comp := sorry : Core FintypeCat.{0} ⥤ ModuleCat.{0} k }

/-- The comultiplication `Δ(A)(z) = ∑_{B ⊆ A} z|_B ⊗ z|_{A∖B}` of `L`. -/
def L.comul : (L : Species k) ⟶ L ⊗ L := sorry

/-- The counit: the only nonzero component sends the unique order on `∅` to `1`. -/
def L.counit : (L : Species k) ⟶ 𝟙_ (Species k) := sorry

/-- `L` is a coalgebra in `Sp`. -/
instance : ComonObj (L : Species k) where
  counit := L.counit
  comul := L.comul
  counit_comul := sorry
  comul_counit := sorry
  comul_assoc := sorry

/-- The **exponential species** `e`: `e(A) = k` for every finite set, with
`Δ(e_A) = ∑_{B ⊆ A} e_B ⊗ e_{A∖B}`. -/
def expSp : Species k := (Functor.const (Core FintypeCat.{0})).obj (ModuleCat.of k k)

instance : ComonObj (expSp : Species k) where
  counit := sorry
  comul := sorry
  counit_comul := sorry
  comul_counit := sorry
  comul_assoc := sorry

/-- A coalgebra in `Sp` is **connected** if `c(∅) ≅ k`. -/
def IsConnected (c : Species k) : Prop := Nonempty (c.ev (FintypeCat.of PEmpty) ≃ₗ[k] k)

/-- `L` and `e` are connected. -/
theorem isConnected_L : IsConnected (L : Species k) := by
  letI : Subsingleton (LinearOrder PEmpty) := ⟨fun a b => by
    apply LinearOrder.ext
    intro x
    exact PEmpty.elim x⟩
  letI : LinearOrder PEmpty := inferInstance
  exact ⟨Finsupp.uniqueLinearEquiv k k (inferInstance : LinearOrder PEmpty)⟩

theorem isConnected_exp : IsConnected (expSp : Species k) := by
  exact ⟨LinearEquiv.refl k k⟩

end Sp

end MartinPhd

end
end Species

section Cobar

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 2 — §2.2 (continued): the cobar construction of `L` and the page `E₁`

The filtered cobar construction `C•(x) = Hom_Sp(x, L̄^{⊗•})` of an `L`-bicomodule `x`, its
spectral sequence `E(x)` (Lemma 2.5, Corollary 2.4) and the identification
`E₁^{p,q}(L) ≅ H^q(Σ_p^•[p])` (Lemma 2.6).

## Modelling choices

* Mathlib has no spectral sequences, and the `Sp`-level cobar complex needs the bicomodule
  categories over `L`. The outline takes the combinatorial complex `Σ_p^•` of `S_p`-modules
  (basis: ordered partitions of `[p]` into nonempty *ordered* blocks) as the primary object, and
  *defines* `E₁^{p,q}(L) := H^{p+q}(Σ_p^•)`, which is Lemma 2.6.
* **Theorem 2.3** ([McC85, Thm 3.2]: a filtered differential graded module with exhaustive and
  weakly convergent filtration has a convergent spectral sequence) and **Corollary 2.4**
  (the spectral sequence `E(x)` converges to `H•(x)`) are cited facts about spectral sequences
  and are not stated.
-/

open scoped TensorProduct BigOperators

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

namespace Sp

variable (k : Type) [Field k]

/-- A basis element of `L̄^{⊗n}([p])`: an ordered partition of `[p]` into `n` nonempty blocks,
each block totally ordered (a list). -/
def OPart (p n : ℕ) : Type :=
  {b : List (List (Fin p)) // b.length = n ∧ (∀ l ∈ b, l ≠ []) ∧ b.flatten.Perm (List.finRange p)}

/-- The `n`-th cochain module `Σ_p^n = L̄^{⊗n}([p])` of the complex `Σ_p^•`. -/
abbrev SigmaC (p n : ℕ) : Type := OPart p n →₀ k

/-- The splittings of a block `l` into two nonempty complementary subwords:
`Δ(l) = ∑_{∅ ⊊ B ⊊ l} l|_B ⊗ l|_{l∖B}`. -/
def splits {α : Type} (l : List α) : Finset (List α × List α) :=
  (l.toFinset.powerset.filter fun S => S ≠ ∅ ∧ S ≠ l.toFinset).image fun S =>
    (l.filter (· ∈ S), l.filter (· ∉ S))

/-- The `i`-th coface `∂ⁱ = id^{⊗ i-1} ⊗ Δ ⊗ id^{⊗ n-i}` (2.3): split the `i`-th block. -/
def cofaceSigma (p n : ℕ) (i : ℕ) : SigmaC k p n →ₗ[k] SigmaC k p (n + 1) := sorry

/-- The differential `δ = ∑_{i=1}^{n} (-1)^i ∂ⁱ` of `Σ_p^•`. -/
def deltaSigma (p n : ℕ) : SigmaC k p n →ₗ[k] SigmaC k p (n + 1) :=
  ∑ i ∈ Finset.Icc 1 n, ((-1 : k) ^ i) • cofaceSigma k p n i

/-- `δ ∘ δ = 0`. -/
theorem deltaSigma_comp (p n : ℕ) : deltaSigma k p (n + 1) ∘ₗ deltaSigma k p n = 0 := sorry

/-- The incoming differential `Σ_p^{n-1} → Σ_p^n` (zero for `n = 0`). -/
def deltaIn (p : ℕ) : ∀ n, SigmaC k p (n - 1) →ₗ[k] SigmaC k p n
  | 0 => 0
  | m + 1 => deltaSigma k p m

/-- The cohomology `H^n(Σ_p^•)` of the complex of `S_p`-modules. -/
abbrev HSigma (p n : ℕ) : Type :=
  LinearMap.ker (deltaSigma k p n) ⧸
    (LinearMap.range (deltaIn k p n)).comap (LinearMap.ker (deltaSigma k p n)).subtype

/-- The action of `S_p` on `Σ_p^n` by relabelling. -/
instance (p n : ℕ) : Module (MonoidAlgebra k (Equiv.Perm (Fin p))) (SigmaC k p n) := sorry

/-- **Lemma 2.6.** The `(p, q)` spot of the first page of the spectral sequence of `L` is
`E₁^{p,q}(L) ≅ H^q(Σ_p^•[p]) = H^{p+q}(Σ_p^•)`; we take this as the definition of
`E₁^{p,q}(L)`. Lemma 2.2 (`C•(x) ≅ Hom_Sp(x, −)(L̄^{⊗•})` for trivial bicomodules) and Lemma 2.5
(`C•(x_p)[p] ≅ E₀^{p,•}(x)`) are the steps of its proof in the thesis. -/
abbrev E1L (p : ℕ) (q : ℤ) : Type := HSigma k p (p + q).toNat

end Sp

end MartinPhd

end
end Cobar

section Arrangements

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 2 — §2.3 Hyperplane arrangements, §2.4 The braid arrangement

## Modelling choices

* A central real arrangement is given by a family of nonzero linear forms `f_i : V → ℝ`
  (hyperplanes `ker f_i`). A **face** is a nonempty set of points with a given *sign vector*
  `(sign f_i(x))_i`; **chambers** are the faces with no zero sign. This is the standard
  equivalent description of the faces of §2.3 as the chambers of the restrictions `A_X`
  (Tits' cone description).
* The **Tits product** `PQ` has sign vector `s(PQ)_i = s(P)_i` if `s(P)_i ≠ 0` and `s(Q)_i`
  otherwise, which is the face containing `x + εy`.
-/

open scoped BigOperators

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §2.3 Hyperplane arrangements -/

/-- A central real hyperplane arrangement in `V`, given by indexed nonzero linear forms. -/
structure Arrangement (ι : Type) (V : Type) [AddCommGroup V] [Module ℝ V] where
  form : ι → V →ₗ[ℝ] ℝ
  form_ne_zero : ∀ i, form i ≠ 0

namespace Arrangement

variable {ι : Type} {V : Type} [AddCommGroup V] [Module ℝ V] (A : Arrangement ι V)

/-- The sign vector of a point. -/
def signs (x : V) : ι → SignType := fun i => SignType.sign (A.form i x)

/-- The **faces** of `A`: realized sign vectors. -/
def Face : Type := {s : ι → SignType // ∃ x, A.signs x = s}

/-- The **chambers** of `A`: faces with no zero sign. -/
def Chamber : Type := {P : A.Face // ∀ i, P.1 i ≠ 0}

/-- `P ≤ Q`: `P` is a face of `Q` (`P` lies in the closure of `Q`). -/
instance : LE A.Face := ⟨fun P Q => ∀ i, P.1 i = 0 ∨ P.1 i = Q.1 i⟩

@[refl]
theorem le_refl (P : A.Face) : P ≤ P := fun _ => Or.inr rfl

theorem le_trans {P Q R : A.Face} (hPQ : P ≤ Q) (hQR : Q ≤ R) : P ≤ R := by
  intro i
  rcases hPQ i with hP0 | hPQeq
  · left; exact hP0
  · rcases hQR i with hQ0 | hQReq
    · left; rw [hPQeq, hQ0]
    · right; rw [hPQeq, hQReq]

theorem le_antisymm {P Q : A.Face} (hPQ : P ≤ Q) (hQP : Q ≤ P) : P = Q := by
  apply Subtype.ext
  funext i
  rcases hPQ i with hP0 | hPQeq
  · rcases hQP i with hQ0 | hQPeq
    · rw [hP0, hQ0]
    · rw [hP0, hQPeq, hP0]
  · exact hPQeq

/-- Under the thesis's hypothesis that the arrangement is finite (`[Finite ι]`), the
Tits product sign vector is realizable: there exists `ε > 0` such that `x + ε • y`
has the sign vector of `P Q`. -/
theorem titsProd_realizable [Finite ι] (x y : V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, SignType.sign (A.form i (x + ε • y)) =
      if SignType.sign (A.form i x) ≠ 0 then SignType.sign (A.form i x)
      else SignType.sign (A.form i y) := by
  have hpos (i : ι) : 0 < if A.form i x = 0 then (1 : ℝ) else |A.form i x| / (|A.form i y| + 1) := by
    split_ifs with h
    · exact zero_lt_one
    · exact div_pos (abs_pos.mpr h) (by positivity)
  have hlin (ε : ℝ) (i : ι) : A.form i (x + ε • y) = A.form i x + ε * A.form i y := by
    rw [map_add, LinearMap.map_smul, smul_eq_mul]
  have : Fintype ι := Fintype.ofFinite ι
  cases isEmpty_or_nonempty ι with
  | inl h_empty =>
    refine ⟨1, zero_lt_one, fun i => isEmptyElim i⟩
  | inr h_non =>
    let s : Finset ℝ := Finset.univ.image fun i =>
      if A.form i x = 0 then (1 : ℝ) else |A.form i x| / (|A.form i y| + 1)
    have hsnon : s.Nonempty := Finset.univ_nonempty.image _
    have hm_mem := Finset.min'_mem s hsnon
    rw [Finset.mem_image] at hm_mem
    rcases hm_mem with ⟨i₀, _, heq⟩
    have hm_pos : 0 < s.min' hsnon := by
      rw [← heq]
      exact hpos i₀
    refine ⟨s.min' hsnon / 2, half_pos hm_pos, fun i => ?_⟩
    rw [hlin]
    have hle : s.min' hsnon ≤ if A.form i x = 0 then (1 : ℝ) else |A.form i x| / (|A.form i y| + 1) :=
      Finset.min'_le s _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hlt : s.min' hsnon / 2 < if A.form i x = 0 then (1 : ℝ) else |A.form i x| / (|A.form i y| + 1) := by
      linarith
    exact sign_add_smul_eq_tits (A.form i x) (A.form i y) (half_pos hm_pos) hlt

/-- Realizability of the Tits product of two realized sign vectors when `ι` is finite. -/
theorem titsProd_exists [Finite ι] (P Q : A.Face) :
    ∃ z, A.signs z = fun i => if P.1 i ≠ 0 then P.1 i else Q.1 i := by
  rcases P.2 with ⟨x, hx⟩
  rcases Q.2 with ⟨y, hy⟩
  obtain ⟨ε, hεpos, hε⟩ := A.titsProd_realizable x y
  refine ⟨x + ε • y, ?_⟩
  rw [← hx, ← hy]
  exact funext hε

/-- The **Tits product** `PQ` of faces: `(PQ)_i = P_i` if `P_i ≠ 0` and `Q_i` otherwise.

**Note.** The thesis assumes arrangements are
finite (§2.3, p. 52: *un conjunto finito de hiperplanos*). The formalization omitted
`[Finite ι]` from `Arrangement`. Without finiteness of `ι`, the sign vector is not in
general realizable: in `V = ℝ²` with `ι = ℕ ∪ {∞}`, `f_∞(x₁, x₂) = x₁` and
`f_n(x₁, x₂) = x₁ + x₂ / (n + 1)`, the faces realized by `x = (0, 1)` and `y = (-1, 0)`
have Tits product requiring `z₁ < 0` and `z₂ > (n + 1)(-z₁)` for all `n ∈ ℕ`, which is
impossible by the Archimedean property of `ℝ`. Under `[Finite ι]`, realizability holds by
evaluating at `x + ε • y` for small `ε > 0` (see `Arrangement.titsProd_exists`). -/
def titsProd [Finite ι] (P Q : A.Face) : A.Face :=
  ⟨fun i => if P.1 i ≠ 0 then P.1 i else Q.1 i, A.titsProd_exists P Q⟩

instance [Finite ι] : Mul A.Face := ⟨titsProd A⟩

@[simp]
theorem mul_coe [Finite ι] (P Q : A.Face) (i : ι) :
    (P * Q).1 i = if P.1 i ≠ 0 then P.1 i else Q.1 i := rfl

/-- The Tits product is associative; faces form a left-regular band with the origin as unit. -/
instance [Finite ι] : Semigroup A.Face where
  mul_assoc P Q R := by
    apply Subtype.ext
    funext i
    simp only [mul_coe]
    by_cases hP : P.1 i = 0
    · simp only [hP, ne_eq, not_true_eq_false, ↓reduceIte]
    · simp only [hP, ne_eq, not_false_eq_true, ↓reduceIte]

/-- **Lemma 2.7** ([AM10, Prop. 10.1]). (1) Chambers form a right ideal: `Q` a chamber implies
`P Q` a chamber. -/
theorem chamber_rightIdeal [Finite ι] (P : A.Face) (Q : A.Chamber) : ∀ i, (P * Q.1).1 i ≠ 0 := by
  intro i
  simp only [mul_coe]
  by_cases hP : P.1 i = 0
  · simp only [hP, ne_eq, not_true_eq_false, ↓reduceIte]
    exact Q.2 i
  · simp only [hP, ne_eq, not_false_eq_true, ↓reduceIte]

/-- **Lemma 2.7** (2). `P ≤ P Q`. -/
theorem le_mul_self [Finite ι] (P Q : A.Face) : P ≤ P * Q := by
  intro i
  simp only [mul_coe]
  by_cases hP : P.1 i = 0
  · left; exact hP
  · right
    simp only [hP, ne_eq, not_false_eq_true, ↓reduceIte]

/-- **Lemma 2.7** (3). If `P ≤ Q` then `P Q = Q` and `Q P = Q`. -/
theorem mul_eq_of_le [Finite ι] (P Q : A.Face) (h : P ≤ Q) : P * Q = Q ∧ Q * P = Q := by
  constructor
  · apply Subtype.ext
    funext i
    simp only [mul_coe]
    rcases h i with h0 | heq
    · simp [h0]
    · rw [heq]
      split_ifs <;> rfl
  · apply Subtype.ext
    funext i
    simp only [mul_coe]
    rcases h i with h0 | heq
    · by_cases hQ : Q.1 i = 0 <;> simp [h0, hQ]
    · rw [heq]
      split_ifs <;> rfl

end Arrangement

/-! ## §2.4 The braid arrangement -/

/-- The **braid arrangement** `B_n` in `ℝⁿ`: hyperplanes `x_i = x_j` for `i < j`. -/
def braidArrangement (n : ℕ) : Arrangement {p : Fin n × Fin n // p.1 < p.2} (Fin n → ℝ) where
  form p := (LinearMap.proj p.1.1 : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj p.1.2
  form_ne_zero := by
    intro ⟨⟨i, j⟩, hij⟩ h
    have h1 : (((LinearMap.proj (R := ℝ) i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j) : (Fin n → ℝ) →ₗ[ℝ] ℝ) (Pi.single i (1 : ℝ)) = 0 := by
      rw [h]
      rfl
    have h2 : (((LinearMap.proj (R := ℝ) i : (Fin n → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j) : (Fin n → ℝ) →ₗ[ℝ] ℝ) (Pi.single i (1 : ℝ)) = 1 := by
      simp only [LinearMap.sub_apply, LinearMap.proj_apply]
      rw [Pi.single_eq_same]
      have : (Pi.single i (1 : ℝ) : Fin n → ℝ) j = 0 := by
        simp [hij.ne']
      rw [this, sub_zero]
    rw [h1] at h2
    exact one_ne_zero h2.symm

/-- The sign vector determines all strict comparisons between coordinates. -/
theorem braid_signs_lt_iff {n : ℕ} {x y : Fin n → ℝ}
    (h : (braidArrangement n).signs x = (braidArrangement n).signs y)
    (i j : Fin n) : x i < x j ↔ y i < y j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hs := congrFun h ⟨(i, j), hij⟩
    change SignType.sign (x i - x j) = SignType.sign (y i - y j) at hs
    rw [← sub_neg, ← sign_eq_neg_one_iff, hs, sign_eq_neg_one_iff, sub_neg]
  · simp
  · have hs := congrFun h ⟨(j, i), hji⟩
    change SignType.sign (x j - x i) = SignType.sign (y j - y i) at hs
    rw [← sub_pos, ← sign_eq_one_iff, hs, sign_eq_one_iff, sub_pos]

/-- Coordinate comparisons determine the braid sign vector. -/
theorem braid_signs_eq_of_lt_iff {n : ℕ} {x y : Fin n → ℝ}
    (h : ∀ i j, x i < x j ↔ y i < y j) :
    (braidArrangement n).signs x = (braidArrangement n).signs y := by
  funext ⟨⟨i, j⟩, hij⟩
  change SignType.sign (x i - x j) = SignType.sign (y i - y j)
  rcases lt_trichotomy (x i) (x j) with hlt | heq | hgt
  · rw [sign_neg (sub_neg.mpr hlt), sign_neg (sub_neg.mpr ((h i j).mp hlt))]
  · have hy : y i = y j := le_antisymm
      (le_of_not_gt (fun h' => (lt_irrefl _ (heq ▸ (h j i).mpr h'))))
      (le_of_not_gt (fun h' => (lt_irrefl _ (heq ▸ (h i j).mpr h'))))
    simp [heq, hy]
  · rw [sign_pos (sub_pos.mpr hgt), sign_pos (sub_pos.mpr ((h j i).mp hgt))]

/-- An **ordered (set) partition** of `[n]`: a list of nonempty, pairwise disjoint blocks
covering `[n]`. -/
def OSP (n : ℕ) : Type :=
  {b : List (Finset (Fin n)) // (∀ B ∈ b, B.Nonempty) ∧ b.Pairwise Disjoint ∧
    b.foldr (· ∪ ·) ∅ = Finset.univ}

section BraidFaces

variable {n : ℕ}

/-- The minimal elements of `S` for the preorder given by the coordinates of `x`. -/
def minSet (x : Fin n → ℝ) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter fun i => ∀ j ∈ S, ¬ x j < x i

theorem minSet_subset (x : Fin n → ℝ) (S : Finset (Fin n)) : minSet x S ⊆ S :=
  Finset.filter_subset _ _

theorem minSet_nonempty (x : Fin n → ℝ) {S : Finset (Fin n)} (hS : S.Nonempty) :
    (minSet x S).Nonempty := by
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image x hS
  exact ⟨i, Finset.mem_filter.2 ⟨hi, fun j hj => not_lt.2 (hmin j hj)⟩⟩

/-- The blocks of the weak order defined by `x` on `S`, from the smallest value up. -/
def blocksAux (x : Fin n → ℝ) (S : Finset (Fin n)) : List (Finset (Fin n)) :=
  if h : S.Nonempty then minSet x S :: blocksAux x (S \ minSet x S) else []
termination_by S.card
decreasing_by
  exact Finset.card_lt_card (Finset.sdiff_ssubset (minSet_subset x S) (minSet_nonempty x h))

theorem subset_foldr_union {l : List (Finset (Fin n))} {B : Finset (Fin n)} (hB : B ∈ l) :
    B ⊆ l.foldr (· ∪ ·) ∅ := by
  induction l with
  | nil => simp at hB
  | cons C l ih =>
    rcases List.mem_cons.1 hB with rfl | hB
    · exact Finset.subset_union_left
    · exact (ih hB).trans Finset.subset_union_right

theorem blocksAux_props (x : Fin n → ℝ) (S : Finset (Fin n)) :
    (∀ B ∈ blocksAux x S, B.Nonempty) ∧ (blocksAux x S).Pairwise Disjoint ∧
      (blocksAux x S).foldr (· ∪ ·) ∅ = S := by
  induction' hc : S.card using Nat.strong_induction_on with c ih generalizing S
  rw [blocksAux]
  split_ifs with h
  · have hlt : (S \ minSet x S).card < c :=
      hc ▸ Finset.card_lt_card (Finset.sdiff_ssubset (minSet_subset x S) (minSet_nonempty x h))
    obtain ⟨hne, hpw, hun⟩ := ih _ hlt (S \ minSet x S) rfl
    refine ⟨?_, ?_, ?_⟩
    · intro B hB
      rcases List.mem_cons.1 hB with rfl | hB
      · exact minSet_nonempty x h
      · exact hne B hB
    · rw [List.pairwise_cons]
      refine ⟨fun B hB => ?_, hpw⟩
      have hsub : B ⊆ S \ minSet x S := hun ▸ subset_foldr_union hB
      exact Finset.disjoint_of_subset_right hsub Finset.disjoint_sdiff
    · simp only [List.foldr_cons, hun]
      exact Finset.union_sdiff_of_subset (minSet_subset x S)
  · simp only [List.not_mem_nil, false_imp_iff, implies_true, List.Pairwise.nil, List.foldr_nil,
      true_and]
    exact (Finset.not_nonempty_iff_eq_empty.1 h).symm

theorem blocksAux_congr (x y : Fin n → ℝ) (S : Finset (Fin n))
    (h : ∀ i ∈ S, ∀ j ∈ S, x i < x j ↔ y i < y j) : blocksAux x S = blocksAux y S := by
  induction' hc : S.card using Nat.strong_induction_on with c ih generalizing S
  conv_lhs => rw [blocksAux]
  conv_rhs => rw [blocksAux]
  split_ifs with hS
  · have hmin : minSet x S = minSet y S := by
      ext i
      simp only [minSet, Finset.mem_filter]
      constructor
      · rintro ⟨hi, hm⟩
        exact ⟨hi, fun j hj hlt => hm j hj ((h j hj i hi).2 hlt)⟩
      · rintro ⟨hi, hm⟩
        exact ⟨hi, fun j hj hlt => hm j hj ((h j hj i hi).1 hlt)⟩
    rw [hmin]
    have hlt : (S \ minSet y S).card < c :=
      hc ▸ Finset.card_lt_card (Finset.sdiff_ssubset (minSet_subset y S) (hmin ▸ minSet_nonempty x hS))
    congr 1
    exact ih _ hlt (S \ minSet y S) (fun i hi j hj => h i (Finset.sdiff_subset hi) j
      (Finset.sdiff_subset hj)) rfl
  · rfl

/-- The point whose coordinates are the block indices of an ordered partition. -/
def ptList : List (Finset (Fin n)) → Fin n → ℝ
  | [], _ => 0
  | B :: l, i => if i ∈ B then 0 else 1 + ptList l i

theorem ptList_nonneg (l : List (Finset (Fin n))) (i : Fin n) : 0 ≤ ptList l i := by
  induction l with
  | nil => simp [ptList]
  | cons B l ih =>
    simp only [ptList]
    split_ifs
    · exact le_rfl
    · linarith [ih]

theorem cmp_blocksAux (x : Fin n → ℝ) (S : Finset (Fin n)) :
    ∀ i ∈ S, ∀ j ∈ S, x i < x j ↔ ptList (blocksAux x S) i < ptList (blocksAux x S) j := by
  induction' hc : S.card using Nat.strong_induction_on with c ih generalizing S
  intro i hi j hj
  have hS : S.Nonempty := ⟨i, hi⟩
  rw [blocksAux, dif_pos hS]
  have hlt : (S \ minSet x S).card < c :=
    hc ▸ Finset.card_lt_card (Finset.sdiff_ssubset (minSet_subset x S) (minSet_nonempty x hS))
  have IH := ih _ hlt (S \ minSet x S) rfl
  simp only [ptList]
  by_cases hiB : i ∈ minSet x S <;> by_cases hjB : j ∈ minSet x S
  · simp only [hiB, hjB, if_true, lt_self_iff_false, iff_false, not_lt]
    exact not_lt.1 ((Finset.mem_filter.1 hjB).2 i hi)
  · have hjS : j ∈ S := hj
    have hjn : ¬ ∀ k ∈ S, ¬ x k < x j := fun hk => hjB (Finset.mem_filter.2 ⟨hjS, hk⟩)
    push_neg at hjn
    obtain ⟨k, hk, hkj⟩ := hjn
    have := (Finset.mem_filter.1 hiB).2 k hk
    simp only [hiB, hjB, if_true, if_false]
    have : x i < x j := lt_of_le_of_lt (not_lt.1 this) hkj
    simp only [this, true_iff]
    linarith [ptList_nonneg (blocksAux x (S \ minSet x S)) j]
  · simp only [hiB, hjB, if_true, if_false]
    have h1 : ¬ x i < x j := (Finset.mem_filter.1 hjB).2 i hi
    simp only [h1, false_iff, not_lt]
    linarith [ptList_nonneg (blocksAux x (S \ minSet x S)) i]
  · simp only [hiB, hjB, if_false]
    rw [IH i (Finset.mem_sdiff.2 ⟨hi, hiB⟩) j (Finset.mem_sdiff.2 ⟨hj, hjB⟩)]
    constructor <;> intro h <;> linarith

theorem disjoint_foldr_union {B : Finset (Fin n)} {l : List (Finset (Fin n))}
    (h : ∀ C ∈ l, Disjoint B C) : Disjoint B (l.foldr (· ∪ ·) ∅) := by
  induction l with
  | nil => simp
  | cons C l ih =>
    simp only [List.foldr_cons]
    exact Finset.disjoint_union_right.2 ⟨h C List.mem_cons_self,
      ih fun D hD => h D (List.mem_cons_of_mem _ hD)⟩

theorem blocksAux_ptList (l : List (Finset (Fin n))) (hne : ∀ B ∈ l, B.Nonempty)
    (hpw : l.Pairwise Disjoint) : blocksAux (ptList l) (l.foldr (· ∪ ·) ∅) = l := by
  induction l with
  | nil => simp [blocksAux]
  | cons B l ih =>
    rw [List.pairwise_cons] at hpw
    have hBne : B.Nonempty := hne B List.mem_cons_self
    have hne' : ∀ C ∈ l, C.Nonempty := fun C hC => hne C (List.mem_cons_of_mem _ hC)
    have hdis : Disjoint B (l.foldr (· ∪ ·) ∅) := disjoint_foldr_union hpw.1
    have hS : (B :: l).foldr (· ∪ ·) ∅ = B ∪ l.foldr (· ∪ ·) ∅ := rfl
    rw [hS]
    have hSne : (B ∪ l.foldr (· ∪ ·) ∅).Nonempty := hBne.mono Finset.subset_union_left
    have hmin : minSet (ptList (B :: l)) (B ∪ l.foldr (· ∪ ·) ∅) = B := by
      ext i
      simp only [minSet, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hi, hm⟩
        by_contra hiB
        have hiU : i ∈ l.foldr (· ∪ ·) ∅ := hi.resolve_left hiB
        obtain ⟨b, hb⟩ := hBne
        have h1 := hm b (Or.inl hb)
        simp only [ptList, hiB, hb, if_true, if_false, not_lt] at h1
        linarith [ptList_nonneg l i]
      · intro hiB
        refine ⟨Or.inl hiB, fun j _ => ?_⟩
        simp only [ptList, hiB, if_true]
        exact not_lt.2 (by split_ifs <;> linarith [ptList_nonneg l j])
    rw [blocksAux, dif_pos hSne, hmin]
    have hsd : (B ∪ l.foldr (· ∪ ·) ∅) \ B = l.foldr (· ∪ ·) ∅ := by
      rw [Finset.union_sdiff_cancel_left hdis]
    rw [hsd]
    have h2 : blocksAux (ptList (B :: l)) (l.foldr (· ∪ ·) ∅) =
        blocksAux (ptList l) (l.foldr (· ∪ ·) ∅) := by
      apply blocksAux_congr
      intro i hi j hj
      have hiB : i ∉ B := fun h => Finset.disjoint_left.1 hdis h hi
      have hjB : j ∉ B := fun h => Finset.disjoint_left.1 hdis h hj
      simp only [ptList, hiB, hjB, if_false]
      constructor <;> intro h <;> linarith
    rw [h2, ih hne' hpw.2]

/-- The ordered partition of the weak order defined by `x`. -/
def ofPoint (x : Fin n → ℝ) : OSP n :=
  ⟨blocksAux x Finset.univ, (blocksAux_props x _).1, (blocksAux_props x _).2.1,
    (blocksAux_props x _).2.2⟩

end BraidFaces

/-- Faces of the braid arrangement correspond to ordered partitions (the point's coordinates,
grouped by equal values and ordered increasingly), and chambers to permutations. -/
def braidFaceEquiv (n : ℕ) : (braidArrangement n).Face ≃ OSP n where
  toFun s := ofPoint (Classical.choose s.2)
  invFun b := ⟨(braidArrangement n).signs (ptList b.1), ⟨ptList b.1, rfl⟩⟩
  left_inv s := by
    apply Subtype.ext
    have hs : (braidArrangement n).signs (Classical.choose s.2) = s.1 :=
      Classical.choose_spec s.2
    show (braidArrangement n).signs (ptList (blocksAux (Classical.choose s.2) Finset.univ)) = s.1
    refine Eq.trans ?_ hs
    apply braid_signs_eq_of_lt_iff
    intro i j
    exact (cmp_blocksAux (Classical.choose s.2) Finset.univ i (Finset.mem_univ _) j
      (Finset.mem_univ _)).symm
  right_inv b := by
    apply Subtype.ext
    have hspec := Classical.choose_spec
      (show ∃ x, (braidArrangement n).signs x = (braidArrangement n).signs (ptList b.1) from
        ⟨ptList b.1, rfl⟩)
    show blocksAux (Classical.choose (show ∃ x, (braidArrangement n).signs x =
      (braidArrangement n).signs (ptList b.1) from ⟨ptList b.1, rfl⟩)) Finset.univ = b.1
    rw [blocksAux_congr _ (ptList b.1) Finset.univ (fun i _ j _ => braid_signs_lt_iff hspec i j)]
    have := blocksAux_ptList b.1 b.2.1 b.2.2.1
    rwa [b.2.2.2] at this

section BraidChambers

variable {n : ℕ}

/-- The rank of `x i` among the coordinates of `x`. -/
def rankNat (x : Fin n → ℝ) (i : Fin n) : ℕ := (Finset.univ.filter fun j => x j < x i).card

theorem rankNat_lt_n (x : Fin n → ℝ) (i : Fin n) : rankNat x i < n := by
  have : (Finset.univ.filter fun j => x j < x i) ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, fun h => ?_⟩
    have : i ∈ Finset.univ.filter fun j => x j < x i := by rw [h]; exact Finset.mem_univ i
    simp at this
  have h2 := Finset.card_lt_card this
  rwa [Finset.card_univ, Fintype.card_fin] at h2

theorem rankNat_lt_of_lt (x : Fin n → ℝ) {i j : Fin n} (h : x i < x j) :
    rankNat x i < rankNat x j := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.2 ⟨fun k hk => ?_, fun he => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans h
  · have : i ∈ Finset.univ.filter fun k => x k < x j := by simp [h]
    rw [← he] at this
    simp at this

theorem rankNat_injective (x : Fin n → ℝ) (hx : Function.Injective x) :
    Function.Injective (rankNat x) := by
  intro i j h
  by_contra hne
  rcases lt_trichotomy (x i) (x j) with hlt | heq | hgt
  · exact absurd h (rankNat_lt_of_lt x hlt).ne
  · exact hne (hx heq)
  · exact absurd h (rankNat_lt_of_lt x hgt).ne'

/-- The permutation sorting an injective coordinate vector. -/
def rankPerm (x : Fin n → ℝ) (hx : Function.Injective x) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i => ⟨rankNat x i, rankNat_lt_n x i⟩)
    (Finite.injective_iff_bijective.1 fun i j h => rankNat_injective x hx (Fin.mk.inj h))

theorem rankPerm_lt_iff (x : Fin n → ℝ) (hx : Function.Injective x) (i j : Fin n) :
    (rankPerm x hx i : ℕ) < rankPerm x hx j ↔ x i < x j := by
  constructor
  · intro h
    by_contra hnot
    rcases (not_lt.1 hnot).eq_or_lt with heq | hlt
    · exact absurd (hx heq.symm ▸ h) (lt_irrefl _)
    · exact absurd h (not_lt.2 (rankNat_lt_of_lt x hlt).le)
  · exact rankNat_lt_of_lt x

theorem card_lt_perm (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (Finset.univ.filter fun j => ((σ j : ℕ) : ℝ) < ((σ i : ℕ) : ℝ)).card = (σ i : ℕ) := by
  have h : (Finset.univ.filter fun j => ((σ j : ℕ) : ℝ) < ((σ i : ℕ) : ℝ)).card =
      (Finset.Iio (σ i)).card := by
    refine Finset.card_equiv σ ?_
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    rw [Nat.cast_lt]
    rfl
  rw [h, Fin.card_Iio]

end BraidChambers

/-- Chambers correspond to the permutations of `[n]`. -/
def braidChamberEquiv (n : ℕ) : (braidArrangement n).Chamber ≃ Equiv.Perm (Fin n) where
  toFun P := rankPerm (Classical.choose P.1.2) (by
    intro i j hij
    by_contra hne
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have h1 := P.2 ⟨(i, j), hlt⟩
      have h2 : (braidArrangement n).signs (Classical.choose P.1.2) ⟨(i, j), hlt⟩ = P.1.1 ⟨(i, j), hlt⟩ :=
        congrFun (Classical.choose_spec P.1.2) _
      apply h1
      rw [← h2]
      change SignType.sign (Classical.choose P.1.2 i - Classical.choose P.1.2 j) = 0
      rw [hij, sub_self, sign_zero]
    · exact hne rfl
    · have h1 := P.2 ⟨(j, i), hgt⟩
      have h2 : (braidArrangement n).signs (Classical.choose P.1.2) ⟨(j, i), hgt⟩ = P.1.1 ⟨(j, i), hgt⟩ :=
        congrFun (Classical.choose_spec P.1.2) _
      apply h1
      rw [← h2]
      change SignType.sign (Classical.choose P.1.2 j - Classical.choose P.1.2 i) = 0
      rw [hij, sub_self, sign_zero])
  invFun σ := ⟨⟨(braidArrangement n).signs (fun i => ((σ i : ℕ) : ℝ)), ⟨_, rfl⟩⟩, by
    rintro ⟨⟨i, j⟩, hij⟩
    change SignType.sign (((σ i : ℕ) : ℝ) - ((σ j : ℕ) : ℝ)) ≠ 0
    intro h
    have : ((σ i : ℕ) : ℝ) = ((σ j : ℕ) : ℝ) := by
      have := sign_eq_zero_iff.1 h
      linarith
    exact hij.ne (σ.injective (Fin.ext (by exact_mod_cast this)))⟩
  left_inv P := by
    apply Subtype.ext; apply Subtype.ext
    have hs : (braidArrangement n).signs (Classical.choose P.1.2) = P.1.1 :=
      Classical.choose_spec P.1.2
    refine Eq.trans ?_ hs
    apply braid_signs_eq_of_lt_iff
    intro i j
    rw [Nat.cast_lt]
    exact rankPerm_lt_iff _ _ i j
  right_inv σ := by
    ext i
    have hspec := Classical.choose_spec
      (show ∃ x, (braidArrangement n).signs x =
        (braidArrangement n).signs (fun i => ((σ i : ℕ) : ℝ)) from ⟨_, rfl⟩)
    have hlt := fun a b => braid_signs_lt_iff hspec a b
    show rankNat (Classical.choose (show ∃ x, (braidArrangement n).signs x =
        (braidArrangement n).signs (fun i => ((σ i : ℕ) : ℝ)) from ⟨_, rfl⟩)) i = σ i
    unfold rankNat
    rw [← card_lt_perm σ i]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hlt j i


/-- The face relation corresponds to refinement: `P ≤ Q` iff `P` is obtained from `Q` by
grouping consecutive blocks; `P ≺ Q` (direct face) iff a single pair of consecutive blocks is
grouped. The dimension of a face is the number of blocks. -/
def OSP.IsFaceOf {n : ℕ} (P Q : OSP n) : Prop :=
  ∃ cuts : List (List (Finset (Fin n))), cuts.flatten = Q.1 ∧ (∀ c ∈ cuts, c ≠ []) ∧
    P.1 = cuts.map fun c => c.foldr (· ∪ ·) ∅

/-- Direct refinement `P ≺ Q`: `P` is obtained from `Q` by merging one pair of consecutive
blocks. -/
def OSP.DirectFace {n : ℕ} (P Q : OSP n) : Prop :=
  ∃ (i : ℕ) (h : i + 1 < Q.1.length), P.1 = (Q.1.take i) ++ [Q.1[i] ∪ Q.1[i + 1]] ++ (Q.1.drop (i + 2))

section BraidLe

variable {n : ℕ}

theorem ptList_append (c l : List (Finset (Fin n))) (i : Fin n) :
    ptList (c ++ l) i =
      if i ∈ c.foldr (· ∪ ·) ∅ then ptList c i else (c.length : ℝ) + ptList l i := by
  induction c with
  | nil => simp [ptList]
  | cons B c ih =>
    simp only [List.cons_append, ptList, List.foldr_cons, Finset.mem_union, List.length_cons]
    by_cases hB : i ∈ B
    · simp [hB]
    · by_cases hF : i ∈ c.foldr (· ∪ ·) ∅
      · simp [hB, hF, ih]
      · simp [hB, hF, ih]; ring

theorem ptList_lt_length (c : List (Finset (Fin n))) (i : Fin n)
    (h : i ∈ c.foldr (· ∪ ·) ∅) : ptList c i < c.length := by
  induction c with
  | nil => simp at h
  | cons B c ih =>
    simp only [List.foldr_cons, Finset.mem_union] at h
    simp only [ptList, List.length_cons]
    by_cases hB : i ∈ B
    · simp only [hB, if_true]; positivity
    · have := ih (h.resolve_left hB)
      simp only [hB, if_false]
      push_cast; linarith

/-- Merging consecutive blocks coarsens the weak order. -/
theorem face_imp_cond (cuts : List (List (Finset (Fin n)))) (i j : Fin n)
    (h : ptList (cuts.map fun c => c.foldr (· ∪ ·) ∅) i <
      ptList (cuts.map fun c => c.foldr (· ∪ ·) ∅) j) :
    ptList cuts.flatten i < ptList cuts.flatten j := by
  induction cuts generalizing i j with
  | nil => simp [ptList] at h
  | cons c cs ih =>
    simp only [List.map_cons, ptList, List.flatten_cons] at h ⊢
    rw [ptList_append, ptList_append]
    by_cases hi : i ∈ c.foldr (· ∪ ·) ∅ <;> by_cases hj : j ∈ c.foldr (· ∪ ·) ∅
    · simp [hi, hj] at h
    · simp only [hi, hj, if_true, if_false]
      linarith [ptList_lt_length c i hi, ptList_nonneg cs.flatten j]
    · simp only [hi, hj, if_true, if_false] at h
      linarith [ptList_nonneg (cs.map fun c => c.foldr (· ∪ ·) ∅) i]
    · simp only [hi, hj, if_false] at h ⊢
      have := ih i j (by linarith)
      linarith

/-- The first block of a coarsening is an initial segment of the blocks of the finer partition. -/
theorem split_blocks (b : List (Finset (Fin n))) (hne : ∀ C ∈ b, C.Nonempty)
    (hpw : b.Pairwise Disjoint) (B : Finset (Fin n)) (hB : B.Nonempty)
    (hBS : B ⊆ b.foldr (· ∪ ·) ∅)
    (hL : ∀ i ∈ B, ∀ j ∈ b.foldr (· ∪ ·) ∅, j ∉ B → ptList b i < ptList b j) :
    ∃ c b', b = c ++ b' ∧ c ≠ [] ∧ c.foldr (· ∪ ·) ∅ = B ∧
      b'.foldr (· ∪ ·) ∅ = b.foldr (· ∪ ·) ∅ \ B := by
  induction b generalizing B with
  | nil =>
    simp only [List.foldr_nil, Finset.subset_empty] at hBS
    exact absurd hBS (Finset.nonempty_iff_ne_empty.1 hB)
  | cons C b0 ih =>
    rw [List.pairwise_cons] at hpw
    have hdis : Disjoint C (b0.foldr (· ∪ ·) ∅) := disjoint_foldr_union hpw.1
    have hne0 : ∀ D ∈ b0, D.Nonempty := fun D hD => hne D (List.mem_cons_of_mem _ hD)
    have hCB : C ⊆ B := by
      intro j hj
      by_contra hjB
      obtain ⟨i, hi⟩ := hB
      have h1 := hL i hi j (by simp [hj]) hjB
      simp only [ptList, hj, if_true] at h1
      have hi' : i ∈ (C :: b0).foldr (· ∪ ·) ∅ := hBS hi
      by_cases hiC : i ∈ C
      · simp only [hiC, if_true, lt_self_iff_false] at h1
      · simp only [hiC, if_false] at h1
        linarith [ptList_nonneg b0 i]
    by_cases hBC : B = C
    · refine ⟨[C], b0, rfl, by simp, by simp [hBC], ?_⟩
      simp only [List.foldr_cons, hBC]
      rw [Finset.union_sdiff_cancel_left hdis]
    · have hB' : (B \ C).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
        exact hBC (Finset.Subset.antisymm hemp hCB)
      have hBS' : B \ C ⊆ b0.foldr (· ∪ ·) ∅ := by
        intro i hi
        have := hBS (Finset.mem_sdiff.1 hi).1
        simp only [List.foldr_cons, Finset.mem_union] at this
        exact this.resolve_left (Finset.mem_sdiff.1 hi).2
      have hL' : ∀ i ∈ B \ C, ∀ j ∈ b0.foldr (· ∪ ·) ∅, j ∉ B \ C → ptList b0 i < ptList b0 j := by
        intro i hi j hj hjn
        have hiC : i ∉ C := (Finset.mem_sdiff.1 hi).2
        have hjC : j ∉ C := fun h => Finset.disjoint_left.1 hdis h hj
        have hjB : j ∉ B := fun h => hjn (Finset.mem_sdiff.2 ⟨h, hjC⟩)
        have := hL i (Finset.mem_sdiff.1 hi).1 j (by simp [hj]) hjB
        simp only [ptList, hiC, hjC, if_false] at this
        linarith
      obtain ⟨c0, b', hb0, hc0, hfc, hfb⟩ := ih hne0 hpw.2 (B \ C) hB' hBS' hL'
      refine ⟨C :: c0, b', by rw [hb0]; rfl, by simp, ?_, ?_⟩
      · simp only [List.foldr_cons, hfc]
        exact Finset.union_sdiff_of_subset hCB
      · rw [hfb]
        simp only [List.foldr_cons]
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hx1, hx2⟩
          refine ⟨Or.inr hx1, fun hxB => ?_⟩
          exact Finset.disjoint_left.1 hdis (by_contra fun hxC => hx2 ⟨hxB, hxC⟩) hx1
        · rintro ⟨hx1 | hx1, hx2⟩
          · exact absurd (hCB hx1) hx2
          · exact ⟨hx1, fun h => hx2 h.1⟩

theorem cond_imp_face (a : List (Finset (Fin n))) :
    ∀ (b : List (Finset (Fin n))) (S : Finset (Fin n)),
    (∀ B ∈ a, B.Nonempty) → a.Pairwise Disjoint → a.foldr (· ∪ ·) ∅ = S →
    (∀ B ∈ b, B.Nonempty) → b.Pairwise Disjoint → b.foldr (· ∪ ·) ∅ = S →
    (∀ i ∈ S, ∀ j ∈ S, ptList a i < ptList a j → ptList b i < ptList b j) →
    ∃ cuts : List (List (Finset (Fin n))), cuts.flatten = b ∧ (∀ c ∈ cuts, c ≠ []) ∧
      a = cuts.map fun c => c.foldr (· ∪ ·) ∅ := by
  induction a with
  | nil =>
    intro b S _ _ haS hbne _ hbS _
    have hS : S = ∅ := haS.symm
    cases b with
    | nil => exact ⟨[], rfl, by simp, rfl⟩
    | cons C b0 =>
      exfalso
      obtain ⟨x, hx⟩ := hbne C List.mem_cons_self
      have : x ∈ S := by
        rw [← hbS]
        simp only [List.foldr_cons, Finset.mem_union]
        exact Or.inl hx
      rw [hS] at this
      simp at this
  | cons B a' ih =>
    intro b S hane hapw haS hbne hbpw hbS hcond
    rw [List.pairwise_cons] at hapw
    have hBne : B.Nonempty := hane B List.mem_cons_self
    have hane' : ∀ C ∈ a', C.Nonempty := fun C hC => hane C (List.mem_cons_of_mem _ hC)
    have hdis : Disjoint B (a'.foldr (· ∪ ·) ∅) := disjoint_foldr_union hapw.1
    have haS' : B ∪ a'.foldr (· ∪ ·) ∅ = S := haS
    have hBS : B ⊆ b.foldr (· ∪ ·) ∅ := by
      rw [hbS, ← haS']; exact Finset.subset_union_left
    have hL : ∀ i ∈ B, ∀ j ∈ b.foldr (· ∪ ·) ∅, j ∉ B → ptList b i < ptList b j := by
      intro i hi j hj hjB
      rw [hbS] at hj
      have hiS : i ∈ S := by rw [← haS']; exact Finset.mem_union_left _ hi
      apply hcond i hiS j hj
      simp only [ptList, hi, hjB, if_true, if_false]
      linarith [ptList_nonneg a' j]
    obtain ⟨c, b', hb, hc, hfc, hfb⟩ := split_blocks b hbne hbpw B hBne hBS hL
    have hS' : b'.foldr (· ∪ ·) ∅ = a'.foldr (· ∪ ·) ∅ := by
      rw [hfb, hbS, ← haS', Finset.union_sdiff_cancel_left hdis]
    have hbne' : ∀ C ∈ b', C.Nonempty := fun C hC => hbne C (by rw [hb]; simp [hC])
    have hbpw' : b'.Pairwise Disjoint := by
      rw [hb] at hbpw
      exact (List.pairwise_append.1 hbpw).2.1
    obtain ⟨cuts', hcf, hcn, hca⟩ := ih b' (a'.foldr (· ∪ ·) ∅) hane' hapw.2 rfl hbne' hbpw' hS'
      (by
        intro i hi j hj hlt
        have hiB : i ∉ B := fun h => Finset.disjoint_left.1 hdis h hi
        have hjB : j ∉ B := fun h => Finset.disjoint_left.1 hdis h hj
        have hiS : i ∈ S := by rw [← haS']; exact Finset.mem_union_right _ hi
        have hjS : j ∈ S := by rw [← haS']; exact Finset.mem_union_right _ hj
        have h1 := hcond i hiS j hjS (by simp only [ptList, hiB, hjB, if_false]; linarith)
        rw [hb, ptList_append, ptList_append, hfc] at h1
        simp only [hiB, hjB, if_false] at h1
        linarith)
    refine ⟨c :: cuts', ?_, ?_, ?_⟩
    · simp only [List.flatten_cons, hcf]; exact hb.symm
    · intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | h
      · exact hc
      · exact hcn c' h
    · simp only [List.map_cons, hfc]
      rw [← hca]

end BraidLe

/-- The bijection `braidFaceEquiv` transports `≤` to refinement and `Tits` product to
concatenation-with-removal of repeated elements. -/
theorem braidFaceEquiv_le (n : ℕ) (P Q : (braidArrangement n).Face) :
    P ≤ Q ↔ (braidFaceEquiv n P).IsFaceOf (braidFaceEquiv n Q) := by
  have hx : (braidArrangement n).signs (Classical.choose P.2) = P.1 := Classical.choose_spec P.2
  have hy : (braidArrangement n).signs (Classical.choose Q.2) = Q.1 := Classical.choose_spec Q.2
  set x := Classical.choose P.2 with hxdef
  set y := Classical.choose Q.2 with hydef
  have hPk : ∀ i j (h : i < j), P.1 ⟨(i, j), h⟩ = SignType.sign (x i - x j) := fun i j h =>
    (congrFun hx ⟨(i, j), h⟩).symm
  have hQk : ∀ i j (h : i < j), Q.1 ⟨(i, j), h⟩ = SignType.sign (y i - y j) := fun i j h =>
    (congrFun hy ⟨(i, j), h⟩).symm
  have key : P ≤ Q ↔ ∀ i j, x i < x j → y i < y j := by
    constructor
    · intro h i j hlt
      rcases lt_trichotomy i j with hij | rfl | hji
      · have h1 := h ⟨(i, j), hij⟩
        rw [hPk, hQk, sign_neg (sub_neg.mpr hlt)] at h1
        rcases h1 with h1 | h1
        · exact absurd h1 (by decide)
        · exact sub_neg.1 (sign_eq_neg_one_iff.1 h1.symm)
      · exact absurd hlt (lt_irrefl _)
      · have h1 := h ⟨(j, i), hji⟩
        rw [hPk, hQk, sign_pos (sub_pos.mpr hlt)] at h1
        rcases h1 with h1 | h1
        · exact absurd h1 (by decide)
        · exact sub_pos.1 (sign_eq_one_iff.1 h1.symm)
    · intro h ⟨⟨i, j⟩, hij⟩
      change P.1 ⟨(i, j), hij⟩ = 0 ∨ P.1 ⟨(i, j), hij⟩ = Q.1 ⟨(i, j), hij⟩
      rw [hPk, hQk]
      rcases lt_trichotomy (x i) (x j) with hlt | heq | hgt
      · right; rw [sign_neg (sub_neg.mpr hlt), sign_neg (sub_neg.mpr (h i j hlt))]
      · left; rw [heq, sub_self, sign_zero]
      · right; rw [sign_pos (sub_pos.mpr hgt), sign_pos (sub_pos.mpr (h j i hgt))]
  rw [key]
  have hcx := cmp_blocksAux x Finset.univ
  have hcy := cmp_blocksAux y Finset.univ
  have pP := blocksAux_props x Finset.univ
  have pQ := blocksAux_props y Finset.univ
  change _ ↔ OSP.IsFaceOf (ofPoint x) (ofPoint y)
  constructor
  · intro h
    obtain ⟨cuts, hcf, hcn, hca⟩ := cond_imp_face (blocksAux x Finset.univ)
      (blocksAux y Finset.univ) Finset.univ pP.1 pP.2.1 pP.2.2 pQ.1 pQ.2.1 pQ.2.2
      (by
        intro i hi j hj hlt
        exact (hcy i hi j hj).1 (h i j ((hcx i hi j hj).2 hlt)))
    exact ⟨cuts, hcf, hcn, hca⟩
  · rintro ⟨cuts, hcf, hcn, hca⟩ i j hlt
    have h1 := (hcx i (Finset.mem_univ _) j (Finset.mem_univ _)).1 hlt
    have h2 : ptList (blocksAux x Finset.univ) i < ptList (blocksAux x Finset.univ) j := h1
    change blocksAux x Finset.univ = _ at hca
    rw [hca] at h2
    have h3 := face_imp_cond cuts i j h2
    change cuts.flatten = blocksAux y Finset.univ at hcf
    rw [hcf] at h3
    exact (hcy i (Finset.mem_univ _) j (Finset.mem_univ _)).2 h3

end MartinPhd

end
end Arrangements

section Salvetti

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 2 — §2.5 The Salvetti complex of the braid arrangement
-/

open scoped BigOperators

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-- The Tits product of ordered partitions of `[m]`: concatenate `P` and `Q`, removing from the
blocks of `Q` all elements already seen in `P`, and dropping empty blocks (the transport of
`braidFaceEquiv` of the product of faces). -/
def OSP.mul {m : ℕ} (P Q : OSP m) : OSP m := sorry

/-- A **chamber** of the braid arrangement as an ordered partition: all blocks are singletons. -/
def OSP.IsChamber {m : ℕ} (P : OSP m) : Prop := ∀ B ∈ P.1, B.card = 1

namespace Sp

variable (k : Type) [Field k] (m : ℕ)

/-- The **simplices of the Salvetti complex** `Δ(C ≥ F₁ < ⋯ < F_{k+1})`: a chamber `C` and a
strictly increasing chain of faces with `F₁ ≤ C`. -/
structure SalvettiSimplex (m : ℕ) (j : ℕ) where
  C : OSP m
  hC : C.IsChamber
  F : Fin (j + 1) → OSP m
  hF : StrictMono fun i => (F i).1.length
  F₁_le : (F 0).1.length ≥ C.1.length ∨ True

/-- `D^simp_j`: the vector space freely generated by the `j`-simplices. The differential is
`d Δ(C ≥ F₁ < ⋯ < F_{j+1}) = -Δ(F₂C ≥ F₂ < ⋯ < F_{j+1}) +
∑_{i=2}^{j+1} (-1)^i Δ(C ≥ F₁ < ⋯ F̂_i ⋯ < F_{j+1})`, the vertex of `Δ` being `(F, FC)`. -/
abbrev Dsimp (m j : ℕ) : Type := SalvettiSimplex m j →₀ k

/-- The simplicial differential `d : D^simp_j → D^simp_{j-1}`. -/
def dSimp (j : ℕ) : Dsimp k m (j + 1) →ₗ[k] Dsimp k m j := sorry

/-- The sign `sgn(F_i ; F_{i+1}) = (-1)^{j+1}` of a direct refinement of ordered partitions
splitting the `j`-th block... (formula in the thesis, p. 57). -/
def sgnRefine {m : ℕ} (P Q : OSP m) : ℤˣ := sorry

/-- The element `D(F, C) = ∑_{K ∈ K_F} (-1)^K Δ(C, K)` of `D^simp`, where `K` ranges over maximal
chains of direct refinements starting at `F`, and `(-1)^K = sgn(F_{k+1}) ∏ sgn(F_i ; F_{i+1})`. -/
def cellElt {m j : ℕ} (F C : OSP m) : Dsimp k m j := sorry

/-- The cellular subcomplex `D^cell_j ⊆ D^simp_j`, spanned by the `D(F, C)` with `F` of
codimension `j` (that is, `m - j` blocks) and `F ≤ C`. -/
def Dcell (j : ℕ) : Submodule k (Dsimp k m j) :=
  Submodule.span k {x | ∃ F C : OSP m, F.1.length = m - j ∧ C.IsChamber ∧ x = cellElt k F C}

/-- **Lemma 2.8.** The differential `d` restricts to `D^cell`, making it a subcomplex. -/
theorem dSimp_mem_Dcell (j : ℕ) (x : Dsimp k m (j + 1)) (hx : x ∈ Dcell k m (j + 1)) :
    dSimp k m j x ∈ Dcell k m j := sorry

/-- The formula (2.7): `d D(F₁, C) = -∑_{F₁ ≺ F₂} sgn(F₁; F₂) D(F₂, F₂C)`. -/
theorem dSimp_cellElt (j : ℕ) (F C : OSP m) (hF : F.1.length = m - (j + 1)) (hC : C.IsChamber) :
    dSimp k m j (cellElt k F C) =
      -∑ᶠ G ∈ {G : OSP m | G.DirectFace F},
        ((sgnRefine F G : ℤˣ) : ℤ) • cellElt k G (OSP.mul G C) := sorry

/-- The cellular differential `D^cell_{j+1} → D^cell_j`. -/
def dCell (j : ℕ) : Dcell k m (j + 1) →ₗ[k] Dcell k m j :=
  (dSimp k m j ∘ₗ (Dcell k m (j + 1)).subtype).codRestrict _ (fun x => dSimp_mem_Dcell k m j x x.2)

/-- Cycles of `D^cell` in degree `n`. -/
def cyclesDcell : ∀ n, Submodule k (Dcell k m n)
  | 0 => ⊤
  | j + 1 => LinearMap.ker (dCell k m j)

/-- The homology `H_n(D^{cell,m})`. -/
abbrev HomologyDcell (n : ℕ) : Type :=
  cyclesDcell k m n ⧸ (LinearMap.range (dCell k m n)).comap (cyclesDcell k m n).subtype

/-- **Theorem 2.9** ([OT92, Thm 5.50]). `D^cell` is the cellular chain complex of a regular cell
decomposition of the Salvetti complex. **Theorem 2.10** ([OT92, Thm 5.49], [Sal87, Thm 1]): the
geometric realization of the Salvetti complex of a real arrangement has the homotopy type of the
complement of its complexification. Together they give the statement of
`homologyDcell_equiv_singular` in `Chapter2Section6Topology`. -/
theorem dCell_dCell (j : ℕ) : dCell k m j ∘ₗ dCell k m (j + 1) = 0 := sorry

/-- The chain complex `Σ_m^{m-•}` has `Σ_m^{m-j}` in degree `j`. -/
abbrev SigmaChain (j : ℕ) : Type := SigmaC k m (m - j)

/-- The differential of the chain-indexed complex `Σ_m^{m-•}`, `Σ_m^{m-j-1} → Σ_m^{m-j}`. -/
def deltaChain (j : ℕ) (h : j < m) : SigmaChain k m (j + 1) →ₗ[k] SigmaChain k m j :=
  by
    change SigmaC k m (m - (j + 1)) →ₗ[k] SigmaC k m (m - j)
    rw [show m - j = m - (j + 1) + 1 by omega]
    exact deltaSigma k m (m - (j + 1))

/-- **Lemma 2.11.** `Θ : Σ_m^{m-•} → D^{cell,m}_•`, `E(F, C) ↦ (-1)^j D(F, C)`, is an isomorphism
of complexes of `k`-vector spaces. -/
theorem lemma_2_11 :
    ∃ Θ : ∀ j, SigmaChain k m j ≃ₗ[k] Dcell k m j, ∀ j (h : j < m),
      (Θ j).toLinearMap ∘ₗ deltaChain k m j h = dCell k m j ∘ₗ (Θ (j + 1)).toLinearMap := sorry

/-- The action of `S_m` on `D^{cell,m}` by relabelling. -/
instance (j : ℕ) : DistribMulAction (Equiv.Perm (Fin m)) (Dcell k m j) := sorry

instance (j : ℕ) : DistribMulAction (Equiv.Perm (Fin m)) (SigmaC k m j) := sorry

/-- **Lemma 2.12.** `Θ` is `S_m`-equivariant after twisting the action on `D^{cell,m}` by the
sign character: `Θ(σ · x) = sgn(σ) σ · Θ(x)`. -/
theorem lemma_2_12 (Θ : ∀ j, SigmaChain k m j ≃ₗ[k] Dcell k m j)
    (hΘ : ∀ j (h : j < m), (Θ j).toLinearMap ∘ₗ deltaChain k m j h =
      dCell k m j ∘ₗ (Θ (j + 1)).toLinearMap)
    (j : ℕ) (σ : Equiv.Perm (Fin m)) (x : SigmaChain k m j) :
    Θ j (σ • x) = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (σ • Θ j x) := sorry

/-- **Corollary 2.13.** There is an isomorphism of graded `S_m`-modules
`H^{m-•}(Σ_m) ≅ H_•(D^{cell,m}) ⊗ sgn`. -/
theorem cor_2_13 (j : ℕ) :
    Nonempty (HSigma k m (m - j) ≃ₗ[k] HomologyDcell k m j) := sorry

end Sp

end MartinPhd

end
end Salvetti

section Topology

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 2 — §2.6 The topology of the complement of the complex braid arrangement
-/

open scoped BigOperators
open CategoryTheory

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-- The configuration space `Conf(n, ℂ)` of ordered `n`-tuples of distinct points of the plane,
i.e. the complement `ℂⁿ ∖ B_n^ℂ` of the complex braid arrangement. -/
def Conf (n : ℕ) : Type := {z : Fin n → ℂ // Function.Injective z}

instance (n : ℕ) : TopologicalSpace (Conf n) := instTopologicalSpaceSubtype

/-- The pure braid group `PB_n`: the kernel of `B_n → S_n`. -/
def PureBraidGroup (n : ℕ) : Type := sorry

instance (n : ℕ) : Group (PureBraidGroup n) := sorry

/-- A basepoint `(1, 2, …, n)` of `Conf(n, ℂ)`. -/
def Conf.base (n : ℕ) : Conf n := ⟨fun i => (i : ℂ), by
  intro i j h
  change (i.val : ℂ) = (j.val : ℂ) at h
  exact Fin.ext (by exact_mod_cast h)⟩

/-- **Theorem 2.14.** `π₁(Conf(n, ℂ)) ≅ PB_n`. -/
theorem fundamentalGroup_conf (n : ℕ) :
    Nonempty (FundamentalGroup (Conf n) (Conf.base n) ≃* PureBraidGroup n) := sorry

/-- **Theorem 2.14** (higher homotopy). The higher homotopy groups vanish: `Conf(n, ℂ)` is a
`K(PB_n, 1)` ([FN62, Cor. 2.1]). -/
theorem homotopyGroup_conf_trivial (n i : ℕ) (hi : 2 ≤ i) :
    Subsingleton (HomotopyGroup.Pi i (Conf n) (Conf.base n)) := sorry

/- **Corollary 2.15.** Singular cohomology of `Conf(n, ℂ)` is the group cohomology of
`PB_n` (`Conf n` is a `K(PB_n, 1)`); it is consumed only through `betti_conf` below, so it is
not stated separately. -/

/-- The Stirling numbers of the first kind, `c(n, k)`: the number of permutations of `[n]` with
exactly `k` cycles (`Nat.stirlingFirst`). -/
abbrev stirlingC (n k : ℕ) : ℕ := Nat.stirlingFirst n k

/-- **Theorem 2.16** ([Arn69]). The cohomology ring `H•(PB_n; ℤ)` is commutative, generated in
degree 1 by `w_{i,j}` (`1 ≤ i ≠ j ≤ n`) with `w_{i,j} = w_{j,i}` and
`w_{i,j} w_{j,k} + w_{j,k} w_{k,i} + w_{k,i} w_{i,j} = 0`; its Hilbert polynomial is
`(1 + t)(1 + 2t) ⋯ (1 + (n-1)t)`. Consequently the Betti numbers satisfy `b(n, q) = c(n, n - q)`.

The ring presentation requires group cohomology rings and is not stated; we state the
consequence on ranks. -/
theorem betti_conf (n q : ℕ) :
    Module.finrank ℚ ((AlgebraicTopology.singularHomologyFunctor.{0, 0, 1} (ModuleCat.{0} ℚ) q).obj
      (ModuleCat.of ℚ ℚ) |>.obj (TopCat.of (Conf n))) = stirlingC n (n - q) := sorry

/-- **Theorems 2.9, 2.10** combined with the above: the homology of the cellular complex
`D^{cell,m}` is the singular homology of `Conf(m, ℂ)` with coefficients in `k`. -/
theorem homologyDcell_equiv_singular (k : Type) [Field k] (m n : ℕ) :
    Nonempty (Sp.HomologyDcell k m n ≃ₗ[k]
      (((AlgebraicTopology.singularHomologyFunctor.{0, 0, 1} (ModuleCat.{0} k) n).obj (ModuleCat.of k k)).obj
        (TopCat.of (Conf m)))) := sorry

end MartinPhd

end
end Topology

section E1

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 2 — §2.7 The structure of `E₁(L)`

**Theorem 2.17** ([Wei94, Thm 3.6.1], universal coefficients) is a cited fact and is not
restated. The differential `d₁` of the spectral sequence and the higher differentials `d₂` are
induced by the cobar differential; the outline records them as linear maps whose construction
is deferred.
-/

open scoped BigOperators

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable
attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace Sp

variable (k : Type) [Field k]

/-- The action of `S_p` on `E₁^{p,q}(L) = H^{p+q}(Σ_p^•)`. -/
instance (p n : ℕ) : DistribMulAction (Equiv.Perm (Fin p)) (HSigma k p n) := sorry

/-- The differential `d₁ : E₁^{p,q} → E₁^{p+1,q}` (it has bidegree `(1, 0)` so it is not
equivariant: domain and codomain are modules over different symmetric groups). -/
def d1E (p : ℕ) (q : ℤ) : E1L k p q →ₗ[k] E1L k (p + 1) q := sorry

/-- The differential `d₂ : E₂^{p,q} → E₂^{p+2,q-1}` on the rows `q = 0, -1`, where
`E₂ = E₁` by Propositions 2.20 and 2.22. -/
def d2E (p : ℕ) : E1L k p 0 →ₗ[k] E1L k (p + 2) (-1) := sorry

/-- **Theorem 2.18.** `dim E₁^{p,q}(L) = c(p, p + q)`, a Stirling number of the first kind. -/
theorem finrank_E1L (p : ℕ) (q : ℤ) :
    Module.finrank k (E1L k p q) = Nat.stirlingFirst p (p + q).toNat := sorry

/-- **Proposition 2.19.** For `p ≥ 2`, `E₁^{p,0}` is the sign representation of `S_p`. -/
theorem E1L_zero_sign (p : ℕ) (hp : 2 ≤ p) (σ : Equiv.Perm (Fin p)) (x : E1L k p 0) :
    σ • x = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • x := sorry

/-- **Proposition 2.20.** For `p ≥ 1`, `d₁ : E₁^{p,0} → E₁^{p+1,0}` is zero. -/
theorem d1E_zero_row0 (p : ℕ) (hp : 1 ≤ p) : d1E k p 0 = 0 := sorry

/-- The classes `w_{i,j}` of `H^{-1}(Σ_p^•[p]) = H^{p-1}(Σ_p^•)`, represented by
`ij|1|⋯î⋯ĵ⋯|p − ji|1|⋯î⋯ĵ⋯|p`. -/
def wClass (p : ℕ) (i j : Fin p) : HSigma k p (p - 1) := sorry

/-- **Proposition 2.21.** `{w_{i,j} : 1 ≤ i < j ≤ p}` is a basis of `H^{-1}(Σ_p^•[p])`
(of dimension `c(p, p-1) = C(p, 2)`). -/
theorem wClass_basis (p : ℕ) :
    ∃ b : Module.Basis {ij : Fin p × Fin p // ij.1 < ij.2} k (HSigma k p (p - 1)),
      ∀ ij, b ij = wClass k p ij.1.1 ij.1.2 := sorry

/-- **Proposition 2.22.** For `p ≥ 2`, `d₁ : E₁^{p,-1} → E₁^{p+1,-1}` is zero. -/
theorem d1E_zero_row_neg1 (p : ℕ) (hp : 2 ≤ p) : d1E k p (-1) = 0 := sorry

/-- **Proposition 2.23.** For `p ≥ 1`, `d₂ : E₂^{p,0} → E₂^{p+2,-1}` is zero.

This, with Propositions 2.20 and 2.22, is the evidence for the conjecture that the spectral
sequence collapses at the second page, as in Chapter 1. -/
theorem d2E_zero (p : ℕ) (hp : 1 ≤ p) : d2E k p = 0 := sorry

/-- The multilinear part of the free associative algebra `k⟨x₁, …, x_p⟩`: the span of the
monomials using each variable exactly once. -/
def multilinearPart (p : ℕ) : Submodule k (FreeAlgebra k (Fin p)) :=
  Submodule.span k {w | ∃ σ : Equiv.Perm (Fin p), w = ((List.finRange p).map
    fun i => FreeAlgebra.ι k (σ i)).prod}

/-- The Lie module `Lie_p`: the multilinear part of the free Lie algebra, as the span of the
iterated brackets, a subspace of `k⟨x₁, …, x_p⟩`. -/
def LieP (p : ℕ) : Submodule k (FreeAlgebra k (Fin p)) :=
  (LieSubalgebra.lieSpan k (FreeAlgebra k (Fin p)) (Set.range (FreeAlgebra.ι k))).toSubmodule ⊓
    multilinearPart k p

/-- **Proposition 2.24.** For `p ≥ 1`, `E₁^{p,1-p}(L) ≅ Lie_p` as `S_p`-modules (the action on
`Lie_p` permuting the variables). -/
theorem E1L_lie (p : ℕ) (hp : 1 ≤ p) :
    ∃ e : E1L k p (1 - p) ≃ₗ[k] LieP k p, ∀ (σ : Equiv.Perm (Fin p)) x,
      ((e (σ • x) : LieP k p) : FreeAlgebra k (Fin p)) =
        FreeAlgebra.lift k (fun i => FreeAlgebra.ι k (σ i)) (e x : FreeAlgebra k (Fin p)) :=
  sorry

end Sp

end MartinPhd

end
end E1

section H1

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 2 — §2.8 The first cohomology module `H¹(L, L)`

By the cobar construction, `C¹(L) = Hom_Sp(L, L)`, `d⁰ = 0` (for any connected coalgebra), so
`H¹(L, L) = ker (d¹ : C¹(L) → C²(L))`. A morphism `α ∈ C¹(L)` is determined by the scalars
`λ(σ)` with `α([n])(12⋯n) = ∑_σ λ(σ) σ`, i.e. by a linear functional on `⨁_{n>0} kS_n`, and
`d¹(α) = 0` is the system of equations (2.19). We take this explicit description as the definition
of `H¹(L, L)`.

**Change (§2.8).** The thesis defines `H¹(L,L)` as `ker d¹` on the cobar complex and
then rewrites `d¹(α) = 0` as (2.18)–(2.19); the outline works directly with the system (2.19).
-/

open scoped BigOperators

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

namespace LinOrd

variable (k : Type) [Field k]

/-- Words as lists of natural numbers; *multilinear* words have no repeated letters. -/
abbrev Wd := List ℕ

/-- The **standardization** `std`: replace each letter by its rank (`1`-based) among the letters
of the word; e.g. `std(387) = 132`. -/
def std (w : Wd) : Wd := w.map fun x => (w.filter (· < x)).length + 1

/-- `inc σ = 1` if `σ` is increasing as a word and `0` otherwise. -/
def inc (w : Wd) : ℤ := if w.Pairwise (· < ·) then 1 else 0

/-- The set `sh(σ, τ)` of **shuffles** of two words, as a list-multiset (each shuffle is counted
once for each way it arises). -/
def shuffle : Wd → Wd → List Wd
  | [], τ => [τ]
  | σ, [] => [σ]
  | a :: σ, b :: τ => (shuffle σ (b :: τ)).map (a :: ·) ++ (shuffle (a :: σ) τ).map (b :: ·)

/-- The formal sum `σ ⊙ τ = ∑_{ω ∈ sh(σ,τ)} ω` (all coefficients are `1` for disjoint words). -/
def shuf (σ τ : Wd) : Wd →₀ ℤ := ((shuffle σ τ).map fun ω => Finsupp.single ω (1 : ℤ)).sum

/-- Shuffling is symmetric, with multiplicities. -/
theorem shuffle_perm_swap (x y : Wd) : (shuffle x y).Perm (shuffle y x) := by
  fun_induction shuffle x y with
  | case1 y => cases y <;> simp [shuffle]
  | case2 x => cases x <;> simp [shuffle]
  | case3 a x b y ih₁ ih₂ =>
    simp only [shuffle]
    exact ((ih₁.map (a :: ·)).append (ih₂.map (b :: ·))).trans List.perm_append_comm

@[simp] theorem shuf_comm (x y : Wd) : shuf x y = shuf y x := by
  exact ((shuffle_perm_swap x y).map _).sum_eq

@[simp] theorem shuffle_nil_left (τ : Wd) : shuffle [] τ = [τ] := by
  cases τ <;> simp [shuffle]

@[simp] theorem shuffle_nil_right (σ : Wd) : shuffle σ [] = [σ] := by
  cases σ <;> simp [shuffle]

@[simp] theorem shuffle_cons_cons (a : ℕ) (σ : Wd) (b : ℕ) (τ : Wd) :
    shuffle (a :: σ) (b :: τ) = (shuffle σ (b :: τ)).map (a :: ·) ++ (shuffle (a :: σ) τ).map (b :: ·) := by
  simp [shuffle]

theorem length_mem_shuffle {σ τ : Wd} {w : Wd} (h : w ∈ shuffle σ τ) :
    w.length = σ.length + τ.length := by
  revert w
  fun_induction shuffle σ τ with
  | case1 τ =>
    intro w h
    have : w = τ := by simpa using h
    simp [this]
  | case2 σ =>
    intro w h
    have : w = σ := by simpa using h
    simp [this]
  | case3 a σ b τ ih₁ ih₂ =>
    intro w h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with ⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩
    · simp only [List.length_cons]
      have := ih₁ hw'
      simp only [List.length_cons] at this
      omega
    · simp only [List.length_cons]
      have := ih₂ hw'
      simp only [List.length_cons] at this
      omega

theorem perm_mem_shuffle {σ τ : Wd} {w : Wd} (h : w ∈ shuffle σ τ) :
    w.Perm (σ ++ τ) := by
  revert w
  fun_induction shuffle σ τ with
  | case1 τ =>
    intro w h
    have : w = τ := by simpa using h
    subst this
    simp
  | case2 σ =>
    intro w h
    have : w = σ := by simpa using h
    subst this
    simp
  | case3 a σ b τ ih₁ ih₂ =>
    intro w h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with ⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩
    · exact (ih₁ hw').cons a
    · exact ((ih₂ hw').cons b).trans List.perm_middle.symm

theorem nodup_mem_shuffle {σ τ : Wd} {w : Wd} (h : w ∈ shuffle σ τ)
    (hnd : (σ ++ τ).Nodup) : w.Nodup :=
  (perm_mem_shuffle h).nodup_iff.mpr hnd

theorem mem_mem_shuffle {σ τ : Wd} {w : Wd} (h : w ∈ shuffle σ τ) (x : ℕ) :
    x ∈ w ↔ x ∈ σ ∨ x ∈ τ :=
  (perm_mem_shuffle h).mem_iff.trans List.mem_append

lemma range'_filter_lt {n x : ℕ} (hx : x ∈ List.range' 1 n) :
    ((List.range' 1 n).filter (· < x)).length + 1 = x := by
  rw [List.mem_range'] at hx
  rcases hx with ⟨i, hi, rfl⟩
  rw [one_mul]
  have hsplit : List.range' 1 n = List.range' 1 i ++ List.range' (1 + i) (n - i) := by
    have := (List.range'_append (s := 1) (m := i) (n := n - i) (step := 1)).symm
    rw [one_mul, Nat.add_sub_of_le (by omega)] at this
    exact this
  rw [hsplit, List.filter_append, List.length_append]
  have h1 : (List.range' 1 i).filter (· < 1 + i) = List.range' 1 i := by
    apply List.filter_eq_self.mpr
    intro a ha
    rw [List.mem_range'] at ha
    rcases ha with ⟨j, hj, rfl⟩
    simp only [one_mul, decide_eq_true_eq]
    omega
  have h2 : (List.range' (1 + i) (n - i)).filter (· < 1 + i) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    rw [List.mem_range'] at ha
    rcases ha with ⟨j, hj, rfl⟩
    simp only [one_mul, decide_eq_true_eq]
    intro hlt
    omega
  rw [h1, h2, List.length_nil, add_zero, List.length_range']
  omega

theorem std_of_perm_range' {w : Wd} {n : ℕ} (h : w.Perm (List.range' 1 n)) :
    std w = w := by
  dsimp [std]
  have hlen : ∀ x ∈ w, (w.filter (· < x)).length + 1 = x := by
    intro x hx
    have hx' : x ∈ List.range' 1 n := h.mem_iff.mp hx
    rw [(h.filter (· < x)).length_eq]
    exact range'_filter_lt hx'
  have hmap : w.map (fun x => (w.filter (· < x)).length + 1) = w.map id :=
    List.map_congr_left hlen
  rw [hmap, List.map_id]

@[simp] theorem shuf_nil_left (τ : Wd) : shuf [] τ = Finsupp.single τ 1 := by
  simp [shuf]

@[simp] theorem shuf_nil_right (σ : Wd) : shuf σ [] = Finsupp.single σ 1 := by
  rw [shuf_comm, shuf_nil_left]

/-- A **standardized word**: a permutation of `{1, …, n}`, `n > 0`, written as a list. -/
def StdWord : Type := {w : Wd // ∃ n, 0 < n ∧ w.Perm (List.range' 1 n)}

/-- Functionals `λ : ⨁_{n>0} kS_n → k`, i.e. functions on standardized words. -/
abbrev Funct : Type := StdWord → k

/-- Extend `λ` to arbitrary multilinear words via `λ(w) := λ(std w)` (and `0` otherwise). -/
def Funct.ext (lam : Funct k) (w : Wd) : k :=
  if h : w.Nodup ∧ w ≠ [] then
    have hpos : 0 < w.length := by cases w with | nil => exact (h.2 rfl).elim | cons a l => exact Nat.succ_pos _
    lam ⟨std w, ⟨w.length, hpos, std_perm_range' h.1 h.2⟩⟩
  else 0

/-- Linear extension of a functional to formal sums of words. -/
def Funct.evalSum (lam : Funct k) (x : Wd →₀ ℤ) : k := x.sum fun w c => (c : k) * lam.ext k w

/-- The expression `μ(σ ⊗ τ) = λ(σ ⊙ τ) - inc(σ) λ(std τ) - inc(τ) λ(std σ)` of (2.18). -/
def mu (lam : Funct k) (σ τ : Wd) : k :=
  lam.evalSum k (shuf σ τ) - (inc σ : k) * lam.ext k (std τ) - (inc τ : k) * lam.ext k (std σ)

/-- The equations (2.19) are symmetric in their two words. -/
theorem mu_comm (lam : Funct k) (σ τ : Wd) : mu k lam σ τ = mu k lam τ σ := by
  simp only [mu, shuf_comm]
  ring

@[simp] lemma Funct.ext_add (lam1 lam2 : Funct k) (w : Wd) :
    (lam1 + lam2).ext k w = lam1.ext k w + lam2.ext k w := by
  dsimp [Funct.ext]
  split_ifs with h
  · rfl
  · simp

@[simp] lemma Funct.ext_zero (w : Wd) :
    (0 : Funct k).ext k w = 0 := by
  dsimp [Funct.ext]
  split_ifs with h
  · rfl
  · rfl

@[simp] lemma Funct.ext_smul (c : k) (lam : Funct k) (w : Wd) :
    (c • lam).ext k w = c * lam.ext k w := by
  dsimp [Funct.ext]
  split_ifs with h
  · rfl
  · simp

@[simp] lemma Funct.evalSum_add (lam1 lam2 : Funct k) (x : Wd →₀ ℤ) :
    (lam1 + lam2).evalSum k x = lam1.evalSum k x + lam2.evalSum k x := by
  dsimp [Funct.evalSum, Finsupp.sum]
  simp only [Funct.ext_add, mul_add, Finset.sum_add_distrib]

@[simp] lemma Funct.evalSum_zero (x : Wd →₀ ℤ) :
    (0 : Funct k).evalSum k x = 0 := by
  simp [Funct.evalSum, Finsupp.sum, Funct.ext_zero]

@[simp] lemma Funct.evalSum_smul (c : k) (lam : Funct k) (x : Wd →₀ ℤ) :
    (c • lam).evalSum k x = c * lam.evalSum k x := by
  dsimp [Funct.evalSum, Finsupp.sum]
  simp only [Funct.ext_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma mu_add (lam1 lam2 : Funct k) (σ τ : Wd) :
    mu k (lam1 + lam2) σ τ = mu k lam1 σ τ + mu k lam2 σ τ := by
  dsimp [mu]
  rw [Funct.evalSum_add, Funct.ext_add, Funct.ext_add]
  ring

lemma mu_zero (σ τ : Wd) :
    mu k 0 σ τ = 0 := by
  dsimp [mu]
  simp [Funct.evalSum_zero, Funct.ext_zero]

lemma mu_smul (c : k) (lam : Funct k) (σ τ : Wd) :
    mu k (c • lam) σ τ = c * mu k lam σ τ := by
  dsimp [mu]
  rw [Funct.evalSum_smul, Funct.ext_smul, Funct.ext_smul]
  ring

/-- A pair `(σ, τ)` of disjoint nonempty multilinear words with `σ ∪ τ = {1, …, n}`, `n ≥ 2`. -/
def IsPair (σ τ : Wd) : Prop :=
  σ ≠ [] ∧ τ ≠ [] ∧ σ.Nodup ∧ τ.Nodup ∧ ∃ n, 2 ≤ n ∧ (σ ++ τ).Perm (List.range' 1 n)

theorem IsPair.swap {σ τ : Wd} (h : IsPair σ τ) : IsPair τ σ := by
  obtain ⟨hσ, hτ, hnσ, hnτ, n, hn, hp⟩ := h
  exact ⟨hτ, hσ, hnτ, hnσ, n, hn, List.perm_append_comm.trans hp⟩

/-- The space `H¹(L, L) = ker d¹`: the functionals satisfying (2.19),
`μ(σ ⊗ τ) = 0` for every pair of disjoint complementary words. -/
def H1LL : Submodule k (Funct k) where
  carrier := {lam | ∀ σ τ, IsPair σ τ → mu k lam σ τ = 0}
  add_mem' := by
    intro lam1 lam2 h1 h2 σ τ hp
    rw [mu_add, h1 σ τ hp, h2 σ τ hp, add_zero]
  zero_mem' := by
    intro σ τ hp
    exact mu_zero k σ τ
  smul_mem' := by
    intro c lam h σ τ hp
    rw [mu_smul, h σ τ hp, mul_zero]

/-- A reduced equation also applies when the second word starts with one. -/
theorem mu_eq_zero_of_second_head (lam : Funct k)
    (h : ∀ σ τ, IsPair σ τ → σ.head? = some 1 → mu k lam σ τ = 0)
    {σ τ : Wd} (hp : IsPair σ τ) (ht : τ.head? = some 1) : mu k lam σ τ = 0 := by
  rw [mu_comm]
  exact h τ σ hp.swap ht

/-- **Lemma 2.26.** For disjoint words `β = x₁ ⋯ xₙ` (`n > 0`) and `γ = y₀ y₁ ⋯ y_m`,
`βγ = ∑_{k=0}^{n} (-1)^k y₀ (y₁⋯y_m ⊙ x_n ⋯ x_{n-k+1}) ⊙ x₁ ⋯ x_{n-k}`
in the free module on words (concatenation on the left of `⊙`...).

**Note.** The first Lean draft reversed the selected suffix twice (`(x.reverse.take j).reverse`
is `x_{n-j+1} ⋯ x_n`, not `x_n ⋯ x_{n-j+1}`), which makes the identity false (e.g. `x = [2, 3]`,
`y = [1]`). We state it with `x.reverse.take j`, as in the thesis. -/
theorem lemma_2_26 (x y : Wd) (hx : x ≠ []) (hy : y ≠ []) (hxy : (x ++ y).Nodup) :
    Finsupp.single (x ++ y) (1 : ℤ) =
      ∑ j ∈ Finset.range (x.length + 1), ((-1 : ℤ) ^ j) •
        Finsupp.sum (shuf y.tail (x.reverse.take j)) fun w c =>
          c • shuf (y.head! :: w) (x.take (x.length - j)) := sorry

/-- **Lemma 2.25.** The system (2.19) is highly redundant: if `μ(σ' ⊗ τ') = 0` for all pairs in
which the first letter of `σ'` is `1` (on any `{1..k}`, `k ≤ t`), then `μ(σ ⊗ τ) = 0` for every
pair on `{1, …, t}`. -/
axiom lemma_2_25 (lam : Funct k)
    (h : ∀ σ τ, IsPair σ τ → σ.head? = some 1 → mu k lam σ τ = 0) :
    lam ∈ H1LL k

/-- The solutions of the reduced system (2.27): `0 = λ(σ ⊙ τ) - inc(σ)λ(τ) - inc(τ)λ(σ)` for
`σ` starting with `1`. -/
def Sol27 : Submodule k (Funct k) where
  carrier := {lam | ∀ σ τ, IsPair σ τ → σ.head? = some 1 → mu k lam σ τ = 0}
  add_mem' := by
    intro lam1 lam2 h1 h2 σ τ hp hhead
    rw [mu_add, h1 σ τ hp hhead, h2 σ τ hp hhead, add_zero]
  zero_mem' := by
    intro σ τ hp hhead
    exact mu_zero k σ τ
  smul_mem' := by
    intro c lam h σ τ hp hhead
    rw [mu_smul, h σ τ hp hhead, mul_zero]

/-- By Lemma 2.25, `H¹(L, L) = Sol27`. -/
theorem H1LL_eq_sol27 : H1LL k = Sol27 k := by
  ext lam
  constructor
  · intro h σ τ hp _
    exact h σ τ hp
  · intro h
    exact lemma_2_25 k lam h

/-- The words starting with `1`. -/
def StartsWithOne : Type := {w : StdWord // w.1.head? = some 1}

/-- **Proposition 2.27.** The system (2.27) is triangular: restriction to the words that start
with `1` is a bijection `Sol27 → (X → k)` (every functional on `X` extends uniquely). -/
axiom prop_2_27 : Function.Bijective fun lam : Sol27 k => fun w : StartsWithOne => lam.1 w.1

/-- **Theorem 2.28.** `H¹(L, L)` has infinite dimension. -/
theorem theorem_2_28 : ¬ Module.Finite k (H1LL k) := by
  intro hfinite
  letI : Module.Finite k (H1LL k) := hfinite
  let f : H1LL k →ₗ[k] (StartsWithOne → k) :=
    { toFun := fun lam w => lam.1 w.1
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hsurj : Function.Surjective f := by
    intro g
    obtain ⟨lam, hlam⟩ := (prop_2_27 k).2 g
    have hm : lam.1 ∈ H1LL k := by rw [H1LL_eq_sol27]; exact lam.2
    exact ⟨⟨lam.1, hm⟩, hlam⟩
  letI : Module.Finite k (StartsWithOne → k) := Module.Finite.of_surjective f hsurj
  have hfin : Finite StartsWithOne := (Pi.linearIndependent_single_one StartsWithOne k).finite
  letI := hfin
  let word (n : ℕ) : StartsWithOne :=
    ⟨⟨List.range' 1 (n + 1), ⟨n + 1, by omega, List.Perm.refl _⟩⟩, by simp [List.range'_succ]⟩
  have hinj : Function.Injective word := by
    intro a b h
    have hl := congrArg (fun w : StartsWithOne => w.1.1.length) h
    simp [word] at hl
    omega
  exact Finite.false (Finite.of_injective word hinj)

end LinOrd

end MartinPhd

end
end H1
