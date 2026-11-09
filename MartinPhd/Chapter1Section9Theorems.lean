import MartinPhd.Chapter1Section9Lemma131
import MartinPhd.Chapter1Section7SpectralSequence
import MartinPhd.Chapter1Section8FlagSpeciesShuffle
import MartinPhd.Chapter1Section4Cohomology
import MartinPhd.Chapter1Section7Convergence

/-!
# Chapter 1, Section 1.9 (Theorems 1.35 and 1.36)

Contents:
* CupPage
* DimSquare
* ShuffleCount
* CupProducts
* Thm135
* Thm135Cup
* Thm135Main
* Thm135Final
* Thm136Detect
* Thm136
-/

section CupPage

/-! Dimension support for the diagonal of the first page, used in Lemma 1.34.
A flag in `V` has length at most `dim V`, so every degree `n` cochain vanishes
in dimensions less than `n`. Its differential has the same property in degree `n+1`.
No compatibility of the cup product with the differential is needed here. -/

open CategoryTheory Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

/-- A degree `n` cochain vanishes on spaces of dimension less than `n`. -/
theorem cochains_le_diagonal_filt (x : EBicomod F k) (n : ℕ) :
    cochains x n ≤ filt x (n : ℤ) n := by
  intro α hα
  refine (mem_filt_iff x _ _ _).2 ⟨hα, fun V hV => ?_⟩
  apply LinearMap.ext
  intro z
  funext G
  exact hα.1 V z G (by
    have hlen := ST.len_le_finrank (F := F) G
    omega)

/-- Every degree `n` cochain represents a cycle on the diagonal of the first page. -/
theorem cochains_le_diagonal_Zpage (x : EBicomod F k) (n : ℕ) :
    cochains x n ≤ Zpage x 1 (n : ℤ) n := by
  intro α hα
  refine ⟨cochains_le_diagonal_filt x n hα, ?_⟩
  change d x n α ∈ filt x ((n : ℤ) + 1) (n + 1)
  simpa only [Nat.cast_add, Nat.cast_one] using
    cochains_le_diagonal_filt x (n + 1) (d_mem x hα)

/-- Cochains one step above the diagonal filtration are first-page boundaries. -/
theorem diagonal_filt_succ_le_Bpage (x : EBicomod F k) (n : ℕ) :
    filt x ((n : ℤ) + 1) n ≤ Bpage x 1 (n : ℤ) n := by
  intro α hα
  have hz : α ∈ Zpage x 0 ((n : ℤ) + 1) n := by
    refine ⟨hα, ?_⟩
    change d x n α ∈ filt x (((n : ℤ) + 1) + 0) (n + 1)
    simpa only [add_zero] using (d_filt x _ n hα).1
  cases n with
  | zero => exact hz
  | succ n => exact Submodule.mem_sup_right hz

/-- A diagonal cochain vanishing on the standard space is a first-page boundary. -/
theorem diagonal_mem_Bpage_of_stdSpace_eq_zero (x : EBicomod F k) (n : ℕ)
    {α : RawCochain x} (hα : α ∈ cochains x n) (h0 : α (stdSpace F n) = 0) :
    α ∈ Bpage x 1 (n : ℤ) n :=
  diagonal_filt_succ_le_Bpage x n
    (mem_filt_succ_of_stdSpace x n n (cochains_le_diagonal_filt x n hα) h0)

/-- Products of the diagonal representatives `α_m` and `α_n` are first-page cycles. -/
theorem cupAlpha_mem_Zpage (m n : ℕ) :
    cupRaw (flagCoalg F k) m n (alphaCochain m) (alphaCochain n) ∈
      Zpage (flagBicomod F k) 1 ((m + n : ℕ) : ℤ) (m + n) := by
  exact cochains_le_diagonal_Zpage _ _
    (cupRaw_mem (flagCoalg F k) (alphaCochain_mem_cochains m) (alphaCochain_mem_cochains n))

end MartinPhd

end
end CupPage

section DimSquare

open scoped BigOperators TensorProduct
open CategoryTheory Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k] [CharZero k]

/-- A primitive for the square of the dimension cocycle. -/
def dimSquarePrimitive : RawCochain (flagBicomod F k) := fun V =>
  Finsupp.linearCombination k fun _ : Flag F V => fun G : Flag F V =>
    if G.len = 1 then -((finrank F V : k) ^ 2) / 2 else 0

theorem dimSquarePrimitive_apply (V : FGModuleCat.{0} F)
    (z : (flagBicomod F k).X.ev V) (G : Flag F V) :
    dimSquarePrimitive (F := F) (k := k) V z G =
      (z.sum fun _ a => a) * (if G.len = 1 then -((finrank F V : k) ^ 2) / 2 else 0) :=
  lin_const_apply _ z G

theorem dimSquarePrimitive_mem : dimSquarePrimitive (F := F) (k := k) ∈
    cochains (flagBicomod F k) 1 := by
  refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
  · rw [dimSquarePrimitive_apply, if_neg hG, mul_zero]
  · rw [dimSquarePrimitive_apply, dimSquarePrimitive_apply, Flag.len_map]
    have hz : (Finsupp.sum (show Flag F W →₀ k from (flagBicomod F k).X.mapEquiv e z)
        (fun _ a => a)) = Finsupp.sum (show Flag F V →₀ k from z) (fun _ a => a) :=
      sum_lmapDomain _ z
    erw [hz]
    rw [(LinearEquiv.finrank_eq e).symm]

/-- On a basis flag, the square is the product of the two dimensions. -/
theorem cup_dim_square_single (V : FGModuleCat.{0} F) (H G : Flag F V) :
    cupRaw (flagCoalg F k) 1 1 dimCochain dimCochain V (Finsupp.single H 1) G =
      if G.len = 2 then (finrank F (G.nth 1) : k) * (finrank F (V ⧸ G.nth 1) : k) else 0 := by
  change (if G.len = 1 + 1 then
    LinearMap.mul' k k ∘ₗ
      TensorProduct.map (LinearMap.proj (G.restrict (G.nth 1)) ∘ₗ dimCochain (sub (G.nth 1)))
        (LinearMap.proj (G.project (G.nth 1)) ∘ₗ dimCochain (quo (G.nth 1))) ∘ₗ
      (flagCoalg F k).comul V (G.nth 1)
    else 0) (Finsupp.single H 1) = _
  by_cases h : G.len = 2
  · rw [if_pos h, if_pos h]
    have hd : (flagCoalg F k).comul V (G.nth 1) (Finsupp.single H 1) =
        (Finsupp.single (H.restrict (G.nth 1)) (1 : k)) ⊗ₜ[k]
          (Finsupp.single (H.project (G.nth 1)) (1 : k)) := by
      change (Finsupp.linearCombination k fun H : Flag F V =>
        (Finsupp.single (H.restrict (G.nth 1)) (1 : k)) ⊗ₜ[k]
          (Finsupp.single (H.project (G.nth 1)) (1 : k))) (Finsupp.single H 1) = _
      rw [Finsupp.linearCombination_single, one_smul]
    change (LinearMap.mul' k k) (TensorProduct.map
      (LinearMap.proj (G.restrict (G.nth 1)) ∘ₗ dimCochain (sub (G.nth 1)))
      (LinearMap.proj (G.project (G.nth 1)) ∘ₗ dimCochain (quo (G.nth 1)))
      ((flagCoalg F k).comul V (G.nth 1) (Finsupp.single H 1))) = _
    rw [hd]
    change (LinearMap.mul' k k) (TensorProduct.map
      (LinearMap.proj (G.restrict (G.nth 1)) ∘ₗ
        Finsupp.linearCombination k (fun _ : Flag F (G.nth 1) => fun K : Flag F (G.nth 1) =>
          if K.len = 1 then (finrank F (G.nth 1) : k) else 0))
      (LinearMap.proj (G.project (G.nth 1)) ∘ₗ
        Finsupp.linearCombination k (fun _ : Flag F (V ⧸ G.nth 1) => fun K : Flag F (V ⧸ G.nth 1) =>
          if K.len = 1 then (finrank F (V ⧸ G.nth 1) : k) else 0))
      ((Finsupp.single (H.restrict (G.nth 1)) (1 : k)) ⊗ₜ[k]
        (Finsupp.single (H.project (G.nth 1)) (1 : k)))) = _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    simp only [LinearMap.comp_apply, LinearMap.proj_apply]
    have hl : (G.restrict (G.nth 1)).len = 1 := by
      rw [Flag.len_restrict G (by omega) (G.nth 1) (by congr 1; omega)]; omega
    have hr : (G.project (G.nth 1)).len = 1 := by
      rw [Flag.len_project G (by omega) (G.nth 1) rfl]; omega
    simp [hl, hr, Finsupp.linearCombination_single]
  · rw [if_neg h, if_neg h]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The differential of the quadratic dimension cochain is the dimension square. -/
theorem d_dimSquarePrimitive_single (V : FGModuleCat.{0} F) (H G : Flag F V) :
    dRaw (flagBicomod F k) 1 dimSquarePrimitive V (Finsupp.single H 1) G =
      cupRaw (flagCoalg F k) 1 1 dimCochain dimCochain V (Finsupp.single H 1) G := by
  rw [cup_dim_square_single]
  have e1 : dRaw (flagBicomod F k) 1 dimSquarePrimitive V (Finsupp.single H 1) G =
      (if G.len = 2 then
        (LinearMap.proj (G.project (G.nth 1)) ∘ₗ dimSquarePrimitive (quo (G.nth 1)) ∘ₗ
          (flagBicomod F k).proj V (G.nth 1)) +
          faceSum _ G (dimSquarePrimitive (F := F) (k := k) V) +
        ((-1 : k) ^ (1 + 1)) • (LinearMap.proj (G.restrict (G.nth 1)) ∘ₗ
          dimSquarePrimitive (sub (G.nth 1)) ∘ₗ (flagBicomod F k).res V (G.nth 1))
      else 0) (Finsupp.single H 1) := rfl
  rw [e1]
  by_cases hG : G.len = 2
  · rw [if_pos hG, if_pos hG]
    erw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply]
    rw [faceSum_len2 _ G hG]
    set S := G.nth 1 with hS
    have hl1 : (G.project S).len = 1 := by
      rw [Flag.len_project G (by omega) S hS.symm]; omega
    have hl3 : (G.restrict S).len = 1 := by
      rw [Flag.len_restrict G (by omega) S (by rw [hS]; congr 1; omega)]; omega
    have hlf : (G.erase S (nth_one_proper G hG)).len = 1 := by
      have h1 := (G.erase S (nth_one_proper G hG)).card_eq_len_succ
      have h2 := G.card_eq_len_succ
      have h3 : (G.erase S (nth_one_proper G hG)).carrier.card + 1 = G.carrier.card :=
        Finset.card_erase_add_one (Flag.nth_mem' G (by omega))
      omega
    have t1 : dimSquarePrimitive (F := F) (k := k) (quo S)
        ((flagBicomod F k).proj V S (Finsupp.single H 1)) (G.project S) =
        -((finrank F (V ⧸ S) : k) ^ 2) / 2 := by
      rw [dimSquarePrimitive_apply, if_pos hl1]
      have hs : Finsupp.sum (show Flag F (quo S) →₀ k from
          (flagBicomod F k).proj V S (Finsupp.single H 1)) (fun _ a => a) = 1 := by
        change ((Finsupp.lmapDomain k k (fun H : Flag F V => H.project S)
          (Finsupp.single H 1)).sum fun _ a => a) = 1
        rw [sum_lmapDomain]; simp
      erw [hs]; simp
    have t3 : dimSquarePrimitive (F := F) (k := k) (sub S)
        ((flagBicomod F k).res V S (Finsupp.single H 1)) (G.restrict S) =
        -((finrank F S : k) ^ 2) / 2 := by
      rw [dimSquarePrimitive_apply, if_pos hl3]
      have hs : Finsupp.sum (show Flag F (sub S) →₀ k from
          (flagBicomod F k).res V S (Finsupp.single H 1)) (fun _ a => a) = 1 := by
        change ((Finsupp.lmapDomain k k (fun H : Flag F V => H.restrict S)
          (Finsupp.single H 1)).sum fun _ a => a) = 1
        rw [sum_lmapDomain]; simp
      erw [hs]; simp
    have tf : dimSquarePrimitive (F := F) (k := k) V (Finsupp.single H 1)
        (G.erase S (nth_one_proper G hG)) = -((finrank F V : k) ^ 2) / 2 := by
      rw [dimSquarePrimitive_apply, if_pos hlf]; simp
    have hdim : (finrank F (V ⧸ S) : k) + finrank F S = finrank F V := by
      have h := congrArg (Nat.cast : ℕ → k) S.finrank_quotient_add_finrank
      push_cast at h; exact h
    change dimSquarePrimitive (quo S) ((flagBicomod F k).proj V S (Finsupp.single H 1)) (G.project S) +
      -dimSquarePrimitive V (Finsupp.single H 1) (G.erase S (nth_one_proper G hG)) +
      (-1 : k) ^ (1 + 1) * dimSquarePrimitive (sub S)
        ((flagBicomod F k).res V S (Finsupp.single H 1)) (G.restrict S) = _
    rw [t1, t3, tf]
    rw [← hdim]
    ring
  · rw [if_neg hG, if_neg hG]; rfl

/-- The dimension class squares to zero in cohomology. -/
theorem dim_cup_dim_mem_coboundaries :
    cupRaw (flagCoalg F k) 1 1 dimCochain dimCochain ∈
      coboundaries (flagBicomod F k) 2 := by
  refine ⟨dimSquarePrimitive, dimSquarePrimitive_mem, ?_⟩
  funext V
  let f : (Flag F V →₀ k) →ₗ[k] (Flag F V → k) := dRaw (flagBicomod F k) 1 dimSquarePrimitive V
  let g : (Flag F V →₀ k) →ₗ[k] (Flag F V → k) :=
    cupRaw (flagCoalg F k) 1 1 dimCochain dimCochain V
  change f = g
  refine Finsupp.lhom_ext fun H b => ?_
  have hs : (Finsupp.single H b : Flag F V →₀ k) = b • Finsupp.single H 1 := by simp
  rw [hs, map_smul, map_smul]
  congr 1
  funext G
  exact d_dimSquarePrimitive_single V H G
end MartinPhd

end
end DimSquare

section ShuffleCount

/-! Signed counts of shuffles used in Lemma 1.34. -/
open scoped BigOperators
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable

/-- The one-element shuffle at position `i` has `i` inversions. -/
theorem inv_shuffle_singleton {n : ℕ} (i : Fin n) :
    inv (shuffle ({i} : Finset (Fin n))) = i.val := by
  have h := inv_shuffle ({i} : Finset (Fin n))
  simp only [Finset.card_singleton, Nat.reduceAdd, Nat.choose_self,
    Finset.sum_singleton] at h
  omega

/-- Enumerating one-element subsets identifies their signed shuffle count with
an alternating sum over the positions. -/
theorem sum_signed_one_shuffles (k : Type*) [Ring k] (n : ℕ) :
    (∑ X ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun X => X.card = 1),
      (-1 : k) ^ inv (shuffle X)) = ∑ i : Fin n, (-1 : k) ^ i.val := by
  symm
  refine Finset.sum_bij (fun i _ => ({i} : Finset (Fin n))) ?_ ?_ ?_ ?_
  · intro i _; simp
  · intro i _ j _ hij
    simpa using hij
  · intro X hX
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hX).2
    exact ⟨i, Finset.mem_univ _, rfl⟩
  · intro i _
    rw [inv_shuffle_singleton]

/-- The coefficient in the product of a degree-one class and a class of even degree. -/
theorem sum_signed_one_shuffles_odd (k : Type*) [Ring k] (a : ℕ) :
    (∑ X ∈ (Finset.univ : Finset (Finset (Fin (1 + 2 * a)))).filter (fun X => X.card = 1),
      (-1 : k) ^ inv (shuffle X)) = 1 := by
  rw [sum_signed_one_shuffles]
  rw [Fin.sum_neg_one_pow]
  simp [Nat.even_add]

/-- The coefficient in the product of a degree-one class and a class of odd degree. -/
theorem sum_signed_one_shuffles_even (k : Type*) [Ring k] (a : ℕ) :
    (∑ X ∈ (Finset.univ : Finset (Finset (Fin (1 + (2 * a + 1))))).filter (fun X => X.card = 1),
      (-1 : k) ^ inv (shuffle X)) = 0 := by
  rw [sum_signed_one_shuffles]
  rw [Fin.sum_neg_one_pow]
  simp [Nat.even_add]
/-- Gaussian binomials at `-1`, in even ambient dimension. -/
theorem eval_neg_one_gauss_even (n : ℕ) :
    ∀ m : ℕ, (gauss (2 * n) (2 * m)).eval (-1) = (n.choose m : ℤ) ∧
      (gauss (2 * n) (2 * m + 1)).eval (-1) = 0 := by
  induction n with
  | zero =>
    intro m
    cases m with
    | zero => simp [gauss]
    | succ m => simp [gauss, Nat.mul_succ]
  | succ n ih =>
    have ho (m : ℕ) :
        (gauss (2 * n + 1) (2 * m)).eval (-1) = (n.choose m : ℤ) ∧
        (gauss (2 * n + 1) (2 * m + 1)).eval (-1) = (n.choose m : ℤ) := by
      constructor
      · cases m with
        | zero => simp [gauss]
        | succ m =>
          have he : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
          rw [he, gauss]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_X, (ih m).2, zero_add]
          simpa only [← he, even_two_mul, Even.neg_one_pow, one_mul] using (ih (m + 1)).1
      · rw [gauss]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, (ih m).1, (ih m).2, mul_zero, add_zero]
    intro m
    have hn : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [hn]
    constructor
    · cases m with
      | zero => simp [gauss]
      | succ m =>
        have hm : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
        rw [hm, gauss]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, (ho m).2]
        simp only [← hm, even_two_mul, Even.neg_one_pow, one_mul, (ho (m + 1)).1,
          Nat.choose_succ_succ, Nat.cast_add]
    · rw [gauss]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, (ho m).1, (ho m).2]
      simp [pow_add, pow_mul]

/-- Omitting the first position contributes one inversion per chosen element. -/
theorem inv_shuffle_map_succ {n : ℕ} (X : Finset (Fin n)) :
    inv (shuffle (X.map (Fin.succEmb n))) = inv (shuffle X) + X.card := by
  have h := inv_shuffle (X.map (Fin.succEmb n))
  have hX := inv_shuffle X
  simp only [Finset.card_map, Finset.sum_map] at h
  change inv (shuffle (X.map (Fin.succEmb n))) + (X.card + 1).choose 2 =
    ∑ x ∈ X, (x.val + 1 + 1) at h
  have hs : (∑ x ∈ X, (x.val + 1 + 1)) = (∑ x ∈ X, (x.val + 1)) + X.card := by
    simp [Finset.sum_add_distrib]
  rw [hs] at h
  omega

/-- Choosing the first position leaves the inversion count unchanged. -/
theorem inv_shuffle_insert_zero_map_succ {n : ℕ} (X : Finset (Fin n)) :
    inv (shuffle (insert 0 (X.map (Fin.succEmb n)))) = inv (shuffle X) := by
  have hz : (0 : Fin (n + 1)) ∉ X.map (Fin.succEmb n) := by simp
  have h := inv_shuffle (insert 0 (X.map (Fin.succEmb n)))
  have hX := inv_shuffle X
  rw [Finset.card_insert_of_notMem hz, Finset.sum_insert hz] at h
  simp only [Finset.card_map, Finset.sum_map] at h
  change inv (shuffle (insert 0 (X.map (Fin.succEmb n)))) + (X.card + 1 + 1).choose 2 =
    1 + ∑ x ∈ X, (x.val + 1 + 1) at h
  have hs : (∑ x ∈ X, (x.val + 1 + 1)) = (∑ x ∈ X, (x.val + 1)) + X.card := by
    simp [Finset.sum_add_distrib]
  have hc : (X.card + 1 + 1).choose 2 = (X.card + 1).choose 2 + (X.card + 1) := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    simp only [Nat.reduceAdd, Nat.add_comm]
  rw [hs, hc] at h
  omega

/-- Signed enumeration of the `r`-shuffles on `n` positions. -/
def signedShuffleCount (n r : ℕ) : ℤ :=
  ∑ X ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun X => X.card = r),
    (-1 : ℤ) ^ inv (shuffle X)

private theorem sum_powerset_map_succ {n : ℕ} (f : Finset (Fin (n + 1)) → ℤ) :
    (∑ X ∈ ((Finset.univ : Finset (Fin n)).map (Fin.succEmb n)).powerset, f X) =
      ∑ X : Finset (Fin n), f (X.map (Fin.succEmb n)) := by
  simp only [Finset.map_eq_image, Finset.powerset_image, Finset.powerset_univ]
  rw [Finset.sum_image]
  exact fun X _ Y _ h => Finset.image_injective (Fin.succ_injective n) h

/-- The Gaussian-binomial recurrence for signed shuffles. -/
theorem signedShuffleCount_succ (n r : ℕ) :
    signedShuffleCount (n + 1) (r + 1) =
      signedShuffleCount n r + (-1 : ℤ) ^ (r + 1) * signedShuffleCount n (r + 1) := by
  unfold signedShuffleCount
  simp only [Finset.sum_filter]
  conv_lhs => rw [← Finset.powerset_univ]
  have hu : (Finset.univ : Finset (Fin (n + 1))) =
      insert 0 ((Finset.univ : Finset (Fin n)).map (Fin.succEmb n)) := by
    ext x
    cases x using Fin.cases <;> simp [Fin.succEmb]
  rw [hu, Finset.sum_powerset_insert (by simp)]
  rw [sum_powerset_map_succ (n := n), sum_powerset_map_succ (n := n)]
  simp only [Finset.card_map, inv_shuffle_map_succ]
  have hzero (X : Finset (Fin n)) : (0 : Fin (n + 1)) ∉ X.map (Fin.succEmb n) := by simp
  simp only [Finset.card_insert_of_notMem (hzero _), Finset.card_map,
    inv_shuffle_insert_zero_map_succ, Nat.add_right_cancel_iff]
  rw [add_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro X _
  by_cases h : X.card = r + 1
  · simp [h, pow_add, mul_comm]
  · simp [h]

/-- The signed shuffle count is the Gaussian binomial evaluated at `-1`. -/
theorem signedShuffleCount_eq_eval (n r : ℕ) :
    signedShuffleCount n r = (gauss n r).eval (-1) := by
  induction n generalizing r with
  | zero =>
    cases r with
    | zero => simp [signedShuffleCount, gauss, inv_shuffle_eq, Finset.sum_filter, show (default : Finset (Fin 0)) = ∅ from rfl]
    | succ r => simp [signedShuffleCount, gauss, Finset.sum_filter, show (default : Finset (Fin 0)) = ∅ from rfl]
  | succ n ih =>
    cases r with
    | zero => simp [signedShuffleCount, gauss, inv_shuffle_eq, Finset.sum_filter, Finset.card_eq_zero]
    | succ r =>
      rw [signedShuffleCount_succ, ih, ih, gauss]
      simp

/-- The even-even signed shuffle count is an ordinary binomial coefficient. -/
theorem signedShuffleCount_even_even (a b : ℕ) :
    signedShuffleCount (2 * a + 2 * b) (2 * a) = ((a + b).choose a : ℤ) := by
  rw [signedShuffleCount_eq_eval]
  simpa only [Nat.mul_add] using (eval_neg_one_gauss_even (a + b) a).1

/-- The signed shuffle count in an arbitrary coefficient ring. -/
theorem sum_signed_even_shuffles (k : Type*) [Ring k] (a b : ℕ) :
    (∑ X ∈ (Finset.univ : Finset (Finset (Fin (2 * a + 2 * b)))).filter (fun X => X.card = 2 * a),
      (-1 : k) ^ inv (shuffle X)) = ((a + b).choose a : k) := by
  have h := congrArg (Int.castRingHom k) (signedShuffleCount_even_even a b)
  simpa [signedShuffleCount] using h

end MartinPhd

end
end ShuffleCount

section CupProducts

/-! Cup products on the diagonal first page (§1.9). -/
open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- An apartment evaluation computes the scalar of a cup product on the diagonal. -/
theorem cupAlpha_sub_mem_Bpage [CharZero k] (m n : ℕ) (c : k)
    (hc : flagPairing F k (m + n)
      (Tlin (flagBicomod F k) (m + n)
        (cupRaw (flagCoalg F k) m n (alphaCochain m) (alphaCochain n))
        (Finsupp.single (stdFlag F (m + n)) 1)) (epsSteinberg F k (m + n)) = c) :
    cupRaw (flagCoalg F k) m n (alphaCochain m) (alphaCochain n) -
      c • alphaCochain (m + n) ∈ Bpage (flagBicomod F k) 1 (m + n : ℕ) (m + n) := by
  apply (diagonal_mem_Bpage_iff (m + n) _
    (Submodule.sub_mem _ (cupAlpha_mem_Zpage m n)
      (Submodule.smul_mem _ c (alphaCochain_mem (m + n))))).2
  change flagBil F k (m + n) _ (epsSteinberg F k (m + n)) = 0
  rw [map_sub, map_smul]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul]
  change flagPairing F k (m + n) _ _ - c * flagPairing F k (m + n) _ _ = 0
  rw [hc, alpha_apartment_pairing, mul_one, sub_self]
set_option backward.isDefEq.respectTransparency false in
/-- **Lemma 1.34.** Cup products in `E₁(Σ)`:
`[δ_{id,2a}] ⌣ [δ_{id,2b}] = C(a+b, a) [δ_{id,2(a+b)}]`,
`[δ_{id,1}] ⌣ [δ_{id,2a}] = [δ_{id,2a+1}]` and `[δ_{id,1}] ⌣ [δ_{id,2a+1}] = 0`.
Classes in `E₁^{m,0}` are equal iff their representatives differ by an element of `B₁`.

**Gap (proof gap).** In the proof, `[δ_{id,2}] ⌣ [δ_{id,2r}]` should be `(r+1)[δ_{id,2r+2}]`,
not `r·[δ_{id,2r+2}]`; the conclusion `[δ_{id,2}]^{⌣n} = n! [δ_{id,2n}]` is right. -/
theorem lemma_1_34 [CharZero k] (a b : ℕ) :
    cupRaw (flagCoalg F k) (2 * a) (2 * b) (alphaCochain (2 * a)) (alphaCochain (2 * b)) -
        ((a + b).choose a : k) • alphaCochain (2 * a + 2 * b) ∈
      Bpage (flagBicomod F k) 1 (2 * a + 2 * b : ℕ) (2 * a + 2 * b) ∧
    cupRaw (flagCoalg F k) 1 (2 * a) (alphaCochain 1) (alphaCochain (2 * a)) -
        alphaCochain (1 + 2 * a) ∈ Bpage (flagBicomod F k) 1 (1 + 2 * a : ℕ) (1 + 2 * a) ∧
    cupRaw (flagCoalg F k) 1 (2 * a + 1) (alphaCochain 1) (alphaCochain (2 * a + 1)) ∈
      Bpage (flagBicomod F k) 1 (1 + (2 * a + 1) : ℕ) (1 + (2 * a + 1)) := by
  constructor
  · apply cupAlpha_sub_mem_Bpage
    exact (cup_alpha_pair_eps (F := F) (k := k) (2 * a) (2 * b)).trans
      (sum_signed_even_shuffles k a b)
  constructor
  · simpa only [one_smul] using
      (cupAlpha_sub_mem_Bpage (F := F) (k := k) 1 (2 * a) 1 (by
        exact (cup_alpha_pair_eps (F := F) (k := k) 1 (2 * a)).trans
          (sum_signed_one_shuffles_odd k a)))
  · simpa only [zero_smul, sub_zero] using
      (cupAlpha_sub_mem_Bpage (F := F) (k := k) 1 (2 * a + 1) 0 (by
        exact (cup_alpha_pair_eps (F := F) (k := k) 1 (2 * a + 1)).trans
          (sum_signed_one_shuffles_even k a)))

end MartinPhd

end
end CupProducts

section Thm135

/-! Cocycles and products used in Theorem 1.35. -/

open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

set_option backward.isDefEq.respectTransparency false in
/-- The cup product with a zero cochain on the left vanishes. -/
theorem cupRaw_zero_left (x : EBicomodCoalg F k) (m n : ℕ) (g : RawCochain x.toEBicomod) :
    cupRaw x m n 0 g = 0 := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  simp [cupRaw]

set_option backward.isDefEq.respectTransparency false in
/-- The cup product with a zero cochain on the right vanishes. -/
theorem cupRaw_zero_right (x : EBicomodCoalg F k) (m n : ℕ) (f : RawCochain x.toEBicomod) :
    cupRaw x m n f 0 = 0 := by
  funext V
  apply LinearMap.ext
  intro z
  funext G
  simp [cupRaw]

set_option backward.isDefEq.respectTransparency false in
/-- Cup products of cocycles are cocycles. -/
theorem cupRaw_mem_cocycles (x : EBicomodCoalg F k) {m n : ℕ}
    {f g : RawCochain x.toEBicomod} (hf : f ∈ cocycles x.toEBicomod m)
    (hg : g ∈ cocycles x.toEBicomod n) :
    cupRaw x m n f g ∈ cocycles x.toEBicomod (m + n) := by
  refine ⟨cupRaw_mem x hf.1 hg.1, ?_⟩
  change dRaw x.toEBicomod (m + n) (cupRaw x m n f g) = 0
  rw [dRaw_cupRaw x m n f g hf.1 hg.1]
  have hdf : dRaw x.toEBicomod m f = 0 := hf.2
  have hdg : dRaw x.toEBicomod n g = 0 := hg.2
  rw [hdf, hdg, cupRaw_zero_left, cupRaw_zero_right, smul_zero, add_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero unit is a cochain. -/
theorem oneCochain_mem_cochains : oneCochain (F := F) (k := k) ∈
    cochains (flagBicomod F k) 0 := by
  refine ⟨fun V z G hG => ?_, fun V W e z G => ?_⟩
  · change (Finsupp.linearCombination k (fun _ : Flag F V =>
        fun G : Flag F V => if G.len = 0 then (1 : k) else 0)) z G = 0
    rw [lin_const_apply, if_neg hG, mul_zero]
  · change (Finsupp.linearCombination k (fun _ : Flag F W =>
        fun G : Flag F W => if G.len = 0 then (1 : k) else 0))
        ((flagBicomod F k).X.mapEquiv e z) (G.map e) =
      (Finsupp.linearCombination k (fun _ : Flag F V =>
        fun G : Flag F V => if G.len = 0 then (1 : k) else 0)) z G
    rw [lin_const_apply, lin_const_apply, Flag.len_map]
    have hz : (Finsupp.sum (show Flag F W →₀ k from (flagBicomod F k).X.mapEquiv e z)
        (fun _ a => a)) = Finsupp.sum (show Flag F V →₀ k from z) (fun _ a => a) :=
      sum_lmapDomain _ z
    rw [hz]

/-- The degree-zero unit is a cocycle. -/
theorem oneCochain_mem_cocycles : oneCochain (F := F) (k := k) ∈
    cocycles (flagBicomod F k) 0 := by
  refine ⟨oneCochain_mem_cochains, ?_⟩
  change dRaw (flagBicomod F k) 0 oneCochain = 0
  funext V
  apply LinearMap.ext
  intro z
  funext G
  by_cases hG : G.len = 1
  · exact dRaw_zero_len1 oneCochain_mem_cochains V z G hG
  · simp [dRaw, hG]

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero unit is not a coboundary. -/
theorem oneCochain_not_coboundary : oneCochain (F := F) (k := k) ∉
    coboundaries (flagBicomod F k) 0 := by
  intro h
  have hz : oneCochain (F := F) (k := k) = 0 := h
  have he := congrArg (fun f : RawCochain (flagBicomod F k) =>
    f (stdSpace F 0) (Finsupp.single (stdFlag F 0) 1) (stdFlag F 0)) hz
  have hs : (stdFlag F 0).len = 0 := by
    rw [stdFlag_eq_flagOf, ST.len_flagOf]
  change (Finsupp.linearCombination k (fun _ : Flag F (Fin 0 → F) =>
    fun G : Flag F (Fin 0 → F) => if G.len = 0 then (1 : k) else 0))
    (Finsupp.single (stdFlag F 0) 1) (stdFlag F 0) = 0 at he
  rw [Finsupp.linearCombination_single, one_smul, if_pos hs] at he
  exact one_ne_zero he

set_option backward.isDefEq.respectTransparency false in
/-- The cup powers of the Schubert cocycle are cocycles. -/
theorem schPow_mem_cocycles (m : ℕ) : schPow (F := F) (k := k) m ∈
    cocycles (flagBicomod F k) (2 * m) := by
  induction m with
  | zero => simpa [schPow] using (oneCochain_mem_cocycles (F := F) (k := k))
  | succ m ih =>
    have h := cupRaw_mem_cocycles (flagCoalg F k) (lemma_1_29 (F := F) (k := k)).1 ih
    change cupRaw (flagCoalg F k) 2 (2 * m) schCochain (schPow m) ∈
      cocycles (flagBicomod F k) (2 + 2 * m) at h
    simpa only [schPow, Nat.mul_succ, Nat.add_comm] using h

set_option backward.isDefEq.respectTransparency false in
/-- The odd-degree products in Theorem 1.35 are cocycles. -/
theorem dim_cup_schPow_mem_cocycles (m : ℕ) :
    cupRaw (flagCoalg F k) 1 (2 * m) dimCochain (schPow m) ∈
      cocycles (flagBicomod F k) (1 + 2 * m) :=
  cupRaw_mem_cocycles (flagCoalg F k) dimCochain_cocycle (schPow_mem_cocycles m)

/-- A cocycle gives a nonzero cohomology class exactly when it is not a coboundary. -/
theorem cohClass_ne_zero_iff {x : EBicomod F k} {n : ℕ}
    (α : RawCochain x) (hα : α ∈ cocycles x n) :
    cohClass x α hα ≠ 0 ↔ α ∉ coboundaries x n := by
  exact not_congr (Submodule.Quotient.mk_eq_zero _)

/-- The dimension class is nonzero. -/
theorem dimClass_ne_zero :
    cohClass (flagBicomod F k) dimCochain (dimCochain_cocycle (F := F) (k := k)) ≠ 0 :=
  (cohClass_ne_zero_iff _ _).2 (lemma_1_28 (F := F) (k := k)).2

/-- The Schubert class is nonzero. -/
theorem schClass_ne_zero :
    cohClass (flagBicomod F k) schCochain (lemma_1_29 (F := F) (k := k)).1 ≠ 0 :=
  (cohClass_ne_zero_iff _ _).2 (lemma_1_29 (F := F) (k := k)).2

/-- In a one-dimensional cohomology group, any nonzero cocycle class spans. -/
theorem span_cohClass_eq_top_of_finrank_one {x : EBicomod F k} {n : ℕ}
    (hfin : finrank k (H x n) = 1) (α : RawCochain x)
    (hα : α ∈ cocycles x n) (hne : α ∉ coboundaries x n) :
    Submodule.span k {cohClass x α hα} = ⊤ := by
  haveI : FiniteDimensional k (H x n) := Module.finite_of_finrank_pos (by rw [hfin]; decide)
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_singleton ((cohClass_ne_zero_iff α hα).2 hne), hfin]

end MartinPhd

end
end Thm135

section Thm135Cup

/-! # Cup products and the first page (towards Theorem 1.35)

Bilinearity of `cupRaw`, its compatibility with the support filtration, and the fact that the
first-page boundaries are stable under cup products with first-page cycles. -/
open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

section Bilinear
variable (x : EBicomodCoalg F k) (m n : ℕ)

theorem cupRaw_add_left (f f' g : RawCochain x.toEBicomod) :
    cupRaw x m n (f + f') g = cupRaw x m n f g + cupRaw x m n f' g := by
  funext V; apply LinearMap.ext; intro z; funext G
  by_cases hG : G.len = m + n
  · simp only [cupRaw, LinearMap.pi_apply, if_pos hG, Pi.add_apply, LinearMap.add_apply,
      LinearMap.comp_apply]
    rw [LinearMap.comp_add, TensorProduct.map_add_left]
    simp
  · simp [cupRaw, hG]

theorem cupRaw_add_right (f g g' : RawCochain x.toEBicomod) :
    cupRaw x m n f (g + g') = cupRaw x m n f g + cupRaw x m n f g' := by
  funext V; apply LinearMap.ext; intro z; funext G
  by_cases hG : G.len = m + n
  · simp only [cupRaw, LinearMap.pi_apply, if_pos hG, Pi.add_apply, LinearMap.add_apply,
      LinearMap.comp_apply]
    rw [LinearMap.comp_add, TensorProduct.map_add_right]
    simp
  · simp [cupRaw, hG]

theorem cupRaw_smul_left (c : k) (f g : RawCochain x.toEBicomod) :
    cupRaw x m n (c • f) g = c • cupRaw x m n f g := by
  funext V; apply LinearMap.ext; intro z; funext G
  by_cases hG : G.len = m + n
  · simp only [cupRaw, LinearMap.pi_apply, if_pos hG, Pi.smul_apply, LinearMap.smul_apply,
      LinearMap.comp_apply]
    rw [LinearMap.comp_smul, TensorProduct.map_smul_left]
    simp
  · simp [cupRaw, hG]

theorem cupRaw_smul_right (c : k) (f g : RawCochain x.toEBicomod) :
    cupRaw x m n f (c • g) = c • cupRaw x m n f g := by
  funext V; apply LinearMap.ext; intro z; funext G
  by_cases hG : G.len = m + n
  · simp only [cupRaw, LinearMap.pi_apply, if_pos hG, Pi.smul_apply, LinearMap.smul_apply,
      LinearMap.comp_apply]
    rw [LinearMap.comp_smul, TensorProduct.map_smul_right]
    simp
  · simp [cupRaw, hG]

theorem cupRaw_sub_left (f f' g : RawCochain x.toEBicomod) :
    cupRaw x m n (f - f') g = cupRaw x m n f g - cupRaw x m n f' g := by
  rw [sub_eq_add_neg, cupRaw_add_left, ← neg_one_smul k f', cupRaw_smul_left]
  rw [neg_one_smul, sub_eq_add_neg]

theorem cupRaw_sub_right (f g g' : RawCochain x.toEBicomod) :
    cupRaw x m n f (g - g') = cupRaw x m n f g - cupRaw x m n f g' := by
  rw [sub_eq_add_neg, cupRaw_add_right, ← neg_one_smul k g', cupRaw_smul_right]
  rw [neg_one_smul, sub_eq_add_neg]

end Bilinear

section Filt
variable (x : EBicomodCoalg F k)

/-- Cup products add the filtration degrees: supports are in dimension `≥ p + q`. -/
theorem cupRaw_mem_filt {m n : ℕ} {p q : ℤ} {f g : RawCochain x.toEBicomod}
    (hf : f ∈ filt x.toEBicomod p m) (hg : g ∈ filt x.toEBicomod q n) :
    cupRaw x m n f g ∈ filt x.toEBicomod (p + q) (m + n) := by
  rw [mem_filt_iff] at hf hg ⊢
  refine ⟨cupRaw_mem x hf.1 hg.1, fun V hV => ?_⟩
  apply LinearMap.ext; intro z; funext G
  show cupRaw x m n f g V z G = 0
  by_cases hG : G.len = m + n
  · simp only [cupRaw, LinearMap.pi_apply, if_pos hG, LinearMap.comp_apply]
    set S := G.nth m with hS
    have hdim := S.finrank_quotient_add_finrank
    have hcases : (finrank F (sub S) : ℤ) < p ∨ (finrank F (quo S) : ℤ) < q := by
      by_contra hcon
      push_neg at hcon
      have h1 : (finrank F V : ℤ) = finrank F (V ⧸ S) + finrank F S := by exact_mod_cast hdim.symm
      have h2 : (finrank F (sub S) : ℤ) = finrank F S := rfl
      have h3 : (finrank F (quo S) : ℤ) = finrank F (V ⧸ S) := rfl
      omega
    rcases hcases with h | h
    · rw [hf.2 (sub S) h]
      simp
    · rw [hg.2 (quo S) h]
      simp
  · simp [cupRaw, hG]

end Filt

section Bdiag
variable {x : EBicomod F k}

theorem filt_mono_right {p p' : ℤ} (h : p' ≤ p) (n : ℕ) : filt x p n ≤ filt x p' n := by
  intro a ha
  rw [mem_filt_iff] at ha ⊢
  exact ⟨ha.1, fun V hV => ha.2 V (lt_of_lt_of_le hV h)⟩

/-- Cochains supported strictly above the diagonal are first-page boundaries. -/
theorem mem_Bdiag_of_filt (n : ℕ) {k' : ℤ} (hk : (n : ℤ) + 1 ≤ k') {a : RawCochain x}
    (ha : a ∈ filt x k' n) : a ∈ Bpage x 1 (n : ℤ) n :=
  diagonal_filt_succ_le_Bpage x n (filt_mono_right hk n ha)

/-- Differentials of diagonal cochains are first-page boundaries. -/
theorem d_mem_Bdiag (n : ℕ) {β : RawCochain x} (hβ : β ∈ filt x ((n + 1 : ℕ) : ℤ) n) :
    d x n β ∈ Bpage x 1 ((n + 1 : ℕ) : ℤ) (n + 1) := by
  rw [mem_Bpage_succ]
  refine ⟨β, hβ, (d_filt x _ n hβ).1, 0, ⟨Submodule.zero_mem _, ?_⟩, by simp⟩
  rw [map_zero]; exact Submodule.zero_mem _

end Bdiag

section CupB
variable (x : EBicomodCoalg F k)

theorem cup_Bdiag_left (p q : ℕ) {a b : RawCochain (x.toEBicomod)}
    (ha : a ∈ Bpage (x.toEBicomod) 1 (p : ℤ) p)
    (hb : b ∈ Zpage (x.toEBicomod) ((1 : ℕ) : ℤ) (q : ℤ) q) :
    cupRaw (x) p q a b ∈
      Bpage (x.toEBicomod) 1 ((p + q : ℕ) : ℤ) (p + q) := by
  obtain ⟨hbf, hdb⟩ := (mem_Zpage_one _ _ _ _).1 hb
  have hbc := ((mem_filt_iff _ _ _ _).1 hbf).1
  cases p with
  | zero =>
    rw [mem_Bpage_zero] at ha
    have := cupRaw_mem_filt (x) (m := 0) (n := q) ha.1 hbf
    exact mem_Bdiag_of_filt _ (by push_cast; omega) this
  | succ m =>
    obtain ⟨β, hβ, -, c, ⟨hc, -⟩, rfl⟩ := (mem_Bpage_succ _ _ _ _).1 ha
    have hβc := ((mem_filt_iff _ _ _ _).1 hβ).1
    rw [cupRaw_add_left]
    refine Submodule.add_mem _ ?_ (mem_Bdiag_of_filt _ (k' := _) ?_ (cupRaw_mem_filt (x) (m := m + 1) (n := q) hc hbf))
    · have hL := dRaw_cupRaw (x) m q β b hβc hbc
      change cupRaw (x) (m + 1) q (dRaw x.toEBicomod m β) b ∈ _
      rw [eq_sub_of_add_eq hL.symm]
      have e1 : cupRaw (x) m q β b ∈ filt (x.toEBicomod) ((m + q + 1 : ℕ) : ℤ) (m + q) := by
        have := cupRaw_mem_filt (x) (m := m) (n := q) hβ hbf
        have e : ((m + 1 : ℕ) : ℤ) + (q : ℤ) = ((m + q + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e] at this
        exact this
      have hidx : m + 1 + q = m + q + 1 := by omega
      rw [show (m + 1 + q : ℕ) = m + q + 1 from hidx]
      have hdb' : dRaw x.toEBicomod q b ∈
          filt x.toEBicomod ((q : ℤ) + 1) (q + 1) := hdb
      have h2 : cupRaw (x) m (q + 1) β (dRaw x.toEBicomod q b) ∈
          filt (x.toEBicomod) (((m + 1 : ℕ) : ℤ) + ((q : ℤ) + 1)) (m + (q + 1)) :=
        cupRaw_mem_filt (x) (m := m) (n := q + 1) hβ hdb'
      have h3 := mem_Bdiag_of_filt (x := x.toEBicomod) (m + q + 1)
        (k' := ((m + 1 : ℕ) : ℤ) + ((q : ℤ) + 1)) (by push_cast; omega) h2
      exact Submodule.sub_mem _ (d_mem_Bdiag _ e1) (Submodule.smul_mem _ _ h3)
    · push_cast; omega

theorem cup_Bdiag_right (p q : ℕ) {a b : RawCochain x.toEBicomod}
    (ha : a ∈ Zpage x.toEBicomod ((1 : ℕ) : ℤ) (p : ℤ) p)
    (hb : b ∈ Bpage x.toEBicomod 1 (q : ℤ) q) :
    cupRaw x p q a b ∈ Bpage x.toEBicomod 1 ((p + q : ℕ) : ℤ) (p + q) := by
  obtain ⟨haf, hda⟩ := (mem_Zpage_one _ _ _ _).1 ha
  have hac := ((mem_filt_iff _ _ _ _).1 haf).1
  cases q with
  | zero =>
    rw [mem_Bpage_zero] at hb
    have := cupRaw_mem_filt x (m := p) (n := 0) haf hb.1
    exact mem_Bdiag_of_filt _ (by push_cast; omega) this
  | succ m =>
    obtain ⟨β, hβ, -, c, ⟨hc, -⟩, rfl⟩ := (mem_Bpage_succ _ _ _ _).1 hb
    have hβc := ((mem_filt_iff _ _ _ _).1 hβ).1
    rw [cupRaw_add_right]
    refine Submodule.add_mem _ ?_
      (mem_Bdiag_of_filt _ (k' := _) ?_ (cupRaw_mem_filt x (m := p) (n := m + 1) haf hc))
    · have hL := dRaw_cupRaw x p m a β hac hβc
      have hs : ((-1 : k) ^ p) * ((-1 : k) ^ p) = 1 := by rw [← mul_pow]; simp
      have hT : cupRaw x p (m + 1) a (dRaw x.toEBicomod m β) =
          ((-1 : k) ^ p) • (dRaw x.toEBicomod (p + m) (cupRaw x p m a β) -
            cupRaw x (p + 1) m (dRaw x.toEBicomod p a) β) := by
        rw [hL, add_sub_cancel_left, smul_smul, hs, one_smul]
      change cupRaw x p (m + 1) a (dRaw x.toEBicomod m β) ∈ _
      rw [hT]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
      · have e1 : cupRaw x p m a β ∈ filt x.toEBicomod ((p + m + 1 : ℕ) : ℤ) (p + m) := by
          have := cupRaw_mem_filt x (m := p) (n := m) haf hβ
          have e : (p : ℤ) + ((m + 1 : ℕ) : ℤ) = ((p + m + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [e] at this
          exact this
        exact d_mem_Bdiag _ e1
      · have hda' : dRaw x.toEBicomod p a ∈ filt x.toEBicomod ((p : ℤ) + 1) (p + 1) := hda
        have h2 : cupRaw x (p + 1) m (dRaw x.toEBicomod p a) β ∈
            filt x.toEBicomod (((p : ℤ) + 1) + ((m + 1 : ℕ) : ℤ)) (p + 1 + m) :=
          cupRaw_mem_filt x (m := p + 1) (n := m) hda' hβ
        have hidx : p + 1 + m = p + m + 1 := by omega
        rw [hidx] at h2
        have h3 := mem_Bdiag_of_filt (x := x.toEBicomod) (p + m + 1)
          (k' := ((p : ℤ) + 1) + ((m + 1 : ℕ) : ℤ)) (by push_cast; omega) h2
        exact h3
    · push_cast; omega

end CupB

end MartinPhd

end
end Thm135Cup

section Thm135Main

/-! # Theorem 1.35: the calculus of first-page classes on the diagonal

`Pf p a` is the evaluation of `a` on the standard apartment against the Steinberg idempotent;
by `diagonal_mem_Bpage_iff` it is a complete invariant of `E₁^{p,0}` (which is a line). -/
open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

/-- The first-page detector. -/
def Pf (F k) [Field F] [Fintype F] [Field k] (p : ℕ) (a : RawCochain (flagBicomod F k)) : k :=
  flagBil F k p (Tlin (flagBicomod F k) p a (Finsupp.single (stdFlag F p) 1)) (epsSteinberg F k p)

theorem Pf_add (p : ℕ) (a b : RawCochain (flagBicomod F k)) :
    Pf F k p (a + b) = Pf F k p a + Pf F k p b := by
  unfold Pf; rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply]

theorem Pf_sub (p : ℕ) (a b : RawCochain (flagBicomod F k)) :
    Pf F k p (a - b) = Pf F k p a - Pf F k p b := by
  unfold Pf; rw [map_sub, LinearMap.sub_apply, map_sub, LinearMap.sub_apply]

theorem Pf_smul (p : ℕ) (c : k) (a : RawCochain (flagBicomod F k)) :
    Pf F k p (c • a) = c * Pf F k p a := by
  unfold Pf; rw [map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem Pf_alpha (p : ℕ) : Pf F k p (alphaCochain p) = 1 :=
  alpha_apartment_pairing (F := F) (k := k) p

variable [CharZero k]

/-- On the diagonal first page, boundaries are exactly the kernel of `Pf`. -/
theorem Pf_eq_zero_iff (p : ℕ) {a : RawCochain (flagBicomod F k)}
    (ha : a ∈ Zpage (flagBicomod F k) 1 p p) :
    a ∈ Bpage (flagBicomod F k) 1 p p ↔ Pf F k p a = 0 :=
  diagonal_mem_Bpage_iff p a ha

/-- Every diagonal cochain is congruent to `Pf · α` modulo first-page boundaries. -/
theorem sub_Pf_alpha_mem (p : ℕ) {a : RawCochain (flagBicomod F k)} (ha : a ∈ cochains (flagBicomod F k) p) :
    a - Pf F k p a • alphaCochain p ∈ Bpage (flagBicomod F k) 1 p p := by
  have hz : a - Pf F k p a • alphaCochain p ∈ Zpage (flagBicomod F k) 1 p p :=
    cochains_le_diagonal_Zpage _ _
      (Submodule.sub_mem _ ha (Submodule.smul_mem _ _ (alphaCochain_mem_cochains p)))
  exact (Pf_eq_zero_iff p hz).2 (by rw [Pf_sub, Pf_smul, Pf_alpha, mul_one, sub_self])

/-- Boundaries are killed by `Pf`. -/
theorem Pf_eq_zero_of_mem_Bpage (p : ℕ) {a : RawCochain (flagBicomod F k)}
    (ha : a ∈ cochains (flagBicomod F k) p) (hB : a ∈ Bpage (flagBicomod F k) 1 p p) :
    Pf F k p a = 0 :=
  (Pf_eq_zero_iff p (cochains_le_diagonal_Zpage _ _ ha)).1 hB

/-- `Pf` is multiplicative up to the structure constant `Pf (α_p ⌣ α_q)`. -/
theorem Pf_cup (p q : ℕ) {a b : RawCochain (flagBicomod F k)}
    (ha : a ∈ cochains (flagBicomod F k) p) (hb : b ∈ cochains (flagBicomod F k) q) :
    Pf F k (p + q) (cupRaw (flagCoalg F k) p q a b) =
      Pf F k p a * Pf F k q b *
        Pf F k (p + q) (cupRaw (flagCoalg F k) p q (alphaCochain p) (alphaCochain q)) := by
  have hαp := alphaCochain_mem_cochains (F := F) (k := k) p
  have hαq := alphaCochain_mem_cochains (F := F) (k := k) q
  have hu := sub_Pf_alpha_mem p ha
  have hv := sub_Pf_alpha_mem q hb
  set Pa := Pf F k p a with hPa
  set Pb := Pf F k q b with hPb
  set u := a - Pa • alphaCochain p with hu_def
  set v := b - Pb • alphaCochain q with hv_def
  have ha' : a = u + Pa • alphaCochain p := by rw [hu_def]; abel
  have hb' : b = v + Pb • alphaCochain q := by rw [hv_def]; abel
  have huc : u ∈ cochains (flagBicomod F k) p :=
    Submodule.sub_mem _ ha (Submodule.smul_mem _ _ hαp)
  have hvc : v ∈ cochains (flagBicomod F k) q :=
    Submodule.sub_mem _ hb (Submodule.smul_mem _ _ hαq)
  have key : cupRaw (flagCoalg F k) p q a b -
      (Pa * Pb) • cupRaw (flagCoalg F k) p q (alphaCochain p) (alphaCochain q) =
      cupRaw (flagCoalg F k) p q u b +
        Pa • cupRaw (flagCoalg F k) p q (alphaCochain p) v := by
    have e1 : cupRaw (flagCoalg F k) p q a b =
        cupRaw (flagCoalg F k) p q u b + Pa • cupRaw (flagCoalg F k) p q (alphaCochain p) b := by
      conv_lhs => rw [ha']
      rw [cupRaw_add_left, cupRaw_smul_left]
    have e2 : cupRaw (flagCoalg F k) p q (alphaCochain p) b =
        cupRaw (flagCoalg F k) p q (alphaCochain p) v +
          Pb • cupRaw (flagCoalg F k) p q (alphaCochain p) (alphaCochain q) := by
      conv_lhs => rw [hb']
      rw [cupRaw_add_right, cupRaw_smul_right]
    rw [e1, e2, smul_add, smul_smul]
    abel
  have hD : cupRaw (flagCoalg F k) p q u b +
        Pa • cupRaw (flagCoalg F k) p q (alphaCochain p) v ∈
      Bpage (flagBicomod F k) 1 ((p + q : ℕ) : ℤ) (p + q) := by
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
    · exact cup_Bdiag_left (flagCoalg F k) p q hu (cochains_le_diagonal_Zpage _ _ hb)
    · exact cup_Bdiag_right (flagCoalg F k) p q (cochains_le_diagonal_Zpage _ _ hαp) hv
  have hDc : cupRaw (flagCoalg F k) p q u b +
        Pa • cupRaw (flagCoalg F k) p q (alphaCochain p) v ∈ cochains (flagBicomod F k) (p + q) :=
    Submodule.add_mem _ (cupRaw_mem (flagCoalg F k) huc hb)
      (Submodule.smul_mem _ _ (cupRaw_mem (flagCoalg F k) hαp hvc))
  have h0 := Pf_eq_zero_of_mem_Bpage (p + q) hDc hD
  rw [← key, Pf_sub, Pf_smul] at h0
  linear_combination h0

/-- In dimension `≤ 1` there is a unique flag. -/
theorem flag_eq_of_finrank_le_one {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hV : finrank F V ≤ 1) (G H : Flag F V) : G = H := by
  have hsub : ∀ K : Flag F V, K.carrier = {⊥, ⊤} := by
    intro K
    apply Finset.Subset.antisymm
    · intro A hA
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have hle : finrank F A ≤ 1 := (Submodule.finrank_le A).trans hV
      by_cases h0 : finrank F A = 0
      · left; exact Submodule.finrank_eq_zero.1 h0
      · right
        apply Submodule.eq_top_of_finrank_eq
        have hAV := Submodule.finrank_le A
        have : finrank F A = 1 := by omega
        omega
    · intro A hA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with rfl | rfl
      · exact K.bot_mem
      · exact K.top_mem
  exact Flag.ext ((hsub G).trans (hsub H).symm)

theorem finsupp_sum_eq_apply {α : Type*} [Subsingleton α] (z : α →₀ k) (G : α) :
    (z.sum fun _ a => a) = z G := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.sum_add_index' (by simp) (by simp), hf, hg]; simp
  | single H c => rw [Subsingleton.elim H G]; simp

/-- On the zero-dimensional and one-dimensional standard spaces, `α_p` agrees with the unit
cochains `1` and `dim`. -/
theorem Pf_one : Pf F k 0 oneCochain = 1 := by
  have hc : oneCochain (F := F) (k := k) - alphaCochain 0 ∈ cochains (flagBicomod F k) 0 :=
    Submodule.sub_mem _ oneCochain_mem_cochains (alphaCochain_mem_cochains 0)
  have h0 : (oneCochain (F := F) (k := k) - alphaCochain 0 : RawCochain (flagBicomod F k)) (stdSpace F 0) = 0 := by
    apply LinearMap.ext; intro z
    show (oneCochain (stdSpace F 0) z - alphaCochain 0 (stdSpace F 0) z) = 0
    funext G
    have hV : finrank F (stdSpace F 0) = 0 := by simp [stdSpace]
    show oneCochain (stdSpace F 0) z G - alphaCochain 0 (stdSpace F 0) z G = 0
    rw [alphaCochain_apply]
    change (Finsupp.linearCombination k (fun _ : Flag F (stdSpace F 0) =>
        fun G : Flag F (stdSpace F 0) => if G.len = 0 then (1 : k) else 0)) z G - _ = 0
    rw [lin_const_apply]
    have hl : G.len = 0 := by
      have := ST.len_le_finrank (F := F) G
      omega
    have hcomp : G.IsComplete := by
      unfold Flag.IsComplete; rw [hl]; exact hV.symm
    rw [if_pos hl, if_pos ⟨hV, hcomp⟩]
    haveI : Subsingleton (Flag F (stdSpace F 0)) :=
      ⟨fun G H => flag_eq_of_finrank_le_one (by omega) G H⟩
    have := finsupp_sum_eq_apply (show Flag F (stdSpace F 0) →₀ k from z) G
    show ((show Flag F (stdSpace F 0) →₀ k from z).sum fun _ a => a) * 1 -
      (show Flag F (stdSpace F 0) →₀ k from z) G * 1 = 0
    rw [this]; ring
  have := Pf_eq_zero_of_mem_Bpage 0 hc (diagonal_mem_Bpage_of_stdSpace_eq_zero _ 0 hc h0)
  rw [Pf_sub, Pf_alpha] at this
  linear_combination this

theorem Pf_dim : Pf F k 1 dimCochain = 1 := by
  have hc : dimCochain (F := F) (k := k) - alphaCochain 1 ∈ cochains (flagBicomod F k) 1 :=
    Submodule.sub_mem _ dimCochain_mem_cochains (alphaCochain_mem_cochains 1)
  have h0 : (dimCochain (F := F) (k := k) - alphaCochain 1 : RawCochain (flagBicomod F k))
      (stdSpace F 1) = 0 := by
    apply LinearMap.ext; intro z
    have hV : finrank F (stdSpace F 1) = 1 := by simp [stdSpace]
    funext G
    show dimCochain (stdSpace F 1) z G - alphaCochain 1 (stdSpace F 1) z G = 0
    rw [alphaCochain_apply, dimCochain_apply]
    have hl : G.len = 1 := by
      have h1 := ST.len_le_finrank (F := F) G
      haveI : Nontrivial (stdSpace F 1) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
      have h2 : ({⊥, ⊤} : Finset (Submodule F (stdSpace F 1))) ⊆ G.carrier := by
        intro A hA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hA
        rcases hA with rfl | rfl
        · exact G.bot_mem
        · exact G.top_mem
      have h3 := Finset.card_le_card h2
      rw [Finset.card_pair bot_ne_top, G.card_eq_len_succ] at h3
      omega
    have hcomp : G.IsComplete := by
      unfold Flag.IsComplete; rw [hl]; exact hV.symm
    rw [if_pos hl, if_pos ⟨hV, hcomp⟩, hV]
    haveI : Subsingleton (Flag F (stdSpace F 1)) :=
      ⟨fun G H => flag_eq_of_finrank_le_one (by omega) G H⟩
    have := finsupp_sum_eq_apply (show Flag F (stdSpace F 1) →₀ k from z) G
    show ((show Flag F (stdSpace F 1) →₀ k from z).sum fun _ a => a) * ((1 : ℕ) : k) -
      (show Flag F (stdSpace F 1) →₀ k from z) G * 1 = 0
    rw [this]; simp
  have := Pf_eq_zero_of_mem_Bpage 1 hc (diagonal_mem_Bpage_of_stdSpace_eq_zero _ 1 hc h0)
  rw [Pf_sub, Pf_alpha] at this
  linear_combination this

section Z
variable (x : EBicomod F k)

/-- A cocycle supported strictly above the diagonal is a coboundary
(consequence of Lemma 1.25: relative projectivity). -/
theorem coboundary_of_filt_succ (hx : x.X.IsRelativelyProjective) (n : ℕ) {w : RawCochain x}
    (hw : w ∈ filt x ((n : ℤ) + 1) n) (hwc : w ∈ cocycles x n) : w ∈ coboundaries x n := by
  have hmem : (Submodule.Quotient.mk (⟨w, hwc⟩ : cocycles x n) : H x n) ∈
      filtH x ((n : ℤ) + 1) n :=
    Submodule.mem_map.2 ⟨⟨w, hwc⟩, hw, rfl⟩
  rw [filtH_succ_eq_bot x hx n, Submodule.mem_bot] at hmem
  exact (Submodule.Quotient.mk_eq_zero ((coboundaries x n).comap (cocycles x n).subtype)).1 hmem

/-- Cocycles that are first-page boundaries on the diagonal are coboundaries. -/
theorem coboundary_of_Bpage (hx : x.X.IsRelativelyProjective) (n : ℕ) {c : RawCochain x}
    (hc : c ∈ cocycles x n) (hB : c ∈ Bpage x 1 (n : ℤ) n) : c ∈ coboundaries x n := by
  cases n with
  | zero =>
    rw [mem_Bpage_zero] at hB
    have h1 : c ∈ filt x 1 0 := by simpa using hB.1
    rw [filt_one_zero, Submodule.mem_bot] at h1
    rw [h1]; exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨β, hβ, -, w, ⟨hw, -⟩, rfl⟩ := (mem_Bpage_succ x _ m c).1 hB
    have hβc := ((mem_filt_iff _ _ _ _).1 hβ).1
    have hdβ : d x m β ∈ coboundaries x (m + 1) := Submodule.mem_map.2 ⟨β, hβc, rfl⟩
    have hdd : d x (m + 1) (d x m β) = 0 := d_comp_d x m hβc
    have hwc : w ∈ cocycles x (m + 1) := by
      refine ⟨((mem_filt_iff _ _ _ _).1 hw).1, ?_⟩
      have : d x (m + 1) (d x m β + w) = 0 := hc.2
      rw [map_add, hdd, zero_add] at this
      exact this
    exact Submodule.add_mem _ hdβ
      (coboundary_of_filt_succ x hx (m + 1) (by simpa using hw) hwc)

/-- The differential of a diagonal first-page boundary comes from `F^{n+1}`. -/
theorem d_eq_of_Bpage (n : ℕ) {a : RawCochain x} (hB : a ∈ Bpage x 1 (n : ℤ) n) :
    ∃ w ∈ filt x ((n : ℤ) + 1) n, d x n a = d x n w := by
  cases n with
  | zero =>
    rw [mem_Bpage_zero] at hB
    exact ⟨a, by simpa using hB.1, rfl⟩
  | succ m =>
    obtain ⟨β, hβ, -, w, ⟨hw, -⟩, rfl⟩ := (mem_Bpage_succ x _ m a).1 hB
    have hβc := ((mem_filt_iff _ _ _ _).1 hβ).1
    refine ⟨w, by simpa using hw, ?_⟩
    rw [map_add, d_comp_d x m hβc, zero_add]

end Z

/-- A diagonal cocycle with nonzero first-page class, next to another one, is not a coboundary. -/
theorem not_coboundary_of_Pf (n : ℕ) {z z' : RawCochain (flagBicomod F k)}
    (hz : z ∈ cocycles (flagBicomod F k) (n + 1)) (hPz : Pf F k (n + 1) z ≠ 0)
    (hz' : z' ∈ cocycles (flagBicomod F k) n) (hPz' : Pf F k n z' ≠ 0) :
    z ∉ coboundaries (flagBicomod F k) (n + 1) := by
  rintro ⟨β, hβc, hβ⟩
  have hdz' : d (flagBicomod F k) n z' = 0 := hz'.2
  -- the class of β
  have hB1 := sub_Pf_alpha_mem n hβc
  obtain ⟨w1, hw1, hd1⟩ := d_eq_of_Bpage _ n hB1
  -- the class of α_n in terms of z'
  have hB2 := Submodule.smul_mem _ (Pf F k n z')⁻¹ (sub_Pf_alpha_mem n hz'.1)
  obtain ⟨w2, hw2, hd2⟩ := d_eq_of_Bpage _ n hB2
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hPz', one_smul, map_sub, map_smul, hdz', smul_zero,
    zero_sub] at hd2
  rw [map_sub, map_smul] at hd1
  have hzd : z = d (flagBicomod F k) n w1 - Pf F k n β • d (flagBicomod F k) n w2 := by
    rw [← hβ]
    have : d (flagBicomod F k) n β = d (flagBicomod F k) n w1 +
        Pf F k n β • d (flagBicomod F k) n (alphaCochain n) := by rw [← hd1]; abel
    rw [this]
    have h3 : d (flagBicomod F k) n (alphaCochain n) = -d (flagBicomod F k) n w2 := by
      rw [← hd2]; simp
    rw [h3]; simp [sub_eq_add_neg]
  have hBz : z ∈ Bpage (flagBicomod F k) 1 ((n + 1 : ℕ) : ℤ) (n + 1) := by
    rw [hzd]
    refine Submodule.sub_mem _ (d_mem_Bdiag n (by simpa using hw1))
      (Submodule.smul_mem _ _ (d_mem_Bdiag n (by simpa using hw2)))
  exact hPz (Pf_eq_zero_of_mem_Bpage (n + 1) hz.1 hBz)

/-- Structure constants of the diagonal first page. -/
theorem Pf_cup_alpha_even (a b : ℕ) :
    Pf F k (2 * a + 2 * b) (cupRaw (flagCoalg F k) (2 * a) (2 * b) (alphaCochain (2 * a))
      (alphaCochain (2 * b))) = (((a + b).choose a : ℕ) : k) :=
  (cup_alpha_pair_eps (F := F) (k := k) (2 * a) (2 * b)).trans (sum_signed_even_shuffles k a b)

theorem Pf_cup_alpha_one_even (a : ℕ) :
    Pf F k (1 + 2 * a) (cupRaw (flagCoalg F k) 1 (2 * a) (alphaCochain 1)
      (alphaCochain (2 * a))) = 1 :=
  (cup_alpha_pair_eps (F := F) (k := k) 1 (2 * a)).trans (sum_signed_one_shuffles_odd k a)

theorem Pf_cup_alpha_two_one :
    Pf F k (2 + 1) (cupRaw (flagCoalg F k) 2 1 (alphaCochain 2) (alphaCochain 1)) = 1 := by
  refine (cup_alpha_pair_eps (F := F) (k := k) 2 1).trans ?_
  have h : signedShuffleCount 3 2 = 1 := by
    simp only [signedShuffleCount, inv_shuffle_eq]
    decide
  have h2 : ((signedShuffleCount 3 2 : ℤ) : k) = 1 := by rw [h]; simp
  refine Eq.trans ?_ h2
  simp [signedShuffleCount]

theorem Pf_sch_ne_zero : Pf F k 2 schCochain ≠ 0 := by
  intro h0
  have hx := GLSpecies.isRelativelyProjective_of_charZero (F := F) (k := k)
    (flagBicomod F k).X
  have hZ : schCochain (F := F) (k := k) ∈ Zpage (flagBicomod F k) 1 (2 : ℕ) 2 :=
    cochains_le_diagonal_Zpage _ _ schCochain_mem_cochains
  have hB := (Pf_eq_zero_iff 2 hZ).2 h0
  exact (lemma_1_29 (F := F) (k := k)).2
    (coboundary_of_Bpage _ hx 2 (lemma_1_29 (F := F) (k := k)).1 hB)

theorem Pf_schPow (m : ℕ) :
    Pf F k (2 * m) (schPow m) = (Pf F k 2 schCochain) ^ m * (m.factorial : k) := by
  induction m with
  | zero => simpa [schPow] using Pf_one (F := F) (k := k)
  | succ m ih =>
    have hs : schPow (F := F) (k := k) m ∈ cochains (flagBicomod F k) (2 * m) :=
      (schPow_mem_cocycles m).1
    have K := Pf_cup_alpha_even (F := F) (k := k) 1 m
    simp only [mul_one, Nat.choose_one_right] at K
    rw [show 2 * (m + 1) = 2 + 2 * m by omega]
    change Pf F k (2 + 2 * m) (cupRaw (flagCoalg F k) 2 (2 * m) schCochain (schPow m)) = _
    rw [Pf_cup 2 (2 * m) schCochain_mem_cochains hs, ih, K]
    push_cast [Nat.factorial_succ]
    ring

theorem Pf_dim_schPow (m : ℕ) :
    Pf F k (1 + 2 * m) (cupRaw (flagCoalg F k) 1 (2 * m) dimCochain (schPow m)) =
      (Pf F k 2 schCochain) ^ m * (m.factorial : k) := by
  have hs : schPow (F := F) (k := k) m ∈ cochains (flagBicomod F k) (2 * m) :=
    (schPow_mem_cocycles m).1
  rw [Pf_cup 1 (2 * m) dimCochain_mem_cochains hs, Pf_dim, Pf_schPow,
    Pf_cup_alpha_one_even, one_mul, mul_one]

theorem schPow_cochains (m : ℕ) : schPow (F := F) (k := k) m ∈ cochains (flagBicomod F k) (2 * m) :=
  (schPow_mem_cocycles m).1

theorem Pf_schPow_ne_zero (m : ℕ) : Pf F k (2 * m) (schPow m) ≠ 0 := by
  rw [Pf_schPow]
  exact mul_ne_zero (pow_ne_zero _ Pf_sch_ne_zero) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))

theorem Pf_dim_schPow_ne_zero (m : ℕ) :
    Pf F k (1 + 2 * m) (cupRaw (flagCoalg F k) 1 (2 * m) dimCochain (schPow m)) ≠ 0 := by
  rw [Pf_dim_schPow]
  exact mul_ne_zero (pow_ne_zero _ Pf_sch_ne_zero) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))

theorem dim_schPow_cocycle (m : ℕ) :
    cupRaw (flagCoalg F k) 1 (2 * m) dimCochain (schPow m) ∈
      cocycles (flagBicomod F k) (1 + 2 * m) :=
  dim_cup_schPow_mem_cocycles m

theorem schPow_not_coboundary (m : ℕ) :
    schPow (F := F) (k := k) m ∉ coboundaries (flagBicomod F k) (2 * m) := by
  cases m with
  | zero => exact oneCochain_not_coboundary
  | succ m =>
    have e1 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    have e2 : 1 + 2 * m = 2 * m + 1 := by omega
    have hz := schPow_mem_cocycles (F := F) (k := k) (m + 1)
    have hPz := Pf_schPow_ne_zero (F := F) (k := k) (m + 1)
    have hz' := dim_schPow_cocycle (F := F) (k := k) m
    have hPz' := Pf_dim_schPow_ne_zero (F := F) (k := k) m
    rw [e1] at hz hPz ⊢
    rw [e2] at hz' hPz'
    exact not_coboundary_of_Pf (2 * m + 1) hz hPz hz' hPz'

theorem dim_schPow_not_coboundary (m : ℕ) :
    cupRaw (flagCoalg F k) 1 (2 * m) dimCochain (schPow m) ∉
      coboundaries (flagBicomod F k) (1 + 2 * m) := by
  have e2 : 1 + 2 * m = 2 * m + 1 := by omega
  have hz := dim_schPow_cocycle (F := F) (k := k) m
  have hPz := Pf_dim_schPow_ne_zero (F := F) (k := k) m
  rw [e2] at hz hPz ⊢
  exact not_coboundary_of_Pf (2 * m) hz hPz (schPow_mem_cocycles m) (Pf_schPow_ne_zero m)

/-- A nonzero first-page class which is not a coboundary spans its cohomology line. -/
theorem H_line (n : ℕ) {z : RawCochain (flagBicomod F k)} (hz : z ∈ cocycles (flagBicomod F k) n)
    (hPz : Pf F k n z ≠ 0) (hnc : z ∉ coboundaries (flagBicomod F k) n) :
    finrank k (H (flagBicomod F k) n) = 1 := by
  have hx := GLSpecies.isRelativelyProjective_of_charZero (F := F) (k := k) (flagBicomod F k).X
  have hne : cohClass (flagBicomod F k) z hz ≠ 0 := (cohClass_ne_zero_iff z hz).2 hnc
  rw [finrank_eq_one_iff_of_nonzero' _ hne]
  intro w
  induction w using Submodule.Quotient.induction_on with
  | _ c =>
    obtain ⟨c, hc⟩ := c
    refine ⟨Pf F k n c / Pf F k n z, ?_⟩
    have hB : c - (Pf F k n c / Pf F k n z) • z ∈ Bpage (flagBicomod F k) 1 (n : ℤ) n := by
      have h1 := sub_Pf_alpha_mem n hc.1
      have h2 := Submodule.smul_mem _ (Pf F k n c / Pf F k n z) (sub_Pf_alpha_mem n hz.1)
      have h3 := Submodule.sub_mem _ h1 h2
      have : c - Pf F k n c • alphaCochain n -
          (Pf F k n c / Pf F k n z) • (z - Pf F k n z • alphaCochain n) =
          c - (Pf F k n c / Pf F k n z) • z := by
        rw [smul_sub, smul_smul, div_mul_cancel₀ _ hPz]; abel
      rwa [this] at h3
    have hcc : c - (Pf F k n c / Pf F k n z) • z ∈ cocycles (flagBicomod F k) n :=
      Submodule.sub_mem _ hc (Submodule.smul_mem _ _ hz)
    have hcb := coboundary_of_Bpage _ hx n hcc hB
    have : ((Pf F k n c / Pf F k n z) • cohClass (flagBicomod F k) z hz : H (flagBicomod F k) n) =
        Submodule.Quotient.mk ⟨c, hc⟩ := by
      rw [eq_comm]
      change Submodule.Quotient.mk (⟨c, hc⟩ : cocycles (flagBicomod F k) n) =
        (Pf F k n c / Pf F k n z) • (Submodule.Quotient.mk ⟨z, hz⟩ : H (flagBicomod F k) n)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      exact hcb
    exact this

end MartinPhd

end
end Thm135Main

section Thm135Final

/-! # Theorem 1.35

The cohomology of the flag species is a line in every degree, spanned by `sch^m`
(degree `2m`) and `dim ⌣ sch^m` (degree `2m+1`). The proof detects classes on the diagonal
of the first page by `Pf` (see `Chapter1Section9Thm135Main`). -/
open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

/-- **Theorem 1.35.** `H•(Σ) ≅ Λ[x] ⊗ k[y]` as graded algebras, with `dim ↦ x` (degree 1)
and `sch ↦ y` (degree 2). Stated concretely: each `Hⁿ(Σ)` is a line, spanned by
`[sch^m]` for `n = 2m` and by `[dim ⌣ sch^m]` for `n = 2m + 1`; `dim ⌣ dim` is a
coboundary and `dim, sch` commute up to coboundaries. Analogue of [Tam17, Thm. III.5.6]. -/
theorem thm_1_35 [CharZero k] :
    (∀ n, finrank k (H (flagBicomod F k) n) = 1) ∧
    (∀ m, schPow (F := F) (k := k) m ∈ cocycles (flagBicomod F k) (2 * m) ∧
      ∀ h : schPow (F := F) (k := k) m ∈ cocycles (flagBicomod F k) (2 * m),
        Submodule.span k {cohClass (flagBicomod F k) _ h} = ⊤) ∧
    (∀ m, cupRaw (flagCoalg F k) 1 (2 * m) dimCochain (schPow m) ∈
        cocycles (flagBicomod F k) (1 + 2 * m) ∧
      ∀ h : cupRaw (flagCoalg F k) 1 (2 * m) dimCochain (schPow m) ∈
          cocycles (flagBicomod F k) (1 + 2 * m),
        Submodule.span k {cohClass (flagBicomod F k) _ h} = ⊤) ∧
    cupRaw (flagCoalg F k) 1 1 dimCochain dimCochain ∈ coboundaries (flagBicomod F k) 2 ∧
    cupRaw (flagCoalg F k) 2 1 schCochain dimCochain -
        cupRaw (flagCoalg F k) 1 2 dimCochain schCochain ∈ coboundaries (flagBicomod F k) 3 :=
  by
  have hx := GLSpecies.isRelativelyProjective_of_charZero (F := F) (k := k) (flagBicomod F k).X
  have hev (m : ℕ) : finrank k (H (flagBicomod F k) (2 * m)) = 1 :=
    H_line (2 * m) (schPow_mem_cocycles m) (Pf_schPow_ne_zero m) (schPow_not_coboundary m)
  have hod (m : ℕ) : finrank k (H (flagBicomod F k) (1 + 2 * m)) = 1 :=
    H_line (1 + 2 * m) (dim_schPow_cocycle m) (Pf_dim_schPow_ne_zero m)
      (dim_schPow_not_coboundary m)
  refine ⟨fun n => ?_, fun m => ⟨schPow_mem_cocycles m, fun h => ?_⟩,
    fun m => ⟨dim_schPow_cocycle m, fun h => ?_⟩, dim_cup_dim_mem_coboundaries, ?_⟩
  · obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · exact hev m
    · rw [show 2 * m + 1 = 1 + 2 * m by omega]; exact hod m
  · exact span_cohClass_eq_top_of_finrank_one (hev m) _ h (schPow_not_coboundary m)
  · exact span_cohClass_eq_top_of_finrank_one (hod m) _ h (dim_schPow_not_coboundary m)
  · have hs := lemma_1_29 (F := F) (k := k)
    have hd := lemma_1_28 (F := F) (k := k)
    have h1 := cupRaw_mem_cocycles (flagCoalg F k) (m := 2) (n := 1) hs.1 hd.1
    have h2 := cupRaw_mem_cocycles (flagCoalg F k) (m := 1) (n := 2) hd.1 hs.1
    change cupRaw (flagCoalg F k) 2 1 schCochain dimCochain ∈
        cocycles (flagBicomod F k) (2 + 1) at h1
    change cupRaw (flagCoalg F k) 1 2 dimCochain schCochain ∈
        cocycles (flagBicomod F k) (1 + 2) at h2
    have hc : cupRaw (flagCoalg F k) 2 1 schCochain dimCochain -
        cupRaw (flagCoalg F k) 1 2 dimCochain schCochain ∈ cocycles (flagBicomod F k) 3 :=
      Submodule.sub_mem _ h1 h2
    have hP : Pf F k 3 (cupRaw (flagCoalg F k) 2 1 schCochain dimCochain -
        cupRaw (flagCoalg F k) 1 2 dimCochain schCochain) = 0 := by
      rw [Pf_sub]
      have a1 := Pf_cup (F := F) (k := k) 2 1 schCochain_mem_cochains dimCochain_mem_cochains
      have a2 := Pf_cup (F := F) (k := k) 1 2 dimCochain_mem_cochains schCochain_mem_cochains
      have k1 := Pf_cup_alpha_two_one (F := F) (k := k)
      have k2 := Pf_cup_alpha_one_even (F := F) (k := k) 1
      simp only [mul_one] at k2
      change Pf F k (2 + 1) _ - Pf F k (1 + 2) _ = 0
      rw [a1, a2, k1, k2, Pf_dim]
      ring
    have hZ : cupRaw (flagCoalg F k) 2 1 schCochain dimCochain -
        cupRaw (flagCoalg F k) 1 2 dimCochain schCochain ∈
        Zpage (flagBicomod F k) 1 (3 : ℕ) 3 := cochains_le_diagonal_Zpage _ _ hc.1
    exact coboundary_of_Bpage _ hx 3 hc ((Pf_eq_zero_iff 3 hZ).2 hP)

end MartinPhd

end
end Thm135Final

section Thm136Detect

/-! # Theorem 1.36: detection on the diagonal first page, for an arbitrary bicomodule

The proof of `diagonal_mem_Bpage_iff`, with the standard flag replaced by an arbitrary
evaluation point `s0` and a reference class `α0` of pairing `1`. Applied to `Σ` and to `L`. -/
open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

private theorem subquot_mk_eq_zero_iff' {M : Type*} [AddCommGroup M] [Module k M]
    {A B : Submodule k M} {a : M} (ha : a ∈ A) :
    (Subquot.mk a ha : Subquot A B) = 0 ↔ a ∈ B := by
  exact Submodule.Quotient.mk_eq_zero _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Evaluation on the standard apartment detects classes on the diagonal first page. -/
theorem diagonal_detect (x : EBicomod F k) (p : ℕ) (s0 : x.X.ev (stdSpace F p))
    (α0 : RawCochain x) (hα0 : α0 ∈ Zpage x 1 p p)
    (hα1 : flagPairing F k p (Tlin x p α0 s0) (epsSteinberg F k p) = 1)
    (hd : finrank k (E x 1 p p) = 1)
    (a : RawCochain x) (ha : a ∈ Zpage x 1 p p) :
    a ∈ Bpage x 1 p p ↔
      flagPairing F k p (Tlin x p a s0) (epsSteinberg F k p) = 0 := by
  obtain ⟨e, he⟩ := (cor_1_9 F k p).2
  let ε : steinberg F k p := ⟨epsSteinberg F k p, by
    rw [steinberg_eq, epsSteinberg_eq]; exact ST.eps_mem_St k _⟩
  let f : Zpage x 1 p p →ₗ[k] k :=
    { toFun := fun z => e ((Theta x p p z).1 s0) ε
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
      (Tlin x p z.1 s0) (epsSteinberg F k p) := by
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
        (Tlin x p z s0) (epsSteinberg F k p) := hf ⟨z, hz⟩
  have hα : L (Subquot.mk _ hα0) = 1 := by
    rw [hL]
    exact hα1
  have hinj : Function.Injective L := by
    have hn : (Subquot.mk _ hα0 : E x 1 p p) ≠ 0 := by
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
    have hz : (Subquot.mk a ha : E x 1 p p) = 0 := (subquot_mk_eq_zero_iff' ha).2 h
    rw [hz, map_zero]
  · intro h
    have hz : (Subquot.mk a ha : E x 1 p p) = 0 := hinj (h.trans (map_zero L).symm)
    exact (subquot_mk_eq_zero_iff' ha).1 hz
end MartinPhd

end
end Thm136Detect

section Thm136

/-! # Theorem 1.36

The inclusion `L → Σ` induces an isomorphism in cohomology. We run the argument of Theorem 1.35
for the bicomodule `L` of complete flags: the first-page class of a diagonal cochain is
detected by the evaluation `PfL` at the standard flag, and `E₁^{p,0}(L)` is a line. -/
open Module
noncomputable section
namespace MartinPhd
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

/-- The standard flag as an element of `L(Fᵖ)`. -/
def s0L (F k) [Field F] [Fintype F] [Field k] (p : ℕ) :
    (completeFlagBicomod F k).X.ev (stdSpace F p) :=
  ⟨Finsupp.single (stdFlag F p) 1, Finsupp.single_mem_supported k _ (stdFlag_isComplete p)⟩

/-- The first-page detector for `L`. -/
def PfL (F k) [Field F] [Fintype F] [Field k] (p : ℕ)
    (a : RawCochain (completeFlagBicomod F k)) : k :=
  flagBil F k p (Tlin (completeFlagBicomod F k) p a (s0L F k p)) (epsSteinberg F k p)

theorem PfL_add (p : ℕ) (a b : RawCochain (completeFlagBicomod F k)) :
    PfL F k p (a + b) = PfL F k p a + PfL F k p b := by
  unfold PfL; rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply]

theorem PfL_sub (p : ℕ) (a b : RawCochain (completeFlagBicomod F k)) :
    PfL F k p (a - b) = PfL F k p a - PfL F k p b := by
  unfold PfL; rw [map_sub, LinearMap.sub_apply, map_sub, LinearMap.sub_apply]

theorem PfL_smul (p : ℕ) (c : k) (a : RawCochain (completeFlagBicomod F k)) :
    PfL F k p (c • a) = c * PfL F k p a := by
  unfold PfL; rw [map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem PfL_restrict (p : ℕ) (a : RawCochain (flagBicomod F k)) :
    PfL F k p (restrictCochain a) = Pf F k p a := rfl

theorem rep_single_L (p : ℕ) (g : GLn F p) (G : Flag F (Fin p → F)) (hG : G.IsComplete) :
    ((completeFlagBicomod F k).X.rep p g
      ⟨Finsupp.single G 1, Finsupp.single_mem_supported k _ hG⟩ :
        (completeFlagBicomod F k).X.ev (stdSpace F p)).1 = Finsupp.single (g • G) 1 := by
  change Finsupp.lmapDomain k k (Flag.map g) (Finsupp.single G 1) = _
  simp [Finsupp.lmapDomain_apply]; rfl

variable [CharZero k]

/-- Evaluation of first-page classes of `L` at the standard flag. -/
def eL (p : ℕ) : E (completeFlagBicomod F k) 1 p p →ₗ[k] HSigma F k p p :=
  Submodule.liftQ _
    ({ toFun := fun z => (Theta (completeFlagBicomod F k) p p z).1 (s0L F k p)
       map_add' := by
         intro z w
         rw [map_add]
         change ((Theta (completeFlagBicomod F k) p p z).1 +
           (Theta (completeFlagBicomod F k) p p w).1) _ = _
         rw [LinearMap.add_apply]
       map_smul' := by
         intro c z
         rw [map_smul]
         change (c • (Theta (completeFlagBicomod F k) p p z).1) _ = _
         rw [LinearMap.smul_apply]
         rfl } :
      Zpage (completeFlagBicomod F k) 1 p p →ₗ[k] HSigma F k p p)
    (by
      intro z hz
      rw [LinearMap.mem_ker]
      have h := Theta_eq_zero_of_Bpage (completeFlagBicomod F k) p p z hz
      change (Theta (completeFlagBicomod F k) p p z).1 _ = 0
      rw [h]
      rfl)

theorem eL_mem_fixed (p : ℕ) (z : E (completeFlagBicomod F k) 1 p p) :
    eL (F := F) (k := k) p z ∈ hsigmaFixed p (borel F p) := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    intro g hg
    change hsigmaRep F k p p g ((Theta (completeFlagBicomod F k) p p z).1 (s0L F k p)) = _
    have h := LinearMap.congr_fun ((Theta (completeFlagBicomod F k) p p z).2 g) (s0L F k p)
    change (Theta (completeFlagBicomod F k) p p z).1
      (((completeFlagBicomod F k).X.rep p g) (s0L F k p)) =
      hsigmaRep F k p p g ((Theta (completeFlagBicomod F k) p p z).1 (s0L F k p)) at h
    have hs : ((completeFlagBicomod F k).X.rep p g) (s0L F k p) = s0L F k p := by
      apply Subtype.ext
      rw [s0L, rep_single_L p g _ (stdFlag_isComplete p)]
      have : g • stdFlag F p = stdFlag F p := hg
      rw [this]
    change hsigmaRep F k p p g ((Theta (completeFlagBicomod F k) p p z).1 (s0L F k p)) =
      (Theta (completeFlagBicomod F k) p p z).1 (s0L F k p)
    rw [← h, hs]

/-- An equivariant map out of `L(Fᵖ)` is determined by its value at the standard flag. -/
theorem equivariantHom_L_eq_zero (p : ℕ)
    (f : equivariantHom ((completeFlagBicomod F k).X.rep p) (hsigmaRep F k p p))
    (h0 : f.1 (s0L F k p) = 0) : f = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  rintro ⟨y, hy⟩
  have hspan := Finsupp.supported_eq_span_single k {G : Flag F (Fin p → F) | G.IsComplete}
  have hm : ∀ y, y ∈ Submodule.span k ((fun i => Finsupp.single i (1 : k)) ''
      {G : Flag F (Fin p → F) | G.IsComplete}) →
      y ∈ Finsupp.supported k k {G : Flag F (Fin p → F) | G.IsComplete} := fun y h => hspan ▸ h
  have hy' := hspan ▸ hy
  show f.1 ⟨y, hy⟩ = 0
  have key : ∀ y (hy1 : y ∈ Submodule.span k ((fun i => Finsupp.single i (1 : k)) ''
      {G : Flag F (Fin p → F) | G.IsComplete})), f.1 ⟨y, hm y hy1⟩ = 0 := by
    intro y hy1
    induction hy1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨G, hG, rfl⟩ := hy
      obtain ⟨g, rfl⟩ := exists_smul_stdFlag G hG
      have he := LinearMap.congr_fun (f.2 g) (s0L F k p)
      change f.1 (((completeFlagBicomod F k).X.rep p g) (s0L F k p)) =
        hsigmaRep F k p p g (f.1 (s0L F k p)) at he
      rw [h0, map_zero] at he
      have hx : ((completeFlagBicomod F k).X.rep p g) (s0L F k p) =
          ⟨Finsupp.single (g • stdFlag F p) 1, hm _ (Submodule.subset_span ⟨_, hG, rfl⟩)⟩ := by
        apply Subtype.ext
        rw [s0L, rep_single_L p g _ (stdFlag_isComplete p)]
      rw [hx] at he
      exact he
    | zero => exact map_zero f.1
    | add y z hy hz ihy ihz =>
      have : (⟨y + z, hm _ (Submodule.add_mem _ hy hz)⟩ :
          Finsupp.supported k k {G : Flag F (Fin p → F) | G.IsComplete}) =
          ⟨y, hm y hy⟩ + ⟨z, hm z hz⟩ := rfl
      rw [this, map_add, ihy, ihz, add_zero]
    | smul c y hy ih =>
      have : (⟨c • y, hm _ (Submodule.smul_mem _ c hy)⟩ :
          Finsupp.supported k k {G : Flag F (Fin p → F) | G.IsComplete}) =
          c • ⟨y, hm y hy⟩ := rfl
      rw [this, map_smul, ih, smul_zero]
  exact key y hy'

theorem eL_injective (p : ℕ) : Function.Injective (eL (F := F) (k := k) p) := by
  have hx := GLSpecies.isRelativelyProjective_of_charZero (F := F) (k := k)
    (completeFlagBicomod F k).X
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | _ a =>
    have hz' : (Theta (completeFlagBicomod F k) p p a).1 (s0L F k p) = 0 := hz
    have hT : Theta (completeFlagBicomod F k) p p a = 0 :=
      equivariantHom_L_eq_zero p _ hz'
    exact (Submodule.Quotient.mk_eq_zero _).2
      (Bpage_of_Theta_eq_zero (completeFlagBicomod F k) p p hx a hT)

theorem resAlpha_cochain (p : ℕ) :
    restrictCochain (alphaCochain (F := F) (k := k) p) ∈
      cochains (completeFlagBicomod F k) p :=
  restrictCochain_mem_cochains p (alphaCochain_mem_cochains p)

theorem resAlpha_Zpage (p : ℕ) :
    restrictCochain (alphaCochain (F := F) (k := k) p) ∈
      Zpage (completeFlagBicomod F k) 1 p p :=
  cochains_le_diagonal_Zpage _ _ (resAlpha_cochain p)

theorem PfL_resAlpha (p : ℕ) : PfL F k p (restrictCochain (alphaCochain p)) = 1 := by
  rw [PfL_restrict, Pf_alpha]

theorem finrank_E_L (p : ℕ) : finrank k (E (completeFlagBicomod F k) 1 p p) = 1 := by
  let g : E (completeFlagBicomod F k) 1 p p →ₗ[k] hsigmaFixed (F := F) (k := k) p (borel F p) :=
    LinearMap.codRestrict _ (eL p) (eL_mem_fixed p)
  have hg : Function.Injective g := by
    intro u v h
    exact eL_injective p (congrArg Subtype.val h)
  haveI : Module.Finite k (hsigmaFixed (F := F) (k := k) p (borel F p)) :=
    Module.finite_of_finrank_pos (by rw [finrank_hsigmaFixed_borel]; decide)
  haveI : Module.Finite k (E (completeFlagBicomod F k) 1 p p) := Module.Finite.of_injective g hg
  have hle := LinearMap.finrank_le_finrank_of_injective hg
  rw [finrank_hsigmaFixed_borel] at hle
  have hne : (Subquot.mk _ (resAlpha_Zpage (F := F) (k := k) p) :
      E (completeFlagBicomod F k) 1 p p) ≠ 0 := by
    intro h0
    have h1 := congrArg (eL (F := F) (k := k) p) h0
    rw [map_zero] at h1
    have h2 : eL (F := F) (k := k) p (Subquot.mk _ (resAlpha_Zpage (F := F) (k := k) p)) =
        e1StdEval (F := F) (k := k) p (Subquot.mk _ (alphaCochain_mem p)) := rfl
    rw [h2] at h1
    have h3 := e1StdEval_injective (F := F) (k := k) p (h1.trans (map_zero _).symm)
    have h4 : alphaCochain (F := F) (k := k) p ∈ Bpage (flagBicomod F k) 1 p p :=
      (Submodule.Quotient.mk_eq_zero ((Bpage (flagBicomod F k) 1 p p).comap
        (Zpage (flagBicomod F k) 1 p p).subtype)).1 h3
    have := Pf_eq_zero_of_mem_Bpage p (alphaCochain_mem_cochains p) h4
    rw [Pf_alpha] at this
    exact one_ne_zero this
  have hpos : 0 < finrank k (E (completeFlagBicomod F k) 1 p p) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, hne⟩
  omega

theorem PfL_eq_zero_iff (p : ℕ) {a : RawCochain (completeFlagBicomod F k)}
    (ha : a ∈ Zpage (completeFlagBicomod F k) 1 p p) :
    a ∈ Bpage (completeFlagBicomod F k) 1 p p ↔ PfL F k p a = 0 :=
  diagonal_detect (completeFlagBicomod F k) p (s0L F k p) _ (resAlpha_Zpage p)
    (PfL_resAlpha p) (finrank_E_L p) a ha


theorem PfL_eq_zero_of_mem_Bpage (p : ℕ) {a : RawCochain (completeFlagBicomod F k)}
    (ha : a ∈ cochains (completeFlagBicomod F k) p)
    (hB : a ∈ Bpage (completeFlagBicomod F k) 1 p p) : PfL F k p a = 0 :=
  (PfL_eq_zero_iff p (cochains_le_diagonal_Zpage _ _ ha)).1 hB

theorem sub_PfL_alpha_mem (p : ℕ) {a : RawCochain (completeFlagBicomod F k)}
    (ha : a ∈ cochains (completeFlagBicomod F k) p) :
    a - PfL F k p a • restrictCochain (alphaCochain p) ∈ Bpage (completeFlagBicomod F k) 1 p p := by
  have hz : a - PfL F k p a • restrictCochain (alphaCochain p) ∈
      Zpage (completeFlagBicomod F k) 1 p p :=
    cochains_le_diagonal_Zpage _ _
      (Submodule.sub_mem _ ha (Submodule.smul_mem _ _ (resAlpha_cochain p)))
  exact (PfL_eq_zero_iff p hz).2 (by rw [PfL_sub, PfL_smul, PfL_resAlpha, mul_one, sub_self])

/-- A diagonal cocycle with nonzero first-page class, next to another one, is not a coboundary. -/
theorem not_coboundary_of_PfL (n : ℕ) {z z' : RawCochain (completeFlagBicomod F k)}
    (hz : z ∈ cocycles (completeFlagBicomod F k) (n + 1)) (hPz : PfL F k (n + 1) z ≠ 0)
    (hz' : z' ∈ cocycles (completeFlagBicomod F k) n) (hPz' : PfL F k n z' ≠ 0) :
    z ∉ coboundaries (completeFlagBicomod F k) (n + 1) := by
  rintro ⟨β, hβc, hβ⟩
  have hdz' : d (completeFlagBicomod F k) n z' = 0 := hz'.2
  -- the class of β
  have hB1 := sub_PfL_alpha_mem n hβc
  obtain ⟨w1, hw1, hd1⟩ := d_eq_of_Bpage _ n hB1
  -- the class of α_n in terms of z'
  have hB2 := Submodule.smul_mem _ (PfL F k n z')⁻¹ (sub_PfL_alpha_mem n hz'.1)
  obtain ⟨w2, hw2, hd2⟩ := d_eq_of_Bpage _ n hB2
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hPz', one_smul, map_sub, map_smul, hdz', smul_zero,
    zero_sub] at hd2
  rw [map_sub, map_smul] at hd1
  have hzd : z = d (completeFlagBicomod F k) n w1 - PfL F k n β • d (completeFlagBicomod F k) n w2 := by
    rw [← hβ]
    have : d (completeFlagBicomod F k) n β = d (completeFlagBicomod F k) n w1 +
        PfL F k n β • d (completeFlagBicomod F k) n (restrictCochain (alphaCochain n)) := by rw [← hd1]; abel
    rw [this]
    have h3 : d (completeFlagBicomod F k) n (restrictCochain (alphaCochain n)) = -d (completeFlagBicomod F k) n w2 := by
      rw [← hd2]; simp
    rw [h3]; simp [sub_eq_add_neg]
  have hBz : z ∈ Bpage (completeFlagBicomod F k) 1 ((n + 1 : ℕ) : ℤ) (n + 1) := by
    rw [hzd]
    refine Submodule.sub_mem _ (d_mem_Bdiag n (by simpa using hw1))
      (Submodule.smul_mem _ _ (d_mem_Bdiag n (by simpa using hw2)))
  exact hPz (PfL_eq_zero_of_mem_Bpage (n + 1) hz.1 hBz)


theorem exists_good (n : ℕ) : ∃ z, z ∈ cocycles (flagBicomod F k) n ∧ Pf F k n z ≠ 0 ∧
    z ∉ coboundaries (flagBicomod F k) n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact ⟨schPow m, schPow_mem_cocycles m, Pf_schPow_ne_zero m, schPow_not_coboundary m⟩
  · rw [show 2 * m + 1 = 1 + 2 * m by omega]
    exact ⟨_, dim_schPow_cocycle m, Pf_dim_schPow_ne_zero m, dim_schPow_not_coboundary m⟩

/-- **Theorem 1.36.** The inclusion `L → Σ` induces an isomorphism of cohomology
algebras `H•(L) ≅ H•(Σ)`. Analogue of [Tam17, Thm. III.6.10]. -/
theorem thm_1_36 [CharZero k] (n : ℕ) :
    Function.Bijective (Subquot.map restrictCochain (restrictCochain_cocycles n)
      (restrictCochain_coboundaries n) :
        H (flagBicomod F k) n →ₗ[k] H (completeFlagBicomod F k) n) :=
  by
  have hxS := GLSpecies.isRelativelyProjective_of_charZero (F := F) (k := k) (flagBicomod F k).X
  have hxL := GLSpecies.isRelativelyProjective_of_charZero (F := F) (k := k)
    (completeFlagBicomod F k).X
  obtain ⟨z, hz, hPz, hnc⟩ := exists_good (F := F) (k := k) n
  have hfin := H_line n hz hPz hnc
  have hne : cohClass (flagBicomod F k) z hz ≠ 0 := (cohClass_ne_zero_iff z hz).2 hnc
  have hw : restrictCochain z ∈ cocycles (completeFlagBicomod F k) n :=
    restrictCochain_cocycles n hz
  have hPw : PfL F k n (restrictCochain z) ≠ 0 := by rw [PfL_restrict]; exact hPz
  have hwnc : restrictCochain z ∉ coboundaries (completeFlagBicomod F k) n := by
    cases n with
    | zero =>
      intro h0
      have : restrictCochain z = 0 := h0
      apply hPw; rw [this]
      have := PfL_smul (F := F) (k := k) 0 0 (restrictCochain z)
      simpa using (by rw [← this, zero_smul] : PfL F k 0 0 = 0 * PfL F k 0 (restrictCochain z))
    | succ m =>
      obtain ⟨z', hz', hPz', -⟩ := exists_good (F := F) (k := k) m
      exact not_coboundary_of_PfL m (restrictCochain_cocycles _ hz)
        (by rw [PfL_restrict]; exact hPz) (restrictCochain_cocycles _ hz')
        (by rw [PfL_restrict]; exact hPz')
  have hmap : Subquot.map restrictCochain (restrictCochain_cocycles n)
      (restrictCochain_coboundaries n) (cohClass (flagBicomod F k) z hz) =
      cohClass (completeFlagBicomod F k) (restrictCochain z) hw := rfl
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hfin x
    rw [LinearMap.mem_ker, map_smul, hmap] at hx
    have hne' : cohClass (completeFlagBicomod F k) (restrictCochain z) hw ≠ 0 :=
      (cohClass_ne_zero_iff _ hw).2 hwnc
    rcases smul_eq_zero.1 hx with h | h
    · rw [h, zero_smul]
    · exact absurd h hne'
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      obtain ⟨c, hc⟩ := c
      refine ⟨(PfL F k n c / PfL F k n (restrictCochain z)) • cohClass (flagBicomod F k) z hz, ?_⟩
      rw [map_smul, hmap]
      have hB : c - (PfL F k n c / PfL F k n (restrictCochain z)) • restrictCochain z ∈
          Bpage (completeFlagBicomod F k) 1 (n : ℤ) n := by
        have hZ : c - (PfL F k n c / PfL F k n (restrictCochain z)) • restrictCochain z ∈
            Zpage (completeFlagBicomod F k) 1 (n : ℤ) n :=
          cochains_le_diagonal_Zpage _ _
            (Submodule.sub_mem _ hc.1 (Submodule.smul_mem _ _ hw.1))
        refine (PfL_eq_zero_iff n hZ).2 ?_
        rw [PfL_sub, PfL_smul, div_mul_cancel₀ _ hPw, sub_self]
      have hcc : c - (PfL F k n c / PfL F k n (restrictCochain z)) • restrictCochain z ∈
          cocycles (completeFlagBicomod F k) n :=
        Submodule.sub_mem _ hc (Submodule.smul_mem _ _ hw)
      have hcb := coboundary_of_Bpage _ hxL n hcc hB
      change (_ : H (completeFlagBicomod F k) n) = Submodule.Quotient.mk ⟨c, hc⟩
      change (PfL F k n c / PfL F k n (restrictCochain z)) •
        (Submodule.Quotient.mk ⟨restrictCochain z, hw⟩ : H (completeFlagBicomod F k) n) = _
      rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
      exact hcb

end MartinPhd

end
end Thm136
