import TamaroffPhd.Chapter3MinimalModels

/-!
# Chapter 6, §6.4: Bergman's Diamond Lemma and the Triangle Lemma

Proposition 4.1 (Bergman's Diamond Lemma) and Proposition 4.2 (Triangle Lemma): a terminating
rewriting system is convergent iff its ambiguities are resolvable.

## Contents

* `inclusionObstruction`, `overlapObstruction`, `ReducesToZero`: the ambiguities of a rewriting
  system and their obstructions (§6.4.1).
* `diamondLemma`: Proposition 4.1, proved (Bergman's argument, [21, Th. 1.2]).
* `triangleLemma`: Proposition 4.2 (statement only).

## Proof of Proposition 4.1

Helpers (not in the source, no label) serve this proof only.

* *The reduction formula.* A basic reduction acts by `ρ g = g + g_{awb} · a (f(w) - w) b`.
* *Termination.* If `<_Σ` is well-founded, every `g` has an irreducible descendant, and `Σ` is
  terminating. The strict reduction steps are well-founded by a lexicographic argument.
* *Determined elements.* `Det g v` says that every irreducible descendant of `g` is `v`. It is
  preserved by linear combinations and by reductions.
* *Bergman's induction.* Every monomial is determined, by induction on `<_Σ`: two reductions at
  the same monomial are two *decompositions* of it, which are disjoint, overlap or are nested,
  and the ambiguity hypotheses resolve each case (`det_two_decomps`).
* *Conclusion.* Every element is determined, so the final value is a linear map that factors
  through `A_Σ` (`RingQuot` induction).

The thesis takes Σ terminating and uses (§2.1, citing [21, 40]) that this is equivalent to
well-foundedness of `<_Σ`. The proof uses the ordering form, so `diamondLemma` assumes that `<_Σ`
is well-founded (see the **Change** on `diamondLemma`). That implies termination
(`isTerminating_of_wellFounded`, proved below).
-/

noncomputable section

namespace TamaroffPhd

open Classical MonomialData


variable {k : Type} [Field k] {X : Type}

/-- An *inclusion ambiguity* `(u, u', a, b)`: relations `u, u' ∈ W` with `u = a u' b`, `u' ≠ u`.
Its obstruction is `f(u) - a f(u') b`. -/
def inclusionObstruction (S : RewritingSystem k X) (u u' a b : FreeMonoid X) : FreeAlg k X :=
  S.f u - mono a * S.f u' * mono b

/-- An *overlap ambiguity* `(u', u'', a, b)`: relations with `u' a = b u''`, `a, b` non-empty and
`u', u''` sharing a non-trivial common divisor. Its obstruction is the S-polynomial
`b f(u'') - f(u') a`. -/
def overlapObstruction (S : RewritingSystem k X) (u' u'' a b : FreeMonoid X) : FreeAlg k X :=
  mono b * S.f u'' - S.f u' * mono a

/-- `ρs` sends `g` to zero, for some reduction `ρs`. -/
def ReducesToZero (S : RewritingSystem k X) (g : FreeAlg k X) : Prop :=
  ∃ ρs, S.IsReductionList ρs ∧ RewritingSystem.reduction ρs g = 0

/-! ## Word combinatorics -/

lemma list_split {A B C D : List X} (h : A ++ B = C ++ D) (hl : A.length ≤ C.length) :
    ∃ t, C = A ++ t ∧ B = t ++ D := by
  rcases List.append_eq_append_iff.1 h with ⟨t, h1, h2⟩ | ⟨c', h1, h2⟩
  · exact ⟨t, h1, h2⟩
  · have hlen : c'.length = 0 := by
      have := congrArg List.length h1
      simp at this; omega
    have hc : c' = [] := List.length_eq_zero_iff.1 hlen
    subst hc
    simp at h1 h2
    exact ⟨[], by simp [h1], by simp [h2]⟩

/-- Two occurrences of words in the same word: identical, disjoint, overlapping or nested. -/
lemma decomp_cases_list {A₁ W₁ B₁ A₂ W₂ B₂ : List X} (h : A₁ ++ W₁ ++ B₁ = A₂ ++ W₂ ++ B₂)
    (hl : A₁.length ≤ A₂.length) :
    (A₁ = A₂ ∧ W₁ = W₂ ∧ B₁ = B₂) ∨
    (∃ t, A₂ = A₁ ++ W₁ ++ t ∧ B₁ = t ++ W₂ ++ B₂) ∨
    (∃ t s c, t ≠ [] ∧ s ≠ [] ∧ c ≠ [] ∧ A₂ = A₁ ++ t ∧ W₁ = t ++ s ∧ W₂ = s ++ c ∧
      B₁ = c ++ B₂) ∨
    (∃ t d, (t ≠ [] ∨ d ≠ []) ∧ A₂ = A₁ ++ t ∧ W₁ = t ++ W₂ ++ d ∧ B₂ = d ++ B₁) ∨
    (∃ c, c ≠ [] ∧ A₂ = A₁ ∧ W₂ = W₁ ++ c ∧ B₁ = c ++ B₂) := by
  have h' : A₁ ++ (W₁ ++ B₁) = A₂ ++ (W₂ ++ B₂) := by simpa [List.append_assoc] using h
  obtain ⟨t, hA, hWB⟩ := list_split h' hl
  rcases le_or_gt W₁.length t.length with h1 | h1
  · obtain ⟨t', ht, hB⟩ := list_split hWB h1
    right; left
    exact ⟨t', by simp [hA, ht], by simp [hB]⟩
  · obtain ⟨s, hW, hWB2⟩ := list_split hWB.symm h1.le
    have hs : s ≠ [] := by
      rintro rfl
      simp at hW
      subst hW
      omega
    rcases lt_trichotomy s.length W₂.length with h2 | h2 | h2
    · obtain ⟨c, hW2, hB⟩ := list_split hWB2.symm h2.le
      have hc : c ≠ [] := by
        rintro rfl
        simp at hW2
        subst hW2
        omega
      by_cases ht : t = []
      · subst ht
        right; right; right; right
        exact ⟨c, hc, by simp [hA], by simp [hW2, hW], hB⟩
      · right; right; left
        exact ⟨t, s, c, ht, hs, hc, hA, hW, hW2, hB⟩
    · obtain ⟨hsW, hB⟩ := List.append_inj hWB2.symm h2
      by_cases ht : t = []
      · subst ht
        left
        exact ⟨by simp [hA], by simp [hW, hsW], hB⟩
      · right; right; right; left
        exact ⟨t, [], Or.inl ht, hA, by simp [hW, hsW], by simp [hB]⟩
    · obtain ⟨d, hsd, hB2⟩ := list_split hWB2 h2.le
      have hd : d ≠ [] := by
        rintro rfl
        simp at hsd
        subst hsd
        omega
      right; right; right; left
      exact ⟨t, d, Or.inr hd, hA, by simp [hW, hsd], hB2⟩

lemma freeMonoid_ne_one {t : List X} (ht : t ≠ []) : (FreeMonoid.ofList t) ≠ 1 := by
  intro h
  exact ht (by simpa using congrArg FreeMonoid.toList h)

lemma toList_ne_nil {t : FreeMonoid X} (ht : t ≠ 1) : t.toList ≠ [] := by
  intro h
  exact ht (FreeMonoid.ext (by simpa using h))

/-- Two occurrences of words in the same monomial, in `⟨X⟩`. -/
lemma decomp_cases {a₁ w₁ b₁ a₂ w₂ b₂ : FreeMonoid X} (h : a₁ * w₁ * b₁ = a₂ * w₂ * b₂)
    (hl : a₁.toList.length ≤ a₂.toList.length) :
    (a₁ = a₂ ∧ w₁ = w₂ ∧ b₁ = b₂) ∨
    (∃ t, a₂ = a₁ * w₁ * t ∧ b₁ = t * w₂ * b₂) ∨
    (∃ t s c, t ≠ 1 ∧ s ≠ 1 ∧ c ≠ 1 ∧ a₂ = a₁ * t ∧ w₁ = t * s ∧ w₂ = s * c ∧ b₁ = c * b₂) ∨
    (∃ t d, (t ≠ 1 ∨ d ≠ 1) ∧ a₂ = a₁ * t ∧ w₁ = t * w₂ * d ∧ b₂ = d * b₁) ∨
    (∃ c, c ≠ 1 ∧ a₂ = a₁ ∧ w₂ = w₁ * c ∧ b₁ = c * b₂) := by
  have h' := congrArg FreeMonoid.toList h
  simp only [FreeMonoid.toList_mul] at h'
  have inj : ∀ {x y : FreeMonoid X}, x.toList = y.toList → x = y :=
    fun e => FreeMonoid.ext e
  have one' : ∀ {t : List X}, (t ≠ []) → FreeMonoid.ofList t ≠ 1 := freeMonoid_ne_one
  rcases decomp_cases_list h' hl with ⟨h1, h2, h3⟩ | ⟨t, h1, h2⟩ |
    ⟨t, s, c, ht, hs, hc, h1, h2, h3, h4⟩ | ⟨t, d, htd, h1, h2, h3⟩ | ⟨c, hc, h1, h2, h3⟩
  · exact Or.inl ⟨inj h1, inj h2, inj h3⟩
  · refine Or.inr (Or.inl ⟨FreeMonoid.ofList t, inj ?_, inj ?_⟩) <;> simp [h1, h2]
  · refine Or.inr (Or.inr (Or.inl ⟨FreeMonoid.ofList t, FreeMonoid.ofList s, FreeMonoid.ofList c,
      one' ht, one' hs, one' hc, inj ?_, inj ?_, inj ?_, inj ?_⟩)) <;> simp [h1, h2, h3, h4]
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨FreeMonoid.ofList t, FreeMonoid.ofList d, ?_,
      inj ?_, inj ?_, inj ?_⟩)))
    · rcases htd with h | h
      · exact Or.inl (one' h)
      · exact Or.inr (one' h)
    all_goals simp [h1, h2, h3]
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨FreeMonoid.ofList c, one' hc, inj ?_, inj ?_,
      inj ?_⟩))) <;> simp [h1, h2, h3]

lemma ne_mul_of_ne_one {t w d : FreeMonoid X} (h : t ≠ 1 ∨ d ≠ 1) : w ≠ t * w * d := by
  intro e
  have := congrArg (fun x : FreeMonoid X => x.toList.length) e
  simp only [FreeMonoid.toList_mul, List.length_append] at this
  rcases h with h | h
  · exact toList_ne_nil h (List.length_eq_zero_iff.1 (by omega))
  · exact toList_ne_nil h (List.length_eq_zero_iff.1 (by omega))

lemma ne_mul_right_of_ne_one {w c : FreeMonoid X} (h : c ≠ 1) : w ≠ w * c := by
  intro e
  have := congrArg (fun x : FreeMonoid X => x.toList.length) e
  simp only [FreeMonoid.toList_mul, List.length_append] at this
  exact toList_ne_nil h (List.length_eq_zero_iff.1 (by omega))

namespace RewritingSystem

variable (S : RewritingSystem k X)

/-! ## The algebra of monomials -/

lemma mono_mul (a b : FreeMonoid X) : (mono (a * b) : FreeAlg k X) = mono a * mono b := by
  simp [mono, MonoidAlgebra.single_mul_single]

lemma mono_one : (mono 1 : FreeAlg k X) = 1 := by
  simp [mono, MonoidAlgebra.one_def]

lemma coeff_mono (m n : FreeMonoid X) :
    (mono m : FreeAlg k X).coeff n = if m = n then 1 else 0 := by
  simp [mono, Finsupp.single_apply]

lemma linOnMonomials_mono {M : Type} [AddCommGroup M] [Module k M] (v : FreeMonoid X → M)
    (n : FreeMonoid X) : linOnMonomials v (mono n : FreeAlg k X) = v n := by
  change Finsupp.linearCombination k v (Finsupp.single n (1 : k)) = v n
  simp

/-- The coefficient of `p x q` at `p m q` is that of `x` at `m`. -/
lemma coeff_ctx (p q m : FreeMonoid X) (x : FreeAlg k X) :
    (mono p * x * mono q).coeff (p * m * q) = x.coeff m := by
  induction x using MonoidAlgebra.induction_on with
  | of n =>
    simp only [MonoidAlgebra.of_apply, ← mono_mul, coeff_mono, mul_left_inj, mul_right_inj]
  | add x y hx hy => simp [mul_add, add_mul, MonoidAlgebra.coeff_add, hx, hy]
  | smul c x hx => simp [hx]

/-- The coefficient of `p x q` vanishes away from the words `p u q`. -/
lemma coeff_ctx_ne (p q d : FreeMonoid X) (hd : ∀ u, d ≠ p * u * q) (x : FreeAlg k X) :
    (mono p * x * mono q).coeff d = 0 := by
  induction x using MonoidAlgebra.induction_on with
  | of n =>
    simp only [MonoidAlgebra.of_apply, ← mono_mul, coeff_mono]
    exact ite_eq_right_iff.2 fun h => absurd h.symm (hd n)
  | add x y hx hy => simp [mul_add, add_mul, MonoidAlgebra.coeff_add, hx, hy]
  | smul c x hx => simp [hx]

/-- `x` is the sum of its monomials. -/
lemma eq_sum_mono (x : FreeAlg k X) : x = ∑ u ∈ supp x, x.coeff u • mono u := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp [mono, MonoidAlgebra.smul_single]

/-! ## Basic reductions -/

/-- The defect `a (f(w) - w) b` of a basic reduction. -/
def defect (a w b : FreeMonoid X) : FreeAlg k X := mono a * S.f w * mono b - mono (a * w * b)

/-- **The reduction formula.** `ρ g = g + g_{awb} · a (f(w) - w) b`. -/
lemma basicReduction_apply (a w b : FreeMonoid X) (g : FreeAlg k X) :
    S.basicReduction a w b g = g + g.coeff (a * w * b) • S.defect a w b := by
  induction g using MonoidAlgebra.induction_on with
  | of n =>
    simp only [MonoidAlgebra.of_apply, basicReduction, linOnMonomials_mono, coeff_mono, defect]
    split_ifs with h
    · subst h; simp
    · simp
  | add x y hx hy => simp [map_add, hx, hy, MonoidAlgebra.coeff_add, add_smul]; abel
  | smul c x hx => simp [map_smul, hx, smul_add, smul_smul]

lemma basicReduction_mono_of_ne {a w b m : FreeMonoid X} (h : m ≠ a * w * b) :
    S.basicReduction a w b (mono m) = mono m := by
  simp [basicReduction_apply, h]

lemma basicReduction_mono_self (a w b : FreeMonoid X) :
    S.basicReduction a w b (mono (a * w * b)) = mono a * S.f w * mono b := by
  simp [basicReduction_apply, defect]

/-- Basic reductions in a context: `ρ_{pawbq}(p x q) = p ρ_{awb}(x) q`. -/
lemma basicReduction_ctx (p q a w b : FreeMonoid X) (x : FreeAlg k X) :
    S.basicReduction (p * a) w (b * q) (mono p * x * mono q) =
      mono p * S.basicReduction a w b x * mono q := by
  have e : p * a * w * (b * q) = p * (a * w * b) * q := by simp [mul_assoc]
  rw [basicReduction_apply, basicReduction_apply, e, coeff_ctx]
  have d : S.defect (p * a) w (b * q) = mono p * S.defect a w b * mono q := by
    simp only [defect, mul_sub, sub_mul, mono_mul, mul_assoc]
  rw [d]
  simp [mul_add, add_mul]

/-- `toAlg` kills the defect of a rule. -/
lemma toAlg_defect {a w b : FreeMonoid X} (hw : w ∈ S.W) : S.toAlg (S.defect a w b) = 0 := by
  have h : S.toAlg (mono w) = S.toAlg (S.f w) :=
    RingQuot.mkAlgHom_rel k (show S.rel (mono w) (S.f w) from ⟨w, hw, rfl, rfl⟩)
  simp only [defect, mono_mul, map_sub, map_mul, ← h, sub_self]


/-! ## Reduction lists and descendants -/

lemma reduction_nil : reduction ([] : List (FreeAlg k X →ₗ[k] FreeAlg k X)) = LinearMap.id := rfl

lemma foldl_reduction (acc : FreeAlg k X →ₗ[k] FreeAlg k X)
    (ρs : List (FreeAlg k X →ₗ[k] FreeAlg k X)) :
    ρs.foldl (fun acc ρ => ρ ∘ₗ acc) acc = reduction ρs ∘ₗ acc := by
  induction ρs generalizing acc with
  | nil => rfl
  | cons ρ ρs ih =>
    simp only [List.foldl_cons, reduction] at ih ⊢
    rw [ih, ih (ρ ∘ₗ LinearMap.id)]
    rfl

lemma reduction_cons (ρ : FreeAlg k X →ₗ[k] FreeAlg k X)
    (ρs : List (FreeAlg k X →ₗ[k] FreeAlg k X)) (g : FreeAlg k X) :
    reduction (ρ :: ρs) g = reduction ρs (ρ g) := by
  simp only [reduction, List.foldl_cons]
  rw [foldl_reduction]
  rfl

lemma reduction_append (ρs σs : List (FreeAlg k X →ₗ[k] FreeAlg k X)) (g : FreeAlg k X) :
    reduction (ρs ++ σs) g = reduction σs (reduction ρs g) := by
  induction ρs generalizing g with
  | nil => rfl
  | cons ρ ρs ih => simp [reduction_cons, ih]

/-- `g` reduces to `h`: some reduction sends `g` to `h`. -/
def Reds (g h : FreeAlg k X) : Prop :=
  ∃ ρs, S.IsReductionList ρs ∧ reduction ρs g = h

variable {S}

lemma reds_refl (g : FreeAlg k X) : S.Reds g g := ⟨[], by simp [IsReductionList], rfl⟩

lemma reds_trans {g h i : FreeAlg k X} (h₁ : S.Reds g h) (h₂ : S.Reds h i) : S.Reds g i := by
  obtain ⟨ρs, hρ, rfl⟩ := h₁
  obtain ⟨σs, hσ, rfl⟩ := h₂
  refine ⟨ρs ++ σs, fun ρ hρ' => ?_, reduction_append ρs σs g⟩
  rcases List.mem_append.1 hρ' with h | h
  · exact hρ ρ h
  · exact hσ ρ h

lemma reds_basic {ρ : FreeAlg k X →ₗ[k] FreeAlg k X} (hρ : ρ ∈ S.basicReductions)
    (g : FreeAlg k X) : S.Reds g (ρ g) :=
  ⟨[ρ], by simpa [IsReductionList] using hρ, by simp [reduction_cons, reduction_nil]⟩

lemma reduction_irreducible {ρs : List (FreeAlg k X →ₗ[k] FreeAlg k X)} (hρs : S.IsReductionList ρs)
    {g : FreeAlg k X} (hg : S.IsIrreducible g) : reduction ρs g = g := by
  induction ρs with
  | nil => rfl
  | cons ρ ρs ih =>
    rw [reduction_cons, hg ρ (hρs ρ (by simp))]
    exact ih fun σ hσ => hρs σ (by simp [hσ])

lemma reds_of_irreducible {g h : FreeAlg k X} (hg : S.IsIrreducible g) (hr : S.Reds g h) :
    h = g := by
  obtain ⟨ρs, hρ, rfl⟩ := hr
  exact reduction_irreducible hρ hg

lemma reds_ctx {g h : FreeAlg k X} (p q : FreeMonoid X) (hr : S.Reds g h) :
    S.Reds (mono p * g * mono q) (mono p * h * mono q) := by
  obtain ⟨ρs, hρ, rfl⟩ := hr
  induction ρs generalizing g with
  | nil => exact reds_refl _
  | cons ρ ρs ih =>
    obtain ⟨a, w, b, hw, rfl⟩ := hρ ρ (by simp)
    rw [reduction_cons]
    have h1 : S.Reds (mono p * g * mono q) (mono p * S.basicReduction a w b g * mono q) := by
      rw [← basicReduction_ctx]
      exact reds_basic ⟨p * a, w, b * q, hw, rfl⟩ _
    exact reds_trans h1 (ih (fun σ hσ => hρ σ (by simp [hσ])))

/-- The first non-trivial step of a reduction. -/
lemma reds_first {g h : FreeAlg k X} (hr : S.Reds g h) (hne : h ≠ g) :
    ∃ ρ ∈ S.basicReductions, ρ g ≠ g ∧ S.Reds (ρ g) h := by
  obtain ⟨ρs, hρ, rfl⟩ := hr
  induction ρs generalizing g with
  | nil => exact absurd rfl hne
  | cons ρ ρs ih =>
    have hρ' : ρ ∈ S.basicReductions := hρ ρ (by simp)
    have hrest : S.IsReductionList ρs := fun σ hσ => hρ σ (by simp [hσ])
    by_cases hfix : ρ g = g
    · rw [reduction_cons, hfix] at hne ⊢
      exact ih hrest hne
    · exact ⟨ρ, hρ', hfix, ⟨ρs, hrest, by rw [reduction_cons]⟩⟩

lemma toAlg_reduction {ρs : List (FreeAlg k X →ₗ[k] FreeAlg k X)} (hρs : S.IsReductionList ρs)
    (g : FreeAlg k X) : S.toAlg (reduction ρs g) = S.toAlg g := by
  induction ρs generalizing g with
  | nil => rfl
  | cons ρ ρs ih =>
    obtain ⟨a, w, b, hw, rfl⟩ := hρs ρ (by simp)
    rw [reduction_cons, ih (fun σ hσ => hρs σ (by simp [hσ])), basicReduction_apply]
    simp [map_add, map_smul, S.toAlg_defect hw]

lemma toAlg_reds {g h : FreeAlg k X} (hr : S.Reds g h) : S.toAlg h = S.toAlg g := by
  obtain ⟨ρs, hρ, rfl⟩ := hr
  exact toAlg_reduction hρ g

/-! ## Determined elements -/

/-- Every irreducible descendant of `g` equals `v`. -/
def Det (g v : FreeAlg k X) : Prop :=
  ∀ h, S.Reds g h → S.IsIrreducible h → h = v

lemma det_irr {h : FreeAlg k X} (hh : S.IsIrreducible h) : S.Det h h :=
  fun _ hr _ => reds_of_irreducible hh hr

lemma det_of_reds {g g' v : FreeAlg k X} (hd : S.Det g v) (hr : S.Reds g g') : S.Det g' v :=
  fun h hh hirr => hd h (reds_trans hr hh) hirr

lemma det_zero : S.Det (0 : FreeAlg k X) 0 :=
  det_irr fun ρ _ => map_zero ρ

section Det

variable (hF : ∀ g : FreeAlg k X, ∃ h, S.Reds g h ∧ S.IsIrreducible h)
include hF

lemma det_unique {g v v' : FreeAlg k X} (hd : S.Det g v) (hd' : S.Det g v') : v = v' := by
  obtain ⟨h, hr, hirr⟩ := hF g
  rw [← hd h hr hirr, ← hd' h hr hirr]

lemma det_final {g v : FreeAlg k X} (hd : S.Det g v) : S.Reds g v ∧ S.IsIrreducible v := by
  obtain ⟨h, hr, hirr⟩ := hF g
  rw [← hd h hr hirr]; exact ⟨hr, hirr⟩

lemma det_add {g g' v v' : FreeAlg k X} (hd : S.Det g v) (hd' : S.Det g' v') :
    S.Det (g + g') (v + v') := by
  intro h hr hirr
  obtain ⟨ρs, hρ, rfl⟩ := hr
  obtain ⟨h₁, ⟨σ₁, hσ₁, e₁⟩, hirr₁⟩ := hF (reduction ρs g)
  obtain ⟨h₂, ⟨σ₂, hσ₂, e₂⟩, hirr₂⟩ := hF (reduction σ₁ (reduction ρs g'))
  have hv : h₁ = v := hd h₁ (reds_trans ⟨ρs, hρ, rfl⟩ ⟨σ₁, hσ₁, e₁⟩) hirr₁
  have hv' : h₂ = v' := hd' h₂ (reds_trans ⟨ρs, hρ, rfl⟩ (reds_trans ⟨σ₁, hσ₁, rfl⟩
    ⟨σ₂, hσ₂, e₂⟩)) hirr₂
  have key : reduction σ₂ (reduction σ₁ (reduction ρs (g + g'))) = reduction ρs (g + g') := by
    rw [reduction_irreducible hσ₁ hirr, reduction_irreducible hσ₂ hirr]
  rw [← key, map_add, map_add, map_add, e₁, ← hv, ← hv', ← e₂,
    reduction_irreducible hσ₂ hirr₁]

lemma det_smul (c : k) {g v : FreeAlg k X} (hd : S.Det g v) : S.Det (c • g) (c • v) := by
  intro h hr hirr
  obtain ⟨ρs, hρ, rfl⟩ := hr
  obtain ⟨h₁, ⟨σ, hσ, e⟩, hirr₁⟩ := hF (reduction ρs g)
  have hv : h₁ = v := hd h₁ (reds_trans ⟨ρs, hρ, rfl⟩ ⟨σ, hσ, e⟩) hirr₁
  have key : reduction σ (reduction ρs (c • g)) = reduction ρs (c • g) :=
    reduction_irreducible hσ hirr
  rw [← key, map_smul, map_smul, e, hv]

lemma det_sum {ι : Type} (s : Finset ι) (c : ι → k) (g v : ι → FreeAlg k X)
    (h : ∀ i ∈ s, S.Det (g i) (v i)) :
    S.Det (∑ i ∈ s, c i • g i) (∑ i ∈ s, c i • v i) := by
  induction s using Finset.induction_on with
  | empty => simpa using det_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact det_add hF (det_smul hF _ (h i (by simp))) (ih fun j hj => h j (by simp [hj]))

/-- Linear combinations of determined elements are determined, along two linear maps at once. -/
lemma det_linear₂ (L₁ L₂ : FreeAlg k X →ₗ[k] FreeAlg k X) (x : FreeAlg k X)
    (h : ∀ u ∈ supp x, ∃ v, S.Det (L₁ (mono u)) v ∧ S.Det (L₂ (mono u)) v) :
    ∃ v, S.Det (L₁ x) v ∧ S.Det (L₂ x) v := by
  choose! v hv using h
  refine ⟨∑ u ∈ supp x, x.coeff u • v u, ?_, ?_⟩
  · conv_lhs => rw [eq_sum_mono x]
    simp only [map_sum, map_smul]
    exact det_sum hF _ _ _ _ fun u hu => (hv u hu).1
  · conv_lhs => rw [eq_sum_mono x]
    simp only [map_sum, map_smul]
    exact det_sum hF _ _ _ _ fun u hu => (hv u hu).2

/-- If `x - y` reduces to `0` and `x`, `y` are determined, their values agree. -/
lemma det_eq_of_reds_zero {x y vx vy : FreeAlg k X} (hx : S.Det x vx) (hy : S.Det y vy)
    (h : S.Reds (x - y) 0) : vx = vy := by
  have hd : S.Det (x - y) (vx - vy) := by
    simpa [sub_eq_add_neg] using det_add hF hx (by simpa using det_smul hF (-1) hy)
  have := hd 0 h (fun ρ _ => map_zero ρ)
  exact sub_eq_zero.1 this.symm

end Det

/-! ## Termination from well-foundedness of `<_Σ` -/

/-- A strict reduction step `g ⟶ h`: some basic reduction sends `g` to `h ≠ g`. -/
def StrictStep (h g : FreeAlg k X) : Prop := (∃ ρ ∈ S.basicReductions, ρ g = h) ∧ h ≠ g

lemma reduction_range_succ (ρ : ℕ → FreeAlg k X →ₗ[k] FreeAlg k X) (n : ℕ) (g : FreeAlg k X) :
    reduction ((List.range (n + 2)).map ρ) g =
      ρ (n + 1) (reduction ((List.range (n + 1)).map ρ) g) := by
  rw [List.range_succ (n := n + 1), List.map_append, reduction_append]
  simp [reduction_cons, reduction_nil]

section WF

variable (hwf : WellFounded S.stepLT)
include hwf

/-- `<_Σ` is irreflexive: `w ∉ supp f(w)`. -/
lemma not_mem_supp_f {w : FreeMonoid X} (hw : w ∈ S.W) : w ∉ supp (S.f w) := by
  intro h
  obtain ⟨a, ha, hmin⟩ := hwf.has_min {w} ⟨w, rfl⟩
  have : a = w := ha
  subst this
  exact hmin a rfl ⟨1, 1, a, a, hw, h, by simp, by simp⟩

/-- A strict reduction step makes the coefficient vector lexicographically smaller, comparing
monomials from the largest in a well-order extending `<_Σ`. -/
lemma wf_strictStep : WellFounded (StrictStep (S := S)) := by
  have : WellFounded S.stepLT := hwf
  obtain ⟨s, hs, hwo⟩ := WellFounded.exists_well_order_ge S.stepLT
  let r' : FreeMonoid X → FreeMonoid X → Prop := fun d j => s j d
  let s' : k → k → Prop := fun a b => a = 0 ∧ b ≠ 0
  have hs'wf : WellFounded s' := by
    have h0 : Acc s' 0 := ⟨0, fun y hy => absurd hy.2 (by simp)⟩
    exact ⟨fun a => ⟨a, fun y hy => by rw [hy.1]; exact h0⟩⟩
  have hr' : WellFounded (r'ᶜ ⊓ (· ≠ ·)) := by
    refine Subrelation.wf (fun {a b} hab => ?_) hwo.wf
    rcases trichotomous_of s a b with h | h | h
    · exact h
    · exact absurd h hab.2
    · exact absurd h hab.1
  have hlex := Finsupp.Lex.wellFounded (r := r') (s := s') (fun n hn => hn.2 rfl) hs'wf hr'
  refine Subrelation.wf ?_ (InvImage.wf (fun g : FreeAlg k X => g.coeff) hlex)
  rintro h g ⟨⟨ρ, hρ, rfl⟩, hne⟩
  obtain ⟨a, w, b, hw, rfl⟩ := hρ
  show Finsupp.Lex r' s' (S.basicReduction a w b g).coeff g.coeff
  have hcoef : ∀ d, (S.basicReduction a w b g).coeff d =
      g.coeff d + g.coeff (a * w * b) * (S.defect a w b).coeff d := by
    intro d
    rw [basicReduction_apply]
    simp [MonoidAlgebra.coeff_add]
  have hdef : ∀ d, (S.defect a w b).coeff d =
      (mono a * S.f w * mono b).coeff d - (mono (a * w * b) : FreeAlg k X).coeff d := by
    intro d; simp [defect, MonoidAlgebra.coeff_sub]
  have hself : (mono a * S.f w * mono b).coeff (a * w * b) = 0 := by
    rw [coeff_ctx]
    simpa [supp] using not_mem_supp_f hwf hw
  have hc : g.coeff (a * w * b) ≠ 0 := by
    intro hc0
    apply hne
    rw [basicReduction_apply]
    simp [hc0]
  rw [Finsupp.lex_def]
  refine ⟨a * w * b, fun d hd => ?_, ?_⟩
  · -- larger monomials are untouched
    have hdj : (mono (a * w * b) : FreeAlg k X).coeff d = 0 := by
      rw [coeff_mono]
      exact ite_eq_right_iff.2 fun h => absurd (h ▸ hd) (irrefl_of s _)
    have hfd : (mono a * S.f w * mono b).coeff d = 0 := by
      by_contra hne0
      by_cases hex : ∃ u, d = a * u * b
      · obtain ⟨u, rfl⟩ := hex
        rw [coeff_ctx] at hne0
        have hu : u ∈ supp (S.f w) := by simpa [supp] using hne0
        exact asymm_of s hd (hs _ _ ⟨a, b, w, u, hw, hu, rfl, rfl⟩)
      · 
        exact hne0 (coeff_ctx_ne a b d (fun u hu => hex ⟨u, hu⟩) _)
    rw [hcoef, hdef, hdj, hfd]
    simp
  · -- at `awb` the coefficient is killed
    refine ⟨?_, hc⟩
    rw [hcoef, hdef, hself, coeff_mono]
    simp

/-- **Existence of irreducible descendants.** -/
lemma exists_irreducible (g : FreeAlg k X) : ∃ h, S.Reds g h ∧ S.IsIrreducible h := by
  induction g using (wf_strictStep hwf).induction with
  | _ g ih =>
    by_cases hirr : S.IsIrreducible g
    · exact ⟨g, reds_refl g, hirr⟩
    · simp only [IsIrreducible, not_forall] at hirr
      obtain ⟨ρ, hρ, hne⟩ := hirr
      obtain ⟨h, hr, hh⟩ := ih (ρ g) ⟨⟨ρ, hρ, rfl⟩, hne⟩
      exact ⟨h, reds_trans (reds_basic hρ g) hr, hh⟩

/-- **Termination.** If `<_Σ` is well-founded, `Σ` is terminating (Definition 4); this is the
easy half of the equivalence of §2.1 cited from [21, 40]. -/
theorem isTerminating_of_wellFounded : S.IsTerminating := by
  intro g ρ hρ
  let t : ℕ → FreeAlg k X := fun n => reduction ((List.range (n + 1)).map ρ) g
  have step : ∀ n, t (n + 1) = ρ (n + 1) (t n) := fun n => reduction_range_succ ρ n g
  obtain ⟨_, ⟨N, rfl⟩, hmin⟩ := (wf_strictStep hwf).has_min (Set.range t) ⟨t 0, 0, rfl⟩
  refine ⟨N, fun n hn => ?_⟩
  show t n = t N
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    by_contra hne
    exact hmin (t (n + 1)) ⟨n + 1, rfl⟩ ⟨⟨ρ (n + 1), hρ _, by rw [step, ih]⟩, hne⟩

end WF

/-! ## Bergman's induction -/

/-- Inclusion ambiguities are resolvable. -/
def InclusionResolvable : Prop :=
  ∀ u ∈ S.W, ∀ u' ∈ S.W, ∀ a b, u = a * u' * b → u' ≠ u →
    ReducesToZero S (inclusionObstruction S u u' a b)

/-- Overlap ambiguities are resolvable. -/
def OverlapResolvable : Prop :=
  ∀ u' ∈ S.W, ∀ u'' ∈ S.W, ∀ a b : FreeMonoid X, a ≠ 1 → b ≠ 1 → u' * a = b * u'' →
    a.toList.length < u''.toList.length → ReducesToZero S (overlapObstruction S u' u'' a b)

/-- `x ↦ P x Q`, as a linear map. -/
def ctxL (P Q : FreeAlg k X) : FreeAlg k X →ₗ[k] FreeAlg k X :=
  LinearMap.mulRight k Q ∘ₗ LinearMap.mulLeft k P

lemma ctxL_apply (P Q x : FreeAlg k X) : ctxL P Q x = P * x * Q := rfl

lemma reds_zero_ctx {o : FreeAlg k X} (p q : FreeMonoid X) (h : S.Reds o 0) :
    S.Reds (mono p * o * mono q) 0 := by
  simpa using reds_ctx p q h

section Core

/-- `a f(w) b` is determined when all monomials below `awb` are. -/
lemma det_below (hwf : WellFounded S.stepLT) {m a w b : FreeMonoid X} (hw : w ∈ S.W)
    (hm : m = a * w * b) (IH : ∀ m', S.stepLT m' m → ∃ v, S.Det (mono m') v) :
    ∃ v, S.Det (mono a * S.f w * mono b) v := by
  have hF := exists_irreducible hwf
  obtain ⟨v, hv, -⟩ := det_linear₂ hF (ctxL (mono a) (mono b)) (ctxL (mono a) (mono b))
    (S.f w) (by
      intro u hu
      obtain ⟨v, hv⟩ := IH (a * u * b) ⟨a, b, w, u, hw, hu, rfl, hm⟩
      have e : ctxL (mono a) (mono b) (mono u) = (mono (a * u * b) : FreeAlg k X) := by
        simp only [ctxL_apply, mono_mul]
      rw [e]
      exact ⟨v, hv, hv⟩)
  exact ⟨v, hv⟩

/-- If `r₁ - r₂` is `P o Q` with `o` reducing to zero, two determined elements agree. -/
lemma det_pair_of_reds_zero (hwf : WellFounded S.stepLT) {m a₁ w₁ b₁ a₂ w₂ b₂ : FreeMonoid X}
    (hw₁ : w₁ ∈ S.W) (hw₂ : w₂ ∈ S.W) (e₁ : m = a₁ * w₁ * b₁) (e₂ : m = a₂ * w₂ * b₂)
    (IH : ∀ m', S.stepLT m' m → ∃ v, S.Det (mono m') v) (P Q : FreeMonoid X) (o : FreeAlg k X)
    (ho : S.Reds o 0)
    (hdiff : mono a₁ * S.f w₁ * mono b₁ - mono a₂ * S.f w₂ * mono b₂ = mono P * o * mono Q ∨
      mono a₂ * S.f w₂ * mono b₂ - mono a₁ * S.f w₁ * mono b₁ = mono P * o * mono Q) :
    ∃ v, S.Det (mono a₁ * S.f w₁ * mono b₁) v ∧ S.Det (mono a₂ * S.f w₂ * mono b₂) v := by
  have hF := exists_irreducible hwf
  obtain ⟨v₁, hv₁⟩ := det_below hwf hw₁ e₁ IH
  obtain ⟨v₂, hv₂⟩ := det_below hwf hw₂ e₂ IH
  have hz := reds_zero_ctx P Q ho
  rcases hdiff with h | h
  · rw [← h] at hz
    exact ⟨v₁, hv₁, det_eq_of_reds_zero hF hv₁ hv₂ hz ▸ hv₂⟩
  · rw [← h] at hz
    exact ⟨v₁, hv₁, (det_eq_of_reds_zero hF hv₂ hv₁ hz) ▸ hv₂⟩

lemma reds_mono_step (a w b : FreeMonoid X) (hw : w ∈ S.W) {m : FreeMonoid X}
    (hm : m = a * w * b) : S.Reds (mono m) (mono a * S.f w * mono b) := by
  subst hm
  have := reds_basic (S := S) ⟨a, w, b, hw, rfl⟩ (mono (a * w * b))
  rwa [basicReduction_mono_self] at this

/-- **Two reductions at the same monomial have a common value** (`|a₁| ≤ |a₂|`): the case
analysis of two occurrences of rules in one word. -/
lemma det_two_decomps_aux (hwf : WellFounded S.stepLT) (hI : S.InclusionResolvable)
    (hO : S.OverlapResolvable) {m a₁ w₁ b₁ a₂ w₂ b₂ : FreeMonoid X} (hw₁ : w₁ ∈ S.W)
    (hw₂ : w₂ ∈ S.W) (e₁ : m = a₁ * w₁ * b₁) (e₂ : m = a₂ * w₂ * b₂)
    (hl : a₁.toList.length ≤ a₂.toList.length)
    (IH : ∀ m', S.stepLT m' m → ∃ v, S.Det (mono m') v) :
    ∃ v, S.Det (mono a₁ * S.f w₁ * mono b₁) v ∧ S.Det (mono a₂ * S.f w₂ * mono b₂) v := by
  have hF := exists_irreducible hwf
  rcases decomp_cases (e₁.symm.trans e₂) hl with ⟨rfl, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ |
    ⟨t, s, c, ht, hs, hc, rfl, rfl, rfl, rfl⟩ | ⟨t, d, htd, rfl, rfl, rfl⟩ |
    ⟨c, hc, rfl, rfl, rfl⟩
  · -- identical decompositions
    obtain ⟨v, hv⟩ := det_below hwf hw₁ e₁ IH
    exact ⟨v, hv, hv⟩
  · -- disjoint occurrences: both reduce to `a₁ f(w₁) t f(w₂) b₂`
    obtain ⟨V, hV₁, hV₂⟩ := det_linear₂ hF
      (ctxL (mono a₁) (mono (t * w₂ * b₂)))
      (ctxL (mono a₁) (mono t * S.f w₂ * mono b₂)) (S.f w₁) (fun u hu => by
        obtain ⟨v, hv⟩ := IH (a₁ * u * (t * w₂ * b₂)) ⟨a₁, t * w₂ * b₂, w₁, u, hw₁, hu, rfl, e₁⟩
        have h1 : ctxL (mono a₁) (mono (t * w₂ * b₂)) (mono u) =
            (mono (a₁ * u * (t * w₂ * b₂)) : FreeAlg k X) := by
          simp only [ctxL_apply, mono_mul]
        have h2 : ctxL (mono a₁) (mono t * S.f w₂ * mono b₂) (mono u) =
            mono (a₁ * u * t) * S.f w₂ * mono b₂ := by
          simp only [ctxL_apply, mono_mul, mul_assoc]
        refine ⟨v, by rw [h1]; exact hv, ?_⟩
        rw [h2]
        exact det_of_reds hv (reds_mono_step _ _ _ hw₂ (by simp [mul_assoc])))
    obtain ⟨V', hV'₁, hV'₂⟩ := det_linear₂ hF
      (ctxL (mono (a₁ * w₁ * t)) (mono b₂))
      (ctxL (mono a₁ * S.f w₁ * mono t) (mono b₂)) (S.f w₂) (fun u hu => by
        obtain ⟨v, hv⟩ := IH (a₁ * w₁ * t * u * b₂) ⟨a₁ * w₁ * t, b₂, w₂, u, hw₂, hu, rfl, e₂⟩
        have h1 : ctxL (mono (a₁ * w₁ * t)) (mono b₂) (mono u) =
            (mono (a₁ * w₁ * t * u * b₂) : FreeAlg k X) := by
          simp only [ctxL_apply, mono_mul]
        have h2 : ctxL (mono a₁ * S.f w₁ * mono t) (mono b₂) (mono u) =
            mono a₁ * S.f w₁ * mono (t * u * b₂) := by
          simp only [ctxL_apply, mono_mul, mul_assoc]
        refine ⟨v, by rw [h1]; exact hv, ?_⟩
        rw [h2]
        exact det_of_reds hv (reds_mono_step a₁ w₁ (t * u * b₂) hw₁ (by simp [mul_assoc])))
    have hVV : V = V' := by
      refine det_unique hF hV₂ ?_
      simpa [ctxL_apply, mul_assoc] using hV'₂
    refine ⟨V, by simpa [ctxL_apply] using hV₁, ?_⟩
    rw [hVV]
    simpa [ctxL_apply] using hV'₁
  · -- overlapping occurrences
    have hres := hO (t * s) hw₁ (s * c) hw₂ c t hc ht (mul_assoc t s c) (by
      rw [FreeMonoid.toList_mul, List.length_append]
      have := List.length_pos_iff.2 (toList_ne_nil hs)
      omega)
    exact det_pair_of_reds_zero hwf hw₁ hw₂ e₁ e₂ IH a₁ b₂ _ hres (Or.inr (by
      simp only [overlapObstruction, mono_mul, mul_sub, sub_mul, mul_assoc]))
  · -- `w₂` inside `w₁`
    have hres := hI (t * w₂ * d) hw₁ w₂ hw₂ t d rfl (ne_mul_of_ne_one htd)
    exact det_pair_of_reds_zero hwf hw₁ hw₂ e₁ e₂ IH a₁ b₁ _ hres (Or.inl (by
      simp only [inclusionObstruction, mono_mul, mul_sub, sub_mul, mul_assoc]))
  · -- `w₁` inside `w₂`, sharing the left end
    have hres := hI (w₁ * c) hw₂ w₁ hw₁ 1 c (by simp) (ne_mul_right_of_ne_one hc)
    exact det_pair_of_reds_zero hwf hw₁ hw₂ e₁ e₂ IH a₂ b₂ _ hres (Or.inr (by
      simp only [inclusionObstruction, mono_one, mono_mul, one_mul, mul_sub, sub_mul, mul_assoc]))

lemma det_two_decomps (hwf : WellFounded S.stepLT) (hI : S.InclusionResolvable)
    (hO : S.OverlapResolvable) {m a₁ w₁ b₁ a₂ w₂ b₂ : FreeMonoid X} (hw₁ : w₁ ∈ S.W)
    (hw₂ : w₂ ∈ S.W) (e₁ : m = a₁ * w₁ * b₁) (e₂ : m = a₂ * w₂ * b₂)
    (IH : ∀ m', S.stepLT m' m → ∃ v, S.Det (mono m') v) :
    ∃ v, S.Det (mono a₁ * S.f w₁ * mono b₁) v ∧ S.Det (mono a₂ * S.f w₂ * mono b₂) v := by
  rcases le_total a₁.toList.length a₂.toList.length with h | h
  · exact det_two_decomps_aux hwf hI hO hw₁ hw₂ e₁ e₂ h IH
  · obtain ⟨v, h2, h1⟩ := det_two_decomps_aux hwf hI hO hw₂ hw₁ e₂ e₁ h IH
    exact ⟨v, h1, h2⟩


lemma basicReduction_mono_ne (hwf : WellFounded S.stepLT) {a w b : FreeMonoid X} (hw : w ∈ S.W) :
    S.basicReduction a w b (mono (a * w * b)) ≠ mono (a * w * b) := by
  intro h
  rw [basicReduction_mono_self] at h
  have hc := congrArg (fun x : FreeAlg k X => x.coeff (a * w * b)) h
  simp at hc
  have h0 : (S.f w).coeff w = 0 := Finsupp.notMem_support_iff.1 (not_mem_supp_f hwf hw)
  rw [h0] at hc
  exact zero_ne_one hc

/-- **Bergman's lemma.** Under the ambiguity hypotheses, every monomial is determined. -/
theorem det_mono (hwf : WellFounded S.stepLT) (hI : S.InclusionResolvable)
    (hO : S.OverlapResolvable) (m : FreeMonoid X) : ∃ v, S.Det (mono m) v := by
  have hF := exists_irreducible hwf
  induction m using hwf.induction with
  | _ m IH =>
    by_cases hdec : ∃ a w b, w ∈ S.W ∧ m = a * w * b
    · obtain ⟨a₀, w₀, b₀, hw₀, hm₀⟩ := hdec
      obtain ⟨v₀, hv₀⟩ := det_below hwf hw₀ hm₀ IH
      refine ⟨v₀, fun h hr hirr => ?_⟩
      have hne : h ≠ mono m := by
        rintro rfl
        have := hirr (S.basicReduction a₀ w₀ b₀) ⟨a₀, w₀, b₀, hw₀, rfl⟩
        rw [hm₀] at this
        exact basicReduction_mono_ne hwf hw₀ this
      obtain ⟨ρ, ⟨a₁, w₁, b₁, hw₁, rfl⟩, hρne, hρr⟩ := reds_first hr hne
      have e₁ : m = a₁ * w₁ * b₁ := by
        by_contra hne'
        exact hρne (S.basicReduction_mono_of_ne hne')
      obtain ⟨v, hv₁, hv₀'⟩ := det_two_decomps hwf hI hO hw₁ hw₀ e₁ hm₀ IH
      have hvv : v = v₀ := det_unique hF hv₀' hv₀
      subst hvv
      have hρ : S.basicReduction a₁ w₁ b₁ (mono m) = mono a₁ * S.f w₁ * mono b₁ := by
        rw [e₁, basicReduction_mono_self]
      rw [hρ] at hρr
      exact hv₁ h hρr hirr
    · refine ⟨mono m, det_irr ?_⟩
      rintro ρ ⟨a, w, b, hw, rfl⟩
      exact S.basicReduction_mono_of_ne fun h => hdec ⟨a, w, b, hw, h⟩

/-- Every element is determined. -/
theorem det_all (hwf : WellFounded S.stepLT) (hI : S.InclusionResolvable)
    (hO : S.OverlapResolvable) (g : FreeAlg k X) : ∃ v, S.Det g v := by
  have hF := exists_irreducible hwf
  induction g using MonoidAlgebra.induction_on with
  | of m => simpa [mono, MonoidAlgebra.of_apply] using det_mono hwf hI hO m
  | add x y hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨v', hv'⟩ := hy
    exact ⟨v + v', det_add hF hv hv'⟩
  | smul c x hx =>
    obtain ⟨v, hv⟩ := hx
    exact ⟨c • v, det_smul hF c hv⟩

lemma toAlg_f {w : FreeMonoid X} (hw : w ∈ S.W) : S.toAlg (S.f w) = S.toAlg (mono w) :=
  (RingQuot.mkAlgHom_rel k (show S.rel (mono w) (S.f w) from ⟨w, hw, rfl, rfl⟩)).symm

/-- **Irreducible elements are determined by their class in `A_Σ`.** -/
theorem eq_of_toAlg_eq (hwf : WellFounded S.stepLT) (hI : S.InclusionResolvable)
    (hO : S.OverlapResolvable) {h h' : FreeAlg k X} (hh : S.IsIrreducible h)
    (hh' : S.IsIrreducible h') (e : S.toAlg h = S.toAlg h') : h = h' := by
  have hF := exists_irreducible hwf
  choose φ hφ using det_all hwf hI hO
  have φ_add : ∀ x y, φ (x + y) = φ x + φ y :=
    fun x y => det_unique hF (hφ _) (det_add hF (hφ x) (hφ y))
  have φ_smul : ∀ (c : k) x, φ (c • x) = c • φ x :=
    fun c x => det_unique hF (hφ _) (det_smul hF c (hφ x))
  have φ_reds : ∀ {x y}, S.Reds x y → φ x = φ y :=
    fun hr => det_unique hF (det_of_reds (hφ _) hr) (hφ _)
  have φ_irr : ∀ {x}, S.IsIrreducible x → φ x = x :=
    fun hx => det_unique hF (hφ _) (det_irr hx)
  have φ_zero : φ 0 = 0 := φ_irr fun ρ _ => map_zero ρ
  have φ_sub : ∀ x y, φ (x - y) = φ x - φ y := by
    intro x y
    have : x - y = x + (-1 : k) • y := by rw [neg_one_smul, sub_eq_add_neg]
    rw [this, φ_add, φ_smul, neg_one_smul, sub_eq_add_neg]
  have φ_ctx : ∀ x P Q, φ x = 0 → φ (mono P * x * mono Q) = 0 := by
    intro x P Q hx
    have hr : S.Reds x (φ x) := (det_final hF (hφ x)).1
    rw [φ_reds (reds_ctx P Q hr), hx]
    simpa using φ_zero
  have φ_ideal : ∀ x y z, φ x = 0 → φ (y * x * z) = 0 := by
    intro x y z hx
    have step1 : ∀ P z, φ (mono P * x * z) = 0 := by
      intro P z
      induction z using MonoidAlgebra.induction_on with
      | of Q => simpa [mono, MonoidAlgebra.of_apply] using φ_ctx x P Q hx
      | add z₁ z₂ h₁ h₂ => rw [mul_add, φ_add, h₁, h₂, add_zero]
      | smul c z h => rw [mul_smul_comm, φ_smul, h, smul_zero]
    induction y using MonoidAlgebra.induction_on with
    | of P => simpa [mono, MonoidAlgebra.of_apply] using step1 P z
    | add y₁ y₂ h₁ h₂ => rw [add_mul, add_mul, φ_add, h₁, h₂, add_zero]
    | smul c y h => rw [smul_mul_assoc, smul_mul_assoc, φ_smul, h, smul_zero]
  have hrel : ∀ {a b}, RingQuot.Rel S.rel a b → φ a = φ b := by
    intro a b hab
    induction hab with
    | of hr =>
      obtain ⟨w, hw, rfl, rfl⟩ := hr
      refine φ_reds ?_
      have := reds_basic (S := S) ⟨1, w, 1, hw, rfl⟩ (mono (1 * w * 1))
      rw [basicReduction_mono_self] at this
      simpa [mono_one] using this
    | add_left h ih => rw [φ_add, φ_add, ih]
    | @mul_left a b c h ih =>
      have h0 : φ (a - b) = 0 := by rw [φ_sub, ih, sub_self]
      have := φ_ideal _ 1 c h0
      rw [one_mul, sub_mul, φ_sub] at this
      exact sub_eq_zero.1 this
    | @mul_right a b c h ih =>
      have h0 : φ (b - c) = 0 := by rw [φ_sub, ih, sub_self]
      have := φ_ideal _ a 1 h0
      rw [mul_one, mul_sub, φ_sub] at this
      exact sub_eq_zero.1 this
  have hEq : Relation.EqvGen (RingQuot.Rel S.rel) h h' := by
    have e' : RingQuot.mkRingHom S.rel h = RingQuot.mkRingHom S.rel h' := by
      rw [← RingQuot.mkAlgHom_coe k S.rel]
      exact e
    simp only [RingQuot.mkRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] at e'
    exact Quot.eqvGen_exact (RingQuot.mk.inj e')
  have hφ_gen : ∀ x y, Relation.EqvGen (RingQuot.Rel S.rel) x y → φ x = φ y := by
    intro x y hxy
    induction hxy with
    | rel x y hxy => exact hrel hxy
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hφ_eq : φ h = φ h' := hφ_gen h h' hEq
  rw [← φ_irr hh, ← φ_irr hh', hφ_eq]

end Core

end RewritingSystem

/-- **Proposition 4.1 (Bergman's Diamond Lemma [21, Th. 1.2]).** A rewriting system with
well-founded `<_Σ` is convergent iff the obstructions of all inclusion and overlap ambiguities
are sent to zero by some reduction.

**Change.** The thesis assumes `Σ` terminating, which it takes (§2.1, citing [21, 40]) to mean
that `<_Σ` is well-founded. We assume well-foundedness, which implies termination
(`isTerminating_of_wellFounded`). The thesis deduces Proposition 4.1 from Theorem 3.2 applied to
the inclusion–exclusion model of Dotsenko–Khoroshkin [52, Th. 2.2], whose degree-two generators
are the inclusion and overlap ambiguities. The model is not constructed here. We prove the
statement directly by Bergman's argument. The finiteness hypotheses (`X`, `W` finite) are not
needed and dropped. -/
theorem diamondLemma (S : RewritingSystem k X) (hwf : WellFounded S.stepLT) :
    S.IsConvergent ↔
      (∀ u ∈ S.W, ∀ u' ∈ S.W, ∀ a b, u = a * u' * b → u' ≠ u →
        ReducesToZero S (inclusionObstruction S u u' a b)) ∧
      (∀ u' ∈ S.W, ∀ u'' ∈ S.W, ∀ a b : FreeMonoid X, a ≠ 1 → b ≠ 1 → u' * a = b * u'' →
        a.toList.length < u''.toList.length →
        ReducesToZero S (overlapObstruction S u' u'' a b)) := by
  have hF := RewritingSystem.exists_irreducible hwf
  constructor
  · rintro ⟨-, huniq⟩
    have key : ∀ o, S.toAlg o = 0 → S.Reds o 0 := by
      intro o ho
      obtain ⟨h, hr, hirr⟩ := hF o
      have h1 : S.IsNormalForm o h := ⟨hirr, RewritingSystem.toAlg_reds hr⟩
      have h2 : S.IsNormalForm o 0 := ⟨fun ρ _ => map_zero ρ, by rw [ho, map_zero]⟩
      exact (huniq o).unique h1 h2 ▸ hr
    refine ⟨fun u hu u' hu' a b e hne => key _ ?_, fun u' hu' u'' hu'' a b ha hb e hlen =>
      key _ ?_⟩
    · subst e
      simp only [inclusionObstruction, map_sub, map_mul, RewritingSystem.toAlg_f hu,
        RewritingSystem.toAlg_f hu', RewritingSystem.mono_mul, sub_self]
    · have h1 : S.toAlg (mono b * S.f u'') = S.toAlg (mono (b * u'')) := by
        rw [map_mul, RewritingSystem.toAlg_f hu'', ← map_mul, ← RewritingSystem.mono_mul]
      have h2 : S.toAlg (S.f u' * mono a) = S.toAlg (mono (u' * a)) := by
        rw [map_mul, RewritingSystem.toAlg_f hu', ← map_mul, ← RewritingSystem.mono_mul]
      rw [overlapObstruction, map_sub, h1, h2, e, sub_self]
  · rintro ⟨hI, hO⟩
    refine ⟨RewritingSystem.isTerminating_of_wellFounded hwf, fun g => ?_⟩
    obtain ⟨v, hv⟩ := RewritingSystem.det_all hwf hI hO g
    obtain ⟨hrv, hirrv⟩ := RewritingSystem.det_final hF hv
    refine ⟨v, ⟨hirrv, RewritingSystem.toAlg_reds hrv⟩, fun g' ⟨hirr', he'⟩ => ?_⟩
    exact RewritingSystem.eq_of_toAlg_eq hwf hI hO hirr' hirrv
      (he'.trans (RewritingSystem.toAlg_reds hrv).symm)

/-- **Proposition 4.2 (Triangle Lemma [31, §2.4.3]).** A minimal terminating rewriting system
(no relations of length one, none dividing another) is convergent iff the S-polynomials of the
minimal overlaps (the Anick `2`-chains `c = u'a = bu''`) are sent to zero by some reduction. -/
theorem triangleLemma [Finite X] (W : Set (List X)) (hW : W.Finite) (hmin : (monData W).IsMinimal)
    (f : FreeMonoid X → FreeAlg k X)
    (hterm : (⟨FreeMonoid.ofList '' W, f⟩ : RewritingSystem k X).IsTerminating) :
    (⟨FreeMonoid.ofList '' W, f⟩ : RewritingSystem k X).IsConvergent ↔
      ∀ c ∈ (monData W).Chains 2, ∀ u' ∈ W, ∀ u'' ∈ W, ∀ a b : List X,
        c = u' ++ a → c = b ++ u'' →
        ReducesToZero (⟨FreeMonoid.ofList '' W, f⟩ : RewritingSystem k X)
          (overlapObstruction (⟨FreeMonoid.ofList '' W, f⟩ : RewritingSystem k X)
            (FreeMonoid.ofList u') (FreeMonoid.ofList u'') (FreeMonoid.ofList a)
            (FreeMonoid.ofList b)) := by
  sorry

end TamaroffPhd

end
