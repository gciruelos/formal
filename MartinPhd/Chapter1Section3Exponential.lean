import MartinPhd.Chapter1Section2Monoidal

/-!
# Chapter 1, Section 1.3 (the exponential species)

Contents:
* Chapter1Section3
* Equiv
* EquivBack
-/

section Chapter1Section3

open scoped BigOperators TensorProduct
open CategoryTheory Module

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

/-! ## §1.3 La especie exponencial -/

section Exponential

variable {F : Type} [Field F] [Finite F] {k : Type} [Field k]

open MonoidalCategory

/-- The exponential species `e`: `e(V) = k·e_V`, every `e(φ)` the identity. -/
def expSpecies : GLSpecies F k := (Functor.const _).obj (ModuleCat.of k k)

/-- The element `∑_{S ≤ V} e_S ⊗ e_{V/S}` of `(e ⊗ e)(V)`. -/
def comulElt (V : FGModuleCat.{0} F) :
    GLSpecies.cauchyObj (expSpecies (F := F) (k := k)) expSpecies V :=
  ∑ S : Submodule F V, (DirectSum.lof k (Submodule F V)
    (fun S => TensorProduct k ((expSpecies (F := F) (k := k)).ev (sub S))
      ((expSpecies (F := F) (k := k)).ev (quo S))) S) ((1 : k) ⊗ₜ (1 : k))

theorem cauchyMap_comulElt {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) :
    GLSpecies.cauchyMap (expSpecies (F := F) (k := k)) expSpecies e (comulElt V) =
      comulElt W := by
  unfold comulElt
  rw [map_sum]
  let σ : Submodule F V ≃ Submodule F W := (Submodule.orderIsoMapComap e).toEquiv
  rw [← Equiv.sum_comp σ (fun T => (DirectSum.lof k (Submodule F W)
    (fun S => TensorProduct k ((expSpecies (F := F) (k := k)).ev (sub S))
      ((expSpecies (F := F) (k := k)).ev (quo S))) T) ((1 : k) ⊗ₜ (1 : k)))]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [GLSpecies.cauchyMap, DirectSum.toModule_lof, LinearMap.comp_apply,
    TensorProduct.map_tmul]
  rfl

/-- The comultiplication `Δ(e_V) = ∑_{S ≤ V} e_S ⊗ e_{V/S}` of `e`. -/
def expComul : (expSpecies (F := F) (k := k)) ⟶ expSpecies ⊗ expSpecies :=
    { app := fun V => ModuleCat.ofHom <| LinearMap.toSpanSingleton k _ (comulElt V.of)
      naturality := by
        intro V W φ
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro c
        let c' : k := c
        show c' • comulElt W.of = GLSpecies.cauchyMap (expSpecies (F := F) (k := k)) expSpecies
          (FGModuleCat.isoToLinearEquiv φ.iso) (c' • comulElt V.of)
        exact (congrArg (c' • ·) (cauchyMap_comulElt (F := F) (k := k)
          (FGModuleCat.isoToLinearEquiv φ.iso)).symm).trans
          (map_smul (GLSpecies.cauchyMap (expSpecies (F := F) (k := k)) expSpecies
            (FGModuleCat.isoToLinearEquiv φ.iso)) c' (comulElt V.of)).symm }

/-- The counit `ε(e_0) = 1`, `ε(e_V) = 0` for `V ≠ 0`. -/
def expCounit : (expSpecies (F := F) (k := k)) ⟶ 𝟙_ (GLSpecies F k) :=
    { app := fun V => ModuleCat.ofHom <|
        if h : finrank F V.of = 0 then
          LinearMap.codRestrict _ LinearMap.id (fun v => by simp [h])
        else 0
      naturality := by
        intro V W φ
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro c
        have hfr : finrank F V.of = finrank F W.of :=
          LinearEquiv.finrank_eq (FGModuleCat.isoToLinearEquiv φ.iso)
        by_cases h : finrank F V.of = 0
        · have h' : finrank F W.of = 0 := hfr ▸ h
          apply Subtype.ext
          simp [h, h']
          rfl
        · have h' : ¬ finrank F W.of = 0 := hfr ▸ h
          apply Subtype.ext
          simp [h, h']
          rfl }

/-- The generator `e_V` of `e(V) = k·e_V`. -/
def expOne (V : FGModuleCat.{0} F) : (expSpecies (F := F) (k := k)).ev V := (1 : k)

theorem expCounit_val (V : FGModuleCat.{0} F) (c : (expSpecies (F := F) (k := k)).ev V) :
    (((expCounit (F := F) (k := k)).app ⟨V⟩).hom c).val =
      if finrank F V = 0 then (show k from c) else 0 := by
  unfold expCounit
  by_cases h : finrank F V = 0
  · simp only [h, if_true, dif_pos]
    rfl
  · simp only [h, if_false, dif_neg, not_false_eq_true]
    rfl

theorem exp_counit_comul :
    expComul (F := F) (k := k) ≫ expCounit ▷ expSpecies = (λ_ (expSpecies (F := F) (k := k))).inv := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  let c' : k := c
  change GLSpecies.cauchyHomMap expCounit (𝟙 _) V.of (c' • comulElt V.of) =
    GLSpecies.leftUnitInv expSpecies V.of c'
  rw [map_smul, comulElt, map_sum, Finset.sum_eq_single ⊥]
  · change c' • GLSpecies.cauchyHomMap expCounit (𝟙 _) V.of
      (GLSpecies.pair expSpecies expSpecies V.of ⊥ (expOne _) (expOne _)) =
      GLSpecies.pair GLSpecies.unit expSpecies V.of ⊥ (GLSpecies.unitOne _ (by simp)) c'
    rw [GLSpecies.cauchyHomMap_pair]
    have h1 : ((expCounit (F := F) (k := k)).app ⟨sub (⊥ : Submodule F V.of)⟩).hom
        (expOne _) = GLSpecies.unitOne _ (by simp) :=
      Subtype.ext (by
        rw [expCounit_val, if_pos (by simp)]
        rfl)
    rw [h1]
    unfold GLSpecies.pair
    rw [← map_smul]
    congr 1
    refine (TensorProduct.smul_tmul' (R := k) c'
      (GLSpecies.unitOne (F := F) (k := k) (sub (⊥ : Submodule F V.of)) (by simp))
      (expOne (F := F) (k := k) (quo (⊥ : Submodule F V.of)))).trans
      ((TensorProduct.smul_tmul (R := k) (R' := k) c'
      (GLSpecies.unitOne (F := F) (k := k) (sub (⊥ : Submodule F V.of)) (by simp))
      (expOne (F := F) (k := k) (quo (⊥ : Submodule F V.of)))).trans ?_)
    congr 1
    exact mul_one c'
  · intro b _ hb
    change GLSpecies.cauchyHomMap expCounit (𝟙 _) V.of
      (GLSpecies.pair expSpecies expSpecies V.of b (expOne _) (expOne _)) = 0
    rw [GLSpecies.cauchyHomMap_pair]
    have h1 : ((expCounit (F := F) (k := k)).app ⟨sub b⟩).hom (expOne _) = 0 :=
      Subtype.ext (by
        rw [expCounit_val, if_neg (Submodule.finrank_eq_zero.not.mpr hb)]; rfl)
    rw [h1]
    simp [GLSpecies.pair]
  · simp

theorem finrank_quotient_eq_zero_iff (V : FGModuleCat.{0} F) (S : Submodule F V) :
    finrank F (V ⧸ S) = 0 ↔ S = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    have hr := S.finrank_quotient_add_finrank
    omega
  · rintro rfl
    exact finrank_zero_of_subsingleton

theorem exp_comul_counit :
    expComul (F := F) (k := k) ≫ expSpecies ◁ expCounit = (ρ_ (expSpecies (F := F) (k := k))).inv := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  let c' : k := c
  change GLSpecies.cauchyHomMap (𝟙 _) expCounit V.of (c' • comulElt V.of) =
    GLSpecies.rightUnitInv expSpecies V.of c'
  rw [map_smul, comulElt, map_sum, Finset.sum_eq_single ⊤]
  · change c' • GLSpecies.cauchyHomMap (𝟙 _) expCounit V.of
      (GLSpecies.pair expSpecies expSpecies V.of ⊤ (expOne _) (expOne _)) =
      GLSpecies.pair expSpecies GLSpecies.unit V.of ⊤ c'
        (GLSpecies.unitOne _ ((finrank_quotient_eq_zero_iff V.of ⊤).mpr rfl))
    rw [GLSpecies.cauchyHomMap_pair]
    have h1 : ((expCounit (F := F) (k := k)).app ⟨quo (⊤ : Submodule F V.of)⟩).hom
        (expOne _) = GLSpecies.unitOne _ ((finrank_quotient_eq_zero_iff V.of ⊤).mpr rfl) :=
      Subtype.ext (by
        rw [expCounit_val, if_pos ((finrank_quotient_eq_zero_iff V.of ⊤).mpr rfl)]
        rfl)
    rw [h1]
    unfold GLSpecies.pair
    rw [← map_smul]
    congr 1
    refine (TensorProduct.smul_tmul' (R := k) c' (expOne (F := F) (k := k) (sub (⊤ : Submodule F V.of)))
      (GLSpecies.unitOne (F := F) (k := k) (quo (⊤ : Submodule F V.of))
        ((finrank_quotient_eq_zero_iff V.of ⊤).mpr rfl))).trans ?_
    congr 1
    exact mul_one c'
  · intro b _ hb
    change GLSpecies.cauchyHomMap (𝟙 _) expCounit V.of
      (GLSpecies.pair expSpecies expSpecies V.of b (expOne _) (expOne _)) = 0
    rw [GLSpecies.cauchyHomMap_pair]
    have h1 : ((expCounit (F := F) (k := k)).app ⟨quo b⟩).hom (expOne _) = 0 :=
      Subtype.ext (by
        rw [expCounit_val, if_neg (mt (finrank_quotient_eq_zero_iff V.of b).mp hb)]; rfl)
    rw [h1]
    simp [GLSpecies.pair]
  · simp

@[simp] theorem exp_mapEquiv {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W)
    (a : (expSpecies (F := F) (k := k)).ev V) :
    (expSpecies (F := F) (k := k)).mapEquiv e a = (a : k) := rfl

theorem expComul_one (V : FGModuleCat.{0} F) :
    (((expComul (F := F) (k := k)).app ⟨V⟩).hom (expOne (F := F) (k := k) V)) = comulElt (F := F) (k := k) V := by
  change (1 : k) • comulElt (F := F) (k := k) V = comulElt V
  exact one_smul _ _

/-- The basic summand of `(e ⊗ (e ⊗ e))(V)` indexed by a flag `T ≤ Q ≤ V` with `Q ≤ V/T`. -/
def expTerm (V : FGModuleCat.{0} F) (T : Submodule F V) (Q : Submodule F (V ⧸ T)) :
    GLSpecies.cauchyObj (expSpecies (F := F) (k := k))
      (expSpecies ⊗ expSpecies) V :=
  GLSpecies.pair expSpecies (expSpecies ⊗ expSpecies) V T (expOne (F := F) (k := k) _)
    (GLSpecies.pair expSpecies expSpecies (quo T) Q (expOne (F := F) (k := k) _)
      (expOne (F := F) (k := k) _))

theorem exp_comul_assoc :
    expComul (F := F) (k := k) ≫ expSpecies ◁ expComul =
      expComul ≫ expComul ▷ expSpecies ≫ (α_ expSpecies expSpecies expSpecies).hom := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  let c' : k := c
  change GLSpecies.cauchyHomMap (𝟙 _) (expComul (F := F) (k := k)) V.of
      (c' • comulElt (F := F) (k := k) V.of) =
    GLSpecies.assocEquiv expSpecies expSpecies expSpecies V.of
      (GLSpecies.cauchyHomMap (expComul (F := F) (k := k)) (𝟙 _) V.of
        (c' • comulElt (F := F) (k := k) V.of))
  have hL : GLSpecies.cauchyHomMap (𝟙 _) (expComul (F := F) (k := k)) V.of
        (c' • comulElt (F := F) (k := k) V.of) =
      c' • ∑ S : Submodule F V.of, ∑ Q : Submodule F (V.of ⧸ S), expTerm V.of S Q := by
    rw [map_smul]
    congr 1
    rw [comulElt, map_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    change GLSpecies.cauchyHomMap (𝟙 _) (expComul (F := F) (k := k)) V.of
      (GLSpecies.pair expSpecies expSpecies V.of S (expOne _) (expOne _)) = _
    rw [GLSpecies.cauchyHomMap_pair]
    change GLSpecies.pair expSpecies (expSpecies ⊗ expSpecies) V.of S (expOne _)
      (((expComul (F := F) (k := k)).app ⟨quo S⟩).hom (expOne _)) = _
    rw [expComul_one, comulElt]
    unfold GLSpecies.pair
    rw [TensorProduct.tmul_sum, map_sum]
    rfl
  have hR : GLSpecies.assocEquiv expSpecies expSpecies expSpecies V.of
      (GLSpecies.cauchyHomMap (expComul (F := F) (k := k)) (𝟙 _) V.of
        (c' • comulElt (F := F) (k := k) V.of)) =
      c' • ∑ S : Submodule F V.of, ∑ T : Submodule F S,
        expTerm V.of (GLSpecies.flagLower S T) (S.map (GLSpecies.flagLower S T).mkQ) := by
    rw [map_smul, map_smul]
    congr 1
    rw [comulElt, map_sum, map_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    change GLSpecies.assocEquiv expSpecies expSpecies expSpecies V.of
      (GLSpecies.cauchyHomMap (expComul (F := F) (k := k)) (𝟙 _) V.of
        (GLSpecies.pair expSpecies expSpecies V.of S (expOne _) (expOne _))) = _
    rw [GLSpecies.cauchyHomMap_pair]
    change GLSpecies.assocEquiv expSpecies expSpecies expSpecies V.of
      (GLSpecies.pair (expSpecies ⊗ expSpecies) expSpecies V.of S
        (((expComul (F := F) (k := k)).app ⟨sub S⟩).hom (expOne _)) (expOne _)) = _
    rw [expComul_one, comulElt]
    unfold GLSpecies.pair
    rw [TensorProduct.sum_tmul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    exact GLSpecies.assocEquiv_pair expSpecies expSpecies expSpecies V.of S T
      (expOne _) (expOne _) (expOne _)
  rw [hL, hR]
  congr 1
  have key : ∑ q : GLSpecies.LeftFlagIndex V.of,
      expTerm (F := F) (k := k) V.of (GLSpecies.flagLower q.1 q.2)
        (q.1.map (GLSpecies.flagLower q.1 q.2).mkQ) =
      ∑ p : GLSpecies.RightFlagIndex V.of, expTerm (F := F) (k := k) V.of p.1 p.2 :=
    Fintype.sum_equiv (GLSpecies.flagIndexEquiv V.of) _ _ (fun q => by
      rfl)
  rw [Fintype.sum_sigma, Fintype.sum_sigma] at key
  exact key.symm

/-- `e` is a coalgebra: `Δ(e_V) = ∑_{S ≤ V} e_S ⊗ e_{V/S}`, `ε(e_0) = 1`. (It is a
bialgebra, with `μ(e_S ⊗ e_{V/S}) = e_V`, `η(1) = e_0`; only the coalgebra is used.) -/
instance : ComonObj (expSpecies (F := F) (k := k)) where
  comul := expComul
  counit := expCounit
  counit_comul := exp_counit_comul
  comul_counit := exp_comul_counit
  comul_assoc := exp_comul_assoc

variable (F k) in
/-- `e` as a comonoid object of `Sp`. -/
def expComon : Comon (GLSpecies F k) := ⟨expSpecies⟩

/-- **e-bicomodules in coordinates** (1.7). A `e`-bicomodule structure on a species `x`
amounts to restriction maps `z ↦ z|_S : x(V) → x(S)` (from `ρ`) and projection maps
`z ↦ z|_{V/S} : x(V) → x(V/S)` (from `λ`), natural in `V` and satisfying (1.7).

**Gap (typo, §1.8).** In §1.8 the thesis swaps the names `l` and `r` relative to (1.7); we
say `res`/`proj`. -/
structure EBicomod (F : Type) [Field F] (k : Type) [Field k] where
  X : GLSpecies F k
  res : ∀ (V : FGModuleCat.{0} F) (S : Submodule F V), X.ev V →ₗ[k] X.ev (sub S)
  proj : ∀ (V : FGModuleCat.{0} F) (S : Submodule F V), X.ev V →ₗ[k] X.ev (quo S)
  res_natural : ∀ {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) (S : Submodule F V),
    X.mapEquiv (V := sub S) (W := sub (S.map (e : V →ₗ[F] W))) (e.submoduleMap S) ∘ₗ res V S =
      res W (S.map (e : V →ₗ[F] W)) ∘ₗ X.mapEquiv e
  proj_natural : ∀ {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) (S : Submodule F V),
    X.mapEquiv (V := quo S) (W := quo (S.map (e : V →ₗ[F] W)))
        (Submodule.Quotient.equiv S _ e rfl) ∘ₗ proj V S =
      proj W (S.map (e : V →ₗ[F] W)) ∘ₗ X.mapEquiv e
  /-- `x(Φ_{T,S,V}) ∘ r_{V/T,S/T} ∘ r_{V,T} = r_{V,S}`. -/
  proj_proj : ∀ (V : FGModuleCat.{0} F) (T S : Submodule F V) (h : T ≤ S),
    X.mapEquiv (V := quo (V := quo T) (S.map T.mkQ)) (W := quo S)
        (Submodule.quotientQuotientEquivQuotient T S h) ∘ₗ
      proj (quo T) (S.map T.mkQ) ∘ₗ proj V T = proj V S
  /-- `l_{S,T} ∘ l_{V,S} = l_{V,T}`. -/
  res_res : ∀ (V : FGModuleCat.{0} F) (T S : Submodule F V) (h : T ≤ S),
    X.mapEquiv (V := sub (V := sub S) (T.comap S.subtype)) (W := sub T)
        (Submodule.comapSubtypeEquivOfLe h) ∘ₗ
      res (sub S) (T.comap S.subtype) ∘ₗ res V S = res V T
  /-- `r_{V,0} = id`. -/
  proj_bot : ∀ V : FGModuleCat.{0} F,
    proj V ⊥ = X.mapEquiv (V := V) (W := quo (⊥ : Submodule F V))
      (Submodule.quotEquivOfEqBot ⊥ rfl).symm
  /-- `l_{V,V} = id`. -/
  res_top : ∀ V : FGModuleCat.{0} F,
    res V ⊤ = X.mapEquiv (V := V) (W := sub (⊤ : Submodule F V)) Submodule.topEquiv.symm
  /-- `r_{S,T} ∘ l_{V,S} = l_{V/T,S/T} ∘ r_{V,T}`, up to `S/T ≅ (S + T)/T`. -/
  proj_res : ∀ (V : FGModuleCat.{0} F) (T S : Submodule F V) (_h : T ≤ S),
    X.mapEquiv (V := quo (V := sub S) (T.comap S.subtype)) (W := sub (V := quo T) (S.map T.mkQ))
        (((Submodule.quotEquivOfEq _ _ (by
            rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
          (T.mkQ ∘ₗ S.subtype).quotKerEquivRange).trans
          (LinearEquiv.ofEq _ _ (by
            rw [LinearMap.range_comp, Submodule.range_subtype]))) ∘ₗ
      proj (sub S) (T.comap S.subtype) ∘ₗ res V S =
    res (quo T) (S.map T.mkQ) ∘ₗ proj V T

/-- The **trivial** `e`-bicomodule structure on a species: `z|_S = 0` unless `S = V`,
and `z|_{V/S} = 0` unless `S = 0`. -/
def EBicomod.trivial (x : GLSpecies F k) : EBicomod F k where
  X := x
  res V S := if h : S = ⊤ then
      x.mapEquiv (V := V) (W := sub S) (Submodule.topEquiv.symm.trans (LinearEquiv.ofEq _ _ h.symm))
    else 0
  proj V S := if h : S = ⊥ then
      x.mapEquiv (V := V) (W := quo S) (Submodule.quotEquivOfEqBot S h).symm
    else 0
  res_natural := by
    intro V W e S
    have hiff : S = ⊤ ↔ S.map (e : V →ₗ[F] W) = ⊤ := by
      constructor
      · intro h; rw [h, Submodule.map_top]; exact LinearEquiv.range e
      · intro h
        rw [← Submodule.comap_map_eq_of_injective e.injective S, h, Submodule.comap_top]
    by_cases h : S = ⊤
    · have h' := hiff.1 h
      simp only [dif_pos h, dif_pos h']
      rw [← GLSpecies.mapEquiv_trans, ← GLSpecies.mapEquiv_trans]
      congr 1
    · have h' : ¬ S.map (e : V →ₗ[F] W) = ⊤ := fun h2 => h (hiff.2 h2)
      simp only [dif_neg h, dif_neg h']
      simp
  proj_natural := by
    intro V W e S
    have hiff : S = ⊥ ↔ S.map (e : V →ₗ[F] W) = ⊥ := by
      constructor
      · intro h; rw [h, Submodule.map_bot]
      · intro h
        rw [← Submodule.comap_map_eq_of_injective e.injective S, h, Submodule.comap_bot,
          LinearEquiv.ker]
    by_cases h : S = ⊥
    · have h' := hiff.1 h
      simp only [dif_pos h, dif_pos h']
      rw [← GLSpecies.mapEquiv_trans, ← GLSpecies.mapEquiv_trans]
      congr 1
      ext v
      subst h
      rfl
    · have h' : ¬ S.map (e : V →ₗ[F] W) = ⊥ := fun h2 => h (hiff.2 h2)
      simp only [dif_neg h, dif_neg h']
      simp
  proj_proj := by
    intro V T S hTS
    by_cases hS : S = ⊥
    · have hT : T = ⊥ := le_bot_iff.1 (hS ▸ hTS)
      have hS' : S.map T.mkQ = ⊥ := by rw [hS, Submodule.map_bot]
      simp only [dif_pos hS, dif_pos hT, dif_pos hS']
      rw [← GLSpecies.mapEquiv_trans, ← GLSpecies.mapEquiv_trans]
      congr 1
      ext v
      subst hS hT
      rfl
    · simp only [dif_neg hS]
      by_cases hT : T = ⊥
      · have hS' : ¬ S.map T.mkQ = ⊥ := by
          intro h
          have h2 : S ≤ T := by
            have := Submodule.map_le_iff_le_comap.1 h.le
            rwa [Submodule.comap_bot, Submodule.ker_mkQ] at this
          exact hS (le_bot_iff.1 (hT ▸ h2))
        simp only [dif_neg hS']
        simp
      · simp only [dif_neg hT]
        simp
  res_res := by
    intro V T S hTS
    by_cases hT : T = ⊤
    · have hS : S = ⊤ := top_le_iff.1 (hT ▸ hTS)
      have hT' : T.comap S.subtype = ⊤ := by
        rw [eq_top_iff]
        intro x _
        show (x : V) ∈ T
        rw [hT]; trivial
      simp only [dif_pos hT, dif_pos hS, dif_pos hT']
      rw [← GLSpecies.mapEquiv_trans, ← GLSpecies.mapEquiv_trans]
      congr 1
    · simp only [dif_neg hT]
      by_cases hS : S = ⊤
      · have hT' : ¬ T.comap S.subtype = ⊤ := by
          intro h
          apply hT
          rw [eq_top_iff]
          intro v _
          have : (⟨v, by rw [hS]; trivial⟩ : S) ∈ T.comap S.subtype := by rw [h]; trivial
          exact this
        simp only [dif_neg hT']
        simp
      · simp only [dif_neg hS]
        simp
  proj_bot := by
    intro V
    simp only [dif_pos rfl]
    congr 1
  res_top := by
    intro V
    simp only [dif_pos rfl]
    congr 1
  proj_res := by
    intro V T S hTS
    by_cases hmain : S = ⊤ ∧ T = ⊥
    · obtain ⟨hS, hT⟩ := hmain
      have h1 : T.comap S.subtype = ⊥ := by subst hT; simp
      have h2 : S.map T.mkQ = ⊤ := by
        subst hS; rw [Submodule.map_top, Submodule.range_mkQ]
      simp only [dif_pos hS, dif_pos hT, dif_pos h1, dif_pos h2]
      rw [← GLSpecies.mapEquiv_trans, ← GLSpecies.mapEquiv_trans, ← GLSpecies.mapEquiv_trans]
      congr 1
      ext v
      subst hS hT
      rfl
    · by_cases hS : S = ⊤
      · have hT : T ≠ ⊥ := fun h => hmain ⟨hS, h⟩
        have h1 : ¬ T.comap S.subtype = ⊥ := by
          intro h
          apply hT
          rw [eq_bot_iff]
          intro v hv
          have : (⟨v, by rw [hS]; trivial⟩ : S) ∈ T.comap S.subtype := hv
          rw [h] at this
          have h0 : (⟨v, _⟩ : S) = 0 := this
          simpa using congrArg Subtype.val h0
        simp only [dif_pos hS, dif_neg h1, dif_neg hT]
        simp
      · simp only [dif_neg hS]
        by_cases hT : T = ⊥
        · have h2 : ¬ S.map T.mkQ = ⊤ := by
            intro h
            apply hS
            rw [eq_top_iff]
            intro v _
            have : T.mkQ v ∈ S.map T.mkQ := by rw [h]; trivial
            obtain ⟨w, hw, hwv⟩ := this
            have : w = v := by
              have := (Submodule.Quotient.eq T).1 hwv
              rw [hT] at this
              simpa [sub_eq_zero] using this
            exact this ▸ hw
          simp only [dif_neg h2]
          simp
        · simp only [dif_neg hT]
          simp

/-- The exponential species with its canonical bicomodule structure. -/
def EBicomod.exp : EBicomod F k where
  X := expSpecies
  res _ _ := LinearMap.id
  proj _ _ := LinearMap.id
  res_natural := by intros; rfl
  proj_natural := by intros; rfl
  proj_proj := by intros; rfl
  res_res := by intros; rfl
  proj_bot := by intros; rfl
  res_top := by intros; rfl
  proj_res := by intros; rfl

/-- The unit species `1`, a (trivial) `e`-bicomodule. -/
def EBicomod.unit : EBicomod F k := EBicomod.trivial GLSpecies.unit

/-- The canonical isomorphism `S/(T ∩ S) ≅ (S + T)/T`, for `T ≤ S` (as in `proj_res`). -/
def subQuotIso {V : FGModuleCat.{0} F} (T S : Submodule F V) :
    quo (V := sub S) (T.comap S.subtype) ≃ₗ[F] ↥(S.map T.mkQ) :=
  ((Submodule.quotEquivOfEq _ _ (by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
    (T.mkQ ∘ₗ S.subtype).quotKerEquivRange).trans
    (LinearEquiv.ofEq _ _ (by
      rw [LinearMap.range_comp, Submodule.range_subtype]))

/-- An `e`-bicomodule that is also a coalgebra in `e`-bicomodules, in coordinates:
`Δ_S : x(V) → x(S) ⊗ x(V/S)`. Only the comultiplication enters the cup product; the
compatibility axioms `comul_proj`, `comul_res`, `comul_res_proj` are exactly those used in the
Leibniz rule (coassociativity itself is not needed). -/
structure EBicomodCoalg (F : Type) [Field F] (k : Type) [Field k] extends EBicomod F k where
  comul : ∀ (V : FGModuleCat.{0} F) (S : Submodule F V), X.ev V →ₗ[k] TensorProduct k (X.ev (sub S)) (X.ev (quo S))
  /-- Naturality of `Δ_S` under linear isomorphisms. -/
  comul_natural : ∀ {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) (S : Submodule F V),
    TensorProduct.map
        (X.mapEquiv (V := sub S) (W := sub (S.map (e : V →ₗ[F] W))) (e.submoduleMap S))
        (X.mapEquiv (V := quo S) (W := quo (S.map (e : V →ₗ[F] W)))
          (Submodule.Quotient.equiv S _ e rfl)) ∘ₗ comul V S =
      comul W (S.map (e : V →ₗ[F] W)) ∘ₗ X.mapEquiv e
  /-- `(r_{S,T} ⊗ id) ∘ Δ_S = Δ_{S/T} ∘ r_{V,T}` for `T ≤ S`, up to the canonical isos. -/
  comul_proj : ∀ (V : FGModuleCat.{0} F) (T S : Submodule F V) (_h : T ≤ S),
    TensorProduct.map (X.mapEquiv (V := quo (V := sub S) (T.comap S.subtype))
          (W := sub (V := quo T) (S.map T.mkQ)) (subQuotIso T S))
        (X.mapEquiv (V := quo S) (W := quo (V := quo T) (S.map T.mkQ))
          (Submodule.quotientQuotientEquivQuotient T S _h).symm) ∘ₗ
      TensorProduct.map (proj (sub S) (T.comap S.subtype)) LinearMap.id ∘ₗ comul V S =
    comul (quo T) (S.map T.mkQ) ∘ₗ proj V T
  /-- `(id ⊗ l_{V/S,U/S}) ∘ Δ_S = Δ_S^U ∘ l_{V,U}` for `S ≤ U`, up to the canonical isos. -/
  comul_res : ∀ (V : FGModuleCat.{0} F) (S U : Submodule F V) (_h : S ≤ U),
    TensorProduct.map (X.mapEquiv (V := sub (V := sub U) (S.comap U.subtype)) (W := sub S)
          (Submodule.comapSubtypeEquivOfLe _h))
        (X.mapEquiv (V := quo (V := sub U) (S.comap U.subtype))
          (W := sub (V := quo S) (U.map S.mkQ)) (subQuotIso S U)) ∘ₗ
      comul (sub U) (S.comap U.subtype) ∘ₗ res V U =
    TensorProduct.map LinearMap.id (res (quo S) (U.map S.mkQ)) ∘ₗ comul V S
  /-- `(l_{S,S'} ⊗ id) ∘ Δ_S = (id ⊗ r_{V/S',S/S'}) ∘ Δ_{S'}` for `S' ≤ S`, up to isos. -/
  comul_res_proj : ∀ (V : FGModuleCat.{0} F) (T S : Submodule F V) (_h : T ≤ S),
    TensorProduct.map (X.mapEquiv (V := sub (V := sub S) (T.comap S.subtype)) (W := sub T)
          (Submodule.comapSubtypeEquivOfLe _h))
        LinearMap.id ∘ₗ
      TensorProduct.map (res (sub S) (T.comap S.subtype)) LinearMap.id ∘ₗ comul V S =
    TensorProduct.map LinearMap.id (X.mapEquiv (V := quo (V := quo T) (S.map T.mkQ))
        (W := quo S) (Submodule.quotientQuotientEquivQuotient T S _h)) ∘ₗ
      TensorProduct.map LinearMap.id (proj (quo T) (S.map T.mkQ)) ∘ₗ comul V T

end Exponential

end MartinPhd

end
end Chapter1Section3

section Equiv

/-
Formalization of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# `e`-bicomodules in coordinates vs. bicomodules over `e` (§1.3)

The forward direction `Bicomod e → EBicomod`: restriction and projection maps are the
components of the two coactions.
-/

open scoped BigOperators TensorProduct DirectSum
open CategoryTheory Module MonoidalCategory

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

namespace GLSpecies

/-- The component of an element of the Cauchy product in the summand indexed by `S`. -/
def comp (x y : GLSpecies F k) (V : FGModuleCat.{0} F) (S : Submodule F V) :
    cauchyObj x y V →ₗ[k] x.ev (sub S) ⊗[k] y.ev (quo S) :=
  DirectSum.component k (Submodule F V) (fun T => x.ev (sub T) ⊗[k] y.ev (quo T)) S

theorem comp_pair_self (x y : GLSpecies F k) (V : FGModuleCat.{0} F) (S : Submodule F V)
    (a : x.ev (sub S)) (b : y.ev (quo S)) : comp x y V S (pair x y V S a b) = a ⊗ₜ b := by
  simp [comp, pair, DirectSum.component.of]

theorem comp_pair_ne (x y : GLSpecies F k) (V : FGModuleCat.{0} F) {S T : Submodule F V}
    (h : S ≠ T) (a : x.ev (sub T)) (b : y.ev (quo T)) : comp x y V S (pair x y V T a b) = 0 := by
  simp [comp, pair, DirectSum.component.of, h.symm]

theorem comp_cauchyMap (x y : GLSpecies F k) {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W)
    (S : Submodule F V) (u : cauchyObj x y V) :
    comp x y W (S.map (e : V →ₗ[F] W)) (cauchyMap x y e u) =
      TensorProduct.map (x.mapEquiv (e.submoduleMap S))
        (y.mapEquiv (Submodule.Quotient.equiv S _ e rfl)) (comp x y V S u) := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | of T c =>
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | tmul a b =>
      change comp x y W _ (cauchyMap x y e (pair x y V T a b)) = _
      rw [cauchyMap_pair]
      by_cases h : T = S
      · subst h
        rw [comp_pair_self]
        change _ = TensorProduct.map _ _ (comp x y V T (pair x y V T a b))
        rw [comp_pair_self, TensorProduct.map_tmul]
      · have h' : T.map (e : V →ₗ[F] W) ≠ S.map (e : V →ₗ[F] W) := fun hh =>
          h (Submodule.map_injective_of_injective e.injective hh)
        rw [comp_pair_ne x y W h'.symm]
        change _ = TensorProduct.map _ _ (comp x y V S (pair x y V T a b))
        rw [comp_pair_ne x y V (Ne.symm h)]
        simp

/-- Component of a flattened left-associated Cauchy product. -/
def compL (x y z : GLSpecies F k) (V : FGModuleCat.{0} F) (p : LeftFlagIndex V) :
    cauchyObj (cauchy x y) z V →ₗ[k] LeftFlagValue x y z V p :=
  DirectSum.component k (LeftFlagIndex V) (LeftFlagValue x y z V) p ∘ₗ
    (flattenLeft x y z V).toLinearMap

/-- Component of a flattened right-associated Cauchy product. -/
def compR (x y z : GLSpecies F k) (V : FGModuleCat.{0} F) (p : RightFlagIndex V) :
    cauchyObj x (cauchy y z) V →ₗ[k] RightFlagValue x y z V p :=
  DirectSum.component k (RightFlagIndex V) (RightFlagValue x y z V) p ∘ₗ
    (flattenRight x y z V).toLinearMap

theorem component_sumCongr {I J : Type} {M : I → Type} {N : J → Type}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)]
    [∀ j, AddCommMonoid (N j)] [∀ j, Module k (N j)]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (f : ∀ i, M i ≃ₗ[k] N (e i))
    (d : ⨁ i, M i) (i : I) :
    DirectSum.component k J N (e i) (sumCongr e f d) = f i (DirectSum.component k I M i d) := by
  induction d using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | of j c =>
    rw [show DirectSum.of M j c = DirectSum.lof k I M j c from rfl, sumCongr_lof]
    by_cases h : j = i
    · subst h
      simp [DirectSum.component.of]
    · have h' : e j ≠ e i := fun hh => h (e.injective hh)
      simp [DirectSum.component.of, h, h']

/-- Components of the associator. -/
theorem compR_assocEquiv (x y z : GLSpecies F k) (V : FGModuleCat.{0} F)
    (p : LeftFlagIndex V) (w : cauchyObj (cauchy x y) z V) :
    compR x y z V (flagIndexEquiv V p) (assocEquiv x y z V w) =
      flagValueEquiv x y z V p (compL x y z V p w) := by
  unfold compR compL
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have : flattenRight x y z V (assocEquiv x y z V w) =
      sumCongr (flagIndexEquiv V) (flagValueEquiv x y z V) (flattenLeft x y z V w) := by
    simp [assocEquiv]
  rw [this]
  exact component_sumCongr (flagIndexEquiv V) (flagValueEquiv x y z V) _ p


theorem compL_pair_self (x y z : GLSpecies F k) (V : FGModuleCat.{0} F) (S : Submodule F V)
    (T : Submodule F S) (A : cauchyObj x y (sub S)) (c : z.ev (quo S)) :
    compL x y z V ⟨S, T⟩ (pair (cauchy x y) z V S A c) =
      (comp x y (sub S) T A) ⊗ₜ[k] c := by
  induction A using DirectSum.induction_on with
  | zero => simp [pair]
  | add a b ha hb =>
    have e : pair (cauchy x y) z V S (a + b) c =
        pair (cauchy x y) z V S a c + pair (cauchy x y) z V S b c := by
      simp [pair, TensorProduct.add_tmul]
    rw [e, map_add, ha, hb, map_add, TensorProduct.add_tmul]
  | of T' u =>
    induction u using TensorProduct.induction_on with
    | zero => simp [pair]
    | add a b ha hb =>
      have e : pair (cauchy x y) z V S (DirectSum.of _ T' (a + b)) c =
          pair (cauchy x y) z V S (DirectSum.of _ T' a) c +
            pair (cauchy x y) z V S (DirectSum.of _ T' b) c := by
        simp [pair, TensorProduct.add_tmul]
      rw [e, map_add, ha, hb, ← TensorProduct.add_tmul, ← map_add, ← map_add]
    | tmul a b =>
      change compL x y z V ⟨S, T⟩ (pair (cauchy x y) z V S (pair x y (sub S) T' a b) c) =
        comp x y (sub S) T (pair x y (sub S) T' a b) ⊗ₜ[k] c
      unfold compL
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, flattenLeft_pair]
      by_cases h : T' = T
      · subst h
        rw [comp_pair_self]
        simp [DirectSum.component.of]
      · rw [comp_pair_ne x y _ (Ne.symm h)]
        simp [DirectSum.component.of, h]

theorem compL_pair_ne (x y z : GLSpecies F k) (V : FGModuleCat.{0} F) {S S' : Submodule F V}
    (h : S' ≠ S) (T : Submodule F S) (A : cauchyObj x y (sub S')) (c : z.ev (quo S')) :
    compL x y z V ⟨S, T⟩ (pair (cauchy x y) z V S' A c) = 0 := by
  induction A using DirectSum.induction_on with
  | zero => simp [pair]
  | add a b ha hb =>
    have e : pair (cauchy x y) z V S' (a + b) c =
        pair (cauchy x y) z V S' a c + pair (cauchy x y) z V S' b c := by
      simp [pair, TensorProduct.add_tmul]
    rw [e, map_add, ha, hb, add_zero]
  | of T' u =>
    induction u using TensorProduct.induction_on with
    | zero => simp [pair]
    | add a b ha hb =>
      have e : pair (cauchy x y) z V S' (DirectSum.of _ T' (a + b)) c =
          pair (cauchy x y) z V S' (DirectSum.of _ T' a) c +
            pair (cauchy x y) z V S' (DirectSum.of _ T' b) c := by
        simp [pair, TensorProduct.add_tmul]
      rw [e, map_add, ha, hb, add_zero]
    | tmul a b =>
      change compL x y z V ⟨S, T⟩ (pair (cauchy x y) z V S' (pair x y (sub S') T' a b) c) = 0
      unfold compL
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, flattenLeft_pair]
      have : (⟨S', T'⟩ : LeftFlagIndex V) ≠ ⟨S, T⟩ := fun hh => h (congrArg Sigma.fst hh)
      simp [DirectSum.component.of, this]

theorem compR_pair_self (x y z : GLSpecies F k) (V : FGModuleCat.{0} F) (T : Submodule F V)
    (Q : Submodule F (V ⧸ T)) (a : x.ev (sub T)) (B : cauchyObj y z (quo T)) :
    compR x y z V ⟨T, Q⟩ (pair x (cauchy y z) V T a B) =
      a ⊗ₜ[k] (comp y z (quo T) Q B) := by
  induction B using DirectSum.induction_on with
  | zero => simp [pair]
  | add b c hb hc =>
    have e : pair x (cauchy y z) V T a (b + c) =
        pair x (cauchy y z) V T a b + pair x (cauchy y z) V T a c := by
      simp [pair, TensorProduct.tmul_add]
    rw [e, map_add, hb, hc, map_add, TensorProduct.tmul_add]
  | of Q' u =>
    induction u using TensorProduct.induction_on with
    | zero => simp [pair]
    | add b c hb hc =>
      have e : pair x (cauchy y z) V T a (DirectSum.of _ Q' (b + c)) =
          pair x (cauchy y z) V T a (DirectSum.of _ Q' b) +
            pair x (cauchy y z) V T a (DirectSum.of _ Q' c) := by
        simp [pair, TensorProduct.tmul_add]
      rw [e, map_add, hb, hc, ← TensorProduct.tmul_add, ← map_add, ← map_add]
    | tmul b c =>
      change compR x y z V ⟨T, Q⟩ (pair x (cauchy y z) V T a (pair y z (quo T) Q' b c)) =
        a ⊗ₜ[k] comp y z (quo T) Q (pair y z (quo T) Q' b c)
      unfold compR
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, flattenRight_pair]
      by_cases h : Q' = Q
      · subst h
        rw [comp_pair_self]
        simp [DirectSum.component.of]
      · rw [comp_pair_ne y z _ (Ne.symm h)]
        simp [DirectSum.component.of, h]

theorem compR_pair_ne (x y z : GLSpecies F k) (V : FGModuleCat.{0} F) {T T' : Submodule F V}
    (h : T' ≠ T) (Q : Submodule F (V ⧸ T)) (a : x.ev (sub T')) (B : cauchyObj y z (quo T')) :
    compR x y z V ⟨T, Q⟩ (pair x (cauchy y z) V T' a B) = 0 := by
  induction B using DirectSum.induction_on with
  | zero => simp [pair]
  | add b c hb hc =>
    have e : pair x (cauchy y z) V T' a (b + c) =
        pair x (cauchy y z) V T' a b + pair x (cauchy y z) V T' a c := by
      simp [pair, TensorProduct.tmul_add]
    rw [e, map_add, hb, hc, add_zero]
  | of Q' u =>
    induction u using TensorProduct.induction_on with
    | zero => simp [pair]
    | add b c hb hc =>
      have e : pair x (cauchy y z) V T' a (DirectSum.of _ Q' (b + c)) =
          pair x (cauchy y z) V T' a (DirectSum.of _ Q' b) +
            pair x (cauchy y z) V T' a (DirectSum.of _ Q' c) := by
        simp [pair, TensorProduct.tmul_add]
      rw [e, map_add, hb, hc, add_zero]
    | tmul b c =>
      change compR x y z V ⟨T, Q⟩ (pair x (cauchy y z) V T' a (pair y z (quo T') Q' b c)) = 0
      unfold compR
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, flattenRight_pair]
      have : (⟨T', Q'⟩ : RightFlagIndex V) ≠ ⟨T, Q⟩ := fun hh => h (congrArg Sigma.fst hh)
      simp [DirectSum.component.of, this]

end GLSpecies


theorem expSpecies_mapEquiv {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W) :
    (expSpecies (F := F) (k := k)).mapEquiv e = LinearMap.id := rfl

/-- The restriction maps of a bicomodule over `e`: components of the right coaction. -/
def Bicomod.resMap (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F) (S : Submodule F V) :
    M.X.ev V →ₗ[k] M.X.ev (sub S) :=
  (TensorProduct.rid k (M.X.ev (sub S))).toLinearMap ∘ₗ
    GLSpecies.comp M.X expSpecies V S ∘ₗ (M.coact.app ⟨V⟩).hom

/-- The projection maps of a bicomodule over `e`: components of the left coaction. -/
def Bicomod.projMap (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F) (S : Submodule F V) :
    M.X.ev V →ₗ[k] M.X.ev (quo S) :=
  (TensorProduct.lid k (M.X.ev (quo S))).toLinearMap ∘ₗ
    GLSpecies.comp expSpecies M.X V S ∘ₗ (M.coactL.app ⟨V⟩).hom

theorem rid_map_aux {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module k A] [Module k B]
    (f : A →ₗ[k] B) (t : A ⊗[k] k) :
    f (TensorProduct.rid k A t) = TensorProduct.rid k B (TensorProduct.map f LinearMap.id t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b => simp

theorem lid_map_aux {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module k A] [Module k B]
    (f : A →ₗ[k] B) (t : k ⊗[k] A) :
    f (TensorProduct.lid k A t) = TensorProduct.lid k B (TensorProduct.map LinearMap.id f t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b => simp

theorem Bicomod.resMap_natural (M : Bicomod (expComon F k)) {V W : FGModuleCat.{0} F}
    (e : V ≃ₗ[F] W) (S : Submodule F V) :
    M.X.mapEquiv (V := sub S) (W := sub (S.map (e : V →ₗ[F] W))) (e.submoduleMap S) ∘ₗ
        M.resMap V S =
      M.resMap W (S.map (e : V →ₗ[F] W)) ∘ₗ M.X.mapEquiv e := by
  apply LinearMap.ext
  intro z
  have h := DFunLike.congr_fun (GLSpecies.mapEquiv_naturality M.coact e) z
  simp only [LinearMap.comp_apply] at h
  have e1 : M.resMap V S z = (TensorProduct.rid k (M.X.ev (sub S)))
      (GLSpecies.comp M.X expSpecies V S ((M.coact.app ⟨V⟩).hom z)) := rfl
  have e2 : M.resMap W (S.map (e : V →ₗ[F] W)) (M.X.mapEquiv e z) =
      (TensorProduct.rid k (M.X.ev (sub (S.map (e : V →ₗ[F] W)))))
        (GLSpecies.comp M.X expSpecies W (S.map (e : V →ₗ[F] W))
          (GLSpecies.cauchyMap M.X expSpecies e ((M.coact.app ⟨V⟩).hom z))) := by
    change (TensorProduct.rid k (M.X.ev (sub (S.map (e : V →ₗ[F] W)))))
        (GLSpecies.comp M.X expSpecies W (S.map (e : V →ₗ[F] W))
          ((M.coact.app ⟨W⟩).hom (M.X.mapEquiv e z))) = _
    rw [h]
    rfl
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2]
  erw [GLSpecies.comp_cauchyMap]
  exact rid_map_aux _ _


theorem GLSpecies.eq_sum_comp (x y : GLSpecies F k) (V : FGModuleCat.{0} F)
    (u : GLSpecies.cauchyObj x y V) :
    u = ∑ S : Submodule F V, DirectSum.lof k (Submodule F V)
      (fun T => x.ev (sub T) ⊗[k] y.ev (quo T)) S (GLSpecies.comp x y V S u) := by
  conv_lhs => rw [← DirectSum.sum_univ_of u]
  rfl

theorem Bicomod.coact_eq (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F) (z : M.X.ev V) :
    (M.coact.app ⟨V⟩).hom z = ∑ S : Submodule F V,
      GLSpecies.pair M.X expSpecies V S (M.resMap V S z) (expOne (quo S)) := by
  have h := GLSpecies.eq_sum_comp M.X expSpecies V ((M.coact.app ⟨V⟩).hom z)
  refine h.trans (Finset.sum_congr rfl fun S _ => ?_)
  have : GLSpecies.comp M.X expSpecies V S ((M.coact.app ⟨V⟩).hom z) =
      (TensorProduct.rid k (M.X.ev (sub S))).symm (M.resMap V S z) := by
    exact (LinearEquiv.eq_symm_apply _).2 rfl
  rw [this, TensorProduct.rid_symm_apply]
  rfl

theorem Bicomod.coactL_eq (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F) (z : M.X.ev V) :
    (M.coactL.app ⟨V⟩).hom z = ∑ S : Submodule F V,
      GLSpecies.pair expSpecies M.X V S (expOne (sub S)) (M.projMap V S z) := by
  have h := GLSpecies.eq_sum_comp expSpecies M.X V ((M.coactL.app ⟨V⟩).hom z)
  refine h.trans (Finset.sum_congr rfl fun S _ => ?_)
  have : GLSpecies.comp expSpecies M.X V S ((M.coactL.app ⟨V⟩).hom z) =
      (TensorProduct.lid k (M.X.ev (quo S))).symm (M.projMap V S z) := by
    exact (LinearEquiv.eq_symm_apply _).2 rfl
  rw [this, TensorProduct.lid_symm_apply]
  rfl


theorem comp_comulElt (W : FGModuleCat.{0} F) (Q : Submodule F W) :
    GLSpecies.comp (expSpecies (F := F) (k := k)) expSpecies W Q (comulElt W) =
      (1 : k) ⊗ₜ[k] (1 : k) := by
  unfold comulElt
  rw [map_sum, Finset.sum_eq_single Q]
  · exact GLSpecies.comp_pair_self _ _ _ _ _ _
  · intro S _ hS
    exact GLSpecies.comp_pair_ne _ _ _ (Ne.symm hS) _ _
  · simp

theorem Bicomod.comp_coact (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F)
    (S : Submodule F V) (z : M.X.ev V) :
    GLSpecies.comp M.X expSpecies V S ((M.coact.app ⟨V⟩).hom z) =
      (M.resMap V S z) ⊗ₜ[k] (1 : k) := by
  have : GLSpecies.comp M.X expSpecies V S ((M.coact.app ⟨V⟩).hom z) =
      (TensorProduct.rid k (M.X.ev (sub S))).symm (M.resMap V S z) :=
    (LinearEquiv.eq_symm_apply _).2 rfl
  rw [this, TensorProduct.rid_symm_apply]

theorem Bicomod.res_res_raw (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F)
    (S1 : Submodule F V) (T1 : Submodule F S1) (z : M.X.ev V) :
    M.resMap V (GLSpecies.flagLower S1 T1) z =
      M.X.mapEquiv (S1.equivSubtypeMap T1) (M.resMap (sub S1) T1 (M.resMap V S1 z)) := by
  have hz := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (NatTrans.congr_app M.coact_assoc ⟨V⟩)) z
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  change GLSpecies.cauchyHomMap (𝟙 M.X) expComul V ((M.coact.app ⟨V⟩).hom z) =
    GLSpecies.assocEquiv M.X expSpecies expSpecies V
      (GLSpecies.cauchyHomMap M.coact (𝟙 _) V ((M.coact.app ⟨V⟩).hom z)) at hz
  have hLHS : GLSpecies.cauchyHomMap (𝟙 M.X) expComul V ((M.coact.app ⟨V⟩).hom z) =
      ∑ S : Submodule F V, GLSpecies.pair M.X (GLSpecies.cauchy expSpecies expSpecies) V S
        (M.resMap V S z) (comulElt (quo S)) := by
    rw [M.coact_eq, map_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [GLSpecies.cauchyHomMap_pair, expComul_one]
    rfl
  have hRHS : GLSpecies.compL M.X expSpecies expSpecies V ⟨S1, T1⟩
      (GLSpecies.cauchyHomMap M.coact (𝟙 _) V ((M.coact.app ⟨V⟩).hom z)) =
      ((M.resMap (sub S1) T1 (M.resMap V S1 z)) ⊗ₜ[k] (1 : k)) ⊗ₜ[k] (1 : k) := by
    rw [M.coact_eq, map_sum]
    erw [map_sum]
    rw [Finset.sum_eq_single S1]
    · rw [GLSpecies.cauchyHomMap_pair]
      change GLSpecies.compL M.X expSpecies expSpecies V ⟨S1, T1⟩
        (GLSpecies.pair (GLSpecies.cauchy M.X expSpecies) expSpecies V S1
          ((M.coact.app ⟨sub S1⟩).hom (M.resMap V S1 z)) (expOne _)) = _
      erw [GLSpecies.compL_pair_self]
      rw [M.comp_coact]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compL_pair_ne _ _ _ _ hS _ _ _
    · simp
  obtain ⟨u, hu⟩ : ∃ u : GLSpecies.cauchyObj M.X expSpecies V,
      u = (M.coact.app ⟨V⟩).hom z := ⟨_, rfl⟩
  rw [← hu] at hz hLHS hRHS
  have e1 := GLSpecies.compR_assocEquiv M.X expSpecies expSpecies V ⟨S1, T1⟩
    (GLSpecies.cauchyHomMap M.coact (𝟙 expSpecies) V u)
  rw [hRHS, ← hz, hLHS] at e1
  have hL : GLSpecies.compR M.X expSpecies expSpecies V (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩)
      (∑ S : Submodule F V, GLSpecies.pair M.X (GLSpecies.cauchy expSpecies expSpecies) V S
        (M.resMap V S z) (comulElt (quo S))) =
      (M.resMap V (GLSpecies.flagLower S1 T1) z) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] (1 : k)) := by
    rw [map_sum, Finset.sum_eq_single (GLSpecies.flagLower S1 T1)]
    · refine (GLSpecies.compR_pair_self M.X expSpecies expSpecies V (GLSpecies.flagLower S1 T1)
        (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 _ _).trans ?_
      exact congrArg _ (comp_comulElt _ _)
    · intro S _ hS
      exact GLSpecies.compR_pair_ne M.X expSpecies expSpecies V
        (T := GLSpecies.flagLower S1 T1) hS (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 _ _
    · simp
  rw [hL] at e1
  have hr : (GLSpecies.flagValueEquiv M.X expSpecies expSpecies V ⟨S1, T1⟩)
      ((M.resMap (sub S1) T1 (M.resMap V S1 z) ⊗ₜ[k] (1 : k)) ⊗ₜ[k] (1 : k)) =
      (M.X.mapEquiv (S1.equivSubtypeMap T1) (M.resMap (sub S1) T1 (M.resMap V S1 z))) ⊗ₜ[k]
        ((1 : k) ⊗ₜ[k] (1 : k)) := by
    simp only [GLSpecies.flagValueEquiv, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
      TensorProduct.congr_tmul]
    rfl
  have e2 : (M.resMap V (GLSpecies.flagLower S1 T1) z) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] (1 : k)) =
      (M.X.mapEquiv (S1.equivSubtypeMap T1) (M.resMap (sub S1) T1 (M.resMap V S1 z))) ⊗ₜ[k]
        ((1 : k) ⊗ₜ[k] (1 : k)) := e1.trans hr
  have hΨ := congrArg (fun t => (TensorProduct.rid k _).toLinearMap
    (TensorProduct.map LinearMap.id (LinearMap.mul' k k) t)) e2
  simpa using hΨ


theorem Bicomod.res_res_ax (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F)
    (T S : Submodule F V) (h : T ≤ S) :
    M.X.mapEquiv (V := sub (V := sub S) (T.comap S.subtype)) (W := sub T)
        (Submodule.comapSubtypeEquivOfLe h) ∘ₗ
      M.resMap (sub S) (T.comap S.subtype) ∘ₗ M.resMap V S = M.resMap V T := by
  apply LinearMap.ext
  intro z
  have hT : GLSpecies.flagLower S (T.comap S.subtype) = T := by
    rw [GLSpecies.flagLower, Submodule.map_comap_subtype]; exact inf_eq_right.2 h
  have key : ∀ T' (hT' : GLSpecies.flagLower S (T.comap S.subtype) = T'),
      M.resMap V T' z = M.X.mapEquiv ((S.equivSubtypeMap (T.comap S.subtype)).trans
        (LinearEquiv.ofEq _ _ hT')) (M.resMap (sub S) (T.comap S.subtype) (M.resMap V S z)) := by
    intro T' hT'
    subst hT'
    have : (S.equivSubtypeMap (T.comap S.subtype)).trans (LinearEquiv.ofEq _ _ rfl) =
        S.equivSubtypeMap (T.comap S.subtype) := LinearEquiv.ext fun _ => rfl
    rw [this]
    exact M.res_res_raw V S _ z
  have hiso : (S.equivSubtypeMap (T.comap S.subtype)).trans (LinearEquiv.ofEq _ _ hT) =
      Submodule.comapSubtypeEquivOfLe h := LinearEquiv.ext fun x => Subtype.ext rfl
  rw [LinearMap.comp_apply, LinearMap.comp_apply, key T hT, hiso]


theorem Bicomod.projMap_natural (M : Bicomod (expComon F k)) {V W : FGModuleCat.{0} F}
    (e : V ≃ₗ[F] W) (S : Submodule F V) :
    M.X.mapEquiv (V := quo S) (W := quo (S.map (e : V →ₗ[F] W)))
        (Submodule.Quotient.equiv S _ e rfl) ∘ₗ M.projMap V S =
      M.projMap W (S.map (e : V →ₗ[F] W)) ∘ₗ M.X.mapEquiv e := by
  apply LinearMap.ext
  intro z
  have h := DFunLike.congr_fun (GLSpecies.mapEquiv_naturality M.coactL e) z
  simp only [LinearMap.comp_apply] at h
  have e1 : M.projMap V S z = (TensorProduct.lid k (M.X.ev (quo S)))
      (GLSpecies.comp expSpecies M.X V S ((M.coactL.app ⟨V⟩).hom z)) := rfl
  have e2 : M.projMap W (S.map (e : V →ₗ[F] W)) (M.X.mapEquiv e z) =
      (TensorProduct.lid k (M.X.ev (quo (S.map (e : V →ₗ[F] W)))))
        (GLSpecies.comp expSpecies M.X W (S.map (e : V →ₗ[F] W))
          (GLSpecies.cauchyMap expSpecies M.X e ((M.coactL.app ⟨V⟩).hom z))) := by
    change (TensorProduct.lid k (M.X.ev (quo (S.map (e : V →ₗ[F] W)))))
        (GLSpecies.comp expSpecies M.X W (S.map (e : V →ₗ[F] W))
          ((M.coactL.app ⟨W⟩).hom (M.X.mapEquiv e z))) = _
    rw [h]
    rfl
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2]
  erw [GLSpecies.comp_cauchyMap]
  exact lid_map_aux _ _

theorem Bicomod.comp_coactL (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F)
    (S : Submodule F V) (z : M.X.ev V) :
    GLSpecies.comp expSpecies M.X V S ((M.coactL.app ⟨V⟩).hom z) =
      (1 : k) ⊗ₜ[k] (M.projMap V S z) := by
  have : GLSpecies.comp expSpecies M.X V S ((M.coactL.app ⟨V⟩).hom z) =
      (TensorProduct.lid k (M.X.ev (quo S))).symm (M.projMap V S z) :=
    (LinearEquiv.eq_symm_apply _).2 rfl
  rw [this, TensorProduct.lid_symm_apply]

theorem GLSpecies.flagIndexEquiv_snd (V : FGModuleCat.{0} F) (S : Submodule F V)
    (T : Submodule F S) :
    (GLSpecies.flagIndexEquiv V ⟨S, T⟩).2 = S.map (GLSpecies.flagLower S T).mkQ := by
  set y := (GLSpecies.flagIndexEquiv V ⟨S, T⟩).2 with hy
  have h1 : Submodule.comap (GLSpecies.flagLower S T).mkQ y = S := by
    have := congrArg Subtype.val
      (((GLSpecies.flagLower S T).comapMkQRelIso).apply_symm_apply
        ⟨S, (S.mapIic T).property⟩)
    exact this
  exact (Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _) y).symm.trans
    (congrArg (Submodule.map _) h1)


theorem Bicomod.proj_proj_raw (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F)
    (S1 : Submodule F V) (T1 : Submodule F S1) (z : M.X.ev V) :
    M.X.mapEquiv (GLSpecies.flagUpperEquiv S1 T1) (M.projMap V S1 z) =
      M.projMap (quo (GLSpecies.flagLower S1 T1)) (S1.map (GLSpecies.flagLower S1 T1).mkQ)
        (M.projMap V (GLSpecies.flagLower S1 T1) z) := by
  have hz := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (NatTrans.congr_app M.coactL_assoc ⟨V⟩)) z
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  change GLSpecies.assocEquiv expSpecies expSpecies M.X V
      (GLSpecies.cauchyHomMap expComul (𝟙 M.X) V ((M.coactL.app ⟨V⟩).hom z)) =
    GLSpecies.cauchyHomMap (𝟙 _) M.coactL V ((M.coactL.app ⟨V⟩).hom z) at hz
  obtain ⟨u, hu⟩ : ∃ u : GLSpecies.cauchyObj expSpecies M.X V,
      u = (M.coactL.app ⟨V⟩).hom z := ⟨_, rfl⟩
  rw [← hu] at hz
  have hLHS : GLSpecies.compL expSpecies expSpecies M.X V ⟨S1, T1⟩
      (GLSpecies.cauchyHomMap expComul (𝟙 M.X) V u) =
      ((1 : k) ⊗ₜ[k] (1 : k)) ⊗ₜ[k] (M.projMap V S1 z) := by
    rw [hu, M.coactL_eq, map_sum]
    erw [map_sum]
    rw [Finset.sum_eq_single S1]
    · rw [GLSpecies.cauchyHomMap_pair]
      change GLSpecies.compL expSpecies expSpecies M.X V ⟨S1, T1⟩
        (GLSpecies.pair (GLSpecies.cauchy expSpecies expSpecies) M.X V S1
          (((expComul (F := F) (k := k)).app ⟨sub S1⟩).hom (expOne _)) (M.projMap V S1 z)) = _
      erw [GLSpecies.compL_pair_self, expComul_one, comp_comulElt]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compL_pair_ne _ _ _ _ hS _ _ _
    · simp
  have e1 := GLSpecies.compR_assocEquiv expSpecies expSpecies M.X V ⟨S1, T1⟩
    (GLSpecies.cauchyHomMap expComul (𝟙 M.X) V u)
  rw [hLHS] at e1
  have hRHS : GLSpecies.compR expSpecies expSpecies M.X V (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩)
      (GLSpecies.cauchyHomMap (𝟙 _) M.coactL V u) =
      (1 : k) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] (M.projMap (quo (GLSpecies.flagLower S1 T1))
        (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 (M.projMap V (GLSpecies.flagLower S1 T1) z))) := by
    rw [hu, M.coactL_eq, map_sum]
    erw [map_sum]
    rw [Finset.sum_eq_single (GLSpecies.flagLower S1 T1)]
    · rw [GLSpecies.cauchyHomMap_pair]
      refine (GLSpecies.compR_pair_self expSpecies expSpecies M.X V (GLSpecies.flagLower S1 T1)
        (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 _ _).trans ?_
      erw [M.comp_coactL]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compR_pair_ne expSpecies expSpecies M.X V
        (T := GLSpecies.flagLower S1 T1) hS (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 _ _
    · simp
  have e2 : (GLSpecies.flagValueEquiv expSpecies expSpecies M.X V ⟨S1, T1⟩)
      (((1 : k) ⊗ₜ[k] (1 : k)) ⊗ₜ[k] (M.projMap V S1 z)) =
      (1 : k) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] (M.projMap (quo (GLSpecies.flagLower S1 T1))
        (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 (M.projMap V (GLSpecies.flagLower S1 T1) z))) :=
    e1.symm.trans ((congrArg (GLSpecies.compR expSpecies expSpecies M.X V
      (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩)) hz).trans hRHS)
  have hr : (GLSpecies.flagValueEquiv expSpecies expSpecies M.X V ⟨S1, T1⟩)
      (((1 : k) ⊗ₜ[k] (1 : k)) ⊗ₜ[k] (M.projMap V S1 z)) =
      (1 : k) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] (M.X.mapEquiv (GLSpecies.flagUpperEquiv S1 T1)
        (M.projMap V S1 z))) := by
    simp only [GLSpecies.flagValueEquiv, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
      TensorProduct.congr_tmul]
    rfl
  have e3 : (1 : k) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] (M.X.mapEquiv (GLSpecies.flagUpperEquiv S1 T1)
        (M.projMap V S1 z))) =
      (1 : k) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] (M.projMap (quo (GLSpecies.flagLower S1 T1))
        (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 (M.projMap V (GLSpecies.flagLower S1 T1) z))) :=
    hr.symm.trans e2
  have e4 := congrArg (fun t => TensorProduct.lid k _ (TensorProduct.lid k _ t)) e3
  simp only [TensorProduct.lid_tmul, one_smul] at e4
  exact e4


theorem Bicomod.proj_proj_ax (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F)
    (T S : Submodule F V) (h : T ≤ S) :
    M.X.mapEquiv (V := quo (V := quo T) (S.map T.mkQ)) (W := quo S)
        (Submodule.quotientQuotientEquivQuotient T S h) ∘ₗ
      M.projMap (quo T) (S.map T.mkQ) ∘ₗ M.projMap V T = M.projMap V S := by
  apply LinearMap.ext
  intro z
  have hT : GLSpecies.flagLower S (T.comap S.subtype) = T := by
    rw [GLSpecies.flagLower, Submodule.map_comap_subtype]; exact inf_eq_right.2 h
  have key : ∀ T' (hT' : GLSpecies.flagLower S (T.comap S.subtype) = T') (h' : T' ≤ S),
      M.X.mapEquiv (V := quo (V := quo T') (S.map T'.mkQ)) (W := quo S)
        (Submodule.quotientQuotientEquivQuotient T' S h')
        (M.projMap (quo T') (S.map T'.mkQ) (M.projMap V T' z)) = M.projMap V S z := by
    intro T' hT' h'
    subst hT'
    have hraw := M.proj_proj_raw V S (T.comap S.subtype) z
    rw [← hraw]
    exact DFunLike.congr_fun (GLSpecies.mapEquiv_comp_symm M.X
      (V := quo (V := quo (GLSpecies.flagLower S (T.comap S.subtype)))
        (S.map (GLSpecies.flagLower S (T.comap S.subtype)).mkQ)) (W := quo S)
      (Submodule.quotientQuotientEquivQuotient (GLSpecies.flagLower S (T.comap S.subtype)) S h')) _
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact key T hT h


theorem Bicomod.proj_res_raw (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F)
    (S1 : Submodule F V) (T1 : Submodule F S1) (z : M.X.ev V) :
    M.X.mapEquiv (GLSpecies.flagMiddleEquiv S1 T1) (M.projMap (sub S1) T1 (M.resMap V S1 z)) =
      M.resMap (quo (GLSpecies.flagLower S1 T1)) (S1.map (GLSpecies.flagLower S1 T1).mkQ)
        (M.projMap V (GLSpecies.flagLower S1 T1) z) := by
  have hz := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (NatTrans.congr_app M.compat ⟨V⟩)) z
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  change GLSpecies.cauchyHomMap (𝟙 _) M.coact V ((M.coactL.app ⟨V⟩).hom z) =
    GLSpecies.assocEquiv expSpecies M.X expSpecies V
      (GLSpecies.cauchyHomMap M.coactL (𝟙 _) V ((M.coact.app ⟨V⟩).hom z)) at hz
  obtain ⟨u, hu⟩ : ∃ u : GLSpecies.cauchyObj M.X expSpecies V,
      u = (M.coact.app ⟨V⟩).hom z := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : GLSpecies.cauchyObj expSpecies M.X V,
      w = (M.coactL.app ⟨V⟩).hom z := ⟨_, rfl⟩
  rw [← hu, ← hw] at hz
  have hL : GLSpecies.compL expSpecies M.X expSpecies V ⟨S1, T1⟩
      (GLSpecies.cauchyHomMap M.coactL (𝟙 _) V u) =
      ((1 : k) ⊗ₜ[k] (M.projMap (sub S1) T1 (M.resMap V S1 z))) ⊗ₜ[k] (1 : k) := by
    rw [hu, M.coact_eq, map_sum]
    erw [map_sum]
    rw [Finset.sum_eq_single S1]
    · rw [GLSpecies.cauchyHomMap_pair]
      change GLSpecies.compL expSpecies M.X expSpecies V ⟨S1, T1⟩
        (GLSpecies.pair (GLSpecies.cauchy expSpecies M.X) expSpecies V S1
          ((M.coactL.app ⟨sub S1⟩).hom (M.resMap V S1 z)) (expOne _)) = _
      erw [GLSpecies.compL_pair_self, M.comp_coactL]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compL_pair_ne _ _ _ _ hS _ _ _
    · simp
  have hR : GLSpecies.compR expSpecies M.X expSpecies V (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩)
      (GLSpecies.cauchyHomMap (𝟙 _) M.coact V w) =
      (1 : k) ⊗ₜ[k] ((M.resMap (quo (GLSpecies.flagLower S1 T1))
        (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 (M.projMap V (GLSpecies.flagLower S1 T1) z))
          ⊗ₜ[k] (1 : k)) := by
    rw [hw, M.coactL_eq, map_sum]
    erw [map_sum]
    rw [Finset.sum_eq_single (GLSpecies.flagLower S1 T1)]
    · rw [GLSpecies.cauchyHomMap_pair]
      refine (GLSpecies.compR_pair_self expSpecies M.X expSpecies V (GLSpecies.flagLower S1 T1)
        (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 _ _).trans ?_
      erw [M.comp_coact]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compR_pair_ne expSpecies M.X expSpecies V
        (T := GLSpecies.flagLower S1 T1) hS (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 _ _
    · simp
  have e1 := GLSpecies.compR_assocEquiv expSpecies M.X expSpecies V ⟨S1, T1⟩
    (GLSpecies.cauchyHomMap M.coactL (𝟙 _) V u)
  rw [hL] at e1
  have e2 : (GLSpecies.flagValueEquiv expSpecies M.X expSpecies V ⟨S1, T1⟩)
      (((1 : k) ⊗ₜ[k] (M.projMap (sub S1) T1 (M.resMap V S1 z))) ⊗ₜ[k] (1 : k)) =
      (1 : k) ⊗ₜ[k] ((M.resMap (quo (GLSpecies.flagLower S1 T1))
        (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 (M.projMap V (GLSpecies.flagLower S1 T1) z))
          ⊗ₜ[k] (1 : k)) :=
    e1.symm.trans ((congrArg (GLSpecies.compR expSpecies M.X expSpecies V
      (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩)) hz.symm).trans hR)
  have hr : (GLSpecies.flagValueEquiv expSpecies M.X expSpecies V ⟨S1, T1⟩)
      (((1 : k) ⊗ₜ[k] (M.projMap (sub S1) T1 (M.resMap V S1 z))) ⊗ₜ[k] (1 : k)) =
      (1 : k) ⊗ₜ[k] ((M.X.mapEquiv (GLSpecies.flagMiddleEquiv S1 T1)
        (M.projMap (sub S1) T1 (M.resMap V S1 z))) ⊗ₜ[k] (1 : k)) := by
    simp only [GLSpecies.flagValueEquiv, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
      TensorProduct.congr_tmul]
    rfl
  have e3 : (1 : k) ⊗ₜ[k] ((M.X.mapEquiv (GLSpecies.flagMiddleEquiv S1 T1)
        (M.projMap (sub S1) T1 (M.resMap V S1 z))) ⊗ₜ[k] (1 : k)) =
      (1 : k) ⊗ₜ[k] ((M.resMap (quo (GLSpecies.flagLower S1 T1))
        (GLSpecies.flagIndexEquiv V ⟨S1, T1⟩).2 (M.projMap V (GLSpecies.flagLower S1 T1) z))
          ⊗ₜ[k] (1 : k)) := hr.symm.trans e2
  have e4 := congrArg (fun t => TensorProduct.rid k _ (TensorProduct.lid k _ t)) e3
  simp only [TensorProduct.lid_tmul, TensorProduct.rid_tmul, one_smul] at e4
  exact e4


theorem Bicomod.proj_res_ax (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F)
    (T S : Submodule F V) (h : T ≤ S) :
    M.X.mapEquiv (V := quo (V := sub S) (T.comap S.subtype))
        (W := sub (V := quo T) (S.map T.mkQ)) (subQuotIso T S) ∘ₗ
      M.projMap (sub S) (T.comap S.subtype) ∘ₗ M.resMap V S =
    M.resMap (quo T) (S.map T.mkQ) ∘ₗ M.projMap V T := by
  apply LinearMap.ext
  intro z
  have hT : GLSpecies.flagLower S (T.comap S.subtype) = T := by
    rw [GLSpecies.flagLower, Submodule.map_comap_subtype]; exact inf_eq_right.2 h
  have key : ∀ T' (hT' : GLSpecies.flagLower S (T.comap S.subtype) = T')
      (e : (↥S ⧸ T.comap S.subtype) ≃ₗ[F] ↥(S.map T'.mkQ))
      (he : ∀ s : S, ((e (Submodule.Quotient.mk s) : S.map T'.mkQ) : ↑V ⧸ T') = T'.mkQ s),
      M.X.mapEquiv (V := quo (V := sub S) (T.comap S.subtype))
        (W := sub (V := quo T') (S.map T'.mkQ)) e
        (M.projMap (sub S) (T.comap S.subtype) (M.resMap V S z)) =
      M.resMap (quo T') (S.map T'.mkQ) (M.projMap V T' z) := by
    intro T' hT' e he
    subst hT'
    have : e = GLSpecies.flagMiddleEquiv S (T.comap S.subtype) := by
      apply LinearEquiv.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H s => exact Subtype.ext (by rw [he s]; rfl)
    rw [this]
    exact M.proj_res_raw V S _ z
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact key T hT (subQuotIso T S) (fun s => rfl)


theorem finrank_quo_top_eq (V : FGModuleCat.{0} F) :
    finrank F (quo (⊤ : Submodule F V)) = 0 := by
  exact finrank_zero_of_subsingleton

theorem Bicomod.res_top_ax (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F) :
    M.resMap V ⊤ = M.X.mapEquiv (V := V) (W := sub (⊤ : Submodule F V))
      Submodule.topEquiv.symm := by
  apply LinearMap.ext
  intro z
  have hz := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (NatTrans.congr_app M.coact_counit ⟨V⟩)) z
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  change GLSpecies.cauchyHomMap (𝟙 M.X) expCounit V ((M.coact.app ⟨V⟩).hom z) =
    GLSpecies.rightUnitInv M.X V z at hz
  have h1 := congrArg (GLSpecies.comp M.X GLSpecies.unit V ⊤) hz
  have hL : GLSpecies.comp M.X GLSpecies.unit V ⊤
      (GLSpecies.cauchyHomMap (𝟙 M.X) expCounit V ((M.coact.app ⟨V⟩).hom z)) =
      (M.resMap V ⊤ z) ⊗ₜ[k] (GLSpecies.unitOne (quo (⊤ : Submodule F V)) (finrank_quo_top_eq V)) := by
    rw [M.coact_eq]
    erw [map_sum, map_sum]
    rw [Finset.sum_eq_single ⊤]
    · rw [GLSpecies.cauchyHomMap_pair]
      refine (GLSpecies.comp_pair_self _ _ _ _ _ _).trans ?_
      congr 1
      apply Subtype.ext
      rw [expCounit_val, if_pos (finrank_quo_top_eq V)]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.comp_pair_ne _ _ _ hS.symm _ _
    · simp
  have hR : GLSpecies.comp M.X GLSpecies.unit V ⊤ (GLSpecies.rightUnitInv M.X V z) =
      (M.X.mapEquiv (GLSpecies.subTopEquiv (⊤ : Submodule F V) rfl).symm z) ⊗ₜ[k]
        (GLSpecies.unitOne (quo (⊤ : Submodule F V)) (finrank_quo_top_eq V)) := by
    unfold GLSpecies.rightUnitInv
    simp only [LinearMap.comp_apply]
    exact GLSpecies.comp_pair_self _ _ _ _ _ _
  rw [hL, hR] at h1
  have h2 := congrArg (fun t => (TensorProduct.rid k _).toLinearMap
    (TensorProduct.map LinearMap.id (Submodule.subtype _) t)) h1
  have hsub : (GLSpecies.subTopEquiv (⊤ : Submodule F V) rfl).symm =
      Submodule.topEquiv.symm := LinearEquiv.ext fun _ => rfl
  rw [hsub] at h2
  simpa [GLSpecies.unitOne] using h2


theorem Bicomod.proj_bot_ax (M : Bicomod (expComon F k)) (V : FGModuleCat.{0} F) :
    M.projMap V ⊥ = M.X.mapEquiv (V := V) (W := quo (⊥ : Submodule F V))
      (Submodule.quotEquivOfEqBot ⊥ rfl).symm := by
  apply LinearMap.ext
  intro z
  have hz := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (NatTrans.congr_app M.counit_coactL ⟨V⟩)) z
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  change GLSpecies.cauchyHomMap expCounit (𝟙 M.X) V ((M.coactL.app ⟨V⟩).hom z) =
    GLSpecies.leftUnitInv M.X V z at hz
  have h1 := congrArg (GLSpecies.comp GLSpecies.unit M.X V ⊥) hz
  have hL : GLSpecies.comp GLSpecies.unit M.X V ⊥
      (GLSpecies.cauchyHomMap expCounit (𝟙 M.X) V ((M.coactL.app ⟨V⟩).hom z)) =
      (GLSpecies.unitOne (sub (⊥ : Submodule F V)) (by simp)) ⊗ₜ[k] (M.projMap V ⊥ z) := by
    rw [M.coactL_eq]
    erw [map_sum, map_sum]
    rw [Finset.sum_eq_single ⊥]
    · rw [GLSpecies.cauchyHomMap_pair]
      refine (GLSpecies.comp_pair_self _ _ _ _ _ _).trans ?_
      congr 1
      apply Subtype.ext
      rw [expCounit_val, if_pos (by simp)]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.comp_pair_ne _ _ _ hS.symm _ _
    · simp
  have hR : GLSpecies.comp GLSpecies.unit M.X V ⊥ (GLSpecies.leftUnitInv M.X V z) =
      (GLSpecies.unitOne (sub (⊥ : Submodule F V)) (by simp)) ⊗ₜ[k]
        (M.X.mapEquiv (Submodule.quotEquivOfEqBot (⊥ : Submodule F V) rfl).symm z) := by
    unfold GLSpecies.leftUnitInv
    simp only [LinearMap.comp_apply]
    exact GLSpecies.comp_pair_self _ _ _ _ _ _
  rw [hL, hR] at h1
  have h2 := congrArg (fun t => (TensorProduct.lid k _).toLinearMap
    (TensorProduct.map (Submodule.subtype _) LinearMap.id t)) h1
  simpa [GLSpecies.unitOne] using h2


/-- The forward direction of the correspondence: coordinates of a bicomodule over `e`. -/
def Bicomod.toE (M : Bicomod (expComon F k)) : EBicomod F k where
  X := M.X
  res := M.resMap
  proj := M.projMap
  res_natural := fun e S => M.resMap_natural e S
  proj_natural := fun e S => M.projMap_natural e S
  proj_proj := fun V T S h => M.proj_proj_ax V T S h
  res_res := fun V T S h => M.res_res_ax V T S h
  proj_bot := fun V => M.proj_bot_ax V
  res_top := fun V => M.res_top_ax V
  proj_res := fun V T S h => M.proj_res_ax V T S h

end MartinPhd

end
end Equiv

section EquivBack

/-
Formalization of F. D. Martin, *Aspectos homológicas de la teoría de especies*.

# Backward direction: from coordinates to a bicomodule over `e`

Given `E : EBicomod`, the coactions are `z ↦ ∑_S pair S (res_S z) 1` and
`z ↦ ∑_S pair S 1 (proj_S z)`.
-/

open scoped BigOperators TensorProduct DirectSum
open CategoryTheory Module MonoidalCategory

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] {k : Type} [Field k]

namespace GLSpecies

theorem ext_comp {x y : GLSpecies F k} {V : FGModuleCat.{0} F} {u u' : cauchyObj x y V}
    (h : ∀ S, comp x y V S u = comp x y V S u') : u = u' := by
  apply DirectSum.ext
  exact h

theorem ext_compR {x y z : GLSpecies F k} {V : FGModuleCat.{0} F}
    {w w' : cauchyObj x (cauchy y z) V}
    (h : ∀ p, compR x y z V p w = compR x y z V p w') : w = w' := by
  apply (flattenRight x y z V).injective
  apply DirectSum.ext
  exact h

end GLSpecies

/-- The right coaction in coordinates: `z ↦ ∑_S z|_S ⊗ e_{V/S}`. -/
def EBicomod.coactApp (E : EBicomod F k) (V : FGModuleCat.{0} F) :
    E.X.ev V →ₗ[k] GLSpecies.cauchyObj E.X expSpecies V :=
  ∑ S : Submodule F V, (DirectSum.lof k (Submodule F V)
      (fun T => E.X.ev (sub T) ⊗[k] expSpecies.ev (quo T)) S) ∘ₗ
    (TensorProduct.rid k (E.X.ev (sub S))).symm.toLinearMap ∘ₗ E.res V S

theorem EBicomod.comp_coactApp (E : EBicomod F k) (V : FGModuleCat.{0} F) (S : Submodule F V)
    (z : E.X.ev V) :
    GLSpecies.comp E.X expSpecies V S (E.coactApp V z) = (E.res V S z) ⊗ₜ[k] (1 : k) := by
  unfold EBicomod.coactApp
  rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single S]
  · simp [GLSpecies.comp, DirectSum.component.of]
    rfl
  · intro T _ hT
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact GLSpecies.comp_pair_ne _ _ _ (Ne.symm hT) _ _
  · simp


namespace GLSpecies

theorem comp_cauchyHomMap {x x' y y' : GLSpecies F k} (f : x ⟶ x') (g : y ⟶ y')
    (V : FGModuleCat.{0} F) (S : Submodule F V) (u : cauchyObj x y V) :
    comp x' y' V S (cauchyHomMap f g V u) =
      TensorProduct.map (f.app ⟨sub S⟩).hom (g.app ⟨quo S⟩).hom (comp x y V S u) := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | of T c =>
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | tmul a b =>
      change comp x' y' V S (cauchyHomMap f g V (pair x y V T a b)) =
        TensorProduct.map _ _ (comp x y V S (pair x y V T a b))
      rw [cauchyHomMap_pair]
      by_cases h : T = S
      · subst h
        rw [comp_pair_self, comp_pair_self, TensorProduct.map_tmul]
      · rw [comp_pair_ne _ _ _ (Ne.symm h), comp_pair_ne _ _ _ (Ne.symm h)]
        simp

end GLSpecies

/-- The left coaction in coordinates: `z ↦ ∑_S e_S ⊗ z|_{V/S}`. -/
def EBicomod.coactLApp (E : EBicomod F k) (V : FGModuleCat.{0} F) :
    E.X.ev V →ₗ[k] GLSpecies.cauchyObj expSpecies E.X V :=
  ∑ S : Submodule F V, (DirectSum.lof k (Submodule F V)
      (fun T => expSpecies.ev (sub T) ⊗[k] E.X.ev (quo T)) S) ∘ₗ
    (TensorProduct.lid k (E.X.ev (quo S))).symm.toLinearMap ∘ₗ E.proj V S

theorem EBicomod.comp_coactLApp (E : EBicomod F k) (V : FGModuleCat.{0} F) (S : Submodule F V)
    (z : E.X.ev V) :
    GLSpecies.comp expSpecies E.X V S (E.coactLApp V z) = (1 : k) ⊗ₜ[k] (E.proj V S z) := by
  unfold EBicomod.coactLApp
  rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single S]
  · simp [GLSpecies.comp]
    rfl
  · intro T _ hT
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact GLSpecies.comp_pair_ne _ _ _ (Ne.symm hT) _ _
  · simp

theorem EBicomod.coactApp_natural (E : EBicomod F k) {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W)
    (z : E.X.ev V) :
    GLSpecies.cauchyMap E.X expSpecies e (E.coactApp V z) = E.coactApp W (E.X.mapEquiv e z) := by
  apply GLSpecies.ext_comp
  intro T
  obtain ⟨S, rfl⟩ : ∃ S : Submodule F V, S.map (e : V →ₗ[F] W) = T :=
    ⟨T.comap (e : V →ₗ[F] W), Submodule.map_comap_eq_of_surjective e.surjective T⟩
  rw [GLSpecies.comp_cauchyMap, E.comp_coactApp, E.comp_coactApp]
  erw [TensorProduct.map_tmul]
  have h := DFunLike.congr_fun (E.res_natural e S) z
  simp only [LinearMap.comp_apply] at h
  rw [← h]
  rfl


theorem EBicomod.coactLApp_natural (E : EBicomod F k) {V W : FGModuleCat.{0} F} (e : V ≃ₗ[F] W)
    (z : E.X.ev V) :
    GLSpecies.cauchyMap expSpecies E.X e (E.coactLApp V z) =
      E.coactLApp W (E.X.mapEquiv e z) := by
  apply GLSpecies.ext_comp
  intro T
  obtain ⟨S, rfl⟩ : ∃ S : Submodule F V, S.map (e : V →ₗ[F] W) = T :=
    ⟨T.comap (e : V →ₗ[F] W), Submodule.map_comap_eq_of_surjective e.surjective T⟩
  rw [GLSpecies.comp_cauchyMap, E.comp_coactLApp, E.comp_coactLApp]
  erw [TensorProduct.map_tmul]
  have h := DFunLike.congr_fun (E.proj_natural e S) z
  simp only [LinearMap.comp_apply] at h
  rw [← h]
  rfl

/-- The right coaction `x ⟶ x ⊗ e`. -/
def EBicomod.coact (E : EBicomod F k) : E.X ⟶ E.X ⊗ (expComon F k).X where
  app V := ModuleCat.ofHom (E.coactApp V.of)
  naturality := by
    intro V W φ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (E.coactApp_natural (FGModuleCat.isoToLinearEquiv φ.iso) z).symm

/-- The left coaction `x ⟶ e ⊗ x`. -/
def EBicomod.coactL (E : EBicomod F k) : E.X ⟶ (expComon F k).X ⊗ E.X where
  app V := ModuleCat.ofHom (E.coactLApp V.of)
  naturality := by
    intro V W φ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (E.coactLApp_natural (FGModuleCat.isoToLinearEquiv φ.iso) z).symm


theorem finrank_quo_eq_zero_iff (V : FGModuleCat.{0} F) (S : Submodule F V) :
    finrank F (quo S) = 0 ↔ S = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    have hr := S.finrank_quotient_add_finrank
    change finrank F (↑V ⧸ S) = 0 at h
    omega
  · rintro rfl
    exact finrank_quo_top_eq V

theorem expCounit_expOne_ne (V : FGModuleCat.{0} F) (h : finrank F V ≠ 0) :
    ((expCounit (F := F) (k := k)).app ⟨V⟩).hom (expOne V) = 0 := by
  apply Subtype.ext
  rw [expCounit_val, if_neg h]
  rfl

theorem EBicomod.coact_counit' (E : EBicomod F k) :
    E.coact ≫ E.X ◁ ComonObj.counit (X := (expComon F k).X) = (ρ_ E.X).inv := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change GLSpecies.cauchyHomMap (𝟙 E.X) expCounit V.of (E.coactApp V.of z) =
    GLSpecies.rightUnitInv E.X V.of z
  apply GLSpecies.ext_comp
  intro S
  rw [GLSpecies.comp_cauchyHomMap, E.comp_coactApp]
  erw [TensorProduct.map_tmul]
  by_cases hS : S = ⊤
  · subst hS
    have hR : GLSpecies.comp E.X GLSpecies.unit V.of ⊤ (GLSpecies.rightUnitInv E.X V.of z) =
        (E.X.mapEquiv (GLSpecies.subTopEquiv (⊤ : Submodule F V.of) rfl).symm z) ⊗ₜ[k]
          (GLSpecies.unitOne (quo (⊤ : Submodule F V.of)) (finrank_quo_top_eq V.of)) := by
      unfold GLSpecies.rightUnitInv
      simp only [LinearMap.comp_apply]
      exact GLSpecies.comp_pair_self _ _ _ _ _ _
    erw [hR]
    have hres : E.res V.of ⊤ z = E.X.mapEquiv (GLSpecies.subTopEquiv (⊤ : Submodule F V.of) rfl).symm z := by
      rw [E.res_top]; rfl
    rw [hres]
    congr 1
    apply Subtype.ext
    erw [expCounit_val, if_pos (finrank_quo_top_eq V.of)]
    rfl
  · have hR : GLSpecies.comp E.X GLSpecies.unit V.of S (GLSpecies.rightUnitInv E.X V.of z) = 0 := by
      unfold GLSpecies.rightUnitInv
      simp only [LinearMap.comp_apply]
      exact GLSpecies.comp_pair_ne _ _ _ hS _ _
    erw [hR]
    have : ((expCounit (F := F) (k := k)).app ⟨quo S⟩).hom (expOne (quo S)) = 0 :=
      expCounit_expOne_ne _ (fun h => hS ((finrank_quo_eq_zero_iff _ _).1 h))
    erw [this]
    simp


theorem EBicomod.counit_coactL' (E : EBicomod F k) :
    E.coactL ≫ ComonObj.counit (X := (expComon F k).X) ▷ E.X = (λ_ E.X).inv := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change GLSpecies.cauchyHomMap expCounit (𝟙 E.X) V.of (E.coactLApp V.of z) =
    GLSpecies.leftUnitInv E.X V.of z
  apply GLSpecies.ext_comp
  intro S
  rw [GLSpecies.comp_cauchyHomMap, E.comp_coactLApp]
  erw [TensorProduct.map_tmul]
  by_cases hS : S = ⊥
  · subst hS
    have hR : GLSpecies.comp GLSpecies.unit E.X V.of ⊥ (GLSpecies.leftUnitInv E.X V.of z) =
        (GLSpecies.unitOne (sub (⊥ : Submodule F V.of)) (by simp)) ⊗ₜ[k]
          (E.X.mapEquiv (Submodule.quotEquivOfEqBot (⊥ : Submodule F V.of) rfl).symm z) := by
      unfold GLSpecies.leftUnitInv
      simp only [LinearMap.comp_apply]
      exact GLSpecies.comp_pair_self _ _ _ _ _ _
    erw [hR]
    have hproj : E.proj V.of ⊥ z =
        E.X.mapEquiv (Submodule.quotEquivOfEqBot (⊥ : Submodule F V.of) rfl).symm z := by
      rw [E.proj_bot]
    rw [hproj]
    congr 1
    apply Subtype.ext
    erw [expCounit_val, if_pos (by simp)]
    rfl
  · have hR : GLSpecies.comp GLSpecies.unit E.X V.of S (GLSpecies.leftUnitInv E.X V.of z) = 0 := by
      unfold GLSpecies.leftUnitInv
      simp only [LinearMap.comp_apply]
      exact GLSpecies.comp_pair_ne _ _ _ hS _ _
    erw [hR]
    have : ((expCounit (F := F) (k := k)).app ⟨sub S⟩).hom (expOne (sub S)) = 0 := by
      apply expCounit_expOne_ne
      intro h
      apply hS
      have h' : finrank F S = 0 := h
      simpa using h'
    erw [this]
    simp


theorem EBicomod.res_congr (E : EBicomod F k) {V : FGModuleCat.{0} F} {X Y : Submodule F V}
    (h : X = Y) (z : E.X.ev V) :
    E.res V Y z = E.X.mapEquiv (LinearEquiv.ofEq X Y h) (E.res V X z) := by
  subst h
  have : LinearEquiv.ofEq X X rfl = LinearEquiv.refl F ↥X := LinearEquiv.ext fun _ => rfl
  rw [this]
  exact (DFunLike.congr_fun (GLSpecies.mapEquiv_refl E.X (sub X)) (E.res V X z)).symm

theorem EBicomod.proj_congr (E : EBicomod F k) {V : FGModuleCat.{0} F} {X Y : Submodule F V}
    (h : X = Y) (z : E.X.ev V) :
    E.proj V Y z = E.X.mapEquiv (Submodule.quotEquivOfEq X Y h) (E.proj V X z) := by
  subst h
  have : Submodule.quotEquivOfEq X X rfl = LinearEquiv.refl F (↑V ⧸ X) :=
    LinearEquiv.ext fun x => by
      induction x using Submodule.Quotient.induction_on
      rfl
  rw [this]
  exact (DFunLike.congr_fun (GLSpecies.mapEquiv_refl E.X (quo X)) (E.proj V X z)).symm

theorem EBicomod.res_res_raw (E : EBicomod F k) (V : FGModuleCat.{0} F)
    (S1 : Submodule F V) (T1 : Submodule F S1) (z : E.X.ev V) :
    E.res V (GLSpecies.flagLower S1 T1) z =
      E.X.mapEquiv (S1.equivSubtypeMap T1) (E.res (sub S1) T1 (E.res V S1 z)) := by
  have hle : GLSpecies.flagLower S1 T1 ≤ S1 := (S1.mapIic T1).property
  have ax := DFunLike.congr_fun (E.res_res V (GLSpecies.flagLower S1 T1) S1 hle) z
  simp only [LinearMap.comp_apply] at ax
  rw [← ax]
  have hX : T1 = (GLSpecies.flagLower S1 T1).comap S1.subtype :=
    (Submodule.comap_map_eq_of_injective S1.injective_subtype T1).symm
  rw [E.res_congr hX (E.res V S1 z)]
  rw [← LinearMap.comp_apply (E.X.mapEquiv _), ← GLSpecies.mapEquiv_trans]
  have hiso : (LinearEquiv.ofEq T1 (Submodule.comap S1.subtype (GLSpecies.flagLower S1 T1)) hX).trans
      (Submodule.comapSubtypeEquivOfLe hle) = S1.equivSubtypeMap T1 :=
    LinearEquiv.ext fun x => Subtype.ext rfl
  rw [hiso]


theorem EBicomod.proj_proj_raw (E : EBicomod F k) (V : FGModuleCat.{0} F)
    (S1 : Submodule F V) (T1 : Submodule F S1) (z : E.X.ev V) :
    E.X.mapEquiv (GLSpecies.flagUpperEquiv S1 T1) (E.proj V S1 z) =
      E.proj (quo (GLSpecies.flagLower S1 T1)) (S1.map (GLSpecies.flagLower S1 T1).mkQ)
        (E.proj V (GLSpecies.flagLower S1 T1) z) := by
  have hle : GLSpecies.flagLower S1 T1 ≤ S1 := (S1.mapIic T1).property
  have ax := DFunLike.congr_fun (E.proj_proj V (GLSpecies.flagLower S1 T1) S1 hle) z
  simp only [LinearMap.comp_apply] at ax
  rw [← ax]
  exact DFunLike.congr_fun (GLSpecies.mapEquiv_symm_comp E.X
    (V := quo (V := quo (GLSpecies.flagLower S1 T1)) (S1.map (GLSpecies.flagLower S1 T1).mkQ))
    (W := quo S1)
    (Submodule.quotientQuotientEquivQuotient (GLSpecies.flagLower S1 T1) S1 hle)) _

theorem EBicomod.proj_res_raw (E : EBicomod F k) (V : FGModuleCat.{0} F)
    (S1 : Submodule F V) (T1 : Submodule F S1) (z : E.X.ev V) :
    E.X.mapEquiv (GLSpecies.flagMiddleEquiv S1 T1) (E.proj (sub S1) T1 (E.res V S1 z)) =
      E.res (quo (GLSpecies.flagLower S1 T1)) (S1.map (GLSpecies.flagLower S1 T1).mkQ)
        (E.proj V (GLSpecies.flagLower S1 T1) z) := by
  have hle : GLSpecies.flagLower S1 T1 ≤ S1 := (S1.mapIic T1).property
  have ax := DFunLike.congr_fun (E.proj_res V (GLSpecies.flagLower S1 T1) S1 hle) z
  simp only [LinearMap.comp_apply] at ax
  rw [← ax]
  have hX : T1 = (GLSpecies.flagLower S1 T1).comap S1.subtype :=
    (Submodule.comap_map_eq_of_injective S1.injective_subtype T1).symm
  rw [E.proj_congr hX (E.res V S1 z)]
  rw [← GLSpecies.mapEquiv_trans_apply]
  have hiso : (T1.quotEquivOfEq (Submodule.comap S1.subtype (GLSpecies.flagLower S1 T1)) hX).trans
      (subQuotIso (GLSpecies.flagLower S1 T1) S1) = GLSpecies.flagMiddleEquiv S1 T1 :=
    LinearEquiv.ext fun x => by
      induction x using Submodule.Quotient.induction_on with
      | H s => exact Subtype.ext rfl
  exact (congrArg (fun e => E.X.mapEquiv e ((E.proj (sub S1) T1) ((E.res V S1) z))) hiso).symm


theorem EBicomod.coactApp_eq (E : EBicomod F k) (V : FGModuleCat.{0} F) (z : E.X.ev V) :
    E.coactApp V z = ∑ S : Submodule F V,
      GLSpecies.pair E.X expSpecies V S (E.res V S z) (expOne (quo S)) := by
  refine (GLSpecies.eq_sum_comp E.X expSpecies V (E.coactApp V z)).trans
    (Finset.sum_congr rfl fun S _ => ?_)
  rw [E.comp_coactApp]
  rfl

theorem EBicomod.coactLApp_eq (E : EBicomod F k) (V : FGModuleCat.{0} F) (z : E.X.ev V) :
    E.coactLApp V z = ∑ S : Submodule F V,
      GLSpecies.pair expSpecies E.X V S (expOne (sub S)) (E.proj V S z) := by
  refine (GLSpecies.eq_sum_comp expSpecies E.X V (E.coactLApp V z)).trans
    (Finset.sum_congr rfl fun S _ => ?_)
  rw [E.comp_coactLApp]
  rfl

theorem EBicomod.coact_assoc' (E : EBicomod F k) :
    E.coact ≫ E.X ◁ ComonObj.comul (X := (expComon F k).X) =
      E.coact ≫ E.coact ▷ (expComon F k).X ≫ (α_ E.X (expComon F k).X (expComon F k).X).hom := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  change GLSpecies.cauchyHomMap (𝟙 E.X) expComul V.of (E.coactApp V.of z) =
    GLSpecies.assocEquiv E.X expSpecies expSpecies V.of
      (GLSpecies.cauchyHomMap E.coact (𝟙 _) V.of (E.coactApp V.of z))
  apply GLSpecies.ext_compR
  intro p
  obtain ⟨⟨S1, T1⟩, rfl⟩ := (GLSpecies.flagIndexEquiv V.of).surjective p
  refine Eq.trans ?_ (GLSpecies.compR_assocEquiv E.X expSpecies expSpecies V.of ⟨S1, T1⟩
    (GLSpecies.cauchyHomMap E.coact (𝟙 expSpecies) V.of (E.coactApp V.of z))).symm
  have hL : GLSpecies.compR E.X expSpecies expSpecies V.of
      (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩)
      (GLSpecies.cauchyHomMap (𝟙 E.X) expComul V.of (E.coactApp V.of z)) =
      (E.res V.of (GLSpecies.flagLower S1 T1) z) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] (1 : k)) := by
    rw [E.coactApp_eq, map_sum, map_sum, Finset.sum_eq_single (GLSpecies.flagLower S1 T1)]
    · rw [GLSpecies.cauchyHomMap_pair, expComul_one]
      refine (GLSpecies.compR_pair_self E.X expSpecies expSpecies V.of
        (GLSpecies.flagLower S1 T1) (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩).2 _ _).trans ?_
      exact congrArg _ (comp_comulElt _ _)
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compR_pair_ne E.X expSpecies expSpecies V.of
        (T := GLSpecies.flagLower S1 T1) hS (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩).2 _ _
    · simp
  have hR : GLSpecies.compL E.X expSpecies expSpecies V.of ⟨S1, T1⟩
      (GLSpecies.cauchyHomMap E.coact (𝟙 _) V.of (E.coactApp V.of z)) =
      ((E.res (sub S1) T1 (E.res V.of S1 z)) ⊗ₜ[k] (1 : k)) ⊗ₜ[k] (1 : k) := by
    rw [E.coactApp_eq, map_sum]
    erw [map_sum]
    rw [Finset.sum_eq_single S1]
    · rw [GLSpecies.cauchyHomMap_pair]
      change GLSpecies.compL E.X expSpecies expSpecies V.of ⟨S1, T1⟩
        (GLSpecies.pair (GLSpecies.cauchy E.X expSpecies) expSpecies V.of S1
          (E.coactApp (sub S1) (E.res V.of S1 z)) (expOne _)) = _
      erw [GLSpecies.compL_pair_self, E.comp_coactApp]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compL_pair_ne _ _ _ _ hS _ _ _
    · simp
  rw [hL]
  erw [hR]
  have hr : (GLSpecies.flagValueEquiv E.X expSpecies expSpecies V.of ⟨S1, T1⟩)
      ((E.res (sub S1) T1 (E.res V.of S1 z) ⊗ₜ[k] (1 : k)) ⊗ₜ[k] (1 : k)) =
      (E.X.mapEquiv (S1.equivSubtypeMap T1) (E.res (sub S1) T1 (E.res V.of S1 z))) ⊗ₜ[k]
        ((1 : k) ⊗ₜ[k] (1 : k)) := by
    simp only [GLSpecies.flagValueEquiv, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
      TensorProduct.congr_tmul]
    rfl
  refine Eq.trans ?_ hr.symm
  rw [E.res_res_raw]
  rfl


theorem EBicomod.coactL_assoc' (E : EBicomod F k) :
    E.coactL ≫ ComonObj.comul (X := (expComon F k).X) ▷ E.X ≫
        (α_ (expComon F k).X (expComon F k).X E.X).hom =
      E.coactL ≫ (expComon F k).X ◁ E.coactL := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  change GLSpecies.assocEquiv expSpecies expSpecies E.X V.of
      (GLSpecies.cauchyHomMap expComul (𝟙 E.X) V.of (E.coactLApp V.of z)) =
    GLSpecies.cauchyHomMap (𝟙 _) E.coactL V.of (E.coactLApp V.of z)
  apply GLSpecies.ext_compR
  intro p
  obtain ⟨⟨S1, T1⟩, rfl⟩ := (GLSpecies.flagIndexEquiv V.of).surjective p
  refine Eq.trans (GLSpecies.compR_assocEquiv expSpecies expSpecies E.X V.of ⟨S1, T1⟩
    (GLSpecies.cauchyHomMap expComul (𝟙 E.X) V.of (E.coactLApp V.of z))) ?_
  have hL : GLSpecies.compL expSpecies expSpecies E.X V.of ⟨S1, T1⟩
      (GLSpecies.cauchyHomMap expComul (𝟙 E.X) V.of (E.coactLApp V.of z)) =
      ((1 : k) ⊗ₜ[k] (1 : k)) ⊗ₜ[k] (E.proj V.of S1 z) := by
    rw [E.coactLApp_eq, map_sum]
    erw [map_sum]
    rw [Finset.sum_eq_single S1]
    · rw [GLSpecies.cauchyHomMap_pair]
      change GLSpecies.compL expSpecies expSpecies E.X V.of ⟨S1, T1⟩
        (GLSpecies.pair (GLSpecies.cauchy expSpecies expSpecies) E.X V.of S1
          (((expComul (F := F) (k := k)).app ⟨sub S1⟩).hom (expOne _)) (E.proj V.of S1 z)) = _
      erw [GLSpecies.compL_pair_self, expComul_one, comp_comulElt]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compL_pair_ne _ _ _ _ hS _ _ _
    · simp
  have hR : GLSpecies.compR expSpecies expSpecies E.X V.of
      (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩)
      (GLSpecies.cauchyHomMap (𝟙 _) E.coactL V.of (E.coactLApp V.of z)) =
      (1 : k) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] (E.proj (quo (GLSpecies.flagLower S1 T1))
        (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩).2 (E.proj V.of (GLSpecies.flagLower S1 T1) z))) := by
    rw [E.coactLApp_eq, map_sum]
    erw [map_sum]
    rw [Finset.sum_eq_single (GLSpecies.flagLower S1 T1)]
    · rw [GLSpecies.cauchyHomMap_pair]
      refine (GLSpecies.compR_pair_self expSpecies expSpecies E.X V.of
        (GLSpecies.flagLower S1 T1) (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩).2 _ _).trans ?_
      erw [E.comp_coactLApp]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compR_pair_ne expSpecies expSpecies E.X V.of
        (T := GLSpecies.flagLower S1 T1) hS (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩).2 _ _
    · simp
  have hr : (GLSpecies.flagValueEquiv expSpecies expSpecies E.X V.of ⟨S1, T1⟩)
      (((1 : k) ⊗ₜ[k] (1 : k)) ⊗ₜ[k] (E.proj V.of S1 z)) =
      (1 : k) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] (E.X.mapEquiv (GLSpecies.flagUpperEquiv S1 T1)
        (E.proj V.of S1 z))) := by
    simp only [GLSpecies.flagValueEquiv, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
      TensorProduct.congr_tmul]
    rfl
  refine Eq.trans (congrArg (GLSpecies.flagValueEquiv expSpecies expSpecies E.X V.of ⟨S1, T1⟩) hL) ?_
  refine Eq.trans hr ?_
  refine Eq.trans ?_ hR.symm
  exact congrArg (fun t => (1 : k) ⊗ₜ[k] ((1 : k) ⊗ₜ[k] t)) (E.proj_proj_raw V.of S1 T1 z)


theorem EBicomod.compat' (E : EBicomod F k) :
    E.coactL ≫ (expComon F k).X ◁ E.coact =
      E.coact ≫ E.coactL ▷ (expComon F k).X ≫
        (α_ (expComon F k).X E.X (expComon F k).X).hom := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  change GLSpecies.cauchyHomMap (𝟙 _) E.coact V.of (E.coactLApp V.of z) =
    GLSpecies.assocEquiv expSpecies E.X expSpecies V.of
      (GLSpecies.cauchyHomMap E.coactL (𝟙 _) V.of (E.coactApp V.of z))
  apply GLSpecies.ext_compR
  intro p
  obtain ⟨⟨S1, T1⟩, rfl⟩ := (GLSpecies.flagIndexEquiv V.of).surjective p
  refine Eq.trans ?_ (GLSpecies.compR_assocEquiv expSpecies E.X expSpecies V.of ⟨S1, T1⟩
    (GLSpecies.cauchyHomMap E.coactL (𝟙 _) V.of (E.coactApp V.of z))).symm
  have hL : GLSpecies.compL expSpecies E.X expSpecies V.of ⟨S1, T1⟩
      (GLSpecies.cauchyHomMap E.coactL (𝟙 _) V.of (E.coactApp V.of z)) =
      ((1 : k) ⊗ₜ[k] (E.proj (sub S1) T1 (E.res V.of S1 z))) ⊗ₜ[k] (1 : k) := by
    rw [E.coactApp_eq, map_sum]
    erw [map_sum]
    rw [Finset.sum_eq_single S1]
    · rw [GLSpecies.cauchyHomMap_pair]
      change GLSpecies.compL expSpecies E.X expSpecies V.of ⟨S1, T1⟩
        (GLSpecies.pair (GLSpecies.cauchy expSpecies E.X) expSpecies V.of S1
          (E.coactLApp (sub S1) (E.res V.of S1 z)) (expOne _)) = _
      erw [GLSpecies.compL_pair_self, E.comp_coactLApp]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compL_pair_ne _ _ _ _ hS _ _ _
    · simp
  have hR : GLSpecies.compR expSpecies E.X expSpecies V.of
      (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩)
      (GLSpecies.cauchyHomMap (𝟙 _) E.coact V.of (E.coactLApp V.of z)) =
      (1 : k) ⊗ₜ[k] ((E.res (quo (GLSpecies.flagLower S1 T1))
        (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩).2 (E.proj V.of (GLSpecies.flagLower S1 T1) z))
          ⊗ₜ[k] (1 : k)) := by
    rw [E.coactLApp_eq, map_sum]
    erw [map_sum]
    rw [Finset.sum_eq_single (GLSpecies.flagLower S1 T1)]
    · rw [GLSpecies.cauchyHomMap_pair]
      refine (GLSpecies.compR_pair_self expSpecies E.X expSpecies V.of
        (GLSpecies.flagLower S1 T1) (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩).2 _ _).trans ?_
      erw [E.comp_coactApp]
      rfl
    · intro S _ hS
      rw [GLSpecies.cauchyHomMap_pair]
      exact GLSpecies.compR_pair_ne expSpecies E.X expSpecies V.of
        (T := GLSpecies.flagLower S1 T1) hS (GLSpecies.flagIndexEquiv V.of ⟨S1, T1⟩).2 _ _
    · simp
  have hr : (GLSpecies.flagValueEquiv expSpecies E.X expSpecies V.of ⟨S1, T1⟩)
      (((1 : k) ⊗ₜ[k] (E.proj (sub S1) T1 (E.res V.of S1 z))) ⊗ₜ[k] (1 : k)) =
      (1 : k) ⊗ₜ[k] ((E.X.mapEquiv (GLSpecies.flagMiddleEquiv S1 T1)
        (E.proj (sub S1) T1 (E.res V.of S1 z))) ⊗ₜ[k] (1 : k)) := by
    simp only [GLSpecies.flagValueEquiv, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
      TensorProduct.congr_tmul]
    rfl
  refine Eq.trans hR ?_
  refine Eq.trans ?_ (congrArg (GLSpecies.flagValueEquiv expSpecies E.X expSpecies V.of ⟨S1, T1⟩) hL).symm
  refine Eq.trans ?_ hr.symm
  exact congrArg (fun t => (1 : k) ⊗ₜ[k] (t ⊗ₜ[k] (1 : k))) (E.proj_res_raw V.of S1 T1 z).symm


/-- The backward direction of the correspondence. -/
def EBicomod.toBicomod (E : EBicomod F k) : Bicomod (expComon F k) where
  X := E.X
  coact := E.coact
  coact_counit := E.coact_counit'
  coact_assoc := E.coact_assoc'
  coactL := E.coactL
  counit_coactL := E.counit_coactL'
  coactL_assoc := E.coactL_assoc'
  compat := E.compat'

theorem Bicomod.toE_toBicomod (E : EBicomod F k) : E.toBicomod.toE = E := by
  have hres : ∀ V S, E.toBicomod.resMap V S = E.res V S := by
    intro V S
    apply LinearMap.ext
    intro z
    change (TensorProduct.rid k (E.X.ev (sub S))) (GLSpecies.comp E.X expSpecies V S
      (E.coactApp V z)) = _
    erw [E.comp_coactApp]
    simp
    rfl
  have hproj : ∀ V S, E.toBicomod.projMap V S = E.proj V S := by
    intro V S
    apply LinearMap.ext
    intro z
    change (TensorProduct.lid k (E.X.ev (quo S))) (GLSpecies.comp expSpecies E.X V S
      (E.coactLApp V z)) = _
    erw [E.comp_coactLApp]
    simp
    rfl
  cases E
  simp only [Bicomod.toE, EBicomod.toBicomod] at hres hproj ⊢
  congr 1
  · funext V S; exact hres V S
  · funext V S; exact hproj V S

theorem Bicomod.ext_aux {c : Comon (GLSpecies F k)} (M N : Bicomod c) (hX : M.X = N.X)
    (h1 : HEq M.coact N.coact) (h2 : HEq M.coactL N.coactL) : M = N := by
  obtain ⟨⟨X, coact, c1, c2⟩, coactL, l1, l2, cm⟩ := M
  obtain ⟨⟨X', coact', c1', c2'⟩, coactL', l1', l2', cm'⟩ := N
  simp only at hX
  subst hX
  simp only [heq_eq_eq] at h1
  subst h1
  simp only [heq_eq_eq] at h2
  subst h2
  rfl

theorem EBicomod.toBicomod_toE (M : Bicomod (expComon F k)) : M.toE.toBicomod = M := by
  have h1 : M.toE.coact = M.coact := by
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change M.toE.coactApp V.of z = (M.coact.app V).hom z
    rw [M.toE.coactApp_eq]
    exact (M.coact_eq V.of z).symm
  have h2 : M.toE.coactL = M.coactL := by
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change M.toE.coactLApp V.of z = (M.coactL.app V).hom z
    rw [M.toE.coactLApp_eq]
    exact (M.coactL_eq V.of z).symm
  exact Bicomod.ext_aux _ _ rfl (heq_of_eq h1) (heq_of_eq h2)


/-- The coordinate description agrees with bicomodules over the comonoid `e`.

**Gap (unproved, §1.3).** The thesis states the correspondence between coordinate
bicomodules and bicomodules over `e` without proof, explicitly omitting all checks
(§1.3, p. 10: "Solamente describiremos la forma de pasar de una estructura a la otra
omitiendo las verificaciones, que son tediosas pero simples"). We prove it:
the restriction/projection maps are the components of the right/left coactions
(`Bicomod.toE`), and conversely the coactions are `z ↦ ∑_S z|_S ⊗ e_{V/S}`
(`EBicomod.toBicomod`). -/
theorem EBicomod.equiv_bicomod :
    Nonempty (EBicomod F k ≃ Bicomod (expComon F k)) :=
  ⟨{ toFun := EBicomod.toBicomod
     invFun := Bicomod.toE
     left_inv := Bicomod.toE_toBicomod
     right_inv := EBicomod.toBicomod_toE }⟩

end MartinPhd

end
end EquivBack
