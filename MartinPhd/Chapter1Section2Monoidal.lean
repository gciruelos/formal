import MartinPhd.Chapter1Section2Cauchy

/-!
# Chapter 1, Section 1.2 (monoidal structure, comodules, injectives)

Contents:
* Monoidal
* Injectives
* Comodules
* Chapter1Section2
-/

section Monoidal

open scoped BigOperators TensorProduct DirectSum
open CategoryTheory Module

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

noncomputable section

namespace MartinPhd

section Species

variable {F : Type} [Field F] {k : Type} [Field k]

attribute [local instance] Classical.propDecidable

namespace GLSpecies

set_option maxHeartbeats 1000000 in
/-- Naturality of the associator under isomorphisms of ambient vector spaces. -/
theorem assocEquiv_naturality (x y z : GLSpecies F k) {V W : FGModuleCat.{0} F}
    (e : V ≃ₗ[F] W) :
    (assocEquiv x y z W).toLinearMap.comp (cauchyMap (cauchy x y) z e) =
      (cauchyMap x (cauchy y z) e).comp (assocEquiv x y z V).toLinearMap := by
  apply tripleLeft_ext
  intro S T a b c
  change assocEquiv x y z W (cauchyMap (cauchy x y) z e
    (pair (cauchy x y) z V S (pair x y (sub S) T a b) c)) =
    cauchyMap x (cauchy y z) e (assocEquiv x y z V
      (pair (cauchy x y) z V S (pair x y (sub S) T a b) c))
  simp only [cauchyMap_pair, cauchy_mapEquiv, assocEquiv_pair]
  let S' := S.map (e : V →ₗ[F] W)
  let T' := T.map (e.submoduleMap S : S →ₗ[F] S')
  let U := flagLower S T
  let U' := flagLower S' T'
  let Ue := U.map (e : V →ₗ[F] W)
  have hU : U' = Ue := by
    dsimp [U', Ue, U, S', T', flagLower]
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    apply congrArg (fun f : S →ₗ[F] W => T.map f)
    ext v
    rfl
  apply pair_congr hU
  · simp only [← mapEquiv_trans_apply]
    rw [← mapEquiv_trans_apply x (U := sub (V := sub S) T) (V := sub U') (W := sub Ue)]
    apply congrArg (fun f : T ≃ₗ[F] Ue =>
      x.mapEquiv (V := sub (V := sub S) T) (W := sub Ue) f a)
    ext v
    rfl
  · simp only [cauchy_mapEquiv]
    rw [cauchyMap_pair y z (V := quo U') (W := quo Ue)
      (Submodule.quotEquivOfEq U' Ue hU)]
    let qh := Submodule.quotEquivOfEq U' Ue hU
    let qe := Submodule.Quotient.equiv U Ue e rfl
    have hQ : (S'.map U'.mkQ).map (qh : (W ⧸ U') →ₗ[F] (W ⧸ Ue)) =
        (S.map U.mkQ).map (qe : (V ⧸ U) →ₗ[F] (W ⧸ Ue)) := by
      dsimp [S', qh, qe]
      simp only [← Submodule.map_comp]
      congr 1
    apply pair_congr hQ
    · simp only [← mapEquiv_trans_apply]
      rw [← mapEquiv_trans_apply y (U := quo (V := sub S) T)
        (V := sub (V := quo U') (S'.map U'.mkQ))
        (W := sub (V := quo Ue) ((S.map U.mkQ).map (qe : (V ⧸ U) →ₗ[F] (W ⧸ Ue))))]
      apply congrArg (fun f : (S ⧸ T) ≃ₗ[F] ((S.map U.mkQ).map (qe : (V ⧸ U) →ₗ[F] (W ⧸ Ue))) =>
        y.mapEquiv (V := quo (V := sub S) T)
          (W := sub (V := quo Ue) ((S.map U.mkQ).map (qe : (V ⧸ U) →ₗ[F] (W ⧸ Ue)))) f b)
      apply LinearEquiv.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | H v =>
        apply Subtype.ext
        rfl
    · simp only [← mapEquiv_trans_apply]
      rw [← mapEquiv_trans_apply z (U := quo S)
        (V := quo (V := quo U') (S'.map U'.mkQ))
        (W := quo (V := quo Ue) ((S.map U.mkQ).map (qe : (V ⧸ U) →ₗ[F] (W ⧸ Ue))))]
      apply congrArg (fun f : (V ⧸ S) ≃ₗ[F]
          ((W ⧸ Ue) ⧸ (S.map U.mkQ).map (qe : (V ⧸ U) →ₗ[F] (W ⧸ Ue))) =>
        z.mapEquiv (V := quo S)
          (W := quo (V := quo Ue) ((S.map U.mkQ).map (qe : (V ⧸ U) →ₗ[F] (W ⧸ Ue)))) f c)
      apply LinearEquiv.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | H v => rfl


/-- The Cauchy associator as an isomorphism of species. -/
def cauchyAssociator (x y z : GLSpecies F k) : cauchy (cauchy x y) z ≅ cauchy x (cauchy y z) :=
  NatIso.ofComponents (fun V => (assocEquiv x y z V.of).toModuleIso)
    (fun {V W} φ => by
      apply ModuleCat.hom_ext
      exact assocEquiv_naturality x y z (FGModuleCat.isoToLinearEquiv φ.iso))

@[simp] theorem cauchyHom_app_hom {x x' y y' : GLSpecies F k}
    (f : x ⟶ x') (g : y ⟶ y') (V : Core (FGModuleCat F)) :
    ((cauchyHom f g).app V).hom = cauchyHomMap f g V.of := rfl

/-- Naturality of the Cauchy associator in each species. -/
theorem cauchyAssociator_naturality {x x' y y' z z' : GLSpecies F k}
    (f : x ⟶ x') (g : y ⟶ y') (h : z ⟶ z') :
    cauchyHom (cauchyHom f g) h ≫ (cauchyAssociator x' y' z').hom =
      (cauchyAssociator x y z).hom ≫ cauchyHom f (cauchyHom g h) := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  change (assocEquiv x' y' z' V.of).toLinearMap.comp
      (cauchyHomMap (cauchyHom f g) h V.of) =
    (cauchyHomMap f (cauchyHom g h) V.of).comp (assocEquiv x y z V.of).toLinearMap
  apply tripleLeft_ext
  intro S T a b c
  change assocEquiv x' y' z' V.of (cauchyHomMap (cauchyHom f g) h V.of
    (pair (cauchy x y) z V.of S (pair x y (sub S) T a b) c)) =
    cauchyHomMap f (cauchyHom g h) V.of (assocEquiv x y z V.of
      (pair (cauchy x y) z V.of S (pair x y (sub S) T a b) c))
  simp only [cauchyHom_app_hom, cauchyHomMap_pair, assocEquiv_pair]
  have hf := DFunLike.congr_fun (mapEquiv_naturality f
    (V := sub (V := sub S) T) (W := sub (flagLower S T)) (S.equivSubtypeMap T)) a
  have hg := DFunLike.congr_fun (mapEquiv_naturality g
    (V := quo (V := sub S) T)
    (W := sub (V := quo (flagLower S T)) (S.map (flagLower S T).mkQ))
    (flagMiddleEquiv S T)) b
  have hh := DFunLike.congr_fun (mapEquiv_naturality h
    (V := quo S) (W := quo (V := quo (flagLower S T)) (S.map (flagLower S T).mkQ))
    (flagUpperEquiv S T)) c
  simp only [LinearMap.comp_apply] at hf hg hh
  rw [hf, hg, hh]

@[simp] theorem cauchyLeftUnitor_app_hom (x : GLSpecies F k) (V : Core (FGModuleCat F)) :
    ((cauchyLeftUnitor x).hom.app V).hom = leftUnitMap x V.of := rfl

@[simp] theorem cauchyRightUnitor_app_hom (x : GLSpecies F k) (V : Core (FGModuleCat F)) :
    ((cauchyRightUnitor x).hom.app V).hom = rightUnitMap x V.of := rfl

theorem pair_smul_swap (x y : GLSpecies F k) (V : FGModuleCat F) (S : Submodule F V)
    (r : k) (a : x.ev (sub S)) (b : y.ev (quo S)) :
    pair x y V S a (r • b) = pair x y V S (r • a) b := by
  simp only [pair, TensorProduct.smul_tmul, TensorProduct.tmul_smul]

/-- The unit triangle for the Cauchy associator. -/
theorem cauchy_triangle (x y : GLSpecies F k) :
    (cauchyAssociator x unit y).hom ≫ cauchyHom (𝟙 x) (cauchyLeftUnitor y).hom =
      cauchyHom (cauchyRightUnitor x).hom (𝟙 y) := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  change (cauchyHomMap (𝟙 x) (cauchyLeftUnitor y).hom V.of).comp
    (assocEquiv x unit y V.of).toLinearMap = cauchyHomMap (cauchyRightUnitor x).hom (𝟙 y) V.of
  apply tripleLeft_ext
  intro S T a b c
  change cauchyHomMap (𝟙 x) (cauchyLeftUnitor y).hom V.of
    (assocEquiv x unit y V.of (pair (cauchy x unit) y V.of S (pair x unit (sub S) T a b) c)) =
    cauchyHomMap (cauchyRightUnitor x).hom (𝟙 y) V.of
      (pair (cauchy x unit) y V.of S (pair x unit (sub S) T a b) c)
  by_cases ht : T = ⊤
  · subst T
    let U := flagLower S (⊤ : Submodule F S)
    have hU : U = S := by simp [U, Submodule.map_top]
    have hQ : S.map U.mkQ = ⊥ := by rw [hU]; exact Submodule.mkQ_map_self S
    simp only [assocEquiv_pair, cauchyHomMap_pair, cauchyLeftUnitor_app_hom,
      cauchyRightUnitor_app_hom, NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply]
    rw [leftUnitMap_pair_of_eq y (quo U) _ hQ, rightUnitMap_pair_top,
      unit_mapEquiv_val, pair_smul_swap]
    apply pair_congr hU
    · rw [map_smul]
      apply congrArg (fun v => b.val • v)
      rw [← mapEquiv_trans_apply x (U := sub (V := sub S) ⊤) (V := sub U) (W := sub S)]
      apply congrArg (fun e : (⊤ : Submodule F S) ≃ₗ[F] S =>
        x.mapEquiv (V := sub (V := sub S) ⊤) (W := sub S) e a)
      ext v
      rfl
    · simp only [← mapEquiv_trans_apply]
      rw [← mapEquiv_trans_apply y (U := quo S)
        (V := quo (V := quo U) (S.map U.mkQ)) (W := quo S)]
      have he : (flagUpperEquiv S (⊤ : Submodule F S)).trans
          ((Submodule.quotEquivOfEqBot (S.map U.mkQ) hQ).trans
            (Submodule.quotEquivOfEq U S hU)) = LinearEquiv.refl F (V.of ⧸ S) := by
        apply LinearEquiv.ext
        intro v
        induction v using Submodule.Quotient.induction_on with
        | H v => rfl
      rw [he, mapEquiv_refl y (quo S), LinearMap.id_apply]
  · have hn : finrank F (S ⧸ T) ≠ 0 := by
      intro h
      have hr := T.finrank_quotient_add_finrank
      exact ht (Submodule.eq_top_of_finrank_eq (by omega))
    have hb : b = 0 := by
      apply Subtype.ext
      change b.val = (0 : k)
      have hp := b.property
      change b.val ∈ (if finrank F (S ⧸ T) = 0 then ⊤ else ⊥ : Submodule k k) at hp
      simpa only [ite_eq_right hn, Submodule.mem_bot] using hp
    simp only [hb, pair, TensorProduct.tmul_zero, TensorProduct.zero_tmul,
      LinearMap.map_zero, LinearEquiv.map_zero]

/-- Functoriality on a chain of 3 subquotient isomorphisms. -/
theorem mapEquiv_chain3_two (x : GLSpecies F k) {A0 A1 A2 A3 B : FGModuleCat F}
    (e1 : A0 ≃ₗ[F] A1)
    (e2 : A1 ≃ₗ[F] A2)
    (e3 : A2 ≃ₗ[F] A3)
    (f1 : A0 ≃ₗ[F] B) (f2 : B ≃ₗ[F] A3) (a : x.ev A0)
    (h : ((e1).trans e2).trans e3 = f1.trans f2) :
    x.mapEquiv e3 (x.mapEquiv e2 (x.mapEquiv e1 (a))) = x.mapEquiv f2 (x.mapEquiv f1 a) := by
  calc
    _ = x.mapEquiv (((e1).trans e2).trans e3) a := by simp only [mapEquiv_trans_apply]
    _ = x.mapEquiv (f1.trans f2) a := congrArg (fun e => x.mapEquiv e a) h
    _ = _ := mapEquiv_trans_apply x f1 f2 a

/-- Functoriality on a chain of 5 subquotient isomorphisms. -/
theorem mapEquiv_chain5_two (x : GLSpecies F k) {A0 A1 A2 A3 A4 A5 B : FGModuleCat F}
    (e1 : A0 ≃ₗ[F] A1)
    (e2 : A1 ≃ₗ[F] A2)
    (e3 : A2 ≃ₗ[F] A3)
    (e4 : A3 ≃ₗ[F] A4)
    (e5 : A4 ≃ₗ[F] A5)
    (f1 : A0 ≃ₗ[F] B) (f2 : B ≃ₗ[F] A5) (a : x.ev A0)
    (h : ((((e1).trans e2).trans e3).trans e4).trans e5 = f1.trans f2) :
    x.mapEquiv e5 (x.mapEquiv e4 (x.mapEquiv e3 (x.mapEquiv e2 (x.mapEquiv e1 (a))))) = x.mapEquiv f2 (x.mapEquiv f1 a) := by
  calc
    _ = x.mapEquiv (((((e1).trans e2).trans e3).trans e4).trans e5) a := by simp only [mapEquiv_trans_apply]
    _ = x.mapEquiv (f1.trans f2) a := congrArg (fun e => x.mapEquiv e a) h
    _ = _ := mapEquiv_trans_apply x f1 f2 a

/-- Functoriality on a chain of 6 subquotient isomorphisms. -/
theorem mapEquiv_chain6_two (x : GLSpecies F k) {A0 A1 A2 A3 A4 A5 A6 B : FGModuleCat F}
    (e1 : A0 ≃ₗ[F] A1)
    (e2 : A1 ≃ₗ[F] A2)
    (e3 : A2 ≃ₗ[F] A3)
    (e4 : A3 ≃ₗ[F] A4)
    (e5 : A4 ≃ₗ[F] A5)
    (e6 : A5 ≃ₗ[F] A6)
    (f1 : A0 ≃ₗ[F] B) (f2 : B ≃ₗ[F] A6) (a : x.ev A0)
    (h : (((((e1).trans e2).trans e3).trans e4).trans e5).trans e6 = f1.trans f2) :
    x.mapEquiv e6 (x.mapEquiv e5 (x.mapEquiv e4 (x.mapEquiv e3 (x.mapEquiv e2 (x.mapEquiv e1 (a)))))) = x.mapEquiv f2 (x.mapEquiv f1 a) := by
  calc
    _ = x.mapEquiv ((((((e1).trans e2).trans e3).trans e4).trans e5).trans e6) a := by simp only [mapEquiv_trans_apply]
    _ = x.mapEquiv (f1.trans f2) a := congrArg (fun e => x.mapEquiv e a) h
    _ = _ := mapEquiv_trans_apply x f1 f2 a

@[simp] theorem cauchyAssociator_app_hom (x y z : GLSpecies F k) (V : Core (FGModuleCat F)) :
    ((cauchyAssociator x y z).hom.app V).hom = (assocEquiv x y z V.of).toLinearMap := rfl

@[simp] theorem pair_zero_left (x y : GLSpecies F k) (V : FGModuleCat F)
    (S : Submodule F V) (b : y.ev (quo S)) : pair x y V S 0 b = 0 := by
  unfold pair
  rw [TensorProduct.zero_tmul]
  exact LinearMap.map_zero _

theorem quadrupleLeft_ext {w x y z : GLSpecies F k} {V : FGModuleCat.{0} F}
    {M : Type} [AddCommGroup M] [Module k M]
    {f g : cauchyObj (cauchy (cauchy w x) y) z V →ₗ[k] M}
    (h : ∀ (S : Submodule F V) (T : Submodule F S) (R : Submodule F T)
      (a : w.ev (sub (V := sub (V := sub S) T) R))
      (b : x.ev (quo (V := sub (V := sub S) T) R))
      (c : y.ev (quo (V := sub S) T)) (d : z.ev (quo S)),
      f (pair (cauchy (cauchy w x) y) z V S
        (pair (cauchy w x) y (sub S) T (pair w x (sub (V := sub S) T) R a b) c) d) =
      g (pair (cauchy (cauchy w x) y) z V S
        (pair (cauchy w x) y (sub S) T (pair w x (sub (V := sub S) T) R a b) c) d)) : f = g := by
  apply tripleLeft_ext
  intro S T a c d
  change cauchyObj w x (sub (V := sub S) T) at a
  induction a using DirectSum.induction_on with
  | zero => rw [pair_zero_left, pair_zero_left, map_zero, map_zero]
  | add a b ha hb => simpa only [pair, TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) ha hb
  | of R t =>
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [pair, map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) ha hb
    | tmul a b => exact h S T R a b c d

/-- The pentagon identity for the Cauchy associator. -/
theorem cauchy_pentagon (w x y z : GLSpecies F k) :
    cauchyHom (cauchyAssociator w x y).hom (𝟙 z) ≫
      (cauchyAssociator w (cauchy x y) z).hom ≫
        cauchyHom (𝟙 w) (cauchyAssociator x y z).hom =
      (cauchyAssociator (cauchy w x) y z).hom ≫ (cauchyAssociator w x (cauchy y z)).hom := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  change (cauchyHomMap (𝟙 w) (cauchyAssociator x y z).hom V.of).comp
      ((assocEquiv w (cauchy x y) z V.of).toLinearMap.comp
        (cauchyHomMap (cauchyAssociator w x y).hom (𝟙 z) V.of)) =
    (assocEquiv w x (cauchy y z) V.of).toLinearMap.comp
      (assocEquiv (cauchy w x) y z V.of).toLinearMap
  apply quadrupleLeft_ext
  intro S T R a b c d
  change cauchyHomMap (𝟙 w) (cauchyAssociator x y z).hom V.of
    (assocEquiv w (cauchy x y) z V.of
      (cauchyHomMap (cauchyAssociator w x y).hom (𝟙 z) V.of
        (pair (cauchy (cauchy w x) y) z V.of S
          (pair (cauchy w x) y (sub S) T (pair w x (sub (V := sub S) T) R a b) c) d))) =
    assocEquiv w x (cauchy y z) V.of
      (assocEquiv (cauchy w x) y z V.of
        (pair (cauchy (cauchy w x) y) z V.of S
          (pair (cauchy w x) y (sub S) T (pair w x (sub (V := sub S) T) R a b) c) d))
  simp only [cauchyHomMap_pair, cauchyAssociator_app_hom,
    LinearEquiv.coe_coe, assocEquiv_pair, cauchy_mapEquiv, cauchyMap_pair,
    NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply]
  let L := flagLower (V := sub S) T R
  let B := flagLower S T
  let R' := R.map (S.equivSubtypeMap T : T →ₗ[F] B)
  let A := flagLower S L
  let A' := flagLower B R'
  have hA : A = A' := by
    dsimp [A, A', L, B, R', flagLower]
    simp only [← Submodule.map_comp]
    apply congrArg (fun f : T →ₗ[F] V.of => R.map f)
    ext v
    rfl
  apply pair_congr hA
  · apply mapEquiv_chain3_two
    ext v
    rfl
  · rw [cauchy_mapEquiv, cauchyMap_pair x (cauchy y z) (V := quo A) (W := quo A')]
    let Q := S.map A.mkQ
    let P := (T.map L.mkQ).map (flagMiddleEquiv S L : (S ⧸ L) →ₗ[F] Q)
    let C := flagLower (V := quo A) Q P
    let qh := Submodule.quotEquivOfEq A A' hA
    have hB : C.map (qh : (V.of ⧸ A) →ₗ[F] (V.of ⧸ A')) = B.map A'.mkQ := by
      dsimp [C, P, Q, B, flagLower]
      simp only [← Submodule.map_comp]
      apply congrArg (fun f : S →ₗ[F] (V.of ⧸ A') => T.map f)
      ext v
      rfl
    apply pair_congr hB
    · apply mapEquiv_chain5_two
      apply LinearEquiv.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | H v =>
        apply Subtype.ext
        rfl
    · simp only [cauchy_mapEquiv]
      let Ce := C.map (qh : (V.of ⧸ A) →ₗ[F] (V.of ⧸ A'))
      let D := B.map A'.mkQ
      let qe := Submodule.Quotient.equiv C Ce qh rfl
      let qhB := Submodule.quotEquivOfEq Ce D hB
      rw [cauchyMap_pair y z (V := quo (V := quo A) C)
        (W := quo (V := quo A') Ce) qe,
        cauchyMap_pair y z (V := quo (V := quo A') Ce)
          (W := quo (V := quo A') D) qhB]
      have hC : ((Q.map C.mkQ).map (qe : ((V.of ⧸ A) ⧸ C) →ₗ[F] ((V.of ⧸ A') ⧸ Ce))).map
          (qhB : ((V.of ⧸ A') ⧸ Ce) →ₗ[F] ((V.of ⧸ A') ⧸ D)) =
          (S.map B.mkQ).map (flagUpperEquiv B R' : (V.of ⧸ B) →ₗ[F] ((V.of ⧸ A') ⧸ D)) := by
        dsimp [Q]
        simp only [← Submodule.map_comp]
        apply congrArg (fun f : V.of →ₗ[F] ((V.of ⧸ A') ⧸ D) => S.map f)
        ext v
        rfl
      apply pair_congr hC
      · apply mapEquiv_chain6_two
        apply LinearEquiv.ext
        intro v
        induction v using Submodule.Quotient.induction_on with
        | H v =>
          apply Subtype.ext
          rfl
      · apply mapEquiv_chain5_two
        apply LinearEquiv.ext
        intro v
        induction v using Submodule.Quotient.induction_on with
        | H v => rfl


/-- The monoidal structure of `Sp` given by the Cauchy product.

The associator is the one in the thesis (via the third isomorphism theorem
`Φ_{T,S,V} : V/S ≅ (V/T)/(S/T)` of (1.2)); the unitors come from those of `Fin_k`.
The associator, unitors, and coherence laws are constructed explicitly below. -/
instance : MonoidalCategoryStruct (GLSpecies F k) where
  tensorObj := cauchy
  whiskerLeft x _ _ g := cauchyHom (𝟙 x) g
  whiskerRight f y := cauchyHom f (𝟙 y)
  tensorHom f g := cauchyHom f g
  tensorUnit := unit
  associator := cauchyAssociator
  leftUnitor := cauchyLeftUnitor
  rightUnitor := cauchyRightUnitor

instance : MonoidalCategory (GLSpecies F k) where
  tensorHom_def := by
    intro x x' y y' f g
    change cauchyHom f g = cauchyHom f (𝟙 y) ≫ cauchyHom (𝟙 x') g
    simpa using cauchyHom_comp f (𝟙 x') (𝟙 y) g
  id_tensorHom_id := cauchyHom_id
  tensorHom_comp_tensorHom f g f' g' := (cauchyHom_comp f f' g g').symm
  whiskerLeft_id := cauchyHom_id
  id_whiskerRight := cauchyHom_id
  associator_naturality := cauchyAssociator_naturality
  leftUnitor_naturality := cauchyLeftUnitor_naturality
  rightUnitor_naturality := cauchyRightUnitor_naturality
  pentagon := cauchy_pentagon
  triangle := cauchy_triangle

/- The projection onto the summand of a flag in `x^{⊗l}(V)` (1.3) and the
convolution product `z ∗ F` of (1.4) are only used for the flag species `Σ`, where
we define them directly (`Flag.concat`, `Flag.convSub`, `Flag.tits` in §1.8). -/

/-- The species is **relatively projective** if every `x(Fⁿ)` is a projective
`k[GL(Fⁿ)]`-module. -/
def IsRelativelyProjective (x : GLSpecies F k) : Prop :=
  ∀ n, Module.Projective (MonoidAlgebra k (GLn F n)) (x.rep n).asModule

/-- Maschke: if `char k = 0` every GL-species is relatively projective. -/
theorem isRelativelyProjective_of_charZero [Finite F] [CharZero k] (x : GLSpecies F k) :
    x.IsRelativelyProjective := by
  intro n
  have : Finite (GLn F n) := Finite.of_injective
    (fun e : GLn F n => (e : (Fin n → F) → (Fin n → F))) DFunLike.coe_injective
  exact Module.projective_of_isSemisimpleRing _ _

/-- The truncation `x_n` of (1.5): `x_n(V) = x(V)` if `dim V = n` and `0` otherwise. -/
def trunc (x : GLSpecies F k) (n : ℕ) : GLSpecies F k where
  obj V := ModuleCat.of k ↥(if finrank F V.of = n then ⊤ else ⊥ : Submodule k (x.obj V))
  map φ := ModuleCat.ofHom <| (x.map φ).hom.restrict (by
    have hd := LinearEquiv.finrank_eq (FGModuleCat.isoToLinearEquiv φ.iso)
    intro v hv
    rw [← hd]
    split_ifs at hv ⊢
    · trivial
    · simpa using congrArg (x.map φ).hom (show v = 0 from hv))
  map_id V := by
    ext v
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (x.map_id V)) v.val
  map_comp φ ψ := by
    ext v
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (x.map_comp φ ψ)) v.val

/-- `x` is concentrated in dimension `n`. -/
def IsConcentrated (x : GLSpecies F k) (n : ℕ) : Prop :=
  ∀ V : FGModuleCat.{0} F, finrank F V ≠ n → Subsingleton (x.ev V)

/-- The natural transformation `π_n : x → x_n`. -/
def truncπ (x : GLSpecies F k) (n : ℕ) : x ⟶ x.trunc n where
  app V := ModuleCat.ofHom <|
    if h : finrank F V.of = n then
      LinearMap.codRestrict _ LinearMap.id (fun v => by simp [h])
    else 0
  naturality {V W} φ := by
    have hd := LinearEquiv.finrank_eq (FGModuleCat.isoToLinearEquiv φ.iso)
    ext v
    apply Subtype.ext
    by_cases h : finrank F V.of = n
    · have h' : finrank F W.of = n := hd ▸ h
      simp only [dite_eq_left h, dite_eq_left h']
      rfl
    · have h' : finrank F W.of ≠ n := hd ▸ h
      simp only [dite_eq_right h, dite_eq_right h']
      change ((0 : x.obj W →ₗ[k] ↥(if finrank F W.of = n then ⊤ else ⊥ : Submodule k (x.obj W))) ((x.map φ).hom v)).val = _
      change (0 : x.obj W) = (x.map φ).hom 0
      simp

/-- Transport an equivariant map from the standard space to isomorphic spaces. -/
private theorem transport_naturality (x y : GLSpecies F k) (n : ℕ)
    (f : x.ev (stdSpace F n) →ₗ[k] y.ev (stdSpace F n))
    (hf : ∀ g : GLn F n, f.comp (x.mapEquiv g) = (y.mapEquiv g).comp f)
    {V W : FGModuleCat.{0} F} (e : (stdSpace F n) ≃ₗ[F] V)
    (d : (stdSpace F n) ≃ₗ[F] W) (a : V ≃ₗ[F] W) :
    ((y.mapEquiv d).comp (f.comp (x.mapEquiv d.symm))).comp (x.mapEquiv a) =
      (y.mapEquiv a).comp ((y.mapEquiv e).comp (f.comp (x.mapEquiv e.symm))) := by
  let g : GLn F n := (e.trans a).trans d.symm
  have he : e.symm.trans g = a.trans d.symm := by ext v; simp [g]
  have hd : g.trans d = e.trans a := by ext v; simp [g]
  have h := congrArg (fun t => (y.mapEquiv d).comp (t.comp (x.mapEquiv e.symm))) (hf g)
  simp only [LinearMap.comp_assoc, ← mapEquiv_trans, he] at h ⊢
  have hyd : (y.mapEquiv d).comp (y.mapEquiv g) =
      (y.mapEquiv a).comp (y.mapEquiv e) := by
    rw [← mapEquiv_trans, hd, mapEquiv_trans]
  simpa only [← LinearMap.comp_assoc, hyd] using h

/-- (1.6) and **Lemma 1.3.** If `x` is concentrated in dimension `n`, then
`Hom_Sp(x, y) ≅ Hom_{GL(Fⁿ)}(x(Fⁿ), y(Fⁿ))`, `φ ↦ φ(Fⁿ)`. -/
theorem hom_concentrated_equiv (x y : GLSpecies F k) (n : ℕ) (hx : x.IsConcentrated n) :
    ∃ e : (x ⟶ y) ≃ {f : x.ev (stdSpace F n) →ₗ[k] y.ev (stdSpace F n) //
        ∀ g, f ∘ₗ x.rep n g = y.rep n g ∘ₗ f},
      ∀ φ, (e φ).1 = (φ.app ⟨stdSpace F n⟩).hom := by
  let eval : (x ⟶ y) → {f : x.ev (stdSpace F n) →ₗ[k] y.ev (stdSpace F n) //
      ∀ g, f ∘ₗ x.rep n g = y.rep n g ∘ₗ f} :=
    fun φ => ⟨(φ.app ⟨stdSpace F n⟩).hom, fun g => mapEquiv_naturality φ (V := stdSpace F n) (W := stdSpace F n) g⟩
  have transport (φ : x ⟶ y) {V : FGModuleCat.{0} F}
      (e : (stdSpace F n) ≃ₗ[F] V) :
      (φ.app ⟨V⟩).hom = (y.mapEquiv e).comp
        ((φ.app ⟨stdSpace F n⟩).hom.comp (x.mapEquiv e.symm)) := by
    symm
    rw [← LinearMap.comp_assoc, ← mapEquiv_naturality, LinearMap.comp_assoc,
      mapEquiv_comp_symm, LinearMap.comp_id]
  let e (V : FGModuleCat.{0} F) (h : finrank F V = n) : (stdSpace F n) ≃ₗ[F] V :=
    LinearEquiv.ofFinrankEq (R := F) (stdSpace F n) V (by simpa using h.symm)
  have hinj : Function.Injective eval := by
    intro φ ψ h
    have hstd := congrArg Subtype.val h
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    by_cases hd : finrank F V.of = n
    · rw [transport φ (e V.of hd), transport ψ (e V.of hd)]
      exact congrArg (fun f => (y.mapEquiv (e V.of hd)).comp
        (f.comp (x.mapEquiv (e V.of hd).symm))) hstd
    · have := hx V.of hd
      ext v
      have hv : v = 0 := Subsingleton.elim _ _
      simp [hv]
  have hsurj : Function.Surjective eval := by
    intro f
    let φ : x ⟶ y :=
      { app := fun V => ModuleCat.ofHom <|
          if h : finrank F V.of = n then
            (y.mapEquiv (e V.of h)).comp (f.val.comp (x.mapEquiv (e V.of h).symm))
          else 0
        naturality := by
          intro V W a
          have hd := LinearEquiv.finrank_eq (FGModuleCat.isoToLinearEquiv a.iso)
          by_cases hV : finrank F V.of = n
          · have hW : finrank F W.of = n := hd ▸ hV
            apply ModuleCat.hom_ext
            simp only [dite_eq_left hV, dite_eq_left hW, ModuleCat.hom_comp,
              ModuleCat.hom_ofHom]
            exact transport_naturality x y n f.val f.property
              (e V.of hV) (e W.of hW) (FGModuleCat.isoToLinearEquiv a.iso)
          · have := hx V.of hV
            ext v
            have hv : v = 0 := Subsingleton.elim _ _
            simp [hv] }
    refine ⟨φ, Subtype.ext ?_⟩
    have hn : finrank F (stdSpace F n) = n := by simp
    change (if h : finrank F (stdSpace F n) = n then _ else _) = f.val
    rw [dite_eq_left hn]
    change (y.mapEquiv (e (stdSpace F n) hn)).comp
      (f.val.comp (x.mapEquiv (e (stdSpace F n) hn).symm)) = f.val
    have hf := f.property (e (stdSpace F n) hn).symm
    change f.val.comp (x.mapEquiv (e (stdSpace F n) hn).symm) =
      (y.mapEquiv (e (stdSpace F n) hn).symm).comp f.val at hf
    rw [hf, ← LinearMap.comp_assoc, mapEquiv_comp_symm, LinearMap.id_comp]
  exact ⟨Equiv.ofBijective eval ⟨hinj, hsurj⟩, fun _ => rfl⟩

/-- The Hilbert series `Hilb_x(t) = ∑ₙ dim x(Fⁿ) / |GL(Fⁿ)| · tⁿ`. -/
def hilbertSeries [Fintype F] (x : GLSpecies F k) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (finrank k (x.ev (stdSpace F n)) : ℚ) / Nat.card (GLn F n)

end GLSpecies

/-- `|GL(Fⁿ)| = ℓ^{n(n-1)/2} ∏_{i=1}^n (ℓ^i - 1)`.

**Gap (error, §1.3).** The thesis (§1.3, p. 8) prints
`|GL(Fⁿ)| = ℓ^{n(n-1)/2}/(1-ℓ)ⁿ · ∏_{i=1}^n (1 + ℓ + ⋯ + ℓ^i)`, which is false: for `n = 1` it
gives `(1 + ℓ)/(1 - ℓ)` instead of `ℓ - 1`. We state the correct count
`ℓ^{n(n-1)/2} ∏_{i=1}^n (ℓ^i - 1) = ℓ^{n(n-1)/2} (ℓ - 1)ⁿ ∏_{i=1}^n (1 + ℓ + ⋯ + ℓ^{i-1})`. -/
theorem card_GLn [Fintype F] (n : ℕ) :
    Nat.card (GLn F n) = Fintype.card F ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 1 n, (Fintype.card F ^ i - 1) := by
  let q := Fintype.card F
  have hc : Nat.card (GLn F n) = ∏ i ∈ Finset.range n, (q ^ n - q ^ i) := by
    rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F))).toEquiv,
      Matrix.card_GL_field]
    exact Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i) n
  rw [hc]
  have hfactor : ∀ i ∈ Finset.range n, q ^ n - q ^ i = q ^ i * (q ^ (n - i) - 1) := by
    intro i hi
    have hi' : i ≤ n := Nat.le_of_lt (Finset.mem_range.mp hi)
    rw [Nat.mul_sub_left_distrib, ← pow_add, Nat.add_sub_of_le hi', mul_one]
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]
  congr 1
  refine Finset.prod_bij (fun i _ => n - i) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i hi j hj h
    simp only [Finset.mem_range] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    exact ⟨n - j, Finset.mem_range.mpr (by omega), by omega⟩


end Species
end MartinPhd

end
end Monoidal

section Injectives

open CategoryTheory Module
open scoped BigOperators TensorProduct DirectSum

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

noncomputable section
namespace MartinPhd
namespace GLSpecies
variable {F k : Type} [Field F] [Field k]
attribute [local instance] Classical.propDecidable

/-- The Cauchy product is additive in either argument. -/
instance : MonoidalPreadditive (GLSpecies F k) where
  whiskerLeft_zero {X Y Z} := by
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    change cauchyHomMap (𝟙 X) (0 : Y ⟶ Z) V.of = 0
    apply pair_ext
    intro S a b
    change cauchyHomMap (𝟙 X) (0 : Y ⟶ Z) V.of (pair X Y V.of S a b) = 0
    simp [cauchyHomMap, pair]
  zero_whiskerRight {X Y Z} := by
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    change cauchyHomMap (0 : Y ⟶ Z) (𝟙 X) V.of = 0
    apply pair_ext
    intro S a b
    change cauchyHomMap (0 : Y ⟶ Z) (𝟙 X) V.of (pair Y X V.of S a b) = 0
    simp [cauchyHomMap, pair]
  whiskerLeft_add {X Y Z} f g := by
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    change cauchyHomMap (𝟙 X) (f + g) V.of =
      cauchyHomMap (𝟙 X) f V.of + cauchyHomMap (𝟙 X) g V.of
    apply pair_ext
    intro S a b
    change cauchyHomMap (𝟙 X) (f + g) V.of (pair X Y V.of S a b) =
      cauchyHomMap (𝟙 X) f V.of (pair X Y V.of S a b) +
        cauchyHomMap (𝟙 X) g V.of (pair X Y V.of S a b)
    simp [cauchyHomMap, pair, TensorProduct.tmul_add]
  add_whiskerRight {X Y Z} f g := by
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    change cauchyHomMap (f + g) (𝟙 X) V.of =
      cauchyHomMap f (𝟙 X) V.of + cauchyHomMap g (𝟙 X) V.of
    apply pair_ext
    intro S a b
    change cauchyHomMap (f + g) (𝟙 X) V.of (pair Y X V.of S a b) =
      cauchyHomMap f (𝟙 X) V.of (pair Y X V.of S a b) +
        cauchyHomMap g (𝟙 X) V.of (pair Y X V.of S a b)
    simp [cauchyHomMap, pair, TensorProduct.add_tmul]

/-- Inclusion of a homogeneous truncation into the original species. -/
def truncι (x : GLSpecies F k) (n : ℕ) : x.trunc n ⟶ x where
  app V := ModuleCat.ofHom (if finrank F V.of = n then ⊤ else ⊥ : Submodule k (x.obj V)).subtype
  naturality {V W} φ := by ext v; rfl

/-- A homogeneous truncation is concentrated in its indicated dimension. -/
theorem trunc_concentrated (x : GLSpecies F k) (n : ℕ) : (x.trunc n).IsConcentrated n := by
  intro V h
  change Subsingleton ↥(if finrank F V = n then ⊤ else ⊥ : Submodule k (x.ev V))
  rw [ite_eq_right h]
  infer_instance

/-- Reassemble a family of maps out of homogeneous truncations. Only the
component indexed by the dimension of the input space contributes. -/
def assemble {x y : GLSpecies F k} (f : ∀ n, x.trunc n ⟶ y) : x ⟶ y where
  app V := (truncπ x (finrank F V.of)).app V ≫ (f (finrank F V.of)).app V
  naturality {V W} a := by
    have hd := LinearEquiv.finrank_eq (FGModuleCat.isoToLinearEquiv a.iso)
    change x.map a ≫ ((truncπ x (finrank F W.of)).app W ≫ (f (finrank F W.of)).app W) =
      ((truncπ x (finrank F V.of)).app V ≫ (f (finrank F V.of)).app V) ≫ y.map a
    rw [← hd, ← Category.assoc, (truncπ x (finrank F V.of)).naturality a,
      Category.assoc, (f (finrank F V.of)).naturality a, Category.assoc]

/-- A morphism of species is determined by its values on the standard spaces. -/
theorem hom_ext_standard {x y : GLSpecies F k} (f g : x ⟶ y)
    (h : ∀ n, f.app ⟨stdSpace F n⟩ = g.app ⟨stdSpace F n⟩) : f = g := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  let e : stdSpace F (finrank F V.of) ≃ₗ[F] V.of :=
    LinearEquiv.ofFinrankEq (R := F) _ _ (by simp)
  have transport (f : x ⟶ y) : (f.app V).hom =
      (y.mapEquiv e).comp ((f.app ⟨stdSpace F (finrank F V.of)⟩).hom.comp (x.mapEquiv e.symm)) := by
    symm
    rw [← LinearMap.comp_assoc, ← mapEquiv_naturality, LinearMap.comp_assoc,
      mapEquiv_comp_symm, LinearMap.comp_id]
  rw [transport f, transport g, h]

/-- Maschke's theorem gives an equivariant retraction at every standard space. -/
theorem standard_retraction [Finite F] [CharZero k] {x y : GLSpecies F k}
    (f : x ⟶ y) [Mono f] (n : ℕ) :
    ∃ r : y.ev (stdSpace F n) →ₗ[k] x.ev (stdSpace F n),
      (∀ g, r.comp (y.rep n g) = (x.rep n g).comp r) ∧
        r.comp (f.app ⟨stdSpace F n⟩).hom = LinearMap.id := by
  have : Finite (GLn F n) := Finite.of_injective
    (fun e : GLn F n => (e : (Fin n → F) → (Fin n → F))) DFunLike.coe_injective
  let i : Representation.IntertwiningMap (x.rep n) (y.rep n) :=
    ⟨(f.app ⟨stdSpace F n⟩).hom, fun g =>
      mapEquiv_naturality f (V := stdSpace F n) (W := stdSpace F n) g⟩
  let im := Representation.IntertwiningMap.equivLinearMapAsModule (x.rep n) (y.rep n) i
  have hi : Function.Injective im := by
    change Function.Injective (f.app ⟨stdSpace F n⟩).hom
    exact (ModuleCat.mono_iff_injective _).mp
      (((NatTrans.mono_iff_mono_app f).mp (inferInstance : Mono f)) _)
  obtain ⟨r, hr⟩ := MonoidAlgebra.exists_leftInverse_of_injective im (LinearMap.ker_eq_bot.mpr hi)
  let ri := (Representation.IntertwiningMap.equivLinearMapAsModule (y.rep n) (x.rep n)).symm r
  refine ⟨ri.toLinearMap, ri.isIntertwining', ?_⟩
  ext v
  exact DFunLike.congr_fun hr v

/-- Every monomorphism of GL-species splits in characteristic zero. -/
theorem exists_retraction [Finite F] [CharZero k] {x y : GLSpecies F k}
    (f : x ⟶ y) [Mono f] : ∃ r : y ⟶ x, f ≫ r = 𝟙 x := by
  choose r heqv hr using standard_retraction f
  have hfs : ∀ n, ∃ g : y.trunc n ⟶ x,
      (g.app ⟨stdSpace F n⟩).hom = (r n).comp ((truncι y n).app ⟨stdSpace F n⟩).hom := by
    intro n
    obtain ⟨e, he⟩ := hom_concentrated_equiv (y.trunc n) x n (trunc_concentrated y n)
    let u : {u : (y.trunc n).ev (stdSpace F n) →ₗ[k] x.ev (stdSpace F n) //
        ∀ g, u.comp ((y.trunc n).rep n g) = (x.rep n g).comp u} :=
      ⟨(r n).comp ((truncι y n).app ⟨stdSpace F n⟩).hom, fun g => by
        have hi := mapEquiv_naturality (truncι y n) (V := stdSpace F n) (W := stdSpace F n) g
        change ((truncι y n).app ⟨stdSpace F n⟩).hom.comp ((y.trunc n).rep n g) =
          (y.rep n g).comp ((truncι y n).app ⟨stdSpace F n⟩).hom at hi
        change (r n).comp (((truncι y n).app ⟨stdSpace F n⟩).hom.comp ((y.trunc n).rep n g)) = _
        rw [hi, ← LinearMap.comp_assoc, heqv n g, LinearMap.comp_assoc]⟩
    refine ⟨e.symm u, ?_⟩
    have h := he (e.symm u)
    rw [e.apply_symm_apply] at h
    exact h.symm
  choose fs hfs using hfs
  refine ⟨assemble fs, ?_⟩
  apply hom_ext_standard
  intro n
  apply ModuleCat.hom_ext
  have hn : finrank F (stdSpace F n) = n := by simp
  change ((fs (finrank F (stdSpace F n))).app ⟨stdSpace F n⟩).hom.comp
    (((truncπ y (finrank F (stdSpace F n))).app ⟨stdSpace F n⟩).hom.comp
      (f.app ⟨stdSpace F n⟩).hom) = LinearMap.id
  rw [hn, hfs]
  have hιπ : ((truncι y n).app ⟨stdSpace F n⟩).hom.comp
      ((truncπ y n).app ⟨stdSpace F n⟩).hom = LinearMap.id := by
    ext v
    simp only [truncι, truncπ, dite_eq_left hn]
    rfl
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (f.app ⟨stdSpace F n⟩).hom
    ((truncπ y n).app ⟨stdSpace F n⟩).hom ((truncι y n).app ⟨stdSpace F n⟩).hom,
    hιπ, LinearMap.id_comp]
  exact hr n

/-- In characteristic zero every GL-species is injective. -/
instance injective [Finite F] [CharZero k] (x : GLSpecies F k) : Injective x where
  factors g f _ := by
    obtain ⟨r, hr⟩ := exists_retraction f
    exact ⟨r ≫ g, by rw [← Category.assoc, hr, Category.id_comp]⟩

end GLSpecies

open CategoryTheory.Limits

/-- An additive functor out of a semisimple abelian category preserves finite
limits, since every short exact sequence splits. -/
theorem preservesFiniteLimits_of_all_injective
    {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    [∀ X : C, Injective X] (F : C ⥤ D) [F.Additive] : PreservesFiniteLimits F := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  let s := hS.splittingOfInjective.map F
  exact ⟨s.exact, s.mono_f⟩

/-- A comonad preserving finite limits inherits enough injectives from its base. -/
theorem enoughInjectives_coalgebra_of_preservesFiniteLimits
    {C : Type*} [Category* C] [HasFiniteLimits C] [EnoughInjectives C]
    (T : Comonad C) [PreservesFiniteLimits T.toFunctor] :
    EnoughInjectives (Comonad.Coalgebra T) := by
  have : PreservesFiniteLimits (Comonad.forget T) := ⟨fun J _ _ => by infer_instance⟩
  exact EnoughInjectives.of_adjunction T.adj

/-- Coalgebras for an additive comonad on a semisimple abelian category have
enough injectives. The forgetful functor creates finite limits and its right
adjoint sends injectives to injectives. -/
theorem enoughInjectives_coalgebra
    {C : Type*} [Category* C] [Abelian C] [∀ X : C, Injective X]
    (T : Comonad C) [T.toFunctor.Additive] : EnoughInjectives (Comonad.Coalgebra T) := by
  have : PreservesFiniteLimits T.toFunctor := preservesFiniteLimits_of_all_injective T.toFunctor
  have : EnoughInjectives C := ⟨fun X => ⟨{ J := X, f := 𝟙 X }⟩⟩
  have : PreservesFiniteLimits (Comonad.forget T) := ⟨fun J _ _ => by infer_instance⟩
  exact EnoughInjectives.of_adjunction T.adj

end MartinPhd

end
end Injectives

section Comodules

open scoped BigOperators TensorProduct DirectSum
open CategoryTheory Module

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

noncomputable section
namespace MartinPhd
section Species
variable {F : Type} [Field F] {k : Type} [Field k]
attribute [local instance] Classical.propDecidable

/-! ### Coalgebras and comodules in `Sp` -/

open MonoidalCategory ComonObj

variable (c : Comon (GLSpecies F k))

/-- A right `c`-comodule in species. -/
structure RightComod where
  X : GLSpecies F k
  coact : X ⟶ X ⊗ c.X
  coact_counit : coact ≫ X ◁ ComonObj.counit (X := c.X) = (ρ_ X).inv
  coact_assoc : coact ≫ X ◁ ComonObj.comul (X := c.X) = coact ≫ coact ▷ c.X ≫ (α_ X c.X c.X).hom

/-- A left `c`-comodule in species. -/
structure LeftComod where
  X : GLSpecies F k
  coact : X ⟶ c.X ⊗ X
  counit_coact : coact ≫ ComonObj.counit (X := c.X) ▷ X = (λ_ X).inv
  coact_assoc : coact ≫ ComonObj.comul (X := c.X) ▷ X ≫ (α_ c.X c.X X).hom = coact ≫ c.X ◁ coact

/-- A `c`-bicomodule in species. -/
structure Bicomod extends RightComod c where
  coactL : X ⟶ c.X ⊗ X
  counit_coactL : coactL ≫ ComonObj.counit (X := c.X) ▷ X = (λ_ X).inv
  coactL_assoc : coactL ≫ ComonObj.comul (X := c.X) ▷ X ≫ (α_ c.X c.X X).hom = coactL ≫ c.X ◁ coactL
  compat : coactL ≫ c.X ◁ coact = coact ≫ coactL ▷ c.X ≫ (α_ c.X X c.X).hom

variable {c}

@[ext] structure RightComod.Hom (M N : RightComod c) where
  hom : M.X ⟶ N.X
  comm : hom ≫ N.coact = M.coact ≫ hom ▷ c.X

@[ext] structure LeftComod.Hom (M N : LeftComod c) where
  hom : M.X ⟶ N.X
  comm : hom ≫ N.coact = M.coact ≫ c.X ◁ hom

@[ext] structure Bicomod.Hom (M N : Bicomod c) where
  hom : M.X ⟶ N.X
  comm : hom ≫ N.coact = M.coact ≫ hom ▷ c.X
  commL : hom ≫ N.coactL = M.coactL ≫ c.X ◁ hom

instance : Category (RightComod c) where
  Hom := RightComod.Hom
  id M := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm, comp_whiskerRight,
      Category.assoc]⟩
  id_comp f := by apply RightComod.Hom.ext; exact Category.id_comp f.hom
  comp_id f := by apply RightComod.Hom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply RightComod.Hom.ext; exact Category.assoc f.hom g.hom h.hom

instance : Category (LeftComod c) where
  Hom := LeftComod.Hom
  id M := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm, whiskerLeft_comp,
      Category.assoc]⟩
  id_comp f := by apply LeftComod.Hom.ext; exact Category.id_comp f.hom
  comp_id f := by apply LeftComod.Hom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply LeftComod.Hom.ext; exact Category.assoc f.hom g.hom h.hom

instance : Category (Bicomod c) where
  Hom := Bicomod.Hom
  id M := ⟨𝟙 _, by simp, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm, comp_whiskerRight,
      Category.assoc], by
    rw [Category.assoc, g.commL, ← Category.assoc, f.commL, whiskerLeft_comp,
      Category.assoc]⟩
  id_comp f := by apply Bicomod.Hom.ext; exact Category.id_comp f.hom
  comp_id f := by apply Bicomod.Hom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply Bicomod.Hom.ext; exact Category.assoc f.hom g.hom h.hom

variable (c)

/-- The forgetful functor `U : comod_c → Sp`. -/
def RightComod.forget : RightComod c ⥤ GLSpecies F k where
  obj M := M.X
  map f := f.hom

/-- The free (cofree) right comodule `y ⊗ c`, with coaction `y ⊗ Δ`. -/
def RightComod.cofree : GLSpecies F k ⥤ RightComod c where
  obj y :=
    { X := y ⊗ c.X
      coact := y ◁ ComonObj.comul (X := c.X) ≫ (α_ y c.X c.X).inv
      coact_counit := by
        rw [Category.assoc, ← associator_inv_naturality_right,
          ← whiskerLeft_comp_assoc, ComonObj.comul_counit]
        monoidal_coherence
      coact_assoc := by
        rw [Category.assoc, ← associator_inv_naturality_right,
          ← whiskerLeft_comp_assoc, ComonObj.comul_assoc]
        simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
        monoidal }
  map f := ⟨f ▷ c.X, by
    dsimp
    simp only [← Category.assoc, ← whisker_exchange]
    simp⟩
  map_id y := by apply RightComod.Hom.ext; exact id_whiskerRight _ _
  map_comp f g := by apply RightComod.Hom.ext; exact comp_whiskerRight _ _ _

private theorem RightComod.lift_comm (M : RightComod c) (y : GLSpecies F k)
    (ψ : M.X ⟶ y) :
    (M.coact ≫ ψ ▷ c.X) ≫ (y ◁ ComonObj.comul (X := c.X) ≫
      (α_ y c.X c.X).inv) = M.coact ≫ (M.coact ≫ ψ ▷ c.X) ▷ c.X := by
  rw [Category.assoc, ← whisker_exchange_assoc, ← Category.assoc, M.coact_assoc]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_naturality_left_assoc]
  simp

private theorem RightComod.counit_lift (M : RightComod c) (y : GLSpecies F k)
    (ψ : M.X ⟶ y) :
    (M.coact ≫ ψ ▷ c.X) ≫ y ◁ ComonObj.counit (X := c.X) ≫ (ρ_ y).hom = ψ := by
  rw [Category.assoc, ← whisker_exchange_assoc, ← Category.assoc M.coact,
    M.coact_counit]
  simp

private theorem RightComod.lift_counit (M : RightComod c) (y : GLSpecies F k)
    (f : M.X ⟶ y ⊗ c.X)
    (hf : f ≫ (y ◁ ComonObj.comul (X := c.X) ≫ (α_ y c.X c.X).inv) =
      M.coact ≫ f ▷ c.X) :
    M.coact ≫ (f ≫ y ◁ ComonObj.counit (X := c.X) ≫ (ρ_ y).hom) ▷ c.X = f := by
  simp only [comp_whiskerRight]
  rw [← Category.assoc, ← hf]
  simp only [Category.assoc]
  rw [← associator_inv_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    ComonObj.counit_comul]
  monoidal

/-- **Proposition 1.4.** `U ⊣ (− ⊗ c)`: the bijection
`Hom_c(M, y ⊗ c) ≅ Hom_Sp(U M, y)` is `φ ↦ (id_y ⊗ ε) φ`, with inverse `ψ ↦ (ψ ⊗ id_c) ρ`. -/
def RightComod.adj : RightComod.forget c ⊣ RightComod.cofree c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M y =>
        { toFun := fun ψ => ⟨M.coact ≫ ψ ▷ c.X, RightComod.lift_comm c M y ψ⟩
          invFun := fun φ => φ.hom ≫ y ◁ ComonObj.counit (X := c.X) ≫ (ρ_ y).hom
          left_inv := fun ψ => RightComod.counit_lift c M y ψ
          right_inv := fun φ => RightComod.Hom.ext (RightComod.lift_counit c M y φ.hom φ.comm) }
      homEquiv_naturality_left_symm := by
        intros
        rfl
      homEquiv_naturality_right := by
        intros
        apply RightComod.Hom.ext
        change _ ≫ (_ ≫ _) ▷ c.X = (_ ≫ _ ▷ c.X) ≫ _ ▷ c.X
        rw [comp_whiskerRight, Category.assoc] }

/-- The comonad associated to the cofree right-comodule adjunction. -/
def RightComod.comonad : Comonad (GLSpecies F k) where
  toFunctor := tensorRight c.X
  «ε» := (RightComod.adj c).toComonad.ε
  «δ» := (RightComod.adj c).toComonad.δ
  coassoc := (RightComod.adj c).toComonad.coassoc
  left_counit := (RightComod.adj c).toComonad.left_counit
  right_counit := (RightComod.adj c).toComonad.right_counit

instance : (RightComod.forget c).Faithful where
  map_injective h := RightComod.Hom.ext h

@[simp] theorem RightComod.comonad_counit (x : GLSpecies F k) :
    (RightComod.comonad c).ε.app x = x ◁ ComonObj.counit (X := c.X) ≫ (ρ_ x).hom := rfl

@[simp] theorem RightComod.comonad_comul (x : GLSpecies F k) :
    (RightComod.comonad c).δ.app x = x ◁ ComonObj.comul (X := c.X) ≫ (α_ x c.X c.X).inv := by
  change (x ◁ ComonObj.comul (X := c.X) ≫ (α_ x c.X c.X).inv) ≫ (𝟙 (x ⊗ c.X)) ▷ c.X = _
  simp

@[simp] theorem RightComod.comparison_coact (M : RightComod c) :
    ((Comonad.comparison (RightComod.adj c)).obj M).a = M.coact := by
  change M.coact ≫ (𝟙 M.X) ▷ c.X = M.coact
  simp

instance : (Comonad.comparison (RightComod.adj c)).Full where
  map_surjective {M N} f := by
    have h := f.h
    change ((Comonad.comparison (RightComod.adj c)).obj M).a ≫ f.f ▷ c.X =
      f.f ≫ ((Comonad.comparison (RightComod.adj c)).obj N).a at h
    refine ⟨⟨f.f, ?_⟩, ?_⟩
    · simpa only [RightComod.comparison_coact] using h.symm
    · apply Comonad.Coalgebra.Hom.ext
      rfl

instance : (Comonad.comparison (RightComod.adj c)).EssSurj where
  mem_essImage A := by
    let M : RightComod c :=
      { X := A.A
        coact := A.a
        coact_counit := by
          have h := A.counit
          change A.a ≫ (RightComod.comonad c).ε.app A.A = 𝟙 A.A at h
          rw [RightComod.comonad_counit] at h
          apply (cancel_mono (ρ_ A.A).hom).mp
          simpa only [Category.assoc, Iso.inv_hom_id] using h
        coact_assoc := by
          have h := A.coassoc
          change A.a ≫ (RightComod.comonad c).δ.app A.A = A.a ≫ A.a ▷ c.X at h
          rw [RightComod.comonad_comul] at h
          apply (cancel_mono (α_ A.A c.X c.X).inv).mp
          simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h }
    refine ⟨M, ⟨Comonad.Coalgebra.isoMk (Iso.refl A.A) ?_⟩⟩
    change ((Comonad.comparison (RightComod.adj c)).obj M).a ≫
      (RightComod.comonad c).map (𝟙 A.A) = 𝟙 A.A ≫ A.a
    rw [RightComod.comparison_coact]
    change M.coact ≫ (𝟙 A.A) ▷ c.X = 𝟙 A.A ≫ A.a
    simp only [id_whiskerRight, Category.id_comp]
    rfl

instance : (RightComod.comonad c).toFunctor.Additive := by
  change (tensorRight c.X).Additive
  infer_instance

instance : (Comonad.comparison (RightComod.adj c)).IsEquivalence where

/-- The comonad `c ⊗ -` associated with a coalgebra. -/
def LeftComod.comonad : Comonad (GLSpecies F k) where
  toFunctor := tensorLeft c.X
  «ε» :=
    { app := fun x => ComonObj.counit (X := c.X) ▷ x ≫ (λ_ x).hom
      naturality := by
        intro x y f
        dsimp
        rw [whisker_exchange_assoc, leftUnitor_naturality]
        rfl }
  «δ» :=
    { app := fun x => ComonObj.comul (X := c.X) ▷ x ≫ (α_ c.X c.X x).hom
      naturality := by
        intro x y f
        dsimp
        rw [whisker_exchange_assoc, associator_naturality_right]
        rfl }
  coassoc x := by
    dsimp
    simp only [Category.assoc]
    rw [← associator_naturality_left_assoc, ← comp_whiskerRight_assoc,
      ComonObj.comul_assoc_flip]
    simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    monoidal
  left_counit x := by
    dsimp
    rw [Category.assoc, ← associator_naturality_left_assoc, ← comp_whiskerRight_assoc,
      ComonObj.counit_comul]
    monoidal
  right_counit x := by
    dsimp
    rw [whiskerLeft_comp, Category.assoc, ← associator_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, ComonObj.comul_counit]
    monoidal

/-- Left comodules are precisely coalgebras for the comonad `c ⊗ -`. -/
def LeftComod.toCoalgebra : LeftComod c ⥤ Comonad.Coalgebra (LeftComod.comonad c) where
  obj M :=
    { A := M.X
      a := M.coact
      counit := by
        change M.coact ≫ (ComonObj.counit (X := c.X) ▷ M.X ≫ (λ_ M.X).hom) = _
        rw [← Category.assoc, M.counit_coact, Iso.inv_hom_id]
      coassoc := M.coact_assoc }
  map f := ⟨f.hom, f.comm.symm⟩

instance : (LeftComod.toCoalgebra c).Faithful where
  map_injective h := LeftComod.Hom.ext (congrArg Comonad.Coalgebra.Hom.f h)

instance : (LeftComod.toCoalgebra c).Full where
  map_surjective f := ⟨⟨f.f, f.h.symm⟩, by apply Comonad.Coalgebra.Hom.ext; rfl⟩

instance : (LeftComod.toCoalgebra c).EssSurj where
  mem_essImage A := by
    let M : LeftComod c :=
      { X := A.A
        coact := A.a
        counit_coact := by
          apply (cancel_mono (λ_ A.A).hom).mp
          have h := A.counit
          change A.a ≫ (ComonObj.counit (X := c.X) ▷ A.A ≫ (λ_ A.A).hom) = 𝟙 A.A at h
          simpa only [Category.assoc, Iso.inv_hom_id] using h
        coact_assoc := A.coassoc }
    exact ⟨M, ⟨Comonad.Coalgebra.isoMk (Iso.refl A.A) (by simp [LeftComod.toCoalgebra, M])⟩⟩

instance : (LeftComod.toCoalgebra c).IsEquivalence where

instance : (LeftComod.comonad c).toFunctor.Additive :=
  inferInstanceAs (tensorLeft c.X).Additive

/-- The forgetful functor from left comodules to species. -/
def LeftComod.forget : LeftComod c ⥤ GLSpecies F k :=
  LeftComod.toCoalgebra c ⋙ Comonad.forget (LeftComod.comonad c)

/-- **Corollary 1.5.** The categories of left, right and bi-comodules over a coalgebra
`c` in species have enough injectives (`char k = 0`, so `Hom_Sp(−, y)` is exact). -/
theorem RightComod.enoughInjectives [Finite F] [CharZero k] : EnoughInjectives (RightComod c) := by
  have : EnoughInjectives (Comonad.Coalgebra (RightComod.adj c).toComonad) :=
    enoughInjectives_coalgebra (RightComod.comonad c)
  exact EnoughInjectives.of_equivalence (Comonad.comparison (RightComod.adj c))

theorem LeftComod.enoughInjectives [Finite F] [CharZero k] : EnoughInjectives (LeftComod c) := by
  have : EnoughInjectives (Comonad.Coalgebra (LeftComod.comonad c)) :=
    enoughInjectives_coalgebra (LeftComod.comonad c)
  exact EnoughInjectives.of_equivalence (LeftComod.toCoalgebra c)


end Species
end MartinPhd

end
end Comodules

section Chapter1Section2

open scoped BigOperators TensorProduct DirectSum
open CategoryTheory Module MonoidalCategory ComonObj

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

noncomputable section
namespace MartinPhd
section Species
variable {F : Type} [Field F] {k : Type} [Field k]
variable (c : Comon (GLSpecies F k))
attribute [local instance] Classical.propDecidable

open CategoryTheory.Limits

instance [Finite F] [CharZero k] : PreservesFiniteLimits (LeftComod.comonad c).toFunctor :=
  preservesFiniteLimits_of_all_injective (LeftComod.comonad c).toFunctor

instance [Finite F] [CharZero k] : PreservesFiniteLimits (Comonad.forget (LeftComod.comonad c)) :=
  ⟨fun J _ _ => by infer_instance⟩

instance [Finite F] [CharZero k] : HasFiniteLimits (Comonad.Coalgebra (LeftComod.comonad c)) :=
  ⟨fun _ _ _ => hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (Comonad.forget (LeftComod.comonad c))⟩

instance [Finite F] [CharZero k] : HasFiniteLimits (LeftComod c) :=
  ⟨fun _ _ _ => Adjunction.hasLimitsOfShape_of_equivalence (LeftComod.toCoalgebra c)⟩

instance [Finite F] [CharZero k] : PreservesFiniteLimits (LeftComod.forget c) := by
  dsimp only [LeftComod.forget]
  infer_instance

instance : (LeftComod.forget c).ReflectsIsomorphisms := by
  dsimp only [LeftComod.forget]
  infer_instance

instance [Finite F] [CharZero k] : ReflectsFiniteLimits (LeftComod.forget c) :=
  ⟨fun _ _ _ => reflectsLimitsOfShape_of_reflectsIsomorphisms⟩

/-- Tensoring on the right lifts to the category of left comodules. -/
def Bicomod.rightTensor : LeftComod c ⥤ LeftComod c where
  obj M :=
    { X := M.X ⊗ c.X
      coact := M.coact ▷ c.X ≫ (α_ c.X M.X c.X).hom
      counit_coact := by
        rw [Category.assoc, ← associator_naturality_left,
          ← comp_whiskerRight_assoc, M.counit_coact]
        monoidal_coherence
      coact_assoc := by
        have h : M.coact ≫ ComonObj.comul (X := c.X) ▷ M.X =
            M.coact ≫ c.X ◁ M.coact ≫ (α_ c.X c.X M.X).inv := by
          apply (cancel_mono (α_ c.X c.X M.X).hom).mp
          simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using M.coact_assoc
        simp only [Category.assoc]
        rw [← associator_naturality_left_assoc, ← comp_whiskerRight_assoc, h]
        simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
        monoidal }
  map f := ⟨f.hom ▷ c.X, by
    dsimp
    rw [← Category.assoc, ← comp_whiskerRight, f.comm, comp_whiskerRight,
      Category.assoc, associator_naturality_middle]
    simp only [Category.assoc]⟩
  map_id M := by apply LeftComod.Hom.ext; exact id_whiskerRight _ _
  map_comp f g := by apply LeftComod.Hom.ext; exact comp_whiskerRight _ _ _

/-- The right coaction comonad lifted to left comodules. Its coalgebras carry
commuting left and right coactions, hence are bicomodules. -/
def Bicomod.comonad : Comonad (LeftComod c) where
  toFunctor := Bicomod.rightTensor c
  «ε» :=
    { app := fun M => ⟨(RightComod.comonad c).ε.app M.X, by
        have h := (RightComod.comonad c).ε.naturality M.coact
        change (M.coact ▷ c.X) ≫
            ((c.X ⊗ M.X) ◁ ComonObj.counit (X := c.X) ≫ (ρ_ (c.X ⊗ M.X)).hom) =
          (M.X ◁ ComonObj.counit (X := c.X) ≫ (ρ_ M.X).hom) ≫ M.coact at h
        change (M.X ◁ ComonObj.counit (X := c.X) ≫ (ρ_ M.X).hom) ≫ M.coact =
          (M.coact ▷ c.X ≫ (α_ c.X M.X c.X).hom) ≫
            c.X ◁ (M.X ◁ ComonObj.counit (X := c.X) ≫ (ρ_ M.X).hom)
        rw [← h]
        simp only [whiskerLeft_comp, Category.assoc]
        rw [← associator_naturality_right_assoc, ← rightUnitor_tensor_hom]⟩
      naturality := by
        intro M N f
        apply LeftComod.Hom.ext
        exact (RightComod.comonad c).ε.naturality f.hom }
  «δ» :=
    { app := fun M => ⟨(RightComod.comonad c).δ.app M.X, by
        have h := (RightComod.comonad c).δ.naturality M.coact
        change (M.coact ▷ c.X) ≫ (RightComod.comonad c).δ.app (c.X ⊗ M.X) =
          (RightComod.comonad c).δ.app M.X ≫ M.coact ▷ c.X ▷ c.X at h
        change (RightComod.comonad c).δ.app M.X ≫
            ((M.coact ▷ c.X ≫ (α_ c.X M.X c.X).hom) ▷ c.X ≫ (α_ c.X (M.X ⊗ c.X) c.X).hom) =
          (M.coact ▷ c.X ≫ (α_ c.X M.X c.X).hom) ≫
            c.X ◁ (RightComod.comonad c).δ.app M.X
        simp only [comp_whiskerRight, Category.assoc]
        rw [← Category.assoc ((RightComod.comonad c).δ.app M.X) (M.coact ▷ c.X ▷ c.X), ← h]
        simp only [RightComod.comonad_comul, Category.assoc, whiskerLeft_comp]
        monoidal⟩
      naturality := by
        intro M N f
        apply LeftComod.Hom.ext
        exact (RightComod.comonad c).δ.naturality f.hom }
  coassoc M := by
    apply LeftComod.Hom.ext
    exact (RightComod.comonad c).coassoc M.X
  left_counit M := by
    apply LeftComod.Hom.ext
    exact (RightComod.comonad c).left_counit M.X
  right_counit M := by
    apply LeftComod.Hom.ext
    exact (RightComod.comonad c).right_counit M.X

instance [Finite F] [CharZero k] : PreservesFiniteLimits (Bicomod.comonad c).toFunctor := by
  have : PreservesFiniteLimits (tensorRight c.X) :=
    preservesFiniteLimits_of_all_injective (tensorRight c.X)
  have : PreservesFiniteLimits ((Bicomod.comonad c).toFunctor ⋙ LeftComod.forget c) := by
    change PreservesFiniteLimits (LeftComod.forget c ⋙ tensorRight c.X)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (LeftComod.forget c)

/-- Forget only the right coaction of a bicomodule. -/
def Bicomod.left (M : Bicomod c) : LeftComod c :=
  ⟨M.X, M.coactL, M.counit_coactL, M.coactL_assoc⟩

/-- The compatibility of the two coactions says that the right coaction is a
morphism of left comodules. -/
def Bicomod.toCoalgebra : Bicomod c ⥤ Comonad.Coalgebra (Bicomod.comonad c) where
  obj M :=
    { A := Bicomod.left c M
      a := ⟨M.coact, M.compat.symm⟩
      counit := by
        apply LeftComod.Hom.ext
        change M.coact ≫ (RightComod.comonad c).ε.app M.X = 𝟙 M.X
        rw [RightComod.comonad_counit, ← Category.assoc, M.coact_counit, Iso.inv_hom_id]
      coassoc := by
        apply LeftComod.Hom.ext
        change M.coact ≫ (RightComod.comonad c).δ.app M.X = M.coact ≫ M.coact ▷ c.X
        rw [RightComod.comonad_comul, ← Category.assoc, M.coact_assoc]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] }
  map f := ⟨⟨f.hom, f.commL⟩, by apply LeftComod.Hom.ext; exact f.comm.symm⟩
  map_id M := by apply Comonad.Coalgebra.Hom.ext; apply LeftComod.Hom.ext; rfl
  map_comp f g := by apply Comonad.Coalgebra.Hom.ext; apply LeftComod.Hom.ext; rfl

instance : (Bicomod.toCoalgebra c).Faithful where
  map_injective h := Bicomod.Hom.ext (congrArg (fun f => f.f.hom) h)

instance : (Bicomod.toCoalgebra c).Full where
  map_surjective f := by
    refine ⟨⟨f.f.hom, ?_, f.f.comm⟩, ?_⟩
    · exact (congrArg LeftComod.Hom.hom f.h).symm
    · apply Comonad.Coalgebra.Hom.ext
      apply LeftComod.Hom.ext
      rfl

instance : (Bicomod.toCoalgebra c).EssSurj where
  mem_essImage A := by
    let M : Bicomod c :=
      { X := A.A.X
        coact := A.a.hom
        coact_counit := by
          have h := congrArg LeftComod.Hom.hom A.counit
          change A.a.hom ≫ (RightComod.comonad c).ε.app A.A.X = 𝟙 A.A.X at h
          rw [RightComod.comonad_counit] at h
          apply (cancel_mono (ρ_ A.A.X).hom).mp
          simpa only [Category.assoc, Iso.inv_hom_id] using h
        coact_assoc := by
          have h := congrArg LeftComod.Hom.hom A.coassoc
          change A.a.hom ≫ (RightComod.comonad c).δ.app A.A.X = A.a.hom ≫ A.a.hom ▷ c.X at h
          rw [RightComod.comonad_comul] at h
          apply (cancel_mono (α_ A.A.X c.X c.X).inv).mp
          simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
        coactL := A.A.coact
        counit_coactL := A.A.counit_coact
        coactL_assoc := A.A.coact_assoc
        compat := A.a.comm.symm }
    refine ⟨M, ⟨Comonad.Coalgebra.isoMk (Iso.refl A.A) ?_⟩⟩
    apply LeftComod.Hom.ext
    change A.a.hom ≫ (𝟙 A.A.X ▷ c.X) = A.a.hom
    simp only [id_whiskerRight]
    exact Category.comp_id A.a.hom

instance : (Bicomod.toCoalgebra c).IsEquivalence where

theorem Bicomod.enoughInjectives [Finite F] [CharZero k] : EnoughInjectives (Bicomod c) := by
  have : EnoughInjectives (LeftComod c) := LeftComod.enoughInjectives c
  have : EnoughInjectives (Comonad.Coalgebra (Bicomod.comonad c)) :=
    enoughInjectives_coalgebra_of_preservesFiniteLimits (Bicomod.comonad c)
  exact EnoughInjectives.of_equivalence (Bicomod.toCoalgebra c)

end Species

end MartinPhd

end
end Chapter1Section2
