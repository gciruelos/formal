import Mathlib
import ScoccolaPhd.PreliminariesProjectiveChainComplexes
import ScoccolaPhd.Chapter2Section1Metric

/-!
# §§2.4–2.6: enriched categories, model categories, persistent objects

Contents:
* Chapter 2.4: Enriched categories
* Chapter 2.5: Model categories
* Chapter 2.6: Persistent objects
-/

universe w v u v₁ u₁ u₂ v₂ t t'

namespace ScoccolaPhd

/-! ## Chapter 2.4: Enriched categories

Elementary notions come from Mathlib:

| Thesis                                  | Mathlib                                           |
|-----------------------------------------|---------------------------------------------------|
| Def 2.4.1 `V`-category                  | `EnrichedCategory V C`                            |
| Def 2.4.2 change of enrichment          | `TransportEnrichment F C`                         |
| Ex 2.4.3 underlying category `C₀`       | `ForgetEnrichment V C` (or `EnrichedOrdinaryCategory`) |
| Def 2.4.5 `V`-functor                   | `EnrichedFunctor V C D`                           |
| Def 2.4.7 opposite                      | instance `EnrichedCategory V Cᵒᵖ`                 |
| Def 2.4.12 (graded) natural transf.     | `EnrichedNatTrans`                                |

What Mathlib lacks, and what we define here: the `V`-functor category `[C, D]` as a
`V`-category (Def 2.4.12) is *not* constructed; instead the object `Hom_{[C,D]}(F, G)` and the
representable functors needed to phrase weighted limits are taken as the data of the class
`FunctorHoms`; naturality of the isomorphisms defining weighted (co)limits is not recorded. (powers, copowers, weighted (co)limits, Kan extensions: Defs 2.4.13–2.4.15). -/

section Enriched

open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

section

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V]

/-- Data standing for the `V`-functor category `[K, D]` (Definitions 2.4.9–2.4.12): the
`V`-object of natural transformations `Hom_{[K,D]}(F, G) = ∫_k Hom_D(F k, G k)` (only for
`V`-valued functors, which is all that weighted limits need), together with, for `c : D` and
`F : K → D`, the `V`-functors `Hom_D(c, F -) : K → V` and `Hom_D(F -, c) : Kᵒᵖ → V`. -/
class FunctorHoms (K : Type u) [EnrichedCategory V K] (D : Type u₂)
    [EnrichedCategory V D] where
  /-- `Hom_{[K,V]}(W, W')`. -/
  natHom : EnrichedFunctor V K V → EnrichedFunctor V K V → V
  /-- `Hom_{[Kᵒᵖ,V]}(W, W')`. -/
  natHomOp : EnrichedFunctor V Kᵒᵖ V → EnrichedFunctor V Kᵒᵖ V → V
  /-- the `V`-functor `Hom_D(c, F -)`. -/
  homFrom : D → EnrichedFunctor V K D → EnrichedFunctor V K V
  /-- the `V`-functor `Hom_D(F -, c)` on `Kᵒᵖ`. -/
  homTo : D → EnrichedFunctor V K D → EnrichedFunctor V Kᵒᵖ V

end

section

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
  (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- Definition 2.4.13: the copower `k · x`, with `Hom(k · x, y) ≅ [k, Hom(x, y)]`. -/
structure Copower (k : V) (x : C) where
  obj : C
  iso : ∀ y : C, (obj ⟶[V] y) ≅ (ihom k).obj (x ⟶[V] y)

/-- Definition 2.4.13: the power `yᵏ`, with `Hom(x, yᵏ) ≅ [k, Hom(x, y)]`. -/
structure Power (k : V) (y : C) where
  obj : C
  iso : ∀ x : C, (x ⟶[V] obj) ≅ (ihom k).obj (x ⟶[V] y)

/-- Definition 2.4.14: a weighted limit of `F : K → C` with weight `W : K → V`:
`Hom(c, lim_W F) ≅ Hom_{[K,V]}(W, Hom_C(c, F -))`. -/
structure WeightedLimit {K : Type u₂} [EnrichedCategory V K] [FunctorHoms V K C]
    (W : EnrichedFunctor V K V) (F : EnrichedFunctor V K C) where
  obj : C
  iso : ∀ c : C, (c ⟶[V] obj) ≅ FunctorHoms.natHom (K := K) (D := C) W (FunctorHoms.homFrom c F)

/-- Definition 2.4.14: a weighted colimit of `F : K → C` with weight `W : Kᵒᵖ → V`:
`Hom(colim_W F, c) ≅ Hom_{[Kᵒᵖ,V]}(W, Hom_C(F -, c))`. -/
structure WeightedColimit {K : Type u₂} [EnrichedCategory V K] [FunctorHoms V K C]
    (W : EnrichedFunctor V Kᵒᵖ V) (F : EnrichedFunctor V K C) where
  obj : C
  iso : ∀ c : C,
    (obj ⟶[V] c) ≅ FunctorHoms.natHomOp (K := K) (D := C) W (FunctorHoms.homTo c F)

/-- Definition 2.4.14: `C` is complete if it admits all small weighted limits. -/
def IsEnrichedComplete (K : Type u₂) [EnrichedCategory V K] [FunctorHoms V K C] : Prop :=
  ∀ (W : EnrichedFunctor V K V) (F : EnrichedFunctor V K C), Nonempty (WeightedLimit V C W F)

/-- Definition 2.4.14: `C` is cocomplete if it admits all small weighted colimits. -/
def IsEnrichedCocomplete (K : Type u₂) [EnrichedCategory V K] [FunctorHoms V K C] : Prop :=
  ∀ (W : EnrichedFunctor V Kᵒᵖ V) (F : EnrichedFunctor V K C),
    Nonempty (WeightedColimit V C W F)

end

section YonedaHelpers

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
  {D : Type u} [Category.{v} D] [EnrichedOrdinaryCategory V D]

lemma eHomEquiv_comp_whisker {X X' Y : D} (f : X ⟶ X') (g : X' ⟶ Y) :
    eHomEquiv V (f ≫ g) = eHomEquiv V g ≫ eHomWhiskerRight V f Y := by
  rw [eHomEquiv_comp]
  simp only [eHomWhiskerRight]
  rw [← Category.assoc (eHomEquiv V g), leftUnitor_inv_naturality]
  simp only [Category.assoc, MonoidalCategory.tensorHom_def, whisker_exchange_assoc]

lemma eHomEquiv_comp_whiskerL {X Y Y' : D} (f : X ⟶ Y) (g : Y ⟶ Y') :
    eHomEquiv V (f ≫ g) = eHomEquiv V f ≫ eHomWhiskerLeft V X g := by
  rw [eHomEquiv_comp]
  simp only [eHomWhiskerLeft]
  rw [← Category.assoc (eHomEquiv V f), rightUnitor_inv_naturality, unitors_inv_equal]
  simp only [Category.assoc, MonoidalCategory.tensorHom_def]

/-- Yoneda for enriched ordinary categories: a family of `V`-isos `(d ⟶[V] A) ≅ (d ⟶[V] B)`
natural in `d` (w.r.t. underlying morphisms) gives `A ≅ B`. -/
noncomputable def isoOfEnrichedHomIso {A B : D} (φ : ∀ d : D, (d ⟶[V] A) ≅ (d ⟶[V] B))
    (hnat : ∀ {d d' : D} (f : d ⟶ d'),
      eHomWhiskerRight V f A ≫ (φ d).hom = (φ d').hom ≫ eHomWhiskerRight V f B) : A ≅ B :=
  Yoneda.fullyFaithful.preimageIso (NatIso.ofComponents (fun d =>
    Equiv.toIso (X := (d.unop ⟶ A)) (Y := (d.unop ⟶ B))
    { toFun := fun g => (eHomEquiv V).symm (eHomEquiv V g ≫ (φ d.unop).hom)
      invFun := fun g => (eHomEquiv V).symm (eHomEquiv V g ≫ (φ d.unop).inv)
      left_inv := fun g => by simp
      right_inv := fun g => by simp })
    (fun {d d'} f => by
      ext g
      simp only [yoneda_obj_map]
      show (eHomEquiv V).symm (eHomEquiv V (f.unop ≫ g) ≫ (φ d'.unop).hom) =
        f.unop ≫ (eHomEquiv V).symm (eHomEquiv V g ≫ (φ d.unop).hom)
      apply (eHomEquiv V).injective
      rw [Equiv.apply_symm_apply, eHomEquiv_comp_whisker, Category.assoc, hnat f.unop,
        eHomEquiv_comp_whisker]
      rw [Equiv.apply_symm_apply, Category.assoc]))

/-- Co-Yoneda version of `isoOfEnrichedHomIso`. -/
noncomputable def isoOfEnrichedHomIso' {A B : D} (φ : ∀ d : D, (A ⟶[V] d) ≅ (B ⟶[V] d))
    (hnat : ∀ {d d' : D} (f : d ⟶ d'),
      eHomWhiskerLeft V A f ≫ (φ d').hom = (φ d).hom ≫ eHomWhiskerLeft V B f) : A ≅ B :=
  ((Coyoneda.fullyFaithful.preimageIso (NatIso.ofComponents (fun d =>
    Equiv.toIso (X := (A ⟶ d)) (Y := (B ⟶ d))
    { toFun := fun g => (eHomEquiv V).symm (eHomEquiv V g ≫ (φ d).hom)
      invFun := fun g => (eHomEquiv V).symm (eHomEquiv V g ≫ (φ d).inv)
      left_inv := fun g => by simp
      right_inv := fun g => by simp })
    (fun {d d'} f => by
      ext g
      show (eHomEquiv V).symm (eHomEquiv V (g ≫ f) ≫ (φ d').hom) =
        (eHomEquiv V).symm (eHomEquiv V g ≫ (φ d).hom) ≫ f
      apply (eHomEquiv V).injective
      rw [Equiv.apply_symm_apply, eHomEquiv_comp_whiskerL, eHomEquiv_comp_whiskerL,
        Equiv.apply_symm_apply, Category.assoc, hnat f, Category.assoc]) :
      coyoneda.obj (Opposite.op A) ≅ coyoneda.obj (Opposite.op B))).unop).symm

end YonedaHelpers

section KanExtensions

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
  {C : Type u₂} [EnrichedCategory V C] {C' : Type u₂} [EnrichedCategory V C']
  {D : Type u} [Category.{v} D] [EnrichedOrdinaryCategory V D]
  [FunctorHoms V C D] [FunctorHoms V C C']

/-- Definition 2.4.15: the pointwise right Kan extension of `F` along `G` at `c'` is the
weighted limit of `F` with weight `Hom_{C'}(c', G -)`. -/
abbrev PointwiseRan (G : EnrichedFunctor V C C') (F : EnrichedFunctor V C D) (c' : C') :=
  WeightedLimit V D (FunctorHoms.homFrom (K := C) (D := C') c' G) F

/-- Definition 2.4.15: the pointwise left Kan extension of `F` along `G` at `c'` is the
weighted colimit of `F` with weight `Hom_{C'}(G -, c')`. -/
abbrev PointwiseLan (G : EnrichedFunctor V C C') (F : EnrichedFunctor V C D) (c' : C') :=
  WeightedColimit V D (FunctorHoms.homTo (K := C) (D := C') c' G) F

/-- A `V`-functor is fully faithful if each `G x y : Hom x y → Hom (G x) (G y)` is an
isomorphism in `V`. -/
def IsFullyFaithfulEnriched {C : Type u₂} [EnrichedCategory V C] {C' : Type u₂}
    [EnrichedCategory V C'] (G : EnrichedFunctor V C C') : Prop :=
  ∀ x y : C, IsIso (G.map x y)

/-- Additional laws on `FunctorHoms` needed for the right Kan extension along a fully faithful
functor (Proposition 2.4.16).

In the thesis, `Ran_G F (G c)` is defined as the weighted limit with weight
`W = Hom_{C'}(G c, G -)`. When `G` is fully faithful, `W` is isomorphic to the representable
weight `Hom_C(c, -)`. By the enriched Yoneda lemma,
`natHom (Hom_C(c, -)) (Hom_D(d, F -)) ≅ Hom_D(d, F c)`.
Since `FunctorHoms` carries only unaxiomatized data, these relationships must be supplied
as hypotheses. -/
structure RanCompLaws (G : EnrichedFunctor V C C') (F : EnrichedFunctor V C D) (c : C) where
  /-- The representable weight `Hom_C(c, -) : C → V`. -/
  repHom : EnrichedFunctor V C V
  /-- Enriched Yoneda: `natHom (Hom_C(c, -)) W ≅ W c` for any weight `W`. -/
  yoneda : ∀ W : EnrichedFunctor V C V,
    FunctorHoms.natHom (K := C) (D := D) repHom W ≅ W.obj c
  /-- Full faithfulness compatibility: since `G` is fully faithful, the weight
  `Hom_{C'}(G c, G -)` is isomorphic to `Hom_C(c, -)`, inducing an isomorphism on `natHom`. -/
  ff_compat : ∀ W : EnrichedFunctor V C V,
    FunctorHoms.natHom (K := C) (D := D)
      (FunctorHoms.homFrom (K := C) (D := C') (G.obj c) G) W ≅
    FunctorHoms.natHom (K := C) (D := D) repHom W
  /-- Evaluation of `homFrom d F` at `c` is `d ⟶[V] F c`. -/
  homFrom_eval : ∀ d : D,
    (FunctorHoms.homFrom (K := C) (D := D) d F).obj c ≅ (d ⟶[V] F.obj c)

/-- Under the enriched Yoneda and full-faithfulness laws, the enriched hom
`d ⟶[V] (Ran_G F)(G c)` is isomorphic in `V` to `d ⟶[V] F c`. -/
def ran_comp_enriched_iso (G : EnrichedFunctor V C C') (_hG : IsFullyFaithfulEnriched V G)
    (F : EnrichedFunctor V C D) (ran : ∀ c', PointwiseRan V G F c') (c : C)
    (hLaws : RanCompLaws V G F c) (d : D) :
    (d ⟶[V] (ran (G.obj c)).obj) ≅ (d ⟶[V] F.obj c) :=
  ((ran (G.obj c)).iso d).trans
    ((hLaws.ff_compat (FunctorHoms.homFrom d F)).trans
      ((hLaws.yoneda (FunctorHoms.homFrom d F)).trans
        (hLaws.homFrom_eval d)))

/-- Proposition 2.4.16 (right case): if `G` is fully faithful, then `(Ran_G F)(G c) ≅ F c`.
The isomorphisms of `RanCompLaws` carry no naturality in `d`, so, as `FunctorHoms` does not record it, we assume it as `hnat`; Yoneda then gives the isomorphism. -/
theorem ran_comp_iso (G : EnrichedFunctor V C C') (hG : IsFullyFaithfulEnriched V G)
    (F : EnrichedFunctor V C D) (ran : ∀ c', PointwiseRan V G F c') (c : C)
    (hLaws : RanCompLaws V G F c)
    (hnat : ∀ {d d' : D} (f : d ⟶ d'),
      eHomWhiskerRight V f (ran (G.obj c)).obj ≫
          (ran_comp_enriched_iso V G hG F ran c hLaws d).hom =
        (ran_comp_enriched_iso V G hG F ran c hLaws d').hom ≫ eHomWhiskerRight V f (F.obj c)) :
    Nonempty ((ran (G.obj c)).obj ≅ F.obj c) :=
  ⟨isoOfEnrichedHomIso V (ran_comp_enriched_iso V G hG F ran c hLaws) hnat⟩

/-- Additional laws on `FunctorHoms` needed for the left Kan extension along a fully faithful
functor (Proposition 2.4.16, dual case).

In the thesis, `Lan_G F (G c)` is defined as the weighted colimit with weight
`W = Hom_{C'}(G -, G c)`. When `G` is fully faithful, `W` is isomorphic to the representable
weight `Hom_C(-, c)`. By the enriched co-Yoneda lemma,
`natHomOp (Hom_C(-, c)) (Hom_D(F -, d)) ≅ Hom_D(F c, d)`. -/
structure LanCompLaws (G : EnrichedFunctor V C C') (F : EnrichedFunctor V C D) (c : C) where
  /-- The representable op-weight `Hom_C(-, c) : Cᵒᵖ → V`. -/
  repHomOp : EnrichedFunctor V Cᵒᵖ V
  /-- Enriched co-Yoneda: `natHomOp (Hom_C(-, c)) W ≅ W (op c)` for any weight `W`. -/
  coyoneda : ∀ W : EnrichedFunctor V Cᵒᵖ V,
    FunctorHoms.natHomOp (K := C) (D := D) repHomOp W ≅ W.obj (Opposite.op c)
  /-- Full faithfulness compatibility: since `G` is fully faithful, the weight
  `Hom_{C'}(G -, G c)` is isomorphic to `Hom_C(-, c)`, inducing an isomorphism on `natHomOp`. -/
  ff_compat : ∀ W : EnrichedFunctor V Cᵒᵖ V,
    FunctorHoms.natHomOp (K := C) (D := D)
      (FunctorHoms.homTo (K := C) (D := C') (G.obj c) G) W ≅
    FunctorHoms.natHomOp (K := C) (D := D) repHomOp W
  /-- Evaluation of `homTo d F` at `op c` is `F c ⟶[V] d`. -/
  homTo_eval : ∀ d : D,
    (FunctorHoms.homTo (K := C) (D := D) d F).obj (Opposite.op c) ≅ (F.obj c ⟶[V] d)

/-- Under the enriched co-Yoneda and full-faithfulness laws, the enriched hom
`(Lan_G F)(G c) ⟶[V] d` is isomorphic in `V` to `F c ⟶[V] d`. -/
def lan_comp_enriched_iso (G : EnrichedFunctor V C C') (_hG : IsFullyFaithfulEnriched V G)
    (F : EnrichedFunctor V C D) (lan : ∀ c', PointwiseLan V G F c') (c : C)
    (hLaws : LanCompLaws V G F c) (d : D) :
    ((lan (G.obj c)).obj ⟶[V] d) ≅ (F.obj c ⟶[V] d) :=
  ((lan (G.obj c)).iso d).trans
    ((hLaws.ff_compat (FunctorHoms.homTo d F)).trans
      ((hLaws.coyoneda (FunctorHoms.homTo d F)).trans
        (hLaws.homTo_eval d)))

/-- Proposition 2.4.16 (left case): if `G` is fully faithful, then `F c ≅ (Lan_G F)(G c)`, given naturality `hnat` of the isomorphisms in `d`. -/
theorem lan_comp_iso (G : EnrichedFunctor V C C') (hG : IsFullyFaithfulEnriched V G)
    (F : EnrichedFunctor V C D) (lan : ∀ c', PointwiseLan V G F c') (c : C)
    (hLaws : LanCompLaws V G F c)
    (hnat : ∀ {d d' : D} (f : d ⟶ d'),
      eHomWhiskerLeft V (lan (G.obj c)).obj f ≫
          (lan_comp_enriched_iso V G hG F lan c hLaws d').hom =
        (lan_comp_enriched_iso V G hG F lan c hLaws d).hom ≫ eHomWhiskerLeft V (F.obj c) f) :
    Nonempty ((lan (G.obj c)).obj ≅ F.obj c) :=
  ⟨isoOfEnrichedHomIso' V (lan_comp_enriched_iso V G hG F lan c hLaws) hnat⟩

end KanExtensions

end Enriched

/-! ## Chapter 2.5: Model categories

Formalization of the theory of model categories and weak factorization systems.
Examples 2.5.10 (`Top`) and 2.5.11 (`sSet`) are omitted: they need the
class of weak homotopy equivalences, which Mathlib does not define. -/

section Model

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

/-- Definition 2.5.1: `i` has the left lifting property against `p` is Mathlib's
`HasLiftingProperty i p`. -/
abbrev HasLLP {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) : Prop := HasLiftingProperty i p

/-- Definition 2.5.2: a functorial weak factorization system `(L, R)`: every morphism `f`
factors functorially as `f = π f ∘ ι f` with `ι f ∈ L`, `π f ∈ R`, and each class is
determined by the lifting property against the other.

**Gap (typo).** The thesis states the second condition with "left lifting property" twice;
the right lifting property is meant. -/
structure FunctorialWFS (C : Type u) [Category.{v} C] where
  L : MorphismProperty C
  R : MorphismProperty C
  /-- the middle object of the factorization -/
  mid : Arrow C ⥤ C
  ι : Arrow.leftFunc ⟶ mid
  π : mid ⟶ Arrow.rightFunc
  fac : ∀ f : Arrow C, ι.app f ≫ π.app f = f.hom
  ι_mem : ∀ f : Arrow C, L (ι.app f)
  π_mem : ∀ f : Arrow C, R (π.app f)
  L_eq : L = R.llp
  R_eq : R = L.rlp

/-- Definition 2.5.3: a model structure on `C`. -/
structure ModelStructure (C : Type u) [Category.{v} C] where
  W : MorphismProperty C
  Cof : MorphismProperty C
  Fib : MorphismProperty C
  twoOutOfThree : W.HasTwoOutOfThreeProperty
  wfs₁ : FunctorialWFS C
  wfs₂ : FunctorialWFS C
  wfs₁_L : wfs₁.L = Cof
  wfs₁_R : wfs₁.R = Fib ⊓ W
  wfs₂_L : wfs₂.L = Cof ⊓ W
  wfs₂_R : wfs₂.R = Fib

/-- Definition 2.5.4: a model category is a complete and cocomplete category with a model
structure. -/
structure ModelCategory (C : Type u) [Category.{v} C] where
  hasLimits : HasLimits C
  hasColimits : HasColimits C
  str : ModelStructure C

/-- Definition 2.5.5: `cell(I)`, the transfinite compositions of pushouts of coproducts of
elements of `I`. -/
def cell (I : MorphismProperty C) : MorphismProperty C :=
  I.coproducts.{v}.pushouts.transfiniteCompositions.{v}

/-- Definition 2.5.5: `cof(I)`, the retracts of elements of `cell(I)`. -/
def cof (I : MorphismProperty C) : MorphismProperty C :=
  (cell I).retracts

/-- Definition 2.5.6: a model category is cofibrantly generated by small sets `I`, `J` of
morphisms admitting the small object argument. -/
structure IsCofibrantlyGeneratedBy (M : ModelStructure C) (I J : MorphismProperty C) : Prop where
  small_I : Small.{v} {f : Arrow C // I f.hom}
  small_J : Small.{v} {f : Arrow C // J f.hom}
  cof_I : cof I = M.Cof
  cof_J : cof J = M.Cof ⊓ M.W
  soa_I : I.HasSmallObjectArgument.{v}
  soa_J : J.HasSmallObjectArgument.{v}

/-- Definition 2.5.6. -/
def IsCofibrantlyGenerated (M : ModelStructure C) : Prop :=
  ∃ I J, IsCofibrantlyGeneratedBy M I J

/-- A class of morphisms `I` admitting the small object argument generates a
functorial weak factorization system `(I.rlp.llp, I.rlp)`. -/
noncomputable def functorialWFS_of_hasSmallObjectArgument
    (I : MorphismProperty C) [I.HasSmallObjectArgument.{v}] :
    FunctorialWFS C where
  L := I.rlp.llp
  R := I.rlp
  mid := (functorialFactorizationData I.rlp.llp I.rlp).Z
  ι := (functorialFactorizationData I.rlp.llp I.rlp).i
  π := (functorialFactorizationData I.rlp.llp I.rlp).p
  fac _ := (functorialFactorizationData I.rlp.llp I.rlp).fac_app
  ι_mem _ := (functorialFactorizationData I.rlp.llp I.rlp).hi _
  π_mem _ := (functorialFactorizationData I.rlp.llp I.rlp).hp _
  L_eq := rfl
  R_eq := I.rlp_llp_rlp.symm

/-- In a cocomplete category, `cof I` coincides with `I.rlp.llp` whenever `I` admits the
small object argument. -/
lemma cof_eq_llp_rlp (I : MorphismProperty C) [I.HasSmallObjectArgument.{v}] :
    cof I = I.rlp.llp := by
  dsimp [cof, cell]
  rw [llp_rlp_of_hasSmallObjectArgument]

lemma fib_inf_w_eq_rlp (M : ModelStructure C) (I J : MorphismProperty C)
    (h : IsCofibrantlyGeneratedBy M I J) :
    M.Fib ⊓ M.W = I.rlp := by
  have : I.HasSmallObjectArgument.{v} := h.soa_I
  have h1 : M.Fib ⊓ M.W = M.wfs₁.R := M.wfs₁_R.symm
  rw [h1, M.wfs₁.R_eq, M.wfs₁_L, ← h.cof_I, cof_eq_llp_rlp, rlp_llp_rlp]

lemma fib_eq_rlp (M : ModelStructure C) (I J : MorphismProperty C)
    (h : IsCofibrantlyGeneratedBy M I J) :
    M.Fib = J.rlp := by
  have : J.HasSmallObjectArgument.{v} := h.soa_J
  have h2 : M.Fib = M.wfs₂.R := M.wfs₂_R.symm
  rw [h2, M.wfs₂.R_eq, M.wfs₂_L, ← h.cof_J, cof_eq_llp_rlp, rlp_llp_rlp]

/-- Recognition theorem constructor for a model structure from generating cofibrations `I`
and trivial cofibrations `J` admitting the small object argument (Hovey 2.1.19). -/
noncomputable def ModelStructure.ofCofibrantlyGenerated
    (W Cof Fib I J : MorphismProperty C)
    [hW : W.HasTwoOutOfThreeProperty]
    [I.HasSmallObjectArgument.{v}] [J.HasSmallObjectArgument.{v}]
    (hCof : Cof = I.rlp.llp)
    (hFibW : Fib ⊓ W = I.rlp)
    (hCofW : Cof ⊓ W = J.rlp.llp)
    (hFib : Fib = J.rlp) :
    ModelStructure C where
  W := W
  Cof := Cof
  Fib := Fib
  twoOutOfThree := hW
  wfs₁ := functorialWFS_of_hasSmallObjectArgument I
  wfs₂ := functorialWFS_of_hasSmallObjectArgument J
  wfs₁_L := hCof.symm
  wfs₁_R := hFibW.symm
  wfs₂_L := hCofW.symm
  wfs₂_R := hFib.symm

/-- Definition 2.5.7: the projective weak equivalences (objectwise weak equivalences). -/
def projectiveWeakEquivalences {D : Type*} [Category D] (W : MorphismProperty C) :
    MorphismProperty (D ⥤ C) :=
  fun _ _ α => ∀ d, W (α.app d)

/-- Definition 2.5.7: the projective fibrations (objectwise fibrations). -/
def projectiveFibrations {D : Type*} [Category D] (Fib : MorphismProperty C) :
    MorphismProperty (D ⥤ C) :=
  fun _ _ α => ∀ d, Fib (α.app d)

instance projectiveWeakEquivalences_hasTwoOutOfThree
    {D : Type*} [Category D] (W : MorphismProperty C) [hW : W.HasTwoOutOfThreeProperty] :
    (projectiveWeakEquivalences (D := D) W).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg d := by
    have : (f ≫ g).app d = f.app d ≫ g.app d := rfl
    rw [this]
    exact hW.comp_mem (f.app d) (g.app d) (hf d) (hg d)
  of_postcomp f g hg hfg d := by
    apply hW.of_postcomp (f.app d) (g.app d) (hg d)
    exact hfg d
  of_precomp f g hf hfg d := by
    apply hW.of_precomp (f.app d) (g.app d) (hf d)
    exact hfg d

lemma hasLiftingProperty_evaluationLeftAdjoint_iff
    {D : Type v} [SmallCategory D] [HasColimits C] (d : D)
    {A B : C} (i : A ⟶ B) {X Y : D ⥤ C} (p : X ⟶ Y) :
    HasLiftingProperty ((evaluationLeftAdjoint C d).map i) p ↔
      HasLiftingProperty i (p.app d) :=
  (evaluationAdjunctionRight C d).hasLiftingProperty_iff i p

/-- Generating morphisms in `D ⥤ C` obtained by applying the left Kan extension / copower
functor `evaluationLeftAdjoint C d` to elements of `I`. -/
inductive generatingFunctorCategory {D : Type v} [SmallCategory D] [HasColimits C]
    (I : MorphismProperty C) : MorphismProperty (D ⥤ C)
  | mk (d : D) {A B : C} (i : A ⟶ B) (hi : I i) :
      generatingFunctorCategory I ((evaluationLeftAdjoint C d).map i)

theorem rlp_generatingFunctorCategory {D : Type v} [SmallCategory D] [HasColimits C]
    (I : MorphismProperty C) :
    (generatingFunctorCategory (D := D) I).rlp = (I.rlp).functorCategory D := by
  ext X Y p
  constructor
  · intro hp d A B i hi
    have hlift := hp ((evaluationLeftAdjoint C d).map i) (generatingFunctorCategory.mk d i hi)
    rw [hasLiftingProperty_evaluationLeftAdjoint_iff] at hlift
    exact hlift
  · intro hp A' B' f hf
    induction' hf with d A B i hi
    rw [hasLiftingProperty_evaluationLeftAdjoint_iff]
    exact hp d i hi

lemma functorCategory_inf (D : Type*) [Category D] (P Q : MorphismProperty C) :
    (P ⊓ Q).functorCategory D = P.functorCategory D ⊓ Q.functorCategory D := by
  ext X Y f
  change (∀ j : D, P (f.app j) ∧ Q (f.app j)) ↔ (∀ j : D, P (f.app j)) ∧ (∀ j : D, Q (f.app j))
  exact forall_and

lemma projectiveFibrations_eq_rlp {D : Type v} [SmallCategory D] [HasColimits C]
    (M : ModelStructure C) (I J : MorphismProperty C)
    (h : IsCofibrantlyGeneratedBy M I J) :
    projectiveFibrations (D := D) M.Fib = (generatingFunctorCategory (D := D) J).rlp := by
  change (M.Fib).functorCategory D = _
  rw [fib_eq_rlp M I J h, ← rlp_generatingFunctorCategory]

lemma projectiveTrivialFibrations_eq_rlp {D : Type v} [SmallCategory D] [HasColimits C]
    (M : ModelStructure C) (I J : MorphismProperty C)
    (h : IsCofibrantlyGeneratedBy M I J) :
    projectiveFibrations (D := D) M.Fib ⊓ projectiveWeakEquivalences (D := D) M.W =
      (generatingFunctorCategory (D := D) I).rlp := by
  change (M.Fib).functorCategory D ⊓ (M.W).functorCategory D = _
  rw [← functorCategory_inf, fib_inf_w_eq_rlp M I J h, ← rlp_generatingFunctorCategory]

/-! ### Transfer of the small object argument to functor categories -/

section CellTransfer

/-- Flattening a colimit cofan of coproducts. -/
noncomputable def flattenCofanIsColimit {K : Type w} (T : K → Type w) (Y : K → C)
    [∀ k, HasCoproductsOfShape (T k) C]
    (cS : Cofan (fun k => ∐ fun _ : T k => Y k)) (hS : IsColimit cS) :
    IsColimit (Cofan.mk (P := cS.pt) (f := fun j : (Σ k, T k) => Y j.1)
      (fun j => Sigma.ι (fun _ : T j.1 => Y j.1) j.2 ≫ cS.inj j.1)) :=
  Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc hS (fun k => Sigma.desc (fun t => s.inj ⟨k, t⟩)))
    (fun s j => by simp)
    (fun s m hm => by
      apply Cofan.IsColimit.hom_ext hS
      intro k
      apply Sigma.hom_ext
      intro t
      have := hm ⟨k, t⟩
      simp [← this])


section
variable {α : Type t} {A B : α → C} (g : ∀ a, A a ⟶ B a) {β : Type t'} (p : β → α)
  (T : β → Type w) [∀ b, HasCoproductsOfShape (T b) C]
  {X₁ X₂ : C} {f : X₁ ⟶ X₂}

/-- The coproduct of `T b` copies of `g (p b)`. -/
noncomputable def copowerFamily : ∀ b : β,
    (∐ fun _ : T b => A (p b)) ⟶ ∐ fun _ : T b => B (p b) :=
  fun b => Limits.Sigma.map (fun _ => g (p b))

/-- Attaching cells that are coproducts of copies of the cells `g (p b)` is attaching cells
`g`. -/
noncomputable def _root_.HomotopicalAlgebra.AttachCells.flatten (c : AttachCells.{w} (copowerFamily g p T) f) :
    AttachCells.{w} g f where
  ι := Σ k : c.ι, T (c.π k)
  π j := p (c.π j.1)
  cofan₁ := Cofan.mk c.cofan₁.pt
    (fun j => Sigma.ι (fun _ : T (c.π j.1) => A (p (c.π j.1))) j.2 ≫ c.cofan₁.inj j.1)
  cofan₂ := Cofan.mk c.cofan₂.pt
    (fun j => Sigma.ι (fun _ : T (c.π j.1) => B (p (c.π j.1))) j.2 ≫ c.cofan₂.inj j.1)
  isColimit₁ := flattenCofanIsColimit (fun k : c.ι => T (c.π k)) (fun k => A (p (c.π k)))
    c.cofan₁ c.isColimit₁
  isColimit₂ := flattenCofanIsColimit (fun k : c.ι => T (c.π k)) (fun k => B (p (c.π k)))
    c.cofan₂ c.isColimit₂
  m := c.m
  hm j := by
    show (Sigma.ι _ j.2 ≫ c.cofan₁.inj j.1) ≫ c.m = _
    rw [Category.assoc, c.hm j.1]
    show Sigma.ι _ j.2 ≫ copowerFamily g p T (c.π j.1) ≫ _ = _
    simp [copowerFamily]
  g₁ := c.g₁
  g₂ := c.g₂
  isPushout := c.isPushout

end


section
variable {C' : Type*} [Category C'] {α : Type t} {A B : α → C'} (g : ∀ a, A a ⟶ B a)
  {X₁ X₂ : C'} {f : X₁ ⟶ X₂} (Φ : C' ⥤ C)
  [PreservesColimitsOfSize.{w, w} Φ] [PreservesColimitsOfShape WalkingSpan Φ]

/-- A colimit-preserving functor maps cell attachments to cell attachments. -/
noncomputable def _root_.HomotopicalAlgebra.AttachCells.mapFunctor (c : AttachCells.{w} g f) :
    AttachCells.{w} (fun a => Φ.map (g a)) (Φ.map f) where
  ι := c.ι
  π := c.π
  cofan₁ := Cofan.mk (Φ.obj c.cofan₁.pt) (fun i => Φ.map (c.cofan₁.inj i))
  cofan₂ := Cofan.mk (Φ.obj c.cofan₂.pt) (fun i => Φ.map (c.cofan₂.inj i))
  isColimit₁ := isColimitCofanMkObjOfIsColimit Φ _ c.cofan₁.inj c.isColimit₁
  isColimit₂ := isColimitCofanMkObjOfIsColimit Φ _ c.cofan₂.inj c.isColimit₂
  m := Φ.map c.m
  hm i := by
    show Φ.map (c.cofan₁.inj i) ≫ Φ.map c.m = Φ.map (g (c.π i)) ≫ Φ.map (c.cofan₂.inj i)
    rw [← Φ.map_comp, ← Φ.map_comp, c.hm i]
  g₁ := Φ.map c.g₁
  g₂ := Φ.map c.g₂
  isPushout := c.isPushout.map Φ

end


section Eval
variable {D : Type v} [SmallCategory D] [HasColimitsOfSize.{v, v} C] (I : MorphismProperty C)

lemma exists_of_generating {X Y : D ⥤ C} (f : X ⟶ Y) (hf : generatingFunctorCategory (D := D) I f) :
    ∃ q : D × I.toSet, CategoryTheory.Arrow.mk f = CategoryTheory.Arrow.mk ((evaluationLeftAdjoint C q.1).map q.2.1.hom) := by
  cases hf with
  | mk d i hi => exact ⟨(d, ⟨CategoryTheory.Arrow.mk i, hi⟩), rfl⟩

/-- Evaluating a cell attachment for the generating family of `D ⥤ C` gives a cell attachment
for `I`. -/
noncomputable def _root_.HomotopicalAlgebra.AttachCells.evalAt {X₁ X₂ : D ⥤ C} {f : X₁ ⟶ X₂}
    (c : AttachCells.{v} (generatingFunctorCategory (D := D) I).homFamily f) (d : D) :
    AttachCells.{v} I.homFamily (f.app d) := by
  let a : (generatingFunctorCategory (D := D) I).toSet → D × I.toSet :=
    fun x => (exists_of_generating I x.1.hom x.2).choose
  have ha : ∀ x, CategoryTheory.Arrow.mk ((generatingFunctorCategory (D := D) I).homFamily x) ≅
      CategoryTheory.Arrow.mk ((evaluationLeftAdjoint C (a x).1).map (a x).2.1.hom) := fun x =>
    eqToIso (exists_of_generating I x.1.hom x.2).choose_spec
  let c1 := c.reindexCellTypes (fun q : D × I.toSet =>
    (evaluationLeftAdjoint C q.1).map q.2.1.hom) a ha
  let c2 := HomotopicalAlgebra.AttachCells.mapFunctor _ ((CategoryTheory.evaluation D C).obj d) c1
  let T : D × I.toSet → Type v := fun q => ((q.1 ⟶ d))
  let c3 := c2.reindexCellTypes (copowerFamily I.homFamily (fun q : D × I.toSet => q.2) T) id (fun q => CategoryTheory.Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
      dsimp [copowerFamily]
      erw [Category.id_comp, Category.comp_id]
      rfl))
  exact c3.flatten I.homFamily (fun q : D × I.toSet => q.2) T


section
variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : D ⥤ C} {f : X ⟶ Y}

/-- Evaluating a relative cell complex for the generating family of `D ⥤ C`. -/
noncomputable def _root_.HomotopicalAlgebra.RelativeCellComplex.evalAt
    (c : RelativeCellComplex.{v} (fun _ : J => (generatingFunctorCategory (D := D) I).homFamily) f)
    (d : D) :
    RelativeCellComplex.{v} (fun _ : J => I.homFamily) (f.app d) where
  toTransfiniteCompositionOfShape :=
    c.toTransfiniteCompositionOfShape.map ((CategoryTheory.evaluation D C).obj d)
  attachCells j hj := AttachCells.evalAt I (c.attachCells j hj) d

end


theorem hasSmallObjectArgument_generatingFunctorCategory [I.HasSmallObjectArgument.{v}] :
    (generatingFunctorCategory (D := D) I).HasSmallObjectArgument.{v} := by
  obtain ⟨κ, hκ, hbot, hcard⟩ := HasSmallObjectArgument.exists_cardinal (I := I)
  refine ⟨κ, hκ, hbot, ?_⟩
  have hsmall := hcard.isSmall
  have hls := hcard.locallySmall
  have hpo := hcard.hasPushouts
  have hcop := hcard.hasCoproducts
  have hit := hcard.hasIterationOfShape
  refine
    { isSmall := ?_
      locallySmall := inferInstance
      hasPushouts := inferInstance
      hasCoproducts := ?_
      hasIterationOfShape := inferInstance
      preservesColimit := ?_ }
  · -- smallness
    have : Small.{v} I.toSet := hsmall.small_toSet
    let a : (generatingFunctorCategory (D := D) I).toSet → D × I.toSet :=
      fun x => (exists_of_generating I x.1.hom x.2).choose
    have ha : Function.Injective a := by
      intro x y hxy
      have hx := (exists_of_generating I x.1.hom x.2).choose_spec
      have hy := (exists_of_generating I y.1.hom y.2).choose_spec
      apply Subtype.ext
      have : CategoryTheory.Arrow.mk x.1.hom = CategoryTheory.Arrow.mk y.1.hom := by
        rw [hx, hy]
        change CategoryTheory.Arrow.mk _ = CategoryTheory.Arrow.mk _
        rw [show (exists_of_generating I x.1.hom x.2).choose = (exists_of_generating I y.1.hom y.2).choose from hxy]
      simpa using this
    exact ⟨small_of_injective ha⟩
  · exact inferInstance
  · intro A B X Y i hi f hf
    obtain ⟨⟨d, i₀⟩, harr⟩ := exists_of_generating I i hi
    let e : A ≅ (evaluationLeftAdjoint C d).obj i₀.1.left :=
      CategoryTheory.Arrow.leftFunc.mapIso (eqToIso harr)
    have hpres : PreservesColimit (hf.evalAt I d).F (coyoneda.obj (Opposite.op i₀.1.left)) :=
      hcard.preservesColimit i₀.1.hom i₀.2 (f.app d) (hf.evalAt I d)
    have h1 : PreservesColimit hf.F
        ((CategoryTheory.evaluation D C).obj d ⋙ coyoneda.obj (Opposite.op i₀.1.left)) :=
      haveI : PreservesColimit (hf.F ⋙ (CategoryTheory.evaluation D C).obj d)
        (coyoneda.obj (Opposite.op i₀.1.left)) := hpres
      comp_preservesColimit _ _
    let adj := evaluationAdjunctionRight C d
    let iso : coyoneda.obj (Opposite.op A) ≅
        (CategoryTheory.evaluation D C).obj d ⋙ coyoneda.obj (Opposite.op i₀.1.left) :=
      NatIso.ofComponents (fun Z => Equiv.toIso
        { toFun := fun g => (adj.homEquiv _ _) (e.inv ≫ g)
          invFun := fun h => e.hom ≫ (adj.homEquiv _ _).symm h
          left_inv := fun g => by simp
          right_inv := fun h => by simp })
        (fun {Z Z'} φ => by
          ext g
          simp [Adjunction.homEquiv_naturality_right])
    exact preservesColimit_of_natIso hf.F iso.symm


lemma evaluation_llp_projectiveFibrations [HasLimitsOfSize.{v, v} C] (J : MorphismProperty C)
    {X₁ X₂ : D ⥤ C} (i : X₁ ⟶ X₂)
    (hi : (projectiveFibrations (D := D) J.rlp).llp i) (d : D) : J.rlp.llp (i.app d) := by
  intro A B p hp
  have adj := evaluationAdjunctionLeft C d
  have key : HasLiftingProperty i ((evaluationRightAdjoint C d).map p) := by
    apply hi
    intro e
    have : ((evaluationRightAdjoint C d).map p).app e =
        Limits.Pi.map (fun _ : e ⟶ d => p) := by
      apply Limits.Pi.hom_ext
      intro g
      erw [Limits.Pi.map_π]
      exact Limits.limit.lift_π _ _
    change J.rlp _
    rw [this]
    exact MorphismProperty.limMap _ (fun ⟨_⟩ => hp)
  exact (adj.hasLiftingProperty_iff i p).2 key


theorem projective_cofW [HasLimitsOfSize.{v, v} C] (M : ModelStructure C) (I J : MorphismProperty C)
    (h : IsCofibrantlyGeneratedBy M I J) :
    (generatingFunctorCategory (D := D) I).rlp.llp ⊓ projectiveWeakEquivalences (D := D) M.W =
      (generatingFunctorCategory (D := D) J).rlp.llp := by
  have hJsoa : J.HasSmallObjectArgument.{v} := h.soa_J
  have : (generatingFunctorCategory (D := D) J).HasSmallObjectArgument.{v} :=
    hasSmallObjectArgument_generatingFunctorCategory J
  have hFibJ := projectiveFibrations_eq_rlp (D := D) M I J h
  have hFibW := projectiveTrivialFibrations_eq_rlp (D := D) M I J h
  have hfibJ : M.Fib = J.rlp := fib_eq_rlp M I J h
  have : (projectiveWeakEquivalences (D := D) M.W).HasTwoOutOfThreeProperty := by
    have := M.twoOutOfThree
    infer_instance
  -- one inclusion
  have partA : ∀ {X Y : D ⥤ C} (i : X ⟶ Y), (generatingFunctorCategory (D := D) J).rlp.llp i →
      ((generatingFunctorCategory (D := D) I).rlp.llp ⊓
        projectiveWeakEquivalences (D := D) M.W) i := by
    intro X Y i hi
    refine ⟨?_, ?_⟩
    · intro A B p hp
      rw [← hFibW] at hp
      have hp1 : (generatingFunctorCategory (D := D) J).rlp p := hFibJ ▸ hp.1
      exact hi p hp1
    · intro d
      have hi' : (projectiveFibrations (D := D) J.rlp).llp i := by
        rw [← hfibJ, hFibJ]; exact hi
      have := evaluation_llp_projectiveFibrations J i hi' d
      have e : J.rlp.llp = M.Cof ⊓ M.W := (cof_eq_llp_rlp J).symm.trans h.cof_J
      rw [e] at this
      exact this.2
  ext X Y i
  constructor
  · rintro ⟨hI, hW⟩
    let W := functorialWFS_of_hasSmallObjectArgument (generatingFunctorCategory (D := D) J)
    let f : Arrow (D ⥤ C) := Arrow.mk i
    have hj : W.L (W.ι.app f) := W.ι_mem f
    have hq : W.R (W.π.app f) := W.π_mem f
    have hfac : W.ι.app f ≫ W.π.app f = i := W.fac f
    have hjL : (generatingFunctorCategory (D := D) J).rlp.llp (W.ι.app f) := hj
    have hqR : (generatingFunctorCategory (D := D) J).rlp (W.π.app f) := hq
    obtain ⟨hjI, hjW⟩ := partA _ hjL
    have hqW : projectiveWeakEquivalences (D := D) M.W (W.π.app f) :=
      (inferInstance : (projectiveWeakEquivalences (D := D) M.W).HasTwoOutOfThreeProperty).of_precomp
        _ _ hjW (hfac ▸ hW)
    have hqI : (generatingFunctorCategory (D := D) I).rlp (W.π.app f) := by
      rw [← hFibW]
      exact ⟨hFibJ ▸ hqR, hqW⟩
    have hl : HasLiftingProperty i (W.π.app f) := hI _ hqI
    have sq : CommSq (W.ι.app f) i (W.π.app f) (𝟙 _) := ⟨by simpa using hfac⟩
    haveI := hl.sq_hasLift sq
    have hl1 : i ≫ sq.lift = W.ι.app f := sq.fac_left
    intro A B p hp
    refine ⟨fun {u v} sq2 => ?_⟩
    haveI := hjL p hp
    have sq3 : CommSq u (W.ι.app f) p (W.π.app f ≫ v) :=
      ⟨by rw [← Category.assoc, hfac]; exact sq2.w⟩
    refine ⟨⟨sq.lift ≫ sq3.lift, ?_, ?_⟩⟩
    · rw [← Category.assoc, hl1]; exact sq3.fac_left
    · rw [Category.assoc, sq3.fac_right, ← Category.assoc, sq.fac_right, Category.id_comp]
  · exact partA i

end Eval


end CellTransfer

/-- Definition 2.5.7: `N` is the projective model structure on `D ⥤ C` induced by `M`. -/
structure IsProjectiveModelStructure {D : Type*} [SmallCategory D] (M : ModelStructure C)
    (N : ModelStructure (D ⥤ C)) : Prop where
  W_eq : N.W = projectiveWeakEquivalences M.W
  Fib_eq : N.Fib = projectiveFibrations M.Fib

/-- **Theorem 2.5.8.** If `C` is a cofibrantly generated model category and `D` is a small
category, the projective model structure on `C^D` exists. -/
theorem exists_projectiveModelStructure {D : Type v} [SmallCategory D] (M : ModelCategory C)
    (hM : IsCofibrantlyGenerated M.str) :
    ∃ N : ModelStructure (D ⥤ C), IsProjectiveModelStructure M.str N := by
  have : HasColimits C := M.hasColimits
  rcases hM with ⟨I, J, hIJ⟩
  let I_D := generatingFunctorCategory (D := D) I
  let J_D := generatingFunctorCategory (D := D) J
  have hFib : projectiveFibrations (D := D) M.str.Fib = J_D.rlp :=
    projectiveFibrations_eq_rlp M.str I J hIJ
  have hFibW : projectiveFibrations (D := D) M.str.Fib ⊓ projectiveWeakEquivalences (D := D) M.str.W =
      I_D.rlp :=
    projectiveTrivialFibrations_eq_rlp M.str I J hIJ
  have : (projectiveWeakEquivalences (D := D) M.str.W).HasTwoOutOfThreeProperty := by
    have := M.str.twoOutOfThree
    infer_instance
  have : I.HasSmallObjectArgument.{v} := hIJ.soa_I
  have : J.HasSmallObjectArgument.{v} := hIJ.soa_J
  have : I_D.HasSmallObjectArgument.{v} := hasSmallObjectArgument_generatingFunctorCategory I
  have : J_D.HasSmallObjectArgument.{v} := hasSmallObjectArgument_generatingFunctorCategory J
  have : HasLimits C := M.hasLimits
  have hCofW : I_D.rlp.llp ⊓ projectiveWeakEquivalences (D := D) M.str.W = J_D.rlp.llp :=
    projective_cofW M.str I J hIJ
  let N := ModelStructure.ofCofibrantlyGenerated
    (W := projectiveWeakEquivalences (D := D) M.str.W)
    (Cof := I_D.rlp.llp)
    (Fib := projectiveFibrations (D := D) M.str.Fib)
    I_D J_D
    rfl hFibW hCofW hFib
  exact ⟨N, ⟨rfl, rfl⟩⟩

/-- Reduction of the projective model structure on chain complexes to the existence of
generating sets `I` and `J` satisfying the Hovey recognition conditions. -/
theorem exists_modelStructure_chainComplex_reduced (R : Type v) [CommRing R]
    (I J : MorphismProperty (ChainComplex (ModuleCat.{v} R) ℕ))
    (hI_small : Small.{v} {f : Arrow (ChainComplex (ModuleCat.{v} R) ℕ) // I f.hom})
    (hJ_small : Small.{v} {f : Arrow (ChainComplex (ModuleCat.{v} R) ℕ) // J f.hom})
    (hI_soa : I.HasSmallObjectArgument.{v})
    (hJ_soa : J.HasSmallObjectArgument.{v})
    (hFib : positiveDegreeSurjections R = J.rlp)
    (hFibW : positiveDegreeSurjections R ⊓ HomologicalComplex.quasiIso _ _ = I.rlp)
    (hCofW : I.rlp.llp ⊓ HomologicalComplex.quasiIso _ _ = J.rlp.llp) :
    ∃ M : ModelStructure (ChainComplex (ModuleCat.{v} R) ℕ),
      IsCofibrantlyGenerated M ∧
      M.W = HomologicalComplex.quasiIso _ _ ∧
      ∀ (X T : ChainComplex (ModuleCat.{v} R) ℕ) (t : X ⟶ T), IsTerminal T → M.Fib t := by
  have : (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.down ℕ)).HasTwoOutOfThreeProperty :=
    inferInstance
  have : I.HasSmallObjectArgument.{v} := hI_soa
  have : J.HasSmallObjectArgument.{v} := hJ_soa
  let M := ModelStructure.ofCofibrantlyGenerated
    (W := HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.down ℕ))
    (Cof := I.rlp.llp)
    (Fib := positiveDegreeSurjections R)
    I J
    rfl hFibW hCofW hFib
  refine ⟨M, ?_, rfl, fun X T t hT => terminal_in_positiveDegreeSurjections R X T t hT⟩
  refine ⟨I, J, ⟨hI_small, hJ_small, ?_, ?_, hI_soa, hJ_soa⟩⟩
  · rw [cof_eq_llp_rlp]; rfl
  · rw [cof_eq_llp_rlp]; exact hCofW.symm

/-- The factor-and-retract step in the recognition argument. Once the left class
of the `J`-factorization consists of weak equivalences and `I`-cofibrations, the
other inclusion follows from two out of three. -/
lemma cofW_eq_of_le (W I J : MorphismProperty C)
    [W.HasTwoOutOfThreeProperty] [J.HasSmallObjectArgument.{v}]
    (hFibW : I.rlp = J.rlp ⊓ W)
    (hJ : J.rlp.llp ≤ I.rlp.llp ⊓ W) :
    I.rlp.llp ⊓ W = J.rlp.llp := by
  ext X Y i
  constructor
  · rintro ⟨hI, hW⟩
    let F := functorialWFS_of_hasSmallObjectArgument J
    let f : Arrow C := Arrow.mk i
    have hj : J.rlp.llp (F.ι.app f) := F.ι_mem f
    have hq : J.rlp (F.π.app f) := F.π_mem f
    have hfac : F.ι.app f ≫ F.π.app f = i := F.fac f
    have hjW : W (F.ι.app f) := (hJ _ hj).2
    have hqW : W (F.π.app f) :=
      (inferInstance : W.HasTwoOutOfThreeProperty).of_precomp
        _ _ hjW (hfac ▸ hW)
    have hqI : I.rlp (F.π.app f) := hFibW.symm ▸ ⟨hq, hqW⟩
    have hl : HasLiftingProperty i (F.π.app f) := hI _ hqI
    have sq : CommSq (F.ι.app f) i (F.π.app f) (𝟙 _) := ⟨by simpa using hfac⟩
    haveI := hl.sq_hasLift sq
    have hl1 : i ≫ sq.lift = F.ι.app f := sq.fac_left
    intro A B p hp
    refine ⟨fun {u v} sq2 => ?_⟩
    haveI := hj p hp
    have sq3 : CommSq u (F.ι.app f) p (F.π.app f ≫ v) :=
      ⟨by rw [← Category.assoc, hfac]; exact sq2.w⟩
    refine ⟨⟨sq.lift ≫ sq3.lift, ?_, ?_⟩⟩
    · rw [← Category.assoc, hl1]; exact sq3.fac_left
    · rw [Category.assoc, sq3.fac_right, ← Category.assoc, sq.fac_right, Category.id_comp]
  · exact hJ _

/-- The generating maps for the projective model structure in Example 2.5.9,
their small object arguments and lifting classes, and the retract argument for
trivial cofibrations. -/
lemma chainComplex_generators (R : Type v) [CommRing R] :
    ∃ I J : MorphismProperty (ChainComplex (ModuleCat.{v} R) ℕ),
      Small.{v} {f : Arrow (ChainComplex (ModuleCat.{v} R) ℕ) // I f.hom} ∧
      Small.{v} {f : Arrow (ChainComplex (ModuleCat.{v} R) ℕ) // J f.hom} ∧
      I.HasSmallObjectArgument.{v} ∧ J.HasSmallObjectArgument.{v} ∧
      positiveDegreeSurjections R = J.rlp ∧
      positiveDegreeSurjections R ⊓ HomologicalComplex.quasiIso _ _ = I.rlp ∧
      J.rlp.llp ≤ I.rlp.llp ⊓ HomologicalComplex.quasiIso _ _ := by
  let I := ProjectiveGenerators.generatingCofibrations R
  let J := ProjectiveGenerators.generatingTrivialCofibrations R
  have hI : positiveDegreeSurjections R ⊓ HomologicalComplex.quasiIso _ _ = I.rlp :=
    (ProjectiveGenerators.generatingCofibrations_rlp R).symm
  have hJ : positiveDegreeSurjections R = J.rlp :=
    (ProjectiveGenerators.generatingTrivialCofibrations_rlp R).symm
  have hIs : Small.{v} I.toSet := inferInstance
  have hJs : Small.{v} J.toSet := inferInstance
  refine ⟨I, J, hIs, hJs, inferInstance, inferInstance, hJ, hI, ?_⟩
  intro X Y f hf
  refine ⟨?_, ProjectiveGenerators.disk_leftClass_quasiIso f hf⟩
  intro A B p hp
  have hp' : (positiveDegreeSurjections R ⊓ HomologicalComplex.quasiIso _ _) p := hI.symm ▸ hp
  exact hf p (hJ ▸ hp'.1)

/-- **Example 2.5.9.** For a commutative ring `R`, there is a cofibrantly generated model
structure on chain complexes with the homology isomorphisms as weak equivalences, in which
every object is fibrant.

**Gap (imprecise, Example 2.5.9).** The statement does not say which chain complexes are meant;
Lean takes the connective (`ℕ`-indexed) ones, with positive-degree surjections as fibrations.

The thesis cites the result from [Hov07, Theorem 2.3.11] without proof. The generating
cofibrations are `0 → S⁰` and `Sⁿ → Dⁿ⁺¹`; the generating trivial cofibrations are
`0 → Dⁿ⁺¹`. Their constructions, lifting classes and small object arguments are proved
in `PreliminariesProjectiveChainComplexes`.

**Change.** To show that maps lifting against the fibrations are quasi-isomorphisms,
we factor through `X ⊞ P(Y)`, where `P(Y)` is an explicit contractible cover of `Y`
surjective in positive degrees. The lifting property makes the original map a retract
of the homotopy equivalence `X → X ⊞ P(Y)`. This avoids a separate homology calculation
for transfinite cell complexes. -/
theorem exists_modelStructure_chainComplex (R : Type v) [CommRing R] :
    ∃ M : ModelStructure (ChainComplex (ModuleCat.{v} R) ℕ),
      IsCofibrantlyGenerated M ∧
      M.W = HomologicalComplex.quasiIso _ _ ∧
      ∀ (X T : ChainComplex (ModuleCat.{v} R) ℕ) (t : X ⟶ T), IsTerminal T → M.Fib t := by
  obtain ⟨I, J, hIs, hJs, hIsoa, hJsoa, hFib, hFibW, hJ⟩ :=
    chainComplex_generators R
  letI := hJsoa
  have hEq : I.rlp = J.rlp ⊓ HomologicalComplex.quasiIso _ _ := by
    rw [← hFib, hFibW]
  exact exists_modelStructure_chainComplex_reduced R I J hIs hJs hIsoa hJsoa
    hFib hFibW (cofW_eq_of_le _ I J hEq hJ)

end Model

/-! ## Chapter 2.6: Persistent objects

A persistent object in `C` indexed by a monoidal poset `P` is a functor `P ⥤ C`. We take a
monoidal poset to be an ordered commutative additive monoid (the only cases used are `ℝ≥0`
and `ℝ`), writing the monoidal product as `+`.

Includes the Yoneda shift isomorphism (2.6.6) and the separation property (2.6.13). -/

section Persistent

open CategoryTheory Limits

section Shift

variable {P : Type u} [AddCommMonoid P] [PartialOrder P] [IsOrderedAddMonoid P]

/-- The functor `q ↦ p + q` on the poset `P`. -/
def addLeft (p : P) : P ⥤ P where
  obj q := p + q
  map {q q'} f := homOfLE (add_le_add_right (leOfHom f) p)

/-- Definition 2.6.1: the `p`-shift to the left `F^p (q) = F (p + q)` of `F : P ⥤ C`. -/
def shift {C : Type w} [Category.{v} C] (p : P) (F : P ⥤ C) : P ⥤ C := addLeft p ⋙ F

/-! ### 2.6.1 Day convolution -/

/-- The addition functor `P × P ⥤ P`. -/
def addFunctor : P × P ⥤ P where
  obj st := st.1 + st.2
  map {st st'} f := homOfLE (add_le_add (leOfHom f.1) (leOfHom f.2))

/-- The external product `(s, t) ↦ F s × G t`. -/
def externalProduct (F G : P ⥤ Type u) : P × P ⥤ Type u where
  obj st := F.obj st.1 × G.obj st.2
  map {st st'} f := TypeCat.ofHom fun x =>
    (F.map f.1 x.1, G.map f.2 x.2)

/-- Equations (2.6.2) / Day convolution: `F ⊗_Day G` is the left Kan extension of the external
product `F ⊠ G` along `+ : P × P ⥤ P`; pointwise this is the coend
`(F ⊗_Day G)(r) = ∫^{s + t ≤ r} F(s) × G(t)`, i.e. the colimit of `F s × G t` over pairs with
`s + t ≤ r`. -/
noncomputable def dayConv [Small.{u} P] (F G : P ⥤ Type u) : P ⥤ Type u :=
  Functor.leftKanExtension (addFunctor (P := P)) (externalProduct F G)


/-- The functoriality of `shift p` in the persistent object: `F ⟶ G` gives `F^p ⟶ G^p`. -/
def shiftMap {C : Type w} [Category.{v} C] (p : P) {F G : P ⥤ C} (α : F ⟶ G) :
    shift p F ⟶ shift p G :=
  Functor.whiskerLeft (addLeft p) α

/-- The natural map `F^p ⟶ F^{p'}` for `p ≤ p'`. -/
def shiftHom {C : Type w} [Category.{v} C] {p p' : P} (h : p ≤ p') (F : P ⥤ C) :
    shift p F ⟶ shift p' F where
  app q := F.map (homOfLE (add_le_add_left h q))
  naturality := by
    intros; simp only [shift, Functor.comp_map, ← Functor.map_comp]; rfl

/-- The functor `r ↦ G^r` from `P` to `P ⥤ C`. -/
def shiftFunctor {C : Type w} [Category.{v} C] (G : P ⥤ C) : P ⥤ (P ⥤ C) where
  obj r := shift r G
  map {r r'} f := shiftHom (leOfHom f) G
  map_id := by
    intro r; ext q
    exact G.map_id _
  map_comp := by
    intro r r' r'' f g; ext q
    exact (G.map_comp _ _)

/-- Equation (2.6.3): the internal hom `[F, G]_Day`, `r ↦ Nat(F, G^r)`. -/
def internalHom (F G : P ⥤ Type u) : P ⥤ Type u :=
  shiftFunctor G ⋙ coyoneda.obj (Opposite.op F)

/-- Definition 2.6.5: the (co)Yoneda embedding, `Y r s` is a singleton if `r ≤ s` and
empty otherwise. -/
def yoneda (r : P) : P ⥤ Type u where
  obj s := ULift.{u} (PLift (r ≤ s))
  map {s s'} f := TypeCat.ofHom fun h => ⟨⟨h.down.down.trans (leOfHom f)⟩⟩

/-- Equation (2.6.6): `G^r ≅ [Y r, G]_Day`. -/
theorem shift_iso_internalHom_yoneda (r : P) (G : P ⥤ Type u) :
    Nonempty (shift r G ≅ internalHom (yoneda r) G) := by
  have comp {a b c : P} (f : a ⟶ b) (g : b ⟶ c) (x : G.obj a) :
      G.map g (G.map f x) = G.map (f ≫ g) x :=
    (ConcreteCategory.congr_hom (G.map_comp f g) x).symm
  let e (s : P) : (shift r G).obj s ≃ (yoneda r ⟶ shift s G) :=
    { toFun := fun x =>
        { app := fun t => TypeCat.ofHom fun h =>
            G.map (homOfLE (add_le_add le_rfl h.down.down))
              (G.map (homOfLE (add_comm r s).le) x)
          naturality := by
            intro t t' f
            ext h
            change G.map _ (G.map _ x) = G.map _ (G.map _ (G.map _ x))
            erw [comp, comp, comp]
            rfl }
      invFun := fun α => G.map (homOfLE (add_comm s r).le) (α.app r ⟨⟨le_rfl⟩⟩)
      left_inv := by
        intro x
        change G.map _ (G.map _ (G.map _ x)) = x
        erw [comp, comp]
        exact ConcreteCategory.congr_hom (G.map_id _) x
      right_inv := by
        intro α
        ext t h
        have hn := congrArg (fun f => f ⟨⟨le_rfl⟩⟩)
          (α.naturality (homOfLE h.down.down))
        change α.app t _ = G.map _ (α.app r _) at hn
        change G.map _ (G.map _ (G.map _ (α.app r _))) = α.app t h
        erw [comp, comp]
        exact hn.symm }
  refine ⟨NatIso.ofComponents (fun s => (e s).toIso) ?_⟩
  intro s t f
  apply ConcreteCategory.hom_ext
  intro x
  change (e t) ((shift r G).map f x) = _
  ext q h
  change G.map _ (G.map _ (G.map _ x)) = G.map _ (G.map _ (G.map _ x))
  erw [comp, comp, comp, comp]
  rfl


/-- Equation (2.6.7): `[F, G]_Day (r) ≅ Nat(F ⊗_Day Y r, G)`. -/
theorem internalHom_obj_iso [Small.{u} P] (F G : P ⥤ Type u) (r : P) :
    Nonempty ((internalHom F G).obj r ≃ (dayConv F (yoneda r) ⟶ G)) := by
  have comp {a b c : P} (f : a ⟶ b) (g : b ⟶ c) (x : G.obj a) :
      G.map g (G.map f x) = G.map (f ≫ g) x :=
    (ConcreteCategory.congr_hom (G.map_comp f g) x).symm
  let e : (F ⟶ shift r G) ≃ (externalProduct F (yoneda r) ⟶ addFunctor ⋙ G) :=
    { toFun := fun α =>
        { app := fun st => TypeCat.ofHom fun x =>
            G.map (homOfLE (by
              change r + st.1 ≤ st.1 + st.2
              exact (add_comm r st.1).le.trans (add_le_add le_rfl x.2.down.down)))
              (α.app st.1 x.1)
          naturality := by
            intro st st' f
            ext x
            have hn := ConcreteCategory.congr_hom (α.naturality f.1) x.1
            change α.app st'.1 (F.map f.1 x.1) = G.map _ (α.app st.1 x.1) at hn
            change G.map _ (α.app _ (F.map _ x.1)) = G.map _ (G.map _ (α.app _ x.1))
            erw [hn, comp, comp]
            rfl }
      invFun := fun β =>
        { app := fun s => TypeCat.ofHom fun x =>
            G.map (homOfLE (add_comm s r).le) (β.app (s, r) (x, ⟨⟨le_rfl⟩⟩))
          naturality := by
            intro s t f
            ext x
            have hn := congrArg (fun f => f ((x, ⟨⟨le_rfl⟩⟩) : (externalProduct F (yoneda r)).obj (s, r)))
              (β.naturality ((f, 𝟙 r) : (s, r) ⟶ (t, r)))
            change β.app (t, r) (F.map f x, ⟨⟨le_rfl⟩⟩) = G.map _ (β.app (s, r) _) at hn
            change G.map _ (β.app (t, r) _) = G.map _ (G.map _ (β.app (s, r) _))
            erw [hn, comp, comp]
            rfl }
      left_inv := by
        intro α
        ext s x
        change G.map _ (G.map _ (α.app s x)) = α.app s x
        erw [comp]
        exact ConcreteCategory.congr_hom (G.map_id _) _
      right_inv := by
        intro β
        ext st x
        have hn := congrArg (fun f => f ((x.1, ⟨⟨le_rfl⟩⟩) : (externalProduct F (yoneda r)).obj (st.1, r)))
          (β.naturality ((𝟙 st.1, homOfLE x.2.down.down) : (st.1, r) ⟶ st))
        change β.app st (F.map (𝟙 _) x.1, x.2) = G.map _ (β.app (st.1, r) _) at hn
        erw [F.map_id] at hn
        change G.map _ (G.map _ (β.app (st.1, r) _)) = β.app st x
        erw [comp]
        exact hn.symm }
  exact ⟨e.trans ((Functor.leftKanExtension addFunctor (externalProduct F (yoneda r))).homEquivOfIsLeftKanExtension
    (Functor.leftKanExtensionUnit addFunctor (externalProduct F (yoneda r))) G).symm⟩

/-- The natural transformation `(Y u ⊠ Y v) ⟶ (+ ⋙ Y (u + v))`. -/
def yonedaAddNatTrans (u v : P) :
    externalProduct (yoneda u) (yoneda v) ⟶ addFunctor ⋙ yoneda (u + v) where
  app st := TypeCat.ofHom fun x => ⟨⟨add_le_add x.1.down.down x.2.down.down⟩⟩
  naturality := by
    intro st st' f
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- `Y (u + v)` is the left Kan extension of `Y u ⊠ Y v` along `+`. -/
theorem isLeftKanExtension_yoneda (u v : P) :
    (yoneda (u + v)).IsLeftKanExtension (yonedaAddNatTrans u v) where
  nonempty_isUniversal := by
    refine ⟨IsInitial.ofUniqueHom ?_ ?_⟩
    · intro y
      have comp {a b c : P} (f : a ⟶ b) (g : b ⟶ c) (x : y.right.obj a) :
          y.right.map g (y.right.map f x) = y.right.map (f ≫ g) x :=
        (ConcreteCategory.congr_hom (y.right.map_comp f g) x).symm
      let pt : (externalProduct (yoneda u) (yoneda v)).obj (u, v) := (⟨⟨le_rfl⟩⟩, ⟨⟨le_rfl⟩⟩)
      refine StructuredArrow.homMk
        { app := fun w => TypeCat.ofHom fun h =>
            y.right.map (homOfLE h.down.down) (y.hom.app (u, v) pt)
          naturality := by
            intro w w' f
            apply ConcreteCategory.hom_ext
            rintro ⟨⟨h⟩⟩
            dsimp
            erw [comp]
            rfl }
        ?_
      ext ⟨s, t⟩ x
      rcases x with ⟨x, y_elem⟩
      have hn := ConcreteCategory.congr_hom
        (y.hom.naturality ((homOfLE x.down.down, homOfLE y_elem.down.down) : (u, v) ⟶ (s, t)))
        pt
      have h_lhs : (externalProduct (yoneda u) (yoneda v)).map
          ((homOfLE x.down.down, homOfLE y_elem.down.down) : (u, v) ⟶ (s, t)) pt = (x, y_elem) := rfl
      change y.hom.app (s, t) ((externalProduct (yoneda u) (yoneda v)).map
          ((homOfLE x.down.down, homOfLE y_elem.down.down) : (u, v) ⟶ (s, t)) pt) =
        y.right.map (homOfLE (add_le_add x.down.down y_elem.down.down)) (y.hom.app (u, v) pt) at hn
      rw [h_lhs] at hn
      change y.right.map (homOfLE (add_le_add x.down.down y_elem.down.down)) (y.hom.app (u, v) pt) =
        y.hom.app (s, t) (x, y_elem)
      exact hn.symm
    · intro y m
      apply StructuredArrow.hom_ext
      ext w h
      rcases h with ⟨⟨h⟩⟩
      let pt : (externalProduct (yoneda u) (yoneda v)).obj (u, v) := (⟨⟨le_rfl⟩⟩, ⟨⟨le_rfl⟩⟩)
      have hm := ConcreteCategory.congr_hom (congr_app m.w (u, v)) pt
      have nat_m := ConcreteCategory.congr_hom (m.right.naturality (homOfLE h : u + v ⟶ w)) ⟨⟨le_rfl⟩⟩
      dsimp
      exact nat_m.trans (congrArg _ hm)

/-- Lemma 2.6.8: the Yoneda embedding is monoidal: `Y u ⊗_Day Y v ≅ Y (u + v)`
(and the unit is `Y 0`). -/
theorem dayConv_yoneda [Small.{u} P] (u v : P) :
    Nonempty (dayConv (yoneda u) (yoneda v) ≅ yoneda (u + v)) := by
  have : (yoneda (u + v)).IsLeftKanExtension (yonedaAddNatTrans u v) :=
    isLeftKanExtension_yoneda u v
  have : (dayConv (yoneda u) (yoneda v)).IsLeftKanExtension
      (Functor.leftKanExtensionUnit addFunctor (externalProduct (yoneda u) (yoneda v))) :=
    inferInstanceAs ((Functor.leftKanExtension addFunctor (externalProduct (yoneda u) (yoneda v))).IsLeftKanExtension _)
  exact ⟨((yoneda (u + v)).leftKanExtensionUnique (yonedaAddNatTrans u v)
    (dayConv (yoneda u) (yoneda v))
    (Functor.leftKanExtensionUnit addFunctor (externalProduct (yoneda u) (yoneda v)))).symm⟩

/-! ### 2.6.2 Continuity of persistent objects -/

/-- The inclusion of the strict lower set `{r' | r' < r}` into `P`. -/
def lowerSet (r : P) : {r' : P // r' < r} ⥤ P where
  obj r' := r'.1
  map {a b} f := homOfLE (leOfHom f)

/-- The inclusion of the strict upper set `{r' | r < r'}` into `P`. -/
def upperSet (r : P) : {r' : P // r < r'} ⥤ P where
  obj r' := r'.1
  map {a b} f := homOfLE (leOfHom f)

/-- Definition 2.6.9: `F : P ⥤ C` is left continuous if `colim F^{<r} ⟶ F r` is an
isomorphism for all `r`. -/
def IsLeftContinuous {C : Type w} [Category.{v} C] [HasColimitsOfSize.{u, u} C]
    (F : P ⥤ C) : Prop :=
  ∀ r : P, IsIso (Limits.colimit.desc (lowerSet r ⋙ F)
    (Limits.Cocone.mk (F.obj r)
      { app := fun s => F.map (homOfLE (le_of_lt s.2))
        naturality := by
          intros
          simp only [Functor.comp_map, Functor.const_obj_map]
          erw [Category.comp_id, ← Functor.map_comp]
          rfl }))

/-- Definition 2.6.9: `F : P ⥤ C` is right continuous if `F r ⟶ lim F^{>r}` is an
isomorphism for all `r`. -/
def IsRightContinuous {C : Type w} [Category.{v} C] [HasLimitsOfSize.{u, u} C]
    (F : P ⥤ C) : Prop :=
  ∀ r : P, IsIso (Limits.limit.lift (upperSet r ⋙ F)
    (Limits.Cone.mk (F.obj r)
      { app := fun s => F.map (homOfLE (le_of_lt s.2))
        naturality := by
          intros
          simp only [Functor.comp_map, Functor.const_obj_map]
          erw [Category.id_comp, ← Functor.map_comp]
          rfl }))

lemma rightCont_inj {G : P ⥤ Type u} (hG : IsRightContinuous G) (r : P) {z z' : G.obj r}
    (h : ∀ s : P, ∀ hs : r < s, G.map (homOfLE hs.le) z = G.map (homOfLE hs.le) z') : z = z' := by
  have := hG r
  have hinj := ((isIso_iff_bijective _).1 this).1
  apply hinj
  apply Types.limit_ext
  intro s
  have := h s.1 s.2
  erw [← types_comp_apply (limit.lift _ _) (limit.π _ s), limit.lift_π,
    ← types_comp_apply (limit.lift _ _) (limit.π _ s), limit.lift_π]
  exact this

lemma rightCont_surj {G : P ⥤ Type u} (hG : IsRightContinuous G) (r : P)
    (x : ∀ s : P, r < s → G.obj s)
    (hx : ∀ s s' (hs : r < s) (hs' : r < s') (h : s ≤ s'), G.map (homOfLE h) (x s hs) = x s' hs') :
    ∃ y : G.obj r, ∀ s (hs : r < s), G.map (homOfLE hs.le) y = x s hs := by
  have := hG r
  have hsurj := ((isIso_iff_bijective _).1 this).2
  obtain ⟨y, hy⟩ := hsurj (Types.Limit.mk (upperSet r ⋙ G) (fun s => x s.1 s.2)
    (fun s s' f => hx s.1 s' s.2 s'.2 (leOfHom f)))
  refine ⟨y, fun s hs => ?_⟩
  have := congrArg (fun z => limit.π (upperSet r ⋙ G) ⟨s, hs⟩ z) hy
  erw [Types.Limit.π_mk] at this
  exact (ConcreteCategory.congr_hom (limit.lift_π (F := upperSet r ⋙ G) _ (⟨s, hs⟩ : {r' : P // r < r'})) y).symm.trans this


/-- `G.map` along `a ≤ b`, elementwise. -/
abbrev persGm (G : P ⥤ Type u) {a b : P} (h : a ≤ b) (z : G.obj a) : G.obj b := G.map (homOfLE h) z

lemma persGm_comp (G : P ⥤ Type u) {a b c : P} (h1 : a ≤ b) (h2 : b ≤ c) (z : G.obj a) :
    persGm G h2 (persGm G h1 z) = persGm G (h1.trans h2) z :=
  (ConcreteCategory.congr_hom (G.map_comp (homOfLE h1) (homOfLE h2)) z).symm

lemma rightCont_intro {G : P ⥤ Type u}
    (hinj : ∀ r : P, ∀ z z' : G.obj r,
      (∀ s : P, ∀ hs : r < s, persGm G hs.le z = persGm G hs.le z') → z = z')
    (hsurj : ∀ r : P, ∀ x : (∀ s : P, r < s → G.obj s),
      (∀ s s' (hs : r < s) (hs' : r < s') (h : s ≤ s'), persGm G h (x s hs) = x s' hs') →
      ∃ y : G.obj r, ∀ s (hs : r < s), persGm G hs.le y = x s hs) :
    IsRightContinuous G := by
  intro r
  rw [isIso_iff_bijective]
  constructor
  · intro z z' h
    apply hinj r
    intro s hs
    have := congrArg (limit.π (upperSet r ⋙ G) ⟨s, hs⟩) h
    erw [← types_comp_apply (limit.lift _ _) (limit.π _ _), limit.lift_π,
      ← types_comp_apply (limit.lift _ _) (limit.π _ _), limit.lift_π] at this
    exact this
  · intro ξ
    obtain ⟨y, hy⟩ := hsurj r (fun s hs => limit.π (upperSet r ⋙ G) ⟨s, hs⟩ ξ) (by
      intro s s' hs hs' h
      have := ConcreteCategory.congr_hom (limit.w (upperSet r ⋙ G)
        (show (⟨s, hs⟩ : {r' : P // r < r'}) ⟶ ⟨s', hs'⟩ from homOfLE h)) ξ
      exact this)
    refine ⟨y, ?_⟩
    apply Types.limit_ext
    intro j
    erw [← types_comp_apply (limit.lift _ _) (limit.π _ _), limit.lift_π]
    exact hy j.1 j.2


/-- component of an element of `[F, G]_Day (r)` at `t`. -/
def persEv {F G : P ⥤ Type u} {r : P} (γ : (internalHom F G).obj r) (t : P) (x : F.obj t) :
    G.obj (r + t) := (γ : F ⟶ shift r G).app t x

/-- Proposition 2.6.10: if `G` is right continuous, so is `[F, G]_Day`.

**Gap (missing hypothesis, Proposition 2.6.10).** The proof uses `lim_{r' > r} G^{r'} ≅ G^r`, i.e. that
`r' ↦ r' + t` maps `{r' > r}` coinitially into `{q > r + t}`, and that `{r' > r}` is
codirected. This holds for `ℝ≥0` and `ℝ`, but not for an arbitrary monoidal poset `P`. We state
it for `P` totally ordered (`hlin`) with the coinitiality condition `hP`, both of which hold
for `ℝ≥0` and `ℝ`. -/
theorem internalHom_isRightContinuous
    (hlin : ∀ a b : P, a ≤ b ∨ b ≤ a)
    (hP : ∀ r q s : P, r + q < s → ∃ r', r < r' ∧ r' + q ≤ s)
    (F G : P ⥤ Type u) (hG : IsRightContinuous G) :
    IsRightContinuous (internalHom F G) := by
  have hshift : ∀ {s s' : P} (h : s ≤ s') (α : (internalHom F G).obj s) (t : P) (x : F.obj t),
      persEv ((internalHom F G).map (homOfLE h) α) t x =
        persGm G (add_le_add_left h t) (persEv α t x) := fun _ _ _ _ => rfl
  have hext : ∀ {r : P} (β β' : (internalHom F G).obj r),
      (∀ t x, persEv β t x = persEv β' t x) → β = β' := by
    intro r β β' h
    change F ⟶ shift r G at β β'
    exact NatTrans.ext (funext fun t => ConcreteCategory.hom_ext _ _ fun x => h t x)
  apply rightCont_intro
  · intro r β β' hs
    apply hext
    intro t x
    apply rightCont_inj hG (r + t)
    intro u hu
    obtain ⟨s, hrs, hsu⟩ := hP r t u hu
    have key : ∀ γ : (internalHom F G).obj r, persGm G hu.le (persEv γ t x) =
        persGm G hsu (persEv ((internalHom F G).map (homOfLE hrs.le) γ) t x) := by
      intro γ
      rw [hshift, persGm_comp]
    change persGm G hu.le (persEv β t x) = persGm G hu.le (persEv β' t x)
    rw [key β, key β']
    exact congrArg (fun z => persGm G hsu (persEv z t x)) (hs s hrs)
  · intro r α hα
    have hα' : ∀ s s' (hs : r < s) (hs' : r < s') (h : s ≤ s') (t : P) (x : F.obj t),
        persGm G (add_le_add_left h t) (persEv (α s hs) t x) = persEv (α s' hs') t x := by
      intro s s' hs hs' h t x
      exact (hshift h (α s hs) t x).symm.trans
        (congrArg (fun z => persEv z t x) (hα s s' hs hs' h))
    have exist : ∀ (t : P) (x : F.obj t), ∃ y : G.obj (r + t),
        ∀ s (hs : r < s), persGm G (add_le_add_left hs.le t) y = persEv (α s hs) t x := by
      intro t x
      choose s0 hs0 hs0u using fun (u : P) (hu : r + t < u) => hP r t u hu
      let xu : ∀ u : P, r + t < u → G.obj u := fun u hu =>
        persGm G (hs0u u hu) (persEv (α (s0 u hu) (hs0 u hu)) t x)
      have agree : ∀ u (hu : r + t < u) s (hs : r < s) (hsu : s + t ≤ u),
          persGm G hsu (persEv (α s hs) t x) = xu u hu := by
        intro u hu s hs hsu
        rcases hlin s (s0 u hu) with h | h
        · show _ = persGm G (hs0u u hu) _
          rw [← hα' s (s0 u hu) hs (hs0 u hu) h t x, persGm_comp]
        · show _ = persGm G (hs0u u hu) _
          rw [← hα' (s0 u hu) s (hs0 u hu) hs h t x, persGm_comp]
      obtain ⟨y, hy⟩ := rightCont_surj hG (r + t) xu (by
        intro u u' hu hu' h
        rw [← agree u' hu' (s0 u hu) (hs0 u hu) ((hs0u u hu).trans h)]
        exact persGm_comp G _ _ _)
      refine ⟨y, fun s hs => ?_⟩
      apply rightCont_inj hG (s + t)
      intro u hu
      have hru : r + t < u := lt_of_le_of_lt (add_le_add_left hs.le t) hu
      change persGm G hu.le (persGm G _ y) = persGm G hu.le (persEv (α s hs) t x)
      rw [persGm_comp]
      exact (hy u hru).trans (agree u hru s hs hu.le).symm
    choose β0 hβ0 using exist
    let β : F ⟶ shift r G :=
      { app := fun t => TypeCat.ofHom (fun x => β0 t x)
        naturality := by
          intro t t' f
          apply ConcreteCategory.hom_ext
          intro x
          have hf : t ≤ t' := leOfHom f
          change β0 t' (F.map f x) = persGm G (add_le_add_right hf r) (β0 t x)
          apply rightCont_inj hG (r + t')
          intro u hu
          obtain ⟨s, hrs, hsu⟩ := hP r t' u hu
          have hn : persGm G (add_le_add_right hf s) (persEv (α s hrs) t x) =
              persEv (α s hrs) t' (F.map f x) :=
            (ConcreteCategory.congr_hom ((α s hrs : F ⟶ shift s G).naturality f) x).symm
          have e1 : persGm G hu.le (β0 t' (F.map f x)) = persGm G hsu (persEv (α s hrs) t' (F.map f x)) := by
            rw [← hβ0 t' (F.map f x) s hrs]
            exact (persGm_comp G _ _ _).symm
          have e2 : persGm G hu.le (persGm G (add_le_add_right hf r) (β0 t x)) =
              persGm G hsu (persEv (α s hrs) t' (F.map f x)) := by
            rw [← hn, ← hβ0 t x s hrs, persGm_comp, persGm_comp, persGm_comp]
          exact e1.trans e2.symm }
    refine ⟨β, fun s hs => ?_⟩
    apply hext
    intro t x
    exact hβ0 t x s hs


end Shift

/-! ### The functor `(-)#` -/

section Sharp

open NNReal

variable {C : Type w} [Category.{v} C]

/-- The natural map `F ⟶ F^r`. -/
def shiftUnit (r : ℝ≥0) (F : ℝ≥0 ⥤ C) : F ⟶ shift r F where
  app s := F.map (homOfLE (le_add_self))
  naturality := by
    intros; simp only [shift, Functor.comp_map, ← Functor.map_comp]; rfl

/-- The diagram `r ↦ F (r + s)` over the positive reals, whose limit is `F# (s)`. -/
def sharpDiagram (F : ℝ≥0 ⥤ C) (s : ℝ≥0) : {r : ℝ≥0 // 0 < r} ⥤ C where
  obj r := F.obj (r.1 + s)
  map {r r'} f := F.map (homOfLE (add_le_add_left (show r.1 ≤ r'.1 from leOfHom f) s))
  map_id := by intros; exact F.map_id _
  map_comp := by intros; exact F.map_comp _ _

/-- `s ↦ (r ↦ F (r + s))`, a functor into diagrams over the positive reals. -/
def sharpFunctor (F : ℝ≥0 ⥤ C) : ℝ≥0 ⥤ ({r : ℝ≥0 // 0 < r} ⥤ C) where
  obj := sharpDiagram F
  map {s s'} f :=
    { app := fun r => F.map (homOfLE (add_le_add_right (leOfHom f) r.1))
      naturality := by
        intros; simp only [sharpDiagram, ← Functor.map_comp]; rfl }
  map_id := by
    intro s; ext r
    exact F.map_id _
  map_comp := by
    intro s s' s'' f g; ext r
    exact F.map_comp _ _

/-- Universal right continuous approximation: `F# = lim_{r > 0} F^r`, i.e.
`F# (s) = lim_{r > 0} F (r + s)`. -/
noncomputable def sharp [Limits.HasLimitsOfSize.{0, 0} C] (F : ℝ≥0 ⥤ C) : ℝ≥0 ⥤ C :=
  sharpFunctor F ⋙ Limits.lim

/-- The natural morphism `η : F ⟶ F#`. -/
noncomputable def sharpUnit [Limits.HasLimitsOfSize.{0, 0} C] (F : ℝ≥0 ⥤ C) : F ⟶ sharp F where
  app s := Limits.limit.lift (sharpDiagram F s)
    { pt := F.obj s
      π := { app := fun r => F.map (homOfLE le_add_self)
             naturality := by
               intros; simp only [sharpDiagram, Functor.const_obj_map]
               erw [Category.id_comp, ← Functor.map_comp]; rfl } }
  naturality := by
    intro s s' f
    apply Limits.limit.hom_ext; intro r
    simp [sharp, sharpFunctor, sharpDiagram]
    erw [Limits.limit.lift_π, Limits.limit.lift_π_assoc]
    simp [← Functor.map_comp]
    rfl

/-- Proposition 2.6.12: up to arbitrarily small shifts, `F` and `F#` are indistinguishable.
There are morphisms `F → (F#)^ε` and `F# → F^ε` whose composites are the natural maps
`F → F^{2ε}` and `F# → (F#)^{2ε}`. -/
theorem sharp_interleaved [Limits.HasLimitsOfSize.{0, 0} C] (F : ℝ≥0 ⥤ C) (ε : ℝ≥0)
    (hε : 0 < ε) :
    ∃ (a : F ⟶ shift ε (sharp F)) (b : sharp F ⟶ shift ε F),
      a ≫ shiftMap ε b = shiftUnit ε F ≫ shiftUnit ε (shift ε F) ∧
      b ≫ shiftMap ε a = shiftUnit ε (sharp F) ≫ shiftUnit ε (shift ε (sharp F)) := by
  let b : sharp F ⟶ shift ε F :=
    { app := fun s => limit.π (sharpDiagram F s) ⟨ε, hε⟩
      naturality := by
        intro s t f
        change limMap ((sharpFunctor F).map f) ≫ limit.π _ ⟨ε, hε⟩ = _
        erw [limMap_π]
        rfl }
  let a : F ⟶ shift ε (sharp F) := sharpUnit F ≫ shiftUnit ε (sharp F)
  refine ⟨a, b, ?_, ?_⟩
  · ext s
    dsimp [a, b, shiftMap, shiftUnit, sharpUnit, sharp, shift, sharpFunctor, sharpDiagram, addLeft]
    erw [Category.assoc, limMap_π, limit.lift_π_assoc]
  · ext s
    apply limit.hom_ext
    intro r
    dsimp [a, b, shiftMap, shiftUnit, sharpUnit, sharp, shift, sharpFunctor, sharpDiagram, addLeft]
    simp only [Category.assoc]
    erw [limMap_π, limMap_π_assoc, limit.lift_π_assoc]
    dsimp
    rw [← F.map_comp, ← F.map_comp]
    have ht : 0 < r.1 + ε + ε := by positivity
    have h₁ : ε ≤ r.1 + ε + ε := le_trans le_add_self le_self_add
    have h₂ : r.1 ≤ r.1 + ε + ε := le_trans le_self_add le_self_add
    have w₁ := limit.w (sharpDiagram F s)
      (homOfLE h₁ : (⟨ε, hε⟩ : {r : ℝ≥0 // 0 < r}) ⟶ ⟨r.1 + ε + ε, ht⟩)
    have w₂ := limit.w (sharpDiagram F s)
      (homOfLE h₂ : r ⟶ ⟨r.1 + ε + ε, ht⟩)
    have map_heq {a b c : ℝ≥0} (f : a ⟶ b) (g : a ⟶ c) (h : b = c) :
        HEq (F.map f) (F.map g) := by
      subst c
      have : f = g := Subsingleton.elim _ _
      subst g
      rfl
    convert w₁.trans w₂.symm using 1 <;>
      simp only [sharpDiagram, add_assoc] <;> congr 1
    all_goals first
      | simp only [add_assoc]
      | exact map_heq _ _ (by simp only [add_assoc])



/-- Lemma 2.6.13: if `s < r` and `η a = η b` in `F# (s)` then `φ_{s,r} a = φ_{s,r} b`. -/
theorem sharpUnit_injective_after_shift (F : ℝ≥0 ⥤ Type u) (s r : ℝ≥0) (hsr : s < r)
    (a b : F.obj s) (h : (sharpUnit F).app s a = (sharpUnit F).app s b) :
    F.map (homOfLE hsr.le) a = F.map (homOfLE hsr.le) b := by
  have hpos : 0 < r - s := tsub_pos_of_lt hsr
  have h2 := congrArg (Limits.limit.π (sharpDiagram F s) ⟨r - s, hpos⟩) h
  have e : (r - s) + s = r := tsub_add_cancel_of_le hsr.le
  have key : ∀ x : F.obj s, Limits.limit.π (sharpDiagram F s) ⟨r - s, hpos⟩
      ((sharpUnit F).app s x) = F.map (homOfLE le_add_self) x := by
    intro x
    simp only [sharpUnit]
    exact Limits.limit.lift_π_apply _ _ _
  rw [key, key] at h2
  have h3 := congrArg (F.map (homOfLE e.le)) h2
  simpa [← types_comp_apply (F.map _) (F.map _), ← Functor.map_comp] using h3

end Sharp

end Persistent

end ScoccolaPhd
