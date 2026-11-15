import Mathlib
import ScoccolaPhd.Chapter6Section7PersistentSets

/-!
# Ackerman's equivalence of ultrametric spaces and flabby separated persistent sets

Theorem 3.12 of N. L. Ackerman, *Completeness in Generalized Ultrametric Spaces* (2013),
Definitions 3.13 and 3.16 and Claims 3.14–3.20, specialized to nonnegative real radii.
Source: https://people.math.harvard.edu/~nate/papers/published/201x/2013/completeness%20in%20generalized%20ultrametric%20spaces/preprint.pdf
This is the categorical assertion cited in Scoccola's Theorem 6.7.10.
-/

universe u

namespace ScoccolaPhd

open CategoryTheory CategoryTheory.Limits
open scoped NNReal ENNReal

/-- **[Ack13, Definition 3.16].** Distance on the zero stage: the infimum of the radii
at which two elements have equal images. -/
noncomputable def separatedClusterDist (F : ℝ≥0 ⥤ Type u) (x y : F.obj 0) : ℝ≥0∞ :=
  ⨅ (r : ℝ≥0) (_ : F.map (homOfLE (show 0 ≤ r from bot_le)) x =
    F.map (homOfLE (show 0 ≤ r from bot_le)) y), (r : ℝ≥0∞)

/-- Closedness of the equality relation, used in [Ack13, Claims 3.17 and 3.19]. -/
theorem separatedClusterDist_le (F : ℝ≥0 ⥤ Type u) (hF : IsSeparated F)
    (x y : F.obj 0) (r : ℝ≥0) :
    separatedClusterDist F x y ≤ (r : ℝ≥0∞) ↔
      F.map (homOfLE (show 0 ≤ r from bot_le)) x =
        F.map (homOfLE (show 0 ≤ r from bot_le)) y := by
  constructor
  · intro hd
    apply hF r
    intro s hrs
    have hlt : separatedClusterDist F x y < (s : ℝ≥0∞) :=
      hd.trans_lt (ENNReal.coe_lt_coe.mpr hrs)
    obtain ⟨q, hq⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hxy, hqs⟩ := iInf_lt_iff.mp hq
    have hqs' : q ≤ s := (ENNReal.coe_lt_coe.mp hqs).le
    have heq := congrArg (fun z => F.map (homOfLE hqs') z) hxy
    simpa only [← types_comp_apply, ← F.map_comp, homOfLE_comp] using heq
  · intro hxy
    exact iInf_le_of_le r (iInf_le_of_le hxy le_rfl)

/-- **[Ack13, Claim 3.17].** The zero stage of a separated persistent set has a canonical
extended ultrametric. -/
noncomputable def separatedUltraMet (F : ℝ≥0 ⥤ Type u) (hF : IsSeparated F) : UltraMet.{u} := by
  let d := separatedClusterDist F
  have hself : ∀ x, d x x = 0 := fun x => le_antisymm
    ((separatedClusterDist_le F hF x x 0).mpr rfl) bot_le
  have hsymm : ∀ x y, d x y = d y x := by
    intro x y
    apply le_antisymm <;> unfold d separatedClusterDist <;>
      refine le_iInf fun r => le_iInf fun h => ?_
    · exact iInf_le_of_le r (iInf_le_of_le h.symm le_rfl)
    · exact iInf_le_of_le r (iInf_le_of_le h.symm le_rfl)
  have hultra : ∀ x y z, d x z ≤ max (d x y) (d y z) := by
    intro x y z
    apply le_of_forall_gt
    intro ε hε
    obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    have hxy := (separatedClusterDist_le F hF x y r).mp ((le_max_left _ _).trans hr.le)
    have hyz := (separatedClusterDist_le F hF y z r).mp ((le_max_right _ _).trans hr.le)
    exact ((separatedClusterDist_le F hF x z r).mpr (hxy.trans hyz)).trans_lt hrε
  let P := PseudoEMetricSpace.ofEDist d hself hsymm (fun x y z =>
    (hultra x y z).trans (max_le (le_add_of_nonneg_right bot_le) (le_add_of_nonneg_left bot_le)))
  letI : EMetricSpace (F.obj 0) := {
    toPseudoEMetricSpace := P
    eq_of_edist_eq_zero := by
      intro x y hxy
      have heq := (separatedClusterDist_le F hF x y 0).mp hxy.le
      simpa only [homOfLE_refl, F.map_id, types_id_apply] using heq
  }
  exact ⟨F.obj 0, hultra⟩

/-- **[Ack13, Claim 3.19].** The map from reconstructed clusters back to a stage of `F`. -/
noncomputable def separatedStageMap (F : ℝ≥0 ⥤ Type u) (hF : IsSeparated F) (r : ℝ≥0) :
    Quotient ((separatedUltraMet F hF).slSetoid r) → F.obj r :=
  Quotient.lift (fun x => F.map (homOfLE (show 0 ≤ r from bot_le)) x)
    (fun x y hxy => (separatedClusterDist_le F hF x y r).mp hxy)

/-- **[Ack13, Claim 3.19].** Flabbiness makes the reconstructed stage map an isomorphism. -/
noncomputable def separatedStageEquiv (F : ℝ≥0 ⥤ Type u)
    (hfl : IsFlabby F) (hsep : IsSeparated F) (r : ℝ≥0) :
    Quotient ((separatedUltraMet F hsep).slSetoid r) ≃ F.obj r :=
  Equiv.ofBijective (separatedStageMap F hsep r) ⟨by
    intro a b
    induction a using Quotient.inductionOn with | _ x =>
      induction b using Quotient.inductionOn with | _ y =>
        intro hxy
        exact Quotient.sound ((separatedClusterDist_le F hsep x y r).mpr hxy), by
    intro z
    obtain ⟨x, hx⟩ := hfl 0 r bot_le z
    exact ⟨Quotient.mk _ x, hx⟩⟩

/-- **[Ack13, Claim 3.19].** Single linkage of the reconstructed ultrametric recovers `F`. -/
noncomputable def separatedSingleLinkageIso (F : ℝ≥0 ⥤ Type u)
    (hfl : IsFlabby F) (hsep : IsSeparated F) :
    (separatedUltraMet F hsep).singleLinkage ≅ F :=
  NatIso.ofComponents (fun r => (separatedStageEquiv F hfl hsep r).toIso) (by
    intro r s h
    ext q
    induction q using Quotient.inductionOn with | _ x =>
      change F.map (homOfLE (show 0 ≤ s from bot_le)) x =
        F.map h (F.map (homOfLE (show 0 ≤ r from bot_le)) x)
      exact ConcreteCategory.congr_hom
        (F.map_comp (homOfLE (show (0 : ℝ≥0) ≤ r from bot_le)) h) x)

/-- The zero-radius cluster identifies a point uniquely, used in [Ack13, Claim 3.20]. -/
noncomputable def UltraMet.zeroClusterEquiv (X : UltraMet.{u}) :
    X.carrier ≃ Quotient (X.slSetoid 0) :=
  Equiv.ofBijective (Quotient.mk (X.slSetoid 0)) ⟨by
    intro x y h
    have hd : edist x y ≤ (0 : ℝ≥0∞) := @Quotient.exact X.carrier (X.slSetoid 0) _ _ h
    exact edist_eq_zero.mp (le_antisymm hd bot_le), Quotient.mk_surjective⟩

/-- Faithfulness in [Ack13, Theorem 3.12]: the zero stage remembers the underlying map. -/
theorem singleLinkage_faithful : singleLinkageFunctor.{u}.Faithful := by
  constructor
  intro X Y f g h
  apply Subtype.ext
  funext x
  apply Y.zeroClusterEquiv.injective
  exact congrArg (fun η => η.app 0 (Quotient.mk (X.slSetoid 0) x)) h

set_option backward.isDefEq.respectTransparency false in
/-- Fullness in [Ack13, Theorem 3.12]: a natural transformation is determined by its zero
component, which is non-expanding by naturality at every radius. -/
theorem singleLinkage_full : singleLinkageFunctor.{u}.Full := by
  constructor
  intro X Y η
  let f : X.carrier → Y.carrier := fun x =>
    Y.zeroClusterEquiv.symm (η.app 0 (Quotient.mk (X.slSetoid 0) x))
  have hf0 : ∀ x, Quotient.mk (Y.slSetoid 0) (f x) =
      η.app 0 (Quotient.mk (X.slSetoid 0) x) := fun x => Y.zeroClusterEquiv.apply_symm_apply _
  have hfr : ∀ (r : ℝ≥0) x, Quotient.mk (Y.slSetoid r) (f x) =
      η.app r (Quotient.mk (X.slSetoid r) x) := by
    intro r x
    have hz := congrArg (fun q => Y.singleLinkage.map
      (homOfLE (show (0 : ℝ≥0) ≤ r from bot_le)) q) (hf0 x)
    have hn := ConcreteCategory.congr_hom (η.naturality
      (homOfLE (show (0 : ℝ≥0) ≤ r from bot_le))) (Quotient.mk (X.slSetoid 0) x)
    exact hz.trans hn.symm
  have hf : IsDistNonIncreasing f := by
    intro x y
    apply le_of_forall_gt
    intro ε hε
    obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    have hxy : Quotient.mk (X.slSetoid r) x = Quotient.mk (X.slSetoid r) y :=
      Quotient.sound hr.le
    have heq := congrArg (η.app r) hxy
    rw [← hfr r x, ← hfr r y] at heq
    have hd : edist (f x) (f y) ≤ (r : ℝ≥0∞) :=
      @Quotient.exact Y.carrier (Y.slSetoid r) _ _ heq
    exact hd.trans_lt hrε
  refine ⟨⟨f, hf⟩, ?_⟩
  ext r q
  induction q using Quotient.inductionOn with | _ x => exact hfr r x

/-- Flabbiness and separation are invariant under isomorphism, as used in
[Ack13, Theorem 3.12]. -/
theorem singleLinkage_iso_properties (X : UltraMet.{u}) {F : ℝ≥0 ⥤ Type u}
    (e : X.singleLinkage ≅ F) : IsFlabby F ∧ IsSeparated F := by
  have hnat : ∀ r s (h : r ≤ s) q,
      F.map (homOfLE h) (e.hom.app r q) = e.hom.app s (X.singleLinkage.map (homOfLE h) q) := by
    intro r s h q
    exact (ConcreteCategory.congr_hom (e.hom.naturality (homOfLE h)) q).symm
  have hnatInv : ∀ r s (h : r ≤ s) q,
      X.singleLinkage.map (homOfLE h) (e.inv.app r q) = e.inv.app s (F.map (homOfLE h) q) := by
    intro r s h q
    exact (ConcreteCategory.congr_hom (e.inv.naturality (homOfLE h)) q).symm
  constructor
  · intro r s h y
    obtain ⟨q, rfl⟩ := (isIso_iff_bijective (e.hom.app s)).mp (by infer_instance) |>.2 y
    obtain ⟨x, hx⟩ := X.singleLinkage_flabby r s h q
    exact ⟨e.hom.app r x, (hnat r s h x).trans (congrArg (e.hom.app s) hx)⟩
  · intro r a b hab
    apply ((isIso_iff_bijective (e.inv.app r)).mp (by infer_instance)).1
    apply X.linkageClass_separated (fun _ => rfl) (fun _ _ _ _ => rfl) r
    intro s hs
    rw [hnatInv, hnatInv, hab s hs]

/-- **Theorem 6.7.10 ([Ack13]).** Single linkage is an equivalence between extended
ultrametric spaces and flabby, separated persistent sets. On totally bounded spaces,
completeness is equivalent to right continuity.

**Gap (error).** The thesis claims the completeness equivalence without total boundedness.
On `ℕ`, put `d(n,m) = 0` for `n = m`, and `1 + 1/(min(n,m)+1)` otherwise. Every Cauchy
sequence is eventually constant, so this ultrametric is complete. At radius `1` the clusters
are singletons, whereas the compatible tail clusters at radii `s > 1` have empty intersection;
hence single linkage is not right continuous. Ackerman distinguishes ordinary Cauchy
completeness from strong Cauchy completeness (§2.3, especially Theorem 2.20); they cannot
be identified here. We restrict the final assertion to totally bounded spaces, where the
compactness argument of Theorem 6.7.11 establishes the claimed equivalence. -/
theorem singleLinkage_equivalence :
    ∃ SL : UltraMet.{u} ⥤ (ℝ≥0 ⥤ Type u),
      (∀ X r, (SL.obj X).obj r = Quotient (X.slSetoid r)) ∧ SL.Full ∧ SL.Faithful ∧
      (∀ F : ℝ≥0 ⥤ Type u, (∃ X, Nonempty (SL.obj X ≅ F)) ↔ IsFlabby F ∧ IsSeparated F) ∧
      (∀ X, IsTotallyBoundedEP X.carrier →
        (IsCompleteEP X.carrier ↔ IsRightContinuous (SL.obj X))) := by
  refine ⟨singleLinkageFunctor, (fun _ _ => rfl), singleLinkage_full,
    singleLinkage_faithful, ?_, ?_⟩
  · intro F
    constructor
    · rintro ⟨X, ⟨e⟩⟩
      exact singleLinkage_iso_properties X e
    · rintro ⟨hfl, hsep⟩
      exact ⟨separatedUltraMet F hsep, ⟨separatedSingleLinkageIso F hfl hsep⟩⟩
  · intro X htb
    constructor
    · intro hc
      have hcompact := isCompactEP_iff_complete_and_totallyBounded.mpr ⟨hc, htb⟩
      exact ((singleLinkage_compact singleLinkageFunctor (fun _ _ => rfl)
        (fun _ _ _ _ _ => rfl) X).2.mp hcompact).2
    · exact X.complete_of_linkage_rightContinuous (fun _ => rfl) (fun _ _ _ _ => rfl)

end ScoccolaPhd
