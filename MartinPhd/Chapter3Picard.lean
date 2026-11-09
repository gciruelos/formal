import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import MartinPhd.Chapter2CoalgebraL

/-!
# Chapter 3 (Picard groups: Sections 3.1–3.3)

Contents:
* Comodules
* Picard
* Examples
-/

section Comodules

/-
Outline of

  Fernando Daniel Martin, *Aspectos homológicos de la teoría de especies*,
  PhD thesis, Universidad de Buenos Aires, 2024 (advisor: M. Suárez-Álvarez).

# Chapter 3 — El grupo de Picard (§3.1 Generalities)

Outline pass. Throughout `k` has characteristic zero and `c` is a **connected** coalgebra in
the category `Sp` of combinatorial species (`c(∅) ≅ k`).

## Modelling choices

* Comodules and bicomodules over a comonoid `c` of a monoidal category `C` are defined for
  an arbitrary `C` (compare `RightComod`, `Bicomod` of §1.2, specific to `GL`-species).
* `Sp` is `k`-linear, abelian with enough injective comodules; the cotensor product
  `x □ y = ker(ρ_x ⊗ id - id ⊗ λ_y)` and the monoidal structure of `c`-bicomodules are recorded
  but their (routine) verification is deferred.
-/

open CategoryTheory MonoidalCategory Limits

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

namespace Sp

variable {k : Type} [Field k]

instance : Preadditive (Species k) := inferInstanceAs (Preadditive (Core FintypeCat.{0} ⥤ ModuleCat.{0} k))
instance : HasKernels (Species k) := inferInstanceAs (HasKernels (Core FintypeCat.{0} ⥤ ModuleCat.{0} k))

section Comodules

variable {C : Type 1} [Category.{1} C] [MonoidalCategory C] (c : Comon C)

/-- A left `c`-comodule. -/
structure LComod where
  X : C
  coact : X ⟶ c.X ⊗ X
  counit_coact : coact ≫ ComonObj.counit (X := c.X) ▷ X = (λ_ X).inv
  coact_assoc : coact ≫ ComonObj.comul (X := c.X) ▷ X ≫ (α_ c.X c.X X).hom = coact ≫ c.X ◁ coact

/-- A right `c`-comodule. -/
structure RComod where
  X : C
  coact : X ⟶ X ⊗ c.X
  coact_counit : coact ≫ X ◁ ComonObj.counit (X := c.X) = (ρ_ X).inv
  coact_assoc : coact ≫ X ◁ ComonObj.comul (X := c.X) = coact ≫ coact ▷ c.X ≫ (α_ X c.X c.X).hom

/-- A `c`-bicomodule: left and right coactions that commute. -/
structure BiComod where
  X : C
  coactR : X ⟶ X ⊗ c.X
  coactL : X ⟶ c.X ⊗ X
  coactR_counit : coactR ≫ X ◁ ComonObj.counit (X := c.X) = (ρ_ X).inv
  coactR_assoc : coactR ≫ X ◁ ComonObj.comul (X := c.X) = coactR ≫ coactR ▷ c.X ≫ (α_ X c.X c.X).hom
  coactL_counit : coactL ≫ ComonObj.counit (X := c.X) ▷ X = (λ_ X).inv
  coactL_assoc : coactL ≫ ComonObj.comul (X := c.X) ▷ X ≫ (α_ c.X c.X X).hom = coactL ≫ c.X ◁ coactL
  compat : coactL ≫ c.X ◁ coactR = coactR ≫ coactL ▷ c.X ≫ (α_ c.X X c.X).hom

variable {c}

/-- Morphisms of left comodules. -/
@[ext] structure LComod.Hom (M N : LComod c) where
  hom : M.X ⟶ N.X
  comm : hom ≫ N.coact = M.coact ≫ c.X ◁ hom

/-- Morphisms of bicomodules. -/
@[ext] structure BiComod.Hom (M N : BiComod c) where
  hom : M.X ⟶ N.X
  commR : hom ≫ N.coactR = M.coactR ≫ hom ▷ c.X
  commL : hom ≫ N.coactL = M.coactL ≫ c.X ◁ hom

instance : Category (LComod c) where
  Hom := LComod.Hom
  id M := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc, MonoidalCategory.whiskerLeft_comp]⟩
  id_comp f := by apply LComod.Hom.ext; exact Category.id_comp f.hom
  comp_id f := by apply LComod.Hom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply LComod.Hom.ext; exact Category.assoc f.hom g.hom h.hom

/-- Morphisms of right comodules. -/
@[ext] structure RComod.Hom (M N : RComod c) where
  hom : M.X ⟶ N.X
  comm : hom ≫ N.coact = M.coact ≫ hom ▷ c.X

instance : Category (RComod c) where
  Hom := RComod.Hom
  id M := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc,
      MonoidalCategory.comp_whiskerRight]⟩
  id_comp f := by apply RComod.Hom.ext; exact Category.id_comp f.hom
  comp_id f := by apply RComod.Hom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply RComod.Hom.ext; exact Category.assoc f.hom g.hom h.hom

instance : Category (BiComod c) where
  Hom := BiComod.Hom
  id M := ⟨𝟙 _, by simp, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.commR, ← Category.assoc, f.commR, Category.assoc,
      MonoidalCategory.comp_whiskerRight], by
    rw [Category.assoc, g.commL, ← Category.assoc, f.commL, Category.assoc,
      MonoidalCategory.whiskerLeft_comp]⟩
  id_comp f := by apply BiComod.Hom.ext <;> exact Category.id_comp f.hom
  comp_id f := by apply BiComod.Hom.ext <;> exact Category.comp_id f.hom
  assoc f g h := by apply BiComod.Hom.ext <;> exact Category.assoc f.hom g.hom h.hom

end Comodules

variable (c : Comon (Species k))

/-- The **cotensor product** `x □ y = ker(ρ_x ⊗ id_y - id_x ⊗ λ_y) ⊆ x ⊗ y` of a right and
a left `c`-comodule. -/
def cotensor (x : RComod c) (y : LComod c) : Species k :=
  kernel (x.coact ▷ y.X ≫ (α_ x.X c.X y.X).hom - x.X ◁ y.coact)

/-- The cotensor product of `c`-bicomodules, a `c`-bicomodule with the coactions
`λ_x ⊗ id_y` and `id_x ⊗ ρ_y`. -/
def BiComod.cotensor (x y : BiComod c) : BiComod c := sorry

/-- The unit of `□` is `c` itself, with the coactions given by the comultiplication. -/
def BiComod.unit : BiComod c where
  X := c.X
  coactR := ComonObj.comul
  coactL := ComonObj.comul
  coactR_counit := ComonObj.comul_counit c.X
  coactR_assoc := ComonObj.comul_assoc c.X
  coactL_counit := ComonObj.counit_comul c.X
  coactL_assoc := (ComonObj.comul_assoc c.X).symm
  compat := ComonObj.comul_assoc c.X

/-- The cotensor product makes the category of `c`-bicomodules monoidal, with unit `c`. -/
axiom instMonoidalCategoryBiComodSpecies {k : Type} [Field k] (c : Comon (Species k)) : MonoidalCategory (BiComod c)
attribute [instance] instMonoidalCategoryBiComodSpecies

/-- The **trivial coalgebra** `k` (concentrated at `∅`), a subcoalgebra of `c`. -/
def trivCoalg : Species k := one

/-- The **coinvariants** `k □ x ⊆ c □ x ≅ x` of a left comodule: the elements with
`λ(z) = 1 ⊗ z`.

**Note.** The thesis assumes `c` is connected throughout this chapter.
For an arbitrary coalgebra there is no canonical inclusion of the trivial coalgebra into `c`,
so these coinvariants cannot be constructed as described without additional data. -/
def coinvariants (x : LComod c) : Species k := sorry

/-- The functor `- □ x` from right comodules to species (`y ↦ y □ x`), for a fixed left
comodule `x`. -/
def cotensorRight (x : LComod c) : RComod c ⥤ Species k := sorry

/-- **Proposition 3.1** ([BW03, 10.4]). If `x` is a left `c`-comodule, the functor `- □ x` is
left exact (and symmetrically for `x □ -`). -/
theorem cotensor_leftExact (x : LComod c) : PreservesFiniteLimits (cotensorRight c x) := sorry

/-- **Lemma 3.2** (first-cardinal Nakayama). If `x ≠ 0` is a left comodule and `I` is a finite
set with `x(I) ≠ 0` and `x(K) = 0` for every finite set `K` with `|K| < |I|`, then
`(k □ x)(I) ≠ 0`.

**Note.** The thesis assumes `c` is connected throughout the chapter;
this statement omits that assumption, which is needed for the specified coinvariants. -/
theorem lemma_3_2 (x : LComod c) (I : FintypeCat.{0}) (hI : Nontrivial (x.X.ev I))
    (hlt : ∀ K : FintypeCat.{0}, Nat.card K.obj < Nat.card I.obj → Subsingleton (x.X.ev K)) :
    Nontrivial ((coinvariants c x).ev I) := sorry

/-- **Corollary 3.3** (Nakayama). A left `c`-comodule is zero iff its coinvariants are. -/
theorem corollary_3_3 (x : LComod c) :
    (∀ I, Subsingleton (x.X.ev I)) ↔ ∀ I, Subsingleton ((coinvariants c x).ev I) := sorry

/-- A coalgebra is a left comodule over itself (via `Δ`). -/
def LComod.self : LComod c where
  X := c.X
  coact := ComonObj.comul
  counit_coact := ComonObj.counit_comul c.X
  coact_assoc := (ComonObj.comul_assoc c.X).symm

/-- **Lemma 3.4.** The coinvariants of a connected coalgebra `c`, as a left comodule over
itself, form the trivial coalgebra `k`. -/
theorem lemma_3_4 (hc : IsConnected c.X) : Nonempty (coinvariants c (LComod.self c) ≅ trivCoalg) :=
  sorry

end Sp

end MartinPhd

end
end Comodules

section Picard

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 3 — §3.2 Twisted forms, §3.3 The Picard group of a connected coalgebra
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

namespace Sp

variable {k : Type} [Field k] (c : Comon (Species k))

/-- The endomorphism underlying an automorphism of `c` in `Comon (Species k)`. -/
def autHom {c : Comon (Species k)} (α : Aut c) : c ⟶ c := α.asIso.hom

/-- The inverse of an automorphism. -/
def autInv {c : Comon (Species k)} (α : Aut c) : c ⟶ c := α.asIso.inv

/-- The left comodule `c ⊗ y` with coaction `Δ ⊗ id`. -/
def LComod.induced (y : Species k) : LComod c where
  X := c.X ⊗ y
  coact := ComonObj.comul ▷ y ≫ (α_ c.X c.X y).hom
  counit_coact := by
    rw [Category.assoc, MonoidalCategory.whiskerRight_tensor]
    simp only [Iso.hom_inv_id_assoc]
    rw [← MonoidalCategory.comp_whiskerRight_assoc, ComonObj.counit_comul c.X,
      MonoidalCategory.leftUnitor_tensor_inv]
  coact_assoc := by
    have h := congrArg (fun f => f ▷ y) (ComonObj.comul_assoc c.X)
    simp only [MonoidalCategory.comp_whiskerRight] at h
    sorry

/-- The inclusion of the coinvariants `k □ x ↪ x`. -/
def coinvariants.incl (x : LComod c) : coinvariants c x ⟶ x.X := sorry

/-- The underlying left (right) comodule of a bicomodule, and `c` as a right comodule. -/
def BiComod.toLComod (x : BiComod c) : LComod c where
  X := x.X
  coact := x.coactL
  counit_coact := x.coactL_counit
  coact_assoc := x.coactL_assoc

def BiComod.toRComod (x : BiComod c) : RComod c where
  X := x.X
  coact := x.coactR
  coact_counit := x.coactR_counit
  coact_assoc := x.coactR_assoc

/-- A coalgebra is a right comodule over itself (via `Δ`). -/
def RComod.self : RComod c where
  X := c.X
  coact := ComonObj.comul
  coact_counit := ComonObj.comul_counit c.X
  coact_assoc := ComonObj.comul_assoc c.X

/-- **Lemma 3.5.** If `π : x → k □ x` is a section (as species) of the inclusion and `x` is an
injective left `c`-comodule, then `ψ = (id ⊗ π) ∘ λ : x → c ⊗ (k □ x)` is an isomorphism of
left `c`-comodules. (More generally, `ψ` is an epimorphism when `Cotor¹_c(k, x) = 0`.) -/
theorem lemma_3_5 (x : LComod c) (hx : Injective x)
    (π : x.X ⟶ coinvariants c x) (hπ : coinvariants.incl c x ≫ π = 𝟙 _) :
    ∃ ψ : x ⟶ LComod.induced c (coinvariants c x),
      ψ.hom = x.coact ≫ c.X ◁ π ∧ IsIso ψ := sorry

/-! ## §3.2 Twisted forms -/

variable {c}

/-- The **twisted form** `φ x ψ` of a `c`-bicomodule `x` by coalgebra endomorphisms `φ, ψ` of `c`:
the same species with coactions `(φ ⊗ id) ∘ λ` and `(id ⊗ ψ) ∘ ρ`. -/
axiom BiComod.twist {k : Type} [Field k] {c : Comon (Species k)} (φ ψ : c ⟶ c) (x : BiComod c) : BiComod c

/-- The coalgebra `c` as a `c`-bicomodule (coactions by `Δ`). -/
def BiComod.self (c : Comon (Species k)) : BiComod c := BiComod.unit c

/-- Twisted forms compose: `φ₂ (φ₁ x ψ₁) ψ₂ ≅ (φ₂ φ₁) x (ψ₂ ψ₁)`. -/
theorem twist_twist (φ₁ ψ₁ φ₂ ψ₂ : c ⟶ c) (x : BiComod c) :
    Nonempty (BiComod.twist φ₂ ψ₂ (BiComod.twist φ₁ ψ₁ x) ≅ BiComod.twist (φ₁ ≫ φ₂) (ψ₁ ≫ ψ₂) x) :=
  sorry

/-- **Lemma 3.7.** If `α, β, γ` are coalgebra automorphisms of `c`, `α⁻¹ : βcγ → α(βcγ)α` is an
isomorphism of bicomodules; in particular `c_α ≅ α⁻¹ c`. -/
theorem lemma_3_7 (α β γ : Aut c) :
    Nonempty (BiComod.twist (autHom β) (autHom γ) (BiComod.self c) ≅
      BiComod.twist ((autHom β) ≫ (autInv α)) ((autHom γ) ≫ (autInv α)) (BiComod.self c)) := sorry

/-- A bicomodule `x` is **invertible** if there is a bicomodule `y` with
`x □ y ≅ c ≅ y □ x`. -/
def BiComod.IsInvertible (x : BiComod c) : Prop :=
  ∃ y : BiComod c, Nonempty (BiComod.cotensor c x y ≅ BiComod.unit c) ∧
    Nonempty (BiComod.cotensor c y x ≅ BiComod.unit c)

/-- **Lemma 3.6.** (`c` connected.) An invertible bicomodule is isomorphic to `c` both as a left and
as a right comodule. (Not as a bicomodule in general.) -/
theorem lemma_3_6 (hc : IsConnected c.X) (x : BiComod c) (hx : x.IsInvertible) :
    Nonempty (x.toLComod ≅ LComod.self c) ∧ Nonempty (x.toRComod ≅ RComod.self c) := sorry

/-- **Lemma 3.8.** If `α` is a coalgebra automorphism of `c`, the bicomodule `c_α` is
invertible with inverse `_α c`. -/
theorem lemma_3_8 (α : Aut c) :
    (BiComod.twist (𝟙 c) (autHom α) (BiComod.self c)).IsInvertible := sorry

/-- **Proposition 3.9.** If `x` is a `c`-bicomodule isomorphic to `c` as right comodule, there is
a coalgebra *endomorphism* `α` with `x ≅ _α c` (twisting on the left). Connectedness is not
needed. -/
theorem prop_3_9 (x : BiComod c) (h : Nonempty (x.toRComod ≅ RComod.self c)) :
    ∃ α : c ⟶ c, Nonempty (x ≅ BiComod.twist α (𝟙 c) (BiComod.self c)) := sorry

/-- **Proposition 3.10.** (`c` connected.) Every invertible bicomodule is isomorphic to `_α c`
for some coalgebra automorphism `α : c → c`. -/
theorem prop_3_10 (hc : IsConnected c.X) (x : BiComod c) (hx : x.IsInvertible) :
    ∃ α : Aut c, Nonempty (x ≅ BiComod.twist (autHom α) (𝟙 c) (BiComod.self c)) := sorry

/-! ## §3.3 The Picard group -/

/-- The **Picard group** of a monoidal category: isomorphism classes of invertible objects under
`⊗`. -/
def Pic (C : Type 1) [Category.{1} C] [MonoidalCategory C] : Type 1 :=
  Quotient (⟨fun x y : {x : C // ∃ y, Nonempty (x ⊗ y ≅ 𝟙_ C) ∧ Nonempty (y ⊗ x ≅ 𝟙_ C)} =>
    Nonempty (x.1 ≅ y.1), ⟨fun x => ⟨Iso.refl _⟩, fun ⟨i⟩ => ⟨i.symm⟩,
      fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩⟩⟩ : Setoid _)

axiom instGroupPic (C : Type 1) [Category.{1} C] [MonoidalCategory C] : Group (Pic C)
attribute [instance] instGroupPic

/-- The Picard group of a coalgebra `c`: that of the category of `c`-bicomodules with `□`. -/
abbrev PicCoalg (c : Comon (Species k)) : Type 1 := Pic (BiComod c)

/-- The morphism of groups `Aut(c) → Pic(c)`, `α ↦ [c_α]`; surjective by Proposition 3.10. -/
axiom autToPic {k : Type} [Field k] {c : Comon (Species k)} : Aut c →* PicCoalg c

/-- Surjectivity of `autToPic` from Proposition 3.10. -/
axiom autToPic_surjective {k : Type} [Field k] {c : Comon (Species k)} (hc : IsConnected c.X) :
    Function.Surjective (autToPic (c := c))

/-- Injectivity condition from Proposition 3.11. -/
axiom autToPic_eq_one_iff {k : Type} [Field k] {c : Comon (Species k)} (α : Aut c) :
    autToPic (c := c) α = 1 ↔ Nonempty (BiComod.twist (𝟙 c) (autHom α) (BiComod.self c) ≅ BiComod.self c)

/-- A coalgebra automorphism is **inner** if `α = (u ⊗ id ⊗ u⁻¹) ∘ (Δ ⊗ id) ∘ Δ` for a
convolution-invertible `u ∈ c* = Hom_Sp(c, k)`. -/
def convolution (φ ψ : c.X ⟶ 𝟙_ (Species k)) : c.X ⟶ 𝟙_ (Species k) :=
  ComonObj.comul ≫ (φ ⊗ₘ ψ) ≫ (λ_ (𝟙_ (Species k))).hom

/-- The subgroup `Inn(c)` of inner automorphisms. -/
axiom Inn {k : Type} [Field k] {c : Comon (Species k)} : Subgroup (Aut c)

/-- **Proposition 3.11.** For a coalgebra automorphism `α`, the twisted form `c_α` is isomorphic
to `c` as a bicomodule iff `α` is inner. -/
axiom prop_3_11 {k : Type} [Field k] {c : Comon (Species k)} (α : Aut c) :
    Nonempty (BiComod.twist (𝟙 c) (autHom α) (BiComod.self c) ≅ BiComod.self c) ↔ α ∈ Inn (c := c)

/-- **Proposition 3.12.** If `c` is connected, `Inn(c)` is trivial. -/
axiom prop_3_12 {k : Type} [Field k] {c : Comon (Species k)} (hc : IsConnected c.X) : Inn (c := c) = ⊥

/-- **Theorem 3.13.** The Picard group of a connected coalgebra is isomorphic to its group of
coalgebra automorphisms: `1 → Inn(c) → Aut(c) → Pic(c) → 1` with `Inn(c) = 1`. -/
theorem theorem_3_13 (hc : IsConnected c.X) : Nonempty (Aut c ≃* PicCoalg c) := by
  have hinj : Function.Injective (autToPic (c := c)) := by
    intro a b hab
    have hker : autToPic (c := c) (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    rw [autToPic_eq_one_iff, prop_3_11, prop_3_12 hc, Subgroup.mem_bot] at hker
    exact mul_inv_eq_one.mp hker
  have hsurj : Function.Surjective (autToPic (c := c)) := autToPic_surjective hc
  exact ⟨MulEquiv.ofBijective (autToPic (c := c)) ⟨hinj, hsurj⟩⟩

end Sp

end MartinPhd

end
end Picard

section Examples

/-
Outline of F. D. Martin, *Aspectos homológicos de la teoría de especies*.

# Chapter 3 — §3.4 The Picard groups of the exponential species and of linear orders
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace MartinPhd

attribute [local instance] Classical.propDecidable

namespace Sp

variable (k : Type) [Field k]

/-- The exponential species as an object of `Comon (Species k)`. -/
def expC : Comon (Species k) := ⟨expSp⟩

/-- The species of linear orders as an object of `Comon (Species k)`. -/
def linC : Comon (Species k) := ⟨L⟩

/-- **Proposition 3.14.** `Θ : k → End_coalg(e)`, `Θ(τ)(I)(e_I) = τ^{|I|} e_I` (with `0⁰ = 1`),
is an isomorphism of monoids (for the multiplicative structure of `k`); it restricts to an
isomorphism of groups `k^× ≅ Aut_coalg(e)`. -/
def Theta (τ : k) : End (expC k) := sorry

/-- The formula `Θ(τ)(I)(e_I) = τ^{|I|} e_I` defining `Θ`, used in Proposition 3.14. -/
theorem theta_apply (τ : k) (I : FintypeCat.{0}) (x : (expSp : Species k).ev I) :
    ((Theta k τ).asHom.hom.app ⟨I⟩).hom x = τ ^ Nat.card I.obj • x := sorry

/-- **Proposition 3.14** (monoids). `Θ : k → End_coalg(e)` is a bijective monoid map. -/
theorem prop_3_14_monoid : Function.Bijective (Theta k) ∧
    (∀ a b, Theta k (a * b) = Theta k a * Theta k b) ∧ Theta k 1 = 1 := sorry

/-- **Proposition 3.14** (groups). `Θ` restricts to `k^× ≅ Aut_coalg(e)`. -/
theorem prop_3_14_group : Nonempty (kˣ ≃* Aut (expC k)) := by
  obtain ⟨hb, hm, ho⟩ := prop_3_14_monoid k
  let f : k →* End (expC k) :=
    { toFun := Theta k
      map_one' := ho
      map_mul' := hm }
  exact ⟨(Units.mapEquiv (MulEquiv.ofBijective f hb)).trans (Aut.unitsEndEquivAut (expC k))⟩

/-- **Corollary 3.15.** `k^× → Pic(e)`, `λ ↦ [Θ(λ) e]`, is an isomorphism of groups. -/
theorem cor_3_15 : Nonempty (kˣ ≃* PicCoalg (expC k)) := by
  obtain ⟨e⟩ := prop_3_14_group k
  obtain ⟨f⟩ := theorem_3_13 (c := expC k) (isConnected_exp (k := k))
  exact ⟨e.trans f⟩

/-! ## The Malvenuto–Reutenauer algebra -/

/-- The graded vector space `SSym` with basis `⨆_n S_n`. -/
def SSym : Type := (Σ n : ℕ, Equiv.Perm (Fin n)) →₀ k

instance : AddCommGroup (SSym k) := inferInstanceAs (AddCommGroup ((Σ n : ℕ, Equiv.Perm (Fin n)) →₀ k))

instance : Module k (SSym k) := inferInstanceAs (Module k ((Σ n : ℕ, Equiv.Perm (Fin n)) →₀ k))

/-- The **product** of `SSym` (3.3): `σ · τ = ∑_{ω ∈ S^{(p,q)}} (σ × τ) ω⁻¹`, the sum over
shuffles interleaving `σ` and the shifted `τ'`; e.g. `21 · 312 = 21534 + 25134 + ⋯`. -/
instance : Ring (SSym k) := sorry

instance : Algebra k (SSym k) := sorry

/-- A permutation `σ ∈ S_n` is **connected** if the only initial interval `[m]` it preserves is
`[n]` (equivalently it does not lie in a proper Young subgroup). -/
def Perm.IsConnectedPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ m : ℕ, 0 < m → m < n → ∃ i : Fin n, i.val < m ∧ m ≤ (σ i).val

/-- The set `Con` of connected permutations (all sizes). -/
def Con : Set (Σ n : ℕ, Equiv.Perm (Fin n)) := {σ | Perm.IsConnectedPerm σ.2}

/-- **Proposition 3.16.** Coalgebra endomorphisms of `L` correspond bijectively to algebra
morphisms `SSym → k`: `f ↦ χ_f` with `χ_f(σ) = α_σ` where `f(12⋯n) = ∑_σ α_σ σ`. -/
theorem prop_3_16 : Nonempty (End (linC k) ≃ (SSym k →ₐ[k] k)) := sorry

/-- **Theorem 3.17** ([PR95, Thm 2.1]). The algebra `SSym` is freely generated by the set `Con`
of connected permutations.

**Gap (error).** The definition `Con` also includes the unique permutation of size zero.
For the intended shuffle algebra its basis element is the multiplicative unit, so it cannot
be a free algebra generator. The theorem requires connected permutations of positive size. -/
theorem theorem_3_17 :
    ∃ e : FreeAlgebra k Con ≃ₐ[k] SSym k,
      ∀ σ : Con, e (FreeAlgebra.ι k σ) = Finsupp.single σ.1 (1 : k) := sorry

/-- **Corollary 3.18.** `End_coalg(L) → Hom_set(Con, k)`, `f ↦ χ_f|_Con`, is a bijection:
coalgebra endomorphisms of `L` are in bijection with arbitrary families of scalars indexed by the
connected permutations. -/
theorem cor_3_18 : Nonempty (End (linC k) ≃ (Con → k)) := by
  obtain ⟨e⟩ := prop_3_16 k
  obtain ⟨f, _⟩ := theorem_3_17 k
  let g : (SSym k →ₐ[k] k) ≃ (FreeAlgebra k Con →ₐ[k] k) :=
    { toFun := fun h => h.comp f.toAlgHom
      invFun := fun h => h.comp f.symm.toAlgHom
      left_inv := by intro h; ext x; simp
      right_inv := by intro h; ext x; simp }
  exact ⟨e.trans (g.trans (FreeAlgebra.lift k).symm)⟩

/-- The coalgebra maps `Θ : L → e` and `Ψ : e → L`, `Ψ(e_I) = ∑_σ σ / |I|!`. They satisfy
`ΘΨ = id_e`, so `L_e = Ψ(e) ⊆ L` is a subcoalgebra isomorphic to `e`. -/
def ThetaL : linC k ⟶ expC k := sorry

def PsiL (hk : CharZero k) : expC k ⟶ linC k := sorry

theorem thetaL_psiL (hk : CharZero k) : PsiL k hk ≫ ThetaL k = 𝟙 _ := sorry

/-- The endomorphisms `φ_λ = Ψ ∘ Θ(λ) ∘ Θ`: `φ_λ(12⋯n) = (λⁿ / n!) ∑_σ σ`. They are exactly the
endomorphisms taking a value `α_σ = λⁿ/n!` depending only on `|σ| = n`; none is an
automorphism (e.g. for `n = 2` the image lies in `⟨12 + 21⟩`). -/
theorem phi_not_aut (hk : CharZero k) (a : k) :
    ¬ IsIso (ThetaL k ≫ (Theta k a).asHom ≫ PsiL k hk) := sorry

/-- The automorphisms `ψ_λ(12⋯n) = λⁿ 12⋯n` and `ψ'_λ(12⋯n) = λⁿ n(n-1)⋯1` (`λ ∈ k^×`). -/
def psiAut (a : kˣ) : Aut (linC k) := sorry

def psiAut' (a : kˣ) : Aut (linC k) := sorry

/- The only coalgebra endomorphisms of `L` taking on each length `n` a single nonzero
coefficient `α_{σ_n}` are the two families `(id_{[n]})_n` and `(n(n-1)⋯1)_n` (thesis, p. 102);
by Corollary 3.18 this is a statement about families of scalars on `Con`, not restated. -/

/-- For `k = ℝ` (or `ℂ`), `Aut_coalg(L)` is uncountable: the set of families
`(α_σ)_{σ ∈ Con}` with every `det(φ^n_α) ≠ 0` is a countable intersection of open dense subsets
of `k^{Con}` (Baire). Hence `Pic(L)` is uncountable. -/
theorem uncountable_aut_L : Uncountable (Aut (linC ℝ)) := sorry

end Sp

end MartinPhd

end
end Examples
