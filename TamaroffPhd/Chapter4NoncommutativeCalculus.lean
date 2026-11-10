import TamaroffPhd.Chapter2Section2DGAlgebras

/-!
# Chapter 4: Non-commutative calculus

The Tamarkin–Tsygan calculus of an associative algebra `A` computed from a model `B = (T(V), d)`
through nc polyvector fields `X*(B) = cone(Ad : B → Der(B))` and nc differential forms
`Θ*(B) = cone(Co : B ⊗ V → B)`.

## Contents

* §4.2.1: Hochschild cochains of `A`, the cup product, Gerstenhaber's pre-Lie product and
  bracket, the Hochschild differential; Proposition 2.1 (the Gerstenhaber algebra part).
* §4.2.2: derivations of a quasi-free algebra, the adjoint map `Ad` and the commutator map
  `Co`, the complexes of nc fields and nc forms; Lemma 2.2 (`Ω¹_B ≅ B ⊗ V ⊗ B`) and the
  projection of Lemma 2.4.

**Not stated.** The operadic part of the chapter needs colored operads, Koszul duality and
algebras up to homotopy, which Mathlib does not have: Propositions 1.1–1.2, Theorems 1.3–1.4
(`PreCalc` is Koszul, `Calc` is inhomogeneous Koszul), Theorem 2.5 (Kontsevich–Soibelman), the
main Theorems 2.6–2.7 (`(X*(B), Θ*(B))` carries a `Calc∞`-structure ∞-quasi-isomorphic to that of
Hochschild (co)chains), Theorem 3.1 (dual braces), Theorem 3.2 (duality with `E_A`) and the
computations of §4.3.3. The module part of Proposition 2.1 (cap product, Lie derivative, Connes'
operator on Hochschild chains) and Corollary 2.3 are left for a later pass.

-/

noncomputable section

namespace TamaroffPhd

open Classical TensorProduct

/-! ## Hochschild cochains (§4.2.1) -/

section Hochschild

variable (k : Type) [Field k] (A : Type) [Ring A] [Algebra k A]

/-- A Hochschild cochain, read on lists of length its arity.

**Change.** A `p`-cochain is a function on lists of elements of `A`, read
on lists of length `p`; multilinearity is a separate predicate. This avoids index arithmetic on
`Fin (p + q - 1)` in the partial compositions. -/
abbrev Cochain := List A → A

variable {k A}

/-- `f` is a `p`-cochain: on lists of length `p` it is `k`-linear in each argument. -/
def IsCochain (p : ℕ) (f : Cochain A) : Prop :=
  ∀ (as : List A) (i : ℕ), as.length = p → i < p → ∀ (x y : A) (c : k),
    f (as.set i (x + c • y)) = f (as.set i x) + c • f (as.set i y)

/-- **§4.2.1 (Cup product).** `(f ⌣ g)(a₁, …, a_{p+q}) = f(a₁, …, a_p) g(a_{p+1}, …, a_{p+q})`. -/
def cup (p : ℕ) (f g : Cochain A) : Cochain A := fun as => f (as.take p) * g (as.drop p)

/-- The partial composition `f ∘ᵢ g` for `g` of arity `q`: insert `g` at position `i`. -/
def circI (q i : ℕ) (f g : Cochain A) : Cochain A :=
  fun as => f (as.take i ++ [g ((as.drop i).take q)] ++ as.drop (i + q))

/-- **§4.2.1 (Gerstenhaber's pre-Lie product).** `f ∘ g = ∑ᵢ (-1)^{(q-1)i} f ∘ᵢ g` for `f` of
arity `p` and `g` of arity `q`. -/
def circ (p q : ℕ) (f g : Cochain A) : Cochain A :=
  fun as => ((List.range p).map fun i => ((-1 : ℤ) ^ ((q - 1) * i)) • circI q i f g as).sum

/-- **§4.2.1 (Gerstenhaber bracket).** `[f, g] = f ∘ g - (-1)^{(p-1)(q-1)} g ∘ f`. -/
def gbracket (p q : ℕ) (f g : Cochain A) : Cochain A :=
  fun as => circ p q f g as - ((-1 : ℤ) ^ ((p - 1) * (q - 1))) • circ q p g f as

/-- The Hochschild differential of a `p`-cochain:
`δf(a₀, …, a_p) = a₀ f(a₁, …, a_p) + ∑ᵢ (-1)^{i+1} f(…, aᵢ a_{i+1}, …) + (-1)^{p+1} f(a₀, …, a_{p-1}) a_p`. -/
def hochDiff (p : ℕ) (f : Cochain A) : Cochain A := fun as =>
  as.headD 0 * f (as.drop 1) +
    ((List.range p).map fun i =>
      ((-1 : ℤ) ^ (i + 1)) • f (as.take i ++ [as.getD i 0 * as.getD (i + 1) 0] ++ as.drop (i + 2))).sum +
    ((-1 : ℤ) ^ (p + 1)) • (f (as.take p) * as.getD p 0)

/-- A Hochschild `p`-cocycle. -/
def IsHochCocycle (p : ℕ) (f : Cochain A) : Prop :=
  IsCochain (k := k) p f ∧ ∀ as : List A, as.length = p + 1 → hochDiff p f as = 0

/-- A Hochschild `p`-coboundary (as a function on lists of length `p`). -/
def IsHochCoboundary (p : ℕ) (f : Cochain A) : Prop :=
  ∃ h, IsCochain (k := k) (p - 1) h ∧ 1 ≤ p ∧ ∀ as : List A, as.length = p → hochDiff (p - 1) h as = f as

/-- **Proposition 2.1 (Gerstenhaber algebra).** On Hochschild cohomology the cup product is
graded commutative and the Gerstenhaber bracket of cocycles is a cocycle: `HH*(A)` with `⌣` and
`[-, -]` is a Gerstenhaber algebra. -/
theorem prop_2_1_gerstenhaber {p q : ℕ} {f g : Cochain A}
    (hf : IsHochCocycle (k := k) p f) (hg : IsHochCocycle (k := k) q g) :
    IsHochCocycle (k := k) (p + q) (cup p f g) ∧
    IsHochCoboundary (k := k) (p + q) (fun as => cup p f g as - ((-1 : ℤ) ^ (p * q)) • cup q g f as) ∧
    IsHochCocycle (k := k) (p + q - 1) (gbracket p q f g) := by
  sorry

/-- **Proposition 2.1 (Leibniz rule).** The bracket is a graded derivation of the cup product up
to coboundaries: `[f ⌣ g, h] - f ⌣ [g, h] - (-1)^{(r-1)q} [f, h] ⌣ g` is a coboundary for
cocycles `f, g, h` of degrees `p, q, r`. -/
theorem prop_2_1_leibniz {p q r : ℕ} {f g h : Cochain A}
    (hf : IsHochCocycle (k := k) p f) (hg : IsHochCocycle (k := k) q g)
    (hh : IsHochCocycle (k := k) r h) :
    IsHochCoboundary (k := k) (p + q + r - 1) (fun as =>
      gbracket (p + q) r (cup p f g) h as - cup p f (gbracket q r g h) as -
        ((-1 : ℤ) ^ ((r - 1) * q)) • cup (p + r - 1) (gbracket p r f h) g as) := by
  sorry

end Hochschild

/-! ## nc fields and nc forms (§4.2.2) -/

section FieldsForms

variable {k : Type} [Field k]

namespace QuasiFree

variable (B : QuasiFree k)

/-- The graded derivations of `B` of degree `δ` (the space `Der(B)` of §4.2.2, degreewise). -/
def Der (δ : ℤ) : Set (FreeAlg k B.G →ₗ[k] FreeAlg k B.G) :=
  {D | B.IsGradedDerivation δ D}

/-- **§4.2.2.** The adjoint map `Ad : B → Der(B)`, `Ad_b = [b, -]` for `b` of degree `n`:
`Ad_b(x) = b x - (-1)^{n |x|} x b` on monomials `x`. -/
def ad (n : ℕ) (b : FreeAlg k B.G) : FreeAlg k B.G →ₗ[k] FreeAlg k B.G :=
  linOnMonomials fun w => b * mono w - ((-1 : k) ^ (n * B.wdeg w)) • (mono w * b)

/-- **§4.2.2.** `Ad_b` is a graded derivation of degree `|b|`. -/
theorem ad_mem_der (n : ℕ) (b : FreeAlg k B.G) (hb : b ∈ B.hom n) :
    B.ad n b ∈ B.Der n := by
  sorry

/-- **§4.2.2.** The commutator map `Co : B ⊗ V → B`, `b ⊗ v ↦ [v, b]`, on a monomial `b` and a
generator `v`. -/
def co (w : FreeMonoid B.G) (v : B.G) : FreeAlg k B.G :=
  mono (FreeMonoid.of v) * mono w - ((-1 : k) ^ (B.deg v * B.wdeg w)) • (mono w * mono (FreeMonoid.of v))

/-- **Corollary 2.3.** The complex of nc polyvector fields `X*(B) = cone(Ad : B → Der(B))`, in
degree `n`: pairs `(λ, f)` with `λ ∈ B` and `f` a derivation, in the shifted degrees of the cone
(`X = λ + f`). -/
def ncFields (n : ℤ) : Set ((FreeAlg k B.G) × (FreeAlg k B.G →ₗ[k] FreeAlg k B.G)) :=
  {x | (0 ≤ n + 1 → x.1 ∈ B.hom (n + 1).toNat) ∧ (n + 1 < 0 → x.1 = 0) ∧ x.2 ∈ B.Der n}

/-- The differential of `X*(B)`: `(λ, f) ↦ (dλ, [d, f] ± Ad_λ)` for `f` of degree `n`. -/
def ncFieldsDiff (n : ℤ) (x : (FreeAlg k B.G) × (FreeAlg k B.G →ₗ[k] FreeAlg k B.G)) :
    (FreeAlg k B.G) × (FreeAlg k B.G →ₗ[k] FreeAlg k B.G) :=
  (B.d x.1, B.bracket (-1) n B.d x.2 + ((-1 : k) ^ (n.natAbs + 1)) • B.ad (n + 1).toNat x.1)

/-! ## Kähler differentials and the small resolution -/

/-- The multiplication `B ⊗ B → B`. -/
def multMap : FreeAlg k B.G ⊗[k] FreeAlg k B.G →ₗ[k] FreeAlg k B.G := LinearMap.mul' k _

/-- **§4.2.2.** The bimodule `Ω¹_B` of non-commutative Kähler differentials, realized as the
kernel of the multiplication `B ⊗ B → B` (with `b db' b'' = b b' ⊗ b'' - b ⊗ b' b''`). -/
def kahler : Submodule k (FreeAlg k B.G ⊗[k] FreeAlg k B.G) := LinearMap.ker (multMap B)

/-- The inclusion `V → B` of the generators. -/
def genIncl : (B.G →₀ k) →ₗ[k] FreeAlg k B.G :=
  Finsupp.linearCombination k fun g => mono (FreeMonoid.of g)

/-- The map `g : B ⊗ V ⊗ B → Ω¹_B`, `b ⊗ v ⊗ b' ↦ b dv b' = bv ⊗ b' - b ⊗ vb'`. -/
def kahlerMap : FreeAlg k B.G ⊗[k] (B.G →₀ k) ⊗[k] FreeAlg k B.G →ₗ[k]
    FreeAlg k B.G ⊗[k] FreeAlg k B.G :=
  TensorProduct.map (LinearMap.mul' k _ ∘ₗ TensorProduct.map LinearMap.id (genIncl B))
      LinearMap.id -
    TensorProduct.map LinearMap.id (LinearMap.mul' k _ ∘ₗ TensorProduct.map (genIncl B) LinearMap.id) ∘ₗ
      (TensorProduct.assoc k (FreeAlg k B.G) (B.G →₀ k) (FreeAlg k B.G)).toLinearMap

/-- **Lemma 2.2.** For a quasi-free `B = T(V)`, the map `g : B ⊗ V ⊗ B → Ω¹_B` is an isomorphism
of `B`-bimodules: it is injective with image `Ω¹_B`. -/
theorem lemma_2_2 :
    Function.Injective (kahlerMap B) ∧ LinearMap.range (kahlerMap B) = kahler B := by
  sorry

/-- The non-trivial component of the projection `π : Bar(B) → S*(B)` of Lemma 2.4:
`π(1 ⊗ v₁ ⋯ vₙ ⊗ 1) = ∑ᵢ v₁ ⋯ v_{i-1} ⊗ vᵢ ⊗ v_{i+1} ⋯ vₙ`. -/
def barProj : List B.G → FreeAlg k B.G ⊗[k] (B.G →₀ k) ⊗[k] FreeAlg k B.G
  | [] => 0
  | v :: w => ((1 : FreeAlg k B.G) ⊗ₜ Finsupp.single v (1 : k)) ⊗ₜ mono (FreeMonoid.ofList w) +
      TensorProduct.map (TensorProduct.map (LinearMap.mulLeft k (mono (FreeMonoid.of v) : FreeAlg k B.G))
        (LinearMap.id : (B.G →₀ k) →ₗ[k] _)) LinearMap.id (barProj w)

/-- **Lemma 2.4.** Under the identification of Lemma 2.2, `π` is the quotient map
`B ⊗ B ⊗ B → Ω¹_B`: `g(π(1 ⊗ b ⊗ 1)) = b ⊗ 1 - 1 ⊗ b` for every monomial `b`. Hence `π` is a
map of complexes, and `S*(B)` is a homotopy retract of the bar resolution. -/
theorem lemma_2_4 (w : List B.G) :
    kahlerMap B (barProj B w) = mono (FreeMonoid.ofList w) ⊗ₜ 1 - 1 ⊗ₜ mono (FreeMonoid.ofList w) := by
  sorry

end QuasiFree

end FieldsForms

end TamaroffPhd

end
