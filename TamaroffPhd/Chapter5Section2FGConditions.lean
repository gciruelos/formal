import TamaroffPhd.Chapter5Section1GorensteinChains

/-!
# Chapter 5, §5.2: the FG conditions and higher structures

The A∞-centre of the Yoneda algebra `E = Ext*_Λ(k, k)` with its A∞-structure (3.5), higher
commutators (5.20), the combinatorial criterion for A∞-centrality (Proposition 2.5), and the
conditions FG′.

## Contents

* `mul2`, `Ehom`, `unitE`: the product `m₂`, the homogeneous parts and the unit of `E`.
* `higherComm`: the higher commutators `[a; x₁, …, xₙ]_{1,n}` of (5.20).
* `hoderDiff`: the differential of the complex `hoder(E)` of homotopy derivations (5.21).
* Definition 13: the A∞-centre `Z∞ E`; the graded centre `Z_gr E`.
* Lemma 2.4, Proposition 2.5 (combinatorial criterion).
* The conditions FG′ (§5.2.2).
-/

noncomputable section

namespace TamaroffPhd

open Classical MonomialData Quiv

variable (k : Type) [Field k] (Q : Quiv) (R : Set (List Q.A))

/-- The basis vector of `E` at a basis element. -/
abbrev eb (b : EBasis Q R) : E k Q R := Finsupp.single b 1

/-- The product `m₂` of the Yoneda algebra, extended bilinearly. -/
def mul2 (x y : E k Q R) : E k Q R := multilin k (yoneda k Q R) [x, y]

/-- The `n`-th power under `m₂` (with `x⁰ = 1`). -/
def mulPow (x : E k Q R) : ℕ → E k Q R
  | 0 => ∑ v : Q.V, eb k Q R (.inl v)
  | n + 1 => mul2 k Q R x (mulPow x n)

/-- The unit `1 = ∑_v e_v` of `E`. -/
def unitE : E k Q R := ∑ v : Q.V, eb k Q R (.inl v)

/-- The homogeneous part `Extⁿ_Λ(k, k)` of `E`. -/
def Ehom (n : ℕ) : Submodule k (E k Q R) := Finsupp.supported k k {b | EBasis.deg b = n}

/-- **(5.20).** The higher commutator
`[a; x₁, …, xₙ]_{1,n} = ∑ᵢ (-1)^i (-1)^{|a|(|x₁| + ⋯ + |xᵢ|)} m_{n+1}(x₁, …, xᵢ, a, x_{i+1}, …, xₙ)`
for `a` of degree `da` and basis elements `xᵢ`. -/
def higherComm (da : ℕ) (a : E k Q R) (xs : List (EBasis Q R)) : E k Q R :=
  ((List.range (xs.length + 1)).map fun i =>
    ((-1 : k) ^ (i + da * tupleDeg EBasis.deg (xs.take i))) •
      multilin k (yoneda k Q R)
        ((xs.take i).map (eb k Q R) ++ [a] ++ (xs.drop i).map (eb k Q R))).sum

/-- The homotopy inner derivation `ad_a = {ad_{a,n}}_{n ≥ 1}` as a cochain on basis tuples. -/
def adCochain (da : ℕ) (a : E k Q R) (xs : List (EBasis Q R)) : E k Q R :=
  if xs = [] then 0 else higherComm k Q R da a xs

/-- **(5.21).** The differential of the complex `hoder(E) = Hom(⨁_{n≥1} E^{⊗n}, E)` of homotopy
derivations, on a cochain `φ` of parity `dφ`: `∂φ = [m, φ]`, that is
`∑ ± m(id^r ⊗ φ ⊗ id^t) - (-1)^{dφ} ∑ ± φ(id^r ⊗ m ⊗ id^t)`.

**Note.** The signs of `hoderDiff` follow the convention (3.4) of the Stasheff identities, with
Koszul signs for evaluating `id^r ⊗ φ ⊗ id^t`. The thesis refers to [32] for this complex. -/
def hoderDiff (dφ : ℕ) (φ : List (EBasis Q R) → E k Q R) (bs : List (EBasis Q R)) : E k Q R :=
  let pairs := (List.range (bs.length + 1)).flatMap fun r =>
    (List.range (bs.length + 1 - r)).map fun s => (r, s)
  let mid (r s : ℕ) := (bs.drop r).take s
  let outer (r s : ℕ) (v : E k Q R) :=
    (bs.take r).map (eb k Q R) ++ [v] ++ (bs.drop (r + s)).map (eb k Q R)
  (pairs.map fun rs =>
    let r := rs.1
    let s := rs.2
    let t := bs.length - r - s
    (if 1 ≤ s then
      ((-1 : k) ^ (r * s + t + dφ * tupleDeg EBasis.deg (bs.take r))) •
        multilin k (yoneda k Q R) (outer r s (φ (mid r s)))
     else 0) -
    (if 2 ≤ s then
      ((-1 : k) ^ (dφ + r * s + t + s * tupleDeg EBasis.deg (bs.take r))) •
        multilin k φ (outer r s (yoneda k Q R (mid r s)))
     else 0)).sum

/-- **Definition 13 (A∞-centre).** A homogeneous `a ∈ Extⁿ` is A∞-central if `[ad_a] = 0` in
`H*(hoder(E))`: `ad_a = ∂ψ` for some cochain `ψ`. -/
def IsAInfCentral (n : ℕ) (a : E k Q R) : Prop :=
  a ∈ Ehom k Q R n ∧ ∃ ψ : List (EBasis Q R) → E k Q R,
    ∀ bs, bs ≠ [] → hoderDiff k Q R (n + 1) ψ bs = adCochain k Q R n a bs

/-- **Definition 13.** The A∞-centre `Z∞ E`, spanned by the homogeneous A∞-central elements. -/
def ZInf : Submodule k (E k Q R) :=
  Submodule.span k {a | ∃ n, IsAInfCentral k Q R n a}

/-- **(5.19).** The graded centre `Z_gr E`: `m₂(a, x) = (-1)^{|a||x|} m₂(x, a)` for all
homogeneous `x`. -/
def IsGradedCentral (n : ℕ) (a : E k Q R) : Prop :=
  a ∈ Ehom k Q R n ∧ ∀ x : EBasis Q R,
    mul2 k Q R a (eb k Q R x) = ((-1 : k) ^ (n * EBasis.deg x)) • mul2 k Q R (eb k Q R x) a

/-- **§5.2.2.** A∞-central classes are graded-central. -/
theorem isGradedCentral_of_isAInfCentral (hR : (Q.data R).IsMinimal) {n : ℕ} {a : E k Q R}
    (h : IsAInfCentral k Q R n a) : IsGradedCentral k Q R n a := by
  sorry

/-- **Lemma 2.4.** If `a` has even degree, then for chains `x₁, …, xₙ` the higher commutator is
`m_{n+1}(a, x₁, …, xₙ) + (-1)ⁿ m_{n+1}(x₁, …, xₙ, a)`. -/
theorem lemma_2_4 (hR : (Q.data R).IsMinimal) {n : ℕ} (hn : Even n) {a : E k Q R}
    (ha : a ∈ Ehom k Q R n) (xs : List (Q.data R).Chain) :
    higherComm k Q R n a (xs.map .inr) =
      multilin k (yoneda k Q R) (a :: (xs.map .inr).map (eb k Q R)) +
        ((-1 : k) ^ xs.length) • multilin k (yoneda k Q R) ((xs.map .inr).map (eb k Q R) ++ [a]) := by
  sorry

/-- The projection of a product of elements of `kC∨` onto `kC∨_N` (§5.2.3): the sum of the
terms of the concatenation (in `kQ^op`) that are chains of the right degree, without signs. -/
def catProj (xs : List (E k Q R)) : E k Q R :=
  multilin k (fun bs => match bs.mapM (fun b => match b with | .inr γ => some γ | .inl _ => none) with
    | some ds => match opConcat Q R ds with
      | some γ => eb k Q R (.inr γ)
      | none => 0
    | none => 0) xs

/-- **§5.2.3.** `a` is *symmetric* if `a e = e a` for all idempotents `e`: a combination of
closed oriented cycles. -/
def IsSymmetric (a : E k Q R) : Prop :=
  ∀ v : Q.V, mul2 k Q R a (eb k Q R (.inl v)) = mul2 k Q R (eb k Q R (.inl v)) a

/-- **Proposition 2.5 (Combinatorial criterion).** Let `a` be symmetric of even degree
`r₀ + 1 ≥ 2`. If `a c₁ ⋯ cₙ = c₁ ⋯ cₙ a` in `kC∨_{r₀ + r₁ + ⋯ + rₙ + 1}` for all chains
`c₁, …, cₙ`, then `a` is A∞-central (and so in the image of Hochschild cohomology). -/
theorem prop_2_5 (hR : (Q.data R).IsMinimal) {r₀ : ℕ} (hev : Even (r₀ + 1)) {a : E k Q R}
    (ha : a ∈ Ehom k Q R (r₀ + 1)) (hsym : IsSymmetric k Q R a)
    (hcomm : ∀ cs : List (Q.data R).Chain,
      catProj k Q R (a :: cs.map fun c => eb k Q R (.inr c)) =
        catProj k Q R (cs.map (fun c => eb k Q R (.inr c)) ++ [a])) :
    IsAInfCentral k Q R (r₀ + 1) a := by
  sorry

/-- The subalgebra (for `m₂`) generated by a set: the smallest subspace containing `1` and the
set and closed under `m₂`. -/
def genAlg (S : Set (E k Q R)) : Submodule k (E k Q R) :=
  sInf {N | unitE k Q R ∈ N ∧ S ⊆ N ∧ ∀ x ∈ N, ∀ y ∈ N, mul2 k Q R x y ∈ N}

/-- **§5.2.2 (FG′).** FG′1: `Z∞` is a finitely generated (equivalently Noetherian) algebra;
FG′2: `Ext*_Λ(k, k)` is a finitely generated `Z∞`-module.

**Change.** The finite generation conditions FG of Snashall–Solberg are stated in terms of
Hochschild cohomology `HH*(Λ, Λ)`, its cup product, and the characteristic morphisms
`φ_M : HH*(Λ, Λ) → Ext*_Λ(M, M)`. Proposition 2.3 shows that FG is equivalent to FG′, which only
involves the A∞-structure of `Ext*_Λ(k, k)`; its proof uses Theorem 2.1 of Briggs–Gélinas
[32], `im φ_k = Z∞ Ext*_Λ(k, k)`. Graded rings of Ext groups and the characteristic morphism are
not formalized, so we state the chapter's results with FG′, computed on the combinatorial model
(3.5) of `Ext*_Λ(k, k)` (Theorem 3.3.3). Theorem 2.1 of [32], Corollary 2.2 and Proposition 2.3
are not stated.

**Change.** FG′1 asks `Z∞` to be Noetherian. `Z∞` is positively graded with
`Z∞⁰` finite dimensional, so this is equivalent to `Z∞` being a finitely generated algebra,
which is the form used in the proof of Proposition 2.3 and the one stated here. -/
def FG' : Prop :=
  (∃ S : Finset (E k Q R), (∀ s ∈ S, s ∈ ZInf k Q R) ∧ genAlg k Q R S = ZInf k Q R) ∧
  ∃ T : Finset (E k Q R),
    Submodule.span k {y | ∃ z ∈ ZInf k Q R, ∃ t ∈ T, y = mul2 k Q R z t} = ⊤

end TamaroffPhd

end
