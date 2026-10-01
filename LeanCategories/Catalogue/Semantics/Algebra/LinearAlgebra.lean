/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dimension.Finrank
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials

@[expose] public section

/-!
# Vectors, matrices and spans (SPEC.md, "Vectors and matrices", "Subspaces and spans")

* `Xⁿ` is the set of `n`-tuples of `X` (`Fin n → X`), built from `() : 1 → X⁰` and
  `cons : X × Xⁿ → Xⁿ⁺¹` (Mathlib `Matrix.vecCons`), the isomorphism `X × Xⁿ ≅ Xⁿ⁺¹`. A set `Xⁿ`
  has no zero; over a ring `K`, `Kⁿ` is a `K`-module, whose additive unit is `0 : 1 → Kⁿ`.
* `Matₙ(K)` is the set of `n × n` matrices over a commutative ring `K`, made from its rows by
  `rows : (Kⁿ)ⁿ → Matₙ(K)` (Mathlib `Matrix.of`); a matrix is applied to vectors,
  `Matₙ(K) × Kⁿ → Kⁿ` (Mathlib `Matrix.mulVec`).
* `Monicₙ(K) ↪ K[x]`, the monic polynomials of degree `n`, and `companion_matrix : Monicₙ(K) →
  Matₙ(K)`. A polynomial is in `Monicₙ(K)` only with the evidence that it is monic of degree `n`.
* Inverses are those of the units `GLₙ(K) = Matₙ(K)ˣ` (`Algebra.Units`): `Matₙ(K) = End(Kⁿ)` is a
  monoid, and a matrix has no inverse unless it is established to be a unit.
* `det`, `trace : Matₙ(K) → K`, `rank : Matₙ(K) → ℕ`, `charpoly : Matₙ(K) → K[x]`, and
  `ker : Matₙ(K) → 𝒫(Kⁿ)`, `{v | M v = 0}`.
* Over a field `K`: `span : 𝒫(Kⁿ) → 𝒫(Kⁿ)` (the subspace a set spans, Mathlib `Submodule.span`)
  and `dim : 𝒫(Kⁿ) → ℕ`, the dimension of its span (Mathlib `Module.finrank`).
-/

open CategoryTheory

namespace CasCatalogue.Algebra.LinearAlgebra

open CasCatalogue.Foundation.PowerSets CasCatalogue.Algebra.Polynomials

/-- `Xⁿ`. -/
abbrev vectors (X : Type) (n : ℕ) : SetsCat.{0} := Fin n → X

/-- The empty tuple `() ∈ X⁰`. -/
def empty (X : Type) : CasCatalogue.Foundation.Objects.fin 1 ⟶ vectors X 0 :=
  TypeCat.ofHom fun _ => ![]

/-- `(x, v) ↦ (x, v₀, …)`, `X × Xⁿ → Xⁿ⁺¹`. -/
def cons (X : Type) (n : ℕ) : (X × vectors X n : SetsCat.{0}) ⟶ vectors X (n + 1) :=
  TypeCat.ofHom fun p => Matrix.vecCons p.1 p.2

/-- `0 ∈ Kⁿ`, the additive unit of the `K`-module `Kⁿ`. -/
def zero (K : Type) [Semiring K] (n : ℕ) : CasCatalogue.Foundation.Objects.fin 1 ⟶ vectors K n :=
  TypeCat.ofHom fun _ => 0

/-- `Matₙ(K)`. -/
abbrev matrices (n : ℕ) (K : Type) [CommRing K] : SetsCat.{0} := Matrix (Fin n) (Fin n) K

/-- The matrix with the given rows. -/
def rows (n : ℕ) (K : Type) [CommRing K] : vectors (vectors K n) n ⟶ matrices n K :=
  TypeCat.ofHom fun r => Matrix.of r

/-- `(M, v) ↦ M v`. -/
def apply (n : ℕ) (K : Type) [CommRing K] :
    (matrices n K × vectors K n : SetsCat.{0}) ⟶ vectors K n :=
  TypeCat.ofHom fun p => p.1.mulVec p.2

/-- The determinant. -/
def det (n : ℕ) (K : Type) [CommRing K] : matrices n K ⟶ (K : SetsCat.{0}) :=
  TypeCat.ofHom fun M => M.det

/-- The trace. -/
def trace (n : ℕ) (K : Type) [CommRing K] : matrices n K ⟶ (K : SetsCat.{0}) :=
  TypeCat.ofHom fun M => M.trace

/-- The rank. -/
noncomputable def rank (n : ℕ) (K : Type) [CommRing K] :
    matrices n K ⟶ CasCatalogue.Foundation.Objects.naturals :=
  TypeCat.ofHom fun M => M.rank

/-- The characteristic polynomial `det(x - M)`. -/
noncomputable def charpoly (n : ℕ) (K : Type) [CommRing K] : matrices n K ⟶ polynomials K :=
  TypeCat.ofHom fun M => M.charpoly

/-- `Monicₙ(K)`, the monic polynomials of degree `n`. -/
abbrev monics (n : ℕ) (K : Type) [CommRing K] : SetsCat.{0} :=
  {p : Polynomial K // p.Monic ∧ p.natDegree = n}

/-- `Monicₙ(K) ↪ K[x]`. -/
def monicsInclusion (n : ℕ) (K : Type) [CommRing K] : monics n K ⟶ polynomials K :=
  TypeCat.ofHom Subtype.val

/-- The monic polynomial `p` of degree `n`, with that evidence. -/
def admitMonic (n : ℕ) (K : Type) [CommRing K] (p : Polynomial K)
    (h : p.Monic ∧ p.natDegree = n) : CasCatalogue.Foundation.Objects.fin 1 ⟶ monics n K :=
  TypeCat.ofHom fun _ => ⟨p, h⟩

open Lean Elab Tactic in
/-- `p` is monic of degree `n`: the leading coefficient of the closed expression is computed with
its degree bound (`Polynomial.monic_of_natDegree_le_of_coeff_eq_one`, Mathlib `monicity`), and its
degree from its terms (Mathlib `compute_degree`); the closed coefficient facts left over are
arithmetic. -/
meta def monicByDegree : TacticM Unit := do
  evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
  let [monic, degree] ← getGoals | throwError "not a conjunction `Monic p ∧ natDegree p = n`"
  setGoals [monic]
  evalTactic (← `(tactic| monicity!))
  CasCatalogue.Algebra.Polynomials.closeCoefficientGoals
  setGoals [degree]
  evalTactic (← `(tactic| compute_degree!))
  CasCatalogue.Algebra.Polynomials.closeCoefficientGoals

/-- The image of a monic polynomial `p` of degree `n` along a ring map `f : R → S` into a ring in
which `0 ≠ 1` is monic of degree `n`: `f` sends the leading coefficient `1` to `1 ≠ 0` and the
coefficients above degree `n`, all `0`, to `0` (Mathlib `Polynomial.Monic.map`,
`Polynomial.Monic.natDegree_map`). No injectivity of `f` is needed. -/
theorem monicOfDegree_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    {p : Polynomial R} {n : ℕ} (hp : p.Monic ∧ p.natDegree = n) (h : (0 : S) ≠ 1) :
    (p.map f).Monic ∧ (p.map f).natDegree = n :=
  haveI := nontrivial_of_ne _ _ h
  ⟨hp.1.map f, (hp.1.natDegree_map f).trans hp.2⟩

open Lean Elab Tactic in
/-- The evidence that a closed polynomial `p ∈ K[x]` is monic of degree `n`, by the structure of
`p`:

* `p` an expression in `x`, constants `C r`, numerals, `+`, `-`, `·`, `^` over a closed
  commutative ring `K`: its coefficient of degree `n` is `1` and none above it is nonzero. They
  are read off the expression, and, when its naive leading terms cancel, off its normal form
  (`Polynomials.normalizePolynomial`);
* `p = q.map f` the image of `q ∈ R[x]` along a ring map `f : R → K`: it is monic of degree `n`
  when `q` is and `0 ≠ 1` in `K` (`monicOfDegree_map`), so the first is established by this
  procedure and the second is a closed arithmetic fact.

It fails on a polynomial that is not monic or has another degree. -/
meta partial def monicEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "Monicₙ(K)" monicCases
where
  /-- The cases above, tried in turn on the main goal `p.Monic ∧ p.natDegree = n`. -/
  monicCases : TacticM Unit :=
    CasCatalogue.Evidence.closeByFirst
      m!"the polynomial is not established to be monic of the degree"
      [monicOfMap, monicByDegree,
       do CasCatalogue.Algebra.Polynomials.normalizePolynomial; monicByDegree]
  /-- `q.map f` is monic of degree `n` from `q` monic of degree `n` and `0 ≠ 1` in the target. -/
  monicOfMap : TacticM Unit := do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOfArity ``And 2 && (target.getArg! 0).isAppOfArity ``Polynomial.Monic 3 &&
        ((target.getArg! 0).getArg! 2).isAppOfArity ``Polynomial.map 6 do
      throwError "not the image of a polynomial along a ring map"
    evalTactic (← `(tactic|
      refine CasCatalogue.Algebra.LinearAlgebra.monicOfDegree_map _ ?_ ?_))
    for goal in ← getGoals do
      setGoals [goal]
      if (← instantiateMVars (← goal.getType)).consumeMData.isAppOf ``And then
        monicCases
      else
        CasCatalogue.Algebra.Polynomials.closeCoefficientGoals

/-- The companion matrix of a monic `p = xⁿ + Σ_{i<n} pᵢ xⁱ`: ones below the diagonal and
`-p₀, …, -pₙ₋₁` in the last column. Mathlib has no companion matrix. -/
def companion (n : ℕ) (K : Type) [CommRing K] : monics n K ⟶ matrices n K :=
  TypeCat.ofHom fun p => Matrix.of fun i j =>
    if j.val + 1 = n then -p.1.coeff i.val else if i.val = j.val + 1 then 1 else 0

/-- The kernel `{v | M v = 0}`. -/
def ker (n : ℕ) (K : Type) [CommRing K] : matrices n K ⟶ powerSet (Fin n → K) :=
  TypeCat.ofHom fun M => {v | M.mulVec v = 0}

/-- The span of a set of vectors. -/
def span (K : Type) [Field K] (n : ℕ) : powerSet (Fin n → K) ⟶ powerSet (Fin n → K) :=
  TypeCat.ofHom fun S => (Submodule.span K S : Set (Fin n → K))

/-- The dimension of the span of a set of vectors. -/
noncomputable def dim (K : Type) [Field K] (n : ℕ) :
    powerSet (Fin n → K) ⟶ CasCatalogue.Foundation.Objects.naturals :=
  TypeCat.ofHom fun S => Module.finrank K (Submodule.span K S)

end CasCatalogue.Algebra.LinearAlgebra

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.vectors"⟩, category := CategoryId.sets, name := "Vec"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.vectors }

normalized_registry .morphism
  { id := ⟨"mor.sets.vectors_zero"⟩, category := CategoryId.sets, name := "0"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.zero }

normalized_registry .object
  { id := ⟨"obj.sets.monics"⟩, category := CategoryId.sets, name := "Monic"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.monics
    inclusion := some `CasCatalogue.Algebra.LinearAlgebra.monicsInclusion
    admission := some `CasCatalogue.Algebra.LinearAlgebra.admitMonic
    evidence := some `CasCatalogue.Algebra.LinearAlgebra.monicEvidence }

normalized_registry .object
  { id := ⟨"obj.sets.matrices"⟩, category := CategoryId.sets, name := "Mat"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.matrices
    application := some `CasCatalogue.Algebra.LinearAlgebra.apply }

normalized_registry .morphism
  { id := ⟨"mor.sets.tuple_empty"⟩, category := CategoryId.sets, name := "()"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.empty }

normalized_registry .morphism
  { id := ⟨"mor.sets.tuple_cons"⟩, category := CategoryId.sets, name := "cons"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.cons }

normalized_registry .morphism
  { id := ⟨"mor.sets.matrix_rows"⟩, category := CategoryId.sets, name := "rows"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.rows }

normalized_registry .morphism
  { id := ⟨"mor.sets.matrix_det"⟩, category := CategoryId.sets, name := "det"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.det }

normalized_registry .morphism
  { id := ⟨"mor.sets.matrix_trace"⟩, category := CategoryId.sets, name := "trace"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.trace }

normalized_registry .morphism
  { id := ⟨"mor.sets.matrix_rank"⟩, category := CategoryId.sets, name := "rank"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.rank }

normalized_registry .morphism
  { id := ⟨"mor.sets.matrix_charpoly"⟩, category := CategoryId.sets, name := "charpoly"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.charpoly }

normalized_registry .morphism
  { id := ⟨"mor.sets.companion_matrix"⟩, category := CategoryId.sets, name := "companion_matrix"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.companion }

normalized_registry .morphism
  { id := ⟨"mor.sets.matrix_ker"⟩, category := CategoryId.sets, name := "ker"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.ker }

normalized_registry .morphism
  { id := ⟨"mor.sets.span"⟩, category := CategoryId.sets, name := "span"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.span }

normalized_registry .morphism
  { id := ⟨"mor.sets.span_dim"⟩, category := CategoryId.sets, name := "dim"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.dim }

end CasCatalogue
