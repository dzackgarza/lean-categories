/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Fields
public import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import LeanCategories.CategoryTheory.OneCat.KernelFunctor
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials

@[expose] public section

/-!
# Vectors, matrices and spans (SPEC.md, "Vectors and matrices", "Subspaces and spans")

* `Xⁿ` is the set of `n`-tuples of `X` (`Fin n → X`), built from `() : 1 → X⁰` and
  `cons : X × Xⁿ → Xⁿ⁺¹` (Mathlib `Matrix.vecCons`), the isomorphism `X × Xⁿ ≅ Xⁿ⁺¹`. A set `Xⁿ`
  has no zero; over an additive monoid `A`, `Aⁿ` is the product additive monoid, whose unit is
  `0 : 1 → Aⁿ` (for a ring `K`, the zero of the `K`-module `Kⁿ`).
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

/-- An additive monoid as an `AddMonCat`. -/
abbrev asAddMonoid (A : LeanCategories.Algebra.AdditiveMonoids.{0}) : AddMonCat.{0} := A

/-- `0 ∈ Aⁿ`, the unit of the additive monoid `Aⁿ`, the `n`-fold product of the additive
monoid `A` (Mathlib `Pi.addMonoid`, the product in `AddMonCat`): the point `(0, …, 0)`. It exists
for every additive monoid `A`, so `A` is an object of additive monoids (LC-13), not a carrier with
an instance.
For a ring `K` it is the zero vector of the `K`-module `Kⁿ`, whose additive monoid is `Aⁿ` at the
additive monoid `A` of `K` (along `Ring → AddCommMon → AddMon`). -/
def zero (A : LeanCategories.Algebra.AdditiveMonoids.{0}) (n : ℕ) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ vectors (asAddMonoid A) n :=
  TypeCat.ofHom fun _ => 0

/-- `Matₙ(K)`. -/
abbrev matrices (n : ℕ) (K : CommRingCat.{0}) : SetsCat.{0} := Matrix (Fin n) (Fin n) K

/-- The matrix with the given rows. -/
def rows (n : ℕ) (K : CommRingCat.{0}) : vectors (vectors K n) n ⟶ matrices n K :=
  TypeCat.ofHom fun r => Matrix.of r

/-- `(M, v) ↦ M v`. -/
def apply (n : ℕ) (K : CommRingCat.{0}) :
    (matrices n K × vectors K n : SetsCat.{0}) ⟶ vectors K n :=
  TypeCat.ofHom fun p => p.1.mulVec p.2

/-- The determinant. -/
def det (n : ℕ) (K : CommRingCat.{0}) : matrices n K ⟶ (K : SetsCat.{0}) :=
  TypeCat.ofHom fun M => M.det

/-- The trace. -/
def trace (n : ℕ) (K : CommRingCat.{0}) : matrices n K ⟶ (K : SetsCat.{0}) :=
  TypeCat.ofHom fun M => M.trace

/-- The rank. -/
noncomputable def rank (n : ℕ) (K : CommRingCat.{0}) :
    matrices n K ⟶ CasCatalogue.Foundation.Objects.naturals :=
  TypeCat.ofHom fun M => M.rank

/-- The characteristic polynomial `det(x - M)`. -/
noncomputable def charpoly (n : ℕ) (K : CommRingCat.{0}) : matrices n K ⟶ polynomials K :=
  TypeCat.ofHom fun M => M.charpoly

/-- `Monicₙ(K)`, the monic polynomials of degree `n`. -/
abbrev monics (n : ℕ) (K : CommRingCat.{0}) : SetsCat.{0} :=
  {p : Polynomial K // p.Monic ∧ p.natDegree = n}

/-- `Monicₙ(K) ↪ K[x]`. -/
def monicsInclusion (n : ℕ) (K : CommRingCat.{0}) : monics n K ⟶ polynomials K :=
  TypeCat.ofHom Subtype.val

/-- The monic polynomial `p` of degree `n`, with that evidence. -/
def admitMonic (n : ℕ) (K : CommRingCat.{0}) (p : Polynomial K)
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
def companion (n : ℕ) (K : CommRingCat.{0}) : monics n K ⟶ matrices n K :=
  TypeCat.ofHom fun p => Matrix.of fun i j =>
    if j.val + 1 = n then -p.1.coeff i.val else if i.val = j.val + 1 then 1 else 0

/-- The kernel `{v | M v = 0}`. -/
def ker (n : ℕ) (K : CommRingCat.{0}) : matrices n K ⟶ powerSet (Fin n → K) :=
  TypeCat.ofHom fun M => {v | M.mulVec v = 0}

/-- The span of a set of vectors over the selected field. -/
def span (K : LeanCategories.Algebra.FieldCat.{0}) (n : ℕ) :
    powerSet (Fin n → Fields.ring K) ⟶ powerSet (Fin n → Fields.ring K) :=
  TypeCat.ofHom fun S => (Submodule.span (Fields.ring K) S : Set (Fin n → Fields.ring K))

/-- A submodule as a chosen categorical subobject, retaining its module and defining inclusion.
This is the representative used by Mathlib `ModuleCat.subobjectModule`, the order isomorphism
between categorical subobjects and submodules. It works for any ring and module, independently
of coordinates or a chosen field. -/
def submoduleSubobject {R : Type*} [Ring R] (M : ModuleCat R) (N : Submodule R M) :
    (LeanCategories.isMonoArrow (ModuleCat R)).FullSubcategory :=
  ⟨Arrow.mk (ModuleCat.ofHom N.subtype), by
    exact (ModuleCat.mono_iff_injective _).2 N.subtype_injective⟩

/-- The generated submodule, with its actual inclusion, as a chosen categorical subobject.
The standard span is the least submodule containing the generators (`Submodule.span_le`). -/
def generatedSubobject {R : Type*} [Ring R] (M : ModuleCat R) (S : Set M) :
    (LeanCategories.isMonoArrow (ModuleCat R)).FullSubcategory :=
  submoduleSubobject M (Submodule.span R S)

/-- The chosen subobject underlying the subset-valued `span` above. Its domain is the span
module itself, and its arrow sends a vector in that module to the same ambient vector. -/
def spanSubobject (K : LeanCategories.Algebra.FieldCat.{0}) (n : ℕ)
    (S : Set (Fin n → Fields.ring K)) :
    (LeanCategories.isMonoArrow (ModuleCat (Fields.ring K))).FullSubcategory :=
  generatedSubobject (ModuleCat.of (Fields.ring K) (Fin n → Fields.ring K)) S

/-- The chosen inclusion has exactly the standard generated submodule as its image. -/
theorem generatedSubobject_range {R : Type*} [Ring R] (M : ModuleCat R) (S : Set M) :
    LinearMap.range (generatedSubobject M S).obj.hom.hom = Submodule.span R S :=
  Submodule.range_subtype _

/-- The generated image is least among all submodules containing the generators. -/
theorem generatedSubobject_le_iff {R : Type*} [Ring R] (M : ModuleCat R)
    (S : Set M) (N : Submodule R M) :
    LinearMap.range (generatedSubobject M S).obj.hom.hom ≤ N ↔ S ⊆ N := by
  change LinearMap.range (Submodule.span R S).subtype ≤ N ↔ S ⊆ N
  rw [Submodule.range_subtype]
  exact Submodule.span_le

/-- Forgetting the chosen span inclusion recovers precisely the existing subset-valued span. -/
theorem spanSubobject_range (K : LeanCategories.Algebra.FieldCat.{0}) (n : ℕ)
    (S : Set (Fin n → Fields.ring K)) :
    Set.range (spanSubobject K n S).obj.hom = (span K n).hom S := by
  exact congrArg (fun N : Submodule (Fields.ring K) (Fin n → Fields.ring K) =>
    (N : Set (Fin n → Fields.ring K)))
      (generatedSubobject_range (ModuleCat.of (Fields.ring K) (Fin n → Fields.ring K)) S)

/-- The dimension of the span over the selected field, using its compatible field structure. -/
noncomputable def dim (K : LeanCategories.Algebra.FieldCat.{0}) (n : ℕ) :
    powerSet (Fin n → Fields.ring K) ⟶ CasCatalogue.Foundation.Objects.naturals :=
  letI := Fields.fieldStructure K
  TypeCat.ofHom fun S => Module.finrank (Fields.ring K) (Submodule.span (Fields.ring K) S)

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
