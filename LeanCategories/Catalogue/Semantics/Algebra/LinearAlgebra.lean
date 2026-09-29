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

@[expose] public section

/-!
# Vectors, matrices and spans (SPEC.md, "Vectors and matrices", "Subspaces and spans")

* `Xⁿ` is the set of `n`-tuples of `X` (`Fin n → X`); `0 ∈ Xⁿ` is its numeral when `X` has a zero.
  Tuples are built from `() : 1 → X⁰` and `cons : X × Xⁿ → Xⁿ⁺¹` (Mathlib `Matrix.vecCons`), the
  isomorphism `X × Xⁿ ≅ Xⁿ⁺¹`.
* `Matₙ(K)` is the set of `n × n` matrices over a commutative ring `K`, made from its rows by
  `rows : (Kⁿ)ⁿ → Matₙ(K)` (Mathlib `Matrix.of`); a matrix is applied to vectors,
  `Matₙ(K) × Kⁿ → Kⁿ` (Mathlib `Matrix.mulVec`).
* `det`, `trace : Matₙ(K) → K`, `rank : Matₙ(K) → ℕ`, `charpoly : Matₙ(K) → K[x]`, and
  `ker : Matₙ(K) → 𝒫(Kⁿ)`, `{v | M v = 0}`.
* Over a field `K`: `span : 𝒫(Kⁿ) → 𝒫(Kⁿ)` (the subspace a set spans, Mathlib `Submodule.span`)
  and `dim : 𝒫(Kⁿ) → ℕ`, the dimension of its span (Mathlib `Module.finrank`).
-/

open CategoryTheory

namespace CasCatalogue.Algebra.LinearAlgebra

open CasCatalogue.Foundation.PowerSets CasCatalogue.Algebra.Polynomials

/-- `Xⁿ`. -/
abbrev vectors (X : Type) [Zero X] (n : ℕ) : SetsCat.{0} := Fin n → X

/-- The numeral `0 ∈ Xⁿ`. -/
def vectorsElement (X : Type) [Zero X] (n : ℕ) (k : ℕ) : Option (vectors X n) :=
  if k = 0 then some 0 else none

/-- The empty tuple `() ∈ X⁰`. -/
def empty (X : Type) [Zero X] : CasCatalogue.Foundation.Objects.fin 1 ⟶ vectors X 0 :=
  TypeCat.ofHom fun _ => ![]

/-- `(x, v) ↦ (x, v₀, …)`, `X × Xⁿ → Xⁿ⁺¹`. -/
def cons (X : Type) [Zero X] (n : ℕ) : (X × vectors X n : SetsCat.{0}) ⟶ vectors X (n + 1) :=
  TypeCat.ofHom fun p => Matrix.vecCons p.1 p.2

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

normalized_registry .elementLiteral
  { id := ⟨"elt.sets.vectors"⟩, object := ⟨"obj.sets.vectors"⟩
    denotation := `CasCatalogue.Algebra.LinearAlgebra.vectorsElement }

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
  { id := ⟨"mor.sets.matrix_ker"⟩, category := CategoryId.sets, name := "ker"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.ker }

normalized_registry .morphism
  { id := ⟨"mor.sets.span"⟩, category := CategoryId.sets, name := "span"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.span }

normalized_registry .morphism
  { id := ⟨"mor.sets.span_dim"⟩, category := CategoryId.sets, name := "dim"
    declaration := `CasCatalogue.Algebra.LinearAlgebra.dim }

end CasCatalogue
