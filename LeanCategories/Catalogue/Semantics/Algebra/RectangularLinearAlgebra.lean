/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Catalogue
public meta import LeanCategories.Catalogue.Semantics.Foundation.Catalogue

@[expose] public section

/-!
# Ordinary rectangular module maps

The two dimensions are independent: parameter order is rows, columns,
coefficient ring, matrix. Square matrices specialize to the existing operation.
For a single row, the codomain is the ring's actual regular module, using
evaluation of the sole coordinate. Thus a `1 × 2` matrix denotes `R² → R`,
without replacing it by a square endomorphism.

Source: Mathlib `Matrix.mulVecLin` and `LinearMap.proj`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.RectangularLinearAlgebra

open LinearAlgebra

/-- Rectangular matrices with their two independent selected dimensions. -/
abbrev rectangularMatrices (rows columns : ℕ) (R : CommRingCat.{0}) : Type :=
  Matrix (Fin rows) (Fin columns) R

/-- The ordinary linear map of a rectangular matrix, with both module endpoints. -/
def rectangularLinearMap (rows columns : ℕ) (R : CommRingCat.{0})
    (M : rectangularMatrices rows columns R) :
    vectorModule (RingCat.of R) columns ⟶ vectorModule (RingCat.of R) rows :=
  ModuleCat.ofHom M.mulVecLin

/-- Its action is the standard rectangular matrix-vector product. -/
theorem rectangularLinearMap_apply (rows columns : ℕ) (R : CommRingCat.{0})
    (M : rectangularMatrices rows columns R) (x : Fin columns → R) :
    (rectangularLinearMap rows columns R M).hom x = M.mulVec x := rfl

/-- The square specialization agrees with the existing owner. -/
theorem square_specialization (n : ℕ) (R : CommRingCat.{0}) (M : matrices n R) :
    rectangularLinearMap n n R M = matrixLinearMap n R M := rfl

/-- A row matrix as a map into the actual scalar regular module. -/
def rowLinearMap (columns : ℕ) (R : CommRingCat.{0})
    (M : rectangularMatrices 1 columns R) :
    vectorModule (RingCat.of R) columns ⟶
      CasCatalogue.Modules.CatalogueRegistration.regularModule (RingCat.of R) :=
  rectangularLinearMap 1 columns R M ≫ ModuleCat.ofHom (LinearMap.proj 0)

/-- The codomain coordinate is the actual scalar value of the selected row. -/
theorem rowLinearMap_apply (columns : ℕ) (R : CommRingCat.{0})
    (M : rectangularMatrices 1 columns R) (x : Fin columns → R) :
    (rowLinearMap columns R M).hom x = ∑ j, M 0 j * x j := rfl

end CasCatalogue.Algebra.RectangularLinearAlgebra

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.rectangular_matrices"⟩, category := CategoryId.sets
    name := "RectangularMatrices"
    declaration := `CasCatalogue.Algebra.RectangularLinearAlgebra.rectangularMatrices }
normalized_registry .morphism
  { id := ⟨"mor.modules.rectangular_linear_map"⟩, category := CategoryId.modulesR
    name := "rectangular_linear_map"
    declaration := `CasCatalogue.Algebra.RectangularLinearAlgebra.rectangularLinearMap }
normalized_registry .morphism
  { id := ⟨"mor.modules.row_linear_map"⟩, category := CategoryId.modulesR
    name := "row_linear_map"
    declaration := `CasCatalogue.Algebra.RectangularLinearAlgebra.rowLinearMap }

end CasCatalogue
