/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Algebras
public import Mathlib.AlgebraicGeometry.Scheme
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Schemes over a ring (SPEC.md, "Differentials": `Spec ℚ[x] in Schemes/ℚ`)

* `Schemes` (Mathlib `AlgebraicGeometry.Scheme`).
* `Schemes/K` is the slice `Sch/Spec K` of schemes over `Spec K` (Mathlib `Over`), a category
  family over the object `Spec K` of schemes.
* `Spec A` of a `K`-algebra `A` is a scheme over `Spec K` by `Spec` of its structure map (Mathlib
  `Spec.map`): `Spec K[x]` and `Spec K[x₀, …, xₙ₋₁]`, named `Spec`.
-/

open CategoryTheory AlgebraicGeometry
open LeanCategories

namespace CasCatalogue

namespace CategoryId
def schemes : CategoryId := ⟨"cat.schemes"⟩
def schemesOver : CategoryId := ⟨"cat.schemes_over"⟩
end CategoryId

namespace Algebra.Schemes

universe u

/-- Schemes. -/
def schemesCategory : ObjCat.{u + 1, u} := Cat.of Scheme.{u}

def SchemesExpr : CategoryExpr := .atom CategoryId.schemes

noncomputable def schemesRealization : CategoryRealization SchemesExpr schemesCategory.{u} := {}

/-- `Schemes/S`, the slice over `S`. -/
def SchemesOverExpr : CategoryExpr :=
  .construct ConstructorId.slice #[.category SchemesExpr, .object ParameterId.x]

/-- `Schemes/S`. -/
def schemesOverCategory (S : schemesCategory.{u}) := Constructors.slice schemesCategory.{u} S

def schemesOverRealization (S : schemesCategory.{u}) :
    CategoryRealization SchemesOverExpr (schemesOverCategory S) := {}

/-- `Spec K[x]` over `Spec K`. -/
noncomputable def specPolynomials (K : Type) [CommRing K] :
    schemesOverCategory (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)))

/-- `Spec K[x₀, …, xₙ₋₁]` over `Spec K`. -/
noncomputable def specMvPolynomials (n : ℕ) (K : Type) [CommRing K] :
    schemesOverCategory (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)))

end Algebra.Schemes

normalized_registry .category
  { id := CategoryId.schemes, name := "Schemes",
    declaration := `CasCatalogue.Algebra.Schemes.schemesCategory
    expression := Algebra.Schemes.SchemesExpr
    realization := `CasCatalogue.Algebra.Schemes.schemesRealization }

normalized_registry .category
  { id := CategoryId.schemesOver, name := "Schemes/",
    declaration := `CasCatalogue.Algebra.Schemes.schemesOverCategory
    expression := Algebra.Schemes.SchemesOverExpr
    realization := `CasCatalogue.Algebra.Schemes.schemesOverRealization }

normalized_registry .object
  { id := ⟨"obj.schemes_over.spec_polynomials"⟩, category := CategoryId.schemesOver,
    name := "Spec Poly"
    declaration := `CasCatalogue.Algebra.Schemes.specPolynomials }

normalized_registry .object
  { id := ⟨"obj.schemes_over.spec_mv_polynomials"⟩, category := CategoryId.schemesOver,
    name := "Spec MvPoly"
    declaration := `CasCatalogue.Algebra.Schemes.specMvPolynomials }

end CasCatalogue
