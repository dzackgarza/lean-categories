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
def schemesOverRing : CategoryId := ⟨"cat.schemes_over_ring"⟩
end CategoryId

namespace CategoryFamilyId
def schemesOverRing : CategoryFamilyId := ⟨"family.schemes_over_ring"⟩
end CategoryFamilyId

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

/-- The actual affine base scheme associated to a selected commutative ring. -/
noncomputable def specBase (K : CommRingCat.{u}) : schemesCategory.{u} := Spec K

/-- Schemes over a ring mean schemes over its affine spectrum, independently of
any particular object subsequently constructed in this category. -/
noncomputable def schemesOverRingCategory (K : CommRingCat.{u}) : ObjCat.{u + 1, u} :=
  schemesOverCategory (specBase K)

def SchemesOverRingExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.schemesOverRing #[.variable ParameterId.r]

noncomputable def schemesOverRingFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1} (P := CommRingCat.{u})
    (fun K => schemesOverRingCategory K)

noncomputable def schemesOverRingFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1}
      CategoryFamilyId.schemesOverRing .commRing (P := Discrete (CommRingCat.{u})) where
  transport := schemesOverRingFamilyTransport
  transportSemantics := .discrete

noncomputable def schemesOverRingRealization (K : CommRingCat.{u}) :
    CategoryRealization SchemesOverRingExpr (schemesOverRingCategory K) where
  familyFibre := some (.mk schemesOverRingFamilyRealization {
    parameter := ⟨K⟩
    parameterQuotation := .commRingR K
    category_eq := by rfl })

/-- `Spec K[x]` over `Spec K`. -/
noncomputable def specPolynomials (K : CommRingCat.{0}) :
    schemesOverRingCategory K :=
  Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K)))

/-- `Spec K[x₀, …, xₙ₋₁]` over `Spec K`. -/
noncomputable def specMvPolynomials (n : ℕ) (K : CommRingCat.{0}) :
    schemesOverRingCategory K :=
  Over.mk (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)))

end Algebra.Schemes

normalized_registry .category
  { id := CategoryId.schemes, name := "Schemes",
    declaration := `CasCatalogue.Algebra.Schemes.schemesCategory
    expression := Algebra.Schemes.SchemesExpr
    realization := `CasCatalogue.Algebra.Schemes.schemesRealization }

normalized_registry .category
  { id := CategoryId.schemesOver, name := "SchemesOver",
    declaration := `CasCatalogue.Algebra.Schemes.schemesOverCategory
    expression := Algebra.Schemes.SchemesOverExpr
    realization := `CasCatalogue.Algebra.Schemes.schemesOverRealization }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.schemesOverRing, schema := .commRing
    realization := `CasCatalogue.Algebra.Schemes.schemesOverRingFamilyRealization
    transport := `CasCatalogue.Algebra.Schemes.schemesOverRingFamilyTransport
    transportSemantics := .discrete }

normalized_registry .category
  { id := CategoryId.schemesOverRing, name := "Schemes/"
    declaration := `CasCatalogue.Algebra.Schemes.schemesOverRingCategory
    expression := Algebra.Schemes.SchemesOverRingExpr
    realization := `CasCatalogue.Algebra.Schemes.schemesOverRingRealization }

normalized_registry .object
  { id := ⟨"obj.schemes.spec_base"⟩, category := CategoryId.schemes, name := "Spec"
    declaration := `CasCatalogue.Algebra.Schemes.specBase }

normalized_registry .object
  { id := ⟨"obj.schemes_over.spec_polynomials"⟩, category := CategoryId.schemesOverRing,
    name := "Spec Poly"
    declaration := `CasCatalogue.Algebra.Schemes.specPolynomials }

normalized_registry .object
  { id := ⟨"obj.schemes_over.spec_mv_polynomials"⟩, category := CategoryId.schemesOverRing,
    name := "Spec MvPoly"
    declaration := `CasCatalogue.Algebra.Schemes.specMvPolynomials }

end CasCatalogue
