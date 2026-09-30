/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.MvPolynomials
public import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public import LeanCategories.Catalogue.Semantics.Algebra.Ports
public import LeanCategories.Catalogue.Semantics.ConstructorRegistration
public import Mathlib.Algebra.Category.Ring.Under.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Commutative algebras over a ring (SPEC.md, "Ellipses": `R in Algebras/ℂ`)

* The underlying ring of a commutative ring, `CommRing → Ring` (Mathlib `forget₂`), is structural:
  it is the one route from commutative rings to sets, through rings.
* `Algebras/K` is the coslice `K ↓ CommRing` of commutative rings under `K` (Mathlib `Under K`;
  Mathlib `CommRingCat.toAlgHom`, `Under` over `CommRingCat` is the category of commutative
  `K`-algebras), a category family over the object `K`, with its structural forgetful functor to
  commutative rings.
* `K[x]` and `K[x₀, …, xₙ₋₁]` are `K`-algebras by their constants: the refinements of the named
  sets `Poly(K)` and `MvPoly(n, K)` into `Algebras/K`.
-/

open CategoryTheory
open LeanCategories LeanCategories.Algebra

namespace CasCatalogue

namespace CategoryId
def algebras : CategoryId := ⟨"cat.algebras"⟩
end CategoryId

namespace FunctorId
def commutativeRingsRings : FunctorId := ⟨"fun.commutative_rings.ring"⟩
def algebrasForget : FunctorId := ⟨"fun.algebras.forget"⟩
end FunctorId

namespace Algebra.Algebras

universe u

open CasCatalogue.Algebra.Catalogue.Rings CasCatalogue.Algebra.CatalogueRegistration

def CommutativeRingsRingsExpr : FunctorExpr CommutativeRings Rings :=
  .atomic FunctorId.commutativeRingsRings

/-- The underlying ring of a commutative ring. -/
def commutativeRingsRings : Algebra.CommutativeRings.{u} ⟶ Algebra.Rings.{u} :=
  (forget₂ CommRingCat RingCat).toCatHom

noncomputable def commutativeRingsRingsRealization :
    FunctorRealization CommutativeRingsRingsExpr Algebra.CommutativeRings.{u} Algebra.Rings.{u}
      commutativeRingsRings.toFunctor :=
  { sourceRealization := commutativeRingsRealization, targetRealization := ringsRealization }

/-- `Algebras/K`, the coslice `K ↓ CommRing`. -/
def AlgebrasExpr : CategoryExpr :=
  .construct ConstructorId.coslice #[.category CommutativeRings, .object ParameterId.x]

def AlgebrasForgetExpr : FunctorExpr AlgebrasExpr CommutativeRings :=
  .atomic FunctorId.algebrasForget

/-- `Algebras/K`. -/
def algebrasCategory (K : Algebra.CommutativeRings.{u}) :=
  Constructors.coslice Algebra.CommutativeRings.{u} K

def algebrasRealization (K : Algebra.CommutativeRings.{u}) :
    CategoryRealization AlgebrasExpr (algebrasCategory K) := {}

/-- The ring of a `K`-algebra. -/
def algebrasForget (K : Algebra.CommutativeRings.{u}) :
    algebrasCategory K ⥤ Algebra.CommutativeRings.{u} :=
  Under.forget K

noncomputable def algebrasForgetRealization (K : Algebra.CommutativeRings.{u}) :
    FunctorRealization AlgebrasForgetExpr (algebrasCategory K) Algebra.CommutativeRings.{u}
      (algebrasForget K) :=
  { sourceRealization := algebrasRealization K
    targetRealization := commutativeRingsRealization }

/-- `K[x₀, …, xₙ₋₁]` as a `K`-algebra. -/
noncomputable def mvAlgebra (n : ℕ) (K : Type) [CommRing K] :
    algebrasCategory (CommRingCat.of K) :=
  Under.mk (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin n) K))

/-- The underlying set of the `K`-algebra `K[x₀, …, xₙ₋₁]` is `K[x₀, …, xₙ₋₁]`. -/
def mvAlgebraIdentification (n : ℕ) (K : Type) [CommRing K] :
    (MvPolynomials.mvPolynomials n K : Foundation.PowerSets.SetsCat.{0}) ≅
      MvPolynomials.mvPolynomials n K :=
  Iso.refl _

/-- `K[x]` as a `K`-algebra. -/
noncomputable def polyAlgebra (K : Type) [CommRing K] : algebrasCategory (CommRingCat.of K) :=
  Under.mk (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K))

/-- The underlying set of the `K`-algebra `K[x]` is `K[x]`. -/
def polyAlgebraIdentification (K : Type) [CommRing K] :
    (Polynomials.polynomials K : Foundation.PowerSets.SetsCat.{0}) ≅ Polynomials.polynomials K :=
  Iso.refl _

end Algebra.Algebras

normalized_registry .functor
  { id := FunctorId.commutativeRingsRings, source := Algebra.Catalogue.Rings.CommutativeRings
    target := Algebra.Catalogue.Rings.Rings
    declaration := `CasCatalogue.Algebra.Algebras.commutativeRingsRings
    realization := `CasCatalogue.Algebra.Algebras.commutativeRingsRingsRealization
    expression := Algebra.Algebras.CommutativeRingsRingsExpr
    structural := true }

normalized_registry .category
  { id := CategoryId.algebras, name := "Algebras",
    declaration := `CasCatalogue.Algebra.Algebras.algebrasCategory
    expression := Algebra.Algebras.AlgebrasExpr
    realization := `CasCatalogue.Algebra.Algebras.algebrasRealization }

normalized_registry .functor
  { id := FunctorId.algebrasForget, source := Algebra.Algebras.AlgebrasExpr
    target := Algebra.Catalogue.Rings.CommutativeRings
    declaration := `CasCatalogue.Algebra.Algebras.algebrasForget
    realization := `CasCatalogue.Algebra.Algebras.algebrasForgetRealization
    expression := Algebra.Algebras.AlgebrasForgetExpr
    structural := true }

normalized_registry .object
  { id := ⟨"obj.algebras.mv_polynomials"⟩, category := CategoryId.algebras, name := "MvPoly"
    declaration := `CasCatalogue.Algebra.Algebras.mvAlgebra
    refines := some
      { base := ⟨"obj.sets.mv_polynomials"⟩
        route := #[.functor FunctorId.algebrasForget, .functor FunctorId.commutativeRingsRings] ++
          ringsToSets
        identification := `CasCatalogue.Algebra.Algebras.mvAlgebraIdentification } }

normalized_registry .object
  { id := ⟨"obj.algebras.polynomials"⟩, category := CategoryId.algebras, name := "Poly"
    declaration := `CasCatalogue.Algebra.Algebras.polyAlgebra
    refines := some
      { base := ⟨"obj.sets.polynomials"⟩
        route := #[.functor FunctorId.algebrasForget, .functor FunctorId.commutativeRingsRings] ++
          ringsToSets
        identification := `CasCatalogue.Algebra.Algebras.polyAlgebraIdentification } }

end CasCatalogue
