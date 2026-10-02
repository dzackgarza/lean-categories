/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Concrete.PolynomialPresentation
public import LeanCategories.Catalogue.Semantics.Algebra.Algebras
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Algebras
public meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings

@[expose] public section

/-!
# Polynomial quotient presentations and their selected translation

The presentation `R[X]/(f)` retains the chosen coefficient ring and defining
polynomial. Translation is the isomorphism induced by `X ↦ X + c`, with its
actual inverse. Two presentations are distinct objects; the comparison is an
explicit datum for transport, never an assertion that they are equal.
-/

open CategoryTheory
open CasCatalogue.Foundation.PowerSets

namespace CasCatalogue.Algebra.PolynomialPresentations
open LeanCategories.Algebra.PolynomialPresentation

/-- The set of the chosen polynomial quotient presentation. -/
abbrev quotient (R : CommRingCat.{0}) (f : Polynomial R) : SetsCat.{0} := AdjoinRoot f

/-- The chosen quotient as a commutative ring. -/
noncomputable abbrev quotientRing (R : CommRingCat.{0}) (f : Polynomial R) :
    CommRingCat.{0} := CommRingCat.of (AdjoinRoot f)

/-- The distinguished root is part of the presentation. -/
noncomputable def generator (R : CommRingCat.{0}) (f : Polynomial R) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ quotient R f :=
  TypeCat.ofHom fun _ => AdjoinRoot.root f

/-- Constants retain the chosen coefficient map. -/
noncomputable def constants (R : CommRingCat.{0}) (f : Polynomial R) :
    (R : SetsCat.{0}) ⟶ quotient R f := TypeCat.ofHom (AdjoinRoot.of f)

/-- Forgetting ring structure keeps precisely the selected quotient presentation. -/
def quotientIdentification (R : CommRingCat.{0}) (f : Polynomial R) :
    (forget CommRingCat).obj (quotientRing R f) ≅ quotient R f := Iso.refl _

/-- The generic comparison, including its chosen translation parameter. -/
noncomputable def translation (R : CommRingCat.{0}) (f : Polynomial R) (c : R) :
    quotientRing R f ≅ quotientRing R (Polynomial.taylor c f) :=
  (translate f c).toRingEquiv.toCommRingCatIso

/-- The target quadratic quotient presentation. -/
noncomputable abbrev second : CommRingCat.{0} :=
  quotientRing (CommRingCat.of (ZMod 3)) secondPolynomial

/-- The source quadratic quotient presentation. -/
noncomputable abbrev first : CommRingCat.{0} :=
  quotientRing (CommRingCat.of (ZMod 3)) firstPolynomial

/-- The prescribed comparison `x ↦ y + 2` between the two presentations. -/
noncomputable def quadraticComparison : first ≅ second :=
  comparison.toRingEquiv.toCommRingCatIso

/-- Underlying set of the source quadratic presentation. -/
noncomputable abbrev firstSet : SetsCat.{0} := AdjoinRoot firstPolynomial

/-- Underlying set of the target quadratic presentation. -/
noncomputable abbrev secondSet : SetsCat.{0} := AdjoinRoot secondPolynomial

def firstIdentification : (forget CommRingCat).obj first ≅ firstSet := Iso.refl _
def secondIdentification : (forget CommRingCat).obj second ≅ secondSet := Iso.refl _

end CasCatalogue.Algebra.PolynomialPresentations

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.polynomial_quotient"⟩, category := CategoryId.sets
    name := "PolynomialQuotient"
    declaration := `CasCatalogue.Algebra.PolynomialPresentations.quotient
    generator := some `CasCatalogue.Algebra.PolynomialPresentations.generator
    constants := some `CasCatalogue.Algebra.PolynomialPresentations.constants }

normalized_registry .object
  { id := ⟨"obj.commutative_rings.polynomial_quotient"⟩
    category := CategoryId.commutativeRings, name := "PolynomialQuotient"
    declaration := `CasCatalogue.Algebra.PolynomialPresentations.quotientRing
    refines := some
      { base := ⟨"obj.sets.polynomial_quotient"⟩
        route := #[.functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.PolynomialPresentations.quotientIdentification } }

normalized_registry .presentation
  { id := ⟨"cmp.polynomial_quotient.translation"⟩, name := "polynomialTranslation"
    source := ⟨"obj.commutative_rings.polynomial_quotient"⟩
    target := ⟨"obj.commutative_rings.polynomial_quotient"⟩
    declaration := `CasCatalogue.Algebra.PolynomialPresentations.translation }

normalized_registry .object
  { id := ⟨"obj.sets.f9_x"⟩, category := CategoryId.sets, name := "F9x"
    declaration := `CasCatalogue.Algebra.PolynomialPresentations.firstSet }
normalized_registry .object
  { id := ⟨"obj.sets.f9_y"⟩, category := CategoryId.sets, name := "F9y"
    declaration := `CasCatalogue.Algebra.PolynomialPresentations.secondSet }
normalized_registry .object
  { id := ⟨"obj.commutative_rings.f9_x"⟩, category := CategoryId.commutativeRings
    name := "F9x", declaration := `CasCatalogue.Algebra.PolynomialPresentations.first
    refines := some
      { base := ⟨"obj.sets.f9_x"⟩
        route := #[.functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.PolynomialPresentations.firstIdentification } }
normalized_registry .object
  { id := ⟨"obj.commutative_rings.f9_y"⟩, category := CategoryId.commutativeRings
    name := "F9y", declaration := `CasCatalogue.Algebra.PolynomialPresentations.second
    refines := some
      { base := ⟨"obj.sets.f9_y"⟩
        route := #[.functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.PolynomialPresentations.secondIdentification } }
normalized_registry .presentation
  { id := ⟨"cmp.f9.translation"⟩, name := "F9translation"
    source := ⟨"obj.commutative_rings.f9_x"⟩, target := ⟨"obj.commutative_rings.f9_y"⟩
    declaration := `CasCatalogue.Algebra.PolynomialPresentations.quadraticComparison }

end CasCatalogue
