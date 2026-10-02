/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Algebras
public import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public meta import LeanCategories.Catalogue.Semantics.Algebra.Algebras
public meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Named coefficient rings

The integer, residue, rational, real and complex rings carry their canonical commutative
ring structures (Mathlib `CommRingCat.of`). Forgetting commutativity recovers the already
named ring, by the identity ring isomorphism. These refinements retain the existing names
and carrier identifications; they provide typed coefficient objects for commutative-ring
families, without making a choice of a new ring structure on a named carrier.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.NamedCommutativeRings

/-- `ℤ` with its canonical commutative ring structure. -/
abbrev integers : CommRingCat.{0} := CommRingCat.of (ℤ)

/-- Forgetting commutativity recovers the named ring `ℤ`. -/
def integersIdentification :
    (forget₂ CommRingCat RingCat).obj (integers) ≅ NamedRings.ringIntegers :=
  Iso.refl _

/-- `ZMod n` with its canonical commutative ring structure. -/
abbrev integersMod (n : ℕ) : CommRingCat.{0} := CommRingCat.of (ZMod n)

/-- Forgetting commutativity recovers the named ring `ZMod n`. -/
def integersModIdentification (n : ℕ) :
    (forget₂ CommRingCat RingCat).obj (integersMod n) ≅ NamedRings.ringIntegersMod n :=
  Iso.refl _

/-- `ℚ` with its canonical commutative ring structure. -/
abbrev rationals : CommRingCat.{0} := CommRingCat.of (ℚ)

/-- Forgetting commutativity recovers the named ring `ℚ`. -/
def rationalsIdentification :
    (forget₂ CommRingCat RingCat).obj (rationals) ≅ NamedRings.ringRationals :=
  Iso.refl _

/-- `ℝ` with its canonical commutative ring structure. -/
noncomputable abbrev reals : CommRingCat.{0} := CommRingCat.of (ℝ)

/-- Forgetting commutativity recovers the named ring `ℝ`. -/
noncomputable def realsIdentification :
    (forget₂ CommRingCat RingCat).obj (reals) ≅ NumberSystems.ringReals :=
  Iso.refl _

/-- `ℂ` with its canonical commutative ring structure. -/
noncomputable abbrev complexes : CommRingCat.{0} := CommRingCat.of (ℂ)

/-- Forgetting commutativity recovers the named ring `ℂ`. -/
noncomputable def complexesIdentification :
    (forget₂ CommRingCat RingCat).obj (complexes) ≅ NumberSystems.ringComplexes :=
  Iso.refl _

/-- The underlying set is the already named set. -/
noncomputable def integersCarrierIdentification :
    (forget CommRingCat).obj (integers) ≅ Foundation.Objects.integers :=
  Iso.refl _

/-- The underlying set is the already named set. -/
noncomputable def integersModCarrierIdentification (n : ℕ) :
    (forget CommRingCat).obj (integersMod n) ≅ Foundation.Objects.integersMod n :=
  Iso.refl _

/-- The underlying set is the already named set. -/
noncomputable def rationalsCarrierIdentification :
    (forget CommRingCat).obj (rationals) ≅ NamedRings.rationals :=
  Iso.refl _

/-- The underlying set is the already named set. -/
noncomputable def realsCarrierIdentification :
    (forget CommRingCat).obj (reals) ≅ NumberSystems.reals :=
  Iso.refl _

/-- The underlying set is the already named set. -/
noncomputable def complexesCarrierIdentification :
    (forget CommRingCat).obj (complexes) ≅ NumberSystems.complexes :=
  Iso.refl _

/-- The canonical integer coefficient map into any chosen commutative ring. -/
def integerCoefficients (R : CommRingCat.{0}) : integers ⟶ R :=
  CommRingCat.ofHom (Int.castRingHom R)

/-- The canonical rational coefficient map into the reals. -/
noncomputable def rationalRealCoefficients : rationals ⟶ reals :=
  CommRingCat.ofHom (algebraMap ℚ ℝ)

/-- The canonical rational coefficient map into the complex numbers. -/
noncomputable def rationalComplexCoefficients : rationals ⟶ complexes :=
  CommRingCat.ofHom (algebraMap ℚ ℂ)

/-- The canonical real coefficient map into the complex numbers. -/
noncomputable def realComplexCoefficients : reals ⟶ complexes :=
  CommRingCat.ofHom Complex.ofRealHom

/-- The selected real algebra over the integers, retaining its defining coefficient map. -/
noncomputable def realIntegerAlgebra : Algebras.algebrasCategory integers :=
  Algebras.scalarAlgebra integers reals (integerCoefficients reals)

/-- The selected real algebra over the rationals, retaining its defining coefficient map. -/
noncomputable def realRationalAlgebra : Algebras.algebrasCategory rationals :=
  Algebras.scalarAlgebra rationals reals rationalRealCoefficients

/-- The selected complex algebra over the integers. -/
noncomputable def complexIntegerAlgebra : Algebras.algebrasCategory integers :=
  Algebras.scalarAlgebra integers complexes (integerCoefficients complexes)

/-- The selected complex algebra over the rationals. -/
noncomputable def complexRationalAlgebra : Algebras.algebrasCategory rationals :=
  Algebras.scalarAlgebra rationals complexes rationalComplexCoefficients

/-- The selected complex algebra over the reals. -/
noncomputable def complexRealAlgebra : Algebras.algebrasCategory reals :=
  Algebras.scalarAlgebra reals complexes realComplexCoefficients

/-- The registered ring map's underlying set map is the existing scalar inclusion. -/
theorem rationalRealCoefficients_underlying :
    (forget CommRingCat).map rationalRealCoefficients = NumberSystems.rationalsReals := rfl

/-- The registered ring map's underlying set map is the existing scalar inclusion. -/
theorem realComplexCoefficients_underlying :
    (forget CommRingCat).map realComplexCoefficients = NumberSystems.realsComplexes := rfl

end CasCatalogue.Algebra.NamedCommutativeRings

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.commutative_rings.integers"⟩, category := CategoryId.commutativeRings
    name := "ℤ"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.integers
    refines := some
      { base := ⟨"obj.sets.integers"⟩
        route := #[.functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.NamedCommutativeRings.integersCarrierIdentification } }

normalized_registry .object
  { id := ⟨"obj.commutative_rings.integers_mod"⟩, category := CategoryId.commutativeRings
    name := "ZMod"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.integersMod
    refines := some
      { base := ⟨"obj.sets.integers_mod"⟩
        route := #[.functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.NamedCommutativeRings.integersModCarrierIdentification } }

normalized_registry .object
  { id := ⟨"obj.commutative_rings.rationals"⟩, category := CategoryId.commutativeRings
    name := "ℚ"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.rationals
    refines := some
      { base := ⟨"obj.sets.rationals"⟩
        route := #[.functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.NamedCommutativeRings.rationalsCarrierIdentification } }

normalized_registry .object
  { id := ⟨"obj.commutative_rings.reals"⟩, category := CategoryId.commutativeRings
    name := "ℝ"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.reals
    refines := some
      { base := ⟨"obj.sets.reals"⟩
        route := #[.functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.NamedCommutativeRings.realsCarrierIdentification } }

normalized_registry .object
  { id := ⟨"obj.commutative_rings.complexes"⟩, category := CategoryId.commutativeRings
    name := "ℂ"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.complexes
    refines := some
      { base := ⟨"obj.sets.complexes"⟩
        route := #[.functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.NamedCommutativeRings.complexesCarrierIdentification } }

normalized_registry .morphism
  { id := ⟨"mor.commutative_rings.integer_coefficients"⟩, category := CategoryId.commutativeRings
    name := "integerCoefficients"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.integerCoefficients }
normalized_registry .morphism
  { id := ⟨"mor.commutative_rings.rational_real_coefficients"⟩
    category := CategoryId.commutativeRings, name := "rationalRealCoefficients"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.rationalRealCoefficients }
normalized_registry .morphism
  { id := ⟨"mor.commutative_rings.rational_complex_coefficients"⟩
    category := CategoryId.commutativeRings, name := "rationalComplexCoefficients"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.rationalComplexCoefficients }
normalized_registry .morphism
  { id := ⟨"mor.commutative_rings.real_complex_coefficients"⟩
    category := CategoryId.commutativeRings, name := "realComplexCoefficients"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.realComplexCoefficients }

normalized_registry .object
  { id := ⟨"obj.algebras.real_integer"⟩, category := CategoryId.algebras, name := "RealOverIntegers"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.realIntegerAlgebra }
normalized_registry .object
  { id := ⟨"obj.algebras.real_rational"⟩, category := CategoryId.algebras, name := "RealOverRationals"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.realRationalAlgebra }
normalized_registry .object
  { id := ⟨"obj.algebras.complex_integer"⟩, category := CategoryId.algebras
    name := "ComplexOverIntegers"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.complexIntegerAlgebra }
normalized_registry .object
  { id := ⟨"obj.algebras.complex_rational"⟩, category := CategoryId.algebras
    name := "ComplexOverRationals"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.complexRationalAlgebra }
normalized_registry .object
  { id := ⟨"obj.algebras.complex_real"⟩, category := CategoryId.algebras, name := "ComplexOverReals"
    declaration := `CasCatalogue.Algebra.NamedCommutativeRings.complexRealAlgebra }

end CasCatalogue
