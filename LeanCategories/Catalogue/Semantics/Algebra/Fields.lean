/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Exceptional.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
public import Mathlib.Algebra.Field.IsField
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Rings
public meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings

@[expose] public section

/-!
# Chosen fields

A field is a commutative ring whose own multiplication has inverses for nonzero
elements, represented by the existing `LeanCategories.Algebra.FieldCat` full
subcategory. Field-dependent operations take this object, never a carrier with
an unrelated field instance (LC-13). Mathlib `IsField.toField` recovers the unique
inverse operation compatible with that selected ring structure.
-/

open CategoryTheory

namespace CasCatalogue
namespace CategoryId
def fields : CategoryId := ⟨"cat.fields"⟩
end CategoryId
namespace ClassifierId
def commutativeRingsField : ClassifierId := ⟨"clf.commutative_rings.field"⟩
end ClassifierId

namespace Algebra.Fields
universe u
open LeanCategories
open CasCatalogue.Algebra.CatalogueRegistration

/-- Fields retain the chosen commutative ring structure. -/
noncomputable def fieldClassifier : Classifier LeanCategories.Algebra.CommutativeRings.{u} where
  total := Cat.of LeanCategories.Algebra.FieldCat.{u}
  forget := (ObjectProperty.ι (fun R : CommRingCat.{u} => IsField R)).toCatHom

def Fields : CategoryExpr := .classifierTotal ClassifierId.commutativeRingsField
noncomputable def fieldsCategory := fieldClassifier.{u}.total
noncomputable def fieldsRealization : CategoryRealization Fields fieldsCategory.{u} := {}
noncomputable def fieldRealization :
    ClassifierRealization Algebra.Catalogue.Rings.CommutativeRings
      ClassifierId.commutativeRingsField LeanCategories.Algebra.CommutativeRings.{u}
      fieldClassifier :=
  { hostRealization := commutativeRingsRealization, totalRealization := fieldsRealization }

/-- The selected field's underlying ring, including its chosen operations. -/
abbrev ring (K : LeanCategories.Algebra.FieldCat.{u}) : CommRingCat.{u} := K.obj

/-- Its field structure is compatible with the chosen ring, by the defining property. -/
noncomputable def fieldStructure (K : LeanCategories.Algebra.FieldCat.{u}) : Field (ring K) :=
  K.property.toField

/-- The named rational field refines its already selected commutative ring. -/
def rationals : LeanCategories.Algebra.FieldCat.{0} :=
  ⟨NamedCommutativeRings.rationals, Field.toIsField ℚ⟩

/-- The named real field refines its already selected commutative ring. -/
noncomputable def reals : LeanCategories.Algebra.FieldCat.{0} :=
  ⟨NamedCommutativeRings.reals, Field.toIsField ℝ⟩

/-- The named complex field refines its already selected commutative ring. -/
noncomputable def complexes : LeanCategories.Algebra.FieldCat.{0} :=
  ⟨NamedCommutativeRings.complexes, Field.toIsField ℂ⟩

/-- Forgetting the rational field structure retains the existing named carrier. -/
def rationalsIdentification :
    (forget CommRingCat).obj (ring rationals) ≅ NamedRings.rationals := Iso.refl _

/-- Forgetting the real field structure retains the existing named carrier. -/
noncomputable def realsIdentification :
    (forget CommRingCat).obj (ring reals) ≅ NumberSystems.reals := Iso.refl _

/-- Forgetting the complex field structure retains the existing named carrier. -/
noncomputable def complexesIdentification :
    (forget CommRingCat).obj (ring complexes) ≅ NumberSystems.complexes := Iso.refl _

end Algebra.Fields

normalized_registry .classifier
  { id := ClassifierId.commutativeRingsField
    host := Algebra.Catalogue.Rings.CommutativeRings
    declaration := `CasCatalogue.Algebra.Fields.fieldClassifier
    realization := `CasCatalogue.Algebra.Fields.fieldRealization }
normalized_registry .category
  { id := CategoryId.fields, name := "Fields", expression := Algebra.Fields.Fields
    declaration := `CasCatalogue.Algebra.Fields.fieldsCategory
    realization := `CasCatalogue.Algebra.Fields.fieldsRealization }

normalized_registry .object
  { id := ⟨"obj.fields.rationals"⟩, category := CategoryId.fields, name := "ℚ"
    declaration := `CasCatalogue.Algebra.Fields.rationals
    refines := some
      { base := ⟨"obj.sets.rationals"⟩
        route := #[.classifierForget ClassifierId.commutativeRingsField,
          .functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.Fields.rationalsIdentification } }

normalized_registry .object
  { id := ⟨"obj.fields.reals"⟩, category := CategoryId.fields, name := "ℝ"
    declaration := `CasCatalogue.Algebra.Fields.reals
    refines := some
      { base := ⟨"obj.sets.reals"⟩
        route := #[.classifierForget ClassifierId.commutativeRingsField,
          .functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.Fields.realsIdentification } }

normalized_registry .object
  { id := ⟨"obj.fields.complexes"⟩, category := CategoryId.fields, name := "ℂ"
    declaration := `CasCatalogue.Algebra.Fields.complexes
    refines := some
      { base := ⟨"obj.sets.complexes"⟩
        route := #[.classifierForget ClassifierId.commutativeRingsField,
          .functor FunctorId.commutativeRingsRings] ++ ringsToSets
        identification := `CasCatalogue.Algebra.Fields.complexesIdentification } }

end CasCatalogue
