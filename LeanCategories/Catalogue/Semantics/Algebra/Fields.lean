/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Exceptional.CatalogueRegistration
public import Mathlib.Algebra.Field.IsField
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Rings

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

end CasCatalogue
