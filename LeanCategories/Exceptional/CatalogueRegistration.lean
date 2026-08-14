module

public import LeanCategories.Algebra.Catalogue.Rings
public import LeanCategories.Algebra.CatalogueRegistration
public import LeanCategories.Foundation.CatalogueRegistration
public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Exceptional.Mathlib
public import LeanCategories.Foundation.Expressions
public import LeanCategories.Exceptional.Catalogue
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Exceptional.Catalogue
public meta import LeanCategories.Algebra.Catalogue.Rings
public meta import LeanCategories.Algebra.CatalogueRegistration
public meta import LeanCategories.Foundation.CatalogueRegistration

@[expose] public section

namespace LeanCategories.Exceptional.CatalogueRegistration

open LeanCategories

universe u

def CrystalsExpr : CategoryExpr := .opaque CategoryId.crystals

noncomputable def m2oRealization :
    CategoryRealization Algebra.Catalogue.Rings.MagmasWithTwoOperations
      Exceptional.Mathlib.MagmasWithTwoOperations := { familyFibre := none }
noncomputable def crystalsRealization :
    CategoryRealization CrystalsExpr Exceptional.Mathlib.Crystals :=
  { familyFibre := none }
noncomputable def distributiveRealization :
    ClassifierRealization Algebra.Catalogue.Rings.MagmasWithTwoOperations
      ClassifierId.m2oDistributive Exceptional.Mathlib.MagmasWithTwoOperations
      Exceptional.Mathlib.distributive :=
  { hostRealization := m2oRealization
    totalRealization := { familyFibre := none } }

def multiplicativePortId : OpaquePortId := ⟨"oport.m2o.multiplicative"⟩
def additivePortId : OpaquePortId := ⟨"oport.m2o.additive"⟩
def crystalsPortId : OpaquePortId := ⟨"oport.crystals.sets"⟩

def multiplicativePortExpr :
    FunctorExpr Algebra.Catalogue.Rings.MagmasWithTwoOperations
      Algebra.Catalogue.Magmas.Magmas := .opaquePort multiplicativePortId
noncomputable def multiplicativePortRealization :
    FunctorRealization multiplicativePortExpr Exceptional.Mathlib.MagmasWithTwoOperations
      Algebra.Magmas Exceptional.Mathlib.multiplicativePort where
  sourceRealization := m2oRealization
  targetRealization := LeanCategories.Algebra.CatalogueRegistration.magmasRealization

def additivePortExpr :
    FunctorExpr Algebra.Catalogue.Rings.MagmasWithTwoOperations
      Algebra.Catalogue.Magmas.Magmas := .opaquePort additivePortId
noncomputable def additivePortRealization :
    FunctorRealization additivePortExpr Exceptional.Mathlib.MagmasWithTwoOperations
      Algebra.Magmas Exceptional.Mathlib.additivePort where
  sourceRealization := m2oRealization
  targetRealization := LeanCategories.Algebra.CatalogueRegistration.magmasRealization

def crystalsPortExpr : FunctorExpr CrystalsExpr Foundation.Sets := .opaquePort crystalsPortId
noncomputable def crystalsPortRealization :
    FunctorRealization crystalsPortExpr Exceptional.Mathlib.Crystals Foundation.Mathlib.Sets
      Exceptional.Mathlib.crystalsToSets where
  sourceRealization := crystalsRealization
  targetRealization := LeanCategories.Foundation.CatalogueRegistration.setsRealization

normalized_registry .category
  { id := CategoryId.magmasWithTwoOperations
    canonicalName := "MagmasWithTwoOperations"
    declaration := `LeanCategories.Exceptional.Mathlib.MagmasWithTwoOperations
    expression := Algebra.Catalogue.Rings.MagmasWithTwoOperations
    realization := `LeanCategories.Exceptional.CatalogueRegistration.m2oRealization}
normalized_registry .category
  { id := CategoryId.crystals, canonicalName := "Crystals"
    declaration := `LeanCategories.Exceptional.Mathlib.Crystals
    expression := CrystalsExpr
    realization := `LeanCategories.Exceptional.CatalogueRegistration.crystalsRealization}

normalized_registry .classifier
  { id := ClassifierId.m2oDistributive, canonicalName := "Distributive"
    declaration := `LeanCategories.Exceptional.Mathlib.distributive
    host := Algebra.Catalogue.Rings.MagmasWithTwoOperations
    realization := `LeanCategories.Exceptional.CatalogueRegistration.distributiveRealization}

normalized_registry .opaque
  { id := CategoryId.magmasWithTwoOperations
    declaration := `LeanCategories.Exceptional.Mathlib.MagmasWithTwoOperations
    realization := `LeanCategories.Exceptional.CatalogueRegistration.m2oRealization
    ports := #[
      { id := multiplicativePortId
        source := Algebra.Catalogue.Rings.MagmasWithTwoOperations
        target := Algebra.Catalogue.Magmas.Magmas
        declaration := `LeanCategories.Exceptional.Mathlib.multiplicativePort
        realization := `LeanCategories.Exceptional.CatalogueRegistration.multiplicativePortRealization
        provenance := "authored opaque interface" },
      { id := additivePortId
        source := Algebra.Catalogue.Rings.MagmasWithTwoOperations
        target := Algebra.Catalogue.Magmas.Magmas
        declaration := `LeanCategories.Exceptional.Mathlib.additivePort
        realization := `LeanCategories.Exceptional.CatalogueRegistration.additivePortRealization
        provenance := "authored opaque interface" }]
    reason := "two-operation host; distributivity is a separate classifier"}

normalized_registry .opaque
  { id := CategoryId.crystals
    declaration := `LeanCategories.Exceptional.Mathlib.Crystals
    realization := `LeanCategories.Exceptional.CatalogueRegistration.crystalsRealization
    ports := #[
      { id := crystalsPortId
        source := CrystalsExpr, target := Foundation.Sets
        declaration := `LeanCategories.Exceptional.Mathlib.crystalsToSets
        realization := `LeanCategories.Exceptional.CatalogueRegistration.crystalsPortRealization
        provenance := "authored opaque interface" }]
    reason := "exceptional combinatorial host"}

normalized_registry .category
  { id := CategoryId.rings, canonicalName := "Rings"
    declaration := `LeanCategories.Algebra.Rings
    expression := Algebra.Catalogue.Rings.Rings
    realization := `LeanCategories.Algebra.CatalogueRegistration.ringsRealization}
normalized_registry .category
  { id := CategoryId.commutativeRings, canonicalName := "CommutativeRings"
    declaration := `LeanCategories.Algebra.CommutativeRings
    expression := Algebra.Catalogue.Rings.CommutativeRings
    realization := `LeanCategories.Algebra.CatalogueRegistration.commutativeRingsRealization}
normalized_registry .classifier
  { id := ClassifierId.ringsDivision, canonicalName := "Division"
    declaration := `LeanCategories.Algebra.divisionOnRings
    host := Algebra.Catalogue.Rings.Rings
    realization := `LeanCategories.Algebra.CatalogueRegistration.divisionRealization}
normalized_registry .category
  { id := CategoryId.divisionRings, canonicalName := "DivisionRings"
    declaration := `LeanCategories.Algebra.DivisionRings
    expression := Algebra.Catalogue.Rings.DivisionRings
    realization := `LeanCategories.Algebra.CatalogueRegistration.divisionRingsRealization}
normalized_registry .alias
  { id := AliasId.crings, spelling := "CRings"
    aliasOf := CategoryId.commutativeRings
    declaration := `LeanCategories.Algebra.CatalogueRegistration.CRings
    realization := `LeanCategories.Algebra.CatalogueRegistration.commutativeRingsRealization }

end LeanCategories.Exceptional.CatalogueRegistration
