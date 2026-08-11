module

public import LeanCategories.Algebra.Catalogue.Rings
public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Exceptional.Mathlib
public import LeanCategories.Foundation.Expressions
public import LeanCategories.Exceptional.Catalogue
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Exceptional.Catalogue
public meta import LeanCategories.Algebra.Catalogue.Rings

@[expose] public section

namespace LeanCategories.Exceptional.CatalogueRegistration

open LeanCategories

universe u

def CrystalsExpr : CategoryExpr := .opaque CategoryId.crystals

noncomputable def m2oRealization :
    CategoryRealization Algebra.Catalogue.Rings.MagmasWithTwoOperations
      Exceptional.Mathlib.MagmasWithTwoOperations := ⟨⟩
noncomputable def crystalsRealization :
    CategoryRealization CrystalsExpr Exceptional.Mathlib.Crystals := ⟨⟩
noncomputable def distributiveRealization :
    ClassifierRealization Algebra.Catalogue.Rings.MagmasWithTwoOperations
      ClassifierId.m2oDistributive Exceptional.Mathlib.MagmasWithTwoOperations
      Exceptional.Mathlib.distributive := ⟨⟩

normalized_registry .category
  { id := CategoryId.magmasWithTwoOperations
    canonicalName := "MagmasWithTwoOperations"
    declaration := `LeanCategories.Exceptional.Mathlib.MagmasWithTwoOperations
    expression := Algebra.Catalogue.Rings.MagmasWithTwoOperations
    realization := `LeanCategories.Exceptional.CatalogueRegistration.m2oRealization
    origin := .opaqueCategory, visibility := .semanticOnly }
normalized_registry .category
  { id := CategoryId.crystals, canonicalName := "Crystals"
    declaration := `LeanCategories.Exceptional.Mathlib.Crystals
    expression := CrystalsExpr
    realization := `LeanCategories.Exceptional.CatalogueRegistration.crystalsRealization
    origin := .opaqueCategory, visibility := .semanticOnly }

normalized_registry .classifier
  { id := ClassifierId.m2oDistributive, canonicalName := "Distributive"
    declaration := `LeanCategories.Exceptional.Mathlib.distributive
    host := Algebra.Catalogue.Rings.MagmasWithTwoOperations
    realization := `LeanCategories.Exceptional.CatalogueRegistration.distributiveRealization
    visibility := .present }

normalized_registry .opaque
  { id := CategoryId.magmasWithTwoOperations
    declaration := `LeanCategories.Exceptional.Mathlib.MagmasWithTwoOperations
    ports := #[
      { id := ⟨"oport.m2o.multiplicative"⟩
        source := CategoryId.magmasWithTwoOperations, target := CategoryId.magmas
        role := PortId.multiplicative
        declaration := `LeanCategories.Exceptional.Mathlib.multiplicativePort
        provenance := "authored opaque interface" },
      { id := ⟨"oport.m2o.additive"⟩
        source := CategoryId.magmasWithTwoOperations, target := CategoryId.magmas
        role := PortId.additive
        declaration := `LeanCategories.Exceptional.Mathlib.additivePort
        provenance := "authored opaque interface" }]
    reason := "two-operation host; distributivity is a separate classifier"
    visibility := .semanticOnly }

normalized_registry .opaque
  { id := CategoryId.crystals
    declaration := `LeanCategories.Exceptional.Mathlib.Crystals
    ports := #[
      { id := ⟨"oport.crystals.sets"⟩
        source := CategoryId.crystals, target := CategoryId.sets
        role := PortId.underlyingSet
        declaration := `LeanCategories.Exceptional.Mathlib.crystalsToSets
        provenance := "authored opaque interface" }]
    reason := "exceptional combinatorial host"
    visibility := .semanticOnly }

end LeanCategories.Exceptional.CatalogueRegistration
