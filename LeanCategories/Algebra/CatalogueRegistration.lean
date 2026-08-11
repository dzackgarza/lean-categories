module

public import LeanCategories.Algebra.Mathlib
public import LeanCategories.Algebra.Magmas
public import LeanCategories.Algebra.Rings
public import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Algebra.Magmas
public meta import LeanCategories.Algebra.Rings
public meta import LeanCategories.Algebra.Catalogue

@[expose] public section

namespace LeanCategories.Algebra.CatalogueRegistration

open LeanCategories

universe u

noncomputable def magmasRealization :
    CategoryRealization Algebra.Magmas.Magmas Algebra.Mathlib.Magmas := ⟨⟩
noncomputable def semigroupsRealization :
    CategoryRealization Algebra.Magmas.Semigroups Algebra.Mathlib.Semigroups := ⟨⟩
noncomputable def monoidsRealization :
    CategoryRealization Algebra.Magmas.Monoids Algebra.Mathlib.Monoids := ⟨⟩
noncomputable def groupsRealization :
    CategoryRealization Algebra.Magmas.Groups Algebra.Mathlib.Groups := ⟨⟩
noncomputable def additiveMagmasRealization :
    CategoryRealization Algebra.Magmas.AdditiveMagmas Algebra.Mathlib.AdditiveMagmas := ⟨⟩
noncomputable def additiveSemigroupsRealization :
    CategoryRealization Algebra.Magmas.AdditiveSemigroups
      Algebra.Mathlib.AdditiveSemigroups := ⟨⟩
noncomputable def additiveMonoidsRealization :
    CategoryRealization Algebra.Magmas.AdditiveMonoids Algebra.Mathlib.AdditiveMonoids := ⟨⟩
noncomputable def additiveGroupsRealization :
    CategoryRealization Algebra.Magmas.AdditiveGroups Algebra.Mathlib.AdditiveGroups := ⟨⟩
noncomputable def ringsRealization :
    CategoryRealization Algebra.Rings.Rings Algebra.Mathlib.Rings := ⟨⟩
noncomputable def commutativeRingsRealization :
    CategoryRealization Algebra.Rings.CommutativeRings
      Algebra.Mathlib.CommutativeRings := ⟨⟩
noncomputable def divisionRingsRealization :
    CategoryRealization Algebra.Rings.DivisionRings Algebra.Mathlib.DivisionRings := ⟨⟩

noncomputable def associativeRealization :
    ClassifierRealization Algebra.Magmas.Magmas ClassifierId.magmasAssociative
      Algebra.Mathlib.Magmas Algebra.Mathlib.associative := ⟨⟩
noncomputable def commutativeRealization :
    ClassifierRealization Algebra.Magmas.Magmas ClassifierId.magmasCommutative
      Algebra.Mathlib.Magmas Algebra.Mathlib.commutative := ⟨⟩
noncomputable def unitalRealization :
    ClassifierRealization Algebra.Magmas.Magmas ClassifierId.magmasUnital
      Algebra.Mathlib.Magmas Algebra.Mathlib.unital := ⟨⟩
noncomputable def inverseRealization :
    ClassifierRealization (.classifierTotal ClassifierId.magmasUnital)
      ClassifierId.magmasInverse Algebra.Mathlib.UnitalMagmas Algebra.Mathlib.inverse := ⟨⟩
noncomputable def additiveRealization :
    ClassifierRealization Algebra.Magmas.Magmas ClassifierId.magmasAdditive
      Algebra.Mathlib.Magmas Algebra.Mathlib.additive := ⟨⟩
noncomputable def multiplicativeRealization :
    ClassifierRealization Algebra.Magmas.Magmas ClassifierId.magmasMultiplicative
      Algebra.Mathlib.Magmas Algebra.Mathlib.multiplicative := ⟨⟩
noncomputable def divisionRealization :
    ClassifierRealization (.atom CategoryId.rings) ClassifierId.ringsDivision
      Algebra.Mathlib.Rings Algebra.Mathlib.divisionOnRings := ⟨⟩

abbrev CRings := Algebra.Mathlib.CommutativeRings

normalized_registry .category
  { id := CategoryId.magmas, canonicalName := "Magmas"
    declaration := `LeanCategories.Algebra.Mathlib.Magmas
    expression := Algebra.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.magmasRealization
    origin := .atomicClassifierTotal, visibility := .present }
normalized_registry .category
  { id := CategoryId.semigroups, canonicalName := "Semigroups"
    declaration := `LeanCategories.Algebra.Mathlib.Semigroups
    expression := Algebra.Magmas.Semigroups
    realization := `LeanCategories.Algebra.CatalogueRegistration.semigroupsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.monoids, canonicalName := "Monoids"
    declaration := `LeanCategories.Algebra.Mathlib.Monoids
    expression := Algebra.Magmas.Monoids
    realization := `LeanCategories.Algebra.CatalogueRegistration.monoidsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.groups, canonicalName := "Groups"
    declaration := `LeanCategories.Algebra.Mathlib.Groups
    expression := Algebra.Magmas.Groups
    realization := `LeanCategories.Algebra.CatalogueRegistration.groupsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.additiveMagmas, canonicalName := "AdditiveMagmas"
    declaration := `LeanCategories.Algebra.Mathlib.AdditiveMagmas
    expression := Algebra.Magmas.AdditiveMagmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.additiveMagmasRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.additiveSemigroups, canonicalName := "AdditiveSemigroups"
    declaration := `LeanCategories.Algebra.Mathlib.AdditiveSemigroups
    expression := Algebra.Magmas.AdditiveSemigroups
    realization := `LeanCategories.Algebra.CatalogueRegistration.additiveSemigroupsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.additiveMonoids, canonicalName := "AdditiveMonoids"
    declaration := `LeanCategories.Algebra.Mathlib.AdditiveMonoids
    expression := Algebra.Magmas.AdditiveMonoids
    realization := `LeanCategories.Algebra.CatalogueRegistration.additiveMonoidsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.additiveGroups, canonicalName := "AdditiveGroups"
    declaration := `LeanCategories.Algebra.Mathlib.AdditiveGroups
    expression := Algebra.Magmas.AdditiveGroups
    realization := `LeanCategories.Algebra.CatalogueRegistration.additiveGroupsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.rings, canonicalName := "Rings"
    declaration := `LeanCategories.Algebra.Mathlib.Rings
    expression := Algebra.Rings.Rings
    realization := `LeanCategories.Algebra.CatalogueRegistration.ringsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.commutativeRings, canonicalName := "CommutativeRings"
    declaration := `LeanCategories.Algebra.Mathlib.CommutativeRings
    expression := Algebra.Rings.CommutativeRings
    realization := `LeanCategories.Algebra.CatalogueRegistration.commutativeRingsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.divisionRings, canonicalName := "DivisionRings"
    declaration := `LeanCategories.Algebra.Mathlib.DivisionRings
    expression := Algebra.Rings.DivisionRings
    realization := `LeanCategories.Algebra.CatalogueRegistration.divisionRingsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasAssociative, canonicalName := "Associative"
    declaration := `LeanCategories.Algebra.Mathlib.associative
    host := Algebra.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.associativeRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.magmasCommutative, canonicalName := "Commutative"
    declaration := `LeanCategories.Algebra.Mathlib.commutative
    host := Algebra.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.commutativeRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.magmasUnital, canonicalName := "Unital"
    declaration := `LeanCategories.Algebra.Mathlib.unital
    host := Algebra.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.unitalRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.magmasInverse, canonicalName := "Inverse"
    declaration := `LeanCategories.Algebra.Mathlib.inverse
    host := .classifierTotal ClassifierId.magmasUnital
    realization := `LeanCategories.Algebra.CatalogueRegistration.inverseRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.magmasAdditive, canonicalName := "Additive"
    declaration := `LeanCategories.Algebra.Mathlib.additive
    host := Algebra.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.additiveRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.magmasMultiplicative, canonicalName := "Multiplicative"
    declaration := `LeanCategories.Algebra.Mathlib.multiplicative
    host := Algebra.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.multiplicativeRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.ringsDivision, canonicalName := "Division"
    declaration := `LeanCategories.Algebra.Mathlib.divisionOnRings
    host := .atom CategoryId.rings
    realization := `LeanCategories.Algebra.CatalogueRegistration.divisionRealization
    visibility := .present }

normalized_registry .alias
  { id := AliasId.crings, spelling := "CRings"
    aliasOf := CategoryId.commutativeRings
    declaration := `LeanCategories.Algebra.CatalogueRegistration.CRings }

end LeanCategories.Algebra.CatalogueRegistration
