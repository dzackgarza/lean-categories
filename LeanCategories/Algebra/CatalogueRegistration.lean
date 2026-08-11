module

public import LeanCategories.Algebra.Concrete.Magmas
public import LeanCategories.Algebra.Concrete.Rings
public import LeanCategories.Algebra.Catalogue.Magmas
public import LeanCategories.Algebra.Catalogue.Rings
public import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Algebra.Catalogue.Magmas
public meta import LeanCategories.Algebra.Catalogue.Rings
public meta import LeanCategories.Algebra.Catalogue

@[expose] public section

namespace LeanCategories.Algebra.CatalogueRegistration

open LeanCategories

universe u

noncomputable def magmasRealization :
    CategoryRealization Algebra.Catalogue.Magmas.Magmas Algebra.Magmas := ⟨⟩
noncomputable def semigroupsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.Semigroups Algebra.Semigroups := ⟨⟩
noncomputable def monoidsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.Monoids Algebra.Monoids := ⟨⟩
noncomputable def groupsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.Groups Algebra.Groups := ⟨⟩
noncomputable def additiveMagmasRealization :
    CategoryRealization Algebra.Catalogue.Magmas.AdditiveMagmas Algebra.AdditiveMagmas := ⟨⟩
noncomputable def additiveSemigroupsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.AdditiveSemigroups
      Algebra.AdditiveSemigroups := ⟨⟩
noncomputable def additiveMonoidsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.AdditiveMonoids Algebra.AdditiveMonoids := ⟨⟩
noncomputable def additiveGroupsRealization :
    CategoryRealization Algebra.Catalogue.Magmas.AdditiveGroups Algebra.AdditiveGroups := ⟨⟩
noncomputable def ringsRealization :
    CategoryRealization Algebra.Catalogue.Rings.Rings Algebra.Rings := ⟨⟩
noncomputable def commutativeRingsRealization :
    CategoryRealization Algebra.Catalogue.Rings.CommutativeRings
      Algebra.CommutativeRings := ⟨⟩
noncomputable def divisionRingsRealization :
    CategoryRealization Algebra.Catalogue.Rings.DivisionRings Algebra.DivisionRings := ⟨⟩

noncomputable def associativeRealization :
    ClassifierRealization Algebra.Catalogue.Magmas.Magmas ClassifierId.magmasAssociative
      Algebra.Magmas Algebra.associative := ⟨⟩
noncomputable def commutativeRealization :
    ClassifierRealization Algebra.Catalogue.Magmas.Magmas ClassifierId.magmasCommutative
      Algebra.Magmas Algebra.commutative := ⟨⟩
noncomputable def unitalRealization :
    ClassifierRealization Algebra.Catalogue.Magmas.Magmas ClassifierId.magmasUnital
      Algebra.Magmas Algebra.unital := ⟨⟩
noncomputable def inverseRealization :
    ClassifierRealization (.classifierTotal ClassifierId.magmasUnital)
      ClassifierId.magmasInverse Algebra.UnitalMagmas Algebra.inverse := ⟨⟩
noncomputable def additiveRealization :
    ClassifierRealization Algebra.Catalogue.Magmas.Magmas ClassifierId.magmasAdditive
      Algebra.Magmas Algebra.additive := ⟨⟩
noncomputable def multiplicativeRealization :
    ClassifierRealization Algebra.Catalogue.Magmas.Magmas ClassifierId.magmasMultiplicative
      Algebra.Magmas Algebra.multiplicative := ⟨⟩
noncomputable def divisionRealization :
    ClassifierRealization (.atom CategoryId.rings) ClassifierId.ringsDivision
      Algebra.Rings Algebra.divisionOnRings := ⟨⟩

abbrev CRings := Algebra.CommutativeRings

normalized_registry .category
  { id := CategoryId.magmas, canonicalName := "Magmas"
    declaration := `LeanCategories.Algebra.Magmas
    expression := Algebra.Catalogue.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.magmasRealization
    origin := .atomicClassifierTotal, visibility := .present }
normalized_registry .category
  { id := CategoryId.semigroups, canonicalName := "Semigroups"
    declaration := `LeanCategories.Algebra.Semigroups
    expression := Algebra.Catalogue.Magmas.Semigroups
    realization := `LeanCategories.Algebra.CatalogueRegistration.semigroupsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.monoids, canonicalName := "Monoids"
    declaration := `LeanCategories.Algebra.Monoids
    expression := Algebra.Catalogue.Magmas.Monoids
    realization := `LeanCategories.Algebra.CatalogueRegistration.monoidsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.groups, canonicalName := "Groups"
    declaration := `LeanCategories.Algebra.Groups
    expression := Algebra.Catalogue.Magmas.Groups
    realization := `LeanCategories.Algebra.CatalogueRegistration.groupsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.additiveMagmas, canonicalName := "AdditiveMagmas"
    declaration := `LeanCategories.Algebra.AdditiveMagmas
    expression := Algebra.Catalogue.Magmas.AdditiveMagmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.additiveMagmasRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.additiveSemigroups, canonicalName := "AdditiveSemigroups"
    declaration := `LeanCategories.Algebra.AdditiveSemigroups
    expression := Algebra.Catalogue.Magmas.AdditiveSemigroups
    realization := `LeanCategories.Algebra.CatalogueRegistration.additiveSemigroupsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.additiveMonoids, canonicalName := "AdditiveMonoids"
    declaration := `LeanCategories.Algebra.AdditiveMonoids
    expression := Algebra.Catalogue.Magmas.AdditiveMonoids
    realization := `LeanCategories.Algebra.CatalogueRegistration.additiveMonoidsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.additiveGroups, canonicalName := "AdditiveGroups"
    declaration := `LeanCategories.Algebra.AdditiveGroups
    expression := Algebra.Catalogue.Magmas.AdditiveGroups
    realization := `LeanCategories.Algebra.CatalogueRegistration.additiveGroupsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.rings, canonicalName := "Rings"
    declaration := `LeanCategories.Algebra.Rings
    expression := Algebra.Catalogue.Rings.Rings
    realization := `LeanCategories.Algebra.CatalogueRegistration.ringsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.commutativeRings, canonicalName := "CommutativeRings"
    declaration := `LeanCategories.Algebra.CommutativeRings
    expression := Algebra.Catalogue.Rings.CommutativeRings
    realization := `LeanCategories.Algebra.CatalogueRegistration.commutativeRingsRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.divisionRings, canonicalName := "DivisionRings"
    declaration := `LeanCategories.Algebra.DivisionRings
    expression := Algebra.Catalogue.Rings.DivisionRings
    realization := `LeanCategories.Algebra.CatalogueRegistration.divisionRingsRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .classifier
  { id := ClassifierId.magmasAssociative, canonicalName := "Associative"
    declaration := `LeanCategories.Algebra.associative
    host := Algebra.Catalogue.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.associativeRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.magmasCommutative, canonicalName := "Commutative"
    declaration := `LeanCategories.Algebra.commutative
    host := Algebra.Catalogue.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.commutativeRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.magmasUnital, canonicalName := "Unital"
    declaration := `LeanCategories.Algebra.unital
    host := Algebra.Catalogue.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.unitalRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.magmasInverse, canonicalName := "Inverse"
    declaration := `LeanCategories.Algebra.inverse
    host := .classifierTotal ClassifierId.magmasUnital
    realization := `LeanCategories.Algebra.CatalogueRegistration.inverseRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.magmasAdditive, canonicalName := "Additive"
    declaration := `LeanCategories.Algebra.additive
    host := Algebra.Catalogue.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.additiveRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.magmasMultiplicative, canonicalName := "Multiplicative"
    declaration := `LeanCategories.Algebra.multiplicative
    host := Algebra.Catalogue.Magmas.Magmas
    realization := `LeanCategories.Algebra.CatalogueRegistration.multiplicativeRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.ringsDivision, canonicalName := "Division"
    declaration := `LeanCategories.Algebra.divisionOnRings
    host := .atom CategoryId.rings
    realization := `LeanCategories.Algebra.CatalogueRegistration.divisionRealization
    visibility := .present }

normalized_registry .alias
  { id := AliasId.crings, spelling := "CRings"
    aliasOf := CategoryId.commutativeRings
    declaration := `LeanCategories.Algebra.CatalogueRegistration.CRings }

end LeanCategories.Algebra.CatalogueRegistration
