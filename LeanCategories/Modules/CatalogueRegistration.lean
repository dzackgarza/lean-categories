module

public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Modules.Expressions
public import LeanCategories.Modules.Mathlib
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Modules.Expressions
public meta import LeanCategories.Modules.Catalogue

@[expose] public section

namespace LeanCategories.Modules.CatalogueRegistration

open LeanCategories

universe u

noncomputable def modulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.Modules (Modules.Mathlib.ModulesOf R) := ⟨⟩
noncomputable def freeModulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.FreeModules (Modules.Mathlib.free R).total := ⟨⟩
noncomputable def finitelyGeneratedModulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.FinitelyGeneratedModules
      (Modules.Mathlib.finitelyGenerated R).total := ⟨⟩
noncomputable def finiteRankModulesRealization (R : RingCat.{u}) :
    CategoryRealization Modules.FiniteRankModules
      (Modules.Mathlib.finiteRank R).total := ⟨⟩

noncomputable def modulesFamilyRealization :
    CategoryFamilyRealization CategoryFamilyId.modules where
  Parameters := RingCat.{u}
  fibre := Modules.Mathlib.ModulesOf

noncomputable def freeRealization (R : RingCat.{u}) :
    ClassifierRealization Modules.Modules ClassifierId.modulesFree
      (Modules.Mathlib.ModulesOf R) (Modules.Mathlib.free R) := ⟨⟩
noncomputable def finitelyGeneratedRealization (R : RingCat.{u}) :
    ClassifierRealization Modules.Modules ClassifierId.modulesFinitelyGenerated
      (Modules.Mathlib.ModulesOf R) (Modules.Mathlib.finitelyGenerated R) := ⟨⟩
noncomputable def finiteRankRealization (R : RingCat.{u}) :
    ClassifierRealization Modules.Modules ClassifierId.modulesFiniteRank
      (Modules.Mathlib.ModulesOf R) (Modules.Mathlib.finiteRank R) := ⟨⟩

normalized_registry .category
  { id := CategoryId.modulesR, canonicalName := "Modules(R)"
    declaration := `LeanCategories.Modules.Mathlib.ModulesOf
    expression := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.modulesRealization
    origin := .root, visibility := .present }
normalized_registry .category
  { id := CategoryId.freeModules, canonicalName := "FreeModules(R)"
    declaration := `LeanCategories.Modules.Mathlib.FreeModules
    expression := Modules.FreeModules
    realization := `LeanCategories.Modules.CatalogueRegistration.freeModulesRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.finitelyGeneratedModules
    canonicalName := "FinitelyGeneratedModules(R)"
    declaration := `LeanCategories.Modules.Mathlib.FinitelyGeneratedModules
    expression := Modules.FinitelyGeneratedModules
    realization := `LeanCategories.Modules.CatalogueRegistration.finitelyGeneratedModulesRealization
    origin := .derivedNamed, visibility := .present }
normalized_registry .category
  { id := CategoryId.finiteRankModules, canonicalName := "FiniteRankModules(R)"
    declaration := `LeanCategories.Modules.Mathlib.FiniteRankModules
    expression := Modules.FiniteRankModules
    realization := `LeanCategories.Modules.CatalogueRegistration.finiteRankModulesRealization
    origin := .derivedNamed, visibility := .present }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.modules, canonicalName := "Modules(R)"
    parameters := #[{ name := "R", kind := ParameterKindId.ringObject }]
    realization := `LeanCategories.Modules.CatalogueRegistration.modulesFamilyRealization
    variance := VarianceId.restrictionOfScalarsContravariant }

normalized_registry .classifier
  { id := ClassifierId.modulesFree, canonicalName := "Free"
    declaration := `LeanCategories.Modules.Mathlib.free
    host := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.freeRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.modulesFinitelyGenerated, canonicalName := "FinitelyGenerated"
    declaration := `LeanCategories.Modules.Mathlib.finitelyGenerated
    host := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.finitelyGeneratedRealization
    visibility := .present }
normalized_registry .classifier
  { id := ClassifierId.modulesFiniteRank, canonicalName := "FiniteRank"
    declaration := `LeanCategories.Modules.Mathlib.finiteRank
    host := Modules.Modules
    realization := `LeanCategories.Modules.CatalogueRegistration.finiteRankRealization
    visibility := .present }

end LeanCategories.Modules.CatalogueRegistration
