module

public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Modules.Mathlib
public import LeanCategories.Modules.Quadratic.Valued.Catalogue
public import LeanCategories.Modules.Quadratic.Valued.Expressions
public import LeanCategories.Modules.Quadratic.Valued.Fixed
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Modules.Catalogue
public meta import LeanCategories.Modules.Quadratic.Valued.Catalogue
public meta import LeanCategories.Modules.Quadratic.Valued.Expressions

@[expose] public section

namespace LeanCategories.Modules.Quadratic.Valued.CatalogueRegistration

open CategoryTheory
open LeanCategories
open LeanCategories.Modules.Quadratic.Valued.Catalogue

universe u

noncomputable def quadModuleCategory (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] : ObjCat.{u + 1, u} :=
  Cat.of (QuadModuleCat R W)

noncomputable def quadModuleRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization QuadModule (quadModuleCategory R W) := ⟨⟩

noncomputable def quadModuleForgetRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    FunctorRealization QuadModuleForget (quadModuleCategory R W)
      (Modules.Mathlib.ModulesOf (RingCat.of R))
      (LeanCategories.Modules.Quadratic.Valued.forget R W).toCatHom := ⟨⟩

noncomputable def quadModuleForgetDeclaration (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    quadModuleCategory R W ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  (LeanCategories.Modules.Quadratic.Valued.forget R W).toCatHom

normalized_registry .category
  { id := CategoryId.quadModule
    canonicalName := "QuadModuleCat"
    declaration := `LeanCategories.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleCategory
    expression := QuadModule
    realization :=
      `LeanCategories.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleRealization
    origin := .opaqueCategory
    visibility := .present }

normalized_registry .functor
  { id := FunctorId.quadModuleForget
    canonicalName := "QuadModuleCat.forget"
    source := QuadModule
    target := Modules.Modules
    declaration :=
      `LeanCategories.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleForgetDeclaration
    realization :=
      `LeanCategories.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleForgetRealization
    expression := QuadModuleForget
    role := .generatedStructural
    admissibility := .generated
    port := none
    origin := "existing quadratic-module forgetful functor"
    coherenceClass := none
    preferredPresentation := false }

end LeanCategories.Modules.Quadratic.Valued.CatalogueRegistration
