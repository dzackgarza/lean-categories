module

public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Modules.Mathlib
public import LeanCategories.Modules.CatalogueRegistration
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

noncomputable def quadModuleFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ R : CommRingCat.{u}, ModuleCat.{u} R)
    (fun (parameter : Σ R : CommRingCat.{u}, ModuleCat.{u} R) =>
    letI := parameter.1.commRing
    (Cat.of (QuadModuleCat parameter.1 parameter.2) : ObjCat.{u + 1, u}))

noncomputable def quadModuleFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1} CategoryFamilyId.quadModule where
  Parameters := Discrete (Σ R : CommRingCat.{u}, ModuleCat.{u} R)
  transport := quadModuleFamilyTransport

noncomputable def quadModuleCategory (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] : ObjCat.{u + 1, u} :=
  Cat.of (QuadModuleCat R W)

noncomputable def quadModuleRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization QuadModule (quadModuleCategory R W) where
  familyFibre := some {
    identifier := CategoryFamilyId.quadModule
    realization := quadModuleFamilyRealization
    parameter := ⟨CommRingCat.of R, ModuleCat.of R W⟩
    category_eq := by rfl }

noncomputable def quadModuleForgetRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    FunctorRealization QuadModuleForget (quadModuleCategory R W)
      (Modules.Mathlib.ModulesOf (RingCat.of R))
      (LeanCategories.Modules.Quadratic.Valued.forget R W).toCatHom := ⟨⟩

noncomputable def quadModuleForgetDeclaration (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    quadModuleCategory R W ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  (LeanCategories.Modules.Quadratic.Valued.forget R W).toCatHom

normalized_registry .categoryFamily
  { id := CategoryFamilyId.quadModule
    canonicalName := "QuadModuleCat(R, W)"
    parameters := #[{ name := "R", kind := ParameterKindId.commRingObject },
      { name := "W", kind := ParameterKindId.moduleObject }]
    realization :=
      `LeanCategories.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleFamilyRealization
    transport :=
      `LeanCategories.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleFamilyTransport
    variance := VarianceId.discrete }

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
