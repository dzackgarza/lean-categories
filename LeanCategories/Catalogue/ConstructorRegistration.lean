/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.ConstructorCatalogue
public import LeanCategories.Catalogue.Constructors
public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Foundation.CatalogueRegistration
public import LeanCategories.Modules.CatalogueRegistration
public meta import LeanCategories.Catalogue.ConstructorCatalogue
public meta import LeanCategories.Catalogue.Registry.Extension

@[expose] public section

/-!
# Registered typed category constructors and constructed categories (#54 §1, CC-CALC)

Every constructed category below is registered with the expression `.construct c args` and is
checked at registration to be definitionally `c`'s semantics (`Catalogue/Constructors.lean`)
applied to the registered denotations of its arguments. `Subobjects(Sets)` is a constructed
category, not an alias or atom (#54 acceptance).
-/

namespace LeanCategories.Catalogue.ConstructorRegistration

open CategoryTheory LeanCategories LeanCategories.Modules.CatalogueRegistration

noncomputable section

universe u

def arrowsSetsCategory := Constructors.arrow Foundation.Mathlib.Sets.{u}
def arrowsSetsRealization :
    CategoryRealization Constructed.ArrowsSets arrowsSetsCategory.{u} := {}

def coreSetsCategory := Constructors.core Foundation.Mathlib.Sets.{u}
def coreSetsRealization : CategoryRealization Constructed.CoreSets coreSetsCategory.{u} := {}

def sliceSetsCategory (X : Type u) := Constructors.slice Foundation.Mathlib.Sets.{u} X
def sliceSetsRealization (X : Type u) :
    CategoryRealization Constructed.SliceSets (sliceSetsCategory X) := {}

def cosliceSetsCategory (X : Type u) := Constructors.coslice Foundation.Mathlib.Sets.{u} X
def cosliceSetsRealization (X : Type u) :
    CategoryRealization Constructed.CosliceSets (cosliceSetsCategory X) := {}

def subobjectsSetsCategory := Constructors.subobjects Foundation.Mathlib.Sets.{u}
def subobjectsSetsRealization :
    CategoryRealization Constructed.SubobjectsSets subobjectsSetsCategory.{u} := {}

def modulePointsCategory :=
  Constructors.elements modulesTotalCategory.{u, u} modulesUnderlyingDeclaration.{u, u}
def modulePointsRealization :
    CategoryRealization Constructed.ModulePoints modulePointsCategory.{u} := {}

def endofunctorsSetsCategory :=
  Constructors.functorCategory Foundation.Mathlib.Sets.{u} Foundation.Mathlib.Sets.{u}
def endofunctorsSetsRealization :
    CategoryRealization Constructed.EndofunctorsSets endofunctorsSetsCategory.{u} := {}

/-- The forgetful functor `Over X ⥤ Sets`. -/
def sliceSetsForgetDeclaration (X : Type u) :
    sliceSetsCategory X ⥤ Foundation.Mathlib.Sets.{u} :=
  Over.forget X
def sliceSetsForgetRealization (X : Type u) :
    FunctorRealization Constructed.SliceSetsForgetExpr (sliceSetsCategory X)
      Foundation.Mathlib.Sets.{u} (sliceSetsForgetDeclaration X) :=
  { sourceRealization := sliceSetsRealization X
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

/-- The projection of the points of modules to the modules: `CategoryOfElements.π U`. -/
def modulePointsProjectionDeclaration :
    modulePointsCategory.{u} ⥤ modulesTotalCategory.{u, u} :=
  CategoryOfElements.π _
def modulePointsProjectionRealization :
    FunctorRealization Constructed.ModulePointsProjectionExpr modulePointsCategory.{u}
      modulesTotalCategory.{u, u} modulePointsProjectionDeclaration :=
  { sourceRealization := modulePointsRealization
    targetRealization := modulesTotalRealization }

end

normalized_registry .constructor
  { id := ConstructorId.arrow, signature := #[.category],
    semantics := `LeanCategories.Constructors.arrow }
normalized_registry .constructor
  { id := ConstructorId.core, signature := #[.category],
    semantics := `LeanCategories.Constructors.core }
normalized_registry .constructor
  { id := ConstructorId.slice, signature := #[.category, .object],
    semantics := `LeanCategories.Constructors.slice }
normalized_registry .constructor
  { id := ConstructorId.coslice, signature := #[.category, .object],
    semantics := `LeanCategories.Constructors.coslice }
normalized_registry .constructor
  { id := ConstructorId.elements, signature := #[.category, .functor],
    semantics := `LeanCategories.Constructors.elements }
normalized_registry .constructor
  { id := ConstructorId.subobjects, signature := #[.category],
    semantics := `LeanCategories.Constructors.subobjects }
normalized_registry .constructor
  { id := ConstructorId.functorCategory, signature := #[.category, .category],
    semantics := `LeanCategories.Constructors.functorCategory }

normalized_registry .category
  { id := CategoryId.arrowsSets,
    declaration := `LeanCategories.Catalogue.ConstructorRegistration.arrowsSetsCategory
    expression := Constructed.ArrowsSets
    realization := `LeanCategories.Catalogue.ConstructorRegistration.arrowsSetsRealization }
normalized_registry .category
  { id := CategoryId.coreSets,
    declaration := `LeanCategories.Catalogue.ConstructorRegistration.coreSetsCategory
    expression := Constructed.CoreSets
    realization := `LeanCategories.Catalogue.ConstructorRegistration.coreSetsRealization }
normalized_registry .category
  { id := CategoryId.sliceSets,
    declaration := `LeanCategories.Catalogue.ConstructorRegistration.sliceSetsCategory
    expression := Constructed.SliceSets
    realization := `LeanCategories.Catalogue.ConstructorRegistration.sliceSetsRealization }
normalized_registry .category
  { id := CategoryId.cosliceSets,
    declaration := `LeanCategories.Catalogue.ConstructorRegistration.cosliceSetsCategory
    expression := Constructed.CosliceSets
    realization := `LeanCategories.Catalogue.ConstructorRegistration.cosliceSetsRealization }
normalized_registry .category
  { id := CategoryId.subobjectsSets,
    declaration := `LeanCategories.Catalogue.ConstructorRegistration.subobjectsSetsCategory
    expression := Constructed.SubobjectsSets
    realization := `LeanCategories.Catalogue.ConstructorRegistration.subobjectsSetsRealization }
normalized_registry .category
  { id := CategoryId.modulePoints,
    declaration := `LeanCategories.Catalogue.ConstructorRegistration.modulePointsCategory
    expression := Constructed.ModulePoints
    realization := `LeanCategories.Catalogue.ConstructorRegistration.modulePointsRealization }
normalized_registry .category
  { id := CategoryId.endofunctorsSets,
    declaration := `LeanCategories.Catalogue.ConstructorRegistration.endofunctorsSetsCategory
    expression := Constructed.EndofunctorsSets
    realization :=
      `LeanCategories.Catalogue.ConstructorRegistration.endofunctorsSetsRealization }

normalized_registry .functor
  { id := FunctorId.sliceSetsForget,
    source := Constructed.SliceSets
    target := Foundation.Sets
    declaration :=
      `LeanCategories.Catalogue.ConstructorRegistration.sliceSetsForgetDeclaration
    realization :=
      `LeanCategories.Catalogue.ConstructorRegistration.sliceSetsForgetRealization
    expression := Constructed.SliceSetsForgetExpr }
normalized_registry .functor
  { id := FunctorId.modulePointsProjection,
    source := Constructed.ModulePoints
    target := Modules.ModulesTotal
    declaration :=
      `LeanCategories.Catalogue.ConstructorRegistration.modulePointsProjectionDeclaration
    realization :=
      `LeanCategories.Catalogue.ConstructorRegistration.modulePointsProjectionRealization
    expression := Constructed.ModulePointsProjectionExpr }

/-! ### Negative probe: a constructed category must be its constructor's semantics -/

noncomputable def coreAsArrows := Constructors.core Foundation.Mathlib.Sets.{0}
noncomputable def coreAsArrowsRealization :
    CategoryRealization Constructed.ArrowsSets coreAsArrows := {}

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let rejects (entry : RegistryEntry) : MetaM Bool := do
      try
        validateRegistryEntryDeclaration entry
        pure false
      catch _ => pure true
    unless ← rejects (.category
        { id := ⟨"cat.probe.core_as_arrows"⟩
          declaration := `LeanCategories.Catalogue.ConstructorRegistration.coreAsArrows
          expression := Constructed.ArrowsSets
          realization :=
            `LeanCategories.Catalogue.ConstructorRegistration.coreAsArrowsRealization }) do
      throwError "Core(Sets) was accepted as Arr(Sets)"
    if ← rejects (.category
        { id := CategoryId.arrowsSets
          declaration := `LeanCategories.Catalogue.ConstructorRegistration.arrowsSetsCategory
          expression := Constructed.ArrowsSets
          realization :=
            `LeanCategories.Catalogue.ConstructorRegistration.arrowsSetsRealization }) then
      throwError "the canonical Arr(Sets) was rejected"

end LeanCategories.Catalogue.ConstructorRegistration
