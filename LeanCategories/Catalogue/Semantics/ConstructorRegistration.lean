/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public import LeanCategories.Catalogue.Constructors
public import LeanCategories.Catalogue.Registry.Semantic
public import LeanCategories.Catalogue.Semantics.Foundation.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Registered typed category constructors and constructed categories (#54 §1, CC-CALC)

Every constructed category below is registered with the expression `.construct c args` and is
checked at registration to be definitionally `c`'s semantics (`Catalogue/Constructors.lean`)
applied to the registered denotations of its arguments. `Subobjects(Sets)` is a constructed
category, not an alias or atom (#54 acceptance).
-/

namespace CasCatalogue.Catalogue.ConstructorRegistration
open LeanCategories

open CategoryTheory LeanCategories CasCatalogue CasCatalogue.Modules.CatalogueRegistration

noncomputable section

universe u v w x

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
    semantics := `CasCatalogue.Constructors.arrow
    functorialAction := some `CasCatalogue.Constructors.arrowMap
    comparisonAction := some `CasCatalogue.Constructors.arrowComparison
    identityComparison := some `CasCatalogue.Constructors.arrowIdentityComparison
    compositionComparison := some `CasCatalogue.Constructors.arrowCompositionComparison }
normalized_registry .constructor
  { id := ConstructorId.core, signature := #[.category],
    semantics := `CasCatalogue.Constructors.core
    functorialAction := some `CasCatalogue.Constructors.coreMap
    comparisonAction := some `CasCatalogue.Constructors.coreComparison
    identityComparison := some `CasCatalogue.Constructors.coreIdentityComparison
    compositionComparison := some `CasCatalogue.Constructors.coreCompositionComparison }
normalized_registry .constructor
  { id := ConstructorId.slice, signature := #[.category, .object],
    semantics := `CasCatalogue.Constructors.slice }
normalized_registry .constructor
  { id := ConstructorId.coslice, signature := #[.category, .object],
    semantics := `CasCatalogue.Constructors.coslice }
normalized_registry .constructor
  { id := ConstructorId.elements, signature := #[.category, .functor],
    semantics := `CasCatalogue.Constructors.elements }
normalized_registry .constructor
  { id := ConstructorId.subobjects, signature := #[.category],
    semantics := `CasCatalogue.Constructors.subobjects }
normalized_registry .constructor
  { id := ConstructorId.functorCategory, signature := #[.category, .category],
    semantics := `CasCatalogue.Constructors.functorCategory }

normalized_registry .category
  { id := CategoryId.arrowsSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.arrowsSetsCategory
    expression := Constructed.ArrowsSets
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.arrowsSetsRealization }
normalized_registry .category
  { id := CategoryId.coreSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.coreSetsCategory
    expression := Constructed.CoreSets
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.coreSetsRealization }
normalized_registry .category
  { id := CategoryId.sliceSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.sliceSetsCategory
    expression := Constructed.SliceSets
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.sliceSetsRealization }
normalized_registry .category
  { id := CategoryId.cosliceSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.cosliceSetsCategory
    expression := Constructed.CosliceSets
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.cosliceSetsRealization }
normalized_registry .category
  { id := CategoryId.subobjectsSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsCategory
    expression := Constructed.SubobjectsSets
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.subobjectsSetsRealization }
normalized_registry .category
  { id := CategoryId.modulePoints,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.modulePointsCategory
    expression := Constructed.ModulePoints
    realization := `CasCatalogue.Catalogue.ConstructorRegistration.modulePointsRealization }
normalized_registry .category
  { id := CategoryId.endofunctorsSets,
    declaration := `CasCatalogue.Catalogue.ConstructorRegistration.endofunctorsSetsCategory
    expression := Constructed.EndofunctorsSets
    realization :=
      `CasCatalogue.Catalogue.ConstructorRegistration.endofunctorsSetsRealization }

normalized_registry .functor
  { id := FunctorId.sliceSetsForget,
    source := Constructed.SliceSets
    target := Foundation.Sets
    declaration :=
      `CasCatalogue.Catalogue.ConstructorRegistration.sliceSetsForgetDeclaration
    realization :=
      `CasCatalogue.Catalogue.ConstructorRegistration.sliceSetsForgetRealization
    expression := Constructed.SliceSetsForgetExpr
    structural := true }
normalized_registry .functor
  { id := FunctorId.modulePointsProjection,
    source := Constructed.ModulePoints
    target := Modules.ModulesTotal
    declaration :=
      `CasCatalogue.Catalogue.ConstructorRegistration.modulePointsProjectionDeclaration
    realization :=
      `CasCatalogue.Catalogue.ConstructorRegistration.modulePointsProjectionRealization
    expression := Constructed.ModulePointsProjectionExpr
    structural := true }

/-! ### Constructor action and endpoint validation

The accepted actions are checked over arbitrary categories and functors. Each malformed row
below has real declarations of the expected broad kind, but different mathematical endpoints.
The checks reject it without consulting constructor names or computational registrations.
-/

/-- A valid restricted action that does not supply the required comparison interface. -/
def arrowAutomorphismOnlyComparison {C : ObjCat.{u, v}} {D : ObjCat.{w, x}} {F : C ⥤ D}
    (α : F ≅ F) : Constructors.arrowMap F ≅ Constructors.arrowMap F :=
  Constructors.arrowComparison α

/-- A valid restricted composition comparison that does not cover different middle categories. -/
def arrowEndofunctorComposition {C : ObjCat.{u, v}} (F G : C ⥤ C) :
    Constructors.arrowMap (F ⋙ G) ≅ Constructors.arrowMap F ⋙ Constructors.arrowMap G :=
  Constructors.arrowCompositionComparison F G

/-- An extra implicit assumption is not part of the published comparison inputs. -/
def arrowConditionalComparison {C : ObjCat.{u, v}} {D : ObjCat.{w, x}} {F G : C ⥤ D}
    {p : Prop} [Fact p] (α : F ≅ G) : Constructors.arrowMap F ≅ Constructors.arrowMap G :=
  Constructors.arrowComparison α

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let arrow : ConstructorEntry := {
      id := ConstructorId.arrow, signature := #[.category]
      semantics := `CasCatalogue.Constructors.arrow
      functorialAction := some `CasCatalogue.Constructors.arrowMap
      comparisonAction := some `CasCatalogue.Constructors.arrowComparison
      identityComparison := some `CasCatalogue.Constructors.arrowIdentityComparison
      compositionComparison := some `CasCatalogue.Constructors.arrowCompositionComparison }
    let core : ConstructorEntry := {
      id := ConstructorId.core, signature := #[.category]
      semantics := `CasCatalogue.Constructors.core
      functorialAction := some `CasCatalogue.Constructors.coreMap
      comparisonAction := some `CasCatalogue.Constructors.coreComparison
      identityComparison := some `CasCatalogue.Constructors.coreIdentityComparison
      compositionComparison := some `CasCatalogue.Constructors.coreCompositionComparison }
    validateConstructor arrow
    validateConstructor core
    let rejects (description : String) (entry : ConstructorEntry) : MetaM Unit := do
      let accepted ← try
        validateConstructor entry
        pure true
      catch _ => pure false
      if accepted then throwError "constructor validation accepted {description}"
    rejects "the core action on arrow categories" { arrow with
      functorialAction := core.functorialAction }
    rejects "the core comparison action on arrow functors" { arrow with
      comparisonAction := core.comparisonAction }
    rejects "the core identity comparison on arrow functors" { arrow with
      identityComparison := core.identityComparison }
    rejects "the core composition comparison on arrow functors" { arrow with
      compositionComparison := core.compositionComparison }
    rejects "an action without its comparison interface" { arrow with
      comparisonAction := none }
    rejects "comparisons without a functor action" { arrow with
      functorialAction := none }
    rejects "a comparison action restricted to automorphisms" { arrow with
      comparisonAction :=
        some `CasCatalogue.Catalogue.ConstructorRegistration.arrowAutomorphismOnlyComparison }
    rejects "a composition action restricted to endofunctors" { arrow with
      compositionComparison :=
        some `CasCatalogue.Catalogue.ConstructorRegistration.arrowEndofunctorComposition }
    rejects "a comparison action with an undeclared condition" { arrow with
      comparisonAction :=
        some `CasCatalogue.Catalogue.ConstructorRegistration.arrowConditionalComparison }

/-! ### Negative probe: a constructed category must be its constructor's semantics -/

noncomputable def coreAsArrows := Constructors.core Foundation.Mathlib.Sets.{0}
noncomputable def coreAsArrowsRealization :
    CategoryRealization Constructed.ArrowsSets coreAsArrows := {}

open Lean Meta Elab Command in
run_cmd
  liftTermElabM do
    let rejects (entry : SemanticEntry) : MetaM Bool := do
      try
        validateSemanticEntryDeclaration entry
        pure false
      catch _ => pure true
    unless ← rejects (.category
        { id := ⟨"cat.probe.core_as_arrows"⟩
          declaration := `CasCatalogue.Catalogue.ConstructorRegistration.coreAsArrows
          expression := Constructed.ArrowsSets
          realization :=
            `CasCatalogue.Catalogue.ConstructorRegistration.coreAsArrowsRealization }) do
      throwError "Core(Sets) was accepted as Arr(Sets)"
    if ← rejects (.category
        { id := CategoryId.arrowsSets
          declaration := `CasCatalogue.Catalogue.ConstructorRegistration.arrowsSetsCategory
          expression := Constructed.ArrowsSets
          realization :=
            `CasCatalogue.Catalogue.ConstructorRegistration.arrowsSetsRealization }) then
      throwError "the canonical Arr(Sets) was rejected"

end CasCatalogue.Catalogue.ConstructorRegistration
