module

public import LeanCategories.Foundation.CatalogueRegistration
public import LeanCategories.Algebra.CatalogueRegistration
public import LeanCategories.Modules.CatalogueRegistration
public import LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration
public import LeanCategories.Modules.Quadratic.Valued.CatalogueRegistration
public import LeanCategories.Lattices.Valued.CatalogueRegistration
public import LeanCategories.Exceptional.CatalogueRegistration

@[expose] public section

namespace LeanCategories.Catalogue.Standard

open LeanCategories

/-- Stable category rows owned by the standard catalogue. -/
def expectedCategoryIds : Array CategoryId := #[
  CategoryId.additiveGroups,
  CategoryId.additiveMagmas,
  CategoryId.additiveMonoids,
  CategoryId.additiveSemigroups,
  CategoryId.bilWForm,
  CategoryId.bilinModule,
  CategoryId.commutativeRings,
  CategoryId.crystals,
  CategoryId.definiteLattice,
  CategoryId.divisionRings,
  CategoryId.evenLattice,
  CategoryId.finiteFreeLattice,
  CategoryId.finiteProjectiveLattice,
  CategoryId.finitelyGeneratedModules,
  CategoryId.finiteRankModules,
  CategoryId.freeModules,
  CategoryId.groups,
  CategoryId.indefiniteLattice,
  CategoryId.lattice,
  CategoryId.magmas,
  CategoryId.magmasWithTwoOperations,
  CategoryId.modulesR,
  CategoryId.monoids,
  CategoryId.quadModule,
  CategoryId.quadWForm,
  CategoryId.rings,
  CategoryId.semigroups,
  CategoryId.sets]

/-- Stable category-family rows owned by the standard catalogue. -/
def expectedCategoryFamilyIds : Array CategoryFamilyId := #[
  CategoryFamilyId.bilWForm,
  CategoryFamilyId.bilinModule,
  CategoryFamilyId.evenLattice,
  CategoryFamilyId.finiteFreeLattice,
  CategoryFamilyId.finiteProjectiveLattice,
  CategoryFamilyId.lattice,
  CategoryFamilyId.modules,
  CategoryFamilyId.quadModule,
  CategoryFamilyId.quadWForm]

/-- Stable classifier rows owned by the standard catalogue. -/
def expectedClassifierIds : Array ClassifierId := #[
  ClassifierId.ringsDivision,
  ClassifierId.magmasAdditive,
  ClassifierId.magmasAssociative,
  ClassifierId.magmasCommutative,
  ClassifierId.magmasInverse,
  ClassifierId.magmasMultiplicative,
  ClassifierId.magmasUnital,
  ClassifierId.m2oDistributive,
  ClassifierId.modulesFinitelyGenerated,
  ClassifierId.modulesFiniteRank,
  ClassifierId.modulesFree,
  ClassifierId.setsBinaryOperation,
  ClassifierId.setsFinite,
  ClassifierId.setsGraded]

/-- Stable functor rows owned by the standard catalogue. -/
def expectedFunctorIds : Array FunctorId := #[
  FunctorId.bilWFormBaseChange,
  FunctorId.bilinModuleBaseChange,
  FunctorId.bilinModuleChangeValue,
  FunctorId.bilinModuleForget,
  FunctorId.finiteProjectiveForget,
  FunctorId.latticeBaseChange,
  FunctorId.latticeChangeValue,
  FunctorId.quadModuleForget,
  FunctorId.quadModuleChangeValue,
  FunctorId.quadWFormCarrier,
  FunctorId.quadWFormValue,
  FunctorId.setsIdentity]

/-- Stable spelling-alias rows owned by the standard catalogue. -/
def expectedAliasIds : Array AliasId := #[AliasId.crings]

/-- Stable opaque-category rows owned by the standard catalogue. -/
def expectedOpaqueCategoryIds : Array CategoryId := #[
  CategoryId.crystals,
  CategoryId.magmasWithTwoOperations]

/-- Stable opaque-port rows owned by the standard catalogue. -/
def expectedOpaquePortIds : Array OpaquePortId := #[
  ⟨"oport.crystals.sets"⟩,
  ⟨"oport.m2o.multiplicative"⟩,
  ⟨"oport.m2o.additive"⟩]

def exactStableIdSet (actual expected : Array String) : Bool :=
  actual.size == expected.size &&
    actual.all (fun id => expected.any (· == id)) &&
    expected.all (fun id => actual.any (· == id))

def validateStableIdSet (kind : String) (actual expected : Array String) :
    Except String Unit :=
  if exactStableIdSet actual expected then
    .ok ()
  else
    .error s!"standard manifest {kind} do not match the expected stable-ID set"

def rawIds {α : Type} (ids : Array α) (raw : α → String) : Array String :=
  ids.map raw

/-- Validate every retained row kind emitted by the standard registry manifest. -/
def validateStandardManifest (manifest : RegistryManifest) : Except String Unit := do
  validateStableIdSet "categories" (manifest.categories.map (·.id))
    (rawIds expectedCategoryIds (·.raw))
  validateStableIdSet "category families" (manifest.categoryFamilies.map (·.id))
    (rawIds expectedCategoryFamilyIds (·.raw))
  validateStableIdSet "classifiers" (manifest.classifiers.map (·.id))
    (rawIds expectedClassifierIds (·.raw))
  validateStableIdSet "functors" (manifest.functors.map (·.id))
    (rawIds expectedFunctorIds (·.raw))
  validateStableIdSet "aliases" (manifest.aliases.map (·.id))
    (rawIds expectedAliasIds (·.raw))
  validateStableIdSet "opaque categories" (manifest.opaqueCategories.map (·.id))
    (rawIds expectedOpaqueCategoryIds (·.raw))
  validateStableIdSet "opaque ports"
    (manifest.opaqueCategories.flatMap (fun category => category.ports.map (·.id)))
    (rawIds expectedOpaquePortIds (·.raw))

/- A missing registration must fail the standard contract. -/
example : !exactStableIdSet #[CategoryId.sets.raw]
    (rawIds expectedCategoryIds (·.raw)) := by
  native_decide

end LeanCategories.Catalogue.Standard
