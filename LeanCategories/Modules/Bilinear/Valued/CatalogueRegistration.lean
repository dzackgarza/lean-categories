module

public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Lattices.Valued.BaseChange
public import LeanCategories.Modules.Bilinear.Valued.Catalogue
public import LeanCategories.Modules.Bilinear.Valued.ChangeValue
public import LeanCategories.Modules.Bilinear.Valued.Expressions
public import LeanCategories.Modules.Bilinear.Valued.Total
public import LeanCategories.Modules.Mathlib
public import LeanCategories.Modules.CatalogueRegistration
public import LeanCategories.Modules.Expressions
public meta import LeanCategories.Catalogue.Registry.Extension
public meta import LeanCategories.Modules.Bilinear.Valued.Catalogue
public meta import LeanCategories.Modules.Bilinear.Valued.Expressions
public meta import LeanCategories.Modules.Catalogue

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration

open CategoryTheory
open LeanCategories
open LeanCategories.Modules.Bilinear.Valued.Catalogue

universe u

noncomputable def bilinModuleFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ R : CommRingCat.{u}, ModuleCat.{u} R)
    (fun (parameter : Σ R : CommRingCat.{u}, ModuleCat.{u} R) =>
    letI := parameter.1.commRing
    (Cat.of (BilinModuleCat parameter.1 parameter.2) : ObjCat.{u + 1, u}))

noncomputable def bilinModuleFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1} CategoryFamilyId.bilinModule .commRingModule
      (P := Discrete (Σ R : CommRingCat.{u}, ModuleCat.{u} R)) where
  transport := bilinModuleFamilyTransport
  transportSemantics := .discrete
noncomputable def bilWFormFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1} (P := CommRingCat.{u})
    (fun (R : CommRingCat.{u}) =>
    letI := R.commRing
    (Cat.of (BilWFormCat R) : ObjCat.{u + 1, u}))

noncomputable def bilWFormFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1} CategoryFamilyId.bilWForm .commRing
      (P := Discrete (CommRingCat.{u})) where
  transport := bilWFormFamilyTransport
  transportSemantics := .discrete
noncomputable def bilinModuleCategory (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] : ObjCat.{u + 1, u} :=
  Cat.of (BilinModuleCat R W)

noncomputable def bilWFormCategory (R : Type u) [CommRing R] : ObjCat.{u + 1, u} :=
  Cat.of (BilWFormCat R)

noncomputable def bilinModuleRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization BilinModule (bilinModuleCategory R W) where
  familyFibre := some (.mk bilinModuleFamilyRealization {
    parameter := ⟨CommRingCat.of R, ModuleCat.of R W⟩
    parameterQuotation := .commRingModuleRW (CommRingCat.of R) (ModuleCat.of R W)
    category_eq := by rfl })

noncomputable def bilWFormRealization (R : Type u) [CommRing R] :
    CategoryRealization BilWForm (bilWFormCategory R) where
  familyFibre := some (.mk bilWFormFamilyRealization {
    parameter := ⟨CommRingCat.of R⟩
    parameterQuotation := .commRingR (CommRingCat.of R)
    category_eq := by rfl })

normalized_registry .categoryFamily
  { id := CategoryFamilyId.bilinModule
    canonicalName := "BilinModuleCat(R, W)"
    schema := .commRingModule
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleFamilyRealization
    transport :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleFamilyTransport
    transportSemantics := .discrete }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.bilWForm
    canonicalName := "BilWFormCat(R)"
    schema := .commRing
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormFamilyRealization
    transport :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormFamilyTransport
    transportSemantics := .discrete }

noncomputable def bilinModuleForgetRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    FunctorRealization BilinModuleForget (bilinModuleCategory R W)
      (Modules.Mathlib.ModulesOf (RingCat.of R))
      (LeanCategories.Modules.Bilinear.Valued.forget R W) :=
  { sourceRealization := bilinModuleRealization R W
    targetRealization := LeanCategories.Modules.CatalogueRegistration.modulesRealization (RingCat.of R) }

noncomputable def bilinModuleChangeValueRealization (R : Type u) [CommRing R]
    (W W' : Type u) [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W') :
    FunctorRealization BilinModuleChangeValue (bilinModuleCategory R W)
      (bilinModuleCategory R W')
      (LeanCategories.Modules.Bilinear.Valued.changeValue R W f) :=
  { sourceRealization := bilinModuleRealization R W
    targetRealization :=
       { familyFibre := some (.mk bilinModuleFamilyRealization {
          parameter := ⟨CommRingCat.of R, ModuleCat.of R W'⟩
          parameterQuotation := .commRingModuleRWPrime (CommRingCat.of R) (ModuleCat.of R W')
          category_eq := by rfl }) } }

noncomputable def bilinModuleBaseChangeRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W]
    (S : Type u) [CommRing S] [Algebra R S] :
    FunctorRealization BilinModuleBaseChange (bilinModuleCategory R W)
      (bilinModuleCategory S (TensorProduct R S W))
      (LeanCategories.Lattices.Valued.baseChangeBilin R W S) :=
  { sourceRealization := bilinModuleRealization R W
    targetRealization :=
       { familyFibre := some (.mk bilinModuleFamilyRealization {
          parameter := ⟨CommRingCat.of S, ModuleCat.of S (TensorProduct R S W)⟩
          parameterQuotation := .commRingModuleTensorProduct R S W
          category_eq := by rfl }) } }

noncomputable def bilWFormBaseChangeRealization (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    FunctorRealization BilWFormBaseChange (bilWFormCategory R)
      (bilWFormCategory S)
      (LeanCategories.Lattices.Valued.baseChangeBilWForm R S) :=
  { sourceRealization := bilWFormRealization R
    targetRealization :=
       { familyFibre := some (.mk bilWFormFamilyRealization {
          parameter := ⟨CommRingCat.of S⟩
          parameterQuotation := .commRingS (CommRingCat.of S)
          category_eq := by rfl }) } }

noncomputable def bilinModuleForgetDeclaration (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    bilinModuleCategory R W ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  (LeanCategories.Modules.Bilinear.Valued.forget R W).toCatHom

noncomputable def bilinModuleChangeValueDeclaration (R : Type u) [CommRing R]
    (W W' : Type u) [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W') :
    bilinModuleCategory R W ⟶ bilinModuleCategory R W' :=
  (LeanCategories.Modules.Bilinear.Valued.changeValue R W f).toCatHom

noncomputable def bilinModuleBaseChangeDeclaration (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W]
    (S : Type u) [CommRing S] [Algebra R S] :
    bilinModuleCategory R W ⟶ bilinModuleCategory S (TensorProduct R S W) :=
  (LeanCategories.Lattices.Valued.baseChangeBilin R W S).toCatHom

noncomputable def bilWFormBaseChangeDeclaration (R : Type u) [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    bilWFormCategory R ⟶ bilWFormCategory S :=
  (LeanCategories.Lattices.Valued.baseChangeBilWForm R S).toCatHom

normalized_registry .category
  { id := CategoryId.bilinModule
    canonicalName := "BilinModuleCat"
    declaration := `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleCategory
    expression := BilinModule
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleRealization}

normalized_registry .category
  { id := CategoryId.bilWForm
    canonicalName := "BilWFormCat"
    declaration := `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormCategory
    expression := BilWForm
    realization := `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormRealization}

normalized_registry .functor
  { id := FunctorId.bilinModuleForget
    canonicalName := "BilinModuleCat.forget"
    source := BilinModule
    target := Modules.Modules
    declaration :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleForgetDeclaration
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleForgetRealization
    expression := BilinModuleForget }

normalized_registry .functor
  { id := FunctorId.bilinModuleChangeValue
    canonicalName := "BilinModuleCat.changeValue"
    source := BilinModule
    target :=
      .familyApp CategoryFamilyId.bilinModule
        #[.variable ParameterId.r, .variable ParameterId.wPrime]
    declaration :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleChangeValueDeclaration
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleChangeValueRealization
    expression := BilinModuleChangeValue }

normalized_registry .functor
  { id := FunctorId.bilinModuleBaseChange
    canonicalName := "BilinModuleCat.baseChangeBilin"
    source := BilinModule
    target :=
      .familyApp CategoryFamilyId.bilinModule
        #[.variable ParameterId.s,
          .apply3 ParameterOperationId.tensorProduct
            (.variable ParameterId.r) (.variable ParameterId.s) (.variable ParameterId.w)]
    declaration :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleBaseChangeDeclaration
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleBaseChangeRealization
    expression := BilinModuleBaseChange }

normalized_registry .functor
  { id := FunctorId.bilWFormBaseChange
    canonicalName := "BilWFormCat.baseChangeBilWForm"
    source := BilWForm
    target := .familyApp CategoryFamilyId.bilWForm #[.variable ParameterId.s]
    declaration :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormBaseChangeDeclaration
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormBaseChangeRealization
    expression := BilWFormBaseChange }

end LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration
