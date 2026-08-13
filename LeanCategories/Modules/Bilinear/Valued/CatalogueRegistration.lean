module

public import LeanCategories.Catalogue.Registry.Extension
public import LeanCategories.Lattices.Valued.BaseChange
public import LeanCategories.Modules.Bilinear.Valued.Catalogue
public import LeanCategories.Modules.Bilinear.Valued.ChangeValue
public import LeanCategories.Modules.Bilinear.Valued.Expressions
public import LeanCategories.Modules.Bilinear.Valued.Total
public import LeanCategories.Modules.Mathlib
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

noncomputable def bilinModuleCategory (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] : ObjCat.{u + 1, u} :=
  Cat.of (BilinModuleCat R W)

noncomputable def bilWFormCategory (R : Type u) [CommRing R] : ObjCat.{u + 1, u} :=
  Cat.of (BilWFormCat R)

noncomputable def bilinModuleRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization BilinModule (bilinModuleCategory R W) := ⟨⟩

noncomputable def bilWFormRealization (R : Type u) [CommRing R] :
    CategoryRealization BilWForm (bilWFormCategory R) := ⟨⟩

noncomputable def bilinModuleForgetRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    FunctorRealization BilinModuleForget (bilinModuleCategory R W)
      (Modules.Mathlib.ModulesOf (RingCat.of R))
      (LeanCategories.Modules.Bilinear.Valued.forget R W).toCatHom := ⟨⟩

noncomputable def bilinModuleChangeValueRealization (R : Type u) [CommRing R]
    (W W' : Type u) [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W') :
    FunctorRealization BilinModuleChangeValue (bilinModuleCategory R W)
      (bilinModuleCategory R W')
      (LeanCategories.Modules.Bilinear.Valued.changeValue R W f).toCatHom := ⟨⟩

noncomputable def bilinModuleBaseChangeRealization (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    (W : Type u) [AddCommGroup W] [Module R W] :
    FunctorRealization BilinModuleBaseChange (bilinModuleCategory R W)
      (bilinModuleCategory S (TensorProduct R S W))
      (LeanCategories.Lattices.Valued.baseChangeBilin R W S).toCatHom := ⟨⟩

noncomputable def bilWFormBaseChangeRealization (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S] :
    FunctorRealization BilWFormBaseChange (bilWFormCategory R)
      (bilWFormCategory S)
      (LeanCategories.Lattices.Valued.baseChangeBilWForm R S).toCatHom := ⟨⟩

normalized_registry .category
  { id := CategoryId.bilinModule
    canonicalName := "BilinModuleCat"
    declaration := `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleCategory
    expression := BilinModule
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleRealization
    origin := .opaqueCategory
    visibility := .present }

normalized_registry .category
  { id := CategoryId.bilWForm
    canonicalName := "BilWFormCat"
    declaration := `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormCategory
    expression := BilWForm
    realization := `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormRealization
    origin := .opaqueCategory
    visibility := .present }

normalized_registry .functor
  { id := FunctorId.bilinModuleForget
    canonicalName := "BilinModuleCat.forget"
    source := BilinModule
    target := Modules.Modules
    declaration := `LeanCategories.Modules.Bilinear.Valued.forget
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleForgetRealization
    expression := BilinModuleForget
    role := .generatedStructural
    admissibility := .generated
    port := none
    origin := "existing formed-module forgetful functor"
    coherenceClass := none
    preferredPresentation := false }

normalized_registry .functor
  { id := FunctorId.bilinModuleChangeValue
    canonicalName := "BilinModuleCat.changeValue"
    source := BilinModule
    target := BilinModule
    declaration := `LeanCategories.Modules.Bilinear.Valued.changeValue
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleChangeValueRealization
    expression := BilinModuleChangeValue
    role := .constructorAction
    admissibility := .declared
    port := none
    origin := "existing formed-module value change"
    coherenceClass := none
    preferredPresentation := false }

normalized_registry .functor
  { id := FunctorId.bilinModuleBaseChange
    canonicalName := "BilinModuleCat.baseChangeBilin"
    source := BilinModule
    target := BilinModule
    declaration := `LeanCategories.Lattices.Valued.baseChangeBilin
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleBaseChangeRealization
    expression := BilinModuleBaseChange
    role := .constructorAction
    admissibility := .declared
    port := none
    origin := "existing formed-module scalar extension"
    coherenceClass := none
    preferredPresentation := false }

normalized_registry .functor
  { id := FunctorId.bilWFormBaseChange
    canonicalName := "BilWFormCat.baseChangeBilWForm"
    source := BilWForm
    target := BilWForm
    declaration := `LeanCategories.Lattices.Valued.baseChangeBilWForm
    realization :=
      `LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormBaseChangeRealization
    expression := BilWFormBaseChange
    role := .constructorAction
    admissibility := .declared
    port := none
    origin := "existing variable-value scalar extension"
    coherenceClass := none
    preferredPresentation := false }

end LeanCategories.Modules.Bilinear.Valued.CatalogueRegistration
