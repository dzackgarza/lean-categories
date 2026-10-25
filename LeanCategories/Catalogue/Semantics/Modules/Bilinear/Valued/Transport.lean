/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Constructions
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Catalogue
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Expressions
public meta import LeanCategories.Catalogue.Semantics.Modules.Catalogue

@[expose] public section

/-!
# Structural routes and prescribed transport of formed modules

The fixed-value inclusion and the direct carrier functor retain the same actual module.
The comparison below is the existing definitions' equality, not an identification
asserted by an implementation. Change of values and scalar extension are the existing
co-Cartesian and tensor-product constructions, retaining the supplied maps.
-/

open CategoryTheory LeanCategories.Modules.Bilinear.Valued
namespace CasCatalogue
namespace FunctorId
def bilinModuleFixedValue : FunctorId := ⟨"fun.bilin_module.fixed_value"⟩
end FunctorId

namespace Modules.Bilinear.Valued.Transport
open _root_.CasCatalogue.Modules.Bilinear.Valued.Catalogue
open _root_.CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration
universe u

def FixedValueExpr : FunctorExpr BilinModule BilWForm :=
  .atomic FunctorId.bilinModuleFixedValue

noncomputable def fixedValue (R : Type u) [CommRing R] (W : ModuleCat.{u} R) :
    bilinModuleCategory R W ⥤ bilWFormCategory R := fixedValueInclusion R W

noncomputable def fixedValueRealization (R : Type u) [CommRing R]
    (W : ModuleCat.{u} R) :
    FunctorRealization FixedValueExpr (bilinModuleCategory R W)
      (bilWFormCategory R) (fixedValue R W) :=
  { sourceRealization := bilinModuleRealization R W
    targetRealization := bilWFormRealization R }

/-- The two structural routes retain exactly the same carrier and carrier maps. -/
noncomputable def carrierRoutes (R : Type u) [CommRing R] (W : ModuleCat.{u} R) :
    fixedValue R W ⋙ carrierFunctor R ≅ forget R W := eqToIso (by rfl)

/-- Change the actual value module by the supplied linear map. -/
def changeValues (R : CommRingCat.{u}) (L : BilWFormCat R)
    (W : ModuleCat.{u} R) (f : L.value ⟶ W) : BilWFormCat R :=
  valueBaseChangeObject R L f

/-- The defining formed arrow over the supplied change of values. -/
def toChangedValues (R : CommRingCat.{u}) (L : BilWFormCat R)
    (W : ModuleCat.{u} R) (f : L.value ⟶ W) : L ⟶ changeValues R L W f :=
  valueBaseChangeHom R L f

/-- Extend both carrier and values along the supplied scalar homomorphism. -/
noncomputable def extendScalars (R S : CommRingCat.{u}) (φ : R ⟶ S)
    (L : BilWFormCat R) : BilWFormCat S := by
  letI : Algebra R S := φ.hom.toAlgebra
  exact (LeanCategories.Lattices.Valued.baseChangeBilWForm R S).obj L

end Modules.Bilinear.Valued.Transport

normalized_registry .functor
  { id := FunctorId.bilinModuleFixedValue
    source := Modules.Bilinear.Valued.Catalogue.BilinModule
    target := Modules.Bilinear.Valued.Catalogue.BilWForm
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Transport.fixedValue
    realization := `CasCatalogue.Modules.Bilinear.Valued.Transport.fixedValueRealization
    expression := Modules.Bilinear.Valued.Transport.FixedValueExpr
    structural := true }
normalized_registry .cell
  { id := ⟨"cell.bilin_module.carrier_routes"⟩
    source := Modules.Bilinear.Valued.Catalogue.BilinModule
    target := Modules.Modules
    left := #[.functor FunctorId.bilinModuleFixedValue, .functor FunctorId.bilWFormCarrier]
    right := #[.functor FunctorId.bilinModuleForget]
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Transport.carrierRoutes
    invertible := true }
normalized_registry .object
  { id := ⟨"obj.bil_wform.changed_values"⟩, category := CategoryId.bilWForm
    name := "ChangedFormValues"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Transport.changeValues }
normalized_registry .morphism
  { id := ⟨"mor.bil_wform.to_changed_values"⟩, category := CategoryId.bilWForm
    name := "to_changed_values"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Transport.toChangedValues }
normalized_registry .object
  { id := ⟨"obj.bil_wform.extended_scalars"⟩, category := CategoryId.bilWForm
    name := "ExtendedFormScalars"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Transport.extendScalars }
end CasCatalogue
