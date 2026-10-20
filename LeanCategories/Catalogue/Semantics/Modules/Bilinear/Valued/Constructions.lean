/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.CatalogueRegistration
public import LeanCategories.Lattices.Valued.Discriminant
public import LeanCategories.Algebra.Concrete.Rings
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units

@[expose] public section

/-!
# Callable constructions of formed modules

The mathematical owners are `BilinModuleCat.ofBilinMap`, `BilWFormCat.of`,
`BilWFormCat.cokernelObject` and `LeanCategories.Lattices.Valued`'s metric-dual and
categorical discriminant constructions. These declarations expose their actual selected
ring, carrier, value module, bilinear map and defining arrows. They add no mathematical
construction or theorem to those owners.

A bilinear map is Mathlib's bundled `LinearMap.BilinMap`. Admission from a function uses
exactly Mathlib's `IsBilinearMap` and `IsBilinearMap.toLinearMap`, not a weaker test of a
finite collection of values. Metric duals retain the original integral-domain hypothesis
as the selected `DomainCat` object; the value module changes to the fraction field and
then its quotient in the discriminant.
-/

open CategoryTheory
open LeanCategories.Algebra LeanCategories.Modules.Bilinear.Valued
open CasCatalogue
namespace CasCatalogue.Modules.Bilinear.Valued.Constructions
universe u

/-- The set of bilinear maps between two selected modules, with the selected value module. -/
def bilinearMaps (R : CommRingCat.{u}) (M N W : ModuleCat.{u} R) : Type u :=
  M →ₗ[R] N →ₗ[R] W

/-- Evaluation of a bilinear map on a pair of carrier elements. -/
def bilinearApplication (R : CommRingCat.{u}) (M N W : ModuleCat.{u} R) :
    (bilinearMaps R M N W × (M × N) : Type u) ⟶ (W : Type u) :=
  TypeCat.ofHom fun p => (show (M →ₗ[R] N →ₗ[R] W) from p.1) p.2.1 p.2.2

/-- The underlying function of a bilinear map. -/
def bilinearInclusion (R : CommRingCat.{u}) (M N W : ModuleCat.{u} R) :
    bilinearMaps R M N W ⟶ (M × N → W : Type u) :=
  TypeCat.ofHom fun b xy => (show (M →ₗ[R] N →ₗ[R] W) from b) xy.1 xy.2

/-- A bilinear function as its bundled linear map in each variable. -/
def admitBilinear (R : CommRingCat.{u}) (M N W : ModuleCat.{u} R) (f : M × N → W)
    (h : IsBilinearMap R (fun x y => f (x, y))) :
    (PUnit.{u + 1} : Type u) ⟶ bilinearMaps R M N W :=
  TypeCat.ofHom fun _ => h.toLinearMap

open Lean Elab Tactic in
/-- Prove a module identity, using the defining product or function coordinates when needed. -/
meta partial def bilinearIdentity : TacticM Unit :=
  CasCatalogue.Evidence.closeByFirst m!"the bilinearity identity is not established"
    [do evalTactic (← `(tactic| simp <;> ring)),
     do evalTactic (← `(tactic| simp <;> module)),
     do
      evalTactic (← `(tactic| apply Prod.ext))
      for goal in ← getGoals do
        setGoals [goal]
        bilinearIdentity,
     do
      evalTactic (← `(tactic| funext i))
      bilinearIdentity]

open Lean Elab Tactic in
/-- Prove the four defining bilinearity laws by the module and ring identities. -/
meta def bilinearEvidence : TacticM Unit :=
  CasCatalogue.Evidence.establish "Bilinearity" do
    CasCatalogue.Algebra.Units.normalizeRingObjects
    evalTactic (← `(tactic| constructor <;> intros))
    for goal in ← getGoals do
      setGoals [goal]
      bilinearIdentity

/-- A chosen bilinear map, with its actual scalar, carrier and value modules. -/
def bilinear (R : CommRingCat.{u}) (M W : ModuleCat.{u} R)
    (b : bilinearMaps R M M W) : BilinModuleCat R W :=
  BilinModuleCat.ofBilinMap b
/-- The same chosen bilinear map in the variable-value category. -/
def formed (R : CommRingCat.{u}) (M W : ModuleCat.{u} R)
    (b : bilinearMaps R M M W) : BilWFormCat R :=
  BilWFormCat.of M W ((TensorProduct.lift.equiv (.id R) M M W) b)

/-- The actual carrier module, in the registered module fibre at the selected underlying ring. -/
def carrier (R : CommRingCat.{u}) (L : BilWFormCat R) :
    LeanCategories.Modules.Mathlib.ModulesOf.{u, u} ((forget₂ CommRingCat RingCat).obj R) :=
  L.carrier

/-- The actual selected value module, in the same registered module fibre. -/
def values (R : CommRingCat.{u}) (L : BilWFormCat R) :
    LeanCategories.Modules.Mathlib.ModulesOf.{u, u} ((forget₂ CommRingCat RingCat).obj R) :=
  L.value

/-- The actual selected bilinear map, as a point of the bilinear-map object. -/
def formMap (R : CommRingCat.{u}) (L : BilWFormCat R) :
    (PUnit.{u + 1} : Type u) ⟶ bilinearMaps R L.carrier L.carrier L.value :=
  TypeCat.ofHom fun _ => L.formed.bilinMap

/-- The carrier component of a formed morphism. -/
def carrierMap (R : CommRingCat.{u}) {X Y : BilWFormCat R} (f : X ⟶ Y) :
    carrier R X ⟶ carrier R Y := BilWFormCat.carrierMap f

/-- The selected value-module component of a formed morphism. -/
def valueMap (R : CommRingCat.{u}) {X Y : BilWFormCat R} (f : X ⟶ Y) :
    values R X ⟶ values R Y := BilWFormCat.valueMap f
/-- Evaluate a variable-value form without forgetting its selected value module. -/
def pairing (R : CommRingCat.{u}) (L : BilWFormCat R) :
    (L.carrier × L.carrier : Type u) ⟶ (L.value : Type u) :=
  TypeCat.ofHom fun xy => L.pairing xy.1 xy.2
/-- The diagonal quadratic value of a bilinear form. -/
def quadratic (R : CommRingCat.{u}) (L : BilWFormCat R) :
    (L.carrier : Type u) ⟶ (L.value : Type u) :=
  TypeCat.ofHom fun x => LinearMap.BilinMap.toQuadraticMap L.formed.bilinMap x
/-- The selected integral lattice as a variable-value formed module. -/
noncomputable def integralForm (R : DomainCat.{u})
    (L : LeanCategories.Lattices.Valued.IntegralLatticeCat R.obj) :
    BilWFormCat R.obj := by
  letI : IsDomain R.obj := R.property
  exact (LeanCategories.Lattices.Valued.integralSymBilWFormObject R.obj L).obj
/-- The metric dual with its fraction-field-valued pairing. -/
noncomputable def metricDual (R : DomainCat.{u})
    (L : LeanCategories.Lattices.Valued.IntegralLatticeCat R.obj) :
    BilWFormCat R.obj := by
  letI : IsDomain R.obj := R.property
  exact (LeanCategories.Lattices.Valued.metricDualSymBilWFormObject R.obj L).obj
/-- The canonical carrier map and its actual change-of-value map. -/
noncomputable def toMetricDual (R : DomainCat.{u})
    (L : LeanCategories.Lattices.Valued.IntegralLatticeCat R.obj) :
    integralForm R L ⟶ metricDual R L := by
  letI : IsDomain R.obj := R.property
  exact (LeanCategories.Lattices.Valued.toMetricDualSymBilWForm R.obj L).hom
/-- The categorical discriminant, retaining its induced value-quotient pairing. -/
noncomputable def discriminant (R : DomainCat.{u})
    (L : LeanCategories.Lattices.Valued.IntegralLatticeCat R.obj) : BilWFormCat R.obj := by
  letI : IsDomain R.obj := R.property
  exact (LeanCategories.Lattices.Valued.discriminantSymBilWFormObject R.obj L).obj
/-- The defining formed projection from metric dual to discriminant. -/
noncomputable def toDiscriminant (R : DomainCat.{u})
    (L : LeanCategories.Lattices.Valued.IntegralLatticeCat R.obj) :
    metricDual R L ⟶ discriminant R L := by
  letI : IsDomain R.obj := R.property
  exact (LeanCategories.Lattices.Valued.discriminantSymBilWFormProjection R.obj L).hom
/-- The categorical formed cokernel of the supplied formed morphism. -/
def cokernel (R : CommRingCat.{u}) {X Y : BilWFormCat R} (f : X ⟶ Y) : BilWFormCat R :=
  BilWFormCat.cokernelObject f
/-- The defining formed quotient morphism of the cokernel. -/
def cokernelProjection (R : CommRingCat.{u}) {X Y : BilWFormCat R} (f : X ⟶ Y) :
    Y ⟶ cokernel R f := BilWFormCat.cokernelProjection f
normalized_registry .object
  { id := ⟨"obj.sets.bilinear_maps"⟩, category := CategoryId.sets, name := "BilinearMaps"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.bilinearMaps
    application := some `CasCatalogue.Modules.Bilinear.Valued.Constructions.bilinearApplication
    inclusion := some `CasCatalogue.Modules.Bilinear.Valued.Constructions.bilinearInclusion
    admission := some `CasCatalogue.Modules.Bilinear.Valued.Constructions.admitBilinear
    evidence := some `CasCatalogue.Modules.Bilinear.Valued.Constructions.bilinearEvidence }

normalized_registry .object
  { id := ⟨"obj.bilin_module.bilinear_form"⟩, category := CategoryId.bilinModule
    name := "BilinearForm",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.bilinear }
normalized_registry .object
  { id := ⟨"obj.bil_wform.formed"⟩, category := CategoryId.bilWForm
    name := "FormedModule",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.formed }
normalized_registry .morphism
  { id := ⟨"mor.sets.formed_pairing"⟩, category := CategoryId.sets
    name := "formed_pairing",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.pairing }
normalized_registry .object
  { id := ⟨"obj.modules.formed_carrier"⟩, category := CategoryId.modulesR
    name := "FormCarrier"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.carrier }
normalized_registry .object
  { id := ⟨"obj.modules.formed_values"⟩, category := CategoryId.modulesR
    name := "FormValues"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.values }
normalized_registry .morphism
  { id := ⟨"mor.sets.formed_form_map"⟩, category := CategoryId.sets
    name := "form_map"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.formMap }
normalized_registry .morphism
  { id := ⟨"mor.modules.formed_carrier_map"⟩, category := CategoryId.modulesR
    name := "formed_carrier_map"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.carrierMap }
normalized_registry .morphism
  { id := ⟨"mor.modules.formed_value_map"⟩, category := CategoryId.modulesR
    name := "formed_value_map"
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.valueMap }
normalized_registry .morphism
  { id := ⟨"mor.sets.formed_quadratic"⟩, category := CategoryId.sets
    name := "quadratic_value",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.quadratic }
normalized_registry .object
  { id := ⟨"obj.bil_wform.integral_form"⟩, category := CategoryId.bilWForm
    name := "IntegralForm",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.integralForm }
normalized_registry .object
  { id := ⟨"obj.bil_wform.metric_dual"⟩, category := CategoryId.bilWForm
    name := "MetricDual",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.metricDual }
normalized_registry .morphism
  { id := ⟨"mor.bil_wform.to_metric_dual"⟩, category := CategoryId.bilWForm
    name := "to_metric_dual",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.toMetricDual }
normalized_registry .object
  { id := ⟨"obj.bil_wform.discriminant"⟩, category := CategoryId.bilWForm
    name := "DiscriminantForm",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.discriminant }
normalized_registry .morphism
  { id := ⟨"mor.bil_wform.to_discriminant"⟩, category := CategoryId.bilWForm
    name := "to_discriminant",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.toDiscriminant }
normalized_registry .object
  { id := ⟨"obj.bil_wform.cokernel"⟩, category := CategoryId.bilWForm
    name := "FormedCokernel",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.cokernel }
normalized_registry .morphism
  { id := ⟨"mor.bil_wform.cokernel_projection"⟩, category := CategoryId.bilWForm
    name := "formed_cokernel_projection",
    declaration := `CasCatalogue.Modules.Bilinear.Valued.Constructions.cokernelProjection }
end CasCatalogue.Modules.Bilinear.Valued.Constructions
