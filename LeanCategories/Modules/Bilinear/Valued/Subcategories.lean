/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Properties
public import LeanCategories.Modules.Bilinear.Valued.Torsion

@[expose] public section

open CategoryTheory

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-! ## Fixed-value carrier conditions -/

def isProjectiveBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L => Module.Projective R L.carrier

abbrev ProjectiveBilinModuleCat :=
  (isProjectiveBilinModule R W).FullSubcategory

def projectiveBilinModuleInclusion :
    ProjectiveBilinModuleCat R W ⥤ BilinModuleCat R W :=
  (isProjectiveBilinModule R W).ι

def projectiveBilinModuleForget :
    ProjectiveBilinModuleCat R W ⥤ ModuleCat R :=
  projectiveBilinModuleInclusion R W ⋙ forget R W

def isFiniteProjectiveBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L => Module.Projective R L.carrier ∧ Module.Finite R L.carrier

abbrev FiniteProjectiveBilinModuleCat :=
  (isFiniteProjectiveBilinModule R W).FullSubcategory

def finiteProjectiveBilinModuleInclusion :
    FiniteProjectiveBilinModuleCat R W ⥤ BilinModuleCat R W :=
  (isFiniteProjectiveBilinModule R W).ι

def finiteProjectiveBilinModuleForget :
    FiniteProjectiveBilinModuleCat R W ⥤ ModuleCat R :=
  finiteProjectiveBilinModuleInclusion R W ⋙ forget R W

def isFreeBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L => Module.Free R L.carrier

abbrev FreeBilinModuleCat :=
  (isFreeBilinModule R W).FullSubcategory

def freeBilinModuleInclusion : FreeBilinModuleCat R W ⥤ BilinModuleCat R W :=
  (isFreeBilinModule R W).ι

def freeBilinModuleForget : FreeBilinModuleCat R W ⥤ ModuleCat R :=
  freeBilinModuleInclusion R W ⋙ forget R W

def isFiniteFreeBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L => Module.Free R L.carrier ∧ Module.Finite R L.carrier

abbrev FiniteFreeBilinModuleCat :=
  (isFiniteFreeBilinModule R W).FullSubcategory

def finiteFreeBilinModuleInclusion :
    FiniteFreeBilinModuleCat R W ⥤ BilinModuleCat R W :=
  (isFiniteFreeBilinModule R W).ι

def finiteFreeBilinModuleForget :
    FiniteFreeBilinModuleCat R W ⥤ ModuleCat R :=
  finiteFreeBilinModuleInclusion R W ⋙ forget R W

def isTorsionFreeBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L => Module.IsTorsionFree R L.carrier

abbrev TorsionFreeBilinModuleCat :=
  (isTorsionFreeBilinModule R W).FullSubcategory

def torsionFreeBilinModuleInclusion :
    TorsionFreeBilinModuleCat R W ⥤ BilinModuleCat R W :=
  (isTorsionFreeBilinModule R W).ι

def torsionFreeBilinModuleForget :
    TorsionFreeBilinModuleCat R W ⥤ ModuleCat R :=
  torsionFreeBilinModuleInclusion R W ⋙ forget R W

def isTorsionBilinModule : ObjectProperty (BilinModuleCat R W) :=
  fun L => Module.IsTorsion R L.carrier

abbrev TorsionBilinModuleCat :=
  (isTorsionBilinModule R W).FullSubcategory

def torsionBilinModuleInclusion :
    TorsionBilinModuleCat R W ⥤ BilinModuleCat R W :=
  (isTorsionBilinModule R W).ι

def torsionBilinModuleForget :
    TorsionBilinModuleCat R W ⥤ ModuleCat R :=
  torsionBilinModuleInclusion R W ⋙ forget R W

def finiteTorsionBilinModuleInclusion :
    FiniteTorsionBilinModuleCat R W ⥤ BilinModuleCat R W :=
  (isFiniteTorsionBilinModule R W).ι

def finiteTorsionBilinModuleForget :
    FiniteTorsionBilinModuleCat R W ⥤ ModuleCat R :=
  finiteTorsionBilinModuleInclusion R W ⋙ forget R W

/-! ## Variable-value carrier conditions -/

def carrierProjection : BilWFormCat R ⥤ ModuleCat R where
  obj := BilWFormCat.carrier
  map := BilWFormCat.carrierMap
  map_id _ := rfl
  map_comp _ _ := rfl

def isProjectiveBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X => Module.Projective R X.carrier

abbrev ProjectiveBilWFormCat :=
  (isProjectiveBilWForm R).FullSubcategory

def projectiveBilWFormInclusion :
    ProjectiveBilWFormCat R ⥤ BilWFormCat R :=
  (isProjectiveBilWForm R).ι

def projectiveBilWFormForget : ProjectiveBilWFormCat R ⥤ ModuleCat R :=
  projectiveBilWFormInclusion R ⋙ carrierProjection R

def isFiniteProjectiveBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X => Module.Projective R X.carrier ∧ Module.Finite R X.carrier

abbrev FiniteProjectiveBilWFormCat :=
  (isFiniteProjectiveBilWForm R).FullSubcategory

def finiteProjectiveBilWFormInclusion :
    FiniteProjectiveBilWFormCat R ⥤ BilWFormCat R :=
  (isFiniteProjectiveBilWForm R).ι

def finiteProjectiveBilWFormForget :
    FiniteProjectiveBilWFormCat R ⥤ ModuleCat R :=
  finiteProjectiveBilWFormInclusion R ⋙ carrierProjection R

def isFreeBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X => Module.Free R X.carrier

abbrev FreeBilWFormCat :=
  (isFreeBilWForm R).FullSubcategory

def freeBilWFormInclusion : FreeBilWFormCat R ⥤ BilWFormCat R :=
  (isFreeBilWForm R).ι

def freeBilWFormForget : FreeBilWFormCat R ⥤ ModuleCat R :=
  freeBilWFormInclusion R ⋙ carrierProjection R

def isFiniteFreeBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X => Module.Free R X.carrier ∧ Module.Finite R X.carrier

abbrev FiniteFreeBilWFormCat :=
  (isFiniteFreeBilWForm R).FullSubcategory

def finiteFreeBilWFormInclusion :
    FiniteFreeBilWFormCat R ⥤ BilWFormCat R :=
  (isFiniteFreeBilWForm R).ι

def finiteFreeBilWFormForget :
    FiniteFreeBilWFormCat R ⥤ ModuleCat R :=
  finiteFreeBilWFormInclusion R ⋙ carrierProjection R

def isTorsionFreeBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X => Module.IsTorsionFree R X.carrier

abbrev TorsionFreeBilWFormCat :=
  (isTorsionFreeBilWForm R).FullSubcategory

def torsionFreeBilWFormInclusion :
    TorsionFreeBilWFormCat R ⥤ BilWFormCat R :=
  (isTorsionFreeBilWForm R).ι

def torsionFreeBilWFormForget : TorsionFreeBilWFormCat R ⥤ ModuleCat R :=
  torsionFreeBilWFormInclusion R ⋙ carrierProjection R

def isTorsionBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X => Module.IsTorsion R X.carrier

abbrev TorsionBilWFormCat :=
  (isTorsionBilWForm R).FullSubcategory

def torsionBilWFormInclusion : TorsionBilWFormCat R ⥤ BilWFormCat R :=
  (isTorsionBilWForm R).ι

def torsionBilWFormForget : TorsionBilWFormCat R ⥤ ModuleCat R :=
  torsionBilWFormInclusion R ⋙ carrierProjection R

def isFiniteTorsionBilWForm : ObjectProperty (BilWFormCat R) :=
  fun X => Module.Finite R X.carrier ∧ Module.IsTorsion R X.carrier

abbrev FiniteTorsionBilWFormCat :=
  (isFiniteTorsionBilWForm R).FullSubcategory

def finiteTorsionBilWFormInclusion :
    FiniteTorsionBilWFormCat R ⥤ BilWFormCat R :=
  (isFiniteTorsionBilWForm R).ι

def finiteTorsionBilWFormForget :
    FiniteTorsionBilWFormCat R ⥤ ModuleCat R :=
  finiteTorsionBilWFormInclusion R ⋙ carrierProjection R

end LeanCategories.Modules.Bilinear.Valued
