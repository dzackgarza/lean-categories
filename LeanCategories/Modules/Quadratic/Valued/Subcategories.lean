/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Torsion
public import LeanCategories.Modules.Quadratic.Valued.Total

@[expose] public section

open CategoryTheory

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-! ## Fixed-value carrier conditions -/

def isProjectiveQuadModule : ObjectProperty (QuadModuleCat R W) :=
  fun Q => Module.Projective R Q.carrier

abbrev ProjectiveQuadModuleCat :=
  (isProjectiveQuadModule R W).FullSubcategory

def projectiveQuadModuleInclusion :
    ProjectiveQuadModuleCat R W ⥤ QuadModuleCat R W :=
  (isProjectiveQuadModule R W).ι

def projectiveQuadModuleForget :
    ProjectiveQuadModuleCat R W ⥤ ModuleCat R :=
  projectiveQuadModuleInclusion R W ⋙ forget R W

def isFiniteProjectiveQuadModule : ObjectProperty (QuadModuleCat R W) :=
  fun Q => Module.Projective R Q.carrier ∧ Module.Finite R Q.carrier

abbrev FiniteProjectiveQuadModuleCat :=
  (isFiniteProjectiveQuadModule R W).FullSubcategory

def finiteProjectiveQuadModuleInclusion :
    FiniteProjectiveQuadModuleCat R W ⥤ QuadModuleCat R W :=
  (isFiniteProjectiveQuadModule R W).ι

def finiteProjectiveQuadModuleForget :
    FiniteProjectiveQuadModuleCat R W ⥤ ModuleCat R :=
  finiteProjectiveQuadModuleInclusion R W ⋙ forget R W

def isFreeQuadModule : ObjectProperty (QuadModuleCat R W) :=
  fun Q => Module.Free R Q.carrier

abbrev FreeQuadModuleCat :=
  (isFreeQuadModule R W).FullSubcategory

def freeQuadModuleInclusion : FreeQuadModuleCat R W ⥤ QuadModuleCat R W :=
  (isFreeQuadModule R W).ι

def freeQuadModuleForget : FreeQuadModuleCat R W ⥤ ModuleCat R :=
  freeQuadModuleInclusion R W ⋙ forget R W

def isFiniteFreeQuadModule : ObjectProperty (QuadModuleCat R W) :=
  fun Q => Module.Free R Q.carrier ∧ Module.Finite R Q.carrier

abbrev FiniteFreeQuadModuleCat :=
  (isFiniteFreeQuadModule R W).FullSubcategory

def finiteFreeQuadModuleInclusion :
    FiniteFreeQuadModuleCat R W ⥤ QuadModuleCat R W :=
  (isFiniteFreeQuadModule R W).ι

def finiteFreeQuadModuleForget :
    FiniteFreeQuadModuleCat R W ⥤ ModuleCat R :=
  finiteFreeQuadModuleInclusion R W ⋙ forget R W

def isTorsionFreeQuadModule : ObjectProperty (QuadModuleCat R W) :=
  fun Q => Module.IsTorsionFree R Q.carrier

abbrev TorsionFreeQuadModuleCat :=
  (isTorsionFreeQuadModule R W).FullSubcategory

def torsionFreeQuadModuleInclusion :
    TorsionFreeQuadModuleCat R W ⥤ QuadModuleCat R W :=
  (isTorsionFreeQuadModule R W).ι

def torsionFreeQuadModuleForget :
    TorsionFreeQuadModuleCat R W ⥤ ModuleCat R :=
  torsionFreeQuadModuleInclusion R W ⋙ forget R W

def isTorsionQuadModule : ObjectProperty (QuadModuleCat R W) :=
  fun Q => Module.IsTorsion R Q.carrier

abbrev TorsionQuadModuleCat :=
  (isTorsionQuadModule R W).FullSubcategory

def torsionQuadModuleInclusion :
    TorsionQuadModuleCat R W ⥤ QuadModuleCat R W :=
  (isTorsionQuadModule R W).ι

def torsionQuadModuleForget :
    TorsionQuadModuleCat R W ⥤ ModuleCat R :=
  torsionQuadModuleInclusion R W ⋙ forget R W

def finiteTorsionQuadModuleInclusion :
    FiniteTorsionQuadModuleCat R W ⥤ QuadModuleCat R W :=
  (isFiniteTorsionQuadModule R W).ι

def finiteTorsionQuadModuleForget :
    FiniteTorsionQuadModuleCat R W ⥤ ModuleCat R :=
  finiteTorsionQuadModuleInclusion R W ⋙ forget R W

/-! ## Variable-value carrier conditions -/

def isProjectiveQuadWForm : ObjectProperty (QuadWFormCat R) :=
  fun X => Module.Projective R X.carrier

abbrev ProjectiveQuadWFormCat :=
  (isProjectiveQuadWForm R).FullSubcategory

def projectiveQuadWFormInclusion :
    ProjectiveQuadWFormCat R ⥤ QuadWFormCat R :=
  (isProjectiveQuadWForm R).ι

def projectiveQuadWFormForget : ProjectiveQuadWFormCat R ⥤ ModuleCat R :=
  projectiveQuadWFormInclusion R ⋙ carrierProjection R

def isFiniteProjectiveQuadWForm : ObjectProperty (QuadWFormCat R) :=
  fun X => Module.Projective R X.carrier ∧ Module.Finite R X.carrier

abbrev FiniteProjectiveQuadWFormCat :=
  (isFiniteProjectiveQuadWForm R).FullSubcategory

def finiteProjectiveQuadWFormInclusion :
    FiniteProjectiveQuadWFormCat R ⥤ QuadWFormCat R :=
  (isFiniteProjectiveQuadWForm R).ι

def finiteProjectiveQuadWFormForget :
    FiniteProjectiveQuadWFormCat R ⥤ ModuleCat R :=
  finiteProjectiveQuadWFormInclusion R ⋙ carrierProjection R

def isFreeQuadWForm : ObjectProperty (QuadWFormCat R) :=
  fun X => Module.Free R X.carrier

abbrev FreeQuadWFormCat :=
  (isFreeQuadWForm R).FullSubcategory

def freeQuadWFormInclusion : FreeQuadWFormCat R ⥤ QuadWFormCat R :=
  (isFreeQuadWForm R).ι

def freeQuadWFormForget : FreeQuadWFormCat R ⥤ ModuleCat R :=
  freeQuadWFormInclusion R ⋙ carrierProjection R

def isFiniteFreeQuadWForm : ObjectProperty (QuadWFormCat R) :=
  fun X => Module.Free R X.carrier ∧ Module.Finite R X.carrier

abbrev FiniteFreeQuadWFormCat :=
  (isFiniteFreeQuadWForm R).FullSubcategory

def finiteFreeQuadWFormInclusion :
    FiniteFreeQuadWFormCat R ⥤ QuadWFormCat R :=
  (isFiniteFreeQuadWForm R).ι

def finiteFreeQuadWFormForget :
    FiniteFreeQuadWFormCat R ⥤ ModuleCat R :=
  finiteFreeQuadWFormInclusion R ⋙ carrierProjection R

def isTorsionFreeQuadWForm : ObjectProperty (QuadWFormCat R) :=
  fun X => Module.IsTorsionFree R X.carrier

abbrev TorsionFreeQuadWFormCat :=
  (isTorsionFreeQuadWForm R).FullSubcategory

def torsionFreeQuadWFormInclusion :
    TorsionFreeQuadWFormCat R ⥤ QuadWFormCat R :=
  (isTorsionFreeQuadWForm R).ι

def torsionFreeQuadWFormForget : TorsionFreeQuadWFormCat R ⥤ ModuleCat R :=
  torsionFreeQuadWFormInclusion R ⋙ carrierProjection R

def isTorsionQuadWForm : ObjectProperty (QuadWFormCat R) :=
  fun X => Module.IsTorsion R X.carrier

abbrev TorsionQuadWFormCat :=
  (isTorsionQuadWForm R).FullSubcategory

def torsionQuadWFormInclusion : TorsionQuadWFormCat R ⥤ QuadWFormCat R :=
  (isTorsionQuadWForm R).ι

def torsionQuadWFormForget : TorsionQuadWFormCat R ⥤ ModuleCat R :=
  torsionQuadWFormInclusion R ⋙ carrierProjection R

def isFiniteTorsionQuadWForm : ObjectProperty (QuadWFormCat R) :=
  fun X => Module.Finite R X.carrier ∧ Module.IsTorsion R X.carrier

abbrev FiniteTorsionQuadWFormCat :=
  (isFiniteTorsionQuadWForm R).FullSubcategory

def finiteTorsionQuadWFormInclusion :
    FiniteTorsionQuadWFormCat R ⥤ QuadWFormCat R :=
  (isFiniteTorsionQuadWForm R).ι

def finiteTorsionQuadWFormForget :
    FiniteTorsionQuadWFormCat R ⥤ ModuleCat R :=
  finiteTorsionQuadWFormInclusion R ⋙ carrierProjection R

end LeanCategories.Modules.Quadratic.Valued
