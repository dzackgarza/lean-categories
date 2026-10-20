/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Constructions
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Constructions

@[expose] public section

/-!
# Actual bilinear formulas and their chosen value modules

The hyperbolic formula is the approved `U` requirement. The other chosen form is three times
that formula on exactly the same module. The variable-value example combines the hyperbolic
and dot-product pairings; its two coordinates are independently evaluated in the examples.
The nonlinear near-miss vanishes at zero but fails additivity, so it is not a bilinear map.
-/

open CategoryTheory
open LeanCategories LeanCategories.Algebra LeanCategories.Modules.Bilinear.Valued
open CasCatalogue.Modules.Bilinear.Valued.Constructions

namespace CasCatalogue.Modules.Bilinear.Valued.ConstructionTests

abbrev integers : CommRingCat := CommRingCat.of ℤ
abbrev vectors : ModuleCat integers := ModuleCat.of integers (Fin 2 → ℤ)
abbrev values : ModuleCat integers := ModuleCat.of integers ℤ
abbrev pairedValues : ModuleCat integers := ModuleCat.of integers (ℤ × ℤ)

/-- The actual hyperbolic bilinear formula, admitted by its four defining laws. -/
def hyperbolic : bilinearMaps integers vectors vectors values :=
  admitBilinear integers vectors vectors values
    (fun xy => xy.1 0 * xy.2 1 + xy.1 1 * xy.2 0)
    (by run_tac bilinearEvidence) PUnit.unit

/-- A different chosen form on the same carrier and with the same value module. -/
def scaledHyperbolic : bilinearMaps integers vectors vectors values :=
  admitBilinear integers vectors vectors values
    (fun xy => 3 * (xy.1 0 * xy.2 1 + xy.1 1 * xy.2 0))
    (by run_tac bilinearEvidence) PUnit.unit

/-- Two independent bilinear coordinates with values in the selected product module. -/
def pairedForm : bilinearMaps integers vectors vectors pairedValues :=
  admitBilinear integers vectors vectors pairedValues
    (fun xy => (xy.1 0 * xy.2 1 + xy.1 1 * xy.2 0,
      xy.1 0 * xy.2 0 + xy.1 1 * xy.2 1))
    (by run_tac bilinearEvidence) PUnit.unit

/-- Bilinearity does not require the two source modules to agree. -/
def mixedMap : bilinearMaps integers vectors values values :=
  admitBilinear integers vectors values values
    (fun xy => (xy.1 0 + 2 * xy.1 1) * xy.2)
    (by run_tac bilinearEvidence) PUnit.unit

example : bilinearApplication integers vectors values values (mixedMap, (![2, 1], 3)) = 12 := by
  change ((2 + 2 * 1) * 3 : ℤ) = 12
  norm_num

example : bilinearApplication integers vectors vectors values
    (hyperbolic, (![2, -1], ![3, 4])) = 5 := by
  change (2 * 4 + (-1) * 3 : ℤ) = 5
  norm_num

example : pairing integers (formed integers vectors values hyperbolic)
    (![2, -1], ![3, 4]) = (5 : ℤ) := by
  change (2 * 4 + (-1) * 3 : ℤ) = 5
  norm_num

example : bilinearApplication integers vectors vectors values
    (formMap integers (formed integers vectors values scaledHyperbolic) PUnit.unit,
      (![2, -1], ![3, 4])) = 15 := by
  change (3 * (2 * 4 + (-1) * 3) : ℤ) = 15
  norm_num

example : pairing integers (formed integers vectors values hyperbolic)
    (![2, -1], ![3, 4]) ≠
    pairing integers (formed integers vectors values scaledHyperbolic)
      (![2, -1], ![3, 4]) := by
  change (2 * 4 + (-1) * 3 : ℤ) ≠ 3 * (2 * 4 + (-1) * 3)
  norm_num

example : quadratic integers (formed integers vectors values hyperbolic) ![2, -1] = (-4 : ℤ) := by
  change (2 * (-1) + (-1) * 2 : ℤ) = -4
  norm_num

example : pairing integers (formed integers vectors pairedValues pairedForm)
    (![2, -1], ![3, 4]) = ((5, 2) : ℤ × ℤ) := by
  change ((2 * 4 + (-1) * 3, 2 * 3 + (-1) * 4) : ℤ × ℤ) = (5, 2)
  norm_num

example : ¬ IsBilinearMap ℤ (fun (x y : Fin 2 → ℤ) => x 0 * x 0 * y 1) := by
  fail_if_success
    have : IsBilinearMap ℤ (fun (x y : Fin 2 → ℤ) => x 0 * x 0 * y 1) := by
      run_tac bilinearEvidence
  intro h
  have hsum := h.add_left ![1, 2] ![1, 2] ![3, 4]
  norm_num at hsum

example (R : DomainCat) (L : LeanCategories.Lattices.Valued.IntegralLatticeCat R.obj) :
    toMetricDual R L ≫ toDiscriminant R L = 0 := by
  let : IsDomain R.obj := R.property
  exact BilWFormCat.comp_cokernelProjection
    (LeanCategories.Lattices.Valued.toMetricDualSymBilWForm R.obj L).hom

example (R : CommRingCat) {X Y : BilWFormCat R} (f : X ⟶ Y) :
    f ≫ cokernelProjection R f = 0 :=
  BilWFormCat.comp_cokernelProjection f

example (R : CommRingCat) {X Y Z : BilWFormCat R}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) :
    cokernelProjection R f ≫ cokernelDesc R f g h = g :=
  cokernelProjection_desc R f g h

end CasCatalogue.Modules.Bilinear.Valued.ConstructionTests
