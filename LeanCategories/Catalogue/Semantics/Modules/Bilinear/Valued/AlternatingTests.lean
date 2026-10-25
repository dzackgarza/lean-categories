/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Alternating
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Constructions

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued
open CasCatalogue.Modules.Bilinear.Valued.Constructions

namespace CasCatalogue.Modules.Bilinear.Valued.AlternatingTests

abbrev integers : CommRingCat := CommRingCat.of ℤ
abbrev vectors : ModuleCat integers := ModuleCat.of integers (Fin 2 → ℤ)
abbrev values : ModuleCat integers := ModuleCat.of integers ℤ

/-- The determinant pairing on the chosen integral plane. -/
def determinantPairing : bilinearMaps integers vectors vectors values :=
  admitBilinear integers vectors vectors values
    (fun xy => xy.1 0 * xy.2 1 - xy.1 1 * xy.2 0)
    (by run_tac bilinearEvidence) PUnit.unit

/-- Classification keeps that actual determinant pairing. -/
def determinantPlane : AltBilinModuleCat integers values :=
  Alternating.alternating integers vectors values determinantPairing (by
    intro x
    change x 0 * x 1 - x 1 * x 0 = (0 : ℤ)
    ring)

example : determinantPlane.obj.pairing ![2, -1] ![3, 4] = (11 : ℤ) := by
  change (2 * 4 - (-1) * 3 : ℤ) = 11
  norm_num

example : determinantPlane.obj.IsSkewSymmetric :=
  determinantPlane.obj.isSkewSymmetric_of_isAlternating determinantPlane.property

/-- The same carrier supports a symmetric form which cannot be classified as alternating. -/
example : ¬ (formed integers vectors values
    (admitBilinear integers vectors vectors values
      (fun xy => xy.1 0 * xy.2 1 + xy.1 1 * xy.2 0)
      (by run_tac bilinearEvidence) PUnit.unit)).IsAlternating := by
  intro h
  have hz := h ![1, 1]
  change (1 * 1 + 1 * 1 : ℤ) = 0 at hz
  norm_num at hz

end CasCatalogue.Modules.Bilinear.Valued.AlternatingTests
