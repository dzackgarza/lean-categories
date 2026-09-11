/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Grothendieck axiom AB4*

Weibel, *An Introduction to Homological Algebra*, §3.5.

Mathlib's `AB4Star` is exactly the source convention: arbitrary products exist and are exact.
The category of abelian groups and every module category already carry pinned Mathlib instances.
This file adds the source's chain-complex example: ordinary chain complexes of abelian groups also
satisfy AB4*, because products and finite-colimit exactness are computed degreewise.
-/

@[expose] public section

open CategoryTheory Limits

namespace LeanCategories.Homological

universe u

/-- The category of abelian groups satisfies Weibel's axiom AB4*. -/
theorem addCommGrpCatAB4Star : AB4Star AddCommGrpCat.{0} := inferInstance

/-- Every module category satisfies Weibel's axiom AB4*. -/
theorem moduleCatAB4Star (R : Type u) [Ring R] : AB4Star (ModuleCat.{u} R) := inferInstance

/-- Products of ordinary chain complexes of abelian groups exist degreewise. -/
noncomputable instance chainComplexAddCommGrpHasProducts :
    HasProducts.{0} (ChainComplex AddCommGrpCat.{0} ℕ) :=
  fun _ => inferInstance

/-- Ordinary chain complexes of abelian groups satisfy AB4*.

Exactness of a product-limit functor is checked after every degree evaluation. Evaluation commutes
with limits and preserves finite colimits, while the product-limit functor in `AddCommGrpCat` is
exact by the pinned AB4* instance.
-/
noncomputable instance chainComplexAddCommGrpAB4Star :
    AB4Star (ChainComplex AddCommGrpCat.{0} ℕ) where
  ofShape α := by
    let J := Discrete α
    refine { preservesFiniteColimits := ?_ }
    refine ⟨fun K _ _ => ?_⟩
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro i
    let E := HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.down ℕ) i
    exact preservesColimitsOfShape_of_natIso (preservesLimitNatIso E).symm

end LeanCategories.Homological
