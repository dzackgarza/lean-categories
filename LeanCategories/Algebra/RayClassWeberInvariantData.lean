/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.GlobalRayClassData
public import LeanCategories.Algebra.WeberFunctionData
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Ray-class Weber-invariant source data

Definition-level realization of Neukirch FC09-C06-U072.

This file records the ray-class fibre and representative-level Weber
evaluation from the source. Choice-independence and quotient descent are
result-layer statements and are not asserted here.
-/

@[expose] public noncomputable section

open IsDedekindDomain NumberField

namespace LeanCategories.Algebra

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The fibre of ray classes mapping to the ordinary class
`modulusClass * chosenClass⁻¹`. -/
def rayClassWeberFiberData
    (m : GlobalRayModulusData K)
    (rayToClass : GlobalRayClassGroupCarrierData K m → ClassGroup (𝓞 K))
    (modulusClass chosenClass : ClassGroup (𝓞 K)) :
    Set (GlobalRayClassGroupCarrierData K m) :=
  {c | rayToClass c = modulusClass * chosenClass⁻¹}

/-- Raw complex evaluation data selected from a representative of one ray
class in the fibre. -/
structure RayClassWeberEvaluationData where
  /-- The chosen ideal lattice, from which the Weber function is now
  constructed intrinsically. -/
  weberLattice : Submodule ℤ ℂ
  /-- Complex image of the chosen principal generator. -/
  argument : ℂ

/-- The representative-level value `tau_a(a)`. -/
def rayClassWeberRepresentativeValueData
    (D : RayClassWeberEvaluationData) : ℂ :=
  weberFunctionData D.weberLattice D.argument

/-- Source-level representative choices for the ray classes in the fibre. -/
abbrev RayClassWeberChoiceData
    (m : GlobalRayModulusData K)
    (rayToClass : GlobalRayClassGroupCarrierData K m → ClassGroup (𝓞 K))
    (modulusClass chosenClass : ClassGroup (𝓞 K)) :=
  rayClassWeberFiberData K m rayToClass modulusClass chosenClass →
    RayClassWeberEvaluationData

/-- The source notation for the Weber value, evaluated from supplied
representative choices. Independence from those choices remains result work. -/
def rayClassWeberInvariantData
    (m : GlobalRayModulusData K)
    (rayToClass : GlobalRayClassGroupCarrierData K m → ClassGroup (𝓞 K))
    (modulusClass chosenClass : ClassGroup (𝓞 K))
    (choice : RayClassWeberChoiceData K m rayToClass modulusClass chosenClass)
    (c : rayClassWeberFiberData K m rayToClass modulusClass chosenClass) : ℂ :=
  rayClassWeberRepresentativeValueData (choice c)

end LeanCategories.Algebra
