/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# The unit-circle total space of the tautological line over the complex projective line

Peters--Sterk, *Symmetric and Quadratic Forms* (June 2024), Chapter 4, source line 2962
(`FC11-C04-U048`), define the fiber of the tautological line over a point of the complex
projective line to be the represented line in `ℂ²`. They then form `X(-1)` from the unit circles
in those fibers.

`Projectivization.submodule` is Mathlib's existing owner for the represented line. The total
space below is a subtype of the product of the projective line and Hermitian `ℂ²`, so it inherits
the subspace topology of the product. The source's identifications of the base with `S²` and the
total space with `S³` are separate statements and are not asserted here.
-/

@[expose] public section

namespace LeanCategories.ForMathlib

/-- The complex projective line, using Hermitian `ℂ²` as its coordinate space. -/
abbrev ComplexProjectiveLine := Projectivization ℂ (EuclideanSpace ℂ (Fin 2))

/-- The quotient topology from the nonzero vectors in Hermitian `ℂ²`. -/
instance : TopologicalSpace ComplexProjectiveLine :=
  inferInstanceAs (TopologicalSpace
    (Quotient (projectivizationSetoid ℂ (EuclideanSpace ℂ (Fin 2)))))

/-- The total space formed by the unit circles in the fibers of the tautological line over
the complex projective line.

A point is a projective line `p` together with a unit vector in the one-dimensional subspace
`p.submodule`. The topology is the subtype topology inherited from
`ComplexProjectiveLine × EuclideanSpace ℂ (Fin 2)`.
-/
def TautologicalUnitCircleBundle :=
  {x : ComplexProjectiveLine × EuclideanSpace ℂ (Fin 2) //
    x.2 ∈ x.1.submodule ∧ ‖x.2‖ = 1}

/-- The subspace topology on the unit-circle total space. -/
instance : TopologicalSpace TautologicalUnitCircleBundle :=
  TopologicalSpace.induced Subtype.val inferInstance

/-- Projection of the tautological unit-circle total space to the complex projective line. -/
def tautologicalUnitCircleProjection :
    ContinuousMap TautologicalUnitCircleBundle ComplexProjectiveLine where
  toFun x := x.1.1
  continuous_toFun := continuous_fst.comp continuous_subtype_val

end LeanCategories.ForMathlib
