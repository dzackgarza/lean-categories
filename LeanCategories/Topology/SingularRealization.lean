/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# The singular-realization source of a space

The adjunction `TopCat.toSSet ⊣ SSet.toTop` gives every topological space a canonical
candidate source for a CW approximation: its singular realization `|Sing X|`, with the
adjunction counit as the structure map, and the point of `|Sing X|` obtained from the standard
zero-simplex.

What is proved here: the realization source, the vertex of `Sing X` at a point, the induced
point of the realization, and the fact that the counit sends that point to the original point.
No CW structure, no weak homotopy equivalence, and no approximation theorem is claimed or used;
`BasedCWApproximationCandidateData` and its predicate are untouched.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

noncomputable section

universe u

namespace LeanCategories.Topology

/-- The singular realization of a topological space, at the same universe. -/
abbrev singularRealizationSource (X : TopCat.{u}) : TopCat.{u} :=
  SSet.toTop.obj (TopCat.toSSet.obj X)

/-- The vertex of the singular set of `X` at a point, as a map out of `Δ[0]`. -/
def singularRealizationVertex (X : TopCat.{u}) (x : X) :
    (Δ[0] : SSet.{u}) ⟶ TopCat.toSSet.obj X :=
  sSetTopAdj.homEquiv _ X
    (TopCat.const (X := SSet.toTop.obj (Δ[0] : SSet.{u})) x)

/-- The point of the singular realization corresponding to a point of `X`. -/
def singularRealizationPoint (X : TopCat.{u}) (x : X) : singularRealizationSource X :=
  SSet.toTop.map (singularRealizationVertex X x)
    (default : SSet.toTop.obj (Δ[0] : SSet.{u}))

/-- The adjunction counit sends the singular-realization point of `x` to `x`. -/
theorem singularRealization_counit_point (X : TopCat.{u}) (x : X) :
    sSetTopAdj.counit.app X (singularRealizationPoint X x) = x := by
  have h := (sSetTopAdj.homEquiv (Δ[0] : SSet.{u}) X).symm_apply_apply
    (TopCat.const (X := SSet.toTop.obj (Δ[0] : SSet.{u})) x)
  rw [Adjunction.homEquiv_counit] at h
  exact ConcreteCategory.congr_hom h
    (default : SSet.toTop.obj (Δ[0] : SSet.{u}))

end LeanCategories.Topology
