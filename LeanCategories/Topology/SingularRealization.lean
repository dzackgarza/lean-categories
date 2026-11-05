/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.SmashProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# The singular-realization source of a space

The adjunction `SSet.toTop ⊣ TopCat.toSSet` gives every topological space a canonical
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

/-- The based singular-realization source of a based space. -/
def basedSingularRealizationSource (X : BasedTop.{u}) : BasedTop.{u} :=
  Under.mk (TopCat.const (X := TopCat.of PUnit.{u + 1})
    (singularRealizationPoint X.right X.point))

@[simp] theorem basedSingularRealizationSource_point (X : BasedTop.{u}) :
    (basedSingularRealizationSource X).point = singularRealizationPoint X.right X.point := rfl

/-- The adjunction counit, as a based map out of the singular realization. -/
def basedSingularRealizationCounit (X : BasedTop.{u}) :
    basedSingularRealizationSource X ⟶ X :=
  Under.homMk (sSetTopAdj.counit.app X.right) (by
    apply TopCat.Hom.ext
    ext z
    cases z
    exact singularRealization_counit_point X.right X.point)

@[simp] theorem basedSingularRealizationCounit_right (X : BasedTop.{u}) :
    (basedSingularRealizationCounit X).right = sSetTopAdj.counit.app X.right := rfl

/-- The based counit is surjective on points. -/
theorem basedSingularRealizationCounit_surjective (X : BasedTop.{u}) :
    Function.Surjective (basedSingularRealizationCounit X).right.hom := by
  intro x
  exact ⟨singularRealizationPoint X.right x, singularRealization_counit_point X.right x⟩

/-- The singular-realization point map is injective. -/
theorem singularRealizationPoint_injective (X : TopCat.{u}) :
    Function.Injective (singularRealizationPoint X) := by
  intro x y h
  have h' := congrArg (fun z => sSetTopAdj.counit.app X z) h
  simpa only [singularRealization_counit_point] using h'

/-- The continuous map of a simplex into the realization of a simplicial set. This is the
simplex-map candidate for the cell structure; no cell decomposition is proved here. -/
def realizationSimplexMap (S : SSet.{u}) (n : ℕ) (σ : S _⦋n⦌) :
    C(stdSimplex ℝ (Fin (n + 1)), SSet.toTop.obj S) :=
  (SSet.toTop.map (SSet.yonedaEquiv.symm σ)).hom.comp
    (ContinuousMap.mk _
      (SimplexCategory.toTopHomeo ⦋n⦌).symm.continuous)

end LeanCategories.Topology
