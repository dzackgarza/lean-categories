/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.AdjointRootData
public import LeanCategories.AlgebraicGeometry.BorelSubgroupData

/-!
# Intersections of Borels through a torus

Definition-level realization of Humphreys FC16-C09-U008.

For a supplied torus subgroup, the source first intersects all Borel
subgroups containing it and then takes the identity component.  The subgroup
intersection is the native infimum in the complete lattice of subgroups.

The exterior roots are the nontrivial adjoint weights whose root spaces do
not lie in the supplied Lie submodule of that identity component.  Proving
the displayed direct-sum decomposition, identifying the supplied Lie
submodule with the Lie algebra of the point-set intersection construction,
and finiteness of the exterior-root set are result content and are not part
of Sweep III.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

section BorelIntersection

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The family of Borel subgroups containing a supplied torus subgroup. -/
def borelSubgroupsContainingData (T : Subgroup G) : Set (Subgroup G) :=
  {B | IsBorelSubgroup B ∧ T ≤ B}

/-- The intersection of all Borel subgroups containing a supplied torus. -/
def borelIntersectionSubgroupData (T : Subgroup G) : Subgroup G :=
  sInf (borelSubgroupsContainingData T)

/-- Humphreys' point-set carrier for I(T): the identity component of the
intersection of all Borel subgroups containing T. -/
noncomputable def torusBorelIntersectionIdentityComponentData
    (T : Subgroup G) : Set G :=
  subgroupIdentityComponentCarrier (borelIntersectionSubgroupData T)

end BorelIntersection

section ExteriorRoots

/-- The exterior roots relative to a supplied Lie submodule for I(T).

The root and root-space constructions are those of FC16-C06-U027.  The
source theorem that the Lie algebra of I(T) is a sum of complete root spaces
is what later turns this complement predicate into the displayed direct-sum
decomposition. -/
noncomputable def exteriorRootsData
    {K : Type u} [Field K] [IsAlgClosed K]
    (T : AffineAlgebraicGroup K) (𝔤 : Type u)
    [AddCommGroup 𝔤] [Module K 𝔤]
    (Ad : RationalRepresentationCoordinateData T 𝔤)
    (lieIntersection : Submodule K 𝔤) :
    Set (GroupLike K (AffineAlgebraicGroup.coordinateHopfAlgebra T)) :=
  {α |
    α ∈ rootsRelativeToDiagonalizableSubgroupData T 𝔤 Ad ∧
      ¬ adjointRootSpaceData T 𝔤 Ad α ≤ lieIntersection}

end ExteriorRoots

end LeanCategories.AlgebraicGeometry
