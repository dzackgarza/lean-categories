/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Cyclic two-periodic resolution data

Definition-level realization of Serre FC10-C08-U021.

For a finite cyclic group `G = ⟨s⟩`, Serre writes

* `D = s - 1`,
* `N = ∑ g ∈ G, g`,
* one copy of `ℤ[G]` in every degree, with differential alternating
  between right multiplication by `D` and `N`, and
* `K(A) = K ⊗_{ℤ[G]} A`.

This file records exactly those objects and maps.  The identities
`DN = ND = 0`, square-zero of the alternating differential, exactness of the
resolution, and comparison with Tate cohomology are result content and are not
proved or bundled here.
-/

@[expose] public noncomputable section

open scoped BigOperators TensorProduct

namespace LeanCategories.Homological

variable {G : Type} [Group G] [Fintype G] [IsCyclic G]

/-- The integral group ring `ℤ[G]` used in Serre's periodic resolution. -/
abbrev cyclicPeriodicGroupRingData :=
  MonoidAlgebra ℤ G

/-- A selected generator `s` of the finite cyclic group. -/
def cyclicPeriodicGeneratorData : G :=
  Classical.choose (IsCyclic.exists_generator (α := G))

/-- Serre's group-ring element `D = s - 1`. -/
def cyclicDifferenceElementData : cyclicPeriodicGroupRingData (G := G) :=
  MonoidAlgebra.single cyclicPeriodicGeneratorData 1 -
    MonoidAlgebra.single 1 1

/-- Serre's norm element `N = ∑_{g ∈ G} g` in `ℤ[G]`. -/
def cyclicNormElementData : cyclicPeriodicGroupRingData (G := G) :=
  ∑ g : G, MonoidAlgebra.single g 1

/-- The degree-`n` carrier of Serre's periodic resolution: one copy of
`ℤ[G]` in every degree. -/
abbrev cyclicPeriodicResolutionDegreeData (_n : ℤ) :=
  cyclicPeriodicGroupRingData (G := G)

/-- The raw alternating differential of the periodic resolution.

At even degree this is right multiplication by `D`; at odd degree it is
right multiplication by `N`.  No assertion that consecutive maps compose
to zero is included. -/
def cyclicPeriodicResolutionDifferentialData (n : ℤ) :
    cyclicPeriodicResolutionDegreeData (G := G) n →ₗ[
      cyclicPeriodicGroupRingData (G := G)]
      cyclicPeriodicResolutionDegreeData (G := G) (n + 1) :=
  if Even n then
    LinearMap.mulRight
      (cyclicPeriodicGroupRingData (G := G))
      cyclicDifferenceElementData
  else
    LinearMap.mulRight
      (cyclicPeriodicGroupRingData (G := G))
      cyclicNormElementData

/-- The degree-`n` carrier of Serre's coefficient complex
`K(A) = K ⊗_{ℤ[G]} A`.

Cyclicity supplies the commutative group structure needed by Mathlib's
commutative-base tensor product. -/
def cyclicPeriodicCoefficientDegreeData
    (A : Rep ℤ G) (n : ℤ) : Type :=
  letI : CommGroup G := IsCyclic.commGroup
  TensorProduct
    (MonoidAlgebra ℤ G)
    (cyclicPeriodicResolutionDegreeData (G := G) n)
    (Rep.toModuleMonoidAlgebra.obj A)

/-- The differential on `K(A)`, induced from the raw periodic resolution by
tensoring its alternating `D/N` map with the identity of `A`.

Square-zero and comparison with the explicit Tate complex remain theorem-layer
statements. -/
def cyclicPeriodicCoefficientDifferentialData
    (A : Rep ℤ G) (n : ℤ) :
    cyclicPeriodicCoefficientDegreeData A n →
      cyclicPeriodicCoefficientDegreeData A (n + 1) :=
  letI : CommGroup G := IsCyclic.commGroup
  TensorProduct.map
    (cyclicPeriodicResolutionDifferentialData (G := G) n)
    LinearMap.id

end LeanCategories.Homological
