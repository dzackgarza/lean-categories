/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.HypersurfaceUnfoldingData
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The unfolding family over its discriminant complement

Supporting definition data for Peters--Sterk FC11-C18-U035, Version JUNE
2024, Section 18.2.C, printed pp. 335--336. The source takes monodromy on
the integral middle homology of a reference fibre over `U \ D_F`.

These definitions construct that base, the restricted zero-hypersurface
family and its projection, the reference fibre as an actual level-set
subspace, and its native integral singular homology. They reuse the
explicit source family from `HypersurfaceUnfoldingData`, with the
source-map ambiguity and unverified specialization recorded there.

No regularity or local-triviality result is asserted for arbitrary inputs.
Geometric parallel transport and its induced homology action are still
missing, so the module is not a construction of the monodromy group.
Neither a representation nor an abstract replacement fibre/module is
supplied by the caller. No action laws or other proofs are introduced.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

/-- The actual parameter neighbourhood with the constructed discriminant
removed. The notation does not assert smoothness for arbitrary data. -/
def hypersurfaceUnfoldingRegularBaseSetData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m)) :
    Set (HypersurfaceUnfoldingParameterData m) :=
  U \ hypersurfaceUnfoldingDiscriminantData f B V U

/-- Restrict the already constructed family to the discriminant complement.
Its native subtype topology is retained. -/
abbrev HypersurfaceUnfoldingRegularFamilyData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m)) : Type :=
  HypersurfaceUnfoldingTotalSpaceData f B V
    (hypersurfaceUnfoldingRegularBaseSetData f B V U)

/-- The parameter projection of the restricted family, reusing its owner. -/
def hypersurfaceUnfoldingRegularProjectionData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m)) :
    HypersurfaceUnfoldingRegularFamilyData f B V U →
      hypersurfaceUnfoldingRegularBaseSetData f B V U :=
  hypersurfaceUnfoldingProjectionData f B V
    (hypersurfaceUnfoldingRegularBaseSetData f B V U)

/-- The reference fibre inside the chosen source neighbourhood, at an
actual point of the constructed discriminant complement. -/
def hypersurfaceUnfoldingReferenceFiberSetData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m))
    (t : hypersurfaceUnfoldingRegularBaseSetData f B V U) :
    Set (MilnorCoordinateSpaceData n) :=
  {z | (z, t.1) ∈ V ∧ hypersurfaceUnfoldingFunctionData f B t.1 z = 0}

/-- The reference fibre with its native subspace topology. -/
abbrev HypersurfaceUnfoldingReferenceFiberData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m))
    (t : hypersurfaceUnfoldingRegularBaseSetData f B V U) : Type :=
  hypersurfaceUnfoldingReferenceFiberSetData f B V U t

/-- Apply native integral singular homology to the actual reference fibre.
The degree is the source's complex fibre dimension `n`, not `n + 1`. -/
def hypersurfaceUnfoldingReferenceHomologyData {n m : ℕ}
    (f : MilnorCoordinateSpaceData n → ℂ)
    (B : Fin m → Fin (n + 1) → ℕ)
    (V : Set (MilnorCoordinateSpaceData n × HypersurfaceUnfoldingParameterData m))
    (U : Set (HypersurfaceUnfoldingParameterData m))
    (t : hypersurfaceUnfoldingRegularBaseSetData f B V U) : ModuleCat.{0} ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (HypersurfaceUnfoldingReferenceFiberData f B V U t))

end LeanCategories.Topology
