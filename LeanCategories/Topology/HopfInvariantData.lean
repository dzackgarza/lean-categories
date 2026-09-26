/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.CohomologyRingData
public import LeanCategories.Topology.MappingConeData
public import Mathlib.Topology.Category.TopCat.Sphere

/-!
# Hopf-invariant definition data

Definition-level realization of Hatcher FC07-C04-U106, ported from the
pinned Cubical Agda Hopf-invariant construction.

For n >= 2 and f : S^(2n-1) -> S^n, Hatcher chooses a generator alpha in
H^n(C_f; Z) and the oriented top-cell generator beta in H^(2n)(C_f; Z).
The Hopf invariant is the integer H satisfying alpha cup alpha = H beta.

Cubical realizes the same convention by normalizing alpha and beta to 1
under explicit cohomology-group isomorphisms; its beta is constructed from
the connecting map applied to the standard oriented sphere generator.

Sweep III records the normalized generator data and the defining coefficient
relation only. Existence of those generators and normalizations, the
mapping-cone cohomology calculation, uniqueness of the coefficient,
independence of the sign of alpha, and descent to homotopy classes are result
content and are not proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open CategoryTheory

/-- Hatcher's mapping cone C_f for a sphere map f : S^(2n-1) -> S^n. -/
abbrev hopfMappingConeData {n : ℕ}
    (f : TopCat.sphere.{0} (2 * n - 1) ⟶ TopCat.sphere.{0} n) : TopCat.{0} :=
  TopCat.of (MappingCone f.hom)

/-- Integral singular cohomology of the mapping cone in degree k. -/
abbrev hopfMappingConeCohomologyData {n : ℕ}
    (f : TopCat.sphere.{0} (2 * n - 1) ⟶ TopCat.sphere.{0} n) (k : ℕ) :
    ModuleCat.{0} ℤ :=
  singularCohomologyModuleData ℤ (hopfMappingConeData f) (ModuleCat.of ℤ ℤ) k

/-- A chosen cohomology generator normalized to 1.

For alpha this is the degree-n generator. Its sign is immaterial to alpha^2,
but the normalization is retained because it is part of the checked Cubical
presentation. -/
structure HopfCohomologyGeneratorData {n : ℕ}
    (f : TopCat.sphere.{0} (2 * n - 1) ⟶ TopCat.sphere.{0} n) (k : ℕ) where
  value : hopfMappingConeCohomologyData f k
  coordinate : (hopfMappingConeCohomologyData f k : Type) ≃ₗ[ℤ] ℤ
  coordinate_value : coordinate value = 1

/-- The oriented top-cell generator beta in H^(2n)(C_f; Z).

The source orientation convention is explicit data here. The theorem layer
constructs this datum from the oriented top cell, equivalently from the
connecting map applied to the standard sphere generator as in Cubical.
Reversing this datum reverses the sign of the Hopf invariant. -/
structure HopfTopCellGeneratorData {n : ℕ}
    (f : TopCat.sphere.{0} (2 * n - 1) ⟶ TopCat.sphere.{0} n) where
  value : hopfMappingConeCohomologyData f (n + n)
  coordinate : (hopfMappingConeCohomologyData f (n + n) : Type) ≃ₗ[ℤ] ℤ
  coordinate_value : coordinate value = 1

/-- Hatcher's defining cup-square relation for the Hopf invariant. -/
def IsHopfInvariantCoefficientData {n : ℕ}
    (f : TopCat.sphere.{0} (2 * n - 1) ⟶ TopCat.sphere.{0} n)
    (cup : SingularCohomologyCupData ℤ (hopfMappingConeData f))
    (alpha : HopfCohomologyGeneratorData f n)
    (beta : HopfTopCellGeneratorData f) (H : ℤ) : Prop :=
  singularCohomologyCupMulData ℤ (hopfMappingConeData f) cup
      alpha.value alpha.value = H • beta.value

/-- Source-faithful Hopf invariant coefficient data determined by normalized
generators and supplied valid cup-product data.

Existence and uniqueness of an integer satisfying the relation are deferred
to Sweep IV; no arbitrary coefficient is selected. -/
abbrev HopfInvariantData {n : ℕ} (_hn : 2 ≤ n)
    (f : TopCat.sphere.{0} (2 * n - 1) ⟶ TopCat.sphere.{0} n)
    (cup : SingularCohomologyCupData ℤ (hopfMappingConeData f))
    (alpha : HopfCohomologyGeneratorData f n)
    (beta : HopfTopCellGeneratorData f) :=
  {H : ℤ // IsHopfInvariantCoefficientData f cup alpha beta H}

end LeanCategories.Topology
