/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Formal-cohomology comparison-map data

Definition-level realization of Hartshorne FC06-C03-U175.

For the theorem on formal functions, Hartshorne first has finite-stage maps

  (R^i f_* F)^∧_y → H^i(X_n, F_n)

compatible with the inverse-system transitions. Their compatibility induces a
single map from the completed stalk to the inverse limit of the finite-stage
cohomology modules.

Constructing a cone and applying limit.lift would require the compatibility
equations as proof arguments. Those equations come from the base-change and
restriction results preceding the construction and belong to the result layer.
Sweep III therefore keeps the finite-stage maps as data and characterizes the
comparison map by its composites with the native limit projections, without
selecting a morphism whose existence has not yet been established.

No compatibility theorem, cone construction, or isomorphism claim is made
here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace LeanCategories.Homological

universe u

/-- Presentation data for Hartshorne's formal-cohomology comparison map.

completedStalk is the completed stalk of the higher direct image in the source
application. cohomologySystem is the inverse system n ↦ H^i(X_n,F_n), and
toStage n is the composite to its nth stage. Compatibility of the stage maps is
deliberately not a proof field. -/
structure FormalCohomologyComparisonPresentationData
    (R : Type u) [CommRing R] (completedStalk : ModuleCat.{u} R) where
  cohomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} R
  toStage (n : ℕ) : completedStalk ⟶ cohomologySystem.obj (op n)

/-- The inverse-limit target of the formal-cohomology comparison. -/
abbrev formalCohomologyLimitData
    {R : Type u} [CommRing R] {completedStalk : ModuleCat.{u} R}
    (D : FormalCohomologyComparisonPresentationData R completedStalk) :
    ModuleCat.{u} R :=
  limit D.cohomologySystem

/-- Type of a candidate comparison map from the completed stalk to the inverse
limit of the finite-stage cohomology system. -/
abbrev FormalCohomologyComparisonHomData
    {R : Type u} [CommRing R] {completedStalk : ModuleCat.{u} R}
    (D : FormalCohomologyComparisonPresentationData R completedStalk) :=
  completedStalk ⟶ formalCohomologyLimitData D

/-- Exact projection graph for Hartshorne's comparison map.

The source compatibility statement is what makes the family toStage a cone.
Rather than proving that proposition in Sweep III, the desired map is
characterized by having precisely those finite-stage composites. -/
def IsFormalCohomologyComparisonData
    {R : Type u} [CommRing R] {completedStalk : ModuleCat.{u} R}
    (D : FormalCohomologyComparisonPresentationData R completedStalk)
    (φ : FormalCohomologyComparisonHomData D) : Prop :=
  ∀ n : ℕ, φ ≫ limit.π D.cohomologySystem (op n) = D.toStage n

end LeanCategories.Homological
