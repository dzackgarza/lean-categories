/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.RationalMapFunctionFieldData
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Degree data for morphisms of integral curves

Definition-level realization of the morphism-degree clause of Hartshorne
FC06-C02-U174.

For a finite morphism of integral curves `f : X ⟶ Y`, Hartshorne defines
`deg f = [K(X) : K(Y)]`.  The only nontrivial interface issue is obtaining the
canonical map `K(Y) → K(X)` from the scheme morphism.  The project already
records the proof-free core of that construction for rational maps in
`RationalMapFunctionFieldData`: the canonical pullback from the stalk at the
actual image of the function-field point, together with the exact generic-point
transport predicate.

This file therefore records:

* the dimension attached to any chosen function-field ring map;
* the proposition that this extension is finite-dimensional;
* the graph condition saying that a ring map is the pullback induced by the
  scheme morphism; and
* the exact graph of Hartshorne's morphism degree.

No generic-point, dominance, finiteness, or injectivity theorem is proved or
selected here.  For finite nonconstant curve morphisms those facts belong to
the preceding structure theorem FC06-C02-U173 / Sweep IV.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

/-- The vector-space dimension attached to a chosen map of function fields.

Hartshorne's degree uses this only when the extension is finite-dimensional;
that condition is recorded separately by `IsFiniteFunctionFieldExtensionData`.
-/
def functionFieldExtensionDegreeData
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y.functionField ⟶ X.functionField) : ℕ :=
  letI : Algebra Y.functionField X.functionField := φ.hom.toAlgebra
  Module.finrank Y.functionField X.functionField

/-- Proposition that a chosen function-field map makes `K(X)` a finite
extension of `K(Y)`. -/
def IsFiniteFunctionFieldExtensionData
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y.functionField ⟶ X.functionField) : Prop :=
  letI : Algebra Y.functionField X.functionField := φ.hom.toAlgebra
  Module.Finite Y.functionField X.functionField

/-- Exact graph condition for a scheme morphism to induce a chosen map of
function fields.

The equality identifying the image of the function-field point with the
generic point is existential data only; this declaration neither proves nor
chooses it. -/
def IsSchemeMorphismFunctionFieldPullbackData
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (φ : Y.functionField ⟶ X.functionField) : Prop :=
  ∃ h : rationalMapFunctionFieldImagePointData f.toRationalMap = genericPoint Y,
    φ =
      (Y.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫
        rationalMapFunctionFieldPullbackAtImageData f.toRationalMap

/-- Hartshorne's degree graph for a finite morphism of curves:
`d = [K(X) : K(Y)]` for the function-field map induced by `f`.

The predicate records finite-dimensionality rather than manufacturing it from
the geometric hypotheses. -/
def IsCurveMorphismDegreeData
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (d : ℕ) : Prop :=
  ∃ φ : Y.functionField ⟶ X.functionField,
    IsSchemeMorphismFunctionFieldPullbackData f φ ∧
      IsFiniteFunctionFieldExtensionData φ ∧
        d = functionFieldExtensionDegreeData φ

end LeanCategories.Schemes
