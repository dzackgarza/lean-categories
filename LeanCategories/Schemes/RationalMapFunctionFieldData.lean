/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Definition-level adaptation of mattrobball/explicit-unirational,
Apache-2.0, revision 67477084d2f2ac7b8c397503d6aec66905a5d70a.
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Dominant
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Function-field pullback data for rational maps

Definition-level realization of Hartshorne FC06-C01-U075.

For a rational map `f : X ⤏ Y`, Mathlib already supplies the function-field
point `f.fromFunctionField : Spec K(X) ⟶ Y`.  Evaluating this point at the
closed point of `Spec K(X)` and applying `Scheme.stalkClosedPointTo` gives the
canonical ring map from the stalk at the actual image point into `K(X)`.

For a dominant map of integral schemes, the external reference proves that the
actual image point is the generic point of `Y`, and then transports this stalk
map to `K(Y) → K(X)`.  That generic-point equality, the resulting algebra-map
compatibility, and injectivity are result-layer statements.  Sweep III records
the canonical map before that transport and the exact predicate characterizing
the transported function-field map; it proves or selects none of those results.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

/-- The actual image in `Y` of the closed point of `Spec K(X)` under the
function-field point attached to a rational map. -/
def rationalMapFunctionFieldImagePointData
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⤏ Y) : Y :=
  f.fromFunctionField (IsLocalRing.closedPoint X.functionField)

/-- The stalk of `Y` at the actual image of the function-field point.

For a dominant rational map this is identified with `K(Y)` only after proving
that the image point is generic. -/
abbrev RationalMapFunctionFieldImageStalkData
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⤏ Y) : CommRingCat.{u} :=
  Y.presheaf.stalk (rationalMapFunctionFieldImagePointData f)

/-- Pullback by composition at the actual image stalk of a rational map.

This is the proof-free core of Hartshorne's `φ*`: it is the canonical stalk
map induced by `f.fromFunctionField`. -/
def rationalMapFunctionFieldPullbackAtImageData
    {X Y : Scheme.{u}} [IsIntegral X] (f : X ⤏ Y) :
    RationalMapFunctionFieldImageStalkData f ⟶ X.functionField :=
  Scheme.stalkClosedPointTo f.fromFunctionField

/-- Exact graph condition for a `K(Y) → K(X)` map to be the function-field
pullback induced by a dominant rational map.

The equality identifying the actual image point with the generic point occurs
only under the existential predicate.  No witness is supplied here: producing
one from dominance is the result proved by the external reference and belongs
to Sweep IV. -/
def IsRationalMapFunctionFieldPullbackData
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⤏ Y) [f.IsDominant]
    (φ : Y.functionField ⟶ X.functionField) : Prop :=
  ∃ h : rationalMapFunctionFieldImagePointData f = genericPoint Y,
    φ =
      (Y.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫
        rationalMapFunctionFieldPullbackAtImageData f

end LeanCategories.Schemes
