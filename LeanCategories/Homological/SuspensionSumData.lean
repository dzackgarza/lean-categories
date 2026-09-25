/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.Prespectrum
public import LeanCategories.Topology.WedgeSum

/-!
# Pinch sums of maps from a reduced suspension

Definition-level realization of Hatcher FC07-C04-U076.

For based maps `f,g : ΣX → K`, Hatcher defines their sum by pinching the
equator of the reduced suspension to obtain `ΣX ∨ ΣX`, then applying `f`
and `g` on the two wedge summands.

Sweep III records the quotient-level pinch and wedge-recursion maps through
their exact representative graphs.  Continuity, compatibility with the
quotient relations/basepoints, projection homotopies, and descent to based
homotopy classes are result-layer statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open LeanCategories.Topology

universe u

/-- The binary wedge of two copies of the reduced suspension of `X`. -/
abbrev SuspensionBinaryWedge (X : BasedTop.{u}) :=
  Wedge
    (fun _ : Bool => Suspension X)
    (fun _ : Bool => suspensionPoint X)

/-- The common wedge point in `ΣX ∨ ΣX`. -/
def suspensionBinaryWedgePoint (X : BasedTop.{u}) :
    SuspensionBinaryWedge X :=
  wedgeMk
    (fun _ : Bool => Suspension X)
    (fun _ : Bool => suspensionPoint X)
    false
    (suspensionPoint X)

/-- Exact representative formula for Hatcher's equatorial pinch
`ΣX → ΣX ∨ ΣX`.

The lower half of the suspension cylinder is rescaled onto the first summand
and the upper half onto the second.  At the equator the formula lands at an
endpoint of a reduced suspension, hence at the common wedge point. -/
def IsReducedSuspensionPinchData
    (X : BasedTop.{u})
    (pinch : Suspension X → SuspensionBinaryWedge X) : Prop :=
  ∀ (t : unitInterval) (x : X.right),
    pinch (Quotient.mk (suspensionSetoid X) (t, x)) =
      if (t : ℝ) ≤ 1 / 2 then
        wedgeMk
          (fun _ : Bool => Suspension X)
          (fun _ : Bool => suspensionPoint X)
          false
          (Quotient.mk (suspensionSetoid X)
            (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ)), x))
      else
        wedgeMk
          (fun _ : Bool => Suspension X)
          (fun _ : Bool => suspensionPoint X)
          true
          (Quotient.mk (suspensionSetoid X)
            (Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1), x))

/-- Hatcher's equatorial pinch, selected from its exact representative
formula.  Quotient well-definedness and continuity are not proved here. -/
def reducedSuspensionPinchData
    (X : BasedTop.{u}) : Suspension X → SuspensionBinaryWedge X :=
  letI : Nonempty (SuspensionBinaryWedge X) :=
    ⟨suspensionBinaryWedgePoint X⟩
  Classical.epsilon (IsReducedSuspensionPinchData X)

/-- Exact source specification for the map out of the binary wedge that is
`f` on the first summand and `g` on the second. -/
def IsSuspensionWedgeRecData
    {X K : BasedTop.{u}}
    (f g : suspensionObj X ⟶ K)
    (r : SuspensionBinaryWedge X → K.right) : Prop :=
  (∀ z : Suspension X,
    r (wedgeMk
      (fun _ : Bool => Suspension X)
      (fun _ : Bool => suspensionPoint X)
      false z) = f.right z) ∧
  ∀ z : Suspension X,
    r (wedgeMk
      (fun _ : Bool => Suspension X)
      (fun _ : Bool => suspensionPoint X)
      true z) = g.right z

/-- The wedge-recursion function determined by `f` and `g`, selected from
the source summand formulas. -/
def suspensionWedgeRecData
    {X K : BasedTop.{u}}
    (f g : suspensionObj X ⟶ K) :
    SuspensionBinaryWedge X → K.right :=
  letI : Nonempty K.right := ⟨K.point⟩
  Classical.epsilon (IsSuspensionWedgeRecData f g)

/-- Hatcher's sum of two based maps from a reduced suspension, as the raw
composite of the equatorial pinch with the wedge-recursion function.

That this raw function is continuous and based, and that it descends to the
sum operation on based homotopy classes, are Sweep-IV assertions. -/
def suspensionMapSumData
    {X K : BasedTop.{u}}
    (f g : suspensionObj X ⟶ K) :
    Suspension X → K.right :=
  fun z => suspensionWedgeRecData f g (reducedSuspensionPinchData X z)

end LeanCategories.Homological
