/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.MulAction

/-!
# Discrete modules over a profinite group

Weibel, *An Introduction to Homological Algebra*, Definition 6.11.8, pp. 206--215
(FC05-C06-U141).

For a profinite group `G`, a discrete `G`-module is a `G`-module whose action is continuous after
giving the module the discrete topology.  Mathlib proves in
`continuousSMul_iff_stabilizer_isOpen` that this is equivalent to every point stabilizer being
open.  We use that topology-free equivalent condition as the defining predicate on `Rep ℤ G` and
bundle it for later use by the category `C_G`.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u

/-- The source condition for a discrete module over a profinite group: every element has open
stabilizer.  By Mathlib's `continuousSMul_iff_stabilizer_isOpen`, this is equivalent to continuity
of the action when the module carries the discrete topology.

Source: Weibel, Definition 6.11.8, pp. 206--215 (FC05-C06-U141). -/
def IsDiscreteProfiniteModule (G : ProfiniteGrp.{u}) (A : Rep.{u} ℤ G) : Prop :=
  ∀ a : A, IsOpen {g : G | A.ρ g a = a}

/-- A `ℤ[G]`-module satisfying Weibel's discrete-module condition.

Source: Weibel, Definition 6.11.8, pp. 206--215 (FC05-C06-U141). -/
structure DiscreteProfiniteModule (G : ProfiniteGrp.{u}) where
  /-- The underlying `G`-module. -/
  toRep : Rep.{u} ℤ G
  /-- Every element has open stabilizer. -/
  isDiscrete : IsDiscreteProfiniteModule G toRep

end LeanCategories.Homological
