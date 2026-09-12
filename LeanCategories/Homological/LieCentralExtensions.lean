/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Extension
public import Mathlib.Algebra.Lie.Solvable

/-!
# Central extensions of Lie algebras

Weibel, *An Introduction to Homological Algebra* (1994), §7.9, pp. 248--253
(FC05-C07-U067).

Mathlib already bundles short exact Lie algebra extensions.  This file adds
Weibel's centrality and universality predicates and the definition of a perfect
Lie algebra.  Existence and recognition theorems for universal central extensions
belong to later source units.
-/

@[expose] public section

namespace LeanCategories.Homological

open LieAlgebra

universe u v w

variable (R : Type u) [CommRing R]

/-- A Lie algebra is perfect when it equals its commutator ideal. -/
def IsPerfectLieAlgebra (L : Type v) [LieRing L] [LieAlgebra R L] : Prop :=
  LieAlgebra.derivedSeries R L 1 = ⊤

variable {N G : Type v} [LieRing N] [LieAlgebra R N]
  [LieRing G] [LieAlgebra R G]

/-- A Lie algebra extension is central when the image of its kernel lies in
the center of the middle Lie algebra. -/
def IsCentralLieExtension (X : LieAlgebra.Extension.{u, v, v, w} R N G) : Prop :=
  X.incl.range ≤ LieAlgebra.center R X.L

/-- A central extension is universal when it has a unique map over the target
to every central extension of that target. -/
def IsUniversalCentralLieExtension
    (X : LieAlgebra.Extension.{u, v, v, w} R N G) : Prop :=
  IsCentralLieExtension R X ∧
    ∀ (N' : Type v) [LieRing N'] [LieAlgebra R N']
      (Y : LieAlgebra.Extension.{u, v, v, w} R N' G),
      IsCentralLieExtension R Y →
        ∃! f : X.L →ₗ⁅R⁆ Y.L, Y.proj.comp f = X.proj

end LeanCategories.Homological
