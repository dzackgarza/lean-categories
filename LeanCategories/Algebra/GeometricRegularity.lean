/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Geometric regularity over a field

Weibel, *An Introduction to Homological Algebra*, Definition 9.3.12, pp. 311--318
(FC05-C09-U047).

Pinned Mathlib's `IsRegularRing` is exactly the source notion of a noetherian commutative ring whose
localization at every prime is regular local.  This file supplies the second definition in Weibel's
unit: geometric regularity after finite field extension.
-/

@[expose] public section

open scoped TensorProduct

namespace LeanCategories.Algebra

universe u v

/-- A commutative `k`-algebra is geometrically regular when every finite field extension `l/k`
has regular scalar extension `R ⊗[k] l`.

Source: Weibel, Definition 9.3.12, pp. 311--318 (FC05-C09-U047). -/
def IsGeometricallyRegularAlgebra
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] : Prop :=
  ∀ (l : Type u) [Field l] [Algebra k l] [FiniteDimensional k l],
    IsRegularRing (R ⊗[k] l)

end LeanCategories.Algebra
