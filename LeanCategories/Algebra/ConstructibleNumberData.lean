/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Constructible real-number data

Definition-level carrier for Dummit--Foote FC01-C13-U035.
-/

@[expose] public section

namespace LeanCategories.Algebra

/-- A real subfield is closed under the nonnegative real square-root operation. -/
def IsSqrtClosedSubfield (K : Subfield ℝ) : Prop :=
  ∀ x : ℝ, x ∈ K → 0 ≤ x → Real.sqrt x ∈ K

/-- The constructible real-number field: the least real subfield containing
the fixed unit and closed under square roots.

The external Compass development identifies this algebraic carrier with signed
straightedge-and-compass lengths.  That geometric equivalence and the closure
theorems are result content; this definition records only the source carrier. -/
noncomputable def constructibleRealSubfield : Subfield ℝ :=
  sInf {K : Subfield ℝ | IsSqrtClosedSubfield K}

/-- The type of constructible real numbers. -/
noncomputable abbrev ConstructibleReal := constructibleRealSubfield

end LeanCategories.Algebra
