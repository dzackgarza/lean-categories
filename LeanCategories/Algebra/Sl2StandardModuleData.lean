/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Data.Matrix.Basic

/-!
# Coordinate data for the standard irreducible sl₂ modules

Definition-level realization of Humphreys FC14-C02-U050.

For `m : ℕ`, the source constructs `V(m)` on the coordinate space with basis
`v₀, …, vₘ` and prescribes the raising, lowering, and Cartan actions by the
usual ladder formulas.  This file records exactly that vector-space carrier
and the three matrices.

Showing that these matrices satisfy the sl₂ relations, assembling the
resulting Lie-module structure, and proving irreducibility are result-layer
obligations and are not part of Sweep III.
-/

@[expose] public section

namespace LeanCategories.Algebra

universe u

variable (K : Type u) [CommRing K]

/-- Humphreys' coordinate carrier for `V(m)`, with basis indexed by
`0, …, m`. -/
abbrev Sl2StandardModuleData (m : ℕ) := Fin (m + 1) → K

/-- Matrix of the raising operator `e` in the source basis:
`e • v_j = j • v_{j-1}`. -/
def sl2StandardRaiseMatrix (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => if (j : ℕ) = (i : ℕ) + 1 then ((j : ℕ) : K) else 0

/-- Matrix of the lowering operator `f` in the source basis:
`f • v_j = (m-j) • v_{j+1}`. -/
def sl2StandardLowerMatrix (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => if (i : ℕ) = (j : ℕ) + 1 then (m : K) - ((j : ℕ) : K) else 0

/-- Matrix of the Cartan operator `h` in the source basis:
`h • v_i = (m-2i) • v_i`. -/
def sl2StandardDiagMatrix (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => if i = j then (m : K) - 2 * ((i : ℕ) : K) else 0

end LeanCategories.Algebra
