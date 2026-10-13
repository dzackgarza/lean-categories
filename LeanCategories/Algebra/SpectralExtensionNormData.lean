/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Spectral extension norm data

Serre, *Local Fields*, Chapter II (FC10-C02-U012).

For a finite extension of a nonarchimedean normed field, pinned Mathlib's
spectral norm is the raw absolute-value data from which the extension topology
is obtained.  Sweep III records that function only.

Multiplicativity, completeness, agreement with the base norm, and uniqueness
of the induced extension topology are result statements already separated from
the source construction.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v

variable (K : Type u) (L : Type v)
variable [NormedField K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Serre's norm defining the topology on a finite extension
(FC10-C02-U012), represented by the pinned spectral norm. -/
noncomputable abbrev serreFiniteExtensionNorm : L → ℝ :=
  spectralNorm K L

end LeanCategories.Algebra
