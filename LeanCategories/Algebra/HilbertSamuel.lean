/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Hilbert--Samuel function

Weibel, *An Introduction to Homological Algebra*, §9.3, pp. 311--318
(FC05-C09-U045).

Only the definition-layer data belongs here.  The eventual agreement with a degree-dimensional
Hilbert--Samuel polynomial and the regular-local criterion are theorem-level statements.
-/

@[expose] public section

open IsLocalRing

namespace LeanCategories.Algebra

universe u

/-- For a commutative local ring `(R,m)`, the Hilbert--Samuel function used by Weibel is
`n ↦ length_R(R / m^n)`.

Source: Weibel, §9.3, pp. 311--318 (FC05-C09-U045). -/
noncomputable def hilbertSamuelFunction (R : Type u) [CommRing R] [IsLocalRing R] : ℕ → ℕ∞ :=
  fun n => Module.length R (R ⧸ (maximalIdeal R) ^ n)

end LeanCategories.Algebra
