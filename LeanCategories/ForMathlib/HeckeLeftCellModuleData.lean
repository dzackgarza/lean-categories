/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# Underlying modules of left-cell modules

Humphreys, *Reflection Groups and Coxeter Groups*, Section 7.15, pp. 169--170
(FC15-C07-U043), forms two spans in the Hecke algebra from a left cell `Z`: the span of canonical
basis elements weakly below `Z`, and the span of those strictly below `Z`. The left-cell module is
their quotient.

This file records the two spans and the underlying `A`-module quotient. Their stability under the
Hecke action, the basis indexed by `Z`, and the resulting representation are subsequent results.
-/

namespace LeanCategories.Hecke

variable {A H W : Type*} [CommRing A] [AddCommGroup H] [Module A H] [Preorder W]

/-- Elements weakly below some member of the left cell `Z` in the left preorder. -/
def weaklyBelowCell (Z : Set W) : Set W :=
  {x | ∃ z ∈ Z, x ≤ z}

/-- Elements strictly below the left cell `Z` in the left preorder. -/
def strictlyBelowCell (Z : Set W) : Set W :=
  {x | ∃ z ∈ Z, x < z}

/-- The span of canonical-basis elements weakly below `Z`. -/
def leftCellUpperSpan (canonicalBasis : W → H) (Z : Set W) : Submodule A H :=
  Submodule.span A (canonicalBasis '' weaklyBelowCell Z)

/-- The span of canonical-basis elements strictly below `Z`. -/
def leftCellLowerSpan (canonicalBasis : W → H) (Z : Set W) : Submodule A H :=
  Submodule.span A (canonicalBasis '' strictlyBelowCell Z)

/-- The lower span, regarded as a submodule of the weakly-lower span. -/
def leftCellLowerInUpper (canonicalBasis : W → H) (Z : Set W) :
    Submodule A (leftCellUpperSpan canonicalBasis Z) :=
  (leftCellLowerSpan canonicalBasis Z).comap (leftCellUpperSpan canonicalBasis Z).subtype

/-- The underlying `A`-module of Humphreys' left-cell module. -/
def leftCellModule (canonicalBasis : W → H) (Z : Set W) : Type _ :=
  (leftCellUpperSpan canonicalBasis Z) ⧸ (leftCellLowerInUpper canonicalBasis Z)

end LeanCategories.Hecke
