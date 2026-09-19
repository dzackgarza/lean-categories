/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

/-!
# Generic span and quotient helpers for left-cell modules

Humphreys, *Reflection Groups and Coxeter Groups*, Section 7.15, pp. 169--170
(FC15-C07-U043), forms two spans in the Hecke algebra from a left cell `Z`: the span of canonical
basis elements weakly below `Z`, and the span of those strictly below `Z`. The left-cell module is
their quotient.

This file records generic set, span, and underlying `A`-module quotient operations for a supplied
preorder and family of vectors. It does not by itself realize FC15-C07-U043: that unit uses the
specific Kazhdan--Lusztig basis and left-cell preorder, and its quotient carries the Hecke-module
action induced by the two spans being left ideals. The canonical basis, ideal stability, free basis
indexed by `Z`, Hecke action, and right-cell and two-sided analogues are absent here.
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

/-- The scalar-module quotient underlying a prospective left-cell module. -/
def leftCellModuleCarrier (canonicalBasis : W → H) (Z : Set W) : Type _ :=
  (leftCellUpperSpan canonicalBasis Z) ⧸ (leftCellLowerInUpper canonicalBasis Z)

end LeanCategories.Hecke
