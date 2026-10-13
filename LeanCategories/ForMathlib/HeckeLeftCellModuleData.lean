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

This file records the construction layer of FC15-C07-U043.  Given the Kazhdan--Lusztig canonical
basis family and the left, right, or two-sided cell preorder, it forms the weakly-lower and
strictly-lower spans and their quotient.  The assertions that these spans are ideals, that the
quotients are free on the corresponding cell, and that the Hecke action descends to a left module,
right module, or bimodule are result-layer statements and are deliberately not bundled here.
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
    Submodule A (leftCellUpperSpan (A := A) canonicalBasis Z) :=
  (leftCellLowerSpan (A := A) canonicalBasis Z).comap
    (leftCellUpperSpan (A := A) canonicalBasis Z).subtype

/-- The scalar-module quotient underlying a prospective left-cell module. -/
def leftCellModuleCarrier (canonicalBasis : W → H) (Z : Set W) : Type _ :=
  (leftCellUpperSpan (A := A) canonicalBasis Z) ⧸
    (leftCellLowerInUpper (A := A) canonicalBasis Z)

section Relation

variable {A H W : Type*} [CommRing A] [AddCommGroup H] [Module A H]

/-- Elements weakly below a cell for an explicitly supplied preorder relation.

This relation-level form is useful for Kazhdan--Lusztig left, right, and
two-sided cell preorders without installing any one of them as the global
`Preorder W` instance. -/
def weaklyBelowCellBy (le : W → W → Prop) (Z : Set W) : Set W :=
  {x | ∃ z ∈ Z, le x z}

/-- Elements strictly below a cell for an explicitly supplied preorder
relation: weakly below some cell element but not conversely comparable. -/
def strictlyBelowCellBy (le : W → W → Prop) (Z : Set W) : Set W :=
  {x | ∃ z ∈ Z, le x z ∧ ¬ le z x}

/-- The scalar span of canonical-basis vectors weakly below `Z` for
the supplied cell preorder. -/
def cellUpperSpanBy (le : W → W → Prop) (canonicalBasis : W → H) (Z : Set W) :
    Submodule A H :=
  Submodule.span A (canonicalBasis '' weaklyBelowCellBy le Z)

/-- The scalar span of canonical-basis vectors strictly below `Z` for
the supplied cell preorder. -/
def cellLowerSpanBy (le : W → W → Prop) (canonicalBasis : W → H) (Z : Set W) :
    Submodule A H :=
  Submodule.span A (canonicalBasis '' strictlyBelowCellBy le Z)

/-- The strictly-lower span regarded as a submodule of the weakly-lower
span.  No ideal-stability assertion is bundled here. -/
def cellLowerInUpperBy (le : W → W → Prop) (canonicalBasis : W → H) (Z : Set W) :
    Submodule A (cellUpperSpanBy (A := A) le canonicalBasis Z) :=
  (cellLowerSpanBy (A := A) le canonicalBasis Z).comap
    (cellUpperSpanBy (A := A) le canonicalBasis Z).subtype

/-- The scalar quotient underlying the cell module for an explicitly
supplied cell preorder.

Passing the left, right, or two-sided Kazhdan--Lusztig preorder gives the
three quotient carriers in Humphreys FC15-C07-U043.  Stability of the spans
under the Hecke action, and hence the induced module or bimodule actions,
are proposition/result-layer statements. -/
def cellModuleCarrierBy (le : W → W → Prop) (canonicalBasis : W → H) (Z : Set W) :
    Type _ :=
  (cellUpperSpanBy (A := A) le canonicalBasis Z) ⧸
    (cellLowerInUpperBy (A := A) le canonicalBasis Z)

/-- The scalar quotient carrier attached to a left cell in FC15-C07-U043.

`leftLE` is the Kazhdan--Lusztig left-cell preorder supplied by the preceding
cell construction; no ideal-stability or descended Hecke action is asserted. -/
def leftCellModuleCarrierBy (leftLE : W → W → Prop) (canonicalBasis : W → H) (Z : Set W) :
    Type _ :=
  cellModuleCarrierBy (A := A) leftLE canonicalBasis Z

/-- The scalar quotient carrier attached to a right cell in FC15-C07-U043.

The right-module structure asserted by the source is result-layer data and is
not required to construct this quotient. -/
def rightCellModuleCarrierBy (rightLE : W → W → Prop) (canonicalBasis : W → H) (Z : Set W) :
    Type _ :=
  cellModuleCarrierBy (A := A) rightLE canonicalBasis Z

/-- The scalar quotient carrier attached to a two-sided cell in FC15-C07-U043.

The source's induced Hecke bimodule structure is a subsequent result; this
declaration records only the defining span quotient. -/
def twoSidedCellBimoduleCarrierBy (twoSidedLE : W → W → Prop)
    (canonicalBasis : W → H) (Z : Set W) : Type _ :=
  cellModuleCarrierBy (A := A) twoSidedLE canonicalBasis Z

end Relation

end LeanCategories.Hecke
