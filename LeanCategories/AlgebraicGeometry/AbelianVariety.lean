/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian

/-!
# Abelian varieties

Definition-level reference port for Humphreys FC16-C02-U002.

The constructor data are ported from
`TauCeti/AlgebraicGeometry/AbelianVariety/Basic.lean::AbelianVariety` at
`74b1b2b2a25467497550234a92ddfc1322a5903f`.  An abelian variety is represented
as a proper geometrically integral group scheme over a field.  Over Humphreys'
algebraically closed ground field this is the scheme-theoretic form of the
complete algebraic group in the source.

Smoothness, connectedness, integrality, commutativity, rational-point data, and
base-change stability are theorem/result-layer consequences and are not ported
here.
-/

@[expose] public section

open CategoryTheory
open _root_.AlgebraicGeometry

namespace LeanCategories.AlgebraicGeometry

universe u

/-- An abelian variety over a field `K`: a proper geometrically integral group
scheme over `Spec K`. -/
structure AbelianVariety (K : Type u) [Field K] where
  /-- The underlying scheme over `Spec K`. -/
  toOver : Over (Spec (.of K))
  /-- The group-object structure on the underlying scheme. -/
  grpObj : GrpObj toOver
  /-- Completeness/properness of the structure morphism. -/
  isProper : IsProper toOver.hom
  /-- Geometric integrality of the underlying variety. -/
  geometricallyIntegral : GeometricallyIntegral toOver.hom

end LeanCategories.AlgebraicGeometry
