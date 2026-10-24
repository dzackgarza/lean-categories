/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.PrimeResidueFields
public import LeanCategories.Catalogue.Semantics.Modules.IntegerResidueModules
public import LeanCategories.Catalogue.Semantics.Algebra.SuccessorSeries
public import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ModuleKernelRestriction
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ChangeValueLifts
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneFactorization
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ChangeValueComparisons
public import LeanCategories.Catalogue.Semantics.Foundation.CoreIsomorphisms
public import LeanCategories.Catalogue.Semantics.Algebra.AutomorphismArrows

/-!
# Independently authored scalar, carrier, series and formed-restriction extensions

Public import root for prime residue fields, restriction of regular modules
along selected ring maps, the full successor-coefficient power-series family,
rectangular matrix maps, restrictions of selected forms to ordinary module
kernels, and cartesian lifts along changes of value module. It also imports
the fixed rational planes and cone arrows with their exact forms, vector
actions, comparison maps and factorization laws.

The declaration docstrings in these modules specify the selected carriers,
scalar and value modules, pairings, dependent parameters, and complete arrow
actions. The constructions and their formal laws remain at their existing
mathematical owners; this file only reexports the additive modules.

The complete comparison/input interfaces additionally expose both directions
of the general change-of-values pullback comparison, specified set isomorphisms
as core arrows (including the complete finite reversal), and the actual arrows
and functorial evaluation of automorphism elements. Their public signatures
are documented in the adjacent `InterfaceCompletion.md`.
-/
