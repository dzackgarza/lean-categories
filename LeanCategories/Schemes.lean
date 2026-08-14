/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import LeanCategories.Schemes.Coherent
public import LeanCategories.Schemes.Divisors
public import LeanCategories.Schemes.Properties
public import LeanCategories.Schemes.Spectra
public import LeanCategories.Schemes.Varieties

/-!
# Scheme routes

Mathlib owns schemes over a base, pullback base change, scheme-theoretic fibers,
residue fields, module sheaves, and quasi-coherent module sheaves. This module
exposes those declarations without a parallel namespace or wrapper layer.
-/

@[expose] public section
