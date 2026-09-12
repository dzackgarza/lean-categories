/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SpectralSequenceConvergence
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Filtered chain complexes

Weibel, *An Introduction to Homological Algebra*, §5.4, p. 131 (FC05-C05-U022).

A filtration of a chain complex is an increasing family of chain subcomplexes.  A chain subcomplex
is represented categorically by a `Subobject` of the `HomologicalComplex`, so the generic
`IncreasingFiltration` owner already contains exactly the source data and is reused here rather than
reimplemented degreewise.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u w

variable (A : Type u) [Category.{v, u} A] [HasZeroMorphisms A]
variable {ι : Type w} (c : ComplexShape ι)

/-- A filtration `… ⊆ F_{p-1}C ⊆ F_pC ⊆ …` of a chain complex by chain subcomplexes.
Source: Weibel, *An Introduction to Homological Algebra*, §5.4, p. 131. -/
abbrev ChainComplexFiltration (K : HomologicalComplex A c) :=
  IncreasingFiltration K

end LeanCategories.Homological
