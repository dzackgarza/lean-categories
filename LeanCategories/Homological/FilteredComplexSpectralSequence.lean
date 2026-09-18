/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.FilteredComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Initial pages of the spectral sequence of a filtered complex

Weibel, *An Introduction to Homological Algebra*, Construction Theorem 5.4.1, pp. 131--134
(FC05-C05-U024).

For an increasing filtration `F` on a chain complex `C`, the associated graded complex in
filtration degree `p` is `F_p C / F_{p-1} C`.  Hence

`E⁰_{p,q} = (F_p C / F_{p-1} C)_{p+q}`

and

`E¹_{p,q} = H_{p+q}(F_p C / F_{p-1} C)`.

The construction of every later page and the proof that these data assemble canonically into a
spectral sequence are result-level content of Theorem 5.4.1 (and are made explicit by Weibel's
Construction 5.4.6); this file owns exactly the source-defined initial-page data.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u

variable (A : Type u) [Category.{v, u} A] [Abelian A]

namespace ChainComplexFiltration

variable {A : Type u} [Category.{v, u} A] [Abelian A] {K : ChainComplex A ℤ}

/-- The associated graded chain complex in filtration degree `p`,
`gr_p^F C = F_p C / F_{p-1} C`.

Source: Weibel, Construction Theorem 5.4.1 (FC05-C05-U024). -/
noncomputable def associatedGradedComplex (F : ChainComplexFiltration A (ComplexShape.down ℤ) K)
    (p : ℤ) : ChainComplex A ℤ :=
  cokernel (Subobject.ofLE (F.obj (p - 1)) (F.obj p) (F.monotone (by omega)))

end ChainComplexFiltration

end LeanCategories.Homological
