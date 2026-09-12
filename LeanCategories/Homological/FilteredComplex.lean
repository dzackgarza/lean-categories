/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SpectralSequenceConvergence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Filtered chain complexes

Weibel, *An Introduction to Homological Algebra*, §5.4, p. 131 (FC05-C05-U022).

A filtration of a chain complex is an increasing family of chain subcomplexes.  A chain subcomplex
is represented categorically by a `Subobject` of the `HomologicalComplex`, so the generic
`IncreasingFiltration` owner already contains exactly the source data and is reused here rather than
reimplemented degreewise.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

universe v u w

variable (A : Type u) [Category.{v, u} A] [Abelian A]
variable {ι : Type w} (c : ComplexShape ι)

/-- A filtration `… ⊆ F_{p-1}C ⊆ F_pC ⊆ …` of a chain complex by chain subcomplexes.
Source: Weibel, *An Introduction to Homological Algebra*, §5.4, p. 131. -/
abbrev ChainComplexFiltration (K : HomologicalComplex A c) :=
  IncreasingFiltration K

namespace ChainComplexFiltration

variable {A c} {K : HomologicalComplex A c}

/-- An exhaustive filtration, i.e. `C = ⋃ₚ FₚC` in the source notation.  Categorically this says
that the filtered chain subcomplexes have the whole complex as their least upper bound.
Source: Weibel, *An Introduction to Homological Algebra*, §5.4, p. 131. -/
abbrev IsExhaustive (F : ChainComplexFiltration A c K) : Prop :=
  IncreasingFiltration.IsExhaustive F

/-- The degree-`n` object `(FₚC)ₙ` of the `p`th chain subcomplex. -/
abbrev degreeObject (F : ChainComplexFiltration A c K) (p : ℤ) (n : ι) : A :=
  (Subobject.underlying.obj (F.obj p)).X n

/-- A bounded filtration: in each chain degree `n`, some lower filtration term is zero and some
strictly later filtration term is all of `Cₙ`.  Source: Weibel, *An Introduction to Homological
Algebra*, Definition 5.4.2, p. 132. -/
def IsBounded (F : ChainComplexFiltration A c K) : Prop :=
  ∀ n : ι, ∃ s t : ℤ, s < t ∧ IsZero (F.degreeObject s n) ∧ IsIso ((F.obj t).arrow.f n)

/-- A filtration is bounded below when, in every degree `n`, some `FₛCₙ` is zero.
Source: Weibel, *An Introduction to Homological Algebra*, §5.4, p. 132. -/
def IsBoundedBelow (F : ChainComplexFiltration A c K) : Prop :=
  ∀ n : ι, ∃ s : ℤ, IsZero (F.degreeObject s n)

/-- A filtration is bounded above when, in every degree `n`, some inclusion `FₜCₙ → Cₙ` is an
isomorphism, i.e. `FₜCₙ=Cₙ`.  Source: Weibel, *An Introduction to Homological Algebra*, §5.4,
p. 132. -/
def IsBoundedAbove (F : ChainComplexFiltration A c K) : Prop :=
  ∀ n : ι, ∃ t : ℤ, IsIso ((F.obj t).arrow.f n)

/-- A Hausdorff filtration, `⋂ₚ FₚC = 0`.  This is the generic Hausdorff predicate specialized to
chain subcomplexes.  Source: Weibel, *An Introduction to Homological Algebra*, Definition 5.4.4,
p. 132. -/
abbrev IsHausdorff (F : ChainComplexFiltration A c K) : Prop :=
  IncreasingFiltration.IsHausdorff F

end ChainComplexFiltration

end LeanCategories.Homological
