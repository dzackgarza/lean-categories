/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Chain complexes associated to simplicial objects

Weibel, *An Introduction to Homological Algebra* (1994), Definitions 8.2.1 and 8.3.6,
pp. 259--269 (FC05-C08-U012 and FC05-C08-U032).

Mathlib already owns both constructions.  This file gives source-facing names for the
unnormalized alternating-face complex, the normalized Moore complex, and the homology
object `π_n(A)=H_n(N(A))`.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- Weibel's unnormalized chain complex of a simplicial object:
`C_n(A)=A_n` with differential `Σ_i (-1)^i ∂_i`. -/
noncomputable def simplicialUnnormalizedChainComplex [Preadditive C]
    (A : SimplicialObject C) : ChainComplex C ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj A

/-- Weibel's normalized Moore complex
`N_n(A)=⋂_{i<n} ker(∂_i)`, with the last face as differential with the standard sign. -/
noncomputable def simplicialNormalizedChainComplex [Abelian C]
    (A : SimplicialObject C) : ChainComplex C ℕ :=
  (AlgebraicTopology.normalizedMooreComplex C).obj A

/-- For a simplicial object in an abelian category, Weibel's `π_n(A)` is the
degree-`n` homology object of its normalized Moore complex. -/
noncomputable def simplicialHomotopyObject [Abelian C]
    (A : SimplicialObject C) (n : ℕ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).obj
    (simplicialNormalizedChainComplex A)

end LeanCategories.Homological
