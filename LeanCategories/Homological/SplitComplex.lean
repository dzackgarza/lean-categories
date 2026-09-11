/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Split and split-exact complexes

Weibel, *An Introduction to Homological Algebra* (1994), Definition 1.4.1,
FC05-C01-U031.

A complex is split when it admits degree-reversing splitting maps satisfying
`d = d s d`. It is split exact when it is both split and acyclic. The nearby
condition `d s + s d = id` is the contracting-homotopy characterization used
in the discussion of split-exact complexes; it is not substituted for the
source definition here.

The definition is stated for an arbitrary homological-complex shape. For an
ordinary chain complex, a proof of `c.Rel j i` says that degree `j` immediately
precedes degree `i`, so `s i j` is exactly Weibel's map from one degree to the
next higher degree.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory Limits

universe v u

variable {ι : Type*} {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
variable {c : ComplexShape ι} (K : HomologicalComplex V c)

/-- Splitting maps for a homological complex. For every differential
`K.d i j`, the corresponding reverse-degree map `s j i` is required to satisfy
the source identity `d = d s d`. -/
structure Splitting where
  s : ∀ i j, c.Rel j i → (K.X i ⟶ K.X j)
  d_s_d : ∀ i j (hij : c.Rel i j),
    K.d i j = K.d i j ≫ s j i hij ≫ K.d i j

/-- A homological complex is split when splitting maps exist. -/
def IsSplit : Prop :=
  Nonempty (Splitting K)

/-- Weibel's split-exact condition: split and acyclic. -/
def IsSplitExact : Prop :=
  IsSplit K ∧ K.Acyclic

/-- A complex whose differentials all vanish is split. This gives a basic
positive model of splitness without imposing exactness. -/
def Splitting.ofDifferentialEqZero (hK : ∀ i j, K.d i j = 0) : Splitting K where
  s := fun _ _ _ => 0
  d_s_d i j _ := by simp [hK i j]

theorem isSplit_of_differentialEqZero (hK : ∀ i j, K.d i j = 0) : IsSplit K :=
  ⟨Splitting.ofDifferentialEqZero K hK⟩

-- Separating boundary: splitness alone does not satisfy the split-exact definition.
example (hS : IsSplit K) (hA : ¬K.Acyclic) : IsSplit K ∧ ¬IsSplitExact K :=
  ⟨hS, fun h => hA h.2⟩

end LeanCategories.Homological
