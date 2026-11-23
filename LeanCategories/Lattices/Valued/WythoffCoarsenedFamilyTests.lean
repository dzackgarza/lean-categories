/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.WythoffCoarsenedFamily
public import Mathlib.Tactic

/-!
# Focused verification for #180

The exported construction and both fan clauses are checked here.  These are general declarations,
not examples or finite-model evidence for the general theorem.
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

/-- A word-reduced representative need not be double-coset minimal: a single inactive generator
is reduced as a Coxeter word, but its double coset contains the identity, of strictly smaller
length.  This rejects confusing `CoxeterSystem.exists_isReduced` with the required
representative. -/
theorem wordReduced_singleton_not_parabolicReduced
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ℳ : CoxeterMatrix ι} {W : Type*} [Group W]
    (cs : CoxeterSystem ℳ W) {J : Finset ι} {j : ι}
    (hj : j ∈ J) :
    cs.IsReduced [j] ∧ ¬ParabolicReduced cs J [j] := by
  constructor
  · rw [CoxeterSystem.IsReduced, cs.wordProd_singleton, cs.length_simple]
    rfl
  · intro hmin
    let u : standardParabolic cs J :=
      ⟨cs.simple j, Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩⟩
    have hle := hmin.2 u 1
    have hu : (u : W) = cs.simple j := rfl
    rw [hu] at hle
    simp at hle

#print axioms LeanCategories.Lattices.Valued.standardParabolic
#print axioms LeanCategories.Lattices.Valued.exists_isParabolicMinimal
#print axioms LeanCategories.Lattices.Valued.exists_parabolicReduced
#print axioms LeanCategories.Lattices.Valued.parabolicLeftReduced_take
#print axioms LeanCategories.Lattices.Valued.wordReduced_singleton_not_parabolicReduced
#print axioms WythoffCoarseningDatum.reduced_gallery
#print axioms WythoffCoarseningDatum.coarsenedCones
#print axioms WythoffCoarseningDatum.mem_of_isFaceOf
#print axioms WythoffCoarseningDatum.inf_simple_isFaceOf
#print axioms WythoffCoarseningDatum.gallery
#print axioms WythoffCoarseningDatum.inf_wordProd_isFaceOf
#print axioms WythoffCoarseningDatum.maximalConesMeetInFaces
#print axioms WythoffCoarseningDatum.inf_isFaceOf_left
#print axioms WythoffCoarseningDatum.inf_isFaceOf_right
#print axioms WythoffCoarseningDatum.inf_mem

end LeanCategories.Lattices.Valued
