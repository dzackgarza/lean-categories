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

#print axioms LeanCategories.Lattices.Valued.standardParabolic
#print axioms WythoffCoarseningDatum.coarsenedCones
#print axioms WythoffCoarseningDatum.mem_of_isFaceOf
#print axioms WythoffCoarseningDatum.inf_simple_isFaceOf
#print axioms WythoffCoarseningDatum.inf_wordProd_isFaceOf
#print axioms WythoffCoarseningDatum.maximalConesMeetInFaces
#print axioms WythoffCoarseningDatum.inf_isFaceOf_left
#print axioms WythoffCoarseningDatum.inf_isFaceOf_right
#print axioms WythoffCoarseningDatum.inf_mem

end LeanCategories.Lattices.Valued
