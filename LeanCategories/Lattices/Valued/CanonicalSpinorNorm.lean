/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ContractionScalars
public import LeanCategories.Lattices.Valued.ReflectionGeneration
public import LeanCategories.Lattices.Valued.SpinorNormDescent

/-!
# The canonical spinor norm

The spinor norm of a nondegenerate finite symmetric form exists and is unique, so it is a
canonical invariant rather than chosen data.

Existence comes from the Clifford construction: the Lipschitz group acts on the module by
twisted conjugation, that action is onto the orthogonal group because reflections generate it,
its kernel is the scalars, and the Clifford norm kills scalars modulo squares, so the norm
descends. Uniqueness comes from reflection generation alone.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- The canonical spinor norm of a nondegenerate finite symmetric form. -/
def canonicalSpinorNorm (L : FiniteFormCat K K) (hL : L.obj.IsLeftNondegenerate) :
    SpinorNorm L :=
  haveI : Module.Finite K L.obj.carrier := L.property.1
  spinorNormOfNondegenerate L hL (contractionsDetectScalars (finiteFormQuadratic L))

/-- Every spinor norm of a nondegenerate form is the canonical one. -/
theorem eq_canonicalSpinorNorm (L : FiniteFormCat K K) (hL : L.obj.IsLeftNondegenerate)
    (ν : SpinorNorm L) : ν = canonicalSpinorNorm L hL :=
  spinorNorm_unique_of_nondegenerate L hL ν _

/-- The canonical spinor norm takes the expected value on a reflection. -/
theorem canonicalSpinorNorm_reflection (L : FiniteFormCat K K)
    (hL : L.obj.IsLeftNondegenerate) (v : L.obj.carrier)
    (hv : L.obj.pairing v v ≠ 0) :
    (canonicalSpinorNorm L hL).1 (finiteFormReflectionElement L v hv) =
      fieldSquareClass (Units.mk0 (L.obj.pairing v v) hv) :=
  (canonicalSpinorNorm L hL).2 v hv

end LeanCategories.Lattices.Valued
