/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PositiveConeReflections
public import LeanCategories.Lattices.Valued.RootSystem
public import LeanCategories.Lattices.Valued.Signature

/-!
# The positive cone, `O⁺` and the reflection group of an integral lattice

The real-form statements of `PositiveCone` and `PositiveConeReflections` are stated for a real
quadratic form. This file attaches the real form itself to an integral lattice `M`: the quadratic
form `realFormQuadratic M` on `M ⊗ ℝ`, whose signature is `integralSignature M` by definition
(`realFormQuadratic_sigPos`, `realFormQuadratic_sigNeg`, `realFormQuadratic_sigRadical`).

Not yet here: `O(M) → O(M ⊗ ℝ)` and with it `O⁺(M)` as a preimage, `W(M) ≤ O⁺(M)`, and
normality of `W(M)` in `O(M)`. The obstruction is mechanical, not mathematical: the group laws
for the isometry-valued homomorphism compare `Q.IsometryEquiv Q`-applications with `LinearEquiv`
applications, and the coercion between them is an instance projection, which definitional
comparison at reducible transparency does not unfold.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv. Akad.
  Nauk SSSR Ser. Mat. 43 (1979), §1.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

section RealForm

variable (L : FiniteProjectiveLatticeCat ℤ ℤ)

/-- The **real form** of an integral lattice: its scalar extension to `ℝ`. -/
noncomputable def realForm : FiniteFormCat ℝ ℝ :=
  (finiteProjectiveToFiniteForm ℝ ℝ).obj ((baseChangeFiniteIntegral ℤ ℝ).obj L)

/-- The quadratic form of the real form of an integral lattice. -/
noncomputable def realFormQuadratic : QuadraticForm ℝ (realForm L).obj.carrier :=
  finiteFormQuadraticForm ℝ (realForm L)

theorem realFormQuadratic_sigPos : sigPos (realFormQuadratic L) = (integralSignature L).1 := rfl

theorem realFormQuadratic_sigNeg : sigNeg (realFormQuadratic L) = (integralSignature L).2.1 := rfl

theorem realFormQuadratic_sigRadical :
    Module.finrank ℝ (realFormQuadratic L).radical = (integralSignature L).2.2 := rfl

theorem realFormQuadratic_apply (x : (realForm L).obj.carrier) :
    realFormQuadratic L x = (realForm L).obj.pairing x x := rfl

end RealForm

end LeanCategories.Lattices.Valued
