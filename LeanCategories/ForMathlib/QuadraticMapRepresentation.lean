/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Chi-Yun Hsu
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Values represented by a quadratic map

This ports the representation and isotropy definitions from
`mariainesdff/HassePrinciple@47df8f51939b364e678893d54e8a3faf6ec52302`,
`HassePrinciple/QuadraticForm/Basic.lean`. The reference is released under Apache-2.0.

These definitions realize Peters--Sterk, *Symmetric and Quadratic Forms* (June 2024),
§3.2 (`FC11-C03-U008`): a quadratic form represents `n` when it takes the value `n`
on a nonzero vector, and it represents zero exactly when it is isotropic.
-/

@[expose] public section

namespace QuadraticMap

variable {R M₁ N : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
  [AddCommMonoid N] [Module R N]

/-- A quadratic map is isotropic if it vanishes on a nonzero vector. -/
abbrev Isotropic (Q : QuadraticMap R M₁ N) : Prop :=
  ¬ Q.Anisotropic

/-- `Q` represents `n` if it takes the value `n` on a nonzero vector. -/
def represents (Q : QuadraticMap R M₁ N) (n : N) : Prop :=
  ∃ x : M₁, Q x = n ∧ x ≠ 0

@[simp]
lemma represents_zero_iff_isotropic {Q : QuadraticMap R M₁ N} :
    Q.represents 0 ↔ Q.Isotropic := by
  simp [Isotropic, Anisotropic, represents]

end QuadraticMap
